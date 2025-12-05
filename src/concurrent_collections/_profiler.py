"""
profiler - Instrumentation for measuring comparator and container performance

This module provides tools for measuring the resource consumption of
comparators and containers, helping users make data-driven optimization
decisions.
"""

import logging
import time
import threading
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Callable, Dict, List, Optional, Union
from pathlib import Path


class OptimizationLevel(Enum):
    """Optimization recommendation levels."""
    NONE_NEEDED = "none_needed"
    CONSIDER_KEY_FUNCTION = "consider_key_function"
    CONSIDER_NATIVE = "consider_native"
    CRITICAL = "critical"


@dataclass
class ComparisonTrace:
    """Record of a sampled comparison for debugging."""
    timestamp_ns: int
    container_name: Optional[str]
    a_repr: str
    b_repr: str
    result: int
    duration_ns: int
    thread_id: int


@dataclass
class ThreadStats:
    """Per-thread comparison statistics."""
    thread_id: int
    thread_name: Optional[str]
    comparison_count: int = 0
    time_sec: float = 0.0
    time_pct: float = 0.0
    avg_comparison_ns: float = 0.0


@dataclass
class ContainerStats:
    """Per-container comparison statistics."""
    name: str
    comparison_count: int = 0
    time_sec: float = 0.0
    time_pct: float = 0.0
    avg_comparison_ns: float = 0.0


@dataclass
class ProfilerReport:
    """Resource consumption report from ComparatorProfiler."""
    # Timing
    wall_time_sec: float = 0.0
    comparator_time_sec: float = 0.0
    comparator_time_pct: float = 0.0

    # Comparison counts
    comparison_count: int = 0
    avg_comparison_ns: float = 0.0

    # Latency percentiles (nanoseconds)
    p50_comparison_ns: float = 0.0
    p95_comparison_ns: float = 0.0
    p99_comparison_ns: float = 0.0
    p999_comparison_ns: float = 0.0
    max_comparison_ns: float = 0.0

    # CPU time (if available)
    cpu_time_sec: Optional[float] = None
    comparator_cpu_sec: Optional[float] = None
    comparator_cpu_pct: Optional[float] = None

    # Memory (if tracked)
    comparator_alloc_bytes: int = 0

    # Per-container breakdown
    containers: Dict[str, ContainerStats] = field(default_factory=dict)

    # Per-thread breakdown
    threads: Dict[int, ThreadStats] = field(default_factory=dict)

    # Sampled comparison traces
    traces: List[ComparisonTrace] = field(default_factory=list)

    @property
    def optimization_level(self) -> OptimizationLevel:
        """Determine optimization recommendation based on measurements."""
        if self.comparator_time_pct < 5:
            return OptimizationLevel.NONE_NEEDED
        elif self.comparator_time_pct < 20:
            return OptimizationLevel.CONSIDER_KEY_FUNCTION
        elif self.comparator_time_pct < 50:
            return OptimizationLevel.CONSIDER_NATIVE
        else:
            return OptimizationLevel.CRITICAL

    def recommendation(self) -> str:
        """Generate human-readable optimization recommendation."""
        level = self.optimization_level

        if level == OptimizationLevel.NONE_NEEDED:
            return (
                f"Comparator overhead is negligible ({self.comparator_time_pct:.1f}%).\n"
                "No optimization needed."
            )
        elif level == OptimizationLevel.CONSIDER_KEY_FUNCTION:
            return (
                f"Comparator overhead is low ({self.comparator_time_pct:.1f}%).\n"
                "Consider using key= parameter instead of cmp= if applicable.\n"
                "Key functions extract once and compare many times."
            )
        elif level == OptimizationLevel.CONSIDER_NATIVE:
            return (
                f"Comparator overhead is moderate ({self.comparator_time_pct:.1f}%).\n"
                "Consider implementing a native comparator (Cython or Rust).\n"
                "See documentation for examples."
            )
        else:
            return (
                f"Comparator overhead is CRITICAL ({self.comparator_time_pct:.1f}%).\n"
                "STRONGLY recommend implementing a native comparator.\n"
                "This is likely a major bottleneck in your application."
            )

    def __str__(self) -> str:
        """Human-readable report."""
        lines = [
            "ComparatorProfiler Report",
            "=========================",
            f"Wall time:              {self.wall_time_sec:.3f} sec",
            f"  Comparator time:      {self.comparator_time_sec:.3f} sec ({self.comparator_time_pct:.1f}%)",
            f"  Other time:           {self.wall_time_sec - self.comparator_time_sec:.3f} sec",
            "",
            f"Comparisons:            {self.comparison_count:,}",
            f"  Avg per comparison:   {self.avg_comparison_ns:.0f} ns",
        ]

        if self.p50_comparison_ns > 0:
            lines.extend([
                "",
                "Latency percentiles:",
                f"  P50:                  {self.p50_comparison_ns:,.0f} ns",
                f"  P95:                  {self.p95_comparison_ns:,.0f} ns",
                f"  P99:                  {self.p99_comparison_ns:,.0f} ns",
                f"  Max:                  {self.max_comparison_ns:,.0f} ns",
            ])

        lines.extend([
            "",
            f"Recommendation: {self.optimization_level.value.upper()}",
            self.recommendation(),
        ])

        return "\n".join(lines)

    def to_dict(self) -> Dict[str, Any]:
        """Machine-readable format."""
        return {
            'wall_time_sec': self.wall_time_sec,
            'comparator_time_sec': self.comparator_time_sec,
            'comparator_time_pct': self.comparator_time_pct,
            'comparison_count': self.comparison_count,
            'avg_comparison_ns': self.avg_comparison_ns,
            'p50_comparison_ns': self.p50_comparison_ns,
            'p95_comparison_ns': self.p95_comparison_ns,
            'p99_comparison_ns': self.p99_comparison_ns,
            'max_comparison_ns': self.max_comparison_ns,
            'optimization_level': self.optimization_level.value,
        }

    def to_json(self, path: Optional[Union[str, Path]] = None) -> str:
        """Export as JSON."""
        import json
        data = self.to_dict()
        json_str = json.dumps(data, indent=2)
        if path:
            Path(path).write_text(json_str)
        return json_str


class ComparatorProfiler:
    """Measure comparator resource consumption relative to total program.

    This profiler measures the time spent in comparison operations
    between two points in your code (point A to point B), allowing
    you to understand whether comparator overhead is significant.

    Usage:
        profiler = ComparatorProfiler()
        profiler.start()  # Point A

        # Your workload
        for item in data:
            container[item.key] = item

        report = profiler.stop()  # Point B
        print(report)

    Or using context manager:
        with ComparatorProfiler() as profiler:
            # Your workload
            ...
        print(profiler.report)
    """

    def __init__(
        self,
        *,
        sample_rate: float = 1.0,
        trace_samples: int = 0,
        track_percentiles: bool = True,
        logger: Optional[logging.Logger] = None,
        log_interval: Optional[float] = None,
        threshold_pct: Optional[float] = None,
        on_threshold: Optional[Callable[['ProfilerReport'], None]] = None,
    ):
        """Initialize profiler.

        Args:
            sample_rate: Fraction of comparisons to time (1.0 = all, 0.01 = 1%)
            trace_samples: Number of comparisons to capture for debugging
            track_percentiles: Whether to compute latency percentiles
            logger: Logger for periodic stats during long workloads
            log_interval: Seconds between log messages (requires logger)
            threshold_pct: Alert when comparator overhead exceeds this percentage
            on_threshold: Callback when threshold exceeded
        """
        self._sample_rate = sample_rate
        self._trace_samples = trace_samples
        self._track_percentiles = track_percentiles
        self._logger = logger
        self._log_interval = log_interval
        self._threshold_pct = threshold_pct
        self._on_threshold = on_threshold

        self._lock = threading.Lock()
        self._start_time: Optional[float] = None
        self._end_time: Optional[float] = None
        self._comparison_count = 0
        self._comparison_time_ns = 0
        self._latencies: List[int] = [] if track_percentiles else None
        self._traces: List[ComparisonTrace] = []
        self._thread_stats: Dict[int, ThreadStats] = {}
        self._container_stats: Dict[str, ContainerStats] = {}
        self._report: Optional[ProfilerReport] = None

    def start(self) -> None:
        """Begin profiling. Call at point A."""
        with self._lock:
            self._start_time = time.perf_counter()
            self._end_time = None
            self._comparison_count = 0
            self._comparison_time_ns = 0
            if self._track_percentiles:
                self._latencies = []
            self._traces = []
            self._thread_stats = {}
            self._container_stats = {}
            self._report = None

    def stop(self) -> ProfilerReport:
        """End profiling. Call at point B. Returns report."""
        with self._lock:
            self._end_time = time.perf_counter()
            self._report = self._compute_report()
            return self._report

    def reset(self) -> None:
        """Reset counters without stopping."""
        with self._lock:
            self._comparison_count = 0
            self._comparison_time_ns = 0
            if self._track_percentiles:
                self._latencies = []
            self._traces = []

    @property
    def report(self) -> ProfilerReport:
        """Get current report without stopping."""
        with self._lock:
            if self._report is not None:
                return self._report
            return self._compute_report()

    def record_comparison(
        self,
        duration_ns: int,
        container_name: Optional[str] = None,
        a: Any = None,
        b: Any = None,
        result: int = 0,
    ) -> None:
        """Record a comparison (called by instrumented containers).

        This method is called by containers to record comparison timing.
        It should not normally be called directly by user code.

        Args:
            duration_ns: Comparison duration in nanoseconds
            container_name: Name of the container
            a: First operand (for tracing)
            b: Second operand (for tracing)
            result: Comparison result
        """
        with self._lock:
            self._comparison_count += 1
            self._comparison_time_ns += duration_ns

            if self._track_percentiles and self._latencies is not None:
                self._latencies.append(duration_ns)

            # Record trace if requested
            if len(self._traces) < self._trace_samples:
                self._traces.append(ComparisonTrace(
                    timestamp_ns=time.perf_counter_ns(),
                    container_name=container_name,
                    a_repr=repr(a)[:100] if a is not None else "None",
                    b_repr=repr(b)[:100] if b is not None else "None",
                    result=result,
                    duration_ns=duration_ns,
                    thread_id=threading.get_ident(),
                ))

            # Update thread stats
            thread_id = threading.get_ident()
            if thread_id not in self._thread_stats:
                self._thread_stats[thread_id] = ThreadStats(
                    thread_id=thread_id,
                    thread_name=threading.current_thread().name,
                )
            self._thread_stats[thread_id].comparison_count += 1
            self._thread_stats[thread_id].time_sec += duration_ns / 1e9

            # Update container stats
            if container_name:
                if container_name not in self._container_stats:
                    self._container_stats[container_name] = ContainerStats(name=container_name)
                self._container_stats[container_name].comparison_count += 1
                self._container_stats[container_name].time_sec += duration_ns / 1e9

    def _compute_report(self) -> ProfilerReport:
        """Compute report from collected data."""
        end_time = self._end_time or time.perf_counter()
        wall_time = end_time - (self._start_time or end_time)

        comparator_time_sec = self._comparison_time_ns / 1e9
        comparator_time_pct = (comparator_time_sec / wall_time * 100) if wall_time > 0 else 0

        avg_ns = (
            self._comparison_time_ns / self._comparison_count
            if self._comparison_count > 0 else 0
        )

        # Compute percentiles
        p50 = p95 = p99 = p999 = max_latency = 0.0
        if self._track_percentiles and self._latencies:
            sorted_latencies = sorted(self._latencies)
            n = len(sorted_latencies)
            p50 = sorted_latencies[int(n * 0.50)] if n > 0 else 0
            p95 = sorted_latencies[int(n * 0.95)] if n > 0 else 0
            p99 = sorted_latencies[int(n * 0.99)] if n > 0 else 0
            p999 = sorted_latencies[int(n * 0.999)] if n > 0 else 0
            max_latency = sorted_latencies[-1] if n > 0 else 0

        # Compute thread percentages
        for stats in self._thread_stats.values():
            stats.time_pct = (stats.time_sec / comparator_time_sec * 100) if comparator_time_sec > 0 else 0
            stats.avg_comparison_ns = (
                stats.time_sec * 1e9 / stats.comparison_count
                if stats.comparison_count > 0 else 0
            )

        # Compute container percentages
        for stats in self._container_stats.values():
            stats.time_pct = (stats.time_sec / comparator_time_sec * 100) if comparator_time_sec > 0 else 0
            stats.avg_comparison_ns = (
                stats.time_sec * 1e9 / stats.comparison_count
                if stats.comparison_count > 0 else 0
            )

        return ProfilerReport(
            wall_time_sec=wall_time,
            comparator_time_sec=comparator_time_sec,
            comparator_time_pct=comparator_time_pct,
            comparison_count=self._comparison_count,
            avg_comparison_ns=avg_ns,
            p50_comparison_ns=p50,
            p95_comparison_ns=p95,
            p99_comparison_ns=p99,
            p999_comparison_ns=p999,
            max_comparison_ns=max_latency,
            containers=dict(self._container_stats),
            threads=dict(self._thread_stats),
            traces=list(self._traces),
        )

    def __enter__(self) -> 'ComparatorProfiler':
        """Context manager entry."""
        self.start()
        return self

    def __exit__(self, *args) -> None:
        """Context manager exit."""
        self.stop()


# Global profiler instance for simple use cases
_active_profiler: Optional[ComparatorProfiler] = None
_profiler_lock = threading.Lock()


def get_active_profiler() -> Optional[ComparatorProfiler]:
    """Get the currently active profiler, if any."""
    with _profiler_lock:
        return _active_profiler


def set_active_profiler(profiler: Optional[ComparatorProfiler]) -> None:
    """Set the active profiler for automatic instrumentation."""
    global _active_profiler
    with _profiler_lock:
        _active_profiler = profiler
