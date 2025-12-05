"""
smr_ibr - Interval-Based Reclamation

This module implements Interval-Based Reclamation (IBR), a safe memory reclamation
scheme for lock-free data structures. IBR solves the fundamental problem of
determining when it's safe to free memory that may still be accessed by
concurrent readers.

Key Concept: Epochs
- Time is divided into epochs
- Each thread records which epoch it entered
- A node retired in epoch E can only be freed when NO thread is in epoch <= E
"""

import threading
import time
from dataclasses import dataclass, field
from datetime import datetime
from typing import Any, Callable, Dict, List, Optional, Set, Tuple
from collections import deque

from concurrent_collections._config import config
from concurrent_collections._atomics import AtomicInt, MemoryOrder


# Configuration defaults
DEFAULT_MAX_THREADS = 256
DEFAULT_RETIRE_THRESHOLD = 64
DEFAULT_MAX_RECLAIM_PER_POLL = 32
DEFAULT_STALL_THRESHOLD_EPOCHS = 100


@dataclass
class RetiredNode:
    """A node waiting for safe reclamation."""
    obj: Any
    size: int
    epoch: int
    retire_time: float
    free_fn: Optional[Callable[[Any, int], None]] = None


@dataclass
class EpochEvent:
    """Record of an epoch-related event."""
    timestamp: float
    event_type: str  # "advance", "enter", "exit", "retire", "reclaim"
    thread_id: int
    epoch: int
    details: Optional[Dict] = None


@dataclass
class LimboSnapshot:
    """Point-in-time limbo list state."""
    timestamp: float
    thread_id: int
    epoch_0_count: int
    epoch_1_count: int
    epoch_2_count: int
    total_count: int
    total_bytes: int


@dataclass
class ThreadSMRStats:
    """Per-thread SMR statistics."""
    thread_id: int
    thread_name: Optional[str] = None
    enter_count: int = 0
    exit_count: int = 0
    retire_count: int = 0
    poll_count: int = 0
    reclaim_count: int = 0
    total_cs_time_ns: int = 0
    avg_cs_time_ns: float = 0.0
    max_cs_time_ns: int = 0
    peak_limbo_count: int = 0
    peak_limbo_bytes: int = 0
    stall_count: int = 0
    caused_stall_epochs: int = 0


@dataclass
class StallEvent:
    """Record of a stall event."""
    timestamp: float
    stalled_thread_id: int
    stalled_at_epoch: int
    global_epoch: int
    epoch_lag: int
    duration_ns: Optional[int] = None
    resolution: str = "unknown"  # "exited", "advanced", "neutralized"


@dataclass
class ReclamationRecord:
    """Record of a node's lifecycle."""
    retire_time: float
    retire_epoch: int
    retire_thread: int
    reclaim_time: Optional[float] = None
    reclaim_epoch: Optional[int] = None
    reclaim_thread: Optional[int] = None
    latency_ns: Optional[int] = None
    size: int = 0


@dataclass
class SMRProfilerReport:
    """Complete SMR profiler report."""
    # Global epoch statistics
    start_epoch: int = 0
    end_epoch: int = 0
    epoch_advances: int = 0
    avg_epoch_duration_ns: float = 0.0

    # Safe epoch statistics
    safe_epoch_lag_avg: float = 0.0
    safe_epoch_lag_max: int = 0

    # Reclamation statistics
    total_retired: int = 0
    total_reclaimed: int = 0
    pending_count: int = 0
    pending_bytes: int = 0

    # Latency percentiles (nanoseconds)
    reclaim_latency_p50: float = 0.0
    reclaim_latency_p95: float = 0.0
    reclaim_latency_p99: float = 0.0
    reclaim_latency_p999: float = 0.0
    reclaim_latency_max: float = 0.0

    # Poll statistics
    poll_count: int = 0
    nodes_per_poll_avg: float = 0.0
    nodes_per_poll_max: int = 0
    empty_poll_pct: float = 0.0

    # Memory pressure
    peak_pending_count: int = 0
    peak_pending_bytes: int = 0
    memory_bound_utilization: float = 0.0

    # Thread statistics
    thread_stats: List[ThreadSMRStats] = field(default_factory=list)

    # Stall analysis
    stall_events: List[StallEvent] = field(default_factory=list)
    total_stall_time_ns: int = 0
    stall_count: int = 0

    # Timeline (if enabled)
    epoch_timeline: Optional[List[EpochEvent]] = None
    limbo_snapshots: Optional[List[LimboSnapshot]] = None

    # Timing
    duration_seconds: float = 0.0
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None


class IBRThreadState:
    """Per-thread state for IBR."""

    __slots__ = (
        'thread_id',
        'local_epoch',
        'active',
        'retire_lists',
        'retire_count',
        'enter_time',
        # Stats
        'stats',
    )

    def __init__(self, thread_id: int):
        """Initialize thread state.

        Args:
            thread_id: Unique thread identifier
        """
        self.thread_id = thread_id
        self.local_epoch = 0
        self.active = False
        # Ring buffer of 3 retire lists (for epochs E-2, E-1, E)
        self.retire_lists: List[List[RetiredNode]] = [[], [], []]
        self.retire_count = 0
        self.enter_time: Optional[float] = None
        self.stats = ThreadSMRStats(thread_id=thread_id)


class IBRDomain:
    """Interval-Based Reclamation Domain.

    This class manages safe memory reclamation using epoch tracking.
    Threads enter/exit critical sections, and retired nodes are only
    freed when it's safe (no thread holds a reference).
    """

    __slots__ = (
        '_lock',
        '_global_epoch',
        '_thread_states',
        '_thread_epochs',
        '_thread_active',
        '_max_threads',
        '_retire_threshold',
        '_max_reclaim_per_poll',
        '_stall_threshold',
        # Statistics
        '_stats_enabled',
        '_retired_count',
        '_reclaimed_count',
        '_poll_count',
        '_empty_poll_count',
        '_peak_pending_count',
        '_peak_pending_bytes',
        '_epoch_advances',
        '_stall_events',
        '_last_epoch_time',
        '_epoch_durations',
        '_reclaim_latencies',
        '_timeline',
    )

    def __init__(
        self,
        max_threads: int = DEFAULT_MAX_THREADS,
        retire_threshold: Optional[int] = None,
        max_reclaim_per_poll: Optional[int] = None,
        stall_threshold: Optional[int] = None,
    ):
        """Initialize IBR domain.

        Args:
            max_threads: Maximum concurrent threads
            retire_threshold: Nodes before triggering reclamation
            max_reclaim_per_poll: Max nodes to reclaim per poll
            stall_threshold: Epochs behind before thread is stalled
        """
        self._lock = threading.Lock()
        self._global_epoch = AtomicInt(1)
        self._thread_states: Dict[int, IBRThreadState] = {}

        # Arrays for fast epoch/active checking
        self._thread_epochs: Dict[int, int] = {}
        self._thread_active: Dict[int, bool] = {}

        self._max_threads = max_threads
        self._retire_threshold = retire_threshold or config.retire_threshold
        self._max_reclaim_per_poll = max_reclaim_per_poll or config.max_reclaim_per_poll
        self._stall_threshold = stall_threshold or DEFAULT_STALL_THRESHOLD_EPOCHS

        # Statistics
        self._stats_enabled = config.enable_statistics
        self._retired_count = 0
        self._reclaimed_count = 0
        self._poll_count = 0
        self._empty_poll_count = 0
        self._peak_pending_count = 0
        self._peak_pending_bytes = 0
        self._epoch_advances = 0
        self._stall_events: List[StallEvent] = []
        self._last_epoch_time = time.time()
        self._epoch_durations: List[float] = []
        self._reclaim_latencies: List[int] = []
        self._timeline: List[EpochEvent] = []

    def thread_register(self) -> int:
        """Register current thread with IBR.

        Must be called before using enter/exit/retire.

        Returns:
            Thread ID for use in other operations
        """
        thread_id = threading.get_ident()
        with self._lock:
            if thread_id not in self._thread_states:
                if len(self._thread_states) >= self._max_threads:
                    raise RuntimeError(f"Maximum threads ({self._max_threads}) exceeded")
                self._thread_states[thread_id] = IBRThreadState(thread_id)
                self._thread_epochs[thread_id] = 0
                self._thread_active[thread_id] = False
        return thread_id

    def thread_unregister(self, thread_id: Optional[int] = None) -> None:
        """Unregister thread from IBR.

        Args:
            thread_id: Thread ID (default: current thread)
        """
        if thread_id is None:
            thread_id = threading.get_ident()

        with self._lock:
            if thread_id in self._thread_states:
                state = self._thread_states[thread_id]
                if state.active:
                    raise RuntimeError("Cannot unregister while in critical section")

                # Reclaim any pending retired nodes
                for bucket in state.retire_lists:
                    for node in bucket:
                        self._do_free(node)
                        self._reclaimed_count += 1
                    bucket.clear()

                del self._thread_states[thread_id]
                del self._thread_epochs[thread_id]
                del self._thread_active[thread_id]

    def enter(self, thread_id: Optional[int] = None) -> int:
        """Enter critical section.

        After entering, the thread can safely read shared data.
        Must call exit() when done.

        Args:
            thread_id: Thread ID (default: current thread)

        Returns:
            Current epoch
        """
        if thread_id is None:
            thread_id = threading.get_ident()

        # Load current global epoch with acquire semantics
        epoch = self._global_epoch.load(MemoryOrder.ACQUIRE)

        with self._lock:
            if thread_id not in self._thread_states:
                self.thread_register()

            state = self._thread_states[thread_id]
            state.local_epoch = epoch
            state.active = True
            state.enter_time = time.time()

            self._thread_epochs[thread_id] = epoch
            self._thread_active[thread_id] = True

            if self._stats_enabled:
                state.stats.enter_count += 1
                self._record_event("enter", thread_id, epoch)

        return epoch

    def exit(self, thread_id: Optional[int] = None) -> None:
        """Exit critical section.

        After exiting, the thread no longer blocks reclamation.
        Must not access protected pointers after this call.

        Args:
            thread_id: Thread ID (default: current thread)
        """
        if thread_id is None:
            thread_id = threading.get_ident()

        with self._lock:
            if thread_id not in self._thread_states:
                return

            state = self._thread_states[thread_id]
            state.active = False
            self._thread_active[thread_id] = False

            if self._stats_enabled and state.enter_time:
                cs_time_ns = int((time.time() - state.enter_time) * 1e9)
                state.stats.exit_count += 1
                state.stats.total_cs_time_ns += cs_time_ns
                if cs_time_ns > state.stats.max_cs_time_ns:
                    state.stats.max_cs_time_ns = cs_time_ns
                if state.stats.exit_count > 0:
                    state.stats.avg_cs_time_ns = state.stats.total_cs_time_ns / state.stats.exit_count
                self._record_event("exit", thread_id, state.local_epoch)

            # Opportunistic reclamation
            if state.retire_count >= self._retire_threshold:
                self._poll_internal(state)

    def retire(
        self,
        obj: Any,
        thread_id: Optional[int] = None,
        size: int = 0,
        free_fn: Optional[Callable[[Any, int], None]] = None,
    ) -> None:
        """Retire a node for deferred reclamation.

        The node will be freed when it's safe (no thread can access it).

        Args:
            obj: Object to retire
            thread_id: Thread ID (default: current thread)
            size: Size of object (for statistics)
            free_fn: Custom free function (optional)
        """
        if thread_id is None:
            thread_id = threading.get_ident()

        with self._lock:
            if thread_id not in self._thread_states:
                self.thread_register()

            state = self._thread_states[thread_id]
            epoch = self._global_epoch.load(MemoryOrder.RELAXED)
            bucket = epoch % 3

            node = RetiredNode(
                obj=obj,
                size=size,
                epoch=epoch,
                retire_time=time.time(),
                free_fn=free_fn,
            )

            state.retire_lists[bucket].append(node)
            state.retire_count += 1
            self._retired_count += 1

            if self._stats_enabled:
                state.stats.retire_count += 1
                self._record_event("retire", thread_id, epoch, {"size": size})

                # Track peak pending
                pending = sum(len(b) for b in state.retire_lists)
                pending_bytes = sum(sum(n.size for n in b) for b in state.retire_lists)
                if pending > state.stats.peak_limbo_count:
                    state.stats.peak_limbo_count = pending
                if pending_bytes > state.stats.peak_limbo_bytes:
                    state.stats.peak_limbo_bytes = pending_bytes

                total_pending = sum(
                    sum(len(b) for b in s.retire_lists)
                    for s in self._thread_states.values()
                )
                total_bytes = sum(
                    sum(sum(n.size for n in b) for b in s.retire_lists)
                    for s in self._thread_states.values()
                )
                if total_pending > self._peak_pending_count:
                    self._peak_pending_count = total_pending
                if total_bytes > self._peak_pending_bytes:
                    self._peak_pending_bytes = total_bytes

            # Trigger reclamation if threshold reached
            if state.retire_count >= self._retire_threshold:
                self._try_advance_epoch()
                self._poll_internal(state)

    def poll(self, thread_id: Optional[int] = None) -> int:
        """Poll for reclamation opportunities.

        Args:
            thread_id: Thread ID (default: current thread)

        Returns:
            Number of nodes reclaimed
        """
        if thread_id is None:
            thread_id = threading.get_ident()

        with self._lock:
            if thread_id not in self._thread_states:
                return 0

            self._try_advance_epoch()
            return self._poll_internal(self._thread_states[thread_id])

    def _try_advance_epoch(self) -> bool:
        """Try to advance the global epoch.

        Returns:
            True if epoch was advanced
        """
        current = self._global_epoch.load(MemoryOrder.ACQUIRE)
        safe_epoch = self._compute_safe_epoch()

        # Can only advance if all active threads have caught up
        if safe_epoch >= current:
            success, _ = self._global_epoch.compare_exchange_strong(
                current, current + 1,
                MemoryOrder.SEQ_CST, MemoryOrder.SEQ_CST
            )
            if success:
                if self._stats_enabled:
                    now = time.time()
                    duration = now - self._last_epoch_time
                    self._epoch_durations.append(duration)
                    self._last_epoch_time = now
                    self._epoch_advances += 1
                    self._record_event("advance", threading.get_ident(), current + 1)
                return True

        return False

    def _compute_safe_epoch(self) -> int:
        """Compute the safe epoch for reclamation.

        Returns:
            Minimum epoch across all active threads
        """
        min_epoch = self._global_epoch.load(MemoryOrder.ACQUIRE)

        for thread_id, active in self._thread_active.items():
            if active:
                epoch = self._thread_epochs.get(thread_id, min_epoch)
                if epoch < min_epoch:
                    min_epoch = epoch

        return min_epoch

    def _poll_internal(self, state: IBRThreadState) -> int:
        """Internal poll implementation.

        Args:
            state: Thread state to poll

        Returns:
            Number of nodes reclaimed
        """
        reclaimed = 0
        current_epoch = self._global_epoch.load(MemoryOrder.ACQUIRE)
        safe_epoch = self._compute_safe_epoch()

        self._poll_count += 1
        if self._stats_enabled:
            state.stats.poll_count += 1

        # Free nodes from epochs older than safe_epoch
        for bucket_idx in range(3):
            bucket = state.retire_lists[bucket_idx]
            remaining = []

            for node in bucket:
                if node.epoch < safe_epoch and reclaimed < self._max_reclaim_per_poll:
                    self._do_free(node)
                    reclaimed += 1
                    state.retire_count -= 1
                    self._reclaimed_count += 1

                    if self._stats_enabled:
                        state.stats.reclaim_count += 1
                        latency_ns = int((time.time() - node.retire_time) * 1e9)
                        self._reclaim_latencies.append(latency_ns)
                        self._record_event("reclaim", state.thread_id, current_epoch, {"size": node.size})
                else:
                    remaining.append(node)

            state.retire_lists[bucket_idx] = remaining

        if reclaimed == 0:
            self._empty_poll_count += 1

        return reclaimed

    def _do_free(self, node: RetiredNode) -> None:
        """Actually free a retired node.

        Args:
            node: Node to free
        """
        if node.free_fn:
            node.free_fn(node.obj, node.size)
        # Let Python GC handle the object

    def _record_event(self, event_type: str, thread_id: int, epoch: int, details: Optional[Dict] = None) -> None:
        """Record an event for profiling.

        Args:
            event_type: Type of event
            thread_id: Thread that triggered event
            epoch: Epoch at time of event
            details: Additional event details
        """
        if self._stats_enabled and len(self._timeline) < 100000:  # Limit timeline size
            self._timeline.append(EpochEvent(
                timestamp=time.time(),
                event_type=event_type,
                thread_id=thread_id,
                epoch=epoch,
                details=details,
            ))

    def is_stalled(self, thread_id: int) -> bool:
        """Check if a thread is stalled (blocking reclamation).

        Args:
            thread_id: Thread to check

        Returns:
            True if thread is stalled
        """
        if not self._thread_active.get(thread_id, False):
            return False

        global_epoch = self._global_epoch.load(MemoryOrder.ACQUIRE)
        thread_epoch = self._thread_epochs.get(thread_id, global_epoch)

        return (global_epoch - thread_epoch) > self._stall_threshold

    def get_epoch(self) -> int:
        """Get current global epoch.

        Returns:
            Current global epoch
        """
        return self._global_epoch.load(MemoryOrder.ACQUIRE)

    def pending_count(self, thread_id: Optional[int] = None) -> int:
        """Get count of pending retired nodes.

        Args:
            thread_id: Thread ID (default: all threads)

        Returns:
            Number of pending nodes
        """
        with self._lock:
            if thread_id is not None:
                if thread_id in self._thread_states:
                    return self._thread_states[thread_id].retire_count
                return 0

            return sum(s.retire_count for s in self._thread_states.values())

    def statistics(self) -> Dict[str, Any]:
        """Get IBR statistics.

        Returns:
            Dictionary with statistics
        """
        with self._lock:
            pending = sum(s.retire_count for s in self._thread_states.values())
            return {
                'global_epoch': self._global_epoch.load(),
                'registered_threads': len(self._thread_states),
                'pending_retired': pending,
                'total_retired': self._retired_count,
                'total_reclaimed': self._reclaimed_count,
                'epoch_advances': self._epoch_advances,
                'poll_count': self._poll_count,
                'empty_poll_pct': (
                    self._empty_poll_count / self._poll_count * 100
                    if self._poll_count > 0 else 0
                ),
            }


class IBRGuard:
    """Context manager for IBR critical sections.

    Usage:
        with IBRGuard(domain) as epoch:
            # Safe to read shared data
            value = node.value
    """

    __slots__ = ('_domain', '_thread_id')

    def __init__(self, domain: IBRDomain, thread_id: Optional[int] = None):
        """Initialize guard.

        Args:
            domain: IBR domain
            thread_id: Thread ID (default: current thread)
        """
        self._domain = domain
        self._thread_id = thread_id or threading.get_ident()

    def __enter__(self) -> int:
        """Enter critical section."""
        return self._domain.enter(self._thread_id)

    def __exit__(self, *args) -> None:
        """Exit critical section."""
        self._domain.exit(self._thread_id)


class SMRProfiler:
    """Profiler for SMR (IBR) analysis."""

    __slots__ = (
        '_domain',
        '_start_time',
        '_start_epoch',
        '_running',
        '_track_timeline',
        '_track_per_thread',
        '_track_latency',
        '_track_limbo_snapshots',
        '_snapshot_interval_ms',
        '_sample_rate',
        '_stall_threshold_epochs',
    )

    def __init__(
        self,
        domain: Optional[IBRDomain] = None,
        *,
        track_timeline: bool = False,
        track_per_thread: bool = True,
        track_latency: bool = True,
        track_limbo_snapshots: bool = False,
        snapshot_interval_ms: float = 100,
        sample_rate: float = 1.0,
        stall_threshold_epochs: int = 10,
    ):
        """Initialize SMR profiler.

        Args:
            domain: IBR domain to profile (default: global)
            track_timeline: Full event timeline (high overhead)
            track_per_thread: Per-thread statistics
            track_latency: Track reclaim latency
            track_limbo_snapshots: Periodic limbo snapshots
            snapshot_interval_ms: Interval for limbo snapshots
            sample_rate: Sampling rate (1.0 = all events)
            stall_threshold_epochs: Epochs before stall detection
        """
        self._domain = domain
        self._start_time: Optional[datetime] = None
        self._start_epoch = 0
        self._running = False
        self._track_timeline = track_timeline
        self._track_per_thread = track_per_thread
        self._track_latency = track_latency
        self._track_limbo_snapshots = track_limbo_snapshots
        self._snapshot_interval_ms = snapshot_interval_ms
        self._sample_rate = sample_rate
        self._stall_threshold_epochs = stall_threshold_epochs

    def __enter__(self) -> 'SMRProfiler':
        """Start profiling."""
        self.start()
        return self

    def __exit__(self, *args) -> None:
        """Stop profiling."""
        self.stop()

    def start(self) -> None:
        """Start profiling."""
        if self._domain is None:
            self._domain = get_default_ibr()

        self._domain._stats_enabled = True
        self._start_time = datetime.now()
        self._start_epoch = self._domain.get_epoch()
        self._running = True

    def stop(self) -> None:
        """Stop profiling."""
        self._running = False

    def snapshot(self) -> SMRProfilerReport:
        """Get current statistics without stopping.

        Returns:
            SMRProfilerReport with current stats
        """
        return self._generate_report()

    def report(self) -> SMRProfilerReport:
        """Get final report.

        Returns:
            Complete SMRProfilerReport
        """
        return self._generate_report()

    def reset(self) -> None:
        """Reset profiling statistics."""
        if self._domain:
            self._domain._retired_count = 0
            self._domain._reclaimed_count = 0
            self._domain._poll_count = 0
            self._domain._empty_poll_count = 0
            self._domain._epoch_advances = 0
            self._domain._stall_events.clear()
            self._domain._epoch_durations.clear()
            self._domain._reclaim_latencies.clear()
            self._domain._timeline.clear()

    def _generate_report(self) -> SMRProfilerReport:
        """Generate profiler report.

        Returns:
            SMRProfilerReport
        """
        if self._domain is None:
            return SMRProfilerReport()

        domain = self._domain
        now = datetime.now()
        end_epoch = domain.get_epoch()

        # Calculate latency percentiles
        latencies = sorted(domain._reclaim_latencies)
        p50 = p95 = p99 = p999 = max_lat = 0.0
        if latencies:
            p50 = latencies[int(len(latencies) * 0.50)]
            p95 = latencies[int(len(latencies) * 0.95)]
            p99 = latencies[int(len(latencies) * 0.99)]
            p999 = latencies[min(int(len(latencies) * 0.999), len(latencies) - 1)]
            max_lat = latencies[-1]

        # Calculate epoch duration average
        avg_epoch_duration = 0.0
        if domain._epoch_durations:
            avg_epoch_duration = sum(domain._epoch_durations) / len(domain._epoch_durations) * 1e9

        # Nodes per poll
        nodes_per_poll_avg = 0.0
        if domain._poll_count > 0:
            nodes_per_poll_avg = domain._reclaimed_count / domain._poll_count

        # Empty poll percentage
        empty_poll_pct = 0.0
        if domain._poll_count > 0:
            empty_poll_pct = domain._empty_poll_count / domain._poll_count * 100

        # Pending count
        pending = domain.pending_count()

        # Thread stats
        thread_stats = []
        if self._track_per_thread:
            for state in domain._thread_states.values():
                thread_stats.append(state.stats)

        # Duration
        duration = 0.0
        if self._start_time:
            duration = (now - self._start_time).total_seconds()

        return SMRProfilerReport(
            start_epoch=self._start_epoch,
            end_epoch=end_epoch,
            epoch_advances=domain._epoch_advances,
            avg_epoch_duration_ns=avg_epoch_duration,
            safe_epoch_lag_avg=0.0,  # Would need tracking
            safe_epoch_lag_max=0,
            total_retired=domain._retired_count,
            total_reclaimed=domain._reclaimed_count,
            pending_count=pending,
            pending_bytes=0,  # Would need tracking
            reclaim_latency_p50=p50,
            reclaim_latency_p95=p95,
            reclaim_latency_p99=p99,
            reclaim_latency_p999=p999,
            reclaim_latency_max=max_lat,
            poll_count=domain._poll_count,
            nodes_per_poll_avg=nodes_per_poll_avg,
            nodes_per_poll_max=0,
            empty_poll_pct=empty_poll_pct,
            peak_pending_count=domain._peak_pending_count,
            peak_pending_bytes=domain._peak_pending_bytes,
            memory_bound_utilization=0.0,
            thread_stats=thread_stats,
            stall_events=domain._stall_events.copy(),
            total_stall_time_ns=0,
            stall_count=len(domain._stall_events),
            epoch_timeline=domain._timeline.copy() if self._track_timeline else None,
            limbo_snapshots=None,
            duration_seconds=duration,
            start_time=self._start_time,
            end_time=now,
        )

    def analyze_stalls(self) -> List[Dict]:
        """Detailed stall analysis with recommendations.

        Returns:
            List of analysis dictionaries
        """
        if not self._domain or not self._domain._stall_events:
            return []

        return [
            {
                "pattern": "Epoch lag detected",
                "frequency": len(self._domain._stall_events),
                "recommendation": "Consider reducing critical section duration"
            }
        ]

    def find_slow_threads(self, threshold_epochs: int = 5) -> List[int]:
        """Find threads that frequently cause epoch lag.

        Args:
            threshold_epochs: Epoch lag threshold

        Returns:
            List of thread IDs
        """
        if not self._domain:
            return []

        slow_threads = []
        for thread_id, state in self._domain._thread_states.items():
            if state.stats.caused_stall_epochs >= threshold_epochs:
                slow_threads.append(thread_id)

        return slow_threads


# Global default IBR domain
_default_ibr: Optional[IBRDomain] = None
_ibr_lock = threading.Lock()


def get_default_ibr() -> IBRDomain:
    """Get the default IBR domain (creates if needed).

    Returns:
        Global IBRDomain instance
    """
    global _default_ibr
    if _default_ibr is None:
        with _ibr_lock:
            if _default_ibr is None:
                _default_ibr = IBRDomain()
    return _default_ibr


# Aliases for backward compatibility with _smr.py
SMRDomain = IBRDomain
SMRGuard = IBRGuard


def get_default_smr() -> IBRDomain:
    """Get the default SMR domain (alias for IBR).

    Returns:
        Global IBRDomain instance
    """
    return get_default_ibr()
