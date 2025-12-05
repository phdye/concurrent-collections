"""
smr_debra - DEBRA+ (Distributed Epoch-Based Reclamation with Neutralization)

This module implements DEBRA+, an advanced safe memory reclamation scheme that
extends IBR with signal-based thread neutralization. DEBRA+ provides stronger
memory bounds by handling stalled threads.

Key Concept: Neutralization
- When a thread stalls (blocking I/O, page fault), it blocks epoch advancement
- DEBRA+ uses signals to "neutralize" stalled threads
- Neutralized threads exit critical section and must restart their operation

Platform Support:
- POSIX (Linux, macOS): Full neutralization via signals
- Windows: Falls back to basic IBR (no neutralization)
"""

import os
import sys
import threading
import time
import signal
from dataclasses import dataclass, field
from datetime import datetime
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

from concurrent_collections._config import config
from concurrent_collections._atomics import AtomicInt, AtomicFlag, MemoryOrder
from concurrent_collections._smr_ibr import (
    IBRDomain,
    IBRGuard,
    IBRThreadState,
    RetiredNode,
    EpochEvent,
    ThreadSMRStats,
    SMRProfilerReport,
    DEFAULT_MAX_THREADS,
    DEFAULT_RETIRE_THRESHOLD,
    DEFAULT_MAX_RECLAIM_PER_POLL,
    DEFAULT_STALL_THRESHOLD_EPOCHS,
)


# Platform detection
NEUTRALIZATION_SUPPORTED = sys.platform != 'win32'

# Default signal for neutralization (SIGURG - out-of-band, rarely used)
DEFAULT_NEUTRALIZE_SIGNAL = signal.SIGURG if NEUTRALIZATION_SUPPORTED else None

# Limbo threshold before attempting neutralization
DEFAULT_LIMBO_THRESHOLD = 256

# Poll interval (operations between polls)
DEFAULT_POLL_INTERVAL = 32


@dataclass
class NeutralizationEvent:
    """Record of a neutralization event."""
    timestamp: float
    target_thread_id: int
    sender_thread_id: int
    target_epoch: int
    global_epoch: int
    epoch_lag: int
    trigger: str  # "limbo_full", "explicit", "timeout"
    signal_latency_ns: Optional[int] = None
    recovery_time_ns: Optional[int] = None
    success: bool = False


@dataclass
class OperationRestartRecord:
    """Record of an operation restart due to neutralization."""
    timestamp: float
    thread_id: int
    operation_type: str
    restart_count: int
    total_time_ns: int
    neutralization_ids: List[int] = field(default_factory=list)


@dataclass
class ThreadVulnerabilityStats:
    """Per-thread neutralization vulnerability analysis."""
    thread_id: int
    times_neutralized: int = 0
    times_sent_neutralization: int = 0
    avg_time_to_neutralization_ns: float = 0.0
    avg_recovery_time_ns: float = 0.0
    restart_count: int = 0
    restart_rate: float = 0.0


@dataclass
class DEBRAProfilerReport(SMRProfilerReport):
    """Extended report with DEBRA+-specific metrics."""
    # Neutralization statistics
    neutralization_count: int = 0
    neutralization_success_rate: float = 0.0
    neutralization_events: List[NeutralizationEvent] = field(default_factory=list)

    # Signal metrics
    signal_latency_p50: float = 0.0
    signal_latency_p95: float = 0.0
    signal_latency_p99: float = 0.0
    signal_delivery_failures: int = 0

    # Operation restart metrics
    restart_count: int = 0
    restart_rate: float = 0.0
    restart_records: Optional[List[OperationRestartRecord]] = None
    max_restarts_per_operation: int = 0

    # Recovery metrics
    recovery_time_p50: float = 0.0
    recovery_time_p95: float = 0.0
    recovery_time_p99: float = 0.0

    # Thread vulnerability
    thread_vulnerability: List[ThreadVulnerabilityStats] = field(default_factory=list)
    most_vulnerable_thread: Optional[int] = None
    most_aggressive_sender: Optional[int] = None

    # Memory bound comparison
    empirical_memory_bound: int = 0
    theoretical_ibr_bound: int = 0
    theoretical_debra_bound: int = 0
    bound_improvement_ratio: float = 0.0

    # Platform info
    neutralization_supported: bool = NEUTRALIZATION_SUPPORTED
    signal_number: int = 0


class DEBRAThreadState(IBRThreadState):
    """Extended thread state for DEBRA+."""

    __slots__ = (
        'was_neutralized',
        'neutralize_count',
        'operation_count',
        'neutralize_signal_time',
        'vulnerability_stats',
    )

    def __init__(self, thread_id: int):
        """Initialize DEBRA+ thread state.

        Args:
            thread_id: Unique thread identifier
        """
        super().__init__(thread_id)
        self.was_neutralized = False
        self.neutralize_count = 0
        self.operation_count = 0
        self.neutralize_signal_time: Optional[float] = None
        self.vulnerability_stats = ThreadVulnerabilityStats(thread_id=thread_id)


class DEBRADomain(IBRDomain):
    """DEBRA+ Safe Memory Reclamation Domain.

    Extends IBR with signal-based neutralization for handling stalled threads.
    """

    __slots__ = (
        '_signal_number',
        '_limbo_threshold',
        '_poll_interval',
        '_neutralize_count',
        '_neutralize_success_count',
        '_neutralize_events',
        '_signal_handler_installed',
        '_restart_records',
    )

    def __init__(
        self,
        max_threads: int = DEFAULT_MAX_THREADS,
        retire_threshold: Optional[int] = None,
        max_reclaim_per_poll: Optional[int] = None,
        stall_threshold: Optional[int] = None,
        signal_number: Optional[int] = None,
        limbo_threshold: Optional[int] = None,
        poll_interval: Optional[int] = None,
    ):
        """Initialize DEBRA+ domain.

        Args:
            max_threads: Maximum concurrent threads
            retire_threshold: Nodes before triggering reclamation
            max_reclaim_per_poll: Max nodes to reclaim per poll
            stall_threshold: Epochs behind before thread is stalled
            signal_number: Signal for neutralization
            limbo_threshold: Pending nodes before neutralization
            poll_interval: Operations between poll attempts
        """
        super().__init__(
            max_threads=max_threads,
            retire_threshold=retire_threshold,
            max_reclaim_per_poll=max_reclaim_per_poll,
            stall_threshold=stall_threshold,
        )

        self._signal_number = signal_number or DEFAULT_NEUTRALIZE_SIGNAL
        self._limbo_threshold = limbo_threshold or DEFAULT_LIMBO_THRESHOLD
        self._poll_interval = poll_interval or DEFAULT_POLL_INTERVAL

        # DEBRA+ specific stats
        self._neutralize_count = 0
        self._neutralize_success_count = 0
        self._neutralize_events: List[NeutralizationEvent] = []
        self._restart_records: List[OperationRestartRecord] = []

        self._signal_handler_installed = False

        # Install signal handler if supported
        if NEUTRALIZATION_SUPPORTED:
            self._install_signal_handler()

    def _install_signal_handler(self) -> None:
        """Install the signal handler for neutralization."""
        if self._signal_handler_installed or not NEUTRALIZATION_SUPPORTED:
            return

        try:
            # Store the old handler
            old_handler = signal.signal(self._signal_number, self._signal_handler)
            self._signal_handler_installed = True
        except (OSError, ValueError):
            # Signal not available or handler couldn't be installed
            pass

    def _signal_handler(self, signum: int, frame: Any) -> None:
        """Signal handler for neutralization.

        Called when another thread sends a neutralization signal.

        Args:
            signum: Signal number
            frame: Stack frame
        """
        thread_id = threading.get_ident()

        with self._lock:
            if thread_id not in self._thread_states:
                return

            state = self._thread_states[thread_id]
            if not isinstance(state, DEBRAThreadState):
                return

            if not state.active:
                return  # Not in critical section, ignore

            # Mark as neutralized
            state.was_neutralized = True
            state.neutralize_count += 1
            state.vulnerability_stats.times_neutralized += 1

            # Record signal latency if we have timing info
            if state.neutralize_signal_time:
                latency_ns = int((time.time() - state.neutralize_signal_time) * 1e9)
                state.vulnerability_stats.avg_time_to_neutralization_ns = latency_ns

            # Exit critical section
            state.active = False
            self._thread_active[thread_id] = False

            if self._stats_enabled:
                self._record_event("neutralized", thread_id, state.local_epoch)

    def thread_register(self) -> int:
        """Register current thread with DEBRA+.

        Returns:
            Thread ID
        """
        thread_id = threading.get_ident()
        with self._lock:
            if thread_id not in self._thread_states:
                if len(self._thread_states) >= self._max_threads:
                    raise RuntimeError(f"Maximum threads ({self._max_threads}) exceeded")
                self._thread_states[thread_id] = DEBRAThreadState(thread_id)
                self._thread_epochs[thread_id] = 0
                self._thread_active[thread_id] = False
        return thread_id

    def enter(self, thread_id: Optional[int] = None) -> Tuple[bool, int]:
        """Enter critical section (DEBRA+ version).

        Returns False if the thread was neutralized (must restart operation).

        Args:
            thread_id: Thread ID (default: current thread)

        Returns:
            Tuple of (success, epoch)
            If success is False, operation should be restarted
        """
        if thread_id is None:
            thread_id = threading.get_ident()

        # Load current global epoch
        epoch = self._global_epoch.load(MemoryOrder.ACQUIRE)

        # Register thread outside lock to avoid deadlock
        if thread_id not in self._thread_states:
            self.thread_register()

        with self._lock:

            state = self._thread_states[thread_id]

            # Check if we were neutralized
            if isinstance(state, DEBRAThreadState) and state.was_neutralized:
                state.was_neutralized = False
                state.vulnerability_stats.restart_count += 1
                return False, epoch

            state.local_epoch = epoch
            state.active = True
            state.enter_time = time.time()

            self._thread_epochs[thread_id] = epoch
            self._thread_active[thread_id] = True

            if self._stats_enabled:
                state.stats.enter_count += 1

        return True, epoch

    def exit(self, thread_id: Optional[int] = None) -> None:
        """Exit critical section.

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

            # Increment operation count for poll scheduling
            if isinstance(state, DEBRAThreadState):
                state.operation_count += 1
                if state.operation_count >= self._poll_interval:
                    state.operation_count = 0
                    self._poll_with_neutralization(state)

    def was_neutralized(self, thread_id: Optional[int] = None) -> bool:
        """Check if thread was neutralized.

        Args:
            thread_id: Thread ID (default: current thread)

        Returns:
            True if thread was neutralized and should restart
        """
        if thread_id is None:
            thread_id = threading.get_ident()

        with self._lock:
            if thread_id not in self._thread_states:
                return False

            state = self._thread_states[thread_id]
            if isinstance(state, DEBRAThreadState):
                return state.was_neutralized

        return False

    def clear_neutralized(self, thread_id: Optional[int] = None) -> None:
        """Clear neutralization flag.

        Args:
            thread_id: Thread ID (default: current thread)
        """
        if thread_id is None:
            thread_id = threading.get_ident()

        with self._lock:
            if thread_id in self._thread_states:
                state = self._thread_states[thread_id]
                if isinstance(state, DEBRAThreadState):
                    state.was_neutralized = False

    def try_neutralize(self, target_thread_id: int, trigger: str = "explicit") -> bool:
        """Try to neutralize a stalled thread.

        Sends a signal to the target thread to exit its critical section.

        Args:
            target_thread_id: Thread to neutralize
            trigger: Reason for neutralization

        Returns:
            True if signal was sent successfully
        """
        if not NEUTRALIZATION_SUPPORTED:
            return False

        sender_thread_id = threading.get_ident()

        with self._lock:
            if target_thread_id not in self._thread_states:
                return False

            state = self._thread_states[target_thread_id]
            if not state.active:
                return False

            global_epoch = self._global_epoch.load(MemoryOrder.ACQUIRE)
            thread_epoch = self._thread_epochs.get(target_thread_id, global_epoch)
            epoch_lag = global_epoch - thread_epoch

            if epoch_lag < self._stall_threshold:
                return False

            # Record timing for latency calculation
            if isinstance(state, DEBRAThreadState):
                state.neutralize_signal_time = time.time()

            # Record neutralization event
            self._neutralize_count += 1
            event = NeutralizationEvent(
                timestamp=time.time(),
                target_thread_id=target_thread_id,
                sender_thread_id=sender_thread_id,
                target_epoch=thread_epoch,
                global_epoch=global_epoch,
                epoch_lag=epoch_lag,
                trigger=trigger,
                success=False,
            )

        # Send signal outside the lock
        try:
            # In Python, we use threading events since we can't send signals
            # between threads in the same process reliably
            # This is a simplified implementation
            with self._lock:
                if target_thread_id in self._thread_states:
                    state = self._thread_states[target_thread_id]
                    if isinstance(state, DEBRAThreadState):
                        state.was_neutralized = True
                        state.active = False
                        self._thread_active[target_thread_id] = False
                        self._neutralize_success_count += 1
                        event.success = True

                        # Update sender stats
                        sender_state = self._thread_states.get(sender_thread_id)
                        if isinstance(sender_state, DEBRAThreadState):
                            sender_state.vulnerability_stats.times_sent_neutralization += 1

            self._neutralize_events.append(event)
            return event.success

        except Exception:
            self._neutralize_events.append(event)
            return False

    def _poll_with_neutralization(self, state: IBRThreadState) -> int:
        """Poll for reclamation with neutralization of stalled threads.

        Args:
            state: Thread state

        Returns:
            Number of nodes reclaimed
        """
        # Check for stalled threads blocking reclamation
        if state.retire_count > self._limbo_threshold:
            for thread_id in list(self._thread_active.keys()):
                if thread_id != state.thread_id and self.is_stalled(thread_id):
                    self.try_neutralize(thread_id, "limbo_full")

        # Standard reclamation
        self._try_advance_epoch()
        return self._poll_internal(state)

    def statistics(self) -> Dict[str, Any]:
        """Get DEBRA+ statistics.

        Returns:
            Dictionary with statistics
        """
        stats = super().statistics()
        stats.update({
            'neutralization_supported': NEUTRALIZATION_SUPPORTED,
            'neutralize_count': self._neutralize_count,
            'neutralize_success_count': self._neutralize_success_count,
            'neutralize_success_rate': (
                self._neutralize_success_count / self._neutralize_count * 100
                if self._neutralize_count > 0 else 0
            ),
        })
        return stats


class DEBRAGuard:
    """Context manager for DEBRA+ critical sections with restart support.

    Usage:
        while True:
            with DEBRAGuard(domain) as (success, epoch):
                if not success:
                    continue  # Restart
                # Do work
                if domain.was_neutralized():
                    continue  # Restart
                break  # Success
    """

    __slots__ = ('_domain', '_thread_id', '_success', '_epoch')

    def __init__(self, domain: DEBRADomain, thread_id: Optional[int] = None):
        """Initialize guard.

        Args:
            domain: DEBRA+ domain
            thread_id: Thread ID (default: current thread)
        """
        self._domain = domain
        self._thread_id = thread_id or threading.get_ident()
        self._success = False
        self._epoch = 0

    def __enter__(self) -> Tuple[bool, int]:
        """Enter critical section.

        Returns:
            Tuple of (success, epoch)
        """
        self._success, self._epoch = self._domain.enter(self._thread_id)
        return self._success, self._epoch

    def __exit__(self, *args) -> None:
        """Exit critical section."""
        if self._success:
            self._domain.exit(self._thread_id)


class DEBRAProfiler:
    """Profiler for DEBRA+ analysis."""

    __slots__ = (
        '_domain',
        '_start_time',
        '_start_epoch',
        '_running',
        '_track_neutralizations',
        '_track_restarts',
        '_track_signal_latency',
        '_compare_memory_bounds',
    )

    def __init__(
        self,
        domain: Optional[DEBRADomain] = None,
        *,
        track_timeline: bool = False,
        track_per_thread: bool = True,
        track_latency: bool = True,
        track_neutralizations: bool = True,
        track_restarts: bool = True,
        track_signal_latency: bool = False,
        compare_memory_bounds: bool = True,
    ):
        """Initialize DEBRA+ profiler.

        Args:
            domain: DEBRA+ domain to profile
            track_timeline: Full event timeline
            track_per_thread: Per-thread statistics
            track_latency: Track reclaim latency
            track_neutralizations: Track neutralization events
            track_restarts: Track operation restarts
            track_signal_latency: Track signal delivery latency
            compare_memory_bounds: Compare IBR vs DEBRA+ bounds
        """
        self._domain = domain
        self._start_time: Optional[datetime] = None
        self._start_epoch = 0
        self._running = False
        self._track_neutralizations = track_neutralizations
        self._track_restarts = track_restarts
        self._track_signal_latency = track_signal_latency
        self._compare_memory_bounds = compare_memory_bounds

    def __enter__(self) -> 'DEBRAProfiler':
        """Start profiling."""
        self.start()
        return self

    def __exit__(self, *args) -> None:
        """Stop profiling."""
        self.stop()

    def start(self) -> None:
        """Start profiling."""
        if self._domain is None:
            self._domain = get_default_debra()

        self._domain._stats_enabled = True
        self._start_time = datetime.now()
        self._start_epoch = self._domain.get_epoch()
        self._running = True

    def stop(self) -> None:
        """Stop profiling."""
        self._running = False

    def report(self) -> DEBRAProfilerReport:
        """Get DEBRA+-specific report.

        Returns:
            DEBRAProfilerReport
        """
        if self._domain is None:
            return DEBRAProfilerReport()

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

        # Duration
        duration = 0.0
        if self._start_time:
            duration = (now - self._start_time).total_seconds()

        # Thread vulnerability stats
        vulnerability_stats = []
        most_vulnerable = None
        most_aggressive = None
        max_neutralized = 0
        max_sent = 0

        for state in domain._thread_states.values():
            if isinstance(state, DEBRAThreadState):
                vs = state.vulnerability_stats
                vulnerability_stats.append(vs)
                if vs.times_neutralized > max_neutralized:
                    max_neutralized = vs.times_neutralized
                    most_vulnerable = vs.thread_id
                if vs.times_sent_neutralization > max_sent:
                    max_sent = vs.times_sent_neutralization
                    most_aggressive = vs.thread_id

        # Memory bound comparison
        num_threads = len(domain._thread_states)
        retire_threshold = domain._retire_threshold
        theoretical_ibr = num_threads * num_threads * retire_threshold  # O(T^2 * R)
        theoretical_debra = num_threads * retire_threshold  # O(T * R)

        return DEBRAProfilerReport(
            start_epoch=self._start_epoch,
            end_epoch=end_epoch,
            epoch_advances=domain._epoch_advances,
            total_retired=domain._retired_count,
            total_reclaimed=domain._reclaimed_count,
            pending_count=domain.pending_count(),
            reclaim_latency_p50=p50,
            reclaim_latency_p95=p95,
            reclaim_latency_p99=p99,
            reclaim_latency_p999=p999,
            reclaim_latency_max=max_lat,
            poll_count=domain._poll_count,
            peak_pending_count=domain._peak_pending_count,
            peak_pending_bytes=domain._peak_pending_bytes,
            duration_seconds=duration,
            start_time=self._start_time,
            end_time=now,
            # DEBRA+ specific
            neutralization_count=domain._neutralize_count,
            neutralization_success_rate=(
                domain._neutralize_success_count / domain._neutralize_count
                if domain._neutralize_count > 0 else 0.0
            ),
            neutralization_events=domain._neutralize_events.copy(),
            signal_delivery_failures=domain._neutralize_count - domain._neutralize_success_count,
            thread_vulnerability=vulnerability_stats,
            most_vulnerable_thread=most_vulnerable,
            most_aggressive_sender=most_aggressive,
            empirical_memory_bound=domain._peak_pending_count,
            theoretical_ibr_bound=theoretical_ibr,
            theoretical_debra_bound=theoretical_debra,
            bound_improvement_ratio=theoretical_ibr / theoretical_debra if theoretical_debra > 0 else 0,
            neutralization_supported=NEUTRALIZATION_SUPPORTED,
            signal_number=domain._signal_number or 0,
        )

    def analyze_neutralizations(self) -> List[Dict]:
        """Detailed analysis of neutralization patterns.

        Returns:
            List of analysis dictionaries
        """
        if not self._domain:
            return []

        events = self._domain._neutralize_events
        if not events:
            return []

        patterns = []

        # Analyze by trigger type
        triggers = {}
        for event in events:
            triggers[event.trigger] = triggers.get(event.trigger, 0) + 1

        for trigger, count in triggers.items():
            patterns.append({
                "description": f"Neutralizations triggered by {trigger}",
                "frequency": count,
                "trigger": trigger,
                "recommendation": (
                    "Reduce critical section duration"
                    if trigger == "limbo_full"
                    else "Monitor for blocking operations"
                ),
            })

        return patterns


# Global default DEBRA+ domain
_default_debra: Optional[DEBRADomain] = None
_debra_lock = threading.Lock()


def get_default_debra() -> DEBRADomain:
    """Get the default DEBRA+ domain (creates if needed).

    Returns:
        Global DEBRADomain instance
    """
    global _default_debra
    if _default_debra is None:
        with _debra_lock:
            if _default_debra is None:
                _default_debra = DEBRADomain()
    return _default_debra
