"""
mimalloc_glue - Memory allocation abstraction layer

This module provides a thin abstraction layer over memory allocation for
node allocation in lock-free data structures. In Python, we leverage Python's
memory management but provide allocation statistics and tracking.

In a native extension implementation, this would wrap mimalloc for efficient
thread-local heaps and cross-thread free handling.
"""

import threading
import time
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Callable
from collections import defaultdict


# Cache line size for alignment
CACHE_LINE_SIZE = 64


@dataclass
class AllocationRecord:
    """Record of an individual allocation (for leak detection)."""
    ptr_id: int
    size: int
    timestamp: float
    thread_id: int
    stack_trace: Optional[List[str]] = None


@dataclass
class AllocationSnapshot:
    """Point-in-time allocation statistics."""
    alloc_count: int
    free_count: int
    alloc_bytes: int
    free_bytes: int
    current_allocated: int
    peak_allocated: int

    @property
    def current_count(self) -> int:
        """Number of currently allocated blocks."""
        return self.alloc_count - self.free_count


@dataclass
class ThreadMemoryStats:
    """Per-thread memory statistics."""
    thread_id: int
    alloc_count: int = 0
    free_count: int = 0
    alloc_bytes: int = 0
    free_bytes: int = 0
    cross_thread_frees_sent: int = 0
    cross_thread_frees_received: int = 0


class AllocatorStats:
    """Thread-safe allocation statistics collector."""

    __slots__ = (
        '_lock',
        '_enabled',
        '_alloc_count',
        '_free_count',
        '_alloc_bytes',
        '_free_bytes',
        '_peak_bytes',
        '_thread_stats',
        '_allocations',
        '_track_leaks',
    )

    def __init__(self):
        """Initialize statistics collector."""
        self._lock = threading.Lock()
        self._enabled = False
        self._alloc_count = 0
        self._free_count = 0
        self._alloc_bytes = 0
        self._free_bytes = 0
        self._peak_bytes = 0
        self._thread_stats: Dict[int, ThreadMemoryStats] = {}
        self._allocations: Dict[int, AllocationRecord] = {}
        self._track_leaks = False

    def enable(self, track_leaks: bool = False) -> None:
        """Enable statistics collection.

        Args:
            track_leaks: If True, track individual allocations for leak detection
        """
        with self._lock:
            self._enabled = True
            self._track_leaks = track_leaks

    def disable(self) -> None:
        """Disable statistics collection."""
        with self._lock:
            self._enabled = False

    def reset(self) -> None:
        """Reset all statistics."""
        with self._lock:
            self._alloc_count = 0
            self._free_count = 0
            self._alloc_bytes = 0
            self._free_bytes = 0
            self._peak_bytes = 0
            self._thread_stats.clear()
            self._allocations.clear()

    def record_alloc(self, ptr_id: int, size: int, thread_id: int) -> None:
        """Record an allocation.

        Args:
            ptr_id: Unique identifier for the allocation (id() of object)
            size: Size of allocation in bytes
            thread_id: Thread that performed the allocation
        """
        if not self._enabled:
            return

        with self._lock:
            self._alloc_count += 1
            self._alloc_bytes += size

            current = self._alloc_bytes - self._free_bytes
            if current > self._peak_bytes:
                self._peak_bytes = current

            # Thread stats
            if thread_id not in self._thread_stats:
                self._thread_stats[thread_id] = ThreadMemoryStats(thread_id=thread_id)
            ts = self._thread_stats[thread_id]
            ts.alloc_count += 1
            ts.alloc_bytes += size

            # Leak tracking
            if self._track_leaks:
                self._allocations[ptr_id] = AllocationRecord(
                    ptr_id=ptr_id,
                    size=size,
                    timestamp=time.time(),
                    thread_id=thread_id,
                )

    def record_free(self, ptr_id: int, size: int, thread_id: int, alloc_thread_id: Optional[int] = None) -> None:
        """Record a free operation.

        Args:
            ptr_id: Unique identifier for the allocation
            size: Size of allocation in bytes
            thread_id: Thread performing the free
            alloc_thread_id: Thread that originally allocated (for cross-thread tracking)
        """
        if not self._enabled:
            return

        with self._lock:
            self._free_count += 1
            self._free_bytes += size

            # Thread stats
            if thread_id not in self._thread_stats:
                self._thread_stats[thread_id] = ThreadMemoryStats(thread_id=thread_id)
            ts = self._thread_stats[thread_id]
            ts.free_count += 1
            ts.free_bytes += size

            # Cross-thread tracking
            if alloc_thread_id is not None and alloc_thread_id != thread_id:
                ts.cross_thread_frees_received += 1
                if alloc_thread_id in self._thread_stats:
                    self._thread_stats[alloc_thread_id].cross_thread_frees_sent += 1

            # Leak tracking
            if self._track_leaks and ptr_id in self._allocations:
                del self._allocations[ptr_id]

    def snapshot(self) -> AllocationSnapshot:
        """Get current statistics snapshot.

        Returns:
            AllocationSnapshot with current statistics
        """
        with self._lock:
            return AllocationSnapshot(
                alloc_count=self._alloc_count,
                free_count=self._free_count,
                alloc_bytes=self._alloc_bytes,
                free_bytes=self._free_bytes,
                current_allocated=self._alloc_bytes - self._free_bytes,
                peak_allocated=self._peak_bytes,
            )

    def get_thread_stats(self) -> List[ThreadMemoryStats]:
        """Get per-thread statistics.

        Returns:
            List of ThreadMemoryStats for each thread
        """
        with self._lock:
            return list(self._thread_stats.values())

    def get_leaked_allocations(self) -> List[AllocationRecord]:
        """Get allocations that haven't been freed.

        Returns:
            List of AllocationRecords for potentially leaked allocations
        """
        with self._lock:
            return list(self._allocations.values())

    @property
    def enabled(self) -> bool:
        """Check if statistics collection is enabled."""
        return self._enabled


# Global statistics instance
_global_stats = AllocatorStats()


class Allocator:
    """Memory allocator abstraction.

    In Python, this wraps object creation with optional statistics tracking.
    In a native extension, this would wrap mimalloc operations.
    """

    __slots__ = ('_stats', '_thread_allocations')

    def __init__(self, stats: Optional[AllocatorStats] = None):
        """Initialize allocator.

        Args:
            stats: Statistics collector (default: global stats)
        """
        self._stats = stats or _global_stats
        # Track which thread allocated each object for cross-thread free detection
        self._thread_allocations: Dict[int, int] = {}

    def alloc(self, size: int) -> Optional[bytearray]:
        """Allocate memory.

        In Python, this creates a bytearray. In native code, this would
        call mi_malloc.

        Args:
            size: Size in bytes

        Returns:
            Allocated memory or None on failure
        """
        if size <= 0:
            return None

        try:
            ptr = bytearray(size)
            ptr_id = id(ptr)
            thread_id = threading.get_ident()

            self._thread_allocations[ptr_id] = thread_id
            self._stats.record_alloc(ptr_id, size, thread_id)

            return ptr
        except MemoryError:
            return None

    def alloc_aligned(self, size: int, alignment: int = CACHE_LINE_SIZE) -> Optional[bytearray]:
        """Allocate aligned memory.

        Args:
            size: Size in bytes
            alignment: Alignment requirement (default: cache line size)

        Returns:
            Allocated memory or None on failure
        """
        # In Python, we can't control alignment directly
        # In native code, this would call mi_malloc_aligned
        aligned_size = ((size + alignment - 1) // alignment) * alignment
        return self.alloc(aligned_size)

    def calloc(self, count: int, size: int) -> Optional[bytearray]:
        """Allocate zeroed memory.

        Args:
            count: Number of elements
            size: Size of each element

        Returns:
            Zeroed memory or None on failure
        """
        return self.alloc(count * size)

    def free(self, ptr: Any, size: int = 0) -> None:
        """Free memory.

        In Python, this just removes our reference and records stats.
        In native code, this would call mi_free.

        Args:
            ptr: Memory to free
            size: Size hint (for statistics)
        """
        if ptr is None:
            return

        ptr_id = id(ptr)
        thread_id = threading.get_ident()
        alloc_thread_id = self._thread_allocations.pop(ptr_id, None)

        self._stats.record_free(ptr_id, size, thread_id, alloc_thread_id)

    def alloc_node(self, size: int) -> Optional[bytearray]:
        """Allocate cache-line aligned node.

        Args:
            size: Size in bytes

        Returns:
            Aligned memory or None on failure
        """
        return self.alloc_aligned(size, CACHE_LINE_SIZE)


# Global allocator instance
_global_allocator: Optional[Allocator] = None
_allocator_lock = threading.Lock()


def get_allocator() -> Allocator:
    """Get the global allocator instance.

    Returns:
        Global Allocator instance
    """
    global _global_allocator
    if _global_allocator is None:
        with _allocator_lock:
            if _global_allocator is None:
                _global_allocator = Allocator()
    return _global_allocator


def cc_alloc(size: int) -> Optional[bytearray]:
    """Allocate memory using the global allocator.

    Args:
        size: Size in bytes

    Returns:
        Allocated memory or None
    """
    return get_allocator().alloc(size)


def cc_alloc_aligned(size: int, alignment: int = CACHE_LINE_SIZE) -> Optional[bytearray]:
    """Allocate aligned memory.

    Args:
        size: Size in bytes
        alignment: Alignment requirement

    Returns:
        Aligned memory or None
    """
    return get_allocator().alloc_aligned(size, alignment)


def cc_calloc(count: int, size: int) -> Optional[bytearray]:
    """Allocate zeroed memory.

    Args:
        count: Number of elements
        size: Size per element

    Returns:
        Zeroed memory or None
    """
    return get_allocator().calloc(count, size)


def cc_free(ptr: Any, size: int = 0) -> None:
    """Free memory.

    Args:
        ptr: Memory to free
        size: Size hint for statistics
    """
    get_allocator().free(ptr, size)


def cc_alloc_node(size: int) -> Optional[bytearray]:
    """Allocate cache-line aligned node.

    Args:
        size: Size in bytes

    Returns:
        Aligned memory or None
    """
    return get_allocator().alloc_node(size)


# Statistics API
def alloc_stats_enable(track_leaks: bool = False) -> None:
    """Enable allocation statistics.

    Args:
        track_leaks: If True, track individual allocations for leak detection
    """
    _global_stats.enable(track_leaks)


def alloc_stats_disable() -> None:
    """Disable allocation statistics."""
    _global_stats.disable()


def alloc_stats_reset() -> None:
    """Reset allocation statistics."""
    _global_stats.reset()


def alloc_stats_snapshot() -> AllocationSnapshot:
    """Get allocation statistics snapshot.

    Returns:
        AllocationSnapshot with current stats
    """
    return _global_stats.snapshot()


def alloc_stats_thread_breakdown() -> List[ThreadMemoryStats]:
    """Get per-thread allocation statistics.

    Returns:
        List of ThreadMemoryStats
    """
    return _global_stats.get_thread_stats()


def alloc_stats_leaked() -> List[AllocationRecord]:
    """Get potentially leaked allocations.

    Note: Must have enabled statistics with track_leaks=True

    Returns:
        List of AllocationRecords for unfreed allocations
    """
    return _global_stats.get_leaked_allocations()
