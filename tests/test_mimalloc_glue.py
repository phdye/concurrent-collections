"""Tests for mimalloc_glue module."""

import threading
import time
import pytest

from concurrent_collections._mimalloc_glue import (
    Allocator,
    AllocatorStats,
    AllocationSnapshot,
    ThreadMemoryStats,
    AllocationRecord,
    cc_alloc,
    cc_calloc,
    cc_alloc_aligned,
    cc_alloc_node,
    cc_free,
    alloc_stats_enable,
    alloc_stats_disable,
    alloc_stats_reset,
    alloc_stats_snapshot,
    alloc_stats_thread_breakdown,
    alloc_stats_leaked,
    get_allocator,
    CACHE_LINE_SIZE,
)


class TestAllocator:
    """Tests for Allocator class."""

    def test_basic_alloc(self):
        """Test basic allocation."""
        alloc = Allocator()
        ptr = alloc.alloc(64)
        assert ptr is not None
        assert len(ptr) == 64

    def test_alloc_zero_size(self):
        """Test allocation with zero size returns None."""
        alloc = Allocator()
        ptr = alloc.alloc(0)
        assert ptr is None

    def test_alloc_negative_size(self):
        """Test allocation with negative size returns None."""
        alloc = Allocator()
        ptr = alloc.alloc(-1)
        assert ptr is None

    def test_calloc(self):
        """Test calloc allocates zeroed memory."""
        alloc = Allocator()
        ptr = alloc.calloc(10, 8)
        assert ptr is not None
        assert len(ptr) == 80
        # Memory should be zeroed
        assert all(b == 0 for b in ptr)

    def test_alloc_aligned(self):
        """Test aligned allocation."""
        alloc = Allocator()
        ptr = alloc.alloc_aligned(100, 64)
        assert ptr is not None
        # Size should be rounded up to alignment
        assert len(ptr) >= 100

    def test_alloc_node(self):
        """Test cache-line aligned node allocation."""
        alloc = Allocator()
        ptr = alloc.alloc_node(48)
        assert ptr is not None
        assert len(ptr) >= 48

    def test_free(self):
        """Test free operation."""
        alloc = Allocator()
        ptr = alloc.alloc(64)
        # Free should not raise
        alloc.free(ptr, 64)

    def test_free_none(self):
        """Test free with None is safe."""
        alloc = Allocator()
        alloc.free(None)  # Should not raise


class TestAllocatorStats:
    """Tests for AllocatorStats class."""

    def setup_method(self):
        """Reset stats before each test."""
        alloc_stats_reset()

    def test_stats_initially_disabled(self):
        """Test stats are disabled by default."""
        stats = AllocatorStats()
        assert not stats.enabled

    def test_enable_disable(self):
        """Test enabling and disabling stats."""
        stats = AllocatorStats()
        stats.enable()
        assert stats.enabled
        stats.disable()
        assert not stats.enabled

    def test_record_alloc(self):
        """Test recording allocations."""
        stats = AllocatorStats()
        stats.enable()
        stats.record_alloc(12345, 64, 1)

        snapshot = stats.snapshot()
        assert snapshot.alloc_count == 1
        assert snapshot.alloc_bytes == 64

    def test_record_free(self):
        """Test recording frees."""
        stats = AllocatorStats()
        stats.enable()
        stats.record_alloc(12345, 64, 1)
        stats.record_free(12345, 64, 1)

        snapshot = stats.snapshot()
        assert snapshot.alloc_count == 1
        assert snapshot.free_count == 1
        assert snapshot.current_allocated == 0

    def test_peak_tracking(self):
        """Test peak memory tracking."""
        stats = AllocatorStats()
        stats.enable()

        stats.record_alloc(1, 100, 1)
        stats.record_alloc(2, 200, 1)
        stats.record_free(1, 100, 1)

        snapshot = stats.snapshot()
        assert snapshot.peak_allocated == 300
        assert snapshot.current_allocated == 200

    def test_cross_thread_tracking(self):
        """Test cross-thread free tracking."""
        stats = AllocatorStats()
        stats.enable()

        # Thread 1 allocates
        stats.record_alloc(1, 64, 1)
        # Thread 2 frees
        stats.record_free(1, 64, 2, alloc_thread_id=1)

        thread_stats = stats.get_thread_stats()
        # Thread 2 should have cross_thread_frees_received
        t2_stats = next((ts for ts in thread_stats if ts.thread_id == 2), None)
        assert t2_stats is not None
        assert t2_stats.cross_thread_frees_received == 1

    def test_leak_tracking(self):
        """Test leak detection."""
        stats = AllocatorStats()
        stats.enable(track_leaks=True)

        stats.record_alloc(1, 64, 1)
        stats.record_alloc(2, 128, 1)
        stats.record_free(1, 64, 1)

        leaked = stats.get_leaked_allocations()
        assert len(leaked) == 1
        assert leaked[0].ptr_id == 2
        assert leaked[0].size == 128

    def test_reset(self):
        """Test stats reset."""
        stats = AllocatorStats()
        stats.enable()
        stats.record_alloc(1, 64, 1)
        stats.reset()

        snapshot = stats.snapshot()
        assert snapshot.alloc_count == 0
        assert snapshot.alloc_bytes == 0


class TestGlobalFunctions:
    """Tests for global allocator functions."""

    def setup_method(self):
        """Reset stats before each test."""
        alloc_stats_reset()

    def test_cc_alloc(self):
        """Test global cc_alloc."""
        ptr = cc_alloc(64)
        assert ptr is not None
        assert len(ptr) == 64

    def test_cc_calloc(self):
        """Test global cc_calloc."""
        ptr = cc_calloc(10, 8)
        assert ptr is not None
        assert len(ptr) == 80

    def test_cc_alloc_aligned(self):
        """Test global cc_alloc_aligned."""
        ptr = cc_alloc_aligned(100, 64)
        assert ptr is not None

    def test_cc_alloc_node(self):
        """Test global cc_alloc_node."""
        ptr = cc_alloc_node(48)
        assert ptr is not None

    def test_cc_free(self):
        """Test global cc_free."""
        ptr = cc_alloc(64)
        cc_free(ptr, 64)  # Should not raise

    def test_stats_api(self):
        """Test global stats API."""
        alloc_stats_enable()

        ptr = cc_alloc(64)
        snapshot = alloc_stats_snapshot()
        assert snapshot.alloc_count >= 1

        cc_free(ptr, 64)
        snapshot = alloc_stats_snapshot()
        assert snapshot.free_count >= 1

        alloc_stats_disable()


class TestAllocationSnapshot:
    """Tests for AllocationSnapshot dataclass."""

    def test_current_count(self):
        """Test current_count property."""
        snapshot = AllocationSnapshot(
            alloc_count=10,
            free_count=7,
            alloc_bytes=1000,
            free_bytes=700,
            current_allocated=300,
            peak_allocated=500,
        )
        assert snapshot.current_count == 3


class TestConcurrency:
    """Concurrency tests for allocator."""

    def test_concurrent_alloc_free(self):
        """Test concurrent allocation and freeing."""
        alloc_stats_enable()
        alloc_stats_reset()

        barrier = threading.Barrier(4)
        errors = []

        def worker():
            try:
                barrier.wait()
                for _ in range(100):
                    ptr = cc_alloc(64)
                    time.sleep(0.0001)  # Small delay
                    cc_free(ptr, 64)
            except Exception as e:
                errors.append(e)

        threads = [threading.Thread(target=worker) for _ in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert not errors

        snapshot = alloc_stats_snapshot()
        assert snapshot.alloc_count == 400
        assert snapshot.free_count == 400

    def test_cross_thread_free(self):
        """Test freeing memory from different thread."""
        ptrs = []

        def alloc_thread():
            for _ in range(10):
                ptrs.append(cc_alloc(64))

        def free_thread():
            time.sleep(0.01)  # Let alloc thread run first
            while ptrs:
                ptr = ptrs.pop()
                cc_free(ptr, 64)

        t1 = threading.Thread(target=alloc_thread)
        t2 = threading.Thread(target=free_thread)

        t1.start()
        t1.join()
        t2.start()
        t2.join()

        # No errors means cross-thread free worked


class TestCacheLineSize:
    """Tests for cache line size constant."""

    def test_cache_line_size_value(self):
        """Test cache line size is reasonable."""
        assert CACHE_LINE_SIZE in [32, 64, 128]  # Common cache line sizes
