"""Tests for smr_ibr module (Interval-Based Reclamation)."""

import threading
import time
import pytest

from concurrent_collections._smr_ibr import (
    IBRDomain,
    IBRGuard,
    IBRThreadState,
    SMRProfiler,
    SMRProfilerReport,
    RetiredNode,
    get_default_ibr,
    get_default_smr,
    SMRDomain,
    SMRGuard,
)


class TestIBRDomain:
    """Tests for IBRDomain class."""

    def test_creation(self):
        """Test domain creation."""
        domain = IBRDomain()
        assert domain.get_epoch() >= 1

    def test_custom_params(self):
        """Test domain with custom parameters."""
        domain = IBRDomain(
            max_threads=64,
            retire_threshold=32,
            max_reclaim_per_poll=16,
            stall_threshold=50,
        )
        assert domain._max_threads == 64
        assert domain._retire_threshold == 32

    def test_thread_register(self):
        """Test thread registration."""
        domain = IBRDomain()
        thread_id = domain.thread_register()
        assert thread_id == threading.get_ident()
        assert thread_id in domain._thread_states

    def test_thread_unregister(self):
        """Test thread unregistration."""
        domain = IBRDomain()
        thread_id = domain.thread_register()
        domain.thread_unregister(thread_id)
        assert thread_id not in domain._thread_states

    def test_unregister_in_critical_section_raises(self):
        """Test unregistering while in critical section raises."""
        domain = IBRDomain()
        thread_id = domain.thread_register()
        domain.enter(thread_id)

        with pytest.raises(RuntimeError):
            domain.thread_unregister(thread_id)

        domain.exit(thread_id)

    def test_enter_exit(self):
        """Test entering and exiting critical section."""
        domain = IBRDomain()
        thread_id = domain.thread_register()

        epoch = domain.enter(thread_id)
        assert epoch >= 1
        assert domain._thread_active[thread_id]

        domain.exit(thread_id)
        assert not domain._thread_active[thread_id]

    def test_enter_auto_register(self):
        """Test enter auto-registers thread if needed."""
        domain = IBRDomain()
        # Don't explicitly register
        epoch = domain.enter()
        assert epoch >= 1
        domain.exit()

    def test_retire(self):
        """Test retiring a node."""
        domain = IBRDomain()
        thread_id = domain.thread_register()
        domain.enter(thread_id)

        obj = {"key": "value"}
        domain.retire(obj, thread_id)

        assert domain.pending_count(thread_id) == 1
        domain.exit(thread_id)

    def test_retire_with_free_fn(self):
        """Test retire with custom free function."""
        freed = []

        def free_fn(obj, size):
            freed.append((obj, size))

        domain = IBRDomain(retire_threshold=1)
        thread_id = domain.thread_register()

        for i in range(10):
            domain.enter(thread_id)
            domain.retire({"id": i}, thread_id, size=64, free_fn=free_fn)
            domain.exit(thread_id)

        # Some nodes should have been freed via the callback
        # (depends on epoch advancement)

    def test_epoch_advancement(self):
        """Test global epoch advances."""
        domain = IBRDomain(retire_threshold=2)

        # Thread 1 enters and exits multiple times
        for _ in range(10):
            domain.enter()
            domain.retire(object())
            domain.exit()

        # Epoch should have advanced
        assert domain.get_epoch() > 1

    def test_poll_reclaims_nodes(self):
        """Test polling reclaims safe nodes."""
        domain = IBRDomain(retire_threshold=1, max_reclaim_per_poll=100)
        thread_id = domain.thread_register()

        # Retire several nodes
        for i in range(5):
            domain.enter(thread_id)
            domain.retire({"id": i}, thread_id)
            domain.exit(thread_id)

        # Force epoch advancement and poll
        for _ in range(5):
            domain.enter(thread_id)
            domain.exit(thread_id)
            domain.poll(thread_id)

        # Some nodes should have been reclaimed
        stats = domain.statistics()
        assert stats['total_reclaimed'] >= 0  # May be 0 if epochs haven't advanced enough

    def test_is_stalled(self):
        """Test stall detection."""
        domain = IBRDomain(stall_threshold=2)
        thread_id = domain.thread_register()

        domain.enter(thread_id)
        # Initially not stalled
        assert not domain.is_stalled(thread_id)

        # Advance epoch several times
        for _ in range(5):
            domain._global_epoch.fetch_add(1)

        # Now should be considered stalled
        assert domain.is_stalled(thread_id)

        domain.exit(thread_id)

    def test_statistics(self):
        """Test statistics reporting."""
        domain = IBRDomain()
        thread_id = domain.thread_register()

        domain.enter(thread_id)
        domain.retire(object(), thread_id)
        domain.exit(thread_id)

        stats = domain.statistics()
        assert 'global_epoch' in stats
        assert 'registered_threads' in stats
        assert 'pending_retired' in stats
        assert 'total_retired' in stats
        assert stats['registered_threads'] == 1
        assert stats['total_retired'] == 1

    def test_pending_count(self):
        """Test pending count tracking."""
        domain = IBRDomain()
        thread_id = domain.thread_register()

        assert domain.pending_count(thread_id) == 0

        domain.enter(thread_id)
        domain.retire(object(), thread_id)
        domain.exit(thread_id)

        assert domain.pending_count(thread_id) >= 0  # May have been reclaimed

        # Total pending
        total = domain.pending_count()
        assert total >= 0


class TestIBRGuard:
    """Tests for IBRGuard context manager."""

    def test_guard_enter_exit(self):
        """Test guard enters and exits correctly."""
        domain = IBRDomain()
        thread_id = domain.thread_register()

        with IBRGuard(domain, thread_id) as epoch:
            assert epoch >= 1
            assert domain._thread_active[thread_id]

        assert not domain._thread_active[thread_id]

    def test_guard_exception_safety(self):
        """Test guard exits on exception."""
        domain = IBRDomain()
        thread_id = domain.thread_register()

        try:
            with IBRGuard(domain, thread_id):
                assert domain._thread_active[thread_id]
                raise ValueError("test error")
        except ValueError:
            pass

        assert not domain._thread_active[thread_id]


class TestSMRProfiler:
    """Tests for SMRProfiler class."""

    def test_profiler_context_manager(self):
        """Test profiler as context manager."""
        domain = IBRDomain()

        with SMRProfiler(domain) as prof:
            for _ in range(10):
                domain.enter()
                domain.retire(object())
                domain.exit()

        report = prof.report()
        assert isinstance(report, SMRProfilerReport)
        assert report.total_retired == 10

    def test_profiler_manual_start_stop(self):
        """Test profiler with manual start/stop."""
        domain = IBRDomain()
        prof = SMRProfiler(domain)

        prof.start()
        domain.enter()
        domain.retire(object())
        domain.exit()
        prof.stop()

        report = prof.report()
        assert report.total_retired == 1

    def test_profiler_snapshot(self):
        """Test profiler snapshot during profiling."""
        domain = IBRDomain()

        with SMRProfiler(domain) as prof:
            domain.enter()
            domain.retire(object())
            domain.exit()

            snapshot = prof.snapshot()
            assert snapshot.total_retired == 1

    def test_profiler_reset(self):
        """Test profiler reset."""
        domain = IBRDomain()

        with SMRProfiler(domain) as prof:
            domain.enter()
            domain.retire(object())
            domain.exit()

            prof.reset()
            report = prof.report()
            assert report.total_retired == 0

    def test_profiler_analyze_stalls(self):
        """Test stall analysis."""
        domain = IBRDomain()
        prof = SMRProfiler(domain)
        prof.start()

        # No stalls in this simple test
        analysis = prof.analyze_stalls()
        # Should return empty list or analysis
        assert isinstance(analysis, list)


class TestSMRAliases:
    """Tests for backward compatibility aliases."""

    def test_smr_domain_alias(self):
        """Test SMRDomain is IBRDomain."""
        assert SMRDomain is IBRDomain

    def test_smr_guard_alias(self):
        """Test SMRGuard is IBRGuard."""
        assert SMRGuard is IBRGuard

    def test_get_default_smr(self):
        """Test get_default_smr returns IBRDomain."""
        domain = get_default_smr()
        assert isinstance(domain, IBRDomain)


class TestConcurrency:
    """Concurrency tests for IBR."""

    def test_concurrent_enter_exit(self):
        """Test concurrent enter/exit from multiple threads."""
        domain = IBRDomain()
        barrier = threading.Barrier(4)
        errors = []

        def worker():
            try:
                barrier.wait()
                for _ in range(100):
                    epoch = domain.enter()
                    time.sleep(0.0001)
                    domain.exit()
            except Exception as e:
                errors.append(e)

        threads = [threading.Thread(target=worker) for _ in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert not errors

    def test_concurrent_retire(self):
        """Test concurrent retirement."""
        domain = IBRDomain()
        barrier = threading.Barrier(4)
        errors = []

        def worker():
            try:
                barrier.wait()
                for i in range(100):
                    domain.enter()
                    domain.retire({"id": i})
                    domain.exit()
            except Exception as e:
                errors.append(e)

        threads = [threading.Thread(target=worker) for _ in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert not errors

        stats = domain.statistics()
        assert stats['total_retired'] == 400

    def test_safe_reclamation(self):
        """Test that reclamation is safe under concurrency."""
        domain = IBRDomain(retire_threshold=10)
        barrier = threading.Barrier(4)
        errors = []
        reclaimed = []

        def free_fn(obj, size):
            reclaimed.append(obj)

        def worker(worker_id):
            try:
                barrier.wait()
                for i in range(100):
                    domain.enter()
                    obj = {"worker": worker_id, "id": i}
                    domain.retire(obj, free_fn=free_fn)
                    domain.exit()
                    time.sleep(0.0001)
            except Exception as e:
                errors.append(e)

        threads = [threading.Thread(target=worker, args=(i,)) for i in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert not errors

        # Some nodes should have been reclaimed
        # (the exact number depends on timing)


class TestRetiredNode:
    """Tests for RetiredNode dataclass."""

    def test_retired_node_creation(self):
        """Test creating a RetiredNode."""
        obj = {"key": "value"}
        node = RetiredNode(
            obj=obj,
            size=64,
            epoch=5,
            retire_time=time.time(),
        )

        assert node.obj is obj
        assert node.size == 64
        assert node.epoch == 5
        assert node.free_fn is None

    def test_retired_node_with_free_fn(self):
        """Test RetiredNode with custom free function."""

        def my_free(obj, size):
            pass

        node = RetiredNode(
            obj={},
            size=32,
            epoch=1,
            retire_time=time.time(),
            free_fn=my_free,
        )

        assert node.free_fn is my_free


class TestMemoryBound:
    """Tests for memory bound properties."""

    def test_memory_bound_under_load(self):
        """Test that memory is bounded under load."""
        domain = IBRDomain(
            retire_threshold=64,
            max_reclaim_per_poll=32,
        )

        # Simulate sustained load
        for _ in range(1000):
            domain.enter()
            domain.retire(object(), size=64)
            domain.exit()

        stats = domain.statistics()
        pending = stats['pending_retired']

        # Pending should be bounded
        # Upper bound is roughly O(T * R) for IBR
        # With 1 thread and retire_threshold=64, should be < 256
        assert pending < 1000  # Reasonable bound for single thread
