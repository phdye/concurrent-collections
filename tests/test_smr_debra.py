"""Tests for smr_debra module (DEBRA+ with neutralization)."""

import threading
import time
import sys
import pytest

from concurrent_collections._smr_debra import (
    DEBRADomain,
    DEBRAGuard,
    DEBRAProfiler,
    DEBRAProfilerReport,
    DEBRAThreadState,
    NeutralizationEvent,
    ThreadVulnerabilityStats,
    get_default_debra,
    NEUTRALIZATION_SUPPORTED,
)


class TestDEBRADomain:
    """Tests for DEBRADomain class."""

    def test_creation(self):
        """Test domain creation."""
        domain = DEBRADomain()
        assert domain.get_epoch() >= 1

    def test_custom_params(self):
        """Test domain with custom parameters."""
        domain = DEBRADomain(
            max_threads=64,
            retire_threshold=32,
            stall_threshold=50,
            limbo_threshold=128,
            poll_interval=16,
        )
        assert domain._max_threads == 64
        assert domain._limbo_threshold == 128
        assert domain._poll_interval == 16

    def test_thread_register(self):
        """Test thread registration creates DEBRAThreadState."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        state = domain._thread_states[thread_id]
        assert isinstance(state, DEBRAThreadState)

    def test_enter_returns_tuple(self):
        """Test enter returns (success, epoch) tuple."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        result = domain.enter(thread_id)
        assert isinstance(result, tuple)
        assert len(result) == 2

        success, epoch = result
        assert isinstance(success, bool)
        assert isinstance(epoch, int)
        assert success is True
        assert epoch >= 1

        domain.exit(thread_id)

    def test_exit(self):
        """Test exit clears active state."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        domain.enter(thread_id)
        assert domain._thread_active[thread_id]

        domain.exit(thread_id)
        assert not domain._thread_active[thread_id]

    def test_was_neutralized_initially_false(self):
        """Test was_neutralized is False initially."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        assert not domain.was_neutralized(thread_id)

    def test_clear_neutralized(self):
        """Test clearing neutralization flag."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        # Manually set neutralized for testing
        state = domain._thread_states[thread_id]
        state.was_neutralized = True

        assert domain.was_neutralized(thread_id)
        domain.clear_neutralized(thread_id)
        assert not domain.was_neutralized(thread_id)

    def test_try_neutralize_not_stalled(self):
        """Test neutralization of non-stalled thread returns False."""
        domain = DEBRADomain(stall_threshold=10)
        thread_id = domain.thread_register()

        domain.enter(thread_id)
        # Thread just entered, not stalled
        result = domain.try_neutralize(thread_id)
        assert result is False

        domain.exit(thread_id)

    def test_try_neutralize_inactive_thread(self):
        """Test neutralization of inactive thread returns False."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        # Don't enter critical section
        result = domain.try_neutralize(thread_id)
        assert result is False

    def test_try_neutralize_stalled_thread(self):
        """Test neutralization of stalled thread."""
        domain = DEBRADomain(stall_threshold=2)
        thread_id = domain.thread_register()

        domain.enter(thread_id)

        # Advance global epoch to make thread look stalled
        for _ in range(5):
            domain._global_epoch.fetch_add(1)

        result = domain.try_neutralize(thread_id)

        if NEUTRALIZATION_SUPPORTED:
            # Should succeed in marking thread as neutralized
            state = domain._thread_states[thread_id]
            assert state.was_neutralized

    def test_retire(self):
        """Test retire operation."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        success, epoch = domain.enter(thread_id)
        assert success

        domain.retire(object(), thread_id)
        assert domain.pending_count(thread_id) >= 0

        domain.exit(thread_id)

    def test_statistics(self):
        """Test statistics includes DEBRA+ specific fields."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        domain.enter(thread_id)
        domain.retire(object(), thread_id)
        domain.exit(thread_id)

        stats = domain.statistics()
        assert 'neutralization_supported' in stats
        assert 'neutralize_count' in stats
        assert 'neutralize_success_rate' in stats


class TestDEBRAGuard:
    """Tests for DEBRAGuard context manager."""

    def test_guard_returns_tuple(self):
        """Test guard returns (success, epoch) tuple."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        with DEBRAGuard(domain, thread_id) as result:
            success, epoch = result
            assert success is True
            assert epoch >= 1
            assert domain._thread_active[thread_id]

        assert not domain._thread_active[thread_id]

    def test_guard_exception_safety(self):
        """Test guard exits on exception."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        try:
            with DEBRAGuard(domain, thread_id) as (success, epoch):
                assert success
                assert domain._thread_active[thread_id]
                raise ValueError("test error")
        except ValueError:
            pass

        assert not domain._thread_active[thread_id]

    def test_guard_neutralization_pattern(self):
        """Test typical neutralization-aware usage pattern."""
        domain = DEBRADomain()
        thread_id = domain.thread_register()

        retries = 0
        max_retries = 3

        while retries < max_retries:
            with DEBRAGuard(domain, thread_id) as (success, epoch):
                if not success:
                    retries += 1
                    continue

                # Do work
                domain.retire(object(), thread_id)

                if domain.was_neutralized(thread_id):
                    retries += 1
                    continue

                # Success
                break

        # Should complete without hitting max retries in this simple case
        assert retries == 0


class TestDEBRAProfiler:
    """Tests for DEBRAProfiler class."""

    def test_profiler_context_manager(self):
        """Test profiler as context manager."""
        domain = DEBRADomain()

        with DEBRAProfiler(domain) as prof:
            for _ in range(10):
                success, _ = domain.enter()
                if success:
                    domain.retire(object())
                    domain.exit()

        report = prof.report()
        assert isinstance(report, DEBRAProfilerReport)
        assert report.total_retired == 10
        assert report.neutralization_supported == NEUTRALIZATION_SUPPORTED

    def test_profiler_report_debra_fields(self):
        """Test DEBRA+ specific report fields."""
        domain = DEBRADomain()

        with DEBRAProfiler(domain) as prof:
            domain.enter()
            domain.retire(object())
            domain.exit()

        report = prof.report()

        # Check DEBRA+ specific fields exist
        assert hasattr(report, 'neutralization_count')
        assert hasattr(report, 'neutralization_success_rate')
        assert hasattr(report, 'neutralization_events')
        assert hasattr(report, 'thread_vulnerability')
        assert hasattr(report, 'theoretical_ibr_bound')
        assert hasattr(report, 'theoretical_debra_bound')

    def test_profiler_memory_bound_comparison(self):
        """Test memory bound comparison metrics."""
        domain = DEBRADomain(retire_threshold=32)

        with DEBRAProfiler(domain) as prof:
            for _ in range(10):
                domain.enter()
                domain.retire(object())
                domain.exit()

        report = prof.report()

        # DEBRA+ should have better theoretical bound than IBR
        if report.theoretical_ibr_bound > 0 and report.theoretical_debra_bound > 0:
            assert report.theoretical_ibr_bound >= report.theoretical_debra_bound

    def test_analyze_neutralizations(self):
        """Test neutralization analysis."""
        domain = DEBRADomain()
        prof = DEBRAProfiler(domain)
        prof.start()

        analysis = prof.analyze_neutralizations()
        assert isinstance(analysis, list)


class TestNeutralizationEvent:
    """Tests for NeutralizationEvent dataclass."""

    def test_event_creation(self):
        """Test creating a neutralization event."""
        event = NeutralizationEvent(
            timestamp=time.time(),
            target_thread_id=1234,
            sender_thread_id=5678,
            target_epoch=5,
            global_epoch=10,
            epoch_lag=5,
            trigger="limbo_full",
            success=True,
        )

        assert event.target_thread_id == 1234
        assert event.sender_thread_id == 5678
        assert event.epoch_lag == 5
        assert event.trigger == "limbo_full"
        assert event.success


class TestThreadVulnerabilityStats:
    """Tests for ThreadVulnerabilityStats dataclass."""

    def test_stats_creation(self):
        """Test creating vulnerability stats."""
        stats = ThreadVulnerabilityStats(
            thread_id=1234,
            times_neutralized=5,
            times_sent_neutralization=3,
        )

        assert stats.thread_id == 1234
        assert stats.times_neutralized == 5
        assert stats.times_sent_neutralization == 3
        assert stats.restart_count == 0


class TestConcurrency:
    """Concurrency tests for DEBRA+."""

    def test_concurrent_enter_exit(self):
        """Test concurrent enter/exit with DEBRA+ tuple return."""
        domain = DEBRADomain()
        barrier = threading.Barrier(4)
        errors = []

        def worker():
            try:
                barrier.wait()
                for _ in range(100):
                    success, epoch = domain.enter()
                    if success:
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
        """Test concurrent retirement with DEBRA+."""
        domain = DEBRADomain()
        barrier = threading.Barrier(4)
        errors = []
        success_count = [0]

        def worker():
            try:
                barrier.wait()
                for i in range(100):
                    success, epoch = domain.enter()
                    if success:
                        domain.retire({"id": i})
                        if not domain.was_neutralized():
                            success_count[0] += 1
                        domain.exit()
            except Exception as e:
                errors.append(e)

        threads = [threading.Thread(target=worker) for _ in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert not errors
        # Most operations should succeed
        assert success_count[0] >= 350  # At least 87.5% success rate


class TestNeutralizationSupport:
    """Tests for platform-specific neutralization support."""

    def test_neutralization_flag(self):
        """Test neutralization support flag matches platform."""
        if sys.platform == 'win32':
            assert not NEUTRALIZATION_SUPPORTED
        else:
            assert NEUTRALIZATION_SUPPORTED

    def test_signal_number(self):
        """Test signal number is set appropriately."""
        domain = DEBRADomain()
        if NEUTRALIZATION_SUPPORTED:
            assert domain._signal_number is not None
        else:
            assert domain._signal_number is None


class TestDEBRAVsIBR:
    """Comparative tests between DEBRA+ and IBR."""

    def test_debra_extends_ibr(self):
        """Test DEBRA+ extends IBR functionality."""
        from concurrent_collections._smr_ibr import IBRDomain

        # DEBRA+ should be a subclass of IBRDomain
        assert issubclass(DEBRADomain, IBRDomain)

    def test_debra_enter_different_signature(self):
        """Test DEBRA+ enter has different return signature."""
        from concurrent_collections._smr_ibr import IBRDomain

        ibr = IBRDomain()
        debra = DEBRADomain()

        # IBR returns int (epoch)
        ibr_result = ibr.enter()
        assert isinstance(ibr_result, int)
        ibr.exit()

        # DEBRA+ returns tuple (success, epoch)
        debra_result = debra.enter()
        assert isinstance(debra_result, tuple)
        debra.exit()

    def test_debra_has_neutralization_methods(self):
        """Test DEBRA+ has neutralization-specific methods."""
        domain = DEBRADomain()

        assert hasattr(domain, 'try_neutralize')
        assert hasattr(domain, 'was_neutralized')
        assert hasattr(domain, 'clear_neutralized')


class TestGetDefaultDEBRA:
    """Tests for get_default_debra."""

    def test_returns_debra_domain(self):
        """Test get_default_debra returns DEBRADomain."""
        domain = get_default_debra()
        assert isinstance(domain, DEBRADomain)

    def test_returns_singleton(self):
        """Test get_default_debra returns same instance."""
        domain1 = get_default_debra()
        domain2 = get_default_debra()
        assert domain1 is domain2
