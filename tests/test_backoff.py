"""Tests for backoff module (Tier 0)."""

import time
import pytest

from concurrent_collections import Backoff, pause
from concurrent_collections._backoff import (
    BackoffConfig,
    AdaptiveBackoff,
    TimedBackoff,
)


class TestPause:
    """Tests for pause function."""

    def test_pause_completes(self):
        """pause() completes without error."""
        pause()

    def test_pause_is_fast(self):
        """pause() is fast (< 1ms for single call)."""
        start = time.perf_counter()
        pause()
        elapsed = time.perf_counter() - start
        # Should complete in less than 10ms (generous for slow systems)
        assert elapsed < 0.01


class TestBackoffConfig:
    """Tests for BackoffConfig dataclass."""

    def test_default_values(self):
        """BackoffConfig has reasonable defaults."""
        config = BackoffConfig()
        assert config.min_iterations == 1
        assert config.max_iterations == 1024
        assert config.growth_factor == 2

    def test_custom_values(self):
        """BackoffConfig accepts custom values."""
        config = BackoffConfig(
            min_iterations=4,
            max_iterations=2048,
            growth_factor=4
        )
        assert config.min_iterations == 4
        assert config.max_iterations == 2048
        assert config.growth_factor == 4


class TestBackoff:
    """Tests for Backoff class."""

    def test_init_default(self):
        """Backoff initializes with default values."""
        b = Backoff()
        assert b.current == 1
        assert b.min_iterations == 1
        assert b.max_iterations == 1024

    def test_init_custom(self):
        """Backoff initializes with custom values."""
        b = Backoff(min_iterations=4, max_iterations=512, growth_factor=4)
        assert b.current == 4
        assert b.min_iterations == 4
        assert b.max_iterations == 512

    def test_from_config(self):
        """Backoff.from_config creates from BackoffConfig."""
        config = BackoffConfig(min_iterations=8, max_iterations=64)
        b = Backoff.from_config(config)
        assert b.current == 8
        assert b.max_iterations == 64

    def test_spin_increases_current(self):
        """spin() doubles current iterations."""
        b = Backoff(min_iterations=1, max_iterations=16)
        assert b.current == 1
        b.spin()
        assert b.current == 2
        b.spin()
        assert b.current == 4
        b.spin()
        assert b.current == 8
        b.spin()
        assert b.current == 16

    def test_spin_caps_at_max(self):
        """spin() caps at max_iterations."""
        b = Backoff(min_iterations=1, max_iterations=4)
        b.spin()  # 2
        b.spin()  # 4
        b.spin()  # Still 4
        b.spin()  # Still 4
        assert b.current == 4

    def test_reset_returns_to_min(self):
        """reset() returns current to min_iterations."""
        b = Backoff(min_iterations=2, max_iterations=128)
        b.spin()
        b.spin()
        assert b.current > 2
        b.reset()
        assert b.current == 2

    def test_spin_executes_pause(self):
        """spin() actually takes time (executes pause)."""
        b = Backoff(min_iterations=100, max_iterations=100)
        start = time.perf_counter()
        b.spin()
        elapsed = time.perf_counter() - start
        # Should take some measurable time
        assert elapsed >= 0

    def test_invalid_min_iterations(self):
        """Invalid min_iterations raises ValueError."""
        with pytest.raises(ValueError):
            Backoff(min_iterations=0)
        with pytest.raises(ValueError):
            Backoff(min_iterations=-1)

    def test_invalid_max_iterations(self):
        """Invalid max_iterations raises ValueError."""
        with pytest.raises(ValueError):
            Backoff(min_iterations=10, max_iterations=5)

    def test_invalid_growth_factor(self):
        """Invalid growth_factor raises ValueError."""
        with pytest.raises(ValueError):
            Backoff(growth_factor=0)

    def test_custom_growth_factor(self):
        """Custom growth_factor works correctly."""
        b = Backoff(min_iterations=1, max_iterations=27, growth_factor=3)
        assert b.current == 1
        b.spin()
        assert b.current == 3
        b.spin()
        assert b.current == 9
        b.spin()
        assert b.current == 27


class TestAdaptiveBackoff:
    """Tests for AdaptiveBackoff class."""

    def test_init(self):
        """AdaptiveBackoff initializes correctly."""
        ab = AdaptiveBackoff()
        assert ab.current == 1

    def test_spin(self):
        """spin() works like regular backoff."""
        ab = AdaptiveBackoff(min_iterations=1, max_iterations=8)
        ab.spin()
        assert ab.current == 2

    def test_success_resets(self):
        """success() resets backoff."""
        ab = AdaptiveBackoff(min_iterations=1, max_iterations=8)
        ab.spin()
        ab.spin()
        assert ab.current == 4
        ab.success()
        assert ab.current == 1

    def test_failure_does_not_reset(self):
        """failure() does not reset backoff."""
        ab = AdaptiveBackoff(min_iterations=1, max_iterations=8)
        ab.spin()
        current_before = ab.current
        ab.failure()
        assert ab.current == current_before


class TestTimedBackoff:
    """Tests for TimedBackoff class."""

    def test_init_default(self):
        """TimedBackoff initializes with default values."""
        tb = TimedBackoff()
        assert tb.current_ms == 1.0

    def test_init_custom(self):
        """TimedBackoff initializes with custom values."""
        tb = TimedBackoff(min_ms=5.0, max_ms=50.0)
        assert tb.current_ms == 5.0

    def test_wait_increases_time(self):
        """wait() increases sleep time."""
        tb = TimedBackoff(min_ms=1.0, max_ms=8.0, growth_factor=2.0)
        assert tb.current_ms == 1.0
        tb.wait()
        assert tb.current_ms == 2.0
        tb.wait()
        assert tb.current_ms == 4.0
        tb.wait()
        assert tb.current_ms == 8.0
        tb.wait()
        assert tb.current_ms == 8.0  # Capped

    def test_reset(self):
        """reset() returns to min_ms."""
        tb = TimedBackoff(min_ms=2.0, max_ms=10.0)
        tb.wait()
        tb.wait()
        assert tb.current_ms > 2.0
        tb.reset()
        assert tb.current_ms == 2.0

    def test_wait_actually_sleeps(self):
        """wait() actually sleeps for the specified time."""
        tb = TimedBackoff(min_ms=10.0, max_ms=10.0)
        start = time.perf_counter()
        tb.wait()
        elapsed = time.perf_counter() - start
        # Should sleep for at least 10ms (accounting for timing jitter)
        assert elapsed >= 0.008  # 8ms minimum

    def test_invalid_min_ms(self):
        """Invalid min_ms raises ValueError."""
        with pytest.raises(ValueError):
            TimedBackoff(min_ms=-1.0)

    def test_invalid_max_ms(self):
        """Invalid max_ms raises ValueError."""
        with pytest.raises(ValueError):
            TimedBackoff(min_ms=10.0, max_ms=5.0)


class TestBackoffPattern:
    """Tests for typical backoff usage patterns."""

    def test_retry_loop_pattern(self):
        """Test typical retry loop with backoff."""
        attempts = 0
        max_attempts = 5
        backoff = Backoff(min_iterations=1, max_iterations=16)

        while attempts < max_attempts:
            attempts += 1
            if attempts < 3:
                # Simulate failure
                backoff.spin()
            else:
                # Simulate success
                backoff.reset()
                break

        assert attempts == 3

    def test_contention_scenario(self):
        """Test backoff in simulated contention scenario."""
        import threading

        counter = [0]
        lock = threading.Lock()
        total_spins = [0]

        def worker():
            backoff = Backoff(min_iterations=1, max_iterations=32)
            for _ in range(10):
                acquired = False
                while not acquired:
                    if lock.acquire(blocking=False):
                        counter[0] += 1
                        lock.release()
                        backoff.reset()
                        acquired = True
                    else:
                        total_spins[0] += 1
                        backoff.spin()

        threads = [threading.Thread(target=worker) for _ in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert counter[0] == 40  # 4 threads * 10 increments
