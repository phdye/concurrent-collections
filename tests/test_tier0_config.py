"""Tests for config module (Tier 0)."""

import os
import sys
import pytest

from concurrent_collections import config
from concurrent_collections._config import Backend, QueueBackend, SMRScheme


class TestGILDetection:
    """Tests for GIL detection."""

    def test_gil_disabled_is_bool(self):
        """gil_disabled returns a boolean."""
        assert isinstance(config.gil_disabled, bool)

    def test_gil_disabled_matches_python_build(self):
        """gil_disabled matches Python build type."""
        # Check if Python was built with free-threading
        abiflags = getattr(sys, 'abiflags', '')
        has_free_threading_flag = 't' in abiflags

        if has_free_threading_flag:
            # Free-threaded build should report GIL disabled
            # But only if actually running without GIL
            if hasattr(sys, '_is_gil_enabled'):
                expected = not sys._is_gil_enabled()
            else:
                expected = True
            assert config.gil_disabled == expected
        else:
            # Regular Python should report GIL enabled
            assert config.gil_disabled is False


class TestArchDetectionViaConfig:
    """Tests for architecture detection exposed via config."""

    def test_detected_arch_is_string(self):
        """detected_arch is a string."""
        assert isinstance(config.detected_arch, str)
        assert config.detected_arch in ('x86_64', 'aarch64', 'riscv64', 'unknown')

    def test_detected_features_is_dict(self):
        """detected_features is a dictionary."""
        features = config.detected_features
        assert isinstance(features, dict)

        # Check expected keys
        assert 'cmpxchg16b' in features
        assert 'lse' in features
        assert 'l1_cache_line_size' in features


class TestBackendSelection:
    """Tests for backend selection."""

    def test_active_backend_is_string(self):
        """active_backend is a valid string."""
        assert config.active_backend in ('lock_free', 'locked')

    def test_force_backend_default(self):
        """force_backend defaults to 'auto'."""
        # Note: may be overridden by environment
        # Check that it's a valid value
        assert config.force_backend in ('auto', 'lock_free', 'locked')

    def test_force_backend_setter(self):
        """force_backend can be set to valid values."""
        original = config.force_backend
        try:
            config.force_backend = 'lock_free'
            assert config.force_backend == 'lock_free'
            assert config.active_backend == 'lock_free'

            config.force_backend = 'locked'
            assert config.force_backend == 'locked'
            assert config.active_backend == 'locked'

            config.force_backend = 'auto'
            assert config.force_backend == 'auto'
        finally:
            config.force_backend = original

    def test_force_backend_invalid(self):
        """force_backend rejects invalid values."""
        with pytest.raises(ValueError):
            config.force_backend = 'invalid'
        with pytest.raises(ValueError):
            config.force_backend = 'lockfree'  # Must be 'lock_free' (with underscore)

    def test_force_backend_case_insensitive_input(self):
        """force_backend accepts case variations."""
        original = config.force_backend
        try:
            config.force_backend = 'Lock_Free'
            assert config.force_backend == 'lock_free'
            config.force_backend = 'LOCKED'
            assert config.force_backend == 'locked'
        finally:
            config.force_backend = original


class TestQueueBackendSelection:
    """Tests for queue backend selection."""

    def test_available_queue_backends(self):
        """available_queue_backends is a non-empty list."""
        backends = config.available_queue_backends
        assert isinstance(backends, list)
        assert 'scq' in backends
        # 'lcrq' may or may not be present depending on platform

    def test_active_queue_backend_is_string(self):
        """active_queue_backend is a valid string."""
        assert config.active_queue_backend in ('scq', 'lcrq')

    def test_queue_backend_setter_scq(self):
        """queue_backend can be set to 'scq'."""
        original = config.queue_backend
        try:
            config.queue_backend = 'scq'
            assert config.queue_backend == 'scq'
            assert config.active_queue_backend == 'scq'
        finally:
            config.queue_backend = original

    def test_queue_backend_invalid(self):
        """queue_backend rejects invalid values."""
        with pytest.raises(ValueError):
            config.queue_backend = 'invalid'


class TestSMRConfiguration:
    """Tests for SMR configuration."""

    def test_smr_scheme_default(self):
        """smr_scheme has a valid default."""
        assert config.smr_scheme in ('ibr', 'debra')

    def test_smr_scheme_setter(self):
        """smr_scheme can be set to valid values."""
        original = config.smr_scheme
        try:
            config.smr_scheme = 'ibr'
            assert config.smr_scheme == 'ibr'

            config.smr_scheme = 'debra'
            assert config.smr_scheme == 'debra'
        finally:
            config.smr_scheme = original

    def test_smr_scheme_invalid(self):
        """smr_scheme rejects invalid values."""
        with pytest.raises(ValueError):
            config.smr_scheme = 'invalid'

    def test_retire_threshold_default(self):
        """retire_threshold has a positive default."""
        assert config.retire_threshold > 0

    def test_retire_threshold_setter(self):
        """retire_threshold can be set to positive values."""
        original = config.retire_threshold
        try:
            config.retire_threshold = 128
            assert config.retire_threshold == 128
        finally:
            config.retire_threshold = original

    def test_retire_threshold_invalid(self):
        """retire_threshold rejects non-positive values."""
        with pytest.raises(ValueError):
            config.retire_threshold = 0
        with pytest.raises(ValueError):
            config.retire_threshold = -1

    def test_max_reclaim_per_poll(self):
        """max_reclaim_per_poll works correctly."""
        original = config.max_reclaim_per_poll
        try:
            assert config.max_reclaim_per_poll > 0
            config.max_reclaim_per_poll = 64
            assert config.max_reclaim_per_poll == 64
        finally:
            config.max_reclaim_per_poll = original

    def test_max_reclaim_per_poll_invalid(self):
        """max_reclaim_per_poll rejects invalid values."""
        with pytest.raises(ValueError):
            config.max_reclaim_per_poll = 0


class TestStatisticsConfiguration:
    """Tests for statistics configuration."""

    def test_enable_statistics_default(self):
        """enable_statistics defaults to False."""
        # May be overridden by environment
        assert isinstance(config.enable_statistics, bool)

    def test_enable_statistics_setter(self):
        """enable_statistics can be toggled."""
        original = config.enable_statistics
        try:
            config.enable_statistics = True
            assert config.enable_statistics is True
            config.enable_statistics = False
            assert config.enable_statistics is False
        finally:
            config.enable_statistics = original

    def test_enable_contention_stats(self):
        """enable_contention_stats works correctly."""
        original = config.enable_contention_stats
        try:
            config.enable_contention_stats = True
            assert config.enable_contention_stats is True
            config.enable_contention_stats = False
            assert config.enable_contention_stats is False
        finally:
            config.enable_contention_stats = original


class TestConfigRepr:
    """Tests for config string representation."""

    def test_repr(self):
        """Config has a useful repr."""
        r = repr(config)
        assert 'Config' in r
        assert 'gil_disabled' in r
        assert 'active_backend' in r
        assert 'detected_arch' in r


class TestImmutableProperties:
    """Tests for immutable configuration properties."""

    def test_gil_disabled_immutable(self):
        """gil_disabled cannot be set."""
        with pytest.raises(AttributeError):
            config.gil_disabled = True

    def test_detected_arch_immutable(self):
        """detected_arch cannot be set."""
        with pytest.raises(AttributeError):
            config.detected_arch = 'fake'

    def test_detected_features_immutable(self):
        """detected_features cannot be set."""
        with pytest.raises(AttributeError):
            config.detected_features = {}

    def test_available_queue_backends_immutable(self):
        """available_queue_backends cannot be set."""
        with pytest.raises(AttributeError):
            config.available_queue_backends = ['fake']

    def test_active_backend_immutable(self):
        """active_backend cannot be set directly."""
        with pytest.raises(AttributeError):
            config.active_backend = 'lock_free'


class TestThreadSafety:
    """Tests for config thread safety."""

    def test_concurrent_reads(self):
        """Concurrent reads work correctly."""
        import threading

        results = []
        def read_config():
            for _ in range(100):
                results.append(config.active_backend)
                results.append(config.detected_arch)

        threads = [threading.Thread(target=read_config) for _ in range(10)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        # All reads should complete without error
        assert len(results) == 10 * 100 * 2

    def test_concurrent_writes(self):
        """Concurrent writes work correctly."""
        import threading

        original = config.enable_statistics

        def toggle_stats():
            for _ in range(100):
                config.enable_statistics = True
                config.enable_statistics = False

        try:
            threads = [threading.Thread(target=toggle_stats) for _ in range(4)]
            for t in threads:
                t.start()
            for t in threads:
                t.join()

            # Should complete without deadlock or corruption
            assert isinstance(config.enable_statistics, bool)
        finally:
            config.enable_statistics = original
