"""Tests for arch_detect module (Tier 0)."""

import platform
import pytest

from concurrent_collections import (
    Arch,
    get_arch,
    get_arch_name,
    get_cpu_features,
    has_cmpxchg16b,
    has_lse,
    get_cache_line_size,
)
from concurrent_collections._arch_detect import CPUFeatures


class TestArchDetection:
    """Tests for architecture detection."""

    def test_get_arch_returns_valid_enum(self):
        """get_arch() returns a valid Arch enum value."""
        arch = get_arch()
        assert isinstance(arch, Arch)
        assert arch in (Arch.X86_64, Arch.ARM64, Arch.RISCV64, Arch.UNKNOWN)

    def test_get_arch_name_returns_string(self):
        """get_arch_name() returns a valid string."""
        name = get_arch_name()
        assert isinstance(name, str)
        assert name in ('x86_64', 'aarch64', 'riscv64', 'unknown')

    def test_arch_and_name_consistent(self):
        """Architecture enum and name are consistent."""
        arch = get_arch()
        name = get_arch_name()

        expected_names = {
            Arch.X86_64: 'x86_64',
            Arch.ARM64: 'aarch64',
            Arch.RISCV64: 'riscv64',
            Arch.UNKNOWN: 'unknown',
        }
        assert name == expected_names[arch]

    def test_arch_matches_platform(self):
        """Detected architecture matches platform.machine()."""
        machine = platform.machine().lower()
        arch = get_arch()

        if machine in ('x86_64', 'amd64', 'x64'):
            assert arch == Arch.X86_64
        elif machine in ('aarch64', 'arm64'):
            assert arch == Arch.ARM64


class TestCPUFeatures:
    """Tests for CPU feature detection."""

    def test_get_cpu_features_returns_dataclass(self):
        """get_cpu_features() returns a CPUFeatures dataclass."""
        features = get_cpu_features()
        assert isinstance(features, CPUFeatures)

    def test_cpu_features_frozen(self):
        """CPUFeatures dataclass is frozen (immutable)."""
        features = get_cpu_features()
        with pytest.raises(Exception):  # FrozenInstanceError
            features.cmpxchg16b = True

    def test_cpu_features_contains_expected_fields(self):
        """CPUFeatures contains all expected fields."""
        features = get_cpu_features()

        # x86-64 features
        assert hasattr(features, 'cmpxchg16b')
        assert hasattr(features, 'avx')
        assert hasattr(features, 'avx2')

        # ARM64 features
        assert hasattr(features, 'lse')
        assert hasattr(features, 'lse2')

        # Cache info
        assert hasattr(features, 'l1_cache_line_size')
        assert hasattr(features, 'l2_cache_line_size')

    def test_feature_values_are_bool(self):
        """Feature flag values are booleans."""
        features = get_cpu_features()
        assert isinstance(features.cmpxchg16b, bool)
        assert isinstance(features.avx, bool)
        assert isinstance(features.avx2, bool)
        assert isinstance(features.lse, bool)
        assert isinstance(features.lse2, bool)

    def test_cache_line_size_reasonable(self):
        """Cache line sizes are reasonable values."""
        features = get_cpu_features()
        # Common cache line sizes are 32, 64, or 128 bytes
        assert features.l1_cache_line_size in (32, 64, 128)
        assert features.l2_cache_line_size in (32, 64, 128)


class TestFeatureQueries:
    """Tests for feature query functions."""

    def test_has_cmpxchg16b_returns_bool(self):
        """has_cmpxchg16b() returns a boolean."""
        result = has_cmpxchg16b()
        assert isinstance(result, bool)

    def test_has_lse_returns_bool(self):
        """has_lse() returns a boolean."""
        result = has_lse()
        assert isinstance(result, bool)

    def test_get_cache_line_size_returns_int(self):
        """get_cache_line_size() returns an integer."""
        size = get_cache_line_size()
        assert isinstance(size, int)
        assert size > 0

    def test_x86_features_on_x86(self):
        """On x86-64, CMPXCHG16B should be detected."""
        if get_arch() == Arch.X86_64:
            # Most modern x86-64 CPUs support CMPXCHG16B
            # This test may fail on very old CPUs
            assert has_cmpxchg16b() is True

    def test_arm_features_on_arm(self):
        """On ARM64 macOS, LSE should be detected."""
        if get_arch() == Arch.ARM64 and platform.system() == 'Darwin':
            # Apple Silicon supports LSE
            assert has_lse() is True


class TestImmutabilityAfterInit:
    """Tests for immutability guarantees."""

    def test_multiple_calls_return_same_values(self):
        """Multiple calls return consistent values."""
        arch1 = get_arch()
        arch2 = get_arch()
        assert arch1 == arch2

        name1 = get_arch_name()
        name2 = get_arch_name()
        assert name1 == name2

        features1 = get_cpu_features()
        features2 = get_cpu_features()
        assert features1 == features2

    def test_features_object_identity(self):
        """Same features object returned on each call."""
        features1 = get_cpu_features()
        features2 = get_cpu_features()
        # Should return the same cached object
        assert features1 is features2


class TestConservativeDefaults:
    """Tests for conservative defaults on unknown architectures."""

    def test_unknown_arch_returns_safe_cache_size(self):
        """Unknown architecture returns safe default cache line size."""
        # We can't easily test this without mocking, but we verify
        # that get_cache_line_size() always returns a valid value
        size = get_cache_line_size()
        assert size >= 32
        assert size <= 256
