"""
arch_detect - CPU architecture detection and feature flags

This module provides compile-time and runtime detection of CPU architecture
and feature flags, enabling the library to select optimal code paths.
"""

import platform
import struct
import os
from enum import IntEnum
from dataclasses import dataclass
from typing import Optional


class Arch(IntEnum):
    """CPU architecture enumeration."""
    X86_64 = 0
    ARM64 = 1
    RISCV64 = 2
    UNKNOWN = 3


@dataclass(frozen=True)
class CPUFeatures:
    """CPU feature flags detected at runtime."""
    # x86-64 features
    cmpxchg16b: bool = False  # Double-width CAS
    avx: bool = False
    avx2: bool = False

    # ARM64 features
    lse: bool = False   # Large System Extensions (LDADD, etc.)
    lse2: bool = False  # Atomic 128-bit load/store

    # Cache info
    l1_cache_line_size: int = 64
    l2_cache_line_size: int = 64


# Module-level state (initialized once)
_arch: Optional[Arch] = None
_arch_name: Optional[str] = None
_cpu_features: Optional[CPUFeatures] = None
_initialized: bool = False


def _detect_arch() -> tuple[Arch, str]:
    """Detect CPU architecture from platform info."""
    machine = platform.machine().lower()

    if machine in ('x86_64', 'amd64', 'x64'):
        return Arch.X86_64, 'x86_64'
    elif machine in ('aarch64', 'arm64'):
        return Arch.ARM64, 'aarch64'
    elif machine.startswith('riscv') and struct.calcsize('P') == 8:
        return Arch.RISCV64, 'riscv64'
    else:
        return Arch.UNKNOWN, 'unknown'


def _detect_x86_features() -> dict:
    """Detect x86-64 CPU features using CPUID."""
    features = {
        'cmpxchg16b': False,
        'avx': False,
        'avx2': False,
    }

    try:
        # Try to use cpuid if available
        # On most x86-64 systems, CMPXCHG16B is supported
        # We'll use a conservative approach: assume supported on x86-64
        # since virtually all modern x86-64 CPUs have it
        features['cmpxchg16b'] = True

        # Check /proc/cpuinfo on Linux for more features
        if os.path.exists('/proc/cpuinfo'):
            with open('/proc/cpuinfo', 'r') as f:
                cpuinfo = f.read().lower()
                if 'cx16' in cpuinfo:
                    features['cmpxchg16b'] = True
                if ' avx ' in cpuinfo or 'avx' in cpuinfo.split():
                    features['avx'] = True
                if 'avx2' in cpuinfo:
                    features['avx2'] = True
    except (OSError, IOError):
        pass

    return features


def _detect_arm64_features() -> dict:
    """Detect ARM64 CPU features."""
    features = {
        'lse': False,
        'lse2': False,
    }

    try:
        # Check /proc/cpuinfo on Linux
        if os.path.exists('/proc/cpuinfo'):
            with open('/proc/cpuinfo', 'r') as f:
                cpuinfo = f.read().lower()
                # Look for 'atomics' feature flag which indicates LSE
                if 'atomics' in cpuinfo:
                    features['lse'] = True
                if 'uscat' in cpuinfo:  # Unaligned single-copy atomicity
                    features['lse2'] = True

        # On macOS, ARM64 chips (M1, M2, etc.) support LSE
        if platform.system() == 'Darwin':
            features['lse'] = True
            features['lse2'] = True

    except (OSError, IOError):
        pass

    return features


def _detect_cache_line_size() -> tuple[int, int]:
    """Detect cache line sizes."""
    l1_size = 64  # Default
    l2_size = 64  # Default

    try:
        # Try Linux sysfs
        cache_paths = [
            '/sys/devices/system/cpu/cpu0/cache/index0/coherency_line_size',  # L1
            '/sys/devices/system/cpu/cpu0/cache/index2/coherency_line_size',  # L2
        ]

        for i, path in enumerate(cache_paths):
            if os.path.exists(path):
                with open(path, 'r') as f:
                    size = int(f.read().strip())
                    if i == 0:
                        l1_size = size
                    else:
                        l2_size = size

    except (OSError, IOError, ValueError):
        pass

    # ARM64 typically uses 64 or 128 byte cache lines
    arch, _ = _detect_arch()
    if arch == Arch.ARM64 and platform.system() == 'Darwin':
        # Apple Silicon uses 128-byte cache lines
        l1_size = 128
        l2_size = 128

    return l1_size, l2_size


def _init() -> None:
    """Initialize architecture detection (called once)."""
    global _arch, _arch_name, _cpu_features, _initialized

    if _initialized:
        return

    _arch, _arch_name = _detect_arch()

    # Detect features based on architecture
    features = {}
    if _arch == Arch.X86_64:
        features = _detect_x86_features()
    elif _arch == Arch.ARM64:
        features = _detect_arm64_features()

    # Detect cache line size
    l1_size, l2_size = _detect_cache_line_size()

    _cpu_features = CPUFeatures(
        cmpxchg16b=features.get('cmpxchg16b', False),
        avx=features.get('avx', False),
        avx2=features.get('avx2', False),
        lse=features.get('lse', False),
        lse2=features.get('lse2', False),
        l1_cache_line_size=l1_size,
        l2_cache_line_size=l2_size,
    )

    _initialized = True


# Public API

def get_arch() -> Arch:
    """Get detected CPU architecture.

    Returns:
        Arch enum value (X86_64, ARM64, RISCV64, or UNKNOWN)
    """
    _init()
    return _arch


def get_arch_name() -> str:
    """Get architecture name as string.

    Returns:
        String: 'x86_64', 'aarch64', 'riscv64', or 'unknown'
    """
    _init()
    return _arch_name


def get_cpu_features() -> CPUFeatures:
    """Get detected CPU feature flags.

    Returns:
        CPUFeatures dataclass with detected features
    """
    _init()
    return _cpu_features


def has_cmpxchg16b() -> bool:
    """Check if CPU supports 128-bit compare-and-swap (x86-64 only).

    Returns:
        True if CMPXCHG16B instruction is available
    """
    _init()
    return _cpu_features.cmpxchg16b


def has_lse() -> bool:
    """Check if CPU supports ARM Large System Extensions.

    Returns:
        True if LSE atomics (LDADD, STADD, etc.) are available
    """
    _init()
    return _cpu_features.lse


def get_cache_line_size() -> int:
    """Get L1 data cache line size in bytes.

    Returns:
        Cache line size (typically 64 or 128)
    """
    _init()
    return _cpu_features.l1_cache_line_size


# Initialize on module import
_init()
