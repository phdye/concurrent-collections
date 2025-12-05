"""
concurrent_collections - Lock-free concurrent data structures for Python 3.13+

This package provides high-performance, thread-safe data structures that scale
on free-threaded Python while remaining competitive on GIL-enabled Python.
"""

__version__ = "0.1.0"

# Tier 0: Platform & Utilities
from concurrent_collections._arch_detect import (
    Arch,
    get_arch,
    get_arch_name,
    get_cpu_features,
    has_cmpxchg16b,
    has_lse,
    get_cache_line_size,
)

from concurrent_collections._config import config

from concurrent_collections._backoff import (
    Backoff,
    pause,
)

from concurrent_collections._atomics import (
    AtomicInt,
    AtomicPtr,
    AtomicFlag,
    MemoryOrder,
    atomic_thread_fence,
)

# Tier 1: Comparator System
from concurrent_collections._comparator import (
    Comparator,
    ComparatorType,
    resolve_comparator,
)

from concurrent_collections._profiler import (
    ComparatorProfiler,
    ProfilerReport,
    OptimizationLevel,
)

__all__ = [
    # Version
    "__version__",
    # Tier 0: arch_detect
    "Arch",
    "get_arch",
    "get_arch_name",
    "get_cpu_features",
    "has_cmpxchg16b",
    "has_lse",
    "get_cache_line_size",
    # Tier 0: config
    "config",
    # Tier 0: backoff
    "Backoff",
    "pause",
    # Tier 0: atomics
    "AtomicInt",
    "AtomicPtr",
    "AtomicFlag",
    "MemoryOrder",
    "atomic_thread_fence",
    # Tier 1: comparator
    "Comparator",
    "ComparatorType",
    "resolve_comparator",
    # Tier 1: profiler
    "ComparatorProfiler",
    "ProfilerReport",
    "OptimizationLevel",
]
