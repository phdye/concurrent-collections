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

# Tier 2: Memory Management
from concurrent_collections._mimalloc_glue import (
    Allocator,
    AllocatorStats,
    AllocationSnapshot,
    alloc_stats_enable,
    alloc_stats_disable,
    alloc_stats_reset,
    alloc_stats_snapshot,
    cc_alloc,
    cc_free,
)

from concurrent_collections._smr_ibr import (
    IBRDomain,
    IBRGuard,
    SMRProfiler,
    SMRProfilerReport,
    get_default_ibr,
    # Aliases for backward compatibility
    SMRDomain,
    SMRGuard,
    get_default_smr,
)

from concurrent_collections._smr_debra import (
    DEBRADomain,
    DEBRAGuard,
    DEBRAProfiler,
    DEBRAProfilerReport,
    get_default_debra,
    NEUTRALIZATION_SUPPORTED,
)

# Tier 3: Core Algorithms
from concurrent_collections._treiber import (
    TreiberStack,
    Empty as StackEmpty,
)

from concurrent_collections._scq import (
    SCQ,
    SimpleBoundedQueue,
)

from concurrent_collections._skiplist import (
    SkipList,
)

# Tier 4: Public API
from concurrent_collections._lockfree_stack import (
    LockFreeStack,
    Empty,
)

from concurrent_collections._lockfree_queue import (
    LockFreeQueue,
    Full,
    Empty as QueueEmpty,
)

from concurrent_collections._skiplistmap import (
    SkipListMap,
    FrozenSkipListMap,
)

from concurrent_collections._skiplistset import (
    SkipListSet,
    FrozenSkipListSet,
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
    # Tier 2: mimalloc_glue
    "Allocator",
    "AllocatorStats",
    "AllocationSnapshot",
    "alloc_stats_enable",
    "alloc_stats_disable",
    "alloc_stats_reset",
    "alloc_stats_snapshot",
    "cc_alloc",
    "cc_free",
    # Tier 2: smr_ibr
    "IBRDomain",
    "IBRGuard",
    "SMRProfiler",
    "SMRProfilerReport",
    "get_default_ibr",
    "SMRDomain",
    "SMRGuard",
    "get_default_smr",
    # Tier 2: smr_debra
    "DEBRADomain",
    "DEBRAGuard",
    "DEBRAProfiler",
    "DEBRAProfilerReport",
    "get_default_debra",
    "NEUTRALIZATION_SUPPORTED",
    # Tier 3: Core Algorithms
    "TreiberStack",
    "StackEmpty",
    "SCQ",
    "SimpleBoundedQueue",
    "SkipList",
    # Tier 4: Public API
    "LockFreeStack",
    "Empty",
    "LockFreeQueue",
    "Full",
    "QueueEmpty",
    "SkipListMap",
    "FrozenSkipListMap",
    "SkipListSet",
    "FrozenSkipListSet",
]
