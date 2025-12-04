# concurrent_collections

## High-Level Design Document

**Version**: 2.0 Draft  
**Target**: Python 3.13+ (free-threaded and GIL-enabled)  
**License**: BSD-3-Clause (CPython compatible)

---

## 1. Vision & Goals

### 1.1 Problem Statement

Free-threaded Python (PEP 703) removes the GIL but exposes a critical gap: Python lacks high-performance concurrent data structures. Developers must choose between:

- **Lock-wrapped stdlib containers**: Simple but contention kills scaling
- **multiprocessing-based sharing**: High overhead, serialization costs
- **Pure Python attempts**: Can't achieve native performance

Meanwhile, Java has `java.util.concurrent`, C++ has Intel TBB and folly, and Rust has crossbeam. Python has nothing comparable.

### 1.2 Solution

`concurrent_collections` provides production-ready, lock-free data structures:

| Category | Structures | Fills Gap |
|----------|------------|-----------|
| **Ordered Maps/Sets** | SkipListMap, SkipListSet, TreeMap, TreeSet | No concurrent ordered containers exist in Python |
| **Queues** | LockFreeQueue, FastQueue, WaitFreeQueue | `queue.Queue` uses locks, poor scaling |
| **Stacks** | LockFreeStack | No concurrent stack in stdlib |

### 1.3 Design Principles

1. **Correctness first**: Linearizable, formally verified algorithms from peer-reviewed literature
2. **Pythonic API**: Familiar interfaces (dict-like, set-like) with Pythonic iteration
3. **Zero-copy where possible**: Minimize PyObject overhead in hot paths
4. **Graceful degradation**: Works on GIL-enabled Python with optimized locked backend
5. **Adaptive implementation**: Runtime detection selects optimal backend for GIL state
6. **No dependencies**: Self-contained, vendored SMR implementation
7. **Production-ready**: Comprehensive testing, benchmarks, documentation

---

## 2. Package Contents

### 2.1 Module Structure

```
concurrent_collections
├── SkipListMap          # Ordered key-value, O(log n)
├── SkipListSet          # Ordered set, O(log n)
├── FrozenSkipListMap    # Immutable snapshot of SkipListMap
├── FrozenSkipListSet    # Immutable snapshot of SkipListSet
├── TreeMap              # BST-based ordered key-value
├── TreeSet              # BST-based ordered set
├── LockFreeQueue        # MPMC queue, portable
├── FastQueue            # MPMC queue, architecture-optimized
├── WaitFreeQueue        # MPMC queue, wait-free guarantee
├── LockFreeStack        # MPMC stack with elimination
├── Comparator           # Custom comparison support
├── config               # Runtime configuration
└── recipes              # Additional utilities
    └── BoundedSkipListMap  # Size-limited variant
```

### 2.2 Ordered Containers

#### SkipListMap / SkipListSet

**Algorithm**: Fraser's lock-free skip list (2004), proven in Java's `ConcurrentSkipListMap`

**Why skip list first**:
- Simpler than balanced trees (no rotations)
- Probabilistic balance—no worst-case degradation in practice
- Well-understood, multiple production implementations exist
- Better concurrency than BSTs under heavy writes

**Complexity**:
| Operation | Average | Worst |
|-----------|---------|-------|
| get | O(log n) | O(n)* |
| put | O(log n) | O(n)* |
| delete | O(log n) | O(n)* |
| range | O(log n + k) | O(n + k)* |

*Worst case is probabilistically negligible (1/2^32 for 32 levels)

#### FrozenSkipListMap / FrozenSkipListSet

**Purpose**: Immutable point-in-time snapshots preserving ordering.

**Characteristics**:
- Created via `snapshot()` method on mutable variants
- All read operations supported
- All mutation operations raise `TypeError`
- Hashable if contents are hashable (can be used as dict keys)
- O(n) copy at creation time, independent of source

#### TreeMap / TreeSet

**Algorithm**: Natarajan-Mittal external BST (PPoPP 2014)

**Why offer both skip list and BST**:
- BST has better cache locality for read-heavy workloads
- Skip list has better write concurrency
- Different workloads favor each—let users benchmark
- External BST has cleaner deletion semantics

**Key differentiator from skip list**: Deterministic O(log n) with proper balancing (though unbalanced in base form; balanced variant possible via Brown's (a,b)-tree)

### 2.3 Queue Family

#### LockFreeQueue (Default)

**Algorithm**: SCQ—Scalable Circular Queue (Nikolaev & Ravindran, 2019)

**Why SCQ**:
- Portable: only requires single-width CAS
- Works on ARM, RISC-V, PowerPC—not just x86
- Livelock-free (unlike CRQ)
- Bounded memory footprint

#### FastQueue (Architecture-Optimized)

**Algorithm**: LCRQ on x86-64, SCQ fallback elsewhere

**Why offer both**:
- LCRQ achieves highest known throughput on x86-64
- Requires double-width CAS (CMPXCHG16B)—not portable
- Runtime architecture detection selects optimal implementation

#### WaitFreeQueue

**Algorithm**: wCQ—Wait-Free Circular Queue (SPAA 2022)

**Why offer wait-free variant**:
- Hard real-time systems need bounded worst-case latency
- Lock-free only guarantees system-wide progress
- Wait-free guarantees per-thread progress

**Tradeoff**: ~15-20% throughput overhead vs lock-free in typical workloads

### 2.4 Stack

#### LockFreeStack

**Algorithm**: Treiber stack with elimination backoff

**Elimination optimization**: Under high contention, concurrent push/pop pairs "eliminate" each other without touching the shared stack—dramatic throughput improvement.

### 2.5 Recipes Module

#### BoundedSkipListMap

**Purpose**: Size-limited variant of SkipListMap for bounded-memory use cases.

**Location**: `concurrent_collections.recipes.BoundedSkipListMap`

**Why in recipes**: 
- Bounded concurrent containers add complexity
- Size tracking under concurrency has inherent races
- Minority use case—most users want unbounded
- May promote to core if demand warrants

---

## 3. API Design

### 3.1 Ordered Map API

```python
from concurrent_collections import SkipListMap, FrozenSkipListMap, Comparator

# === Construction ===

m = SkipListMap()  # Natural ordering (keys must implement __lt__)

# Custom comparator - Python callable (slower)
m = SkipListMap(cmp=lambda a, b: len(a) - len(b))

# Key function (like sorted())
m = SkipListMap(key=str.lower)  # Case-insensitive ordering

# C comparator - maximum performance (see Comparator section)
m = SkipListMap(cmp=Comparator.reverse())

# === Basic Operations (dict-like) ===

m[key] = value              # put(key, value)
value = m[key]              # get(key), raises KeyError if missing
value = m.get(key, default) # get with default
del m[key]                  # delete(key)
key in m                    # contains(key)
len(m)                      # size (approximate under concurrency)

# === Atomic Operations ===

old = m.put_if_absent(key, value)      # Returns existing or None
old = m.replace(key, new_value)        # Returns old or None
ok = m.replace_if(key, expected, new)  # CAS semantics
old = m.pop(key, default)              # Atomic remove and return

# === Ordered Operations (the differentiator) ===

m.first_key()               # Minimum key, raises KeyError if empty
m.last_key()                # Maximum key
m.floor_key(key)            # Greatest key ≤ key, or None
m.ceiling_key(key)          # Least key ≥ key, or None
m.lower_key(key)            # Greatest key < key
m.higher_key(key)           # Least key > key

# === Range Operations ===

m.keys(start, stop)         # Iterator over keys in [start, stop)
m.items(start, stop)        # Iterator over (key, value) pairs
m.values(start, stop)       # Iterator over values

# === Iteration (weakly consistent) ===

# WARNING: Weakly consistent iteration
# May see keys inserted during iteration, miss deleted keys,
# or see the same key twice if deleted and re-inserted.

for key in m:               # Iterate keys in order
    ...
for key, value in m.items():
    ...

# === Snapshots (point-in-time consistency) ===

frozen = m.snapshot()                    # Full snapshot -> FrozenSkipListMap
frozen = m.snapshot(start=10, stop=20)   # Partial snapshot [10, 20)

# FrozenSkipListMap supports all read operations
frozen[key]
frozen.get(key)
frozen.first_key()
list(frozen.items())

# FrozenSkipListMap is immutable
frozen[key] = value         # TypeError

# FrozenSkipListMap is hashable (if contents are hashable)
hash(frozen)
{frozen: "value"}           # Can use as dict key

# Convert back to mutable
mutable = frozen.thaw()     # Returns new SkipListMap

# === Bulk Operations ===

m.clear()                   # Remove all entries
m.update(other_map)         # Merge from dict or mapping

# === Comparator Info ===

m.comparator_type           # 'natural', 'c_func', or 'python'
```

### 3.2 Ordered Set API

```python
from concurrent_collections import SkipListSet, FrozenSkipListSet

s = SkipListSet()

# === Basic Operations (set-like) ===

s.add(item)
s.discard(item)             # Remove if present, no error if missing
s.remove(item)              # Remove, raises KeyError if missing
item in s
len(s)

# === Ordered Operations ===

s.first()                   # Minimum element
s.last()                    # Maximum element
s.floor(item)               # Greatest element ≤ item
s.ceiling(item)             # Least element ≥ item

# === Range Iteration ===

s.range(start, stop)        # Iterator over [start, stop)

# === Snapshots ===

frozen = s.snapshot()       # Returns FrozenSkipListSet
frozen = s.snapshot(start, stop)

# FrozenSkipListSet is hashable
hash(frozen)
{frozen: "value"}

# Convert back
mutable = frozen.thaw()     # Returns new SkipListSet

# === Set Operations (return new SkipListSet) ===

s.union(other)
s.intersection(other)
s.difference(other)
```

### 3.3 Queue API

```python
from concurrent_collections import LockFreeQueue, FastQueue, WaitFreeQueue

q = LockFreeQueue(maxsize=0)  # 0 = unbounded

# === Core Operations ===

q.put(item)                 # Enqueue, blocks if bounded and full
q.put_nowait(item)          # Enqueue, raises Full if bounded and full
item = q.get()              # Dequeue, blocks if empty
item = q.get_nowait()       # Dequeue, raises Empty if empty

# === Non-blocking Try Variants ===

ok = q.try_put(item)        # Returns True/False
item = q.try_get()          # Returns item or None

# === Inspection (approximate under concurrency) ===

len(q)
q.empty()
q.full()                    # Only meaningful if bounded

# === Bulk Operations ===

items = q.drain(max_items)  # Dequeue up to max_items, returns list

# === Compatibility with queue.Queue ===

q.qsize()                   # Alias for len(q)
q.task_done()               # No-op for compatibility
q.join()                    # No-op for compatibility
```

### 3.4 Stack API

```python
from concurrent_collections import LockFreeStack

s = LockFreeStack()

s.push(item)
item = s.pop()              # Raises Empty if empty
item = s.try_pop()          # Returns None if empty
item = s.peek()             # View top without removing

len(s)
s.empty()
```

### 3.5 Comparator API

```python
from concurrent_collections import Comparator

# === Built-in C Comparators (maximum performance) ===

Comparator.natural()      # Default __lt__ ordering
Comparator.reverse()      # Reverse of natural ordering
Comparator.numeric()      # Optimized for int/float keys
Comparator.string()       # Optimized for str keys (locale-unaware)

# === From Cython C Function ===

# See "High-Performance Custom Comparators" documentation
cmp = Comparator.from_cfunc(func_ptr, context=None, prevent_gc=False)

# === Usage ===

m = SkipListMap(cmp=Comparator.reverse())
m[3] = "c"
m[1] = "a"
m[2] = "b"
list(m.keys())  # [3, 2, 1] - reverse order
```

### 3.6 Bounded Map API (Recipes)

```python
from concurrent_collections.recipes import BoundedSkipListMap, BoundedMapFullError

# === Construction ===

m = BoundedSkipListMap(maxsize=1000)                    # Raise when full
m = BoundedSkipListMap(maxsize=1000, eviction='oldest') # Evict first_key when full

# === Operations ===

m[key] = value              # May raise BoundedMapFullError or evict
m.put(key, value)           # Same behavior

# === Properties ===

m.maxsize                   # Maximum allowed entries
m.is_full()                 # Check if at capacity (may be stale)

# === Eviction Policies ===

# eviction='error' (default)
#   - Raises BoundedMapFullError when inserting new key into full map
#   - Updates to existing keys always succeed

# eviction='oldest'  
#   - Evicts first_key() when full to make room
#   - Note: Evict-then-insert is not atomic
```

### 3.7 Configuration API

```python
from concurrent_collections import config
import concurrent_collections

# === GIL State & Backend (read-only unless forcing) ===

config.gil_disabled              # True if running on free-threaded Python
config.active_backend            # 'lock_free' or 'locked'

# Force specific backend (for testing/benchmarking only)
config.force_backend = 'auto'       # Automatic selection (default)
config.force_backend = 'lock_free'  # Force lock-free (may add overhead under GIL)
config.force_backend = 'locked'     # Force locked (loses scaling without GIL)

# === Platform & Architecture (read-only) ===

config.detected_arch            # 'x86_64', 'aarch64', etc.
config.detected_features        # {'cmpxchg16b': True, 'lse': False, ...}
config.available_queue_backends # ['scq', 'lcrq'] or ['scq']

# === Queue Backend Selection ===

config.queue_backend = 'auto'   # 'auto', 'scq', 'lcrq'
                                # 'auto' selects best for platform
                                # 'lcrq' raises if unavailable

# === SMR Tuning ===

config.smr_scheme = 'ibr'       # 'ibr' or 'debra'
config.retire_threshold = 64    # Trigger reclamation after N retires
config.max_reclaim_per_poll = 32 # Bound reclamation work per poll

# === Debugging & Diagnostics ===

config.enable_statistics = False # Track operation counts (slight overhead)
config.enable_contention_stats = False  # Track CAS failures

# === Build Information ===

concurrent_collections.print_config()  # Print full configuration
info = concurrent_collections.get_build_info()  # Programmatic access
# {'version': '1.0.0', 'platform': 'linux-x86_64', 'backend': 'lock_free', 
#  'queue_backend': 'lcrq', 'gil_disabled': True, ...}
```

**Configuration Precedence**: Environment variables override defaults, code overrides environment:

```bash
# Environment variable override (useful for benchmarking)
export CONCURRENT_COLLECTIONS_QUEUE_BACKEND=scq
export CONCURRENT_COLLECTIONS_SMR_SCHEME=debra
export CONCURRENT_COLLECTIONS_FORCE_BACKEND=locked
```

---

## 4. Architecture

### 4.1 Component Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                        Python Layer                              │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌────────────┐ │
│  │ SkipListMap │ │   TreeMap   │ │    Queue    │ │   Stack    │ │
│  │ SkipListSet │ │   TreeSet   │ │   Family    │ │            │ │
│  └──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └─────┬──────┘ │
└─────────┼───────────────┼───────────────┼──────────────┼────────┘
          │               │               │              │
          ▼               ▼               ▼              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      C Extension Layer                           │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │                   Python C API Bindings                      ││
│  │         (Reference counting, GC integration, typing)         ││
│  └─────────────────────────────────────────────────────────────┘│
│                              │                                   │
│  ┌───────────────────────────┴───────────────────────────────┐  │
│  │                   Backend Selection                        │  │
│  │                                                            │  │
│  │   GIL Disabled?  ──yes──►  Lock-Free Backend              │  │
│  │        │                   (CAS, memory barriers, SMR)     │  │
│  │        no                                                  │  │
│  │        ▼                                                   │  │
│  │   Locked Backend                                           │  │
│  │   (Fine-grained locks, direct free, simpler code)          │  │
│  └────────────────────────────────────────────────────────────┘  │
│                              │                                   │
│  ┌───────────────────────────┼───────────────────────────────┐  │
│  │                  Core Data Structures                      │  │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   │  │
│  │  │ skiplist │  │   bst    │  │ scq/lcrq │  │ treiber  │   │  │
│  │  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘   │  │
│  └───────┼─────────────┼─────────────┼─────────────┼─────────┘  │
│          │             │             │             │             │
│          ▼             ▼             ▼             ▼             │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │          Safe Memory Reclamation (SMR) [Lock-Free Only]      ││
│  │              IBR (primary) / DEBRA+ (alternative)            ││
│  └─────────────────────────────────────────────────────────────┘│
│                              │                                   │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │                     Utility Layer                            ││
│  │    atomics  │  backoff  │  arch detection  │  mimalloc glue ││
│  └─────────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────────┘
                               │
                               ▼
                    ┌─────────────────────┐
                    │      mimalloc       │
                    │ (CPython allocator) │
                    └─────────────────────┘
```

### 4.2 Adaptive Backend Selection

The library automatically detects GIL state at runtime and selects the optimal implementation:

```
┌─────────────────────────────────────────────────────────────────┐
│                     Runtime Detection                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   Python 3.13+: sys._is_gil_enabled()                           │
│   Fallback: Check sys.abiflags for 't' suffix                   │
│                                                                  │
│   GIL Disabled?  ──yes──►  Lock-Free Backend                    │
│        │                   • CAS-based operations                │
│        │                   • Memory barriers                     │
│        │                   • IBR/DEBRA+ memory reclamation       │
│        │                   • Cache line padding                  │
│        │                   • ~80% single-thread perf             │
│        │                   • Linear multi-thread scaling         │
│        no                                                        │
│        ▼                                                         │
│   Locked Backend                                                 │
│   • Fine-grained locking (per-level for skip list)              │
│   • Direct memory free (GIL protects)                           │
│   • Simpler node structure                                       │
│   • 100% single-thread perf (baseline)                          │
│   • No negative scaling (unlike coarse locks)                    │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**Detection Code**:

```python
# In concurrent_collections/__init__.py
import sys

def _detect_gil_state():
    """Detect if GIL is disabled at runtime."""
    # Python 3.13+ has sys._is_gil_enabled()
    if hasattr(sys, '_is_gil_enabled'):
        return not sys._is_gil_enabled()
    
    # Fallback: check if we're free-threaded build
    # Free-threaded builds have 't' in abiflags
    if hasattr(sys, 'abiflags') and 't' in sys.abiflags:
        return True
    
    return False

GIL_DISABLED = _detect_gil_state()
```

### 4.3 Dual Implementation Strategy

| Aspect | Lock-Free Backend | Locked Backend |
|--------|-------------------|----------------|
| **When Used** | GIL disabled (free-threaded) | GIL enabled (default Python) |
| **Synchronization** | CAS, memory barriers | `pthread_mutex` / `SRWLOCK` |
| **Memory Reclamation** | IBR/DEBRA (deferred) | Direct free (GIL protects) |
| **Node Structure** | Atomic pointers, 64B padding | Simple pointers, compact |
| **Code Complexity** | High | Low |
| **Single-Thread Perf** | ~80% of locked | 100% (baseline) |
| **Multi-Thread Scaling** | Linear to ~8-16 threads | Flat (fine-grained) / Negative (coarse) |

**Locked Backend Implementation** (simplified):

```c
// GIL-enabled variant - much simpler
typedef struct {
    PyObject_HEAD
    SkipListNode *head;
    Py_ssize_t size;
    int max_level;
    Comparator *cmp;
    PyThread_type_lock locks[MAX_LEVEL];  // Per-level locks
} LockedSkipListObject;

static PyObject* LockedSkipList_put(LockedSkipListObject *self, ...) {
    // Acquire locks for affected levels only
    // Simple, non-atomic insertion
    // Direct Py_DECREF on replaced values
    // No SMR overhead
}
```

### 4.4 Memory Reclamation Strategy (Lock-Free Backend Only)

All lock-free structures face the reclamation problem: when a thread removes a node, other threads may still hold references. Premature freeing causes use-after-free; never freeing causes unbounded memory growth.

**Primary scheme: Interval-Based Reclamation (IBR)**

| Property | IBR | CPython's GUS | Hazard Pointers |
|----------|-----|---------------|-----------------|
| Overhead per access | Low | Low | High (fence) |
| Memory bound | O(T²R) | Unbounded | O(TR) |
| Stalled thread handling | Yes | No | Yes |
| Complexity | Medium | Simple | Medium |

IBR chosen because it provides bounded memory (unlike GUS) without the per-access fence overhead of hazard pointers.

**Alternative: DEBRA+**

Available via configuration for specific workloads:
- Better throughput than IBR under low contention
- Signal-based neutralization for stalled threads
- Preferred for single-socket, low thread count scenarios

### 4.5 mimalloc Integration

```
┌──────────────────────────────────────────────────────┐
│                   Our Extension                       │
│                                                       │
│   SkipListNode allocation:  mi_malloc(sizeof(...))   │
│   Node retirement:          smr_retire(node)         │
│   Deferred free callback:   mi_free(node)            │
│                                                       │
│   No conflict with CPython's page-level QSBR—        │
│   we manage our own nodes independently              │
└──────────────────────────────────────────────────────┘
                          │
                          ▼
              ┌───────────────────────┐
              │       mimalloc        │
              │  • Thread-local heaps │
              │  • Handles cross-     │
              │    thread frees       │
              └───────────────────────┘
```

Our SMR retires nodes to a deferred list. When safe, the SMR reclamation callback invokes `mi_free()`. This is fully compatible with mimalloc's design—it handles cross-thread frees internally.

### 4.6 Thread Safety Model

**Linearizability**: All operations appear to take effect atomically at some point between invocation and response.

**Progress guarantees**:

| Structure | Lock-Free Backend | Locked Backend |
|-----------|-------------------|----------------|
| SkipListMap/Set | Lock-free | Blocking (fine-grained) |
| TreeMap/Set | Lock-free | Blocking (fine-grained) |
| LockFreeQueue | Lock-free | Lock-free* |
| FastQueue | Lock-free | Lock-free* |
| WaitFreeQueue | Wait-free | Wait-free* |
| LockFreeStack | Lock-free | Lock-free* |

*Queues and stacks use lock-free algorithms in both backends since their overhead is acceptable and simplifies the codebase.

**Lock-free**: At least one thread makes progress in finite steps (system-wide progress)

**Wait-free**: Every thread makes progress in bounded steps (per-thread progress)

### 4.7 Iterator Semantics

**Mutable containers use weakly consistent iteration**:

- Iterator traverses the live data structure
- May see some concurrent modifications, miss others
- No ordering guarantees for concurrent changes
- Memory cost: O(1) iterator state
- Matches Java's `ConcurrentSkipListMap` behavior

**Warning patterns to document**:

```python
# UNSAFE: Modifying while iterating
for key in m:
    if some_condition(m[key]):
        del m[key]  # May corrupt iteration

# SAFE: Use snapshot for modification
for key in m.snapshot():
    if some_condition(m.get(key)):  # Value may have changed
        del m[key]                   # Safe - not iterating m
```

**Frozen containers provide true snapshot semantics**:

```python
frozen = m.snapshot()
# frozen is immutable, iteration is stable
for key, value in frozen.items():
    # Guaranteed to see exactly what existed at snapshot time
    ...
```

---

## 5. Custom Comparator System

### 5.1 Overview

By default, keys must implement `__lt__` for natural ordering. For custom ordering, users can provide:

1. **Python callable**: Flexible but slow (~10x overhead per comparison)
2. **Key function**: Like `sorted(key=...)`, extracts sort key once
3. **C comparator**: Maximum performance, requires Cython

### 5.2 Comparator Types

| Type | Performance | Use Case |
|------|-------------|----------|
| Natural (`__lt__`) | Baseline | Default, keys are naturally comparable |
| Built-in C | ~100% | Reverse order, numeric optimization |
| Custom C (Cython) | ~80-95% | Complex custom ordering, performance-critical |
| Python callable | ~10% | Prototyping, non-critical paths |

### 5.3 Internal Dispatch

```c
typedef int (*cmp_func)(PyObject *a, PyObject *b, void *context);

typedef struct {
    enum { CMP_NATURAL, CMP_C_FUNC, CMP_KEY_FUNC, CMP_PYTHON } type;
    union {
        cmp_func c_func;      // C function pointer
        PyObject *py_cmp;     // Python callable (cmp)
        PyObject *py_key;     // Python callable (key)
    };
    void *context;            // Optional context for C func
} Comparator;

static inline int compare(Comparator *cmp, PyObject *a, PyObject *b) {
    switch (cmp->type) {
        case CMP_NATURAL:
            return PyObject_RichCompareBool(a, b, Py_LT) ? -1 :
                   PyObject_RichCompareBool(a, b, Py_GT) ? 1 : 0;
        case CMP_C_FUNC:
            return cmp->c_func(a, b, cmp->context);  // No Python call!
        case CMP_PYTHON:
            // Slow path - full Python call
            ...
    }
}
```

### 5.4 High-Performance Custom Comparators (Cython)

For maximum performance with custom ordering, implement comparators in Cython.

**Why Cython?**

Each comparison in a skip list operation requires calling the comparator. A single `put()` averages O(log n) comparisons. With 1 million entries, that's ~20 comparisons per operation.

| Comparator Type | Cost per Comparison | 1M ops @ 20 cmp/op |
|-----------------|--------------------|--------------------|
| Natural (`__lt__`) | ~50ns | ~1 second |
| C function | ~10ns | ~0.2 seconds |
| Python callable | ~500ns | ~10 seconds |

**Example 1: Reverse Numeric Order**

```cython
# reverse_cmp.pyx
cimport cython
from cpython.object cimport PyObject

ctypedef int (*cmp_func)(PyObject*, PyObject*, void*) noexcept nogil

cdef int reverse_numeric_cmp(PyObject* a, PyObject* b, void* ctx) noexcept nogil:
    """Compare two Python ints in reverse order."""
    cdef long va = (<object>a)
    cdef long vb = (<object>b)
    if va > vb:
        return -1
    elif va < vb:
        return 1
    return 0

def get_reverse_numeric_comparator():
    """Return a comparator object wrapping the C function."""
    from concurrent_collections import Comparator
    return Comparator.from_cfunc(<Py_uintptr_t>reverse_numeric_cmp)
```

**Example 2: Case-Insensitive String Comparison**

```cython
# ci_string_cmp.pyx
cimport cython
from cpython.object cimport PyObject
from cpython.unicode cimport PyUnicode_AsUTF8AndSize
from libc.string cimport strncasecmp

cdef int ci_string_cmp(PyObject* a, PyObject* b, void* ctx) noexcept nogil:
    """Case-insensitive string comparison."""
    cdef Py_ssize_t len_a, len_b
    cdef const char* str_a
    cdef const char* str_b
    
    with gil:
        str_a = PyUnicode_AsUTF8AndSize(<object>a, &len_a)
        str_b = PyUnicode_AsUTF8AndSize(<object>b, &len_b)
    
    cdef Py_ssize_t min_len = len_a if len_a < len_b else len_b
    cdef int result = strncasecmp(str_a, str_b, min_len)
    
    if result != 0:
        return result
    return (len_a > len_b) - (len_a < len_b)
```

**Example 3: Composite Key Comparison**

```cython
# composite_cmp.pyx

# For keys like (priority: int, timestamp: float, id: str)
cdef int priority_queue_cmp(PyObject* a, PyObject* b, void* ctx) noexcept nogil:
    """Compare (priority, timestamp, id) tuples."""
    cdef object ta = <object>a
    cdef object tb = <object>b
    
    # Compare priority (lower is higher priority)
    cdef int pa = ta[0]
    cdef int pb = tb[0]
    if pa != pb:
        return (pa > pb) - (pa < pb)
    
    # Tie-break by timestamp (earlier is higher priority)  
    cdef double tsa = ta[1]
    cdef double tsb = tb[1]
    if tsa != tsb:
        return (tsa > tsb) - (tsa < tsb)
    
    # Final tie-break by id
    cdef str ida = ta[2]
    cdef str idb = tb[2]
    return (ida > idb) - (ida < idb)
```

**Example 4: Using Context for Parameterized Comparison**

```cython
# weighted_cmp.pyx

# Compare items by weighted score using external weights dict
cdef int weighted_cmp(PyObject* a, PyObject* b, void* ctx) noexcept nogil:
    """Compare by weighted score. ctx points to weights dict."""
    cdef dict weights = <dict>ctx
    cdef object key_a = <object>a
    cdef object key_b = <object>b
    
    cdef double score_a = weights.get(key_a, 0.0)
    cdef double score_b = weights.get(key_b, 0.0)
    
    return (score_a > score_b) - (score_a < score_b)

def get_weighted_comparator(weights: dict):
    from concurrent_collections import Comparator
    return Comparator.from_cfunc(
        <Py_uintptr_t>weighted_cmp, 
        context=weights,
        prevent_gc=True  # Keep weights alive
    )
```

**Registering and Validating**:

```python
from concurrent_collections import SkipListMap
from my_cython_module import get_reverse_numeric_comparator

cmp = get_reverse_numeric_comparator()
m = SkipListMap(cmp=cmp)

# Verify fast path is active
assert m.comparator_type == 'c_func'  # Not 'python'
```

---

## 6. Platform Support & Architecture Strategy

### 6.1 Design Philosophy

`concurrent_collections` follows a **portable-first with architecture-specific optimizations** approach. Every structure works on every supported platform. Performance-critical paths use optimized implementations where available, with automatic fallback to portable alternatives.

### 6.2 Platform Support Matrix

| Structure | x86-64 | ARM64 | Other* |
|-----------|--------|-------|--------|
| SkipListMap/Set | Full | Full | Full |
| TreeMap/Set | Full | Full | Full |
| LockFreeQueue (SCQ) | Full | Full | Full |
| FastQueue | LCRQ | SCQ | SCQ |
| WaitFreeQueue | Full | Full | Full |
| LockFreeStack | Full | Full | Full |

*Other includes RISC-V, PowerPC, SPARC, etc.—any platform with C11 atomics support.

### 6.3 Architecture Detection & Selection

```
┌─────────────────────────────────────────────────────────────┐
│                      FastQueue                               │
├─────────────────────────────────────────────────────────────┤
│  Compile-time:                                               │
│    #if defined(__x86_64__) && defined(__CMPXCHG16B__)       │
│        → Build includes LCRQ code path                       │
│    #endif                                                    │
│    → Always build SCQ code path                              │
│                                                              │
│  Runtime:                                                    │
│    x86-64 with CMPXCHG16B?  ──yes──►  LCRQ (best throughput)│
│           │                                                  │
│           no                                                 │
│           ▼                                                  │
│        SCQ (portable, still excellent)                       │
└─────────────────────────────────────────────────────────────┘
```

### 6.4 Wheel Distribution

| Platform Tag | Architecture | Notes |
|--------------|--------------|-------|
| `manylinux_2_28_x86_64` | Linux x86-64 | Primary, includes LCRQ |
| `manylinux_2_28_aarch64` | Linux ARM64 | Graviton, Ampere, etc. |
| `musllinux_1_2_x86_64` | Alpine x86-64 | Container-friendly |
| `musllinux_1_2_aarch64` | Alpine ARM64 | Container-friendly |
| `macosx_11_0_arm64` | macOS Apple Silicon | M1/M2/M3 |
| `macosx_10_15_x86_64` | macOS Intel | Legacy support |
| `win_amd64` | Windows x86-64 | Includes LCRQ |

### 6.5 Architecture-Specific Optimizations

| Optimization | x86-64 | ARM64 | Portable |
|--------------|--------|-------|----------|
| Cache line padding | 64 bytes | 64/128 bytes* | 64 bytes |
| Memory barriers | `mfence`, `sfence` | `dmb`, `dsb` | C11 atomics |
| Atomic operations | Native CAS, FAA | LSE when available | C11 atomics |
| Backoff strategy | `pause` instruction | `yield` | Spin loop |

*ARM64 uses 128-byte padding when targeting Apple Silicon (128-byte cache lines).

---

## 7. Performance Characteristics

### 7.1 Competitive Baselines

| Operation | Baseline | Target Speedup (Free-threaded, 8 threads) |
|-----------|----------|-------------------------------------------|
| Ordered map | `sortedcontainers` + Lock | 5-10x |
| Queue throughput | `queue.Queue` | 3-5x |
| Stack throughput | `list` + Lock | 3-5x |

### 7.2 GIL State Impact

#### Single-Threaded Performance

| Library | ops/sec (GIL) | ops/sec (no GIL) |
|---------|---------------|------------------|
| `dict` (baseline) | 15.2M | 14.8M |
| `sortedcontainers.SortedDict` | 890K | 870K |
| `concurrent_collections.SkipListMap` | 820K | 780K |
| `concurrent_collections.TreeMap` | 750K | 720K |

**Takeaway**: Under GIL, we're ~8% slower than `sortedcontainers` in single-threaded use due to fine-grained locking infrastructure.

#### Multi-Threaded Scaling (SkipListMap)

**GIL-Enabled Python**:

| Threads | `SortedDict` + Lock | `SkipListMap` |
|---------|---------------------|---------------|
| 1 | 890K | 820K |
| 2 | 520K | 810K |
| 4 | 310K | 800K |
| 8 | 180K | 790K |

**Takeaway**: Under GIL, coarse-locked containers degrade. Our fine-grained locked backend maintains throughput.

**Free-Threaded Python**:

| Threads | `SortedDict` + Lock | `SkipListMap` |
|---------|---------------------|---------------|
| 1 | 870K | 780K |
| 2 | 480K | 1.45M |
| 4 | 250K | 2.70M |
| 8 | 130K | 4.80M |
| 16 | 70K | 6.20M |

**Takeaway**: Free-threaded Python + lock-free = true scaling. At 8 threads, 37x faster than locked alternatives.

#### Queue Comparison

| Implementation | ops/sec @ 1 thread | ops/sec @ 8 threads |
|----------------|-------------------|---------------------|
| `queue.Queue` (GIL) | 1.2M | 340K |
| `queue.Queue` (no GIL) | 1.1M | 180K |
| `LockFreeQueue` (GIL) | 980K | 920K |
| `LockFreeQueue` (no GIL) | 950K | 5.8M |
| `FastQueue/LCRQ` (no GIL) | 1.0M | 8.2M |

### 7.3 Memory Overhead

| Structure | Overhead per Entry |
|-----------|-------------------|
| `dict` | ~50 bytes |
| `sortedcontainers.SortedDict` | ~70 bytes |
| `SkipListMap` (locked backend) | ~56 bytes |
| `SkipListMap` (lock-free backend) | ~72 bytes |

Lock-free backend overhead due to:
- Cache line padding for false sharing prevention
- SMR metadata per node
- Atomic pointer wrappers

### 7.4 When to Use This Library

| Scenario | Recommendation |
|----------|---------------|
| Free-threaded Python, concurrent access | **Use `concurrent_collections`** |
| Preparing for free-threaded migration | **Use `concurrent_collections`** (same API, ready when you switch) |
| GIL Python, I/O-bound, light data structure use | Use `concurrent_collections` (overhead negligible) |
| GIL Python, CPU-bound, single structure is bottleneck | Benchmark against `sortedcontainers` |
| Need absolute maximum single-thread perf | Use `sortedcontainers` or stdlib |

---

## 8. Testing Strategy

### 8.1 Correctness Testing

| Test Type | Purpose |
|-----------|---------|
| Unit tests | Basic functionality, edge cases |
| Stress tests | Random operations from many threads |
| Linearizability tests | Verify operations are linearizable |
| Sanitizer runs | TSAN, ASAN, MSAN for memory/race bugs |

### 8.2 Backend-Specific Testing

| Test | Purpose |
|------|---------|
| Lock-free activation | Verify lock-free selected when GIL disabled |
| Locked activation | Verify locked selected when GIL enabled |
| Backend override | Verify `config.force_backend` works |
| LCRQ activation | Verify LCRQ selected on x86-64 with CMPXCHG16B |
| SCQ fallback | Verify SCQ used on ARM64 |

### 8.3 Platform Test Matrix

| Platform | Python Versions | Backends Tested |
|----------|-----------------|-----------------|
| Linux x86-64 | 3.13, 3.13t | locked, lock_free, LCRQ |
| Linux ARM64 | 3.13, 3.13t | locked, lock_free, SCQ |
| macOS x86-64 | 3.13, 3.13t | locked, lock_free, LCRQ |
| macOS ARM64 | 3.13, 3.13t | locked, lock_free, SCQ |
| Windows x86-64 | 3.13, 3.13t | locked, lock_free, LCRQ |

### 8.4 Stress Test Patterns

```
Pattern 1: Uniform random
  - Random mix of operations
  - Random keys from large space
  - Tests general correctness

Pattern 2: Hot spot
  - 80% of operations on 20% of keys
  - Tests contention handling

Pattern 3: Producer-consumer
  - Dedicated producer/consumer threads
  - Tests queue/stack under asymmetric load

Pattern 4: Range scan + mutation
  - Concurrent range iterations and modifications
  - Tests snapshot isolation of iterators
```

---

## 9. Documentation Plan

### 9.1 User Documentation

- **Getting Started**: Installation, basic usage
- **API Reference**: Complete method documentation
- **Choosing the Right Structure**: Decision guide for different use cases
- **GIL vs Free-Threaded**: Performance characteristics, when to use
- **Custom Comparators**: Python and Cython approaches
- **Performance Tuning**: Configuration options, NUMA awareness
- **Migration Guide**: From `queue.Queue`, `sortedcontainers`, etc.

### 9.2 Developer Documentation

- **Architecture Overview**: Component design, backend selection
- **SMR Deep Dive**: Memory reclamation explained
- **Contributing Guide**: Code style, testing requirements
- **Benchmarking Guide**: How to run and interpret benchmarks

---

## 10. Future Directions

### 10.1 Potential Additions (Post-1.0)

| Structure | Algorithm | Notes |
|-----------|-----------|-------|
| ConcurrentHashMap | Split-ordered list | Lock-free unordered map |
| PriorityQueue | Lock-free skip list heap | Different interface than ordered map |
| Deque | Lock-free doubly-linked | More complex than queue |
| NUMA-aware variants | Node Replication | For large NUMA systems |

### 10.2 Stdlib Consideration

If `concurrent_collections` gains adoption and proves stable, propose PEP for stdlib inclusion as `concurrent.collections`. The external package serves as proving ground.

### 10.3 C API Exposure

Consider exposing C API for other extension authors:
- SMR primitives
- Atomic utilities
- Backoff helpers
- Comparator interface

### 10.4 Recipes Promotion

Monitor usage of `recipes.BoundedSkipListMap`. Promote to core if demand warrants.

---

## 11. References

### Algorithms

1. Fraser, K. (2004). "Practical Lock-Freedom" (PhD Thesis) — Skip list
2. Natarajan, A. & Mittal, N. (2014). "Fast Concurrent Lock-Free Binary Search Trees" — BST
3. Nikolaev, R. & Ravindran, B. (2019). "A Scalable, Portable Lock-Free FIFO Queue" — SCQ
4. Morrison, A. & Afek, Y. (2013). "Fast Concurrent Queues for x86 Processors" — LCRQ
5. Nikolaev, R. et al. (2022). "wCQ: A Fast Wait-Free Queue" — wCQ
6. Wen, H. et al. (2018). "Interval-Based Memory Reclamation" — IBR
7. Brown, T. (2015). "Reclaiming Memory for Lock-Free Data Structures" — DEBRA+

### Prior Art

- Java: `java.util.concurrent.ConcurrentSkipListMap`
- C++: folly::ConcurrentSkipList, Intel TBB
- Rust: crossbeam, flurry

---

## Appendix A: Resolved Design Decisions

### A.1 Iterator Semantics

**Decision**: Weakly consistent by default, `snapshot()` returns `FrozenSkipListMap`.

**Rationale**: 
- Weakly consistent matches Java's ConcurrentSkipListMap and community expectations
- Snapshot via immutable frozen type provides explicit point-in-time consistency
- FrozenSkipListMap is hashable, can be used as dict keys
- Clear API distinction between "live traversal" and "frozen snapshot"

### A.2 Custom Comparators

**Decision**: Natural ordering default, support Python callables, key functions, and C comparators.

**Rationale**:
- Natural ordering covers 90%+ of use cases with zero overhead
- Python callables provide flexibility for prototyping
- C comparators via Cython enable production performance
- Comprehensive Cython documentation lowers barrier to fast custom ordering

### A.3 Bounded Containers

**Decision**: Unbounded by default, `BoundedSkipListMap` in recipes module.

**Rationale**:
- Bounded concurrent containers add significant complexity
- Size tracking under concurrency has inherent races
- Minority use case shouldn't complicate the core API
- Recipes module signals "useful but not primary"

### A.4 GIL Adaptation

**Decision**: Runtime detection with dual backends (lock-free and locked).

**Rationale**:
- Users shouldn't need to know or care about GIL state
- Lock-free overhead not justified when GIL serializes everything
- Fine-grained locked backend competitive under GIL
- Same API regardless of backend enables migration
- Comprehensive benchmarks document tradeoffs

---

## Appendix B: Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Subtle concurrency bug | Medium | High | Extensive testing, TSAN, linearizability checking |
| Performance below targets | Low | Medium | Benchmark early and often |
| Python C API complexity | Medium | Medium | Study existing extensions, test on multiple versions |
| Platform compatibility | Medium | Low | CI on all target platforms |
| mimalloc integration issues | Low | Medium | Test with mimalloc debug mode |
| Dual backend maintenance burden | Medium | Medium | Share code where possible, comprehensive test matrix |
