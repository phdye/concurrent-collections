# Concurrent Collections — Module Order

## Overview

This document defines the authoritative module list and implementation order for `concurrent_collections`. Modules are organized into dependency tiers — lower tiers must be complete before higher tiers can begin.

---

## Tier Summary

| Tier | Category | Modules | Description |
|------|----------|---------|-------------|
| 0 | Platform & Utilities | 4 | Architecture detection, atomics, backoff, config |
| 1 | Comparator System | 1 | Key comparison dispatch |
| 2 | Memory Management | 3 | Allocator integration, SMR schemes |
| 3 | Core Algorithms | 8 | Lock-free and locked data structure implementations |
| 4 | Public API | 10 | User-facing container classes |
| 5 | Extensions | 1 | Additional utilities |

**Total:** 27 modules

---

## Tier 0: Platform & Utilities

**Dependencies:** None (platform/compiler provides primitives)

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `arch_detect` | CPU detection (x86-64, ARM64), feature flags (CMPXCHG16B, LSE) | Low | ⬜ |
| `atomics` | Atomic ops abstraction, memory barriers, CAS variants | Medium | ⬜ |
| `backoff` | Exponential backoff, pause/yield, spin limits | Low | ⬜ |
| `config` | Runtime config, GIL detection, backend selection, env vars | Medium | ⬜ |

Legend: ⬜ Not started, 🔶 In progress, ✅ Complete

### Tier 0 Completion Criteria

- [ ] `arch_detect` correctly identifies x86-64 vs ARM64 vs other
- [ ] `arch_detect` detects CMPXCHG16B on x86-64, LSE on ARM64
- [ ] `atomics` provides load/store/CAS/FAA with configurable memory order
- [ ] `atomics` compiles on all target platforms (Linux, macOS, Windows)
- [ ] `backoff` provides tunable exponential backoff with platform-optimal pause
- [ ] `config` detects GIL state via `sys._is_gil_enabled()` or fallback
- [ ] `config` reads environment variables for overrides
- [ ] All modules have design.md, spec.md, tests.md
- [ ] Unit tests pass on all platforms

---

## Tier 1: Comparator System

**Dependencies:** Tier 0 (config for type dispatch)

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `comparator` | Comparison dispatch, C function pointers, key extraction | Medium | ⬜ |

### Tier 1 Completion Criteria

- [ ] Natural ordering works via `PyObject_RichCompare`
- [ ] C function comparators callable without Python overhead
- [ ] Python callable comparators work (with documented overhead)
- [ ] Key functions (like `sorted(key=...)`) extract key once at insertion
- [ ] Built-in comparators: `reverse()`, `numeric()`, `string()`
- [ ] Cython integration documented with examples
- [ ] `comparator_type` attribute reports active type
- [ ] design.md, spec.md, tests.md complete

---

## Tier 2: Memory Management

**Dependencies:** Tier 0 (atomics, config)

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `mimalloc_glue` | mimalloc integration, allocation/free wrappers | Low | ⬜ |
| `smr_ibr` | Interval-Based Reclamation, epoch tracking, retire lists | High | ⬜ |
| `smr_debra` | DEBRA+ with signal-based neutralization | High | ⬜ |

### Tier 2 Completion Criteria

- [ ] `mimalloc_glue` allocates/frees through mimalloc
- [ ] Cross-thread frees work correctly
- [ ] `smr_ibr` tracks epochs per thread
- [ ] `smr_ibr` retires nodes to deferred list
- [ ] `smr_ibr` reclaims when safe (no thread in old epoch)
- [ ] `smr_ibr` handles stalled threads
- [ ] `smr_debra` implements quiescent state detection
- [ ] `smr_debra` uses signals for neutralization
- [ ] Memory bounded under sustained load (no unbounded growth)
- [ ] TSAN clean under stress test
- [ ] ASAN clean (no use-after-free, no leaks)
- [ ] TLA+ spec for IBR safety properties
- [ ] design.md, spec.md, tests.md, spec.tla, perf.md complete

### Key Invariants (TLA+)

```tla
\* No thread accesses a freed node
SafeReclamation ==
    \A node \in retired:
        Freed(node) => \A t \in Threads: ~Accessing(t, node)

\* Retired nodes eventually freed (liveness)
EventualReclamation ==
    \A node \in retired: <>(Freed(node))

\* Memory bounded
BoundedMemory ==
    Cardinality(retired) <= O(Threads^2 * RetireThreshold)
```

---

## Tier 3: Core Algorithms

**Dependencies:** Tier 0-2

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `skiplist_lockfree` | Fraser lock-free skip list, CAS-based insert/delete | High | ⬜ |
| `skiplist_locked` | Fine-grained locked skip list for GIL backend | Medium | ⬜ |
| `bst_lockfree` | Natarajan-Mittal external BST | High | ⬜ |
| `bst_locked` | Fine-grained locked BST for GIL backend | Medium | ⬜ |
| `scq` | Scalable Circular Queue (portable, single-width CAS) | High | ⬜ |
| `lcrq` | Linked Concurrent Ring Queue (x86-64, double-width CAS) | High | ⬜ |
| `wcq` | Wait-free Circular Queue | High | ⬜ |
| `treiber` | Treiber stack with elimination backoff | Medium | ⬜ |

### Tier 3 Completion Criteria

#### Skip List
- [ ] `skiplist_lockfree` implements Fraser's algorithm
- [ ] Insert, delete, find all lock-free
- [ ] Probabilistic level selection (geometric distribution)
- [ ] Supports range iteration (weakly consistent)
- [ ] `skiplist_locked` uses per-level locks
- [ ] Both variants share node structure definition
- [ ] TLA+ spec proves linearizability

#### BST
- [ ] `bst_lockfree` implements Natarajan-Mittal
- [ ] External tree structure (keys in leaves)
- [ ] CAS-based edge modification
- [ ] `bst_locked` uses hand-over-hand locking
- [ ] TLA+ spec proves linearizability

#### Queues
- [ ] `scq` implements Nikolaev-Ravindran algorithm
- [ ] Works with single-width CAS (portable)
- [ ] `lcrq` implements Morrison-Afek algorithm
- [ ] Uses CMPXCHG16B (x86-64 only)
- [ ] `wcq` provides wait-free guarantee
- [ ] All queues maintain FIFO order
- [ ] Bounded and unbounded modes supported
- [ ] TLA+ specs prove FIFO and progress

#### Stack
- [ ] `treiber` implements classic Treiber stack
- [ ] Elimination backoff for high contention
- [ ] Elimination array with timeout
- [ ] TLA+ spec proves LIFO and lock-freedom

#### General
- [ ] All lock-free modules integrate with SMR
- [ ] All modules have design.md, spec.md, tests.md, spec.tla, perf.md
- [ ] TSAN clean under stress test
- [ ] Linearizability tests pass (history verification)

### Key Invariants (TLA+)

```tla
\* Skip list ordering preserved
SkipListOrdered ==
    \A node \in Nodes:
        node.next[0] # NIL => node.key < node.next[0].key

\* Queue FIFO
QueueFIFO ==
    \A i, j \in EnqueueIndices:
        i < j => DequeueOrder(i) < DequeueOrder(j)

\* Lock-free progress
LockFreeProgress ==
    []<>(\E t \in Threads: Completes(t))

\* Linearizability (abstract)
Linearizable ==
    \E linearization \in Permutations(ops):
        LegalSequential(linearization) /\ RespectsRealTime(linearization)
```

---

## Tier 4: Public API

**Dependencies:** Tier 0-3

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `SkipListMap` | Ordered map, dict-like API, range queries | Medium | ⬜ |
| `SkipListSet` | Ordered set, set-like API, range iteration | Medium | ⬜ |
| `FrozenSkipListMap` | Immutable snapshot, hashable | Low | ⬜ |
| `FrozenSkipListSet` | Immutable snapshot, hashable | Low | ⬜ |
| `TreeMap` | BST-based ordered map | Medium | ⬜ |
| `TreeSet` | BST-based ordered set | Medium | ⬜ |
| `LockFreeQueue` | MPMC queue using SCQ backend | Low | ⬜ |
| `FastQueue` | MPMC queue, LCRQ on x86-64, SCQ elsewhere | Low | ⬜ |
| `WaitFreeQueue` | MPMC queue with wait-free guarantee | Low | ⬜ |
| `LockFreeStack` | MPMC stack using Treiber backend | Low | ⬜ |

### Tier 4 Completion Criteria

#### Ordered Maps
- [ ] `SkipListMap` provides dict-like API (`[]`, `.get()`, `del`, `in`, `len`)
- [ ] Atomic operations: `put_if_absent`, `replace`, `replace_if`, `pop`
- [ ] Ordered operations: `first_key`, `last_key`, `floor_key`, `ceiling_key`
- [ ] Range iteration: `keys(start, stop)`, `items(start, stop)`, `values(start, stop)`
- [ ] `snapshot()` returns `FrozenSkipListMap`
- [ ] `TreeMap` provides same API backed by BST
- [ ] Custom comparators work via `cmp=` or `key=` parameter

#### Ordered Sets
- [ ] `SkipListSet` provides set-like API (`add`, `discard`, `remove`, `in`, `len`)
- [ ] Ordered operations: `first`, `last`, `floor`, `ceiling`
- [ ] Range iteration: `range(start, stop)`
- [ ] `snapshot()` returns `FrozenSkipListSet`
- [ ] Set operations: `union`, `intersection`, `difference`
- [ ] `TreeSet` provides same API backed by BST

#### Frozen Variants
- [ ] `FrozenSkipListMap` supports all read operations
- [ ] Mutation raises `TypeError`
- [ ] `__hash__` works if contents hashable
- [ ] Can be used as dict key
- [ ] `thaw()` returns mutable copy

#### Queues
- [ ] `queue.Queue`-compatible API: `put`, `get`, `put_nowait`, `get_nowait`
- [ ] Non-blocking variants: `try_put`, `try_get`
- [ ] `drain(max_items)` for bulk dequeue
- [ ] `FastQueue` auto-selects LCRQ on x86-64
- [ ] `WaitFreeQueue` provides bounded latency guarantee

#### Stack
- [ ] `push`, `pop`, `try_pop`, `peek`
- [ ] `Empty` exception on pop from empty stack

#### General
- [ ] All classes integrate with Python GC (`tp_traverse`, `tp_clear`)
- [ ] Reference counting correct for stored objects
- [ ] Backend selection transparent (lock-free vs locked)
- [ ] `comparator_type` attribute available
- [ ] design.md, spec.md, tests.md, perf.md complete
- [ ] Docstrings complete
- [ ] Type stubs (`.pyi`) complete

---

## Tier 5: Extensions

**Dependencies:** Tier 4

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `BoundedSkipListMap` | Size-limited wrapper with eviction policy | Low | ⬜ |

### Tier 5 Completion Criteria

- [ ] `maxsize` parameter limits entries
- [ ] `eviction='error'` raises `BoundedMapFullError` when full
- [ ] `eviction='oldest'` evicts `first_key()` to make room
- [ ] `is_full()` check available
- [ ] Inherits all `SkipListMap` functionality
- [ ] Documented race conditions under concurrency
- [ ] design.md, spec.md, tests.md complete

---

## Cross-Cutting Concerns

| Concern | Affected Tiers | Approach |
|---------|----------------|----------|
| Error handling | All | Python exceptions from C; error codes internally |
| Logging | 2-4 | Debug logging via Python `logging` module |
| Thread safety | 2-4 | Lock-free algorithms; linearizability verified |
| Memory safety | 2-3 | SMR prevents use-after-free; ASAN in CI |
| Platform support | 0, 3 | Portable C11 with platform-specific optimizations |
| GIL compatibility | 0, 3, 4 | Runtime detection, dual backend |
| Performance testing | 2-4 | Benchmarks in CI, regression detection |

---

## Milestones

| Milestone | Tiers Required | Capability Achieved |
|-----------|----------------|---------------------|
| M1: Foundation | Tier 0 | Platform abstraction, config working |
| M2: Memory Safe | Tier 0-2 | SMR operational, memory bounded |
| M3: Skip List | Tier 0-3 (skiplist only) | First concurrent container functional |
| M4: Full Containers | Tier 0-4 | All public APIs available |
| M5: Production | Tier 0-5 | Extensions, full documentation, benchmarks |

---

## Module Document Requirements

Each module directory must contain:

| File | Required | Notes |
|------|----------|-------|
| `design.md` | **Yes** | Architecture, algorithms, data structures |
| `spec.md` | **Yes** | Contracts, invariants, behavior |
| `tests.md` | **Yes** | Test coverage mapping |
| `spec.tla` | Tier 2-3 | Formal concurrency specification |
| `perf.md` | Tier 2-4 | Performance targets and benchmarks |
| `platform.md` | When applicable | Platform-specific implementation notes |

---

## Platform Test Matrix

| Platform | Python Versions | Backends | Queue Backends |
|----------|-----------------|----------|----------------|
| Linux x86-64 | 3.13, 3.13t | locked, lock_free | SCQ, LCRQ |
| Linux ARM64 | 3.13, 3.13t | locked, lock_free | SCQ |
| macOS x86-64 | 3.13, 3.13t | locked, lock_free | SCQ, LCRQ |
| macOS ARM64 | 3.13, 3.13t | locked, lock_free | SCQ |
| Windows x86-64 | 3.13, 3.13t | locked, lock_free | SCQ, LCRQ |

---

## Revision History

| Date | Author | Changes |
|------|--------|---------|
| 2024-12-04 | Initial | Initial module order based on Design.v3.md |
