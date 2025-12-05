# Design Capture — Concurrent Collections

## Purpose

This document provides the technical home base for the `concurrent_collections` project. The goal is to create production-ready, lock-free data structures for Python 3.13+ that scale on free-threaded Python while remaining competitive on GIL-enabled Python.

This documentation set enables:
- Implementation from the ground up
- Future porting to other languages/runtimes
- Formal verification of concurrency properties
- Team collaboration and onboarding

---

## Project Configuration

| Field | Value |
|-------|-------|
| Project Name | concurrent_collections |
| Target Runtime | Python 3.13+ (free-threaded and GIL-enabled) |
| License | BSD-3-Clause (CPython compatible) |
| Design Docs Root | `doc/design/` |
| Authoritative Tier List | `doc/design/porting-order.md` |
| Templates Directory | `doc/design/_templates/` |
| High-Level Design | `doc/Design.v3.md` |
| Implementation Root | `src/concurrent_collections/` |
| Tests Root | `tests/` |

### Scope

| Category | Status | Notes |
|----------|--------|-------|
| Ordered Maps (SkipListMap, TreeMap) | ✅ | Lock-free, O(log n), range queries |
| Ordered Sets (SkipListSet, TreeSet) | ✅ | Lock-free, O(log n), range iteration |
| Frozen Variants | ✅ | Immutable snapshots, hashable |
| MPMC Queues | ✅ | SCQ (portable), LCRQ (x86-64), wCQ (wait-free) |
| MPMC Stack | ✅ | Treiber with elimination backoff |
| Custom Comparators | ✅ | Natural, Python callable, C function |
| Dual Backend (lock-free/locked) | ✅ | Runtime GIL detection, adaptive selection |
| SMR (memory reclamation) | ✅ | IBR primary, DEBRA+ alternative |
| Bounded Containers | ✅ | recipes.BoundedSkipListMap |
| Distribution/RPC | ❌ | Out of scope—single process only |
| Persistence | ❌ | Out of scope—in-memory only |
| Unordered HashMap | ⏸️ | Defer to post-1.0; split-ordered list candidate |
| Priority Queue | ⏸️ | Defer to post-1.0; skip list heap candidate |
| Deque | ⏸️ | Defer to post-1.0; complex lock-free doubly-linked |

Legend: ✅ In scope, ⏸️ Deferred, ❌ Excluded

### Formal Specification Method

| Primary | Secondary | Notes |
|---------|-----------|-------|
| TLA+ | Property-based testing | TLA+ for concurrency invariants; PBT for implementation validation |

**Rationale:** Lock-free data structures require formal reasoning about linearizability, progress guarantees, and memory reclamation safety. TLA+ excels at modeling these properties. Property-based testing (Hypothesis) validates implementations against specs.

### Reference Materials

| Source | Purpose |
|--------|---------|
| Fraser (2004) "Practical Lock-Freedom" | Skip list algorithm |
| Natarajan & Mittal (PPoPP 2014) | External BST algorithm |
| Nikolaev & Ravindran (2019) | SCQ algorithm |
| Morrison & Afek (2013) | LCRQ algorithm |
| Nikolaev et al. (SPAA 2022) | wCQ algorithm |
| Wen et al. (2018) | IBR algorithm |
| Brown (2015) | DEBRA+ algorithm |
| Java ConcurrentSkipListMap | API design reference |
| CPython 3.13 source | Free-threaded internals, mimalloc |

### Related Documents

| Document | Purpose |
|----------|---------|
| `doc/Design.v3.md` | High-level design document |
| `doc/Design.v2.md` | Previous design iteration |
| `doc/implementation/progress.md` | Implementation progress tracking |
| `doc/report/tier-*.md` | Tier validation reports |
| `ref/complete-design.md` | Documentation methodology |

### Dependent Projects

None currently. Future consideration for stdlib inclusion as `concurrent.collections`.

---

## Implementation Status

### Tier Completion Summary

| Tier | Category | Status | Modules | Tests |
|------|----------|--------|---------|-------|
| 0 | Platform & Utilities | ✅ Complete | 4/4 | 75+ |
| 1 | Comparator System | ✅ Complete | 1/1 | 20+ |
| 2 | Memory Management | ✅ Complete | 3/3 | 25+ |
| 3 | Core Algorithms | ✅ Partial | 3/8 | 48+ |
| 4 | Public API | ✅ Partial | 6/10 | 105+ |
| 5 | Extensions | ⬜ Not started | 0/1 | — |

Legend: ✅ Complete, 🔶 In progress, ⬜ Not started

### Implementation Files

| Tier | Module | File | Status |
|------|--------|------|--------|
| 0 | arch_detect | `_arch_detect.py` | ✅ |
| 0 | atomics | `_atomics.py` | ✅ |
| 0 | backoff | `_backoff.py` | ✅ |
| 0 | config | `_config.py` | ✅ |
| 1 | comparator | `_comparator.py` | ✅ |
| 1 | profiler | `_profiler.py` | ✅ |
| 2 | mimalloc_glue | `_mimalloc_glue.py` | ✅ |
| 2 | smr_ibr | `_smr_ibr.py` | ✅ |
| 2 | smr_debra | `_smr_debra.py` | ✅ |
| 3 | skiplist_locked | `_skiplist.py` | ✅ |
| 3 | treiber | `_treiber.py` | ✅ |
| 3 | scq | `_scq.py` | ✅ |
| 3 | skiplist_lockfree | — | ⬜ |
| 3 | bst_lockfree | — | ⬜ |
| 3 | bst_locked | — | ⬜ |
| 3 | lcrq | — | ⬜ |
| 3 | wcq | — | ⬜ |
| 4 | SkipListMap | `_skiplistmap.py` | ✅ |
| 4 | SkipListSet | `_skiplistset.py` | ✅ |
| 4 | FrozenSkipListMap | `_skiplistmap.py` | ✅ |
| 4 | FrozenSkipListSet | `_skiplistset.py` | ✅ |
| 4 | LockFreeQueue | `_lockfree_queue.py` | ✅ |
| 4 | LockFreeStack | `_lockfree_stack.py` | ✅ |
| 4 | TreeMap | — | ⬜ |
| 4 | TreeSet | — | ⬜ |
| 4 | FastQueue | — | ⬜ |
| 4 | WaitFreeQueue | — | ⬜ |
| 5 | BoundedSkipListMap | — | ⬜ |

---

## Tier Overview

| Tier | Category | Description |
|------|----------|-------------|
| 0 | Platform & Utilities | Architecture detection, atomics, backoff, configuration |
| 1 | Comparator System | Key comparison dispatch (natural, C, Python) |
| 2 | Memory Management | Allocator integration, safe memory reclamation |
| 3 | Core Algorithms | Internal data structure implementations |
| 4 | Public API | User-facing container classes |
| 5 | Extensions | Additional utilities (bounded containers, recipes) |

### Tier Dependencies

```
Tier 0: Platform & Utilities     ← arch_detect, atomics, backoff, config
           │                       [COMPLETE ✅]
           ▼
Tier 1: Comparator System        ← comparator (natural, C func, Python callable)
           │                       [COMPLETE ✅]
           ▼
Tier 2: Memory Management        ← mimalloc_glue, smr_ibr, smr_debra
           │                       [COMPLETE ✅]
           ▼
Tier 3: Core Algorithms          ← skiplist, bst, scq, lcrq, wcq, treiber
           │                       [PARTIAL - Core complete]
           ▼
Tier 4: Public API               ← SkipListMap, TreeMap, Queues, Stack, Frozen*
           │                       [PARTIAL - Core complete]
           ▼
Tier 5: Extensions               ← BoundedSkipListMap, future recipes
                                   [NOT STARTED]
```

---

## Module Breakdown by Tier

### Tier 0: Platform & Utilities

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `arch_detect` | CPU architecture detection, feature flags (CMPXCHG16B, LSE) | Low | ✅ |
| `atomics` | Atomic operations abstraction, memory barriers | Medium | ✅ |
| `backoff` | Exponential backoff, pause/yield instructions | Low | ✅ |
| `config` | Runtime configuration, GIL detection, backend selection | Medium | ✅ |

### Tier 1: Comparator System

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `comparator` | Comparison dispatch, C function registration, key extraction | Medium | ✅ |
| `profiler` | Comparator performance profiling, optimization hints | Low | ✅ |

### Tier 2: Memory Management

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `mimalloc_glue` | mimalloc allocator integration, cross-thread free | Low | ✅ |
| `smr_ibr` | Interval-Based Reclamation implementation | High | ✅ |
| `smr_debra` | DEBRA+ implementation with signal-based neutralization | High | ✅ |

### Tier 3: Core Algorithms

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `skiplist_lockfree` | Fraser lock-free skip list (CAS-based) | High | ⬜ |
| `skiplist_locked` | Fine-grained locked skip list (GIL backend) | Medium | ✅ |
| `bst_lockfree` | Natarajan-Mittal external BST | High | ⬜ |
| `bst_locked` | Fine-grained locked BST (GIL backend) | Medium | ⬜ |
| `scq` | Scalable Circular Queue (portable) | High | ✅ |
| `lcrq` | Linked Concurrent Ring Queue (x86-64 only) | High | ⬜ |
| `wcq` | Wait-free Circular Queue | High | ⬜ |
| `treiber` | Treiber stack with elimination backoff | Medium | ✅ |

### Tier 4: Public API

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `SkipListMap` | Ordered map with dict-like API | Medium | ✅ |
| `SkipListSet` | Ordered set with set-like API | Medium | ✅ |
| `FrozenSkipListMap` | Immutable snapshot, hashable | Low | ✅ |
| `FrozenSkipListSet` | Immutable snapshot, hashable | Low | ✅ |
| `TreeMap` | BST-based ordered map | Medium | ⬜ |
| `TreeSet` | BST-based ordered set | Medium | ⬜ |
| `LockFreeQueue` | MPMC queue using SCQ | Low | ✅ |
| `FastQueue` | MPMC queue with LCRQ optimization | Low | ⬜ |
| `WaitFreeQueue` | MPMC queue with wait-free guarantee | Low | ⬜ |
| `LockFreeStack` | MPMC stack | Low | ✅ |

### Tier 5: Extensions

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `BoundedSkipListMap` | Size-limited SkipListMap wrapper | Low | ⬜ |

---

## Milestones

| Milestone | Tiers Required | Status | Capability Achieved |
|-----------|----------------|--------|---------------------|
| M1: Foundation | Tier 0 | ✅ Complete | Platform abstraction, config working |
| M2: Memory Safe | Tier 0-2 | ✅ Complete | SMR operational, memory bounded |
| M3: Core Containers | Tier 0-4 (core) | ✅ Complete | SkipListMap, Queue, Stack functional |
| M4: Full Containers | Tier 0-4 (all) | 🔶 In progress | All public APIs available |
| M5: Production | Tier 0-5 | ⬜ Not started | Extensions, full docs, benchmarks |

---

## Open Design Questions

| Question | Options | Impact | Status |
|----------|---------|--------|--------|
| SMR thread registration | Explicit register/unregister vs automatic | API ergonomics, safety | Open |
| Frozen snapshot allocation | Copy to new skiplist vs compact array | Memory, iteration perf | Open |
| Queue unbounded growth | Linked segments vs realloc | Memory patterns | Open |
| LCRQ segment size | Fixed 1024 vs configurable | Cache behavior | Open |
| Backoff tuning | Fixed params vs adaptive | Contention response | Open |

---

## Resolved Design Decisions

| Decision | Choice | Rationale | Alternatives Considered |
|----------|--------|-----------|------------------------|
| Iterator semantics | Weakly consistent default, snapshot() for frozen | Matches Java, performance | Snapshot-only (memory cost) |
| Custom comparators | Natural default + C/Python options | Performance + flexibility | Natural only (limiting) |
| Bounded containers | recipes module, not core | Minority use case | Core class (API bloat) |
| GIL adaptation | Runtime detect, dual backend | Transparent to user | Single backend (suboptimal) |
| Frozen type | FrozenSkipListMap (hashable) | Can be dict key | Return dict (loses ordering) |
| SMR scheme | IBR primary, DEBRA+ configurable | Bounded memory, good perf | Hazard pointers (overhead) |
| Python version | 3.11+ for development, 3.13+ target | Compatibility with free-threading | 3.13+ only |

---

## Module Completion Requirements

### Required Documents Per Module

| File | Purpose | Required |
|------|---------|----------|
| `design.md` | Architecture, algorithms, data structures | **MANDATORY** |
| `spec.md` | Contracts, invariants, behavior | **MANDATORY** |
| `tests.md` | Test coverage mapping | **MANDATORY** |

### Conditional Documents

| File | When Required |
|------|---------------|
| `spec.tla` | All Tier 2-3 modules (concurrency critical) |
| `perf.md` | All Tier 2-4 modules (performance critical) |
| `platform.md` | Modules with platform-specific code (arch_detect, atomics, lcrq) |

---

## TLA+ Specification Guidance

### Required For

All Tier 2-3 modules require TLA+ specifications:

| Module Category | Key Properties to Model |
|-----------------|------------------------|
| SMR (Tier 2) | Safe reclamation, eventual freeing, bounded memory |
| Skip List (Tier 3) | Linearizability, ordering, lock-freedom |
| Queue (Tier 3) | FIFO ordering, lock-freedom, bounded size |
| Stack (Tier 3) | LIFO ordering, lock-freedom |

### Key Invariants

```tla
\* Safe Memory Reclamation
SafeReclamation ==
    \A node \in retired:
        Freed(node) => \A t \in Threads: ~Accessing(t, node)

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
```

---

## File Structure

```
concurrent-collections/
  src/concurrent_collections/
    __init__.py              # Public exports
    _arch_detect.py          # Tier 0: CPU detection
    _atomics.py              # Tier 0: Atomic operations
    _backoff.py              # Tier 0: Backoff strategies
    _config.py               # Tier 0: Configuration
    _comparator.py           # Tier 1: Comparators
    _profiler.py             # Tier 1: Profiling
    _mimalloc_glue.py        # Tier 2: Allocator
    _smr_ibr.py              # Tier 2: IBR
    _smr_debra.py            # Tier 2: DEBRA+
    _smr.py                  # Tier 2: SMR compatibility
    _skiplist.py             # Tier 3: Skip list (locked)
    _treiber.py              # Tier 3: Treiber stack
    _scq.py                  # Tier 3: SCQ
    _skiplistmap.py          # Tier 4: SkipListMap
    _skiplistset.py          # Tier 4: SkipListSet
    _lockfree_queue.py       # Tier 4: LockFreeQueue
    _lockfree_stack.py       # Tier 4: LockFreeStack

  tests/
    test_arch_detect.py      # Tier 0 tests
    test_atomics.py
    test_backoff.py
    test_config.py
    test_comparator.py       # Tier 1 tests
    test_profiler.py
    test_mimalloc_glue.py    # Tier 2 tests
    test_smr_ibr.py
    test_smr_debra.py
    test_treiber.py          # Tier 3 tests
    test_queue.py
    test_skiplistmap.py      # Tier 4 tests
    test_skiplistset.py

  doc/design/
    design-capture.md        # THIS DOCUMENT
    porting-order.md         # Module list and tiers
    _templates/              # Document templates
    tier-0/                  # Tier 0 design docs
    tier-1/                  # Tier 1 design docs
    tier-2/                  # Tier 2 design docs
    tier-3/                  # Tier 3 design docs
    tier-4/                  # Tier 4 design docs
    tier-5/                  # Tier 5 design docs

  doc/report/
    tier-0.md                # Tier 0 validation report
    tier-1.md                # Tier 1 validation report
    tier-2.md                # Tier 2 validation report
```

---

## Cross-Cutting Concerns

| Concern | Affected Tiers | Notes |
|---------|----------------|-------|
| Error handling | All | Python exceptions, C error codes |
| Thread safety | 2-4 | Linearizability required |
| Memory safety | 2-3 | SMR must prevent use-after-free |
| Platform abstraction | 0, 3 | x86-64 vs ARM64 vs portable |
| GIL compatibility | 0, 3, 4 | Dual backend support |
| Reference counting | 4 | Python object lifecycle |
| GC integration | 4 | Cyclic reference handling |

---

## Semantic Requirements

The implementation must provide these guarantees:

| Requirement | Specification | Modules Affected |
|-------------|---------------|------------------|
| Linearizability | All operations appear atomic | All Tier 3-4 |
| Lock-free progress | System-wide progress guaranteed | All Tier 3-4 (lock-free backend) |
| Wait-free progress | Per-thread progress bounded | WaitFreeQueue only |
| FIFO ordering | Queue maintains insertion order | scq, lcrq, wcq |
| LIFO ordering | Stack maintains LIFO order | treiber |
| Sorted ordering | Map/Set maintain key order | skiplist, bst |
| Memory safety | No use-after-free, no leaks | All |
| Snapshot consistency | Frozen views are immutable | Frozen* classes |

---

## Performance Targets

| Operation | Target (single-thread) | Target (8 threads, no GIL) |
|-----------|----------------------|---------------------------|
| SkipListMap get | 800K ops/sec | 5M+ ops/sec |
| SkipListMap put | 700K ops/sec | 4M+ ops/sec |
| Queue enqueue/dequeue | 1M ops/sec | 6M+ ops/sec |
| Stack push/pop | 1M ops/sec | 5M+ ops/sec |

---

## Session Handoff Checklist

- [ ] All modules worked on have ALL MANDATORY files
- [ ] TLA+ specifications parse and type-check
- [ ] Open questions updated with current thinking
- [ ] Tier completion status updated in this document
- [ ] Next priority identified
- [ ] Any blockers documented
- [ ] Tests pass: `pytest tests/`
- [ ] Imports work: `from concurrent_collections import *`

---

## Next Priorities

1. **TreeMap/TreeSet** — BST-based containers (requires bst_locked implementation)
2. **FastQueue** — LCRQ optimization for x86-64
3. **WaitFreeQueue** — Wait-free queue implementation
4. **BoundedSkipListMap** — Size-limited container extension
5. **TLA+ specifications** — Formal verification of concurrency properties

---

## Revision History

| Date | Changes |
|------|---------|
| 2024-12-05 | Added implementation status tracking, milestones, file structure |
| 2024-12-04 | Initial design capture document |
