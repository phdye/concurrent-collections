# Design Capture — Concurrent Collections

## Purpose

This document provides the technical home base for the `concurrent_collections` project. The goal is to create production-ready, lock-free data structures for Python 3.13+ that scale on free-threaded Python while remaining competitive on GIL-enabled Python. The implementation uses Rust via PyO3 for performance and memory safety.

This documentation set enables:
- Implementation from the ground up
- Formal verification of concurrency properties
- Team collaboration and onboarding

---

## Project Configuration

| Field | Value |
|-------|-------|
| Project Name | concurrent_collections |
| Target Runtime | Python 3.13+ (free-threaded and GIL-enabled) |
| Implementation Language | Rust (stable, 1.75+) via PyO3 |
| Minimum Supported Rust Version (MSRV) | 1.75.0 |
| Build System | maturin |
| License | BSD-3-Clause (CPython compatible) |
| Design Docs Root | `doc/design/` |
| Authoritative Tier List | `doc/design/porting-order.md` |
| Templates Directory | `doc/design/_templates/` |
| High-Level Design | `doc/Design.v3.md` |

### Scope

| Category | Status | Notes |
|----------|--------|-------|
| Ordered Maps (SkipListMap, TreeMap) | ✅ | Lock-free, O(log n), range queries, dict-like API |
| Ordered Sets (SkipListSet, TreeSet) | ✅ | Lock-free, O(log n), range iteration, set-like API |
| Frozen Variants | ✅ | Immutable snapshots, hashable |
| MPMC Queues | ✅ | SCQ (portable), LCRQ (x86-64), wCQ (wait-free) |
| MPMC Stack | ✅ | Treiber with elimination backoff |
| Custom Comparators | ✅ | Natural ordering, Python callable, Rust function |
| Dual Backend (lock-free/locked) | ✅ | Runtime GIL detection, adaptive selection |
| SMR (memory reclamation) | ✅ | Epoch-based (crossbeam-epoch style), DEBRA+ alternative |
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

**Rationale:** Lock-free data structures require formal reasoning about linearizability, progress guarantees, and memory reclamation safety. TLA+ excels at modeling these properties. Property-based testing (proptest/quickcheck) validates implementations against specs.

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
| PyO3 User Guide | Rust-Python bindings |
| crossbeam-epoch | Rust epoch-based reclamation |
| CPython 3.13 source | Free-threaded Python internals |

### Related Documents

| Document | Purpose |
|----------|---------|
| `doc/Design.v3.md` | High-level design document |
| `doc/Design.v2.md` | Previous design iteration |
| `ref/complete-design.md` | Documentation methodology |

### Dependent Projects

None currently. Future consideration for stdlib inclusion as `concurrent.collections`.

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
           │
           ▼
Tier 1: Comparator System        ← comparator (natural, C func, Python callable)
           │
           ▼
Tier 2: Memory Management        ← mimalloc_glue, smr_ibr, smr_debra
           │
           ▼
Tier 3: Core Algorithms          ← skiplist, bst, scq, lcrq, wcq, treiber
           │
           ▼
Tier 4: Public API               ← SkipListMap, TreeMap, Queues, Stack, Frozen*
           │
           ▼
Tier 5: Extensions               ← BoundedSkipListMap, future recipes
```

---

## Module Breakdown by Tier

### Tier 0: Platform & Utilities

| Module | Description | Complexity |
|--------|-------------|------------|
| `arch_detect` | CPU architecture detection, feature flags (CMPXCHG16B, LSE, CAS2) | Low |
| `atomics` | Atomic operations abstraction, memory orderings | Medium |
| `backoff` | Exponential backoff, spin_loop hints | Low |
| `config` | Runtime configuration, feature flags, allocator selection | Medium |

### Tier 1: Comparator System

| Module | Description | Complexity |
|--------|-------------|------------|
| `comparator` | Comparison traits, custom `Ord` implementations, key extraction | Medium |

### Tier 2: Memory Management

| Module | Description | Complexity |
|--------|-------------|------------|
| `allocator` | Custom allocator integration (mimalloc, jemalloc via GlobalAlloc) | Low |
| `smr_epoch` | Epoch-based reclamation (crossbeam-epoch style) | High |
| `smr_debra` | DEBRA+ implementation with quiescent-state detection | High |

### Tier 3: Core Algorithms

| Module | Description | Complexity |
|--------|-------------|------------|
| `skiplist_lockfree` | Fraser lock-free skip list (CAS-based) | High |
| `skiplist_locked` | Fine-grained locked skip list (RwLock-based) | Medium |
| `bst_lockfree` | Natarajan-Mittal external BST | High |
| `bst_locked` | Fine-grained locked BST (RwLock-based) | Medium |
| `scq` | Scalable Circular Queue (portable) | High |
| `lcrq` | Linked Concurrent Ring Queue (x86-64 only) | High |
| `wcq` | Wait-free Circular Queue | High |
| `treiber` | Treiber stack with elimination backoff | Medium |

### Tier 4: Public API

| Module | Description | Complexity |
|--------|-------------|------------|
| `SkipListMap` | Ordered map implementing standard traits | Medium |
| `SkipListSet` | Ordered set implementing standard traits | Medium |
| `FrozenSkipListMap` | Immutable snapshot via `Arc<T>` | Low |
| `FrozenSkipListSet` | Immutable snapshot via `Arc<T>` | Low |
| `TreeMap` | BST-based ordered map | Medium |
| `TreeSet` | BST-based ordered set | Medium |
| `LockFreeQueue` | MPMC queue using SCQ | Low |
| `FastQueue` | MPMC queue with LCRQ optimization | Low |
| `WaitFreeQueue` | MPMC queue with wait-free guarantee | Low |
| `LockFreeStack` | MPMC stack | Low |

### Tier 5: Extensions

| Module | Description | Complexity |
|--------|-------------|------------|
| `BoundedSkipListMap` | Size-limited SkipListMap wrapper | Low |

---

## Open Design Questions

| Question | Options | Impact | Status |
|----------|---------|--------|--------|
| SMR thread registration | Explicit register/unregister vs automatic | API ergonomics, safety | Open |
| Frozen snapshot allocation | Copy to new structure vs compact array | Memory, iteration perf | Open |
| Queue unbounded growth | Linked segments vs realloc | Memory patterns | Open |
| LCRQ segment size | Fixed 1024 vs configurable | Cache behavior | Open |
| Backoff tuning | Fixed params vs adaptive | Contention response | Open |
| PyO3 GIL handling | Release GIL during Rust ops vs hold | Python interop, performance | Open |

---

## Resolved Design Decisions

| Decision | Choice | Rationale | Alternatives Considered |
|----------|--------|-----------|------------------------|
| Implementation language | Rust via PyO3 | Memory safety, performance, no GIL contention in Rust | C extension (manual memory), Cython (still Python-bound) |
| Iterator semantics | Weakly consistent default, snapshot() for frozen | Matches Java, performance | Snapshot-only (memory cost) |
| Custom comparators | Natural default + Python callable option | Flexibility for Python users | Natural only (limiting) |
| Bounded containers | recipes module, not core | Minority use case | Core class (API bloat) |
| GIL adaptation | Runtime detect, dual backend | Transparent to user | Single backend (suboptimal) |
| Frozen type | FrozenSkipListMap (hashable) | Can be dict key | Return dict (loses ordering) |
| SMR scheme | Epoch-based primary (crossbeam-style), DEBRA+ configurable | Bounded memory, good perf | Hazard pointers (overhead) |
| Error handling | Python exceptions via PyO3 | Idiomatic Python | Return codes (not Pythonic) |
| Thread safety | All types are Send + Sync in Rust | Safe concurrent access | Single-threaded only (limiting) |

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

## File Structure

```
doc/design/
  design-capture.md         # THIS DOCUMENT
  porting-order.md          # Module list and tiers
  
  _templates/
    design.md               # Module design template
    spec.md                 # Module spec template
    tests.md                # Module tests template
    spec.tla                # TLA+ template
    perf.md                 # Performance template
    platform.md             # Platform template
  
  tier-0/
    README.md
    arch_detect/
    atomics/
    backoff/
    config/
  
  tier-1/
    README.md
    comparator/
  
  tier-2/
    README.md
    mimalloc_glue/
    smr_ibr/
    smr_debra/
  
  tier-3/
    README.md
    skiplist_lockfree/
    skiplist_locked/
    bst_lockfree/
    bst_locked/
    scq/
    lcrq/
    wcq/
    treiber/
  
  tier-4/
    README.md
    SkipListMap/
    SkipListSet/
    FrozenSkipListMap/
    FrozenSkipListSet/
    TreeMap/
    TreeSet/
    LockFreeQueue/
    FastQueue/
    WaitFreeQueue/
    LockFreeStack/
  
  tier-5/
    README.md
    BoundedSkipListMap/
```

---

## Cross-Cutting Concerns

| Concern | Affected Tiers | Notes |
|---------|----------------|-------|
| Error handling | All | Python exceptions via PyO3, Rust `Result<T, E>` internally |
| Thread safety | 2-4 | Linearizability required, Rust `Send + Sync` bounds |
| Memory safety | 2-3 | Rust ownership + SMR for lock-free structures |
| Platform abstraction | 0, 3 | x86-64 vs ARM64 via `cfg(target_arch)` |
| GIL compatibility | 0, 3, 4 | Dual backend support, release GIL during Rust ops |
| PyO3 integration | 4 | Python object lifecycle, reference counting |
| Unsafe code | 2-3 | Minimized, well-documented, MIRI-tested |

---

## Semantic Requirements

The implementation must provide these guarantees:

| Requirement | Specification | Modules Affected |
|-------------|---------------|------------------|
| Linearizability | All operations appear atomic | All Tier 3-4 |
| Lock-free progress | System-wide progress guaranteed | All Tier 3-4 (lock-free backend) |
| Wait-free progress | Per-thread progress bounded | WaitFreeQueue only |
| FIFO ordering | Queue maintains insertion order | scq, lcrq, wcq |
| Sorted ordering | Map/Set maintain key order | skiplist, bst |
| Memory safety | No use-after-free, no leaks | All |
| Snapshot consistency | Frozen views are immutable | Frozen* classes |

---

## Performance Targets

| Operation | Target (single-thread) | Target (8 threads, free-threaded Python) |
|-----------|----------------------|---------------------------|
| SkipListMap get | 2M ops/sec | 12M+ ops/sec |
| SkipListMap put | 1.5M ops/sec | 10M+ ops/sec |
| Queue enqueue/dequeue | 3M ops/sec | 20M+ ops/sec |
| Stack push/pop | 3M ops/sec | 18M+ ops/sec |

*Note: Rust implementation via PyO3 provides significant speedup over pure Python while maintaining Pythonic API. GIL is released during Rust operations for maximum concurrency on free-threaded Python.*

---

## Session Handoff Checklist

- [ ] All modules worked on have ALL MANDATORY files
- [ ] TLA+ specifications parse and type-check
- [ ] Open questions updated with current thinking
- [ ] Tier completion status updated in porting-order.md
- [ ] Next priority identified
- [ ] Any blockers documented
