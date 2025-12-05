# Concurrent Collections — Module Order

## Overview

This document defines the authoritative module list and implementation order for `concurrent_collections`. Modules are organized into dependency tiers — lower tiers must be complete before higher tiers can begin.

**Target Runtime:** Python 3.13+ (free-threaded and GIL-enabled)
**Implementation Language:** Rust (stable, MSRV 1.75.0) via PyO3
**Build System:** maturin
**Rust Foundation:** ck-rust (`github.com/phdye/ck-rust`, branch `phdye`)

---

## Tier Summary

| Tier | Category | Modules | Description |
|------|----------|---------|-------------|
| 0 | Platform & Utilities | 4 | Architecture detection, atomics, backoff, config |
| 1 | Comparator System | 1 | Key comparison traits and dispatch |
| 2 | Memory Management | 3 | Allocator integration, SMR schemes |
| 3 | Core Algorithms | 8 | Lock-free and locked data structure implementations |
| 4 | Public API | 10 | User-facing container types |
| 5 | Extensions | 1 | Additional utilities |

**Total:** 27 modules

---

## ck-rust Module Mappings

The Rust implementation builds on **ck-rust**, a Rust port of ConcurrencyKit. This eliminates the need to reimplement low-level primitives:

| ck-rust Module | Our Module | Tier | Usage |
|----------------|------------|------|-------|
| `ck::pr` | `atomics` | 0 | Atomic primitives, memory barriers, fences |
| `ck::backoff` | `backoff` | 0 | Exponential backoff, spin hints |
| `ck::cc` | `arch_detect` | 0 | Compiler hints, branch prediction, CPU features |
| `ck::spinlock` | `config` | 0 | Spinlock variants (TAS, CAS, Ticket, MCS, CLH) |
| `ck::epoch` | `smr_epoch` | 2 | Epoch-based safe memory reclamation |
| `ck::hp` | `smr_hp` | 2 | Hazard pointers (alternative SMR) |
| `ck::stack` | `treiber` | 3 | Lock-free Treiber stack |
| `ck::queue` | `scq`, `lcrq` | 3 | Michael-Scott queue, LCRQ |
| `ck::ring` | (internal) | 3 | Ring buffer for queue segments |
| `ck::hs` | (future) | 4 | Concurrent hash set |
| `ck::ht` | (future) | 4 | Concurrent hash table |

### Dependency Configuration

```toml
# Cargo.toml (production - after ck-rust published to crates.io)
[dependencies]
ck = "0.1"
pyo3 = { version = "0.20", features = ["extension-module"] }

# Development (before crates.io publication)
# ck = { git = "https://github.com/phdye/ck-rust", branch = "phdye" }
```

### What We Build vs. What ck-rust Provides

| Category | ck-rust Provides | We Build |
|----------|------------------|----------|
| Atomics | `ck::pr` primitives | PyO3 wrappers, Python API |
| SMR | `ck::epoch`, `ck::hp` | Integration with our containers |
| Stack | `ck::stack` | `LockFreeStack` Python wrapper |
| Queue | `ck::queue`, `ck::ring` | `LockFreeQueue`, `FastQueue` Python wrappers |
| Skip List | — | Full implementation (Fraser algorithm) |
| BST | — | Full implementation (Natarajan-Mittal) |
| Public API | — | All `SkipListMap`, `TreeMap`, etc. |

---

## Tier 0: Platform & Utilities

**Dependencies:** ck-rust (`ck::pr`, `ck::cc`, `ck::backoff`, `ck::spinlock`)

| Module | Description | ck-rust | Complexity | Status |
|--------|-------------|---------|------------|--------|
| `arch_detect` | CPU detection, feature flags | `ck::cc` | Low | ⬜ |
| `atomics` | Atomic ops, memory orderings | `ck::pr` | Medium | ⬜ |
| `backoff` | Exponential backoff, spin hints | `ck::backoff` | Low | ⬜ |
| `config` | Runtime config, spinlock selection | `ck::spinlock` | Medium | ⬜ |

Legend: ⬜ Not started, 🔶 In progress, ✅ Complete

### Tier 0 Completion Criteria

- [ ] `arch_detect` wraps `ck::cc` for CPU feature detection
- [ ] `arch_detect` runtime detection for CMPXCHG16B (x86-64), LSE (aarch64)
- [ ] `atomics` wraps `ck::pr` primitives with PyO3 bindings
- [ ] `atomics` exposes `AtomicInt`, `AtomicPtr`, `AtomicU128` to Python
- [ ] `backoff` wraps `ck::backoff` with Python API
- [ ] `config` provides runtime configuration, spinlock selection from `ck::spinlock`
- [ ] `config` reads environment variables via `std::env`
- [ ] All modules have design.md, spec.md, tests.md
- [ ] `cargo test` passes on all platforms
- [ ] `cargo clippy` clean, `cargo fmt` applied

---

## Tier 1: Comparator System

**Dependencies:** Tier 0 (config for type dispatch)

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `comparator` | Comparison dispatch, Rust `Ord` trait, Python callable support | Medium | ⬜ |

### Tier 1 Completion Criteria

- [ ] Natural ordering works via Rust `Ord` trait for primitive types
- [ ] Python callable comparators work via PyO3 (with documented overhead)
- [ ] Key functions (like `sorted(key=...)`) extract key once at insertion
- [ ] Built-in comparators: `reverse()`, `numeric()`, `string()`
- [ ] `comparator_type` attribute reports active type
- [ ] design.md, spec.md, tests.md complete
- [ ] `cargo test` and `pytest` pass

---

## Tier 2: Memory Management

**Dependencies:** Tier 0, ck-rust (`ck::epoch`, `ck::hp`)

| Module | Description | ck-rust | Complexity | Status |
|--------|-------------|---------|------------|--------|
| `allocator` | Custom allocator integration (mimalloc) | — | Low | ⬜ |
| `smr_epoch` | Epoch-based reclamation | `ck::epoch` | High | ⬜ |
| `smr_debra` | DEBRA+ with quiescent-state detection | — | High | ⬜ |
| `smr_hp` | Hazard pointers (alternative) | `ck::hp` | High | ⬜ |

### Tier 2 Completion Criteria

- [ ] `allocator` integrates mimalloc via Rust's GlobalAlloc trait
- [ ] Cross-thread frees work correctly
- [ ] `smr_epoch` wraps `ck::epoch` with PyO3 bindings
- [ ] `smr_epoch` retires nodes to deferred list
- [ ] `smr_epoch` reclaims when safe (no thread in old epoch)
- [ ] `smr_epoch` handles stalled threads
- [ ] `smr_hp` wraps `ck::hp` for hazard pointer alternative
- [ ] `smr_debra` implements quiescent state detection
- [ ] Memory bounded under sustained load (no unbounded growth)
- [ ] MIRI clean under stress test
- [ ] TLA+ spec for epoch-based safety properties
- [ ] design.md, spec.md, tests.md, spec.tla, perf.md complete
- [ ] `cargo test` passes

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

**Dependencies:** Tier 0-2, ck-rust (`ck::stack`, `ck::queue`, `ck::ring`)

| Module | Description | ck-rust | Complexity | Status |
|--------|-------------|---------|------------|--------|
| `skiplist_lockfree` | Fraser lock-free skip list | — | High | ⬜ |
| `skiplist_locked` | Fine-grained locked skip list | — | Medium | ⬜ |
| `bst_lockfree` | Natarajan-Mittal external BST | — | High | ⬜ |
| `bst_locked` | Fine-grained locked BST | — | Medium | ⬜ |
| `scq` | Scalable Circular Queue | `ck::queue` | High | ⬜ |
| `lcrq` | Linked Concurrent Ring Queue | `ck::queue` | High | ⬜ |
| `wcq` | Wait-free Circular Queue | — | High | ⬜ |
| `treiber` | Treiber stack with elimination | `ck::stack` | Medium | ⬜ |

### Tier 3 Completion Criteria

#### Skip List
- [ ] `skiplist_lockfree` implements Fraser's algorithm in Rust
- [ ] Insert, delete, find all lock-free using `std::sync::atomic`
- [ ] Probabilistic level selection (geometric distribution)
- [ ] Supports range iteration (weakly consistent)
- [ ] `skiplist_locked` uses `RwLock` for per-level locking
- [ ] Both variants share node structure definition
- [ ] TLA+ spec proves linearizability

#### BST
- [ ] `bst_lockfree` implements Natarajan-Mittal in Rust
- [ ] External tree structure (keys in leaves)
- [ ] CAS-based edge modification using `AtomicPtr`
- [ ] `bst_locked` uses `RwLock` for hand-over-hand locking
- [ ] TLA+ spec proves linearizability

#### Queues
- [ ] `scq` wraps `ck::queue` Michael-Scott implementation
- [ ] Works with single-width CAS (portable)
- [ ] `lcrq` wraps `ck::queue` LCRQ variant
- [ ] Uses `AtomicU128` / CMPXCHG16B (x86-64 only, via `cfg(target_arch)`)
- [ ] `wcq` provides wait-free guarantee (custom implementation)
- [ ] All queues maintain FIFO order
- [ ] Bounded and unbounded modes supported
- [ ] TLA+ specs prove FIFO and progress

#### Stack
- [ ] `treiber` wraps `ck::stack` Treiber implementation
- [ ] Elimination backoff for high contention
- [ ] Elimination array with timeout
- [ ] TLA+ spec proves LIFO and lock-freedom

#### General
- [ ] All lock-free modules integrate with SMR (epoch-based)
- [ ] All modules have design.md, spec.md, tests.md, spec.tla, perf.md
- [ ] MIRI clean under stress test
- [ ] Linearizability tests pass (history verification)
- [ ] `cargo test` passes

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
| `SkipListMap` | Ordered map, dict-like Python API, range queries | Medium | ⬜ |
| `SkipListSet` | Ordered set, set-like Python API, range iteration | Medium | ⬜ |
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

#### General (PyO3 Integration)
- [ ] All classes exposed via `#[pyclass]` with `#[pymethods]`
- [ ] GIL released during Rust operations via `py.allow_threads()`
- [ ] Python object reference counting handled via PyO3
- [ ] Backend selection transparent (lock-free vs locked based on GIL detection)
- [ ] `comparator_type` attribute available
- [ ] design.md, spec.md, tests.md, perf.md complete
- [ ] Docstrings complete (via `#[pyo3(text_signature)]`)
- [ ] Type stubs (`.pyi`) complete
- [ ] `pytest` tests pass

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
- [ ] `pytest` tests pass

---

## Cross-Cutting Concerns

| Concern | Affected Tiers | Approach |
|---------|----------------|----------|
| Error handling | All | Python exceptions via PyO3; Rust `Result<T, E>` internally |
| Logging | 2-4 | Debug logging via `tracing` crate + Python `logging` bridge |
| Thread safety | 2-4 | Lock-free algorithms; linearizability verified; Rust `Send + Sync` |
| Memory safety | 2-3 | Rust ownership + SMR for lock-free; MIRI in CI |
| Platform support | 0, 3 | Rust `cfg(target_arch)` with platform-specific optimizations |
| GIL compatibility | 0, 3, 4 | Runtime detection, dual backend, `py.allow_threads()` |
| Performance testing | 2-4 | Criterion.rs benchmarks + pytest-benchmark in CI |
| Build system | All | maturin for Python wheel building |

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

| Platform | Python Versions | Rust Target | Backends | Queue Backends |
|----------|-----------------|-------------|----------|----------------|
| Linux x86-64 | 3.13, 3.13t | x86_64-unknown-linux-gnu | locked, lock_free | SCQ, LCRQ |
| Linux ARM64 | 3.13, 3.13t | aarch64-unknown-linux-gnu | locked, lock_free | SCQ |
| macOS x86-64 | 3.13, 3.13t | x86_64-apple-darwin | locked, lock_free | SCQ, LCRQ |
| macOS ARM64 | 3.13, 3.13t | aarch64-apple-darwin | locked, lock_free | SCQ |
| Windows x86-64 | 3.13, 3.13t | x86_64-pc-windows-msvc | locked, lock_free | SCQ, LCRQ |

---

## Revision History

| Date | Author | Changes |
|------|--------|---------|
| 2024-12-04 | Initial | Initial module order based on Design.v3.md |
| 2025-12-05 | Update | Updated for Rust implementation via PyO3 |
| 2025-12-05 | Update | Added ck-rust as Rust foundation, module mappings |
