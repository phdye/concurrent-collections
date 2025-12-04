# Tier 3: Core Algorithms

## Overview

Core algorithms implement the internal lock-free and locked data structure primitives. These are not exposed directly to users but provide the foundation for the public API in Tier 4.

## Dependencies

- Tier 0-2 (Platform, Comparator, Memory Management)

## Modules

| Module | Description | Complexity |
|--------|-------------|------------|
| `skiplist_lockfree` | Fraser lock-free skip list, CAS-based insert/delete | High |
| `skiplist_locked` | Fine-grained locked skip list for GIL backend | Medium |
| `bst_lockfree` | Natarajan-Mittal external BST | High |
| `bst_locked` | Fine-grained locked BST for GIL backend | Medium |
| `scq` | Scalable Circular Queue (portable, single-width CAS) | High |
| `lcrq` | Linked Concurrent Ring Queue (x86-64, double-width CAS) | High |
| `wcq` | Wait-free Circular Queue | High |
| `treiber` | Treiber stack with elimination backoff | Medium |

## Completion Criteria

### Skip List
- [ ] `skiplist_lockfree` implements Fraser's algorithm
- [ ] Insert, delete, find all lock-free
- [ ] Probabilistic level selection (geometric distribution)
- [ ] Supports range iteration (weakly consistent)
- [ ] `skiplist_locked` uses per-level locks
- [ ] Both variants share node structure definition
- [ ] TLA+ spec proves linearizability

### BST
- [ ] `bst_lockfree` implements Natarajan-Mittal
- [ ] External tree structure (keys in leaves)
- [ ] CAS-based edge modification
- [ ] `bst_locked` uses hand-over-hand locking
- [ ] TLA+ spec proves linearizability

### Queues
- [ ] `scq` implements Nikolaev-Ravindran algorithm
- [ ] Works with single-width CAS (portable)
- [ ] `lcrq` implements Morrison-Afek algorithm
- [ ] Uses CMPXCHG16B (x86-64 only)
- [ ] `wcq` provides wait-free guarantee
- [ ] All queues maintain FIFO order
- [ ] Bounded and unbounded modes supported
- [ ] TLA+ specs prove FIFO and progress

### Stack
- [ ] `treiber` implements classic Treiber stack
- [ ] Elimination backoff for high contention
- [ ] Elimination array with timeout
- [ ] TLA+ spec proves LIFO and lock-freedom

### General
- [ ] All lock-free modules integrate with SMR
- [ ] All modules have design.md, spec.md, tests.md, spec.tla, perf.md
- [ ] TSAN clean under stress test
- [ ] Linearizability tests pass (history verification)

## Key Invariants (TLA+)

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

## Algorithm References

| Module | Algorithm | Paper |
|--------|-----------|-------|
| skiplist_lockfree | Fraser's lock-free skip list | Fraser (2004) "Practical Lock-Freedom" |
| bst_lockfree | Natarajan-Mittal external BST | PPoPP 2014 |
| scq | Scalable Circular Queue | Nikolaev & Ravindran (2019) |
| lcrq | Linked Concurrent Ring Queue | Morrison & Afek (2013) |
| wcq | Wait-free Circular Queue | SPAA 2022 |
| treiber | Treiber stack | Classic, with elimination from Hendler et al. |
