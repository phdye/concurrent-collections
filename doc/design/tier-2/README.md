# Tier 2: Memory Management

## Overview

Memory management provides allocator integration and safe memory reclamation (SMR) for lock-free data structures. SMR solves the fundamental problem of when it's safe to free memory that may still be accessed by concurrent readers.

## Dependencies

- Tier 0: `atomics`, `config`

## Modules

| Module | Description | Complexity |
|--------|-------------|------------|
| `mimalloc_glue` | mimalloc allocator integration, allocation/free wrappers | Low |
| `smr_ibr` | Interval-Based Reclamation, epoch tracking, retire lists | High |
| `smr_debra` | DEBRA+ with signal-based neutralization | High |

## Completion Criteria

### mimalloc_glue
- [ ] Allocates/frees through mimalloc
- [ ] Cross-thread frees work correctly

### smr_ibr
- [ ] Tracks epochs per thread
- [ ] Retires nodes to deferred list
- [ ] Reclaims when safe (no thread in old epoch)
- [ ] Handles stalled threads
- [ ] TLA+ spec for safety properties

### smr_debra
- [ ] Implements quiescent state detection
- [ ] Uses signals for neutralization

### General
- [ ] Memory bounded under sustained load (no unbounded growth)
- [ ] TSAN clean under stress test
- [ ] ASAN clean (no use-after-free, no leaks)
- [ ] design.md, spec.md, tests.md, spec.tla, perf.md complete

## Key Invariants (TLA+)

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

## SMR Comparison

| Property | IBR | DEBRA+ | Hazard Pointers |
|----------|-----|--------|-----------------|
| Overhead per access | Low | Low | High (fence) |
| Memory bound | O(T²R) | O(T²R) | O(TR) |
| Stalled thread handling | Yes | Yes (signals) | Yes |
| Complexity | Medium | High | Medium |
