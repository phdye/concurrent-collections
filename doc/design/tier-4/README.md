# Tier 4: Public API

## Overview

The public API tier provides user-facing container classes with Pythonic interfaces. These wrap the core algorithms from Tier 3 and handle Python-specific concerns like reference counting, garbage collection integration, and exception handling.

## Dependencies

- Tier 0-3 (all lower tiers)

## Modules

| Module | Description | Complexity |
|--------|-------------|------------|
| `SkipListMap` | Ordered map, dict-like API, range queries | Medium |
| `SkipListSet` | Ordered set, set-like API, range iteration | Medium |
| `FrozenSkipListMap` | Immutable snapshot, hashable | Low |
| `FrozenSkipListSet` | Immutable snapshot, hashable | Low |
| `TreeMap` | BST-based ordered map | Medium |
| `TreeSet` | BST-based ordered set | Medium |
| `LockFreeQueue` | MPMC queue using SCQ backend | Low |
| `FastQueue` | MPMC queue, LCRQ on x86-64, SCQ elsewhere | Low |
| `WaitFreeQueue` | MPMC queue with wait-free guarantee | Low |
| `LockFreeStack` | MPMC stack using Treiber backend | Low |

## Completion Criteria

### Ordered Maps
- [ ] `SkipListMap` provides dict-like API (`[]`, `.get()`, `del`, `in`, `len`)
- [ ] Atomic operations: `put_if_absent`, `replace`, `replace_if`, `pop`
- [ ] Ordered operations: `first_key`, `last_key`, `floor_key`, `ceiling_key`
- [ ] Range iteration: `keys(start, stop)`, `items(start, stop)`, `values(start, stop)`
- [ ] `snapshot()` returns `FrozenSkipListMap`
- [ ] `TreeMap` provides same API backed by BST
- [ ] Custom comparators work via `cmp=` or `key=` parameter

### Ordered Sets
- [ ] `SkipListSet` provides set-like API (`add`, `discard`, `remove`, `in`, `len`)
- [ ] Ordered operations: `first`, `last`, `floor`, `ceiling`
- [ ] Range iteration: `range(start, stop)`
- [ ] `snapshot()` returns `FrozenSkipListSet`
- [ ] Set operations: `union`, `intersection`, `difference`
- [ ] `TreeSet` provides same API backed by BST

### Frozen Variants
- [ ] `FrozenSkipListMap` supports all read operations
- [ ] Mutation raises `TypeError`
- [ ] `__hash__` works if contents hashable
- [ ] Can be used as dict key
- [ ] `thaw()` returns mutable copy

### Queues
- [ ] `queue.Queue`-compatible API: `put`, `get`, `put_nowait`, `get_nowait`
- [ ] Non-blocking variants: `try_put`, `try_get`
- [ ] `drain(max_items)` for bulk dequeue
- [ ] `FastQueue` auto-selects LCRQ on x86-64
- [ ] `WaitFreeQueue` provides bounded latency guarantee

### Stack
- [ ] `push`, `pop`, `try_pop`, `peek`
- [ ] `Empty` exception on pop from empty stack

### General
- [ ] All classes integrate with Python GC (`tp_traverse`, `tp_clear`)
- [ ] Reference counting correct for stored objects
- [ ] Backend selection transparent (lock-free vs locked)
- [ ] `comparator_type` attribute available
- [ ] design.md, spec.md, tests.md, perf.md complete
- [ ] Docstrings complete
- [ ] Type stubs (`.pyi`) complete

## API Summary

### SkipListMap

```python
m = SkipListMap()
m[key] = value          # put
value = m[key]          # get (KeyError if missing)
del m[key]              # delete
key in m                # contains
len(m)                  # size

# Atomic operations
m.put_if_absent(key, value)
m.replace(key, new_value)
m.replace_if(key, expected, new)

# Ordered operations
m.first_key()
m.last_key()
m.floor_key(key)
m.ceiling_key(key)

# Range operations
m.keys(start, stop)
m.items(start, stop)
m.values(start, stop)

# Snapshot
frozen = m.snapshot()
```

### Queue

```python
q = LockFreeQueue()
q.put(item)
item = q.get()
item = q.try_get()      # Returns None if empty
items = q.drain(max_n)  # Bulk dequeue
```
