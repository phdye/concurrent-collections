# TreeMap — Design Document

## Overview

`TreeMap` provides an ordered map backed by a binary search tree (Natarajan-Mittal lock-free BST or locked BST). It offers the same API as `SkipListMap` but with different performance characteristics.

## Public API

Same as `SkipListMap` - implements `MutableMapping[K, V]` with ordered operations.

```python
class TreeMap(MutableMapping[K, V]):
    def __init__(
        self,
        items: Iterable[Tuple[K, V]] = None,
        *,
        cmp: Callable[[K, K], int] = None,
        key: Callable[[K], Any] = None,
        backend: Literal['auto', 'lockfree', 'locked'] = 'auto'
    ): ...

    # Same methods as SkipListMap
```

## When to Use TreeMap vs SkipListMap

| Aspect | TreeMap | SkipListMap |
|--------|---------|-------------|
| Memory | Lower (no level pointers) | Higher (multi-level) |
| Range queries | Slower (tree traversal) | Faster (linked lists) |
| Point queries | Similar | Similar |
| Insert/Delete | Similar | Similar |
| Iteration | In-order traversal | Follow level-0 links |

### Recommendation

- **SkipListMap**: Default choice, better for range queries
- **TreeMap**: When memory is constrained

## Usage

```python
from concurrent_collections import TreeMap

m = TreeMap()
m['x'] = 1
m['y'] = 2
m['z'] = 3

# Same API as SkipListMap
print(m.first_key())  # 'x'
print(list(m.keys('x', 'z')))  # ['x', 'y']
```

## Performance

| Operation | Expected | Notes |
|-----------|----------|-------|
| get/put/delete | O(log n) | May degrade if unbalanced |
| first/last | O(log n) | Must traverse to leaf |
| range | O(log n + k) | In-order traversal |
