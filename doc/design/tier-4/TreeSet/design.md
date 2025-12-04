# TreeSet — Design Document

## Overview

`TreeSet` provides an ordered set backed by a binary search tree. Same API as `SkipListSet`.

## Public API

Same as `SkipListSet` - implements `MutableSet[T]` with ordered operations.

```python
class TreeSet(MutableSet[T]):
    def __init__(
        self,
        items: Iterable[T] = None,
        *,
        cmp: Callable[[T, T], int] = None,
        key: Callable[[T], Any] = None,
        backend: Literal['auto', 'lockfree', 'locked'] = 'auto'
    ): ...
```

## Usage

```python
from concurrent_collections import TreeSet

s = TreeSet([3, 1, 4, 1, 5])
print(list(s))  # [1, 3, 4, 5]
```

## When to Use

- Lower memory usage than SkipListSet
- Similar performance for most operations
- SkipListSet preferred for heavy range iteration
