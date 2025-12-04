# FrozenSkipListMap — Design Document

## Overview

`FrozenSkipListMap` is an immutable snapshot of a `SkipListMap`. It supports all read operations but raises `TypeError` on mutation attempts. Can be used as a dictionary key if contents are hashable.

## Public API

```python
class FrozenSkipListMap(Mapping[K, V], Hashable):
    def __init__(self, items: Mapping[K, V] = None): ...

    # Read operations (same as SkipListMap)
    def __getitem__(self, key: K) -> V: ...
    def __contains__(self, key: K) -> bool: ...
    def __len__(self) -> int: ...
    def __iter__(self) -> Iterator[K]: ...
    def get(self, key: K, default: V = None) -> V: ...

    def first_key(self) -> K: ...
    def last_key(self) -> K: ...
    def floor_key(self, key: K) -> Optional[K]: ...
    def ceiling_key(self, key: K) -> Optional[K]: ...

    def keys(self, start: K = None, stop: K = None) -> Iterator[K]: ...
    def values(self, start: K = None, stop: K = None) -> Iterator[V]: ...
    def items(self, start: K = None, stop: K = None) -> Iterator[Tuple[K, V]]: ...

    # Hashable
    def __hash__(self) -> int: ...
    def __eq__(self, other) -> bool: ...

    # Convert back to mutable
    def thaw(self) -> SkipListMap[K, V]: ...
```

## Usage

```python
from concurrent_collections import SkipListMap, FrozenSkipListMap

# Create from mutable
m = SkipListMap({'a': 1, 'b': 2})
frozen = m.snapshot()  # or FrozenSkipListMap(m)

# Read operations work
print(frozen['a'])  # 1
print(frozen.first_key())  # 'a'

# Mutations raise TypeError
frozen['c'] = 3  # TypeError: FrozenSkipListMap is immutable

# Use as dict key (if contents hashable)
cache = {frozen: "cached_result"}

# Convert back to mutable
m2 = frozen.thaw()
m2['c'] = 3  # OK
```

## Thread Safety

Fully thread-safe for all read operations - immutability guarantees consistency.

## Implementation

- Backed by a read-only copy of skip list nodes
- No locking required (immutable)
- Hash computed lazily and cached
