# FrozenSkipListSet — Design Document

## Overview

`FrozenSkipListSet` is an immutable snapshot of a `SkipListSet`. Supports all read operations, can be used as a dictionary key.

## Public API

```python
class FrozenSkipListSet(Set[T], Hashable):
    def __init__(self, items: Iterable[T] = None): ...

    # Read operations
    def __contains__(self, item: T) -> bool: ...
    def __len__(self) -> int: ...
    def __iter__(self) -> Iterator[T]: ...

    def first(self) -> T: ...
    def last(self) -> T: ...
    def floor(self, item: T) -> Optional[T]: ...
    def ceiling(self, item: T) -> Optional[T]: ...
    def range(self, start: T = None, stop: T = None) -> Iterator[T]: ...

    # Set algebra (returns FrozenSkipListSet)
    def union(self, other: Set[T]) -> 'FrozenSkipListSet[T]': ...
    def intersection(self, other: Set[T]) -> 'FrozenSkipListSet[T]': ...
    def difference(self, other: Set[T]) -> 'FrozenSkipListSet[T]': ...

    # Hashable
    def __hash__(self) -> int: ...
    def __eq__(self, other) -> bool: ...

    # Convert to mutable
    def thaw(self) -> SkipListSet[T]: ...
```

## Usage

```python
s = SkipListSet([1, 2, 3])
frozen = s.snapshot()

# Read operations
print(3 in frozen)  # True
print(frozen.first())  # 1

# As dict key
cache = {frozen: "result"}

# Mutations fail
frozen.add(4)  # TypeError
```
