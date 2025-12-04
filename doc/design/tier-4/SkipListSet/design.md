# SkipListSet — Design Document

## Overview

`SkipListSet` is an ordered set container providing set operations with concurrent access safety. Built on top of `skiplist_lockfree` or `skiplist_locked`.

## Public API

```python
class SkipListSet(MutableSet[T]):
    def __init__(
        self,
        items: Iterable[T] = None,
        *,
        cmp: Callable[[T, T], int] = None,
        key: Callable[[T], Any] = None,
        backend: Literal['auto', 'lockfree', 'locked'] = 'auto'
    ): ...

    # Set operations
    def add(self, item: T) -> None: ...
    def discard(self, item: T) -> None: ...
    def remove(self, item: T) -> None: ...  # Raises KeyError
    def __contains__(self, item: T) -> bool: ...
    def __len__(self) -> int: ...
    def __iter__(self) -> Iterator[T]: ...

    # Ordered operations
    def first(self) -> T: ...
    def last(self) -> T: ...
    def floor(self, item: T) -> Optional[T]: ...
    def ceiling(self, item: T) -> Optional[T]: ...

    # Range iteration
    def range(self, start: T = None, stop: T = None) -> Iterator[T]: ...

    # Set algebra (returns new sets)
    def union(self, other: Set[T]) -> 'SkipListSet[T]': ...
    def intersection(self, other: Set[T]) -> 'SkipListSet[T]': ...
    def difference(self, other: Set[T]) -> 'SkipListSet[T]': ...
    def symmetric_difference(self, other: Set[T]) -> 'SkipListSet[T]': ...

    # Snapshot
    def snapshot(self) -> 'FrozenSkipListSet[T]': ...
```

## Usage Examples

```python
from concurrent_collections import SkipListSet

s = SkipListSet([3, 1, 4, 1, 5, 9])
print(list(s))  # [1, 3, 4, 5, 9] - sorted, unique

# Ordered operations
print(s.first())  # 1
print(s.last())   # 9
print(s.floor(6))  # 5
print(s.ceiling(6))  # 9

# Range iteration
for x in s.range(2, 6):
    print(x)  # 3, 4, 5

# Concurrent modification safe
def adder(s, base):
    for i in range(100):
        s.add(base + i)

threads = [Thread(target=adder, args=(s, i*100)) for i in range(4)]
```

## Thread Safety

Same as SkipListMap - lock-free or locked backend depending on configuration.

## Performance

| Operation | Complexity |
|-----------|------------|
| add/remove/contains | O(log n) |
| first/last | O(1) |
| floor/ceiling | O(log n) |
| range(k items) | O(log n + k) |
| set operations | O(n + m) |
