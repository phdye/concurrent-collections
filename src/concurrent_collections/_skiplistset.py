"""
SkipListSet - Thread-safe ordered set implementation

This module provides SkipListSet, an ordered set container with a set-like
API and concurrent access safety. It wraps the skip list implementation.
"""

from collections.abc import MutableSet
import threading
from typing import (
    Any, Callable, Generic, Iterator, Literal, Optional,
    Set, TypeVar, Union, Iterable, AbstractSet
)

from concurrent_collections._skiplist import SkipList
from concurrent_collections._comparator import Comparator, resolve_comparator
from concurrent_collections._config import config


T = TypeVar('T')


class SkipListSet(MutableSet, Generic[T]):
    """Thread-safe ordered set based on skip list.

    Provides set-like API with concurrent access safety. Supports custom
    ordering via comparator or key functions.

    Example:
        >>> s = SkipListSet()
        >>> s.add('alice')
        >>> s.add('bob')
        >>> s.add('alice')  # No effect, already exists
        >>> list(s)
        ['alice', 'bob']
        >>> 'alice' in s
        True
    """

    __slots__ = (
        '_skiplist',
        '_comparator',
        '_backend',
        '_lock',
    )

    # Sentinel value for the skiplist (since we're using key-value pairs)
    _PRESENT = object()

    def __init__(
        self,
        items: Optional[Iterable[T]] = None,
        *,
        cmp: Optional[Union[Comparator, Callable[[Any, Any], int]]] = None,
        key: Optional[Callable[[Any], Any]] = None,
        backend: Literal['auto', 'lockfree', 'locked'] = 'auto',
    ):
        """Initialize SkipListSet.

        Args:
            items: Initial items
            cmp: Comparator or comparison function
            key: Key extraction function
            backend: Backend selection ('auto', 'lockfree', 'locked')
        """
        # Resolve backend
        if backend == 'auto':
            self._backend = config.queue_backend
        else:
            self._backend = backend

        # Create underlying skip list
        self._comparator = resolve_comparator(cmp, key)
        self._skiplist: SkipList[T, object] = SkipList(cmp=self._comparator)
        self._lock = threading.RLock()  # For compound operations

        # Populate with initial items
        if items:
            for item in items:
                self._skiplist.insert(item, self._PRESENT, replace=False)

    # ==========================================================================
    # MutableSet interface
    # ==========================================================================

    def add(self, item: T) -> None:
        """Add an item to the set.

        Args:
            item: Item to add

        If the item already exists, this has no effect.
        """
        self._skiplist.insert(item, self._PRESENT, replace=False)

    def discard(self, item: T) -> None:
        """Remove an item if present.

        Args:
            item: Item to remove

        If the item doesn't exist, this has no effect (no exception).
        """
        self._skiplist.delete(item)

    def remove(self, item: T) -> None:
        """Remove an item.

        Args:
            item: Item to remove

        Raises:
            KeyError: If item not found
        """
        success, _ = self._skiplist.delete(item)
        if not success:
            raise KeyError(item)

    def pop(self) -> T:
        """Remove and return an arbitrary item.

        Returns:
            An item from the set

        Raises:
            KeyError: If set is empty
        """
        # Get first item
        key = self._skiplist.first_key()
        if key is None:
            raise KeyError("Set is empty")
        self._skiplist.delete(key)
        return key

    def __contains__(self, item: object) -> bool:
        """Check if item exists.

        Args:
            item: Item to check

        Returns:
            True if item exists
        """
        return self._skiplist.contains(item)  # type: ignore

    def __len__(self) -> int:
        """Get number of items.

        Returns:
            Number of items in set
        """
        return len(self._skiplist)

    def __iter__(self) -> Iterator[T]:
        """Iterate over items in order.

        Yields:
            Items in sorted order
        """
        return iter(self._skiplist)

    # ==========================================================================
    # Set operations
    # ==========================================================================

    def clear(self) -> None:
        """Remove all items."""
        self._skiplist = SkipList(cmp=self._comparator)

    def copy(self) -> 'SkipListSet[T]':
        """Create a shallow copy.

        Returns:
            New SkipListSet with same items
        """
        return SkipListSet(iter(self), cmp=self._comparator)

    def union(self, *others: Iterable[T]) -> 'SkipListSet[T]':
        """Return union with other iterables.

        Args:
            *others: Other iterables

        Returns:
            New set with all items
        """
        result = self.copy()
        for other in others:
            for item in other:
                result.add(item)
        return result

    def __or__(self, other: AbstractSet[T]) -> 'SkipListSet[T]':
        """Union operator."""
        return self.union(other)

    def intersection(self, *others: Iterable[T]) -> 'SkipListSet[T]':
        """Return intersection with other iterables.

        Args:
            *others: Other iterables

        Returns:
            New set with common items
        """
        result: SkipListSet[T] = SkipListSet(cmp=self._comparator)
        other_sets = [set(o) for o in others]

        for item in self:
            if all(item in s for s in other_sets):
                result.add(item)

        return result

    def __and__(self, other: AbstractSet[T]) -> 'SkipListSet[T]':
        """Intersection operator."""
        return self.intersection(other)

    def difference(self, *others: Iterable[T]) -> 'SkipListSet[T]':
        """Return difference with other iterables.

        Args:
            *others: Other iterables

        Returns:
            New set with items not in others
        """
        other_items: Set[Any] = set()
        for other in others:
            other_items.update(other)

        result: SkipListSet[T] = SkipListSet(cmp=self._comparator)
        for item in self:
            if item not in other_items:
                result.add(item)

        return result

    def __sub__(self, other: AbstractSet[T]) -> 'SkipListSet[T]':
        """Difference operator."""
        return self.difference(other)

    def symmetric_difference(self, other: Iterable[T]) -> 'SkipListSet[T]':
        """Return symmetric difference.

        Args:
            other: Other iterable

        Returns:
            New set with items in exactly one set
        """
        other_set = set(other)
        result: SkipListSet[T] = SkipListSet(cmp=self._comparator)

        for item in self:
            if item not in other_set:
                result.add(item)

        for item in other_set:
            if item not in self:
                result.add(item)

        return result

    def __xor__(self, other: AbstractSet[T]) -> 'SkipListSet[T]':
        """Symmetric difference operator."""
        return self.symmetric_difference(other)

    def issubset(self, other: Iterable[T]) -> bool:
        """Check if this is a subset."""
        other_set = set(other)
        return all(item in other_set for item in self)

    def __le__(self, other: AbstractSet[T]) -> bool:
        """Subset or equal operator."""
        return self.issubset(other)

    def __lt__(self, other: AbstractSet[T]) -> bool:
        """Proper subset operator."""
        return len(self) < len(other) and self.issubset(other)

    def issuperset(self, other: Iterable[T]) -> bool:
        """Check if this is a superset."""
        return all(item in self for item in other)

    def __ge__(self, other: AbstractSet[T]) -> bool:
        """Superset or equal operator."""
        return self.issuperset(other)

    def __gt__(self, other: AbstractSet[T]) -> bool:
        """Proper superset operator."""
        other_set = set(other)
        return len(self) > len(other_set) and self.issuperset(other_set)

    def isdisjoint(self, other: Iterable[T]) -> bool:
        """Check if sets have no common items."""
        for item in other:
            if item in self:
                return False
        return True

    # ==========================================================================
    # Ordered operations
    # ==========================================================================

    def first(self) -> T:
        """Get smallest item.

        Returns:
            First (smallest) item

        Raises:
            KeyError: If set is empty
        """
        key = self._skiplist.first_key()
        if key is None:
            raise KeyError("Set is empty")
        return key

    def last(self) -> T:
        """Get largest item.

        Returns:
            Last (largest) item

        Raises:
            KeyError: If set is empty
        """
        key = self._skiplist.last_key()
        if key is None:
            raise KeyError("Set is empty")
        return key

    def floor(self, item: T) -> Optional[T]:
        """Get greatest item less than or equal to given item.

        Args:
            item: Reference item

        Returns:
            Floor item or None if none exists
        """
        return self._skiplist.floor_key(item)

    def ceiling(self, item: T) -> Optional[T]:
        """Get smallest item greater than or equal to given item.

        Args:
            item: Reference item

        Returns:
            Ceiling item or None if none exists
        """
        return self._skiplist.ceiling_key(item)

    # ==========================================================================
    # Range operations
    # ==========================================================================

    def range(
        self,
        start: Optional[T] = None,
        stop: Optional[T] = None,
    ) -> Iterator[T]:
        """Iterate over items in range.

        Args:
            start: Start item (inclusive)
            stop: Stop item (exclusive)

        Yields:
            Items in sorted order
        """
        return self._skiplist.keys(start, stop)

    def subset(
        self,
        start: T,
        stop: T,
        inclusive: bool = False,
    ) -> 'SkipListSet[T]':
        """Get subset for item range.

        Args:
            start: Start item
            stop: Stop item
            inclusive: If True, include stop item

        Returns:
            New SkipListSet with items in range
        """
        result: SkipListSet[T] = SkipListSet(cmp=self._comparator)
        for item in self._skiplist.keys(start, stop):
            result.add(item)
        if inclusive and stop in self:
            result.add(stop)
        return result

    # ==========================================================================
    # Snapshot
    # ==========================================================================

    def snapshot(self) -> 'FrozenSkipListSet[T]':
        """Create immutable snapshot.

        Returns:
            FrozenSkipListSet with current contents
        """
        return FrozenSkipListSet(iter(self), cmp=self._comparator)

    # ==========================================================================
    # Properties
    # ==========================================================================

    @property
    def comparator_type(self) -> str:
        """Get comparator type string."""
        return self._comparator.type

    @property
    def backend_type(self) -> str:
        """Get backend type ('lockfree' or 'locked')."""
        return self._backend

    def __repr__(self) -> str:
        """String representation."""
        items = list(self)
        if len(items) > 5:
            items_str = ", ".join(f"{x!r}" for x in items[:5]) + ", ..."
        else:
            items_str = ", ".join(f"{x!r}" for x in items)
        return f"SkipListSet({{{items_str}}})"

    def __eq__(self, other: object) -> bool:
        """Equality comparison."""
        if isinstance(other, (SkipListSet, FrozenSkipListSet)):
            return len(self) == len(other) and all(x in other for x in self)
        if isinstance(other, (set, frozenset)):
            return len(self) == len(other) and all(x in other for x in self)
        return False


class FrozenSkipListSet(Generic[T]):
    """Immutable snapshot of a SkipListSet.

    Created via SkipListSet.snapshot(). Supports all read operations
    but raises TypeError on mutation attempts. Hashable if contents
    are hashable.
    """

    __slots__ = ('_data', '_comparator', '_hash')

    def __init__(
        self,
        items: Optional[Iterable[T]] = None,
        *,
        cmp: Optional[Union[Comparator, Callable[[Any, Any], int]]] = None,
        key: Optional[Callable[[Any], Any]] = None,
    ):
        """Initialize FrozenSkipListSet.

        Args:
            items: Initial items
            cmp: Comparator or comparison function
            key: Key extraction function
        """
        self._comparator = cmp if isinstance(cmp, Comparator) else resolve_comparator(cmp, key)
        self._data: Set[T] = set()
        self._hash: Optional[int] = None

        if items:
            for item in items:
                self._data.add(item)

    def __contains__(self, item: object) -> bool:
        """Check if item exists."""
        return item in self._data

    def __len__(self) -> int:
        """Get number of items."""
        return len(self._data)

    def __iter__(self) -> Iterator[T]:
        """Iterate over items in sorted order."""
        return iter(sorted(self._data, key=self._comparator.extract_key))

    def first(self) -> T:
        """Get smallest item."""
        if not self._data:
            raise KeyError("Set is empty")
        return min(self._data, key=self._comparator.extract_key)

    def last(self) -> T:
        """Get largest item."""
        if not self._data:
            raise KeyError("Set is empty")
        return max(self._data, key=self._comparator.extract_key)

    def thaw(self) -> SkipListSet[T]:
        """Create mutable copy.

        Returns:
            New SkipListSet with same contents
        """
        return SkipListSet(iter(self), cmp=self._comparator)

    def __hash__(self) -> int:
        """Hash (works if contents are hashable)."""
        if self._hash is None:
            self._hash = hash(frozenset(self._data))
        return self._hash

    def __eq__(self, other: object) -> bool:
        """Equality comparison."""
        if isinstance(other, FrozenSkipListSet):
            return self._data == other._data
        if isinstance(other, (set, frozenset, SkipListSet)):
            return len(self) == len(other) and all(x in other for x in self)
        return False

    def __repr__(self) -> str:
        """String representation."""
        items = list(self)
        if len(items) > 5:
            items_str = ", ".join(f"{x!r}" for x in items[:5]) + ", ..."
        else:
            items_str = ", ".join(f"{x!r}" for x in items)
        return f"FrozenSkipListSet({{{items_str}}})"

    # Set operations return FrozenSkipListSet

    def union(self, *others: Iterable[T]) -> 'FrozenSkipListSet[T]':
        """Return union."""
        result = set(self._data)
        for other in others:
            result.update(other)
        return FrozenSkipListSet(result, cmp=self._comparator)

    def __or__(self, other: AbstractSet[T]) -> 'FrozenSkipListSet[T]':
        return self.union(other)

    def intersection(self, *others: Iterable[T]) -> 'FrozenSkipListSet[T]':
        """Return intersection."""
        result = self._data.copy()
        for other in others:
            result &= set(other)
        return FrozenSkipListSet(result, cmp=self._comparator)

    def __and__(self, other: AbstractSet[T]) -> 'FrozenSkipListSet[T]':
        return self.intersection(other)

    def difference(self, *others: Iterable[T]) -> 'FrozenSkipListSet[T]':
        """Return difference."""
        result = self._data.copy()
        for other in others:
            result -= set(other)
        return FrozenSkipListSet(result, cmp=self._comparator)

    def __sub__(self, other: AbstractSet[T]) -> 'FrozenSkipListSet[T]':
        return self.difference(other)

    def symmetric_difference(self, other: Iterable[T]) -> 'FrozenSkipListSet[T]':
        """Return symmetric difference."""
        return FrozenSkipListSet(self._data ^ set(other), cmp=self._comparator)

    def __xor__(self, other: AbstractSet[T]) -> 'FrozenSkipListSet[T]':
        return self.symmetric_difference(other)

    def issubset(self, other: Iterable[T]) -> bool:
        """Check if subset."""
        return self._data.issubset(other)

    def __le__(self, other: AbstractSet[T]) -> bool:
        return self.issubset(other)

    def issuperset(self, other: Iterable[T]) -> bool:
        """Check if superset."""
        return self._data.issuperset(other)

    def __ge__(self, other: AbstractSet[T]) -> bool:
        return self.issuperset(other)

    def isdisjoint(self, other: Iterable[T]) -> bool:
        """Check if disjoint."""
        return self._data.isdisjoint(other)

    # Mutation raises TypeError
    def add(self, item: T) -> None:
        raise TypeError("FrozenSkipListSet does not support item addition")

    def discard(self, item: T) -> None:
        raise TypeError("FrozenSkipListSet does not support item removal")

    def remove(self, item: T) -> None:
        raise TypeError("FrozenSkipListSet does not support item removal")

    def pop(self) -> T:
        raise TypeError("FrozenSkipListSet does not support pop")

    def clear(self) -> None:
        raise TypeError("FrozenSkipListSet does not support clear")
