"""
SkipListMap - Thread-safe ordered map implementation

This module provides SkipListMap, the primary ordered map container with a
dict-like API and concurrent access safety. It wraps the skip list
implementation and provides additional atomic operations.
"""

from collections.abc import MutableMapping
import threading
from typing import (
    Any, Callable, Dict, Generic, Iterator, Literal, Optional,
    Tuple, TypeVar, Union, Iterable
)

from concurrent_collections._skiplist import SkipList
from concurrent_collections._comparator import Comparator, resolve_comparator
from concurrent_collections._config import config


K = TypeVar('K')
V = TypeVar('V')


class SkipListMap(MutableMapping, Generic[K, V]):
    """Thread-safe ordered map based on skip list.

    Provides dict-like API with concurrent access safety. Supports custom
    ordering via comparator or key functions.

    Example:
        >>> m = SkipListMap()
        >>> m['alice'] = 100
        >>> m['bob'] = 200
        >>> print(m['alice'])
        100
        >>> list(m.keys())
        ['alice', 'bob']
    """

    __slots__ = (
        '_skiplist',
        '_comparator',
        '_backend',
        '_lock',
    )

    def __init__(
        self,
        items: Optional[Iterable[Tuple[K, V]]] = None,
        *,
        cmp: Optional[Union[Comparator, Callable[[Any, Any], int]]] = None,
        key: Optional[Callable[[Any], Any]] = None,
        backend: Literal['auto', 'lockfree', 'locked'] = 'auto',
    ):
        """Initialize SkipListMap.

        Args:
            items: Initial key-value pairs
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
        self._skiplist: SkipList[K, V] = SkipList(cmp=self._comparator)
        self._lock = threading.RLock()  # For compound operations

        # Populate with initial items
        if items:
            for k, v in items:
                self._skiplist.insert(k, v)

    # ==========================================================================
    # MutableMapping interface
    # ==========================================================================

    def __getitem__(self, key: K) -> V:
        """Get value for key.

        Args:
            key: Key to look up

        Returns:
            Value associated with key

        Raises:
            KeyError: If key not found
        """
        value = self._skiplist.search(key)
        if value is None:
            raise KeyError(key)
        return value

    def __setitem__(self, key: K, value: V) -> None:
        """Set value for key.

        Args:
            key: Key to set
            value: Value to associate
        """
        self._skiplist.insert(key, value)

    def __delitem__(self, key: K) -> None:
        """Delete key.

        Args:
            key: Key to delete

        Raises:
            KeyError: If key not found
        """
        success, _ = self._skiplist.delete(key)
        if not success:
            raise KeyError(key)

    def __contains__(self, key: object) -> bool:
        """Check if key exists.

        Args:
            key: Key to check

        Returns:
            True if key exists
        """
        return self._skiplist.contains(key)  # type: ignore

    def __len__(self) -> int:
        """Get number of entries.

        Returns:
            Number of key-value pairs
        """
        return len(self._skiplist)

    def __iter__(self) -> Iterator[K]:
        """Iterate over keys in order.

        Yields:
            Keys in sorted order
        """
        return iter(self._skiplist)

    # ==========================================================================
    # Dict-like operations
    # ==========================================================================

    def get(self, key: K, default: Optional[V] = None) -> Optional[V]:
        """Get value for key with default.

        Args:
            key: Key to look up
            default: Default value if not found

        Returns:
            Value or default
        """
        value = self._skiplist.search(key)
        return value if value is not None else default

    def pop(self, key: K, *args: V) -> V:
        """Remove and return value for key.

        Args:
            key: Key to remove
            *args: Optional default value

        Returns:
            Removed value or default

        Raises:
            KeyError: If key not found and no default given
        """
        success, old_value = self._skiplist.delete(key)
        if success:
            return old_value  # type: ignore
        if args:
            return args[0]
        raise KeyError(key)

    def setdefault(self, key: K, default: Optional[V] = None) -> Optional[V]:
        """Get value, setting default if key doesn't exist.

        Args:
            key: Key to look up
            default: Default to set if not present

        Returns:
            Existing or newly set value
        """
        with self._lock:
            value = self._skiplist.search(key)
            if value is not None:
                return value
            self._skiplist.insert(key, default)  # type: ignore
            return default

    def update(self, other: Union[Dict[K, V], Iterable[Tuple[K, V]], None] = None, **kwargs: V) -> None:
        """Update from dict or iterable.

        Args:
            other: Dict or iterable of (key, value) pairs
            **kwargs: Additional key-value pairs
        """
        if other:
            if isinstance(other, dict):
                for k, v in other.items():
                    self._skiplist.insert(k, v)
            else:
                for k, v in other:
                    self._skiplist.insert(k, v)
        for k, v in kwargs.items():
            self._skiplist.insert(k, v)  # type: ignore

    def clear(self) -> None:
        """Remove all entries."""
        # Create new skiplist with same comparator
        self._skiplist = SkipList(cmp=self._comparator)

    # ==========================================================================
    # Atomic operations
    # ==========================================================================

    def put_if_absent(self, key: K, value: V) -> Optional[V]:
        """Insert only if key doesn't exist.

        Args:
            key: Key to insert
            value: Value to insert

        Returns:
            None if inserted, existing value if not
        """
        success, old = self._skiplist.insert(key, value, replace=False)
        if success:
            return None
        return old

    def replace(self, key: K, value: V) -> Optional[V]:
        """Replace value only if key exists.

        Args:
            key: Key to replace
            value: New value

        Returns:
            Old value if replaced, None if key didn't exist
        """
        with self._lock:
            old = self._skiplist.search(key)
            if old is not None:
                self._skiplist.insert(key, value)
                return old
            return None

    def replace_if(self, key: K, old_value: V, new_value: V) -> bool:
        """Replace value only if current value matches.

        Args:
            key: Key to replace
            old_value: Expected current value
            new_value: New value to set

        Returns:
            True if replaced
        """
        with self._lock:
            current = self._skiplist.search(key)
            if current == old_value:
                self._skiplist.insert(key, new_value)
                return True
            return False

    def compute_if_absent(self, key: K, func: Callable[[K], V]) -> V:
        """Compute value if key doesn't exist.

        Args:
            key: Key to look up
            func: Function to compute value (receives key)

        Returns:
            Existing or computed value
        """
        with self._lock:
            value = self._skiplist.search(key)
            if value is not None:
                return value
            computed = func(key)
            self._skiplist.insert(key, computed)
            return computed

    # ==========================================================================
    # Ordered operations
    # ==========================================================================

    def first_key(self) -> K:
        """Get smallest key.

        Returns:
            First (smallest) key

        Raises:
            KeyError: If map is empty
        """
        key = self._skiplist.first_key()
        if key is None:
            raise KeyError("Map is empty")
        return key

    def last_key(self) -> K:
        """Get largest key.

        Returns:
            Last (largest) key

        Raises:
            KeyError: If map is empty
        """
        key = self._skiplist.last_key()
        if key is None:
            raise KeyError("Map is empty")
        return key

    def floor_key(self, key: K) -> Optional[K]:
        """Get greatest key less than or equal to given key.

        Args:
            key: Reference key

        Returns:
            Floor key or None if none exists
        """
        return self._skiplist.floor_key(key)

    def ceiling_key(self, key: K) -> Optional[K]:
        """Get smallest key greater than or equal to given key.

        Args:
            key: Reference key

        Returns:
            Ceiling key or None if none exists
        """
        return self._skiplist.ceiling_key(key)

    def lower_key(self, key: K) -> Optional[K]:
        """Get greatest key strictly less than given key.

        Args:
            key: Reference key

        Returns:
            Lower key or None if none exists
        """
        floor = self._skiplist.floor_key(key)
        if floor is not None and floor != key:
            return floor
        # Need to find strictly less
        for k in self._skiplist.keys(stop=key):
            pass  # Iterate to last before key
        # This is inefficient, but works for now
        result = None
        for k in self._skiplist.keys():
            if self._comparator.compare(
                self._comparator.extract_key(k),
                self._comparator.extract_key(key)
            ) >= 0:
                break
            result = k
        return result

    def higher_key(self, key: K) -> Optional[K]:
        """Get smallest key strictly greater than given key.

        Args:
            key: Reference key

        Returns:
            Higher key or None if none exists
        """
        # Find first key >= key, then skip if equal
        for k in self._skiplist.keys(start=key):
            if k != key:
                return k
        return None

    # ==========================================================================
    # Range operations
    # ==========================================================================

    def keys(
        self,
        start: Optional[K] = None,
        stop: Optional[K] = None,
    ) -> Iterator[K]:
        """Iterate over keys in range.

        Args:
            start: Start key (inclusive)
            stop: Stop key (exclusive)

        Yields:
            Keys in sorted order
        """
        return self._skiplist.keys(start, stop)

    def values(
        self,
        start: Optional[K] = None,
        stop: Optional[K] = None,
    ) -> Iterator[V]:
        """Iterate over values in key order.

        Args:
            start: Start key (inclusive)
            stop: Stop key (exclusive)

        Yields:
            Values in key order
        """
        return self._skiplist.values(start, stop)

    def items(
        self,
        start: Optional[K] = None,
        stop: Optional[K] = None,
    ) -> Iterator[Tuple[K, V]]:
        """Iterate over (key, value) pairs in order.

        Args:
            start: Start key (inclusive)
            stop: Stop key (exclusive)

        Yields:
            Key-value tuples in sorted order
        """
        return self._skiplist.items(start, stop)

    def submap(
        self,
        start: K,
        stop: K,
        inclusive: bool = False,
    ) -> 'SkipListMap[K, V]':
        """Get submap for key range.

        Args:
            start: Start key
            stop: Stop key
            inclusive: If True, include stop key

        Returns:
            New SkipListMap with entries in range
        """
        result: SkipListMap[K, V] = SkipListMap(cmp=self._comparator)
        for k, v in self._skiplist.items(start, stop):
            result[k] = v
        if inclusive:
            stop_val = self._skiplist.search(stop)
            if stop_val is not None:
                result[stop] = stop_val
        return result

    # ==========================================================================
    # Snapshot
    # ==========================================================================

    def snapshot(self) -> 'FrozenSkipListMap[K, V]':
        """Create immutable snapshot.

        Returns:
            FrozenSkipListMap with current contents
        """
        return FrozenSkipListMap(self.items(), cmp=self._comparator)

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
        items = list(self.items())
        if len(items) > 5:
            items_str = ", ".join(f"{k!r}: {v!r}" for k, v in items[:5]) + ", ..."
        else:
            items_str = ", ".join(f"{k!r}: {v!r}" for k, v in items)
        return f"SkipListMap({{{items_str}}})"


class FrozenSkipListMap(Generic[K, V]):
    """Immutable snapshot of a SkipListMap.

    Created via SkipListMap.snapshot(). Supports all read operations
    but raises TypeError on mutation attempts.
    """

    __slots__ = ('_data', '_comparator', '_hash')

    def __init__(
        self,
        items: Optional[Iterable[Tuple[K, V]]] = None,
        *,
        cmp: Optional[Union[Comparator, Callable[[Any, Any], int]]] = None,
        key: Optional[Callable[[Any], Any]] = None,
    ):
        """Initialize FrozenSkipListMap.

        Args:
            items: Initial key-value pairs
            cmp: Comparator or comparison function
            key: Key extraction function
        """
        self._comparator = cmp if isinstance(cmp, Comparator) else resolve_comparator(cmp, key)
        self._data: Dict[K, V] = {}
        self._hash: Optional[int] = None

        if items:
            for k, v in items:
                self._data[k] = v

    def __getitem__(self, key: K) -> V:
        """Get value for key."""
        return self._data[key]

    def __contains__(self, key: object) -> bool:
        """Check if key exists."""
        return key in self._data

    def __len__(self) -> int:
        """Get number of entries."""
        return len(self._data)

    def __iter__(self) -> Iterator[K]:
        """Iterate over keys in sorted order."""
        return iter(sorted(self._data.keys(), key=self._comparator.extract_key))

    def get(self, key: K, default: Optional[V] = None) -> Optional[V]:
        """Get value with default."""
        return self._data.get(key, default)

    def keys(self) -> Iterator[K]:
        """Iterate over keys in sorted order."""
        return iter(self)

    def values(self) -> Iterator[V]:
        """Iterate over values in key order."""
        for k in self:
            yield self._data[k]

    def items(self) -> Iterator[Tuple[K, V]]:
        """Iterate over (key, value) pairs in sorted order."""
        for k in self:
            yield k, self._data[k]

    def first_key(self) -> K:
        """Get smallest key."""
        if not self._data:
            raise KeyError("Map is empty")
        return min(self._data.keys(), key=self._comparator.extract_key)

    def last_key(self) -> K:
        """Get largest key."""
        if not self._data:
            raise KeyError("Map is empty")
        return max(self._data.keys(), key=self._comparator.extract_key)

    def thaw(self) -> SkipListMap[K, V]:
        """Create mutable copy.

        Returns:
            New SkipListMap with same contents
        """
        return SkipListMap(self.items(), cmp=self._comparator)

    def __hash__(self) -> int:
        """Hash (works if contents are hashable)."""
        if self._hash is None:
            self._hash = hash(tuple(sorted(self._data.items())))
        return self._hash

    def __eq__(self, other: object) -> bool:
        """Equality comparison."""
        if isinstance(other, FrozenSkipListMap):
            return self._data == other._data
        return False

    def __repr__(self) -> str:
        """String representation."""
        items = list(self.items())
        if len(items) > 5:
            items_str = ", ".join(f"{k!r}: {v!r}" for k, v in items[:5]) + ", ..."
        else:
            items_str = ", ".join(f"{k!r}: {v!r}" for k, v in items)
        return f"FrozenSkipListMap({{{items_str}}})"

    # Mutation raises TypeError
    def __setitem__(self, key: K, value: V) -> None:
        raise TypeError("FrozenSkipListMap does not support item assignment")

    def __delitem__(self, key: K) -> None:
        raise TypeError("FrozenSkipListMap does not support item deletion")
