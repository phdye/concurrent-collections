"""
skiplist - Thread-safe skip list implementation

This module provides a thread-safe skip list for ordered maps and sets.
The implementation uses fine-grained locking for thread safety.
"""

import random
import threading
from typing import (
    Any, Callable, Dict, Generic, Iterator, List, Optional,
    Tuple, TypeVar, Union
)
from dataclasses import dataclass

from concurrent_collections._comparator import Comparator, resolve_comparator
from concurrent_collections._smr import SMRDomain, SMRGuard, get_default_smr


K = TypeVar('K')
V = TypeVar('V')


# Maximum level for skip list (allows up to 2^32 elements efficiently)
MAX_LEVEL = 32
# Probability for level promotion (1/4 = 0.25)
LEVEL_PROBABILITY = 0.25


def _random_level() -> int:
    """Generate a random level for a new node.

    Returns a level between 0 and MAX_LEVEL-1 with geometric distribution.
    """
    level = 0
    while random.random() < LEVEL_PROBABILITY and level < MAX_LEVEL - 1:
        level += 1
    return level


class SkipListNode(Generic[K, V]):
    """Node in a skip list."""

    __slots__ = ('key', 'sort_key', 'value', 'next', 'lock', 'marked', 'fully_linked')

    def __init__(
        self,
        key: K,
        value: V,
        level: int,
        sort_key: Optional[Any] = None,
    ):
        """Initialize node.

        Args:
            key: Node key
            value: Node value
            level: Node level (0 to MAX_LEVEL-1)
            sort_key: Extracted sort key (for key function comparators)
        """
        self.key = key
        self.sort_key = sort_key if sort_key is not None else key
        self.value = value
        self.next: List[Optional['SkipListNode[K, V]']] = [None] * (level + 1)
        self.lock = threading.Lock()
        self.marked = False  # Logically deleted
        self.fully_linked = False  # Fully inserted into all levels


class SkipList(Generic[K, V]):
    """Thread-safe skip list with fine-grained locking.

    This implementation uses optimistic concurrent skip list algorithm
    with fine-grained locking for updates and lock-free reads.
    """

    __slots__ = (
        '_head',
        '_comparator',
        '_max_level',
        '_size',
        '_size_lock',
        '_smr',
    )

    def __init__(
        self,
        cmp: Optional[Union[Comparator, Callable[[Any, Any], int]]] = None,
        key: Optional[Callable[[Any], Any]] = None,
        smr: Optional[SMRDomain] = None,
    ):
        """Initialize skip list.

        Args:
            cmp: Comparator or comparison function
            key: Key extraction function
            smr: SMR domain for memory reclamation
        """
        self._comparator = resolve_comparator(cmp, key)
        self._smr = smr or get_default_smr()

        # Create sentinel head node with maximum level
        self._head: SkipListNode[K, V] = SkipListNode(
            key=None,  # type: ignore
            value=None,  # type: ignore
            level=MAX_LEVEL - 1,
        )
        self._head.fully_linked = True

        self._max_level = 0
        self._size = 0
        self._size_lock = threading.Lock()

    def _compare(self, a: Any, b: Any) -> int:
        """Compare two keys."""
        return self._comparator.compare(a, b)

    def _extract_key(self, key: K) -> Any:
        """Extract sort key from key."""
        return self._comparator.extract_key(key)

    def _find(
        self,
        key: K,
        preds: List[Optional[SkipListNode[K, V]]],
        succs: List[Optional[SkipListNode[K, V]]],
    ) -> int:
        """Find predecessors and successors for a key.

        Args:
            key: Key to find
            preds: Output list for predecessor nodes at each level
            succs: Output list for successor nodes at each level

        Returns:
            Level where key was found, or -1 if not found
        """
        sort_key = self._extract_key(key)
        found = -1
        pred = self._head

        for level in range(MAX_LEVEL - 1, -1, -1):
            curr = pred.next[level]

            while curr is not None:
                cmp = self._compare(curr.sort_key, sort_key)
                if cmp < 0:
                    pred = curr
                    curr = curr.next[level]
                else:
                    break

            if found == -1 and curr is not None:
                cmp = self._compare(curr.sort_key, sort_key)
                if cmp == 0:
                    found = level

            preds[level] = pred
            succs[level] = curr

        return found

    def search(self, key: K) -> Optional[V]:
        """Search for a key.

        Args:
            key: Key to search for

        Returns:
            Value if found, None otherwise
        """
        sort_key = self._extract_key(key)
        pred = self._head

        for level in range(MAX_LEVEL - 1, -1, -1):
            curr = pred.next[level]

            while curr is not None:
                cmp = self._compare(curr.sort_key, sort_key)
                if cmp < 0:
                    pred = curr
                    curr = curr.next[level]
                else:
                    break

        # Found at level 0?
        curr = pred.next[0]
        if curr is not None and not curr.marked:
            cmp = self._compare(curr.sort_key, sort_key)
            if cmp == 0 and curr.fully_linked:
                return curr.value

        return None

    def contains(self, key: K) -> bool:
        """Check if key exists.

        Args:
            key: Key to check

        Returns:
            True if key exists
        """
        return self.search(key) is not None

    def insert(self, key: K, value: V, replace: bool = True) -> Tuple[bool, Optional[V]]:
        """Insert or update a key-value pair.

        Args:
            key: Key to insert
            value: Value to insert
            replace: If True, replace existing value; if False, fail if exists

        Returns:
            Tuple of (success, old_value)
        """
        sort_key = self._extract_key(key)
        top_level = _random_level()
        preds: List[Optional[SkipListNode[K, V]]] = [None] * MAX_LEVEL
        succs: List[Optional[SkipListNode[K, V]]] = [None] * MAX_LEVEL

        while True:
            found = self._find(key, preds, succs)

            if found != -1:
                node_found = succs[found]
                if node_found is not None and not node_found.marked:
                    # Wait until fully linked
                    while not node_found.fully_linked:
                        pass

                    if replace:
                        # Replace value
                        with node_found.lock:
                            if not node_found.marked:
                                old_value = node_found.value
                                node_found.value = value
                                return True, old_value
                    else:
                        return False, node_found.value

                continue  # Retry if marked

            # Acquire locks in order
            locked: List[SkipListNode[K, V]] = []
            valid = True

            try:
                for level in range(top_level + 1):
                    pred = preds[level]
                    succ = succs[level]

                    if pred is not None:
                        pred.lock.acquire()
                        locked.append(pred)

                    # Validate
                    if pred is None or pred.marked:
                        valid = False
                        break
                    if pred.next[level] is not succ:
                        valid = False
                        break
                    if succ is not None and succ.marked:
                        valid = False
                        break

                if not valid:
                    continue  # Retry

                # Create and link new node
                new_node: SkipListNode[K, V] = SkipListNode(
                    key=key,
                    value=value,
                    level=top_level,
                    sort_key=sort_key,
                )

                for level in range(top_level + 1):
                    new_node.next[level] = succs[level]

                for level in range(top_level + 1):
                    pred = preds[level]
                    if pred is not None:
                        pred.next[level] = new_node

                new_node.fully_linked = True

                with self._size_lock:
                    self._size += 1
                    if top_level > self._max_level:
                        self._max_level = top_level

                return True, None

            finally:
                for node in locked:
                    node.lock.release()

    def delete(self, key: K) -> Tuple[bool, Optional[V]]:
        """Delete a key.

        Args:
            key: Key to delete

        Returns:
            Tuple of (success, old_value)
        """
        preds: List[Optional[SkipListNode[K, V]]] = [None] * MAX_LEVEL
        succs: List[Optional[SkipListNode[K, V]]] = [None] * MAX_LEVEL
        victim: Optional[SkipListNode[K, V]] = None
        is_marked = False
        top_level = -1

        while True:
            found = self._find(key, preds, succs)

            if found != -1:
                victim = succs[found]
            else:
                return False, None

            if victim is None:
                return False, None

            if not is_marked:
                top_level = len(victim.next) - 1
                if not victim.fully_linked or victim.marked:
                    return False, None

                # Try to mark
                victim.lock.acquire()
                if victim.marked:
                    victim.lock.release()
                    return False, None

                victim.marked = True
                is_marked = True

            # Acquire locks and unlink
            locked: List[SkipListNode[K, V]] = []
            valid = True

            try:
                for level in range(top_level + 1):
                    pred = preds[level]

                    if pred is not None:
                        pred.lock.acquire()
                        locked.append(pred)

                    # Validate
                    if pred is None or pred.marked:
                        valid = False
                        break
                    if pred.next[level] is not victim:
                        valid = False
                        break

                if not valid:
                    continue  # Retry find

                # Unlink at all levels
                for level in range(top_level, -1, -1):
                    pred = preds[level]
                    if pred is not None:
                        pred.next[level] = victim.next[level]

                with self._size_lock:
                    self._size -= 1

                # Retire node for safe reclamation
                old_value = victim.value
                self._smr.retire(victim)

                return True, old_value

            finally:
                for node in locked:
                    node.lock.release()
                if is_marked:
                    victim.lock.release()

    def __len__(self) -> int:
        """Get size of skip list."""
        return self._size

    def __contains__(self, key: K) -> bool:
        """Check if key exists."""
        return self.contains(key)

    def __iter__(self) -> Iterator[K]:
        """Iterate over keys in order."""
        node = self._head.next[0]
        while node is not None:
            if node.fully_linked and not node.marked:
                yield node.key
            node = node.next[0]

    def items(
        self,
        start: Optional[K] = None,
        stop: Optional[K] = None,
    ) -> Iterator[Tuple[K, V]]:
        """Iterate over key-value pairs in order.

        Args:
            start: Start key (inclusive)
            stop: Stop key (exclusive)

        Yields:
            Key-value tuples
        """
        node = self._head.next[0]

        # Find start position
        if start is not None:
            start_key = self._extract_key(start)
            while node is not None:
                cmp = self._compare(node.sort_key, start_key)
                if cmp >= 0:
                    break
                node = node.next[0]

        # Iterate until stop
        while node is not None:
            if node.fully_linked and not node.marked:
                if stop is not None:
                    stop_key = self._extract_key(stop)
                    cmp = self._compare(node.sort_key, stop_key)
                    if cmp >= 0:
                        break
                yield node.key, node.value
            node = node.next[0]

    def keys(
        self,
        start: Optional[K] = None,
        stop: Optional[K] = None,
    ) -> Iterator[K]:
        """Iterate over keys in order."""
        for key, _ in self.items(start, stop):
            yield key

    def values(
        self,
        start: Optional[K] = None,
        stop: Optional[K] = None,
    ) -> Iterator[V]:
        """Iterate over values in key order."""
        for _, value in self.items(start, stop):
            yield value

    def first_key(self) -> Optional[K]:
        """Get the first (smallest) key."""
        node = self._head.next[0]
        while node is not None:
            if node.fully_linked and not node.marked:
                return node.key
            node = node.next[0]
        return None

    def last_key(self) -> Optional[K]:
        """Get the last (largest) key."""
        # Traverse to find last valid node
        pred = self._head
        for level in range(MAX_LEVEL - 1, -1, -1):
            curr = pred.next[level]
            while curr is not None:
                if not curr.marked:
                    pred = curr
                curr = curr.next[level] if curr.next[level] is not None else None

        if pred is self._head:
            return None
        return pred.key if pred.fully_linked and not pred.marked else None

    def floor_key(self, key: K) -> Optional[K]:
        """Get the greatest key less than or equal to given key."""
        sort_key = self._extract_key(key)
        pred = self._head
        result: Optional[K] = None

        for level in range(MAX_LEVEL - 1, -1, -1):
            curr = pred.next[level]
            while curr is not None:
                cmp = self._compare(curr.sort_key, sort_key)
                if cmp <= 0:
                    if curr.fully_linked and not curr.marked:
                        result = curr.key
                    pred = curr
                    curr = curr.next[level]
                else:
                    break

        return result

    def ceiling_key(self, key: K) -> Optional[K]:
        """Get the smallest key greater than or equal to given key."""
        sort_key = self._extract_key(key)
        pred = self._head

        for level in range(MAX_LEVEL - 1, -1, -1):
            curr = pred.next[level]
            while curr is not None:
                cmp = self._compare(curr.sort_key, sort_key)
                if cmp < 0:
                    pred = curr
                    curr = curr.next[level]
                else:
                    break

        # curr is now the first node >= key at level 0
        curr = pred.next[0]
        while curr is not None:
            cmp = self._compare(curr.sort_key, sort_key)
            if cmp >= 0 and curr.fully_linked and not curr.marked:
                return curr.key
            curr = curr.next[0]

        return None

    @property
    def comparator_type(self) -> str:
        """Get the comparator type."""
        return self._comparator.type
