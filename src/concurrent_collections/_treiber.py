"""
treiber - Lock-free Treiber stack with elimination backoff

This module provides a lock-free stack implementation using the Treiber
algorithm with an elimination array for improved scalability under
high contention.
"""

import threading
import random
from typing import Any, Callable, Generic, List, Optional, TypeVar

from concurrent_collections._atomics import AtomicPtr, AtomicInt, MemoryOrder
from concurrent_collections._backoff import Backoff
from concurrent_collections._smr_ibr import get_default_ibr, IBRDomain


T = TypeVar('T')


# Elimination array configuration
DEFAULT_ELIMINATION_SIZE = 16
ELIMINATION_TIMEOUT_NS = 100_000  # 100 microseconds


class StackNode(Generic[T]):
    """Node in a Treiber stack."""

    __slots__ = ('value', 'next')

    def __init__(self, value: T):
        """Initialize node.

        Args:
            value: The value stored in this node
        """
        self.value = value
        self.next: Optional['StackNode[T]'] = None


class Empty(Exception):
    """Exception raised when popping from an empty stack."""
    pass


class EliminationSlot(Generic[T]):
    """A slot in the elimination array for push/pop exchange."""

    __slots__ = ('_state', '_value', '_lock')

    # States
    EMPTY = 0
    WAITING = 1
    BUSY = 2

    def __init__(self):
        """Initialize slot."""
        self._state = AtomicInt(self.EMPTY)
        self._value: Optional[T] = None
        self._lock = threading.Lock()

    def try_push(self, value: T, timeout_ns: int) -> bool:
        """Try to exchange with a popper.

        Args:
            value: Value to push
            timeout_ns: Timeout in nanoseconds

        Returns:
            True if exchanged with a popper
        """
        # Try to claim slot
        if not self._state.compare_exchange_strong(self.EMPTY, self.WAITING):
            return False

        self._value = value

        # Wait for popper
        backoff = Backoff()
        spins = 0
        max_spins = max(1, timeout_ns // 1000)  # Approximate

        while spins < max_spins:
            if self._state.load(MemoryOrder.ACQUIRE) == self.BUSY:
                # Popper took the value
                self._state.store(self.EMPTY, MemoryOrder.RELEASE)
                return True
            backoff.spin()
            spins += 1

        # Timeout - try to reclaim
        if self._state.compare_exchange_strong(self.WAITING, self.EMPTY):
            return False

        # Popper took it during reclaim attempt
        self._state.store(self.EMPTY, MemoryOrder.RELEASE)
        return True

    def try_pop(self, timeout_ns: int) -> Optional[T]:
        """Try to exchange with a pusher.

        Args:
            timeout_ns: Timeout in nanoseconds

        Returns:
            Value if exchanged, None otherwise
        """
        # Wait for a pusher
        backoff = Backoff()
        spins = 0
        max_spins = max(1, timeout_ns // 1000)

        while spins < max_spins:
            state = self._state.load(MemoryOrder.ACQUIRE)
            if state == self.WAITING:
                # Try to take value
                if self._state.compare_exchange_strong(self.WAITING, self.BUSY):
                    value = self._value
                    return value
            backoff.spin()
            spins += 1

        return None


class EliminationArray(Generic[T]):
    """Array of elimination slots for push/pop exchange."""

    __slots__ = ('_slots', '_size', '_random')

    def __init__(self, size: int = DEFAULT_ELIMINATION_SIZE):
        """Initialize array.

        Args:
            size: Number of slots
        """
        self._size = size
        self._slots: List[EliminationSlot[T]] = [
            EliminationSlot() for _ in range(size)
        ]
        self._random = random.Random()

    def try_push(self, value: T, timeout_ns: int = ELIMINATION_TIMEOUT_NS) -> bool:
        """Try to exchange with a popper.

        Args:
            value: Value to push
            timeout_ns: Timeout in nanoseconds

        Returns:
            True if successfully exchanged
        """
        slot_idx = self._random.randint(0, self._size - 1)
        return self._slots[slot_idx].try_push(value, timeout_ns)

    def try_pop(self, timeout_ns: int = ELIMINATION_TIMEOUT_NS) -> Optional[T]:
        """Try to exchange with a pusher.

        Args:
            timeout_ns: Timeout in nanoseconds

        Returns:
            Value if successfully exchanged, None otherwise
        """
        slot_idx = self._random.randint(0, self._size - 1)
        return self._slots[slot_idx].try_pop(timeout_ns)


class TreiberStack(Generic[T]):
    """Lock-free Treiber stack with elimination backoff.

    This implementation provides:
    - Lock-free push and pop operations
    - LIFO (Last-In-First-Out) ordering
    - Elimination backoff for high-contention scenarios
    - Safe memory reclamation via SMR/IBR

    Example:
        >>> stack = TreiberStack()
        >>> stack.push(1)
        >>> stack.push(2)
        >>> stack.pop()
        2
        >>> stack.pop()
        1
    """

    __slots__ = (
        '_top',
        '_size',
        '_smr',
        '_elimination',
        '_enable_elimination',
        '_max_elimination_attempts',
    )

    def __init__(
        self,
        *,
        enable_elimination: bool = True,
        elimination_size: int = DEFAULT_ELIMINATION_SIZE,
        smr: Optional[IBRDomain] = None,
    ):
        """Initialize stack.

        Args:
            enable_elimination: Enable elimination backoff
            elimination_size: Size of elimination array
            smr: SMR domain for memory reclamation
        """
        self._top = AtomicPtr[StackNode[T]](None)
        self._size = AtomicInt(0)
        self._smr = smr or get_default_ibr()
        self._enable_elimination = enable_elimination
        self._max_elimination_attempts = 2

        if enable_elimination:
            self._elimination: Optional[EliminationArray[T]] = EliminationArray(elimination_size)
        else:
            self._elimination = None

    def push(self, item: T) -> None:
        """Push an item onto the stack.

        Args:
            item: Item to push

        This operation is lock-free.
        """
        if item is None:
            raise ValueError("Cannot push None")

        node = StackNode(item)
        backoff = Backoff()
        elimination_attempts = 0

        while True:
            old_top = self._top.load(MemoryOrder.ACQUIRE)
            node.next = old_top

            if self._top.compare_exchange_weak(old_top, node):
                self._size.fetch_add(1, MemoryOrder.RELAXED)
                return

            # Try elimination on contention
            if self._elimination is not None and elimination_attempts < self._max_elimination_attempts:
                if self._elimination.try_push(item, ELIMINATION_TIMEOUT_NS):
                    self._size.fetch_add(1, MemoryOrder.RELAXED)
                    return
                elimination_attempts += 1

            backoff.spin()

    def pop(self) -> T:
        """Pop an item from the stack.

        Returns:
            The top item

        Raises:
            Empty: If the stack is empty

        This operation is lock-free.
        """
        result = self.try_pop()
        if result is None:
            raise Empty("Stack is empty")
        return result

    def try_pop(self) -> Optional[T]:
        """Try to pop an item from the stack.

        Returns:
            The top item, or None if empty

        This operation is lock-free.
        """
        backoff = Backoff()
        elimination_attempts = 0
        thread_id = threading.get_ident()

        # Register thread with SMR
        if hasattr(self._smr, 'thread_register'):
            self._smr.thread_register()

        while True:
            old_top = self._top.load(MemoryOrder.ACQUIRE)

            if old_top is None:
                # Try elimination even on empty
                if self._elimination is not None and elimination_attempts < self._max_elimination_attempts:
                    result = self._elimination.try_pop(ELIMINATION_TIMEOUT_NS)
                    if result is not None:
                        self._size.fetch_sub(1, MemoryOrder.RELAXED)
                        return result
                    elimination_attempts += 1
                    continue
                return None

            new_top = old_top.next

            if self._top.compare_exchange_weak(old_top, new_top):
                value = old_top.value
                self._size.fetch_sub(1, MemoryOrder.RELAXED)

                # Retire the old node for safe reclamation
                self._smr.retire(old_top, thread_id)

                return value

            # Try elimination on contention
            if self._elimination is not None and elimination_attempts < self._max_elimination_attempts:
                result = self._elimination.try_pop(ELIMINATION_TIMEOUT_NS)
                if result is not None:
                    self._size.fetch_sub(1, MemoryOrder.RELAXED)
                    return result
                elimination_attempts += 1

            backoff.spin()

    def peek(self) -> Optional[T]:
        """Peek at the top item without removing it.

        Returns:
            The top item, or None if empty

        This operation is wait-free.
        """
        top = self._top.load(MemoryOrder.ACQUIRE)
        if top is None:
            return None
        return top.value

    def __len__(self) -> int:
        """Get the approximate size of the stack.

        Returns:
            Approximate number of items
        """
        return max(0, self._size.load(MemoryOrder.RELAXED))

    def empty(self) -> bool:
        """Check if the stack is empty.

        Returns:
            True if empty
        """
        return self._top.load(MemoryOrder.ACQUIRE) is None

    @property
    def elimination_enabled(self) -> bool:
        """Check if elimination is enabled."""
        return self._enable_elimination

    def clear(self) -> None:
        """Remove all items from the stack."""
        while self.try_pop() is not None:
            pass

    def __iter__(self):
        """Iterate over items from top to bottom.

        Note: This provides a snapshot view and is not thread-safe
        for concurrent modifications.
        """
        items = []
        node = self._top.load(MemoryOrder.ACQUIRE)
        while node is not None:
            items.append(node.value)
            node = node.next
        return iter(items)

    def __repr__(self) -> str:
        """String representation."""
        size = len(self)
        return f"TreiberStack(size={size}, elimination={self._enable_elimination})"
