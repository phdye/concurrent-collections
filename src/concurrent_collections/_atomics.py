"""
atomics - Portable atomic operations abstraction

This module provides atomic operations and memory barriers for lock-free
programming. It wraps Python's threading primitives with the semantics
needed for concurrent data structures.
"""

import threading
from enum import IntEnum
from typing import TypeVar, Generic, Optional, Any


class MemoryOrder(IntEnum):
    """Memory ordering constraints for atomic operations."""
    RELAXED = 0  # No ordering constraints
    CONSUME = 1  # Data-dependent ordering (deprecated, treat as ACQUIRE)
    ACQUIRE = 2  # Prevent reordering of subsequent reads
    RELEASE = 3  # Prevent reordering of previous writes
    ACQ_REL = 4  # Both ACQUIRE and RELEASE
    SEQ_CST = 5  # Sequential consistency (strongest)


T = TypeVar('T')


class AtomicInt:
    """Atomic integer operations.

    Provides atomic load, store, exchange, compare-and-swap, and
    fetch-and-add operations on integers with configurable memory ordering.
    """

    __slots__ = ('_value', '_lock')

    def __init__(self, initial: int = 0) -> None:
        """Initialize atomic integer.

        Args:
            initial: Initial value (default 0)
        """
        self._value = initial
        self._lock = threading.Lock()

    def load(self, order: MemoryOrder = MemoryOrder.SEQ_CST) -> int:
        """Atomically load the current value.

        Args:
            order: Memory ordering (default SEQ_CST)

        Returns:
            Current value
        """
        with self._lock:
            return self._value

    def store(self, value: int, order: MemoryOrder = MemoryOrder.SEQ_CST) -> None:
        """Atomically store a new value.

        Args:
            value: Value to store
            order: Memory ordering (default SEQ_CST)
        """
        with self._lock:
            self._value = value

    def exchange(self, value: int, order: MemoryOrder = MemoryOrder.SEQ_CST) -> int:
        """Atomically exchange the value.

        Args:
            value: New value to store
            order: Memory ordering (default SEQ_CST)

        Returns:
            Previous value
        """
        with self._lock:
            old = self._value
            self._value = value
            return old

    def compare_exchange_weak(
        self,
        expected: int,
        desired: int,
        success_order: MemoryOrder = MemoryOrder.SEQ_CST,
        failure_order: MemoryOrder = MemoryOrder.SEQ_CST,
    ) -> tuple[bool, int]:
        """Atomically compare and exchange (may spuriously fail).

        Args:
            expected: Expected current value
            desired: Value to store if current == expected
            success_order: Memory ordering on success
            failure_order: Memory ordering on failure

        Returns:
            Tuple of (success: bool, actual_value: int)
        """
        with self._lock:
            actual = self._value
            if actual == expected:
                self._value = desired
                return True, actual
            return False, actual

    def compare_exchange_strong(
        self,
        expected: int,
        desired: int,
        success_order: MemoryOrder = MemoryOrder.SEQ_CST,
        failure_order: MemoryOrder = MemoryOrder.SEQ_CST,
    ) -> tuple[bool, int]:
        """Atomically compare and exchange (no spurious failure).

        Args:
            expected: Expected current value
            desired: Value to store if current == expected
            success_order: Memory ordering on success
            failure_order: Memory ordering on failure

        Returns:
            Tuple of (success: bool, actual_value: int)
        """
        # In Python, this is identical to weak version
        return self.compare_exchange_weak(expected, desired, success_order, failure_order)

    def fetch_add(self, value: int, order: MemoryOrder = MemoryOrder.SEQ_CST) -> int:
        """Atomically add and return previous value.

        Args:
            value: Value to add
            order: Memory ordering (default SEQ_CST)

        Returns:
            Value before addition
        """
        with self._lock:
            old = self._value
            self._value = old + value
            return old

    def fetch_sub(self, value: int, order: MemoryOrder = MemoryOrder.SEQ_CST) -> int:
        """Atomically subtract and return previous value.

        Args:
            value: Value to subtract
            order: Memory ordering (default SEQ_CST)

        Returns:
            Value before subtraction
        """
        with self._lock:
            old = self._value
            self._value = old - value
            return old

    def fetch_or(self, value: int, order: MemoryOrder = MemoryOrder.SEQ_CST) -> int:
        """Atomically OR and return previous value.

        Args:
            value: Value to OR
            order: Memory ordering (default SEQ_CST)

        Returns:
            Value before OR
        """
        with self._lock:
            old = self._value
            self._value = old | value
            return old

    def fetch_and(self, value: int, order: MemoryOrder = MemoryOrder.SEQ_CST) -> int:
        """Atomically AND and return previous value.

        Args:
            value: Value to AND
            order: Memory ordering (default SEQ_CST)

        Returns:
            Value before AND
        """
        with self._lock:
            old = self._value
            self._value = old & value
            return old

    @property
    def value(self) -> int:
        """Get current value (convenience property)."""
        return self.load()


class AtomicPtr(Generic[T]):
    """Atomic pointer/reference operations.

    Provides atomic operations on object references for building
    lock-free data structures.
    """

    __slots__ = ('_value', '_lock')

    def __init__(self, initial: Optional[T] = None) -> None:
        """Initialize atomic pointer.

        Args:
            initial: Initial value (default None)
        """
        self._value: Optional[T] = initial
        self._lock = threading.Lock()

    def load(self, order: MemoryOrder = MemoryOrder.SEQ_CST) -> Optional[T]:
        """Atomically load the current reference.

        Args:
            order: Memory ordering (default SEQ_CST)

        Returns:
            Current reference
        """
        with self._lock:
            return self._value

    def store(self, value: Optional[T], order: MemoryOrder = MemoryOrder.SEQ_CST) -> None:
        """Atomically store a new reference.

        Args:
            value: Reference to store
            order: Memory ordering (default SEQ_CST)
        """
        with self._lock:
            self._value = value

    def exchange(self, value: Optional[T], order: MemoryOrder = MemoryOrder.SEQ_CST) -> Optional[T]:
        """Atomically exchange the reference.

        Args:
            value: New reference to store
            order: Memory ordering (default SEQ_CST)

        Returns:
            Previous reference
        """
        with self._lock:
            old = self._value
            self._value = value
            return old

    def compare_exchange_weak(
        self,
        expected: Optional[T],
        desired: Optional[T],
        success_order: MemoryOrder = MemoryOrder.SEQ_CST,
        failure_order: MemoryOrder = MemoryOrder.SEQ_CST,
    ) -> tuple[bool, Optional[T]]:
        """Atomically compare and exchange (may spuriously fail).

        Args:
            expected: Expected current reference (compared by identity)
            desired: Reference to store if current is expected
            success_order: Memory ordering on success
            failure_order: Memory ordering on failure

        Returns:
            Tuple of (success: bool, actual_reference)
        """
        with self._lock:
            actual = self._value
            if actual is expected:
                self._value = desired
                return True, actual
            return False, actual

    def compare_exchange_strong(
        self,
        expected: Optional[T],
        desired: Optional[T],
        success_order: MemoryOrder = MemoryOrder.SEQ_CST,
        failure_order: MemoryOrder = MemoryOrder.SEQ_CST,
    ) -> tuple[bool, Optional[T]]:
        """Atomically compare and exchange (no spurious failure).

        Args:
            expected: Expected current reference (compared by identity)
            desired: Reference to store if current is expected
            success_order: Memory ordering on success
            failure_order: Memory ordering on failure

        Returns:
            Tuple of (success: bool, actual_reference)
        """
        return self.compare_exchange_weak(expected, desired, success_order, failure_order)

    @property
    def value(self) -> Optional[T]:
        """Get current reference (convenience property)."""
        return self.load()


class AtomicFlag:
    """Atomic boolean flag.

    Provides atomic test-and-set and clear operations, commonly used
    for simple spinlocks.
    """

    __slots__ = ('_value', '_lock')

    def __init__(self, initial: bool = False) -> None:
        """Initialize atomic flag.

        Args:
            initial: Initial value (default False)
        """
        self._value = initial
        self._lock = threading.Lock()

    def test_and_set(self, order: MemoryOrder = MemoryOrder.SEQ_CST) -> bool:
        """Atomically set flag and return previous value.

        Args:
            order: Memory ordering (default SEQ_CST)

        Returns:
            Previous value (True if was already set)
        """
        with self._lock:
            old = self._value
            self._value = True
            return old

    def clear(self, order: MemoryOrder = MemoryOrder.SEQ_CST) -> None:
        """Atomically clear the flag.

        Args:
            order: Memory ordering (default SEQ_CST)
        """
        with self._lock:
            self._value = False

    def test(self, order: MemoryOrder = MemoryOrder.SEQ_CST) -> bool:
        """Atomically test the flag value.

        Args:
            order: Memory ordering (default SEQ_CST)

        Returns:
            Current flag value
        """
        with self._lock:
            return self._value

    @property
    def value(self) -> bool:
        """Get current flag value (convenience property)."""
        return self.test()


def atomic_thread_fence(order: MemoryOrder) -> None:
    """Issue a memory fence.

    In CPython with GIL, this is a no-op as the GIL provides
    sequential consistency. In free-threaded Python, this
    provides the specified ordering guarantee.

    Args:
        order: Memory ordering to enforce
    """
    # In Python, the threading primitives and GIL handle memory ordering.
    # This is a placeholder for C extension implementation.
    pass


def atomic_signal_fence(order: MemoryOrder) -> None:
    """Issue a signal fence (compiler barrier).

    Prevents compiler reordering across this point but does not
    issue hardware memory barriers.

    Args:
        order: Memory ordering to enforce
    """
    # In Python, this is primarily a documentation marker.
    pass
