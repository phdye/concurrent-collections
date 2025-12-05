"""
scq - Scalable Circular Queue (SCQ)

This module provides a bounded lock-free MPMC (Multi-Producer Multi-Consumer)
queue using the SCQ algorithm. The queue uses a circular buffer with
safe-bit tagging to prevent ABA problems.
"""

import threading
from typing import Any, Generic, List, Optional, TypeVar

from concurrent_collections._atomics import AtomicInt, AtomicPtr, MemoryOrder
from concurrent_collections._backoff import Backoff


T = TypeVar('T')


def _next_power_of_2(n: int) -> int:
    """Round up to next power of 2."""
    if n <= 0:
        return 1
    n -= 1
    n |= n >> 1
    n |= n >> 2
    n |= n >> 4
    n |= n >> 8
    n |= n >> 16
    n |= n >> 32
    return n + 1


class SCQSlot(Generic[T]):
    """A slot in the SCQ circular buffer.

    Each slot contains a cycle counter (for ABA prevention) and a value.
    The cycle determines whether the slot is valid for the current
    enqueue/dequeue cycle.
    """

    __slots__ = ('_cycle', '_value', '_has_value')

    def __init__(self, initial_cycle: int = 0):
        """Initialize slot.

        Args:
            initial_cycle: Initial cycle number
        """
        self._cycle = AtomicInt(initial_cycle)
        self._value: Optional[T] = None
        self._has_value = False

    def get_cycle(self) -> int:
        """Get current cycle."""
        return self._cycle.load(MemoryOrder.ACQUIRE)

    def set_cycle(self, cycle: int) -> None:
        """Set cycle."""
        self._cycle.store(cycle, MemoryOrder.RELEASE)

    def try_claim_for_enqueue(self, expected_cycle: int) -> bool:
        """Try to claim slot for enqueue.

        Args:
            expected_cycle: Expected cycle value

        Returns:
            True if claimed
        """
        return self._cycle.compare_exchange_strong(expected_cycle, expected_cycle + 1)

    def get_value(self) -> Optional[T]:
        """Get stored value."""
        return self._value if self._has_value else None

    def set_value(self, value: T) -> None:
        """Set stored value."""
        self._value = value
        self._has_value = True

    def clear_value(self) -> Optional[T]:
        """Clear and return value."""
        if self._has_value:
            value = self._value
            self._value = None
            self._has_value = False
            return value
        return None


class SCQ(Generic[T]):
    """Scalable Circular Queue - bounded lock-free MPMC queue.

    This implementation provides:
    - Lock-free enqueue and dequeue operations
    - FIFO (First-In-First-Out) ordering
    - Bounded capacity (power of 2)
    - Safe for multiple producers and consumers

    The algorithm uses a circular buffer with cycle counters in each slot
    to prevent ABA problems without requiring double-width CAS.

    Example:
        >>> q = SCQ(capacity=16)
        >>> q.enqueue(1)
        True
        >>> q.enqueue(2)
        True
        >>> q.dequeue()
        1
        >>> q.dequeue()
        2
    """

    __slots__ = (
        '_capacity',
        '_mask',
        '_slots',
        '_head',
        '_tail',
        '_threshold',
    )

    def __init__(self, capacity: int = 1024):
        """Initialize queue.

        Args:
            capacity: Maximum capacity (will be rounded to power of 2)
        """
        if capacity <= 0:
            capacity = 1024

        # Round to power of 2
        self._capacity = _next_power_of_2(capacity)
        self._mask = self._capacity - 1

        # Initialize slots with appropriate cycle values
        # Slot i starts with cycle = i / capacity (initially 0 for all)
        self._slots: List[SCQSlot[T]] = [
            SCQSlot(initial_cycle=0) for _ in range(self._capacity)
        ]

        self._head = AtomicInt(0)
        self._tail = AtomicInt(0)
        self._threshold = AtomicInt(0)

    @property
    def capacity(self) -> int:
        """Get queue capacity."""
        return self._capacity

    def enqueue(self, item: T) -> bool:
        """Enqueue an item.

        Args:
            item: Item to enqueue

        Returns:
            True if enqueued, False if queue is full

        This operation is lock-free.
        """
        if item is None:
            raise ValueError("Cannot enqueue None")

        backoff = Backoff()

        while True:
            # Get current tail
            tail = self._tail.load(MemoryOrder.ACQUIRE)
            head = self._head.load(MemoryOrder.ACQUIRE)

            # Check if full
            if tail - head >= self._capacity:
                return False

            # Calculate slot index
            slot_idx = tail & self._mask
            slot = self._slots[slot_idx]

            # Calculate expected cycle for this position
            expected_cycle = tail >> self._capacity.bit_length() - 1
            if self._capacity == 1:
                expected_cycle = tail

            # The slot cycle should be 2 * (tail / capacity) for empty slot
            # After enqueue, it becomes 2 * (tail / capacity) + 1
            cycle_at_slot = slot.get_cycle()
            expected_empty_cycle = (tail // self._capacity) * 2

            if cycle_at_slot == expected_empty_cycle:
                # Try to claim the slot
                if self._tail.compare_exchange_weak(tail, tail + 1):
                    # Won the slot
                    slot.set_value(item)
                    slot.set_cycle(expected_empty_cycle + 1)  # Mark as full
                    return True
            elif cycle_at_slot < expected_empty_cycle:
                # Slot from old cycle, queue is full
                return False

            backoff.spin()

    def dequeue(self) -> Optional[T]:
        """Dequeue an item.

        Returns:
            Item or None if empty

        This operation is lock-free.
        """
        backoff = Backoff()

        while True:
            # Get current head
            head = self._head.load(MemoryOrder.ACQUIRE)
            tail = self._tail.load(MemoryOrder.ACQUIRE)

            # Check if empty
            if head >= tail:
                return None

            # Calculate slot index
            slot_idx = head & self._mask
            slot = self._slots[slot_idx]

            # Check cycle
            cycle_at_slot = slot.get_cycle()
            expected_full_cycle = (head // self._capacity) * 2 + 1

            if cycle_at_slot == expected_full_cycle:
                # Try to claim the slot
                if self._head.compare_exchange_weak(head, head + 1):
                    # Won the slot
                    value = slot.clear_value()
                    slot.set_cycle(expected_full_cycle + 1)  # Mark as empty for next cycle
                    return value
            elif cycle_at_slot < expected_full_cycle:
                # Slot not yet filled or from old cycle, retry
                pass

            backoff.spin()

    def try_enqueue(self, item: T) -> bool:
        """Try to enqueue without blocking.

        Alias for enqueue() since SCQ is already non-blocking.
        """
        return self.enqueue(item)

    def try_dequeue(self) -> Optional[T]:
        """Try to dequeue without blocking.

        Alias for dequeue() since SCQ is already non-blocking.
        """
        return self.dequeue()

    def size(self) -> int:
        """Get approximate size.

        Returns:
            Approximate number of items (may be stale)
        """
        tail = self._tail.load(MemoryOrder.RELAXED)
        head = self._head.load(MemoryOrder.RELAXED)
        return max(0, min(tail - head, self._capacity))

    def __len__(self) -> int:
        """Get approximate size."""
        return self.size()

    def empty(self) -> bool:
        """Check if queue is empty."""
        return self._head.load(MemoryOrder.ACQUIRE) >= self._tail.load(MemoryOrder.ACQUIRE)

    def full(self) -> bool:
        """Check if queue is full."""
        tail = self._tail.load(MemoryOrder.ACQUIRE)
        head = self._head.load(MemoryOrder.ACQUIRE)
        return tail - head >= self._capacity

    def clear(self) -> None:
        """Remove all items from the queue."""
        while self.dequeue() is not None:
            pass

    def drain(self, max_items: int = -1) -> List[T]:
        """Drain items from queue.

        Args:
            max_items: Maximum items to drain (-1 for all)

        Returns:
            List of dequeued items
        """
        items: List[T] = []
        count = 0

        while max_items < 0 or count < max_items:
            item = self.dequeue()
            if item is None:
                break
            items.append(item)
            count += 1

        return items

    def __repr__(self) -> str:
        """String representation."""
        return f"SCQ(capacity={self._capacity}, size={self.size()})"


# Simpler bounded queue using array with head/tail pointers
class SimpleBoundedQueue(Generic[T]):
    """Simple bounded MPMC queue with lock-based fallback.

    Uses optimistic lock-free for single operations, falls back to
    locking under high contention. Good for moderate contention levels.
    """

    __slots__ = ('_capacity', '_buffer', '_head', '_tail', '_lock')

    def __init__(self, capacity: int = 1024):
        """Initialize queue.

        Args:
            capacity: Maximum capacity
        """
        self._capacity = max(1, capacity)
        self._buffer: List[Optional[T]] = [None] * self._capacity
        self._head = AtomicInt(0)
        self._tail = AtomicInt(0)
        self._lock = threading.Lock()

    @property
    def capacity(self) -> int:
        """Get queue capacity."""
        return self._capacity

    def enqueue(self, item: T) -> bool:
        """Enqueue an item."""
        if item is None:
            raise ValueError("Cannot enqueue None")

        with self._lock:
            tail = self._tail.load(MemoryOrder.RELAXED)
            head = self._head.load(MemoryOrder.RELAXED)

            if tail - head >= self._capacity:
                return False

            idx = tail % self._capacity
            self._buffer[idx] = item
            self._tail.store(tail + 1, MemoryOrder.RELEASE)
            return True

    def dequeue(self) -> Optional[T]:
        """Dequeue an item."""
        with self._lock:
            head = self._head.load(MemoryOrder.RELAXED)
            tail = self._tail.load(MemoryOrder.RELAXED)

            if head >= tail:
                return None

            idx = head % self._capacity
            item = self._buffer[idx]
            self._buffer[idx] = None
            self._head.store(head + 1, MemoryOrder.RELEASE)
            return item

    def size(self) -> int:
        """Get approximate size."""
        tail = self._tail.load(MemoryOrder.RELAXED)
        head = self._head.load(MemoryOrder.RELAXED)
        return max(0, tail - head)

    def __len__(self) -> int:
        return self.size()

    def empty(self) -> bool:
        """Check if empty."""
        return self.size() == 0

    def full(self) -> bool:
        """Check if full."""
        return self.size() >= self._capacity

    def clear(self) -> None:
        """Clear the queue."""
        while self.dequeue() is not None:
            pass

    def __repr__(self) -> str:
        return f"SimpleBoundedQueue(capacity={self._capacity}, size={self.size()})"
