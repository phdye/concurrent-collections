"""
LockFreeQueue - Public API for lock-free bounded queue

This module provides the public LockFreeQueue class that wraps the
SCQ implementation with a queue.Queue-compatible API.
"""

import time
from typing import Generic, List, Optional, TypeVar

from concurrent_collections._scq import SCQ


T = TypeVar('T')


class Full(Exception):
    """Exception raised when putting to a full queue."""
    pass


class Empty(Exception):
    """Exception raised when getting from an empty queue."""
    pass


__all__ = ['LockFreeQueue', 'Full', 'Empty']


class LockFreeQueue(Generic[T]):
    """Lock-free bounded MPMC queue with queue.Queue-compatible API.

    This class provides a thread-safe bounded queue that uses lock-free
    algorithms for high concurrency. It supports multiple producers and
    multiple consumers (MPMC).

    Example:
        >>> from concurrent_collections import LockFreeQueue
        >>> q = LockFreeQueue(maxsize=100)
        >>> q.put(1)
        >>> q.put(2)
        >>> q.get()  # Returns 1
        1
        >>> q.get()  # Returns 2
        2

    The API is compatible with queue.Queue for easy migration:
        - put(item, block=True, timeout=None)
        - get(block=True, timeout=None)
        - put_nowait(item)
        - get_nowait()

    Thread Safety:
        All operations are lock-free and safe for concurrent use
        by multiple threads.
    """

    __slots__ = ('_queue', '_maxsize')

    def __init__(self, maxsize: int = 0):
        """Initialize the queue.

        Args:
            maxsize: Maximum number of items. If 0 or negative,
                the queue size defaults to 1024.
        """
        if maxsize <= 0:
            maxsize = 1024
        self._maxsize = maxsize
        self._queue = SCQ[T](capacity=maxsize)

    @property
    def maxsize(self) -> int:
        """Maximum queue size."""
        return self._maxsize

    def put(self, item: T, block: bool = True, timeout: Optional[float] = None) -> None:
        """Put an item into the queue.

        Args:
            item: The item to put. Must not be None.
            block: If True, block until space is available.
            timeout: Maximum time to wait in seconds (None = wait forever).

        Raises:
            Full: If the queue is full and block is False, or
                if timeout expires while waiting.
            ValueError: If item is None.
        """
        if item is None:
            raise ValueError("Cannot put None")

        if not block:
            if not self._queue.enqueue(item):
                raise Full()
            return

        # Blocking put with optional timeout
        deadline = None
        if timeout is not None:
            deadline = time.monotonic() + timeout

        while True:
            if self._queue.enqueue(item):
                return

            if deadline is not None and time.monotonic() >= deadline:
                raise Full()

            # Small sleep to avoid busy waiting
            time.sleep(0.0001)  # 100 microseconds

    def get(self, block: bool = True, timeout: Optional[float] = None) -> T:
        """Get an item from the queue.

        Args:
            block: If True, block until an item is available.
            timeout: Maximum time to wait in seconds (None = wait forever).

        Returns:
            The oldest item in the queue.

        Raises:
            Empty: If the queue is empty and block is False, or
                if timeout expires while waiting.
        """
        if not block:
            item = self._queue.dequeue()
            if item is None:
                raise Empty()
            return item

        # Blocking get with optional timeout
        deadline = None
        if timeout is not None:
            deadline = time.monotonic() + timeout

        while True:
            item = self._queue.dequeue()
            if item is not None:
                return item

            if deadline is not None and time.monotonic() >= deadline:
                raise Empty()

            # Small sleep to avoid busy waiting
            time.sleep(0.0001)  # 100 microseconds

    def put_nowait(self, item: T) -> None:
        """Put an item without blocking.

        Equivalent to put(item, block=False).

        Raises:
            Full: If the queue is full.
        """
        self.put(item, block=False)

    def get_nowait(self) -> T:
        """Get an item without blocking.

        Equivalent to get(block=False).

        Raises:
            Empty: If the queue is empty.
        """
        return self.get(block=False)

    def try_put(self, item: T) -> bool:
        """Try to put an item without blocking.

        Args:
            item: The item to put.

        Returns:
            True if successful, False if queue is full.
        """
        return self._queue.enqueue(item)

    def try_get(self) -> Optional[T]:
        """Try to get an item without blocking.

        Returns:
            The item, or None if queue is empty.
        """
        return self._queue.dequeue()

    def drain(self, max_items: int = -1) -> List[T]:
        """Drain multiple items from the queue.

        Args:
            max_items: Maximum items to drain (-1 for all available).

        Returns:
            List of items drained from the queue.
        """
        return self._queue.drain(max_items)

    def qsize(self) -> int:
        """Get approximate queue size.

        Returns:
            Approximate number of items. May be slightly stale
            under concurrent modifications.
        """
        return len(self._queue)

    def __len__(self) -> int:
        """Get approximate queue size."""
        return self.qsize()

    def empty(self) -> bool:
        """Check if the queue appears empty.

        Returns:
            True if the queue appears empty.
        """
        return self._queue.empty()

    def full(self) -> bool:
        """Check if the queue appears full.

        Returns:
            True if the queue appears full.
        """
        return self._queue.full()

    def clear(self) -> None:
        """Remove all items from the queue."""
        self._queue.clear()

    def __repr__(self) -> str:
        """String representation."""
        return f"LockFreeQueue(maxsize={self._maxsize}, size={self.qsize()})"

    def __bool__(self) -> bool:
        """Return True if queue is non-empty."""
        return not self.empty()
