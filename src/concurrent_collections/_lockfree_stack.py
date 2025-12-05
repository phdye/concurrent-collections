"""
LockFreeStack - Public API for lock-free stack

This module provides the public LockFreeStack class that wraps the
Treiber stack implementation with a user-friendly API.
"""

from typing import Generic, Iterator, List, Optional, TypeVar

from concurrent_collections._treiber import TreiberStack, Empty


T = TypeVar('T')


# Re-export Empty exception
__all__ = ['LockFreeStack', 'Empty']


class LockFreeStack(Generic[T]):
    """Lock-free LIFO stack with optional elimination backoff.

    This class provides a thread-safe stack that uses lock-free
    algorithms for high concurrency. Under contention, matching
    push/pop operations can exchange directly via an elimination
    array, bypassing the main stack.

    Example:
        >>> from concurrent_collections import LockFreeStack
        >>> stack = LockFreeStack()
        >>> stack.push(1)
        >>> stack.push(2)
        >>> stack.push(3)
        >>> stack.pop()  # Returns 3
        3
        >>> stack.pop()  # Returns 2
        2
        >>> stack.peek()  # Returns 1 without removing
        1

    Thread Safety:
        All operations are lock-free and safe for concurrent use
        by multiple threads.
    """

    __slots__ = ('_stack',)

    def __init__(self, *, enable_elimination: bool = True):
        """Initialize the stack.

        Args:
            enable_elimination: If True, enable elimination backoff
                for improved performance under high contention.
                Default is True.
        """
        self._stack = TreiberStack[T](enable_elimination=enable_elimination)

    def push(self, item: T) -> None:
        """Push an item onto the stack.

        Args:
            item: The item to push. Must not be None.

        Raises:
            ValueError: If item is None.

        Complexity: O(1) amortized
        Thread Safety: Lock-free
        """
        self._stack.push(item)

    def pop(self) -> T:
        """Pop and return the top item.

        Returns:
            The top item from the stack.

        Raises:
            Empty: If the stack is empty.

        Complexity: O(1) amortized
        Thread Safety: Lock-free
        """
        return self._stack.pop()

    def try_pop(self) -> Optional[T]:
        """Try to pop an item without raising on empty.

        Returns:
            The top item, or None if the stack is empty.

        Complexity: O(1) amortized
        Thread Safety: Lock-free
        """
        return self._stack.try_pop()

    def peek(self) -> Optional[T]:
        """Peek at the top item without removing it.

        Returns:
            The top item, or None if the stack is empty.

        Complexity: O(1)
        Thread Safety: Wait-free
        """
        return self._stack.peek()

    def __len__(self) -> int:
        """Get the approximate number of items.

        Returns:
            Approximate count of items. May be slightly stale
            under concurrent modifications.
        """
        return len(self._stack)

    def empty(self) -> bool:
        """Check if the stack is empty.

        Returns:
            True if the stack appears to be empty.
        """
        return self._stack.empty()

    @property
    def elimination_enabled(self) -> bool:
        """Check if elimination backoff is enabled."""
        return self._stack.elimination_enabled

    def clear(self) -> None:
        """Remove all items from the stack."""
        self._stack.clear()

    def __iter__(self) -> Iterator[T]:
        """Iterate over items from top to bottom.

        Note: This provides a snapshot and is not guaranteed to
        be consistent under concurrent modifications.
        """
        return iter(self._stack)

    def __repr__(self) -> str:
        """String representation."""
        return f"LockFreeStack(size={len(self)}, elimination={self.elimination_enabled})"

    def __bool__(self) -> bool:
        """Return True if stack is non-empty."""
        return not self.empty()
