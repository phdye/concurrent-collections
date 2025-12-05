"""Tests for the Treiber stack implementation."""

import pytest
import threading
import time
from concurrent.futures import ThreadPoolExecutor

from concurrent_collections import TreiberStack, LockFreeStack, Empty


class TestTreiberStackBasic:
    """Basic functionality tests."""

    def test_create_empty_stack(self):
        """Test creating an empty stack."""
        stack = TreiberStack()
        assert len(stack) == 0
        assert stack.empty()

    def test_push_single(self):
        """Test pushing a single item."""
        stack = TreiberStack()
        stack.push(42)
        assert len(stack) == 1
        assert not stack.empty()

    def test_push_pop_single(self):
        """Test push then pop."""
        stack = TreiberStack()
        stack.push(42)
        result = stack.pop()
        assert result == 42
        assert stack.empty()

    def test_lifo_order(self):
        """Test LIFO ordering."""
        stack = TreiberStack()
        for i in range(5):
            stack.push(i)

        for i in range(4, -1, -1):
            assert stack.pop() == i

    def test_pop_empty_raises(self):
        """Test that pop on empty raises Empty."""
        stack = TreiberStack()
        with pytest.raises(Empty):
            stack.pop()

    def test_try_pop_empty_returns_none(self):
        """Test that try_pop on empty returns None."""
        stack = TreiberStack()
        assert stack.try_pop() is None

    def test_peek(self):
        """Test peek operation."""
        stack = TreiberStack()
        stack.push(1)
        stack.push(2)
        stack.push(3)

        assert stack.peek() == 3
        assert len(stack) == 3  # peek doesn't remove

    def test_peek_empty(self):
        """Test peek on empty stack."""
        stack = TreiberStack()
        assert stack.peek() is None

    def test_push_none_raises(self):
        """Test that pushing None raises ValueError."""
        stack = TreiberStack()
        with pytest.raises(ValueError):
            stack.push(None)

    def test_clear(self):
        """Test clearing the stack."""
        stack = TreiberStack()
        for i in range(10):
            stack.push(i)

        stack.clear()
        assert stack.empty()
        assert len(stack) == 0

    def test_iteration(self):
        """Test iterating over stack."""
        stack = TreiberStack()
        items = [1, 2, 3, 4, 5]
        for item in items:
            stack.push(item)

        result = list(stack)
        assert result == [5, 4, 3, 2, 1]  # Top to bottom


class TestTreiberStackElimination:
    """Tests for elimination backoff."""

    def test_elimination_enabled(self):
        """Test elimination enabled property."""
        stack1 = TreiberStack(enable_elimination=True)
        stack2 = TreiberStack(enable_elimination=False)

        assert stack1.elimination_enabled is True
        assert stack2.elimination_enabled is False

    def test_stack_works_without_elimination(self):
        """Test stack works with elimination disabled."""
        stack = TreiberStack(enable_elimination=False)
        for i in range(100):
            stack.push(i)

        for i in range(99, -1, -1):
            assert stack.pop() == i


class TestTreiberStackConcurrency:
    """Concurrent access tests."""

    def test_concurrent_push(self):
        """Test concurrent pushes."""
        stack = TreiberStack()
        num_threads = 4
        items_per_thread = 100

        def pusher(tid):
            for i in range(items_per_thread):
                stack.push((tid, i))

        threads = [threading.Thread(target=pusher, args=(t,))
                   for t in range(num_threads)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert len(stack) == num_threads * items_per_thread

    def test_concurrent_pop(self):
        """Test concurrent pops."""
        stack = TreiberStack()
        num_items = 1000

        for i in range(num_items):
            stack.push(i)

        results = []
        lock = threading.Lock()

        def popper():
            while True:
                item = stack.try_pop()
                if item is None:
                    break
                with lock:
                    results.append(item)

        threads = [threading.Thread(target=popper) for _ in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert len(results) == num_items
        assert set(results) == set(range(num_items))

    def test_concurrent_push_pop(self):
        """Test concurrent push and pop."""
        stack = TreiberStack()
        num_ops = 500
        pushed = []
        popped = []
        push_lock = threading.Lock()
        pop_lock = threading.Lock()

        def pusher():
            for i in range(num_ops):
                stack.push(i)
                with push_lock:
                    pushed.append(i)

        def popper():
            count = 0
            while count < num_ops:
                item = stack.try_pop()
                if item is not None:
                    with pop_lock:
                        popped.append(item)
                    count += 1
                else:
                    time.sleep(0.0001)

        t1 = threading.Thread(target=pusher)
        t2 = threading.Thread(target=popper)

        t1.start()
        t2.start()
        t1.join()
        t2.join()

        assert len(popped) == num_ops


class TestLockFreeStackAPI:
    """Tests for the public LockFreeStack API."""

    def test_basic_operations(self):
        """Test basic push/pop."""
        stack = LockFreeStack()
        stack.push(1)
        stack.push(2)
        stack.push(3)

        assert stack.pop() == 3
        assert stack.pop() == 2
        assert stack.pop() == 1

    def test_try_pop(self):
        """Test try_pop."""
        stack = LockFreeStack()
        assert stack.try_pop() is None

        stack.push(42)
        assert stack.try_pop() == 42
        assert stack.try_pop() is None

    def test_pop_empty_raises(self):
        """Test pop on empty raises Empty."""
        stack = LockFreeStack()
        with pytest.raises(Empty):
            stack.pop()

    def test_peek(self):
        """Test peek."""
        stack = LockFreeStack()
        stack.push(1)
        assert stack.peek() == 1
        assert len(stack) == 1

    def test_bool(self):
        """Test boolean conversion."""
        stack = LockFreeStack()
        assert not stack
        stack.push(1)
        assert stack

    def test_repr(self):
        """Test string representation."""
        stack = LockFreeStack()
        assert "LockFreeStack" in repr(stack)
