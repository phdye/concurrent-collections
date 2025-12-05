"""Tests for the SCQ and LockFreeQueue implementations."""

import pytest
import threading
import time
from concurrent.futures import ThreadPoolExecutor

from concurrent_collections import SCQ, SimpleBoundedQueue, LockFreeQueue, Full
from concurrent_collections._lockfree_queue import Empty


class TestSCQBasic:
    """Basic functionality tests for SCQ."""

    def test_create_queue(self):
        """Test creating a queue."""
        q = SCQ(capacity=16)
        assert q.capacity >= 16
        assert q.empty()
        assert len(q) == 0

    def test_capacity_power_of_2(self):
        """Test capacity is rounded to power of 2."""
        q = SCQ(capacity=10)
        assert q.capacity == 16  # Rounded up to 16

    def test_enqueue_dequeue_single(self):
        """Test enqueue then dequeue."""
        q = SCQ(capacity=16)
        assert q.enqueue(42)
        assert q.dequeue() == 42
        assert q.empty()

    def test_fifo_order(self):
        """Test FIFO ordering."""
        q = SCQ(capacity=16)
        for i in range(5):
            q.enqueue(i)

        for i in range(5):
            assert q.dequeue() == i

    def test_dequeue_empty_returns_none(self):
        """Test dequeue on empty returns None."""
        q = SCQ(capacity=16)
        assert q.dequeue() is None

    def test_enqueue_full_returns_false(self):
        """Test enqueue on full returns False."""
        q = SCQ(capacity=4)
        for i in range(4):
            assert q.enqueue(i)

        assert q.full()
        assert not q.enqueue(999)

    def test_enqueue_none_raises(self):
        """Test enqueue None raises ValueError."""
        q = SCQ(capacity=16)
        with pytest.raises(ValueError):
            q.enqueue(None)

    def test_size(self):
        """Test size tracking."""
        q = SCQ(capacity=16)
        assert q.size() == 0

        q.enqueue(1)
        q.enqueue(2)
        assert q.size() == 2

        q.dequeue()
        assert q.size() == 1

    def test_clear(self):
        """Test clearing queue."""
        q = SCQ(capacity=16)
        for i in range(10):
            q.enqueue(i)

        q.clear()
        assert q.empty()

    def test_drain(self):
        """Test draining queue."""
        q = SCQ(capacity=16)
        for i in range(10):
            q.enqueue(i)

        items = q.drain(5)
        assert items == [0, 1, 2, 3, 4]
        assert q.size() == 5

        items = q.drain()
        assert items == [5, 6, 7, 8, 9]
        assert q.empty()


class TestSimpleBoundedQueue:
    """Tests for SimpleBoundedQueue."""

    def test_basic_operations(self):
        """Test basic enqueue/dequeue."""
        q = SimpleBoundedQueue(capacity=16)
        q.enqueue(1)
        q.enqueue(2)

        assert q.dequeue() == 1
        assert q.dequeue() == 2

    def test_full_and_empty(self):
        """Test full and empty detection."""
        q = SimpleBoundedQueue(capacity=2)
        assert q.empty()
        assert not q.full()

        q.enqueue(1)
        q.enqueue(2)
        assert q.full()
        assert not q.empty()


class TestLockFreeQueueAPI:
    """Tests for the public LockFreeQueue API."""

    def test_basic_operations(self):
        """Test basic put/get."""
        q = LockFreeQueue(maxsize=100)
        q.put(1)
        q.put(2)
        q.put(3)

        assert q.get() == 1
        assert q.get() == 2
        assert q.get() == 3

    def test_put_nowait(self):
        """Test put_nowait."""
        q = LockFreeQueue(maxsize=2)
        q.put_nowait(1)
        q.put_nowait(2)

        with pytest.raises(Full):
            q.put_nowait(3)

    def test_get_nowait(self):
        """Test get_nowait."""
        q = LockFreeQueue(maxsize=100)
        with pytest.raises(Empty):
            q.get_nowait()

        q.put(42)
        assert q.get_nowait() == 42

    def test_try_put_get(self):
        """Test try_put and try_get."""
        q = LockFreeQueue(maxsize=2)

        assert q.try_put(1)
        assert q.try_put(2)
        assert not q.try_put(3)

        assert q.try_get() == 1
        assert q.try_get() == 2
        assert q.try_get() is None

    def test_drain(self):
        """Test drain operation."""
        q = LockFreeQueue(maxsize=100)
        for i in range(10):
            q.put(i)

        items = q.drain(5)
        assert items == [0, 1, 2, 3, 4]

    def test_qsize(self):
        """Test queue size."""
        q = LockFreeQueue(maxsize=100)
        assert q.qsize() == 0

        q.put(1)
        q.put(2)
        assert q.qsize() == 2

    def test_empty_full(self):
        """Test empty and full detection."""
        q = LockFreeQueue(maxsize=2)
        assert q.empty()
        assert not q.full()

        q.put(1)
        q.put(2)
        assert not q.empty()
        assert q.full()

    def test_bool(self):
        """Test boolean conversion."""
        q = LockFreeQueue(maxsize=100)
        assert not q
        q.put(1)
        assert q

    def test_maxsize_property(self):
        """Test maxsize property."""
        q = LockFreeQueue(maxsize=50)
        assert q.maxsize == 50

    def test_blocking_put_timeout(self):
        """Test blocking put with timeout."""
        q = LockFreeQueue(maxsize=1)
        q.put(1)

        start = time.time()
        with pytest.raises(Full):
            q.put(2, block=True, timeout=0.1)
        elapsed = time.time() - start
        assert elapsed >= 0.1

    def test_blocking_get_timeout(self):
        """Test blocking get with timeout."""
        q = LockFreeQueue(maxsize=100)

        start = time.time()
        with pytest.raises(Empty):
            q.get(block=True, timeout=0.1)
        elapsed = time.time() - start
        assert elapsed >= 0.1


class TestQueueConcurrency:
    """Concurrent access tests."""

    def test_mpmc(self):
        """Test multiple producers and consumers."""
        q = LockFreeQueue(maxsize=1000)
        num_producers = 4
        num_consumers = 4
        items_per_producer = 100

        produced = []
        consumed = []
        prod_lock = threading.Lock()
        cons_lock = threading.Lock()

        def producer(tid):
            for i in range(items_per_producer):
                item = (tid, i)
                q.put(item)
                with prod_lock:
                    produced.append(item)

        def consumer():
            local = []
            while True:
                try:
                    item = q.get(timeout=0.5)
                    local.append(item)
                except Empty:
                    break
            with cons_lock:
                consumed.extend(local)

        prod_threads = [threading.Thread(target=producer, args=(t,))
                        for t in range(num_producers)]
        cons_threads = [threading.Thread(target=consumer)
                        for _ in range(num_consumers)]

        for t in prod_threads:
            t.start()
        for t in cons_threads:
            t.start()
        for t in prod_threads:
            t.join()
        for t in cons_threads:
            t.join()

        assert len(consumed) == num_producers * items_per_producer
        assert set(consumed) == set(produced)

    def test_concurrent_enqueue_dequeue(self):
        """Test concurrent enqueue and dequeue with SCQ."""
        q = SCQ(capacity=256)
        num_ops = 500
        enqueued = []
        dequeued = []
        enq_lock = threading.Lock()
        deq_lock = threading.Lock()

        def enqueuer():
            for i in range(num_ops):
                while not q.enqueue(i):
                    time.sleep(0.0001)
                with enq_lock:
                    enqueued.append(i)

        def dequeuer():
            count = 0
            while count < num_ops:
                item = q.dequeue()
                if item is not None:
                    with deq_lock:
                        dequeued.append(item)
                    count += 1
                else:
                    time.sleep(0.0001)

        t1 = threading.Thread(target=enqueuer)
        t2 = threading.Thread(target=dequeuer)

        t1.start()
        t2.start()
        t1.join()
        t2.join()

        assert len(dequeued) == num_ops
        assert set(dequeued) == set(range(num_ops))
