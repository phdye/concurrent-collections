"""Tests for atomics module (Tier 0)."""

import threading
import pytest

from concurrent_collections import (
    AtomicInt,
    AtomicPtr,
    AtomicFlag,
    MemoryOrder,
    atomic_thread_fence,
)


class TestMemoryOrder:
    """Tests for MemoryOrder enum."""

    def test_memory_order_values(self):
        """MemoryOrder contains expected values."""
        assert MemoryOrder.RELAXED == 0
        assert MemoryOrder.CONSUME == 1
        assert MemoryOrder.ACQUIRE == 2
        assert MemoryOrder.RELEASE == 3
        assert MemoryOrder.ACQ_REL == 4
        assert MemoryOrder.SEQ_CST == 5


class TestAtomicInt:
    """Tests for AtomicInt class."""

    def test_init_default(self):
        """AtomicInt initializes to 0 by default."""
        a = AtomicInt()
        assert a.load() == 0

    def test_init_with_value(self):
        """AtomicInt initializes to specified value."""
        a = AtomicInt(42)
        assert a.load() == 42

    def test_load_store(self):
        """load() and store() work correctly."""
        a = AtomicInt(10)
        assert a.load() == 10
        a.store(20)
        assert a.load() == 20

    def test_exchange(self):
        """exchange() returns old value and stores new."""
        a = AtomicInt(10)
        old = a.exchange(20)
        assert old == 10
        assert a.load() == 20

    def test_compare_exchange_success(self):
        """compare_exchange succeeds when expected matches."""
        a = AtomicInt(10)
        success, actual = a.compare_exchange_strong(10, 20)
        assert success is True
        assert actual == 10
        assert a.load() == 20

    def test_compare_exchange_failure(self):
        """compare_exchange fails when expected doesn't match."""
        a = AtomicInt(10)
        success, actual = a.compare_exchange_strong(5, 20)
        assert success is False
        assert actual == 10
        assert a.load() == 10

    def test_compare_exchange_weak(self):
        """compare_exchange_weak has same semantics in Python."""
        a = AtomicInt(10)
        success, actual = a.compare_exchange_weak(10, 20)
        assert success is True
        assert a.load() == 20

    def test_fetch_add(self):
        """fetch_add returns old value and adds."""
        a = AtomicInt(10)
        old = a.fetch_add(5)
        assert old == 10
        assert a.load() == 15

    def test_fetch_sub(self):
        """fetch_sub returns old value and subtracts."""
        a = AtomicInt(10)
        old = a.fetch_sub(3)
        assert old == 10
        assert a.load() == 7

    def test_fetch_or(self):
        """fetch_or returns old value and ORs."""
        a = AtomicInt(0b1010)
        old = a.fetch_or(0b0101)
        assert old == 0b1010
        assert a.load() == 0b1111

    def test_fetch_and(self):
        """fetch_and returns old value and ANDs."""
        a = AtomicInt(0b1111)
        old = a.fetch_and(0b1100)
        assert old == 0b1111
        assert a.load() == 0b1100

    def test_value_property(self):
        """value property returns current value."""
        a = AtomicInt(42)
        assert a.value == 42

    def test_negative_values(self):
        """Negative values work correctly."""
        a = AtomicInt(-10)
        assert a.load() == -10
        a.fetch_add(15)
        assert a.load() == 5

    def test_memory_order_parameter(self):
        """Memory order parameters are accepted."""
        a = AtomicInt(0)
        a.load(MemoryOrder.ACQUIRE)
        a.store(1, MemoryOrder.RELEASE)
        a.exchange(2, MemoryOrder.ACQ_REL)
        a.compare_exchange_strong(
            2, 3,
            MemoryOrder.ACQ_REL,
            MemoryOrder.ACQUIRE
        )
        a.fetch_add(1, MemoryOrder.RELAXED)


class TestAtomicIntThreadSafety:
    """Thread safety tests for AtomicInt."""

    def test_concurrent_fetch_add(self):
        """fetch_add is thread-safe with concurrent access."""
        a = AtomicInt(0)
        num_threads = 10
        increments_per_thread = 1000

        def increment():
            for _ in range(increments_per_thread):
                a.fetch_add(1)

        threads = [threading.Thread(target=increment) for _ in range(num_threads)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert a.load() == num_threads * increments_per_thread

    def test_concurrent_compare_exchange(self):
        """compare_exchange is thread-safe with concurrent access."""
        a = AtomicInt(0)
        success_count = AtomicInt(0)
        num_threads = 10
        attempts_per_thread = 100

        def try_cas():
            for _ in range(attempts_per_thread):
                while True:
                    old = a.load()
                    success, _ = a.compare_exchange_strong(old, old + 1)
                    if success:
                        success_count.fetch_add(1)
                        break

        threads = [threading.Thread(target=try_cas) for _ in range(num_threads)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert a.load() == num_threads * attempts_per_thread
        assert success_count.load() == num_threads * attempts_per_thread


class TestAtomicPtr:
    """Tests for AtomicPtr class."""

    def test_init_default(self):
        """AtomicPtr initializes to None by default."""
        p = AtomicPtr()
        assert p.load() is None

    def test_init_with_value(self):
        """AtomicPtr initializes to specified reference."""
        obj = [1, 2, 3]
        p = AtomicPtr(obj)
        assert p.load() is obj

    def test_load_store(self):
        """load() and store() work correctly."""
        obj1 = {'a': 1}
        obj2 = {'b': 2}
        p = AtomicPtr(obj1)
        assert p.load() is obj1
        p.store(obj2)
        assert p.load() is obj2

    def test_exchange(self):
        """exchange() returns old reference and stores new."""
        obj1 = "first"
        obj2 = "second"
        p = AtomicPtr(obj1)
        old = p.exchange(obj2)
        assert old is obj1
        assert p.load() is obj2

    def test_compare_exchange_success(self):
        """compare_exchange succeeds when expected matches."""
        obj1 = (1, 2, 3)
        obj2 = (4, 5, 6)
        p = AtomicPtr(obj1)
        success, actual = p.compare_exchange_strong(obj1, obj2)
        assert success is True
        assert actual is obj1
        assert p.load() is obj2

    def test_compare_exchange_failure(self):
        """compare_exchange fails when expected doesn't match."""
        obj1 = [1]
        obj2 = [2]
        obj3 = [3]
        p = AtomicPtr(obj1)
        success, actual = p.compare_exchange_strong(obj2, obj3)
        assert success is False
        assert actual is obj1
        assert p.load() is obj1

    def test_compare_by_identity(self):
        """compare_exchange compares by identity, not equality."""
        obj1 = [1, 2, 3]
        obj2 = [1, 2, 3]  # Equal but different object
        obj3 = [4, 5, 6]
        p = AtomicPtr(obj1)
        # Should fail because obj2 is not the same object as obj1
        success, actual = p.compare_exchange_strong(obj2, obj3)
        assert success is False
        assert actual is obj1

    def test_value_property(self):
        """value property returns current reference."""
        obj = object()
        p = AtomicPtr(obj)
        assert p.value is obj


class TestAtomicFlag:
    """Tests for AtomicFlag class."""

    def test_init_default(self):
        """AtomicFlag initializes to False by default."""
        f = AtomicFlag()
        assert f.test() is False

    def test_init_with_value(self):
        """AtomicFlag initializes to specified value."""
        f = AtomicFlag(True)
        assert f.test() is True

    def test_test_and_set(self):
        """test_and_set returns old value and sets to True."""
        f = AtomicFlag()
        assert f.test_and_set() is False
        assert f.test() is True
        assert f.test_and_set() is True
        assert f.test() is True

    def test_clear(self):
        """clear() sets flag to False."""
        f = AtomicFlag(True)
        f.clear()
        assert f.test() is False

    def test_value_property(self):
        """value property returns current flag value."""
        f = AtomicFlag(True)
        assert f.value is True
        f.clear()
        assert f.value is False

    def test_spinlock_pattern(self):
        """AtomicFlag works as a simple spinlock."""
        lock = AtomicFlag()
        counter = [0]  # Mutable to allow modification in nested function

        def critical_section():
            # Acquire lock
            while lock.test_and_set():
                pass
            try:
                # Critical section
                counter[0] += 1
            finally:
                # Release lock
                lock.clear()

        threads = [threading.Thread(target=critical_section) for _ in range(10)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert counter[0] == 10


class TestAtomicThreadFence:
    """Tests for atomic_thread_fence function."""

    def test_fence_accepts_all_orders(self):
        """atomic_thread_fence accepts all memory orders."""
        for order in MemoryOrder:
            atomic_thread_fence(order)
