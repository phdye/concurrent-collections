"""Tests for atomics module (Tier 0)."""

import threading
import pytest

from concurrent_collections import (
    AtomicInt,
    AtomicPtr,
    AtomicFlag,
    AtomicU128,
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

    def test_fetch_xor(self):
        """fetch_xor returns old value and XORs."""
        a = AtomicInt(0b1010)
        old = a.fetch_xor(0b0110)
        assert old == 0b1010
        assert a.load() == 0b1100  # 1010 XOR 0110 = 1100

    def test_fetch_max(self):
        """fetch_max returns old value and computes max."""
        a = AtomicInt(10)
        old = a.fetch_max(5)
        assert old == 10
        assert a.load() == 10  # max(10, 5) = 10

        old = a.fetch_max(20)
        assert old == 10
        assert a.load() == 20  # max(10, 20) = 20

    def test_fetch_min(self):
        """fetch_min returns old value and computes min."""
        a = AtomicInt(10)
        old = a.fetch_min(15)
        assert old == 10
        assert a.load() == 10  # min(10, 15) = 10

        old = a.fetch_min(5)
        assert old == 10
        assert a.load() == 5  # min(10, 5) = 5


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


class TestAtomicU128:
    """Tests for AtomicU128 class (128-bit atomic operations)."""

    def test_init_default(self):
        """AtomicU128 initializes to (0, 0) by default."""
        a = AtomicU128()
        high, low = a.load()
        assert high == 0
        assert low == 0

    def test_init_with_values(self):
        """AtomicU128 initializes to specified high/low values."""
        a = AtomicU128(high=0x123456789ABCDEF0, low=0xFEDCBA9876543210)
        high, low = a.load()
        assert high == 0x123456789ABCDEF0
        assert low == 0xFEDCBA9876543210

    def test_from_int(self):
        """AtomicU128.from_int creates from Python integer."""
        # Create a 128-bit value
        value = (0x123456789ABCDEF0 << 64) | 0xFEDCBA9876543210
        a = AtomicU128.from_int(value)
        assert a.load_int() == value

    def test_load_store(self):
        """load() and store() work correctly."""
        a = AtomicU128(high=1, low=2)
        high, low = a.load()
        assert high == 1
        assert low == 2

        a.store(high=3, low=4)
        high, low = a.load()
        assert high == 3
        assert low == 4

    def test_load_store_int(self):
        """load_int() and store_int() work correctly."""
        value = (0xABCD << 64) | 0x1234
        a = AtomicU128()
        a.store_int(value)
        assert a.load_int() == value

    def test_compare_exchange_success(self):
        """compare_exchange succeeds when expected matches."""
        a = AtomicU128(high=1, low=2)
        success, actual_high, actual_low = a.compare_exchange(
            expected_high=1, expected_low=2,
            desired_high=3, desired_low=4
        )
        assert success is True
        assert actual_high == 1
        assert actual_low == 2
        assert a.load() == (3, 4)

    def test_compare_exchange_failure(self):
        """compare_exchange fails when expected doesn't match."""
        a = AtomicU128(high=1, low=2)
        success, actual_high, actual_low = a.compare_exchange(
            expected_high=5, expected_low=6,
            desired_high=3, desired_low=4
        )
        assert success is False
        assert actual_high == 1
        assert actual_low == 2
        assert a.load() == (1, 2)  # Unchanged

    def test_compare_exchange_int(self):
        """compare_exchange_int works with Python integers."""
        original = (0x100 << 64) | 0x200
        new_value = (0x300 << 64) | 0x400
        a = AtomicU128.from_int(original)

        success, actual = a.compare_exchange_int(original, new_value)
        assert success is True
        assert actual == original
        assert a.load_int() == new_value

    def test_compare_exchange_int_failure(self):
        """compare_exchange_int fails when expected doesn't match."""
        original = (0x100 << 64) | 0x200
        wrong = (0x999 << 64) | 0x888
        new_value = (0x300 << 64) | 0x400
        a = AtomicU128.from_int(original)

        success, actual = a.compare_exchange_int(wrong, new_value)
        assert success is False
        assert actual == original
        assert a.load_int() == original  # Unchanged

    def test_properties(self):
        """high, low, and value properties work correctly."""
        a = AtomicU128(high=0xAAAA, low=0xBBBB)
        assert a.high == 0xAAAA
        assert a.low == 0xBBBB
        assert a.value == (0xAAAA << 64) | 0xBBBB

    def test_64bit_boundaries(self):
        """Values at 64-bit boundaries work correctly."""
        max_64 = 0xFFFFFFFFFFFFFFFF
        a = AtomicU128(high=max_64, low=max_64)
        high, low = a.load()
        assert high == max_64
        assert low == max_64

    def test_value_masking(self):
        """Values are properly masked to 64 bits."""
        # Try to store a value larger than 64 bits
        too_large = 0x1_FFFFFFFFFFFFFFFF  # 65 bits
        a = AtomicU128(high=too_large, low=too_large)
        high, low = a.load()
        assert high == 0xFFFFFFFFFFFFFFFF  # Masked to 64 bits
        assert low == 0xFFFFFFFFFFFFFFFF


class TestAtomicU128ThreadSafety:
    """Thread safety tests for AtomicU128."""

    def test_concurrent_compare_exchange(self):
        """compare_exchange is thread-safe with concurrent access."""
        a = AtomicU128(high=0, low=0)
        success_count = AtomicInt(0)
        num_threads = 8
        attempts_per_thread = 100

        def try_cas():
            for _ in range(attempts_per_thread):
                while True:
                    high, low = a.load()
                    new_low = low + 1
                    new_high = high + (1 if new_low == 0 else 0)
                    success, _, _ = a.compare_exchange(
                        high, low, new_high, new_low
                    )
                    if success:
                        success_count.fetch_add(1)
                        break

        threads = [threading.Thread(target=try_cas) for _ in range(num_threads)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert success_count.load() == num_threads * attempts_per_thread
        # Final value should equal total increments
        assert a.low == num_threads * attempts_per_thread
