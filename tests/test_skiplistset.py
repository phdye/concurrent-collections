"""Tests for the SkipListSet implementation."""

import pytest
import threading
from concurrent_collections import SkipListSet, FrozenSkipListSet


class TestSkipListSetBasic:
    """Basic functionality tests."""

    def test_create_empty_set(self):
        """Test creating an empty set."""
        s = SkipListSet()
        assert len(s) == 0
        assert list(s) == []

    def test_add_single(self):
        """Test adding a single item."""
        s = SkipListSet()
        s.add('item')
        assert 'item' in s
        assert len(s) == 1

    def test_add_duplicate(self):
        """Test adding duplicate has no effect."""
        s = SkipListSet()
        s.add('item')
        s.add('item')
        assert len(s) == 1

    def test_contains(self):
        """Test __contains__."""
        s = SkipListSet()
        s.add('a')
        s.add('b')

        assert 'a' in s
        assert 'b' in s
        assert 'c' not in s

    def test_discard(self):
        """Test discard."""
        s = SkipListSet()
        s.add('item')
        s.discard('item')
        assert 'item' not in s

    def test_discard_missing(self):
        """Test discard on missing item (no exception)."""
        s = SkipListSet()
        s.discard('missing')  # Should not raise

    def test_remove(self):
        """Test remove."""
        s = SkipListSet()
        s.add('item')
        s.remove('item')
        assert 'item' not in s

    def test_remove_missing_raises(self):
        """Test remove on missing raises KeyError."""
        s = SkipListSet()
        with pytest.raises(KeyError):
            s.remove('missing')

    def test_pop(self):
        """Test pop."""
        s = SkipListSet()
        s.add('a')
        s.add('b')

        item = s.pop()
        assert item in ('a', 'b')
        assert len(s) == 1

    def test_pop_empty_raises(self):
        """Test pop on empty raises KeyError."""
        s = SkipListSet()
        with pytest.raises(KeyError):
            s.pop()

    def test_clear(self):
        """Test clear."""
        s = SkipListSet()
        s.add('a')
        s.add('b')
        s.clear()

        assert len(s) == 0

    def test_iteration_order(self):
        """Test items are iterated in sorted order."""
        s = SkipListSet()
        s.add('charlie')
        s.add('alice')
        s.add('bob')

        assert list(s) == ['alice', 'bob', 'charlie']


class TestSkipListSetOperations:
    """Tests for set operations."""

    def test_union(self):
        """Test union."""
        s1 = SkipListSet([1, 2, 3])
        s2 = SkipListSet([3, 4, 5])

        result = s1.union(s2)
        assert list(result) == [1, 2, 3, 4, 5]

    def test_union_operator(self):
        """Test | operator."""
        s1 = SkipListSet([1, 2])
        s2 = {2, 3}

        result = s1 | s2
        assert list(result) == [1, 2, 3]

    def test_intersection(self):
        """Test intersection."""
        s1 = SkipListSet([1, 2, 3])
        s2 = SkipListSet([2, 3, 4])

        result = s1.intersection(s2)
        assert list(result) == [2, 3]

    def test_intersection_operator(self):
        """Test & operator."""
        s1 = SkipListSet([1, 2, 3])
        s2 = {2, 3, 4}

        result = s1 & s2
        assert list(result) == [2, 3]

    def test_difference(self):
        """Test difference."""
        s1 = SkipListSet([1, 2, 3])
        s2 = SkipListSet([2, 3, 4])

        result = s1.difference(s2)
        assert list(result) == [1]

    def test_difference_operator(self):
        """Test - operator."""
        s1 = SkipListSet([1, 2, 3])
        s2 = {2, 3}

        result = s1 - s2
        assert list(result) == [1]

    def test_symmetric_difference(self):
        """Test symmetric difference."""
        s1 = SkipListSet([1, 2, 3])
        s2 = SkipListSet([2, 3, 4])

        result = s1.symmetric_difference(s2)
        assert list(result) == [1, 4]

    def test_issubset(self):
        """Test issubset."""
        s1 = SkipListSet([1, 2])
        s2 = SkipListSet([1, 2, 3])

        assert s1.issubset(s2)
        assert not s2.issubset(s1)

    def test_issuperset(self):
        """Test issuperset."""
        s1 = SkipListSet([1, 2, 3])
        s2 = SkipListSet([1, 2])

        assert s1.issuperset(s2)
        assert not s2.issuperset(s1)

    def test_isdisjoint(self):
        """Test isdisjoint."""
        s1 = SkipListSet([1, 2])
        s2 = SkipListSet([3, 4])
        s3 = SkipListSet([2, 3])

        assert s1.isdisjoint(s2)
        assert not s1.isdisjoint(s3)


class TestSkipListSetOrdered:
    """Tests for ordered operations."""

    def test_first(self):
        """Test first."""
        s = SkipListSet()
        s.add('c')
        s.add('a')
        s.add('b')

        assert s.first() == 'a'

    def test_first_empty_raises(self):
        """Test first on empty raises."""
        s = SkipListSet()
        with pytest.raises(KeyError):
            s.first()

    def test_last(self):
        """Test last."""
        s = SkipListSet()
        s.add('c')
        s.add('a')
        s.add('b')

        assert s.last() == 'c'

    def test_floor(self):
        """Test floor."""
        s = SkipListSet([1, 3, 5])

        assert s.floor(3) == 3
        assert s.floor(4) == 3
        assert s.floor(1) == 1

    def test_ceiling(self):
        """Test ceiling."""
        s = SkipListSet([1, 3, 5])

        assert s.ceiling(3) == 3
        assert s.ceiling(2) == 3
        assert s.ceiling(5) == 5


class TestSkipListSetRange:
    """Tests for range operations."""

    def test_range(self):
        """Test range iteration."""
        s = SkipListSet('abcdefgh')

        assert list(s.range('c', 'f')) == ['c', 'd', 'e']

    def test_subset(self):
        """Test subset."""
        s = SkipListSet('abcde')

        sub = s.subset('b', 'd')
        assert list(sub) == ['b', 'c']

    def test_subset_inclusive(self):
        """Test subset with inclusive stop."""
        s = SkipListSet('abcde')

        sub = s.subset('b', 'd', inclusive=True)
        assert list(sub) == ['b', 'c', 'd']


class TestSkipListSetSnapshot:
    """Tests for snapshot/freeze."""

    def test_snapshot(self):
        """Test creating snapshot."""
        s = SkipListSet([1, 2, 3])
        frozen = s.snapshot()

        assert isinstance(frozen, FrozenSkipListSet)
        assert list(frozen) == [1, 2, 3]

    def test_frozen_is_immutable(self):
        """Test frozen set is immutable."""
        frozen = FrozenSkipListSet([1, 2])

        with pytest.raises(TypeError):
            frozen.add(3)

        with pytest.raises(TypeError):
            frozen.discard(1)

        with pytest.raises(TypeError):
            frozen.remove(1)

    def test_frozen_thaw(self):
        """Test thawing frozen set."""
        frozen = FrozenSkipListSet([1, 2])
        thawed = frozen.thaw()

        assert isinstance(thawed, SkipListSet)
        thawed.add(3)
        assert 3 in thawed

    def test_frozen_hash(self):
        """Test frozen set is hashable."""
        frozen1 = FrozenSkipListSet([1, 2])
        frozen2 = FrozenSkipListSet([1, 2])

        assert hash(frozen1) == hash(frozen2)

    def test_frozen_equality(self):
        """Test frozen set equality."""
        frozen1 = FrozenSkipListSet([1, 2])
        frozen2 = FrozenSkipListSet([1, 2])
        frozen3 = FrozenSkipListSet([1])

        assert frozen1 == frozen2
        assert frozen1 != frozen3


class TestSkipListSetEquality:
    """Tests for equality."""

    def test_equality_with_set(self):
        """Test equality with regular set."""
        s = SkipListSet([1, 2, 3])
        assert s == {1, 2, 3}
        assert s != {1, 2}

    def test_equality_with_frozenset(self):
        """Test equality with frozenset."""
        s = SkipListSet([1, 2, 3])
        assert s == frozenset([1, 2, 3])

    def test_equality_with_skiplistset(self):
        """Test equality with another SkipListSet."""
        s1 = SkipListSet([1, 2, 3])
        s2 = SkipListSet([1, 2, 3])
        s3 = SkipListSet([1, 2])

        assert s1 == s2
        assert s1 != s3


class TestSkipListSetConcurrency:
    """Concurrent access tests."""

    def test_concurrent_adds(self):
        """Test concurrent adds."""
        s = SkipListSet()

        def adder(tid):
            for i in range(100):
                s.add(f"{tid}_{i}")

        threads = [threading.Thread(target=adder, args=(t,))
                   for t in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert len(s) == 400

    def test_concurrent_reads(self):
        """Test concurrent reads."""
        s = SkipListSet(range(100))

        def reader():
            for _ in range(100):
                for i in range(100):
                    assert i in s

        threads = [threading.Thread(target=reader) for _ in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()


class TestSkipListSetCustomComparator:
    """Tests with custom comparator."""

    def test_reverse_order(self):
        """Test with reverse comparator."""
        def reverse_cmp(a, b):
            if a < b:
                return 1
            elif a > b:
                return -1
            return 0

        s = SkipListSet([1, 2, 3], cmp=reverse_cmp)
        assert list(s) == [3, 2, 1]

    def test_with_key_function(self):
        """Test with key function."""
        s = SkipListSet(['apple', 'Banana', 'cherry'], key=str.lower)
        assert list(s) == ['apple', 'Banana', 'cherry']
