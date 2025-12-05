"""Tests for the SkipListMap implementation."""

import pytest
import threading
from concurrent_collections import SkipListMap, FrozenSkipListMap


class TestSkipListMapBasic:
    """Basic functionality tests."""

    def test_create_empty_map(self):
        """Test creating an empty map."""
        m = SkipListMap()
        assert len(m) == 0
        assert list(m) == []

    def test_setitem_getitem(self):
        """Test setting and getting items."""
        m = SkipListMap()
        m['key1'] = 'value1'
        m['key2'] = 'value2'

        assert m['key1'] == 'value1'
        assert m['key2'] == 'value2'

    def test_getitem_missing_raises(self):
        """Test getting missing key raises KeyError."""
        m = SkipListMap()
        with pytest.raises(KeyError):
            _ = m['missing']

    def test_contains(self):
        """Test __contains__."""
        m = SkipListMap()
        m['key'] = 'value'

        assert 'key' in m
        assert 'missing' not in m

    def test_len(self):
        """Test __len__."""
        m = SkipListMap()
        assert len(m) == 0

        m['a'] = 1
        m['b'] = 2
        assert len(m) == 2

    def test_delitem(self):
        """Test __delitem__."""
        m = SkipListMap()
        m['key'] = 'value'
        del m['key']

        assert 'key' not in m
        assert len(m) == 0

    def test_delitem_missing_raises(self):
        """Test deleting missing key raises KeyError."""
        m = SkipListMap()
        with pytest.raises(KeyError):
            del m['missing']

    def test_iteration_order(self):
        """Test keys are iterated in sorted order."""
        m = SkipListMap()
        m['charlie'] = 3
        m['alice'] = 1
        m['bob'] = 2

        assert list(m) == ['alice', 'bob', 'charlie']

    def test_get_with_default(self):
        """Test get with default."""
        m = SkipListMap()
        m['key'] = 'value'

        assert m.get('key') == 'value'
        assert m.get('missing') is None
        assert m.get('missing', 'default') == 'default'

    def test_pop(self):
        """Test pop."""
        m = SkipListMap()
        m['key'] = 'value'

        assert m.pop('key') == 'value'
        assert 'key' not in m

    def test_pop_missing_with_default(self):
        """Test pop with missing key and default."""
        m = SkipListMap()
        assert m.pop('missing', 'default') == 'default'

    def test_pop_missing_raises(self):
        """Test pop with missing key raises."""
        m = SkipListMap()
        with pytest.raises(KeyError):
            m.pop('missing')

    def test_setdefault(self):
        """Test setdefault."""
        m = SkipListMap()

        result = m.setdefault('key', 'default')
        assert result == 'default'
        assert m['key'] == 'default'

        result = m.setdefault('key', 'other')
        assert result == 'default'  # Existing value

    def test_update_from_dict(self):
        """Test update from dict."""
        m = SkipListMap()
        m.update({'a': 1, 'b': 2})

        assert m['a'] == 1
        assert m['b'] == 2

    def test_update_from_items(self):
        """Test update from items."""
        m = SkipListMap()
        m.update([('a', 1), ('b', 2)])

        assert m['a'] == 1
        assert m['b'] == 2

    def test_clear(self):
        """Test clear."""
        m = SkipListMap()
        m['a'] = 1
        m['b'] = 2

        m.clear()
        assert len(m) == 0

    def test_keys_values_items(self):
        """Test keys, values, items methods."""
        m = SkipListMap()
        m['b'] = 2
        m['a'] = 1
        m['c'] = 3

        assert list(m.keys()) == ['a', 'b', 'c']
        assert list(m.values()) == [1, 2, 3]
        assert list(m.items()) == [('a', 1), ('b', 2), ('c', 3)]


class TestSkipListMapAtomic:
    """Tests for atomic operations."""

    def test_put_if_absent(self):
        """Test put_if_absent."""
        m = SkipListMap()

        result = m.put_if_absent('key', 'value1')
        assert result is None  # Inserted
        assert m['key'] == 'value1'

        result = m.put_if_absent('key', 'value2')
        assert result == 'value1'  # Already exists
        assert m['key'] == 'value1'

    def test_replace(self):
        """Test replace."""
        m = SkipListMap()

        result = m.replace('key', 'value')
        assert result is None  # Key didn't exist

        m['key'] = 'old'
        result = m.replace('key', 'new')
        assert result == 'old'
        assert m['key'] == 'new'

    def test_replace_if(self):
        """Test replace_if."""
        m = SkipListMap()
        m['key'] = 'old'

        assert not m.replace_if('key', 'wrong', 'new')
        assert m['key'] == 'old'

        assert m.replace_if('key', 'old', 'new')
        assert m['key'] == 'new'

    def test_compute_if_absent(self):
        """Test compute_if_absent."""
        m = SkipListMap()

        def compute(k):
            return f"computed_{k}"

        result = m.compute_if_absent('key', compute)
        assert result == 'computed_key'
        assert m['key'] == 'computed_key'

        # Should not recompute
        result = m.compute_if_absent('key', lambda k: 'other')
        assert result == 'computed_key'


class TestSkipListMapOrdered:
    """Tests for ordered operations."""

    def test_first_key(self):
        """Test first_key."""
        m = SkipListMap()
        m['c'] = 3
        m['a'] = 1
        m['b'] = 2

        assert m.first_key() == 'a'

    def test_first_key_empty_raises(self):
        """Test first_key on empty raises."""
        m = SkipListMap()
        with pytest.raises(KeyError):
            m.first_key()

    def test_last_key(self):
        """Test last_key."""
        m = SkipListMap()
        m['c'] = 3
        m['a'] = 1
        m['b'] = 2

        assert m.last_key() == 'c'

    def test_floor_key(self):
        """Test floor_key."""
        m = SkipListMap()
        m['a'] = 1
        m['c'] = 3
        m['e'] = 5

        assert m.floor_key('c') == 'c'
        assert m.floor_key('d') == 'c'
        assert m.floor_key('a') == 'a'

    def test_ceiling_key(self):
        """Test ceiling_key."""
        m = SkipListMap()
        m['a'] = 1
        m['c'] = 3
        m['e'] = 5

        assert m.ceiling_key('c') == 'c'
        assert m.ceiling_key('b') == 'c'
        assert m.ceiling_key('e') == 'e'


class TestSkipListMapRange:
    """Tests for range operations."""

    def test_keys_range(self):
        """Test keys with range."""
        m = SkipListMap()
        for i, c in enumerate('abcdefgh'):
            m[c] = i

        assert list(m.keys('c', 'f')) == ['c', 'd', 'e']

    def test_items_range(self):
        """Test items with range."""
        m = SkipListMap()
        for i, c in enumerate('abcde'):
            m[c] = i

        assert list(m.items('b', 'd')) == [('b', 1), ('c', 2)]

    def test_submap(self):
        """Test submap."""
        m = SkipListMap()
        for i, c in enumerate('abcde'):
            m[c] = i

        sub = m.submap('b', 'd')
        assert list(sub.keys()) == ['b', 'c']

    def test_submap_inclusive(self):
        """Test submap with inclusive stop."""
        m = SkipListMap()
        for i, c in enumerate('abcde'):
            m[c] = i

        sub = m.submap('b', 'd', inclusive=True)
        assert list(sub.keys()) == ['b', 'c', 'd']


class TestSkipListMapSnapshot:
    """Tests for snapshot/freeze."""

    def test_snapshot(self):
        """Test creating snapshot."""
        m = SkipListMap()
        m['a'] = 1
        m['b'] = 2

        frozen = m.snapshot()
        assert isinstance(frozen, FrozenSkipListMap)
        assert frozen['a'] == 1
        assert frozen['b'] == 2

    def test_frozen_is_immutable(self):
        """Test frozen map is immutable."""
        frozen = FrozenSkipListMap([('a', 1)])

        with pytest.raises(TypeError):
            frozen['b'] = 2

        with pytest.raises(TypeError):
            del frozen['a']

    def test_frozen_iteration(self):
        """Test frozen map iteration."""
        frozen = FrozenSkipListMap([('c', 3), ('a', 1), ('b', 2)])

        assert list(frozen) == ['a', 'b', 'c']
        assert list(frozen.items()) == [('a', 1), ('b', 2), ('c', 3)]

    def test_frozen_thaw(self):
        """Test thawing frozen map."""
        frozen = FrozenSkipListMap([('a', 1), ('b', 2)])
        thawed = frozen.thaw()

        assert isinstance(thawed, SkipListMap)
        thawed['c'] = 3
        assert 'c' in thawed

    def test_frozen_hash(self):
        """Test frozen map is hashable."""
        frozen1 = FrozenSkipListMap([('a', 1)])
        frozen2 = FrozenSkipListMap([('a', 1)])

        assert hash(frozen1) == hash(frozen2)

    def test_frozen_equality(self):
        """Test frozen map equality."""
        frozen1 = FrozenSkipListMap([('a', 1), ('b', 2)])
        frozen2 = FrozenSkipListMap([('a', 1), ('b', 2)])
        frozen3 = FrozenSkipListMap([('a', 1)])

        assert frozen1 == frozen2
        assert frozen1 != frozen3


class TestSkipListMapConcurrency:
    """Concurrent access tests."""

    def test_concurrent_reads(self):
        """Test concurrent reads."""
        m = SkipListMap()
        for i in range(100):
            m[str(i)] = i

        def reader():
            for _ in range(100):
                for i in range(100):
                    assert m.get(str(i)) == i

        threads = [threading.Thread(target=reader) for _ in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

    def test_concurrent_writes(self):
        """Test concurrent writes."""
        m = SkipListMap()

        def writer(tid):
            for i in range(100):
                m[f"{tid}_{i}"] = (tid, i)

        threads = [threading.Thread(target=writer, args=(t,))
                   for t in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()

        assert len(m) == 400
