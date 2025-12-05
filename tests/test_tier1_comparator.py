"""Tests for comparator module (Tier 1)."""

import pytest

from concurrent_collections import (
    Comparator,
    ComparatorType,
    resolve_comparator,
)


class TestComparatorNatural:
    """Tests for natural ordering comparator."""

    def test_natural_creation(self):
        """natural() creates a valid comparator."""
        cmp = Comparator.natural()
        assert cmp.type == 'natural'

    def test_natural_comparison_less(self):
        """Natural comparator returns -1 for less than."""
        cmp = Comparator.natural()
        assert cmp.compare(1, 2) == -1
        assert cmp.compare('a', 'b') == -1

    def test_natural_comparison_greater(self):
        """Natural comparator returns 1 for greater than."""
        cmp = Comparator.natural()
        assert cmp.compare(2, 1) == 1
        assert cmp.compare('b', 'a') == 1

    def test_natural_comparison_equal(self):
        """Natural comparator returns 0 for equal."""
        cmp = Comparator.natural()
        assert cmp.compare(1, 1) == 0
        assert cmp.compare('a', 'a') == 0

    def test_natural_with_objects(self):
        """Natural comparator works with comparable objects."""
        cmp = Comparator.natural()

        class Item:
            def __init__(self, val):
                self.val = val
            def __lt__(self, other):
                return self.val < other.val
            def __gt__(self, other):
                return self.val > other.val

        a, b, c = Item(1), Item(2), Item(1)
        assert cmp.compare(a, b) == -1
        assert cmp.compare(b, a) == 1
        assert cmp.compare(a, c) == 0


class TestComparatorReverse:
    """Tests for reverse ordering comparator."""

    def test_reverse_creation(self):
        """reverse() creates a valid comparator."""
        cmp = Comparator.reverse()
        assert cmp.type == 'c_func'

    def test_reverse_comparison(self):
        """Reverse comparator inverts natural ordering."""
        cmp = Comparator.reverse()
        assert cmp.compare(1, 2) == 1   # 1 > 2 in reverse
        assert cmp.compare(2, 1) == -1  # 2 < 1 in reverse
        assert cmp.compare(1, 1) == 0


class TestComparatorNumeric:
    """Tests for numeric comparator."""

    def test_numeric_creation(self):
        """numeric() creates a valid comparator."""
        cmp = Comparator.numeric()
        assert cmp.type == 'c_func'

    def test_numeric_int_comparison(self):
        """Numeric comparator handles integers."""
        cmp = Comparator.numeric()
        assert cmp.compare(1, 2) == -1
        assert cmp.compare(2, 1) == 1
        assert cmp.compare(5, 5) == 0

    def test_numeric_float_comparison(self):
        """Numeric comparator handles floats."""
        cmp = Comparator.numeric()
        assert cmp.compare(1.5, 2.5) == -1
        assert cmp.compare(2.5, 1.5) == 1
        assert cmp.compare(1.0, 1.0) == 0

    def test_numeric_mixed_comparison(self):
        """Numeric comparator handles int/float mix."""
        cmp = Comparator.numeric()
        assert cmp.compare(1, 2.0) == -1
        assert cmp.compare(2.0, 1) == 1

    def test_numeric_fallback(self):
        """Numeric comparator falls back for non-numeric types."""
        cmp = Comparator.numeric()
        assert cmp.compare('a', 'b') == -1


class TestComparatorString:
    """Tests for string comparator."""

    def test_string_creation(self):
        """string() creates a valid comparator."""
        cmp = Comparator.string()
        assert cmp.type == 'c_func'

    def test_string_comparison(self):
        """String comparator handles strings."""
        cmp = Comparator.string()
        assert cmp.compare('apple', 'banana') == -1
        assert cmp.compare('cherry', 'banana') == 1
        assert cmp.compare('apple', 'apple') == 0

    def test_string_fallback(self):
        """String comparator falls back for non-string types."""
        cmp = Comparator.string()
        assert cmp.compare(1, 2) == -1


class TestComparatorFromCallable:
    """Tests for Python callable comparators."""

    def test_from_callable_creation(self):
        """from_callable() creates a valid comparator."""
        cmp = Comparator.from_callable(lambda a, b: a - b)
        assert cmp.type == 'python'

    def test_from_callable_comparison(self):
        """Callable comparator uses provided function."""
        def by_length(a, b):
            return len(a) - len(b)

        cmp = Comparator.from_callable(by_length)
        assert cmp.compare('ab', 'abc') == -1  # 2 - 3 = -1
        assert cmp.compare('abcd', 'ab') == 2   # 4 - 2 = 2
        assert cmp.compare('ab', 'xy') == 0     # 2 - 2 = 0

    def test_from_callable_lambda(self):
        """Callable comparator works with lambdas."""
        cmp = Comparator.from_callable(lambda a, b: (a > b) - (a < b))
        assert cmp.compare(1, 2) == -1
        assert cmp.compare(2, 1) == 1

    def test_from_callable_not_callable(self):
        """from_callable() rejects non-callable."""
        with pytest.raises(TypeError):
            Comparator.from_callable(42)


class TestComparatorFromKey:
    """Tests for key function comparators."""

    def test_from_key_creation(self):
        """from_key() creates a valid comparator."""
        cmp = Comparator.from_key(len)
        assert cmp.type == 'key_func'

    def test_from_key_extracts_key(self):
        """Key comparator extracts keys correctly."""
        cmp = Comparator.from_key(str.lower)
        assert cmp.extract_key('HELLO') == 'hello'

    def test_from_key_comparison(self):
        """Key comparator compares by extracted key."""
        cmp = Comparator.from_key(abs)
        # Compare by absolute value
        # Need to manually compare extracted keys
        key_a = cmp.extract_key(-5)
        key_b = cmp.extract_key(3)
        assert cmp.compare(key_a, key_b) == 1  # 5 > 3

    def test_from_key_not_callable(self):
        """from_key() rejects non-callable."""
        with pytest.raises(TypeError):
            Comparator.from_key("not callable")


class TestComparatorFromCFunc:
    """Tests for C function comparators."""

    def test_from_cfunc_rejects_null(self):
        """from_cfunc() rejects NULL pointer."""
        with pytest.raises(ValueError):
            Comparator.from_cfunc(0)

    def test_from_cfunc_rejects_non_int(self):
        """from_cfunc() rejects non-integer."""
        with pytest.raises(TypeError):
            Comparator.from_cfunc("not a pointer")

    def test_from_cfunc_creation(self):
        """from_cfunc() creates a comparator with valid pointer."""
        # Use a fake but non-zero pointer for testing
        # Note: This won't actually work for comparison, just tests construction
        cmp = Comparator.from_cfunc(0x1000)
        assert cmp.type == 'c_func'


class TestResolveComparator:
    """Tests for resolve_comparator helper."""

    def test_resolve_none(self):
        """resolve_comparator with no args returns natural."""
        cmp = resolve_comparator()
        assert cmp.type == 'natural'

    def test_resolve_comparator_instance(self):
        """resolve_comparator passes through Comparator instances."""
        original = Comparator.reverse()
        resolved = resolve_comparator(cmp=original)
        assert resolved is original

    def test_resolve_callable(self):
        """resolve_comparator wraps callable."""
        resolved = resolve_comparator(cmp=lambda a, b: a - b)
        assert resolved.type == 'python'

    def test_resolve_key(self):
        """resolve_comparator creates key comparator."""
        resolved = resolve_comparator(key=len)
        assert resolved.type == 'key_func'

    def test_resolve_both_error(self):
        """resolve_comparator rejects both cmp and key."""
        with pytest.raises(TypeError):
            resolve_comparator(cmp=lambda a, b: 0, key=len)

    def test_resolve_invalid_cmp(self):
        """resolve_comparator rejects invalid cmp."""
        with pytest.raises(TypeError):
            resolve_comparator(cmp=42)

    def test_resolve_invalid_key(self):
        """resolve_comparator rejects invalid key."""
        with pytest.raises(TypeError):
            resolve_comparator(key="not callable")


class TestComparatorInvariants:
    """Tests for comparator invariants (transitivity, antisymmetry)."""

    def test_antisymmetry(self):
        """Comparators maintain antisymmetry."""
        comparators = [
            Comparator.natural(),
            Comparator.reverse(),
            Comparator.numeric(),
            Comparator.string(),
        ]
        values = [1, 2, 3, 4, 5]

        for cmp in comparators:
            for a in values:
                for b in values:
                    ab = cmp.compare(a, b)
                    ba = cmp.compare(b, a)
                    # If a < b then b > a
                    if ab < 0:
                        assert ba > 0
                    elif ab > 0:
                        assert ba < 0
                    else:
                        assert ba == 0

    def test_transitivity(self):
        """Comparators maintain transitivity."""
        cmp = Comparator.natural()
        values = [1, 2, 3, 4, 5]

        for a in values:
            for b in values:
                for c in values:
                    ab = cmp.compare(a, b)
                    bc = cmp.compare(b, c)
                    ac = cmp.compare(a, c)

                    # If a < b and b < c, then a < c
                    if ab < 0 and bc < 0:
                        assert ac < 0
                    # If a > b and b > c, then a > c
                    if ab > 0 and bc > 0:
                        assert ac > 0

    def test_reflexivity(self):
        """Comparators maintain reflexivity of equality."""
        comparators = [
            Comparator.natural(),
            Comparator.reverse(),
            Comparator.numeric(),
            Comparator.string(),
        ]
        values = [1, 2, 'a', 'b', 1.5, 2.5]

        for cmp in comparators:
            for v in values:
                try:
                    assert cmp.compare(v, v) == 0
                except TypeError:
                    # Some comparisons may fail for mixed types
                    pass


class TestComparatorRepr:
    """Tests for comparator string representation."""

    def test_natural_repr(self):
        """Natural comparator has useful repr."""
        cmp = Comparator.natural()
        assert 'Comparator' in repr(cmp)
        assert 'natural' in repr(cmp)

    def test_reverse_repr(self):
        """Reverse comparator has useful repr."""
        cmp = Comparator.reverse()
        assert 'Comparator' in repr(cmp)
