"""
comparator - Unified comparison dispatch system for ordered containers

This module provides a comparison dispatch system supporting natural ordering,
optimized type-specific comparators, custom Python callables, key functions,
and C function pointers for maximum performance.
"""

import ctypes
import functools
import threading
from enum import Enum
from typing import Any, Callable, Optional, TypeVar, Union


T = TypeVar('T')


class ComparatorType(Enum):
    """Comparator implementation type."""
    NATURAL = "natural"
    C_FUNC = "c_func"
    KEY_FUNC = "key_func"
    PYTHON = "python"


# Type for C comparator functions: int cmp(PyObject*, PyObject*, void*)
CmpFuncType = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.py_object, ctypes.py_object, ctypes.c_void_p)


def _compare_natural(a: Any, b: Any) -> int:
    """Three-way comparison using natural ordering.

    Returns:
        -1 if a < b, 0 if a == b, 1 if a > b
    """
    if a < b:
        return -1
    elif a > b:
        return 1
    return 0


def _compare_reverse(a: Any, b: Any) -> int:
    """Reverse natural ordering."""
    return -_compare_natural(a, b)


def _compare_numeric(a: Any, b: Any) -> int:
    """Optimized comparison for numeric types."""
    # Fast path for same-type int comparison
    if isinstance(a, int) and isinstance(b, int):
        return (a > b) - (a < b)
    # Fast path for float comparison
    if isinstance(a, float) and isinstance(b, float):
        return (a > b) - (a < b)
    # Handle mixed int/float
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return (a > b) - (a < b)
    # Fall back to natural ordering
    return _compare_natural(a, b)


def _compare_string(a: Any, b: Any) -> int:
    """Optimized comparison for string types."""
    if isinstance(a, str) and isinstance(b, str):
        if a < b:
            return -1
        elif a > b:
            return 1
        return 0
    # Fall back to natural ordering
    return _compare_natural(a, b)


class Comparator:
    """Key comparison dispatcher for ordered containers.

    Comparators define the ordering used by sorted containers like
    SkipListMap and TreeMap. Multiple comparison strategies are supported:

    - Natural ordering (default): Uses Python's __lt__ and __gt__
    - Reverse ordering: Inverts natural ordering
    - Numeric: Optimized for int/float keys
    - String: Optimized for str keys
    - Key function: Extracts sort keys (like sorted(key=...))
    - Python callable: Custom three-way comparison function
    - C function: Maximum performance via C ABI

    Examples:
        # Natural ordering (default)
        m = SkipListMap()

        # Reverse ordering
        m = SkipListMap(cmp=Comparator.reverse())

        # Key function
        m = SkipListMap(key=str.lower)

        # Custom Python callable
        def by_length(a, b):
            return len(a) - len(b)
        m = SkipListMap(cmp=by_length)
    """

    __slots__ = ('_type', '_compare_func', '_key_func', '_context', '_context_ref')

    def __init__(
        self,
        cmp_type: ComparatorType,
        compare_func: Optional[Callable[[Any, Any], int]] = None,
        key_func: Optional[Callable[[Any], Any]] = None,
        context: Optional[Any] = None,
        context_ref: Optional[Any] = None,
    ):
        """Initialize comparator (internal use - use static methods)."""
        self._type = cmp_type
        self._compare_func = compare_func
        self._key_func = key_func
        self._context = context
        self._context_ref = context_ref

    @staticmethod
    def natural() -> 'Comparator':
        """Create a comparator using Python's natural ordering.

        Uses __lt__ and __gt__ operators for comparison.
        This is the default comparator for ordered containers.

        Returns:
            Comparator with natural ordering
        """
        return Comparator(ComparatorType.NATURAL, _compare_natural)

    @staticmethod
    def reverse() -> 'Comparator':
        """Create a comparator that reverses natural ordering.

        Returns:
            Comparator with reversed natural ordering
        """
        return Comparator(ComparatorType.C_FUNC, _compare_reverse)

    @staticmethod
    def numeric() -> 'Comparator':
        """Create a comparator optimized for int and float keys.

        Uses direct numeric comparison for int/float pairs, falling
        back to natural ordering for other types.

        Returns:
            Comparator optimized for numeric keys
        """
        return Comparator(ComparatorType.C_FUNC, _compare_numeric)

    @staticmethod
    def string() -> 'Comparator':
        """Create a comparator optimized for str keys.

        Uses direct string comparison for str pairs, falling
        back to natural ordering for other types. This comparison
        is locale-unaware (uses byte ordering).

        Returns:
            Comparator optimized for string keys
        """
        return Comparator(ComparatorType.C_FUNC, _compare_string)

    @staticmethod
    def from_callable(func: Callable[[Any, Any], int]) -> 'Comparator':
        """Create a comparator from a Python callable.

        The callable must accept two arguments and return:
        - Negative integer if first < second
        - Zero if first == second
        - Positive integer if first > second

        Args:
            func: Comparison function

        Returns:
            Comparator wrapping the callable

        Raises:
            TypeError: If func is not callable
        """
        if not callable(func):
            raise TypeError("func must be callable")
        return Comparator(ComparatorType.PYTHON, func)

    @staticmethod
    def from_key(key_func: Callable[[Any], Any]) -> 'Comparator':
        """Create a comparator from a key function.

        The key function extracts a comparison key from each element,
        similar to the key parameter in sorted(). Keys are extracted
        at insertion time and compared using natural ordering.

        Args:
            key_func: Function to extract comparison key

        Returns:
            Comparator using key function

        Raises:
            TypeError: If key_func is not callable
        """
        if not callable(key_func):
            raise TypeError("key_func must be callable")
        return Comparator(ComparatorType.KEY_FUNC, _compare_natural, key_func)

    @staticmethod
    def from_cfunc(
        func_ptr: int,
        context: Optional[Any] = None,
        prevent_gc: bool = False,
    ) -> 'Comparator':
        """Create a comparator from a C function pointer.

        For maximum performance, custom comparators can be implemented
        in C, Cython, Rust, or other languages that support the C ABI.

        The C function must have signature:
            int cmp(PyObject *a, PyObject *b, void *context)

        And return:
        - Negative if a < b
        - Zero if a == b
        - Positive if a > b

        Args:
            func_ptr: Memory address of C function
            context: Optional context passed to each comparison
            prevent_gc: If True, hold reference to context to prevent GC

        Returns:
            Comparator calling the C function

        Raises:
            TypeError: If func_ptr is not an integer
            ValueError: If func_ptr is zero (NULL)
        """
        if not isinstance(func_ptr, int):
            raise TypeError("func_ptr must be an integer")
        if func_ptr == 0:
            raise ValueError("func_ptr cannot be NULL (zero)")

        # Create ctypes wrapper for the C function
        c_func = CmpFuncType(func_ptr)

        # Create wrapper that calls the C function
        ctx_ptr = ctypes.c_void_p(id(context) if context else 0)

        def compare_c(a: Any, b: Any) -> int:
            return c_func(a, b, ctx_ptr)

        context_ref = context if prevent_gc else None
        return Comparator(
            ComparatorType.C_FUNC,
            compare_c,
            context=context,
            context_ref=context_ref,
        )

    def compare(self, a: Any, b: Any) -> int:
        """Compare two values.

        Args:
            a: First value
            b: Second value

        Returns:
            -1 if a < b, 0 if a == b, 1 if a > b
        """
        return self._compare_func(a, b)

    def extract_key(self, value: Any) -> Any:
        """Extract comparison key from a value.

        For key function comparators, this extracts the sort key.
        For other comparators, returns the value unchanged.

        Args:
            value: Value to extract key from

        Returns:
            Comparison key
        """
        if self._key_func is not None:
            return self._key_func(value)
        return value

    @property
    def type(self) -> str:
        """Get comparator type as string.

        Returns:
            'natural', 'c_func', 'key_func', or 'python'
        """
        return self._type.value

    def __repr__(self) -> str:
        return f"Comparator(type='{self.type}')"


def resolve_comparator(
    cmp: Optional[Union[Comparator, Callable[[Any, Any], int]]] = None,
    key: Optional[Callable[[Any], Any]] = None,
) -> Comparator:
    """Resolve comparator from cmp/key parameters.

    This helper function is used by container constructors to create
    the appropriate comparator from user-provided parameters.

    Args:
        cmp: Comparator instance or comparison callable
        key: Key extraction function

    Returns:
        Resolved Comparator

    Raises:
        TypeError: If both cmp and key are provided
        TypeError: If cmp is not Comparator or callable
        TypeError: If key is not callable
    """
    if cmp is not None and key is not None:
        raise TypeError("Cannot specify both 'cmp' and 'key'")

    if cmp is not None:
        if isinstance(cmp, Comparator):
            return cmp
        if callable(cmp):
            return Comparator.from_callable(cmp)
        raise TypeError("cmp must be a Comparator or callable")

    if key is not None:
        if not callable(key):
            raise TypeError("key must be callable")
        return Comparator.from_key(key)

    # Default: natural ordering
    return Comparator.natural()


# Singleton comparators for common cases
_NATURAL_COMPARATOR = Comparator.natural()
_REVERSE_COMPARATOR = Comparator.reverse()
_NUMERIC_COMPARATOR = Comparator.numeric()
_STRING_COMPARATOR = Comparator.string()
