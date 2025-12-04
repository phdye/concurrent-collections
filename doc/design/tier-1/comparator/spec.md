# comparator — Specification

## Overview

The `comparator` module guarantees consistent three-way comparison semantics across all comparator types. It ensures that comparisons are transitive, antisymmetric, and deterministic within a single container lifetime.

## Invariants

1. **Transitivity**: If `compare(a, b) < 0` and `compare(b, c) < 0`, then `compare(a, c) < 0`
2. **Antisymmetry**: `compare(a, b)` and `compare(b, a)` have opposite signs (or both zero)
3. **Determinism**: `compare(a, b)` returns the same result for the same inputs within a container lifetime
4. **Immutability**: A Comparator object's comparison behavior cannot change after construction
5. **Type consistency**: `comparator_type` accurately reflects the active comparison path

## Preconditions

- Keys must be comparable by the selected comparison method
- For natural ordering: keys must implement `__lt__` and `__gt__`
- For C function comparators: function pointer must be valid and non-NULL
- For Python callables: callable must accept two arguments and return an integer
- For key functions: function must accept one argument and return a comparable object

## Contracts by Operation

### Comparator.natural()

**Signature:**
```python
@staticmethod
def natural() -> Comparator
```

**Description:** Create a comparator that uses Python's natural ordering via `__lt__` and `__gt__`.

**Preconditions:** None

**Postconditions:**
- Returns a Comparator with `type == 'natural'`
- Comparisons use `PyObject_RichCompareBool`

**Errors:** None (construction cannot fail)

**Complexity:** O(1)

**Thread Safety:** Thread-safe (returns new immutable object)

---

### Comparator.reverse()

**Signature:**
```python
@staticmethod
def reverse() -> Comparator
```

**Description:** Create a comparator that reverses natural ordering.

**Preconditions:** None

**Postconditions:**
- Returns a Comparator with `type == 'c_func'`
- `compare(a, b)` returns `-compare_natural(a, b)`

**Errors:** None

**Complexity:** O(1)

**Thread Safety:** Thread-safe

---

### Comparator.numeric()

**Signature:**
```python
@staticmethod
def numeric() -> Comparator
```

**Description:** Create a comparator optimized for `int` and `float` keys.

**Preconditions:** None

**Postconditions:**
- Returns a Comparator with `type == 'c_func'`
- For int/int or float/float: uses direct C comparison
- For mixed or other types: falls back to natural ordering

**Errors:** None

**Complexity:** O(1)

**Thread Safety:** Thread-safe

---

### Comparator.string()

**Signature:**
```python
@staticmethod
def string() -> Comparator
```

**Description:** Create a comparator optimized for `str` keys (locale-unaware).

**Preconditions:** None

**Postconditions:**
- Returns a Comparator with `type == 'c_func'`
- For str/str: uses `PyUnicode_Compare`
- For other types: falls back to natural ordering

**Errors:** None

**Complexity:** O(1)

**Thread Safety:** Thread-safe

---

### Comparator.from_cfunc

**Signature:**
```python
@staticmethod
def from_cfunc(func_ptr: int, context=None, prevent_gc: bool = False) -> Comparator
```

**Description:** Create a comparator from a C function pointer.

**Preconditions:**
- `func_ptr` is a valid memory address of a C function
- Function has signature: `int func(PyObject *a, PyObject *b, void *context)`
- Function returns negative/zero/positive for less/equal/greater
- If `prevent_gc=True`, `context` must be a Python object

**Postconditions:**
- Returns a Comparator with `type == 'c_func'`
- Comparisons call the C function directly
- If `prevent_gc=True`, Comparator holds reference to `context`

**Errors:**
- `TypeError` if `func_ptr` is not an integer
- `ValueError` if `func_ptr` is zero/NULL
- `TypeError` if `prevent_gc=True` and `context` is not a Python object

**Complexity:** O(1)

**Thread Safety:** Thread-safe

---

### Comparator_Compare (C API)

**Signature:**
```c
int Comparator_Compare(ComparatorObject *cmp, PyObject *a, PyObject *b);
```

**Description:** Compare two Python objects using the comparator.

**Preconditions:**
- `cmp` is a valid Comparator
- `a` and `b` are valid PyObject pointers

**Postconditions:**
- Returns negative if `a < b`
- Returns zero if `a == b`
- Returns positive if `a > b`
- On error: returns 0 and sets Python exception

**Errors:**
- `TypeError` if objects are not comparable
- Any exception raised by Python `__lt__`/`__gt__` or callable
- Check `PyErr_Occurred()` to distinguish error from equality

**Complexity:**
- Natural: O(comparison cost of objects)
- C function: O(function cost)
- Python callable: O(1) + callable cost

**Thread Safety:**
- Natural/C function: Thread-safe if objects are thread-safe
- Python callable: Acquires GIL if not held

---

### Container constructor with cmp/key

**Signature:**
```python
SkipListMap(cmp: Comparator | Callable = None, key: Callable = None)
```

**Description:** Create ordered container with custom comparison.

**Preconditions:**
- At most one of `cmp` or `key` may be provided
- If `cmp` is Callable (not Comparator): must accept two args
- If `key` is provided: must accept one arg

**Postconditions:**
- Container uses specified comparison method
- `container.comparator_type` reflects the method

**Errors:**
- `TypeError` if both `cmp` and `key` provided
- `TypeError` if `cmp` is not Comparator or Callable
- `TypeError` if `key` is not Callable

**Thread Safety:** Thread-safe (construction)

## Error Handling

| Error Condition | Detection | Response |
|-----------------|-----------|----------|
| NULL function pointer | Check in from_cfunc | `ValueError` |
| Non-comparable objects | `PyErr_Occurred()` | Propagate `TypeError` |
| Callable raises | `PyErr_Occurred()` | Propagate exception |
| Invalid func_ptr type | `PyLong_Check` | `TypeError` |
| Both cmp and key given | Argument check | `TypeError` |

## Thread Safety

| Guarantee | Scope | Notes |
|-----------|-------|-------|
| Construction | Thread-safe | Static methods create new objects |
| Comparison | Depends on type | See below |
| Object access | Thread-safe | Comparator is immutable |

### Per-Type Thread Safety

| Type | Thread Safety | GIL Required |
|------|---------------|--------------|
| Natural | Thread-safe* | Yes (Python calls) |
| C function | Depends on function | Can be nogil |
| Key function | Thread-safe* | Yes (Python calls) |
| Python callable | Thread-safe* | Yes (Python calls) |

*Thread-safe assuming compared objects are not mutated concurrently.

## Memory Model

### Reference Counting

```
Comparator object:
  ├── type (enum, no ref)
  ├── c_func (pointer, no ref)
  ├── py_callable (PyObject*, INCREF)
  └── context_ref (PyObject*, INCREF if prevent_gc)
```

### Ownership Rules

| Field | Ownership | Lifecycle |
|-------|-----------|-----------|
| `py_callable` | Owned | Comparator lifetime |
| `context_ref` | Owned if prevent_gc | Comparator lifetime |
| `context` (void*) | Borrowed | Must outlive Comparator |

## Performance Bounds

| Operation | Average | Worst Case | Notes |
|-----------|---------|------------|-------|
| `natural()` | O(1) | O(1) | Static singleton |
| `reverse()` | O(1) | O(1) | Static singleton |
| `from_cfunc()` | O(1) | O(1) | Allocation |
| Compare (natural) | O(cmp) | O(cmp) | Depends on key type |
| Compare (c_func) | O(func) | O(func) | Direct call |
| Compare (python) | O(call) | O(call) | Python call overhead |

## Comparison Contract

Comparators must maintain these properties for any keys a, b, c:

```
1. Reflexivity of equality:
   compare(a, a) == 0

2. Antisymmetry:
   compare(a, b) < 0  ⟹  compare(b, a) > 0
   compare(a, b) > 0  ⟹  compare(b, a) < 0
   compare(a, b) == 0 ⟹  compare(b, a) == 0

3. Transitivity:
   compare(a, b) < 0 ∧ compare(b, c) < 0  ⟹  compare(a, c) < 0
   compare(a, b) > 0 ∧ compare(b, c) > 0  ⟹  compare(a, c) > 0

4. Consistency with equality:
   compare(a, b) == 0 ∧ compare(b, c) == 0  ⟹  compare(a, c) == 0
```

Violation of these properties results in undefined container behavior.
