# comparator — Design

## Overview

The `comparator` module provides a unified comparison dispatch system for ordered containers. It allows users to customize key ordering through multiple mechanisms: natural ordering via `__lt__`, Python callables, key functions, and high-performance native function pointers. The design prioritizes the common case (natural ordering) while providing efficient paths for performance-critical custom ordering via Rust closures or C/Cython functions.

## Dependencies

| Dependency | Purpose |
|------------|---------|
| config | Runtime configuration for comparison behavior |
| PyO3 | Python-Rust bindings (if Rust implementation) |
| Python C API | `PyObject_RichCompareBool`, exception handling (if C implementation) |

## Implementation Language Note

This design supports multiple implementation approaches (decision pending):
- **Rust with PyO3**: Native Rust comparators via trait objects/closures
- **C extension**: C function pointers via Cython or direct C
- **C++ with pybind11**: C++ functors

The examples below show both C and Rust implementations. The final choice will be made during implementation planning.

## Architecture

### Core Data Structure

```c
// Function pointer type for C comparators
// Returns: negative if a < b, zero if a == b, positive if a > b
typedef int (*cc_cmp_func)(PyObject *a, PyObject *b, void *context);

// Comparator types
typedef enum {
    CC_CMP_NATURAL,     // Use PyObject_RichCompareBool (default)
    CC_CMP_C_FUNC,      // C function pointer (fastest custom)
    CC_CMP_KEY_FUNC,    // Python key function (extract once)
    CC_CMP_PYTHON       // Python callable (slowest)
} cc_cmp_type_t;

// Comparator structure
typedef struct {
    PyObject_HEAD
    cc_cmp_type_t type;
    union {
        cc_cmp_func c_func;       // For CC_CMP_C_FUNC
        PyObject *py_callable;    // For CC_CMP_PYTHON or CC_CMP_KEY_FUNC
    };
    void *context;                // Optional context for C func
    PyObject *context_ref;        // Python object to prevent GC
    bool owns_context;            // Whether to free context on dealloc
} ComparatorObject;
```

### Comparison Dispatch

```c
static inline int cc_compare(ComparatorObject *cmp, PyObject *a, PyObject *b) {
    switch (cmp->type) {
        case CC_CMP_NATURAL:
            return cc_compare_natural(a, b);

        case CC_CMP_C_FUNC:
            // Fastest path - direct C function call
            return cmp->c_func(a, b, cmp->context);

        case CC_CMP_KEY_FUNC:
            // Extract keys, then compare naturally
            return cc_compare_by_key(cmp, a, b);

        case CC_CMP_PYTHON:
            // Slowest - full Python call protocol
            return cc_compare_python(cmp, a, b);
    }
    return 0;  // Should never reach
}

static inline int cc_compare_natural(PyObject *a, PyObject *b) {
    // Three-way comparison using rich compare
    int lt = PyObject_RichCompareBool(a, b, Py_LT);
    if (lt < 0) return 0;  // Exception
    if (lt) return -1;

    int gt = PyObject_RichCompareBool(a, b, Py_GT);
    if (gt < 0) return 0;  // Exception
    if (gt) return 1;

    return 0;  // Equal
}
```

### Built-in C Comparators

```c
// Reverse ordering comparator
static int cmp_reverse(PyObject *a, PyObject *b, void *ctx) {
    return -cc_compare_natural(a, b);
}

// Optimized numeric comparator (avoids rich compare for int/float)
static int cmp_numeric(PyObject *a, PyObject *b, void *ctx) {
    // Fast path for same-type comparisons
    if (PyLong_Check(a) && PyLong_Check(b)) {
        long va = PyLong_AsLong(a);
        long vb = PyLong_AsLong(b);
        return (va > vb) - (va < vb);
    }
    if (PyFloat_Check(a) && PyFloat_Check(b)) {
        double va = PyFloat_AS_DOUBLE(a);
        double vb = PyFloat_AS_DOUBLE(b);
        return (va > vb) - (va < vb);
    }
    // Fall back to natural comparison
    return cc_compare_natural(a, b);
}

// Optimized string comparator (locale-unaware)
static int cmp_string(PyObject *a, PyObject *b, void *ctx) {
    if (PyUnicode_Check(a) && PyUnicode_Check(b)) {
        return PyUnicode_Compare(a, b);
    }
    return cc_compare_natural(a, b);
}
```

### Key Function Handling

For key functions (like `sorted(key=...)`), keys are extracted at insertion time and stored with the node:

```c
// In SkipListNode
typedef struct SkipListNode {
    PyObject *key;          // Original key
    PyObject *sort_key;     // Extracted sort key (if using key function)
    PyObject *value;
    // ...
} SkipListNode;

// Extraction at insertion
PyObject *sort_key = key;
if (cmp->type == CC_CMP_KEY_FUNC) {
    sort_key = PyObject_CallOneArg(cmp->py_callable, key);
    if (!sort_key) return -1;  // Exception
}
// Store sort_key in node

// Comparison uses sort_key
int result = cc_compare(cmp, node_a->sort_key, node_b->sort_key);
```

## API Surface

### Python API

```python
class Comparator:
    """Key comparison dispatcher for ordered containers."""

    # Built-in comparators (return Comparator instances)
    @staticmethod
    def natural() -> Comparator:
        """Default __lt__ ordering."""

    @staticmethod
    def reverse() -> Comparator:
        """Reverse of natural ordering."""

    @staticmethod
    def numeric() -> Comparator:
        """Optimized for int/float keys."""

    @staticmethod
    def string() -> Comparator:
        """Optimized for str keys (locale-unaware)."""

    # Custom comparators
    @staticmethod
    def from_cfunc(func_ptr: int, context=None, prevent_gc: bool = False) -> Comparator:
        """
        Create comparator from C function pointer.

        Args:
            func_ptr: Address of C function with signature:
                      int cmp(PyObject *a, PyObject *b, void *context)
            context: Optional context passed to each comparison
            prevent_gc: If True, hold reference to context to prevent GC
        """

    # Properties
    @property
    def type(self) -> str:
        """Return comparator type: 'natural', 'c_func', 'key_func', or 'python'."""
```

### C API

```c
// Create comparators
ComparatorObject* Comparator_Natural(void);
ComparatorObject* Comparator_Reverse(void);
ComparatorObject* Comparator_Numeric(void);
ComparatorObject* Comparator_String(void);
ComparatorObject* Comparator_FromCFunc(cc_cmp_func func, void *ctx, PyObject *ctx_ref);
ComparatorObject* Comparator_FromPython(PyObject *callable, bool is_key_func);

// Perform comparison
int Comparator_Compare(ComparatorObject *cmp, PyObject *a, PyObject *b);

// Check for pending exception after comparison
bool Comparator_HasError(void);
```

### Container Integration

```python
# Constructor accepts cmp= or key= parameter
m = SkipListMap()                           # Natural ordering
m = SkipListMap(cmp=Comparator.reverse())   # C comparator
m = SkipListMap(cmp=lambda a, b: ...)       # Python callable
m = SkipListMap(key=str.lower)              # Key function

# Report active comparator type
m.comparator_type  # 'natural', 'c_func', 'key_func', or 'python'
```

## Design Decisions

| Decision | Choice | Rationale | Alternatives Considered |
|----------|--------|-----------|------------------------|
| Three-way compare | Return -1/0/+1 | Compatible with C, efficient | Boolean less-than only (requires two calls) |
| Key extraction | At insertion time | Amortize cost, consistent ordering | At comparison time (repeated cost) |
| Context support | Void pointer + PyObject ref | Flexible, supports GC prevention | Closure capture (Python only) |
| Built-in comparators | Static methods | Clear factory pattern | Singleton instances (less flexible) |
| Error handling | Check PyErr_Occurred | Standard Python C API pattern | Return value sentinel (ambiguous) |

## Performance Characteristics

| Comparator Type | Cost per Comparison | Notes |
|-----------------|---------------------|-------|
| Natural | ~50ns | Two `PyObject_RichCompareBool` calls |
| C function | ~10ns | Direct C call, no Python overhead |
| Numeric (optimized) | ~15ns | Type check + direct comparison |
| String (optimized) | ~20ns | PyUnicode_Compare |
| Key function | ~50ns | Natural on extracted key |
| Python callable | ~500ns | Full Python call protocol |

## Integration Points

### With Ordered Containers

```c
// In SkipListMap
typedef struct {
    PyObject_HEAD
    ComparatorObject *comparator;  // Owned reference
    // ...
} SkipListMapObject;

// At construction
self->comparator = resolve_comparator(cmp_arg, key_arg);

// At comparison
int result = Comparator_Compare(self->comparator, a, b);
if (Comparator_HasError()) {
    return NULL;  // Propagate exception
}
```

### With Cython (C implementation path)

```cython
# User defines comparator function
cdef int my_cmp(PyObject* a, PyObject* b, void* ctx) noexcept nogil:
    # Custom comparison logic
    ...

# Register with library
def get_my_comparator():
    from concurrent_collections import Comparator
    return Comparator.from_cfunc(<Py_uintptr_t>my_cmp)
```

### With Rust (Rust implementation path)

If implementing in Rust with PyO3, custom comparators can be provided via Rust closures or trait implementations:

```rust
use pyo3::prelude::*;
use std::cmp::Ordering;

/// Trait for custom comparators
pub trait PyComparator: Send + Sync {
    /// Compare two Python objects
    /// Returns Ordering::Less, Equal, or Greater
    fn compare(&self, py: Python<'_>, a: &PyAny, b: &PyAny) -> PyResult<Ordering>;
}

/// Comparator type enumeration
pub enum ComparatorKind {
    Natural,
    Reverse,
    Numeric,
    String,
    RustFn(Box<dyn PyComparator>),
    PythonCallable(PyObject),
    KeyFunction(PyObject),
}

/// Main comparator struct
#[pyclass]
pub struct Comparator {
    kind: ComparatorKind,
}

#[pymethods]
impl Comparator {
    /// Create natural ordering comparator
    #[staticmethod]
    fn natural() -> Self {
        Comparator { kind: ComparatorKind::Natural }
    }

    /// Create reverse ordering comparator
    #[staticmethod]
    fn reverse() -> Self {
        Comparator { kind: ComparatorKind::Reverse }
    }

    /// Create from Rust closure (for Rust users extending the library)
    #[staticmethod]
    fn from_rust_fn(cmp_fn: Box<dyn PyComparator>) -> Self {
        Comparator { kind: ComparatorKind::RustFn(cmp_fn) }
    }

    /// Get comparator type as string
    #[getter]
    fn r#type(&self) -> &'static str {
        match &self.kind {
            ComparatorKind::Natural => "natural",
            ComparatorKind::Reverse | ComparatorKind::Numeric |
            ComparatorKind::String | ComparatorKind::RustFn(_) => "rust_fn",
            ComparatorKind::PythonCallable(_) => "python",
            ComparatorKind::KeyFunction(_) => "key_func",
        }
    }
}

impl Comparator {
    /// Internal comparison method
    pub fn compare(&self, py: Python<'_>, a: &PyAny, b: &PyAny) -> PyResult<Ordering> {
        match &self.kind {
            ComparatorKind::Natural => {
                if a.lt(b)? { Ok(Ordering::Less) }
                else if a.gt(b)? { Ok(Ordering::Greater) }
                else { Ok(Ordering::Equal) }
            }
            ComparatorKind::Reverse => {
                self.compare_natural(py, b, a)  // Swap arguments
            }
            ComparatorKind::RustFn(f) => f.compare(py, a, b),
            // ... other cases
        }
    }
}
```

#### Example: Custom Rust Comparator

```rust
use concurrent_collections::{Comparator, PyComparator};
use pyo3::prelude::*;
use std::cmp::Ordering;

/// Case-insensitive string comparator
struct CaseInsensitiveComparator;

impl PyComparator for CaseInsensitiveComparator {
    fn compare(&self, py: Python<'_>, a: &PyAny, b: &PyAny) -> PyResult<Ordering> {
        let a_str: String = a.extract()?;
        let b_str: String = b.extract()?;
        Ok(a_str.to_lowercase().cmp(&b_str.to_lowercase()))
    }
}

/// Numeric reverse comparator with fast path
struct NumericReverseComparator;

impl PyComparator for NumericReverseComparator {
    fn compare(&self, py: Python<'_>, a: &PyAny, b: &PyAny) -> PyResult<Ordering> {
        // Try fast path for i64
        if let (Ok(a_int), Ok(b_int)) = (a.extract::<i64>(), b.extract::<i64>()) {
            return Ok(b_int.cmp(&a_int));  // Reversed
        }
        // Fallback to float
        if let (Ok(a_f), Ok(b_f)) = (a.extract::<f64>(), b.extract::<f64>()) {
            return Ok(b_f.partial_cmp(&a_f).unwrap_or(Ordering::Equal));
        }
        // Fallback to Python comparison (reversed)
        if b.lt(a)? { Ok(Ordering::Less) }
        else if b.gt(a)? { Ok(Ordering::Greater) }
        else { Ok(Ordering::Equal) }
    }
}

// Register with Python module
#[pymodule]
fn my_comparators(_py: Python<'_>, m: &PyModule) -> PyResult<()> {
    #[pyfn(m)]
    fn case_insensitive() -> Comparator {
        Comparator::from_rust_fn(Box::new(CaseInsensitiveComparator))
    }

    #[pyfn(m)]
    fn numeric_reverse() -> Comparator {
        Comparator::from_rust_fn(Box::new(NumericReverseComparator))
    }

    Ok(())
}
```

#### Usage from Python

```python
from concurrent_collections import SkipListMap
from my_comparators import case_insensitive, numeric_reverse

# Case-insensitive string ordering
m = SkipListMap(cmp=case_insensitive())
m["Apple"] = 1
m["banana"] = 2
m["CHERRY"] = 3
list(m.keys())  # ['Apple', 'banana', 'CHERRY'] - case-insensitive order

# Numeric reverse ordering
m2 = SkipListMap(cmp=numeric_reverse())
m2[1] = "a"
m2[10] = "b"
m2[5] = "c"
list(m2.keys())  # [10, 5, 1]
```

## Open Questions

| Question | Options | Impact |
|----------|---------|--------|
| Thread safety | Comparator immutable vs allow mutation | Concurrent container usage |
| Comparison caching | Cache recent results vs always compute | Memory vs CPU tradeoff |
| Error propagation | Exception vs error code | API consistency |
