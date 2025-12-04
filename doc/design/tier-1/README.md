# Tier 1: Comparator System

## Overview

The comparator system provides key comparison dispatch for ordered containers. It supports natural ordering (via `__lt__`), Python callables, key functions, and high-performance C function pointers for Cython integration.

## Dependencies

- Tier 0: `config` (for type dispatch)

## Modules

| Module | Description | Complexity |
|--------|-------------|------------|
| `comparator` | Comparison dispatch, C function pointers, key extraction | Medium |

## Completion Criteria

- [ ] Natural ordering works via `PyObject_RichCompare`
- [ ] C function comparators callable without Python overhead
- [ ] Python callable comparators work (with documented overhead)
- [ ] Key functions (like `sorted(key=...)`) extract key once at insertion
- [ ] Built-in comparators: `reverse()`, `numeric()`, `string()`
- [ ] Cython integration documented with examples
- [ ] `comparator_type` attribute reports active type
- [ ] design.md, spec.md, tests.md complete

## Key Concepts

### Comparator Types

| Type | Performance | Use Case |
|------|-------------|----------|
| Natural (`__lt__`) | Baseline | Default, keys are naturally comparable |
| Built-in C | ~100% | Reverse order, numeric optimization |
| Custom C (Cython) | ~80-95% | Complex custom ordering, performance-critical |
| Python callable | ~10% | Prototyping, non-critical paths |

### Internal Dispatch

```c
typedef int (*cmp_func)(PyObject *a, PyObject *b, void *context);

typedef struct {
    enum { CMP_NATURAL, CMP_C_FUNC, CMP_KEY_FUNC, CMP_PYTHON } type;
    union {
        cmp_func c_func;      // C function pointer
        PyObject *py_cmp;     // Python callable (cmp)
        PyObject *py_key;     // Python callable (key)
    };
    void *context;            // Optional context for C func
} Comparator;
```
