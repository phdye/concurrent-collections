# comparator — Test Coverage

## Overview

Testing strategy validates comparison correctness, type dispatch accuracy, performance characteristics, and error handling. Tests cover all comparator types and their integration with ordered containers.

## Test Categories

### Unit Tests — Construction

| Test | Covers | Status |
|------|--------|--------|
| `test_natural_returns_comparator` | `Comparator.natural()` returns valid object | ⬜ |
| `test_reverse_returns_comparator` | `Comparator.reverse()` returns valid object | ⬜ |
| `test_numeric_returns_comparator` | `Comparator.numeric()` returns valid object | ⬜ |
| `test_string_returns_comparator` | `Comparator.string()` returns valid object | ⬜ |
| `test_natural_type_is_natural` | `natural().type == 'natural'` | ⬜ |
| `test_reverse_type_is_cfunc` | `reverse().type == 'c_func'` | ⬜ |
| `test_numeric_type_is_cfunc` | `numeric().type == 'c_func'` | ⬜ |
| `test_string_type_is_cfunc` | `string().type == 'c_func'` | ⬜ |
| `test_from_cfunc_basic` | `from_cfunc()` with valid pointer | ⬜ |
| `test_from_cfunc_with_context` | `from_cfunc()` with context | ⬜ |
| `test_from_cfunc_prevent_gc` | `from_cfunc()` with prevent_gc=True | ⬜ |

Legend: ⬜ Not implemented, 🔶 Partial, ✅ Complete

### Unit Tests — Comparison Behavior

| Test | Covers | Status |
|------|--------|--------|
| `test_natural_less_than` | `compare(1, 2) < 0` | ⬜ |
| `test_natural_greater_than` | `compare(2, 1) > 0` | ⬜ |
| `test_natural_equal` | `compare(1, 1) == 0` | ⬜ |
| `test_natural_strings` | Natural ordering of strings | ⬜ |
| `test_natural_tuples` | Natural ordering of tuples | ⬜ |
| `test_reverse_less_than` | `compare(1, 2) > 0` (reversed) | ⬜ |
| `test_reverse_greater_than` | `compare(2, 1) < 0` (reversed) | ⬜ |
| `test_reverse_equal` | `compare(1, 1) == 0` | ⬜ |
| `test_numeric_int_int` | Fast path for int comparison | ⬜ |
| `test_numeric_float_float` | Fast path for float comparison | ⬜ |
| `test_numeric_int_float` | Mixed numeric comparison | ⬜ |
| `test_numeric_fallback` | Non-numeric falls back to natural | ⬜ |
| `test_string_str_str` | Fast path for string comparison | ⬜ |
| `test_string_fallback` | Non-string falls back to natural | ⬜ |

### Unit Tests — Python Callable

| Test | Covers | Status |
|------|--------|--------|
| `test_python_callable_basic` | Lambda comparator works | ⬜ |
| `test_python_callable_function` | Function comparator works | ⬜ |
| `test_python_callable_type_reported` | `type == 'python'` | ⬜ |
| `test_python_callable_exception` | Exception propagates | ⬜ |
| `test_python_callable_wrong_return` | Non-int return handled | ⬜ |

### Unit Tests — Key Function

| Test | Covers | Status |
|------|--------|--------|
| `test_key_function_basic` | `key=str.lower` works | ⬜ |
| `test_key_function_lambda` | `key=lambda x: -x` works | ⬜ |
| `test_key_function_type_reported` | `type == 'key_func'` | ⬜ |
| `test_key_function_exception` | Exception propagates | ⬜ |
| `test_key_extracted_once` | Key not re-extracted on compare | ⬜ |

### Unit Tests — Error Handling

| Test | Covers | Status |
|------|--------|--------|
| `test_from_cfunc_null_pointer` | NULL pointer raises ValueError | ⬜ |
| `test_from_cfunc_invalid_type` | Non-int pointer raises TypeError | ⬜ |
| `test_both_cmp_and_key_error` | Both args raises TypeError | ⬜ |
| `test_non_callable_cmp_error` | Non-callable cmp raises TypeError | ⬜ |
| `test_non_callable_key_error` | Non-callable key raises TypeError | ⬜ |
| `test_uncomparable_objects` | TypeError on non-comparable | ⬜ |

### Integration Tests — Container Usage

| Test | Covers | Dependencies | Status |
|------|--------|--------------|--------|
| `test_skiplistmap_natural` | Default ordering works | SkipListMap | ⬜ |
| `test_skiplistmap_reverse` | Reverse ordering works | SkipListMap | ⬜ |
| `test_skiplistmap_numeric` | Numeric optimization works | SkipListMap | ⬜ |
| `test_skiplistmap_key_func` | Key function works | SkipListMap | ⬜ |
| `test_skiplistmap_python_cmp` | Python callable works | SkipListMap | ⬜ |
| `test_skiplistmap_comparator_type` | `comparator_type` accurate | SkipListMap | ⬜ |
| `test_treemap_comparators` | TreeMap accepts comparators | TreeMap | ⬜ |
| `test_skiplistset_comparators` | SkipListSet accepts comparators | SkipListSet | ⬜ |

### Property-Based Tests

| Property | Generator | Invariant Checked | Status |
|----------|-----------|-------------------|--------|
| `prop_antisymmetry` | Random pairs | `cmp(a,b) == -cmp(b,a)` | ⬜ |
| `prop_transitivity` | Random triples | Transitive ordering | ⬜ |
| `prop_reflexivity` | Random values | `cmp(a,a) == 0` | ⬜ |
| `prop_consistency` | Same pair twice | Same result | ⬜ |
| `prop_natural_matches_sorted` | Random list | Sort order matches | ⬜ |
| `prop_reverse_inverts` | Random pairs | `reverse(a,b) == -natural(a,b)` | ⬜ |

### Performance Tests

| Test | Metric | Target | Status |
|------|--------|--------|--------|
| `perf_natural_comparison` | ns/compare | ~50ns | ⬜ |
| `perf_cfunc_comparison` | ns/compare | ~10ns | ⬜ |
| `perf_numeric_comparison` | ns/compare | ~15ns | ⬜ |
| `perf_string_comparison` | ns/compare | ~20ns | ⬜ |
| `perf_python_comparison` | ns/compare | ~500ns | ⬜ |
| `perf_key_function` | ns/compare | ~50ns (after extraction) | ⬜ |

### Cython Integration Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_cython_cfunc_registration` | C function from Cython works | ⬜ |
| `test_cython_nogil_comparison` | nogil comparator works | ⬜ |
| `test_cython_context_passing` | Context passed correctly | ⬜ |
| `test_cython_prevent_gc` | Context kept alive | ⬜ |

## Edge Cases

| Case | Expected Behavior | Test |
|------|-------------------|------|
| Compare object with itself | Returns 0 | `test_compare_same_object` |
| Compare None values | TypeError (not comparable) | `test_compare_none` |
| Empty string comparison | Works correctly | `test_compare_empty_strings` |
| Very large integers | No overflow | `test_compare_large_ints` |
| NaN float comparison | Consistent behavior | `test_compare_nan` |
| Unicode normalization | Not applied (raw compare) | `test_compare_unicode_forms` |

## Error Paths

| Error Condition | Expected Result | Test |
|-----------------|-----------------|------|
| NULL function pointer | `ValueError` | `test_from_cfunc_null_pointer` |
| Both cmp and key | `TypeError` | `test_both_cmp_and_key_error` |
| Non-comparable types | `TypeError` | `test_uncomparable_objects` |
| Callable returns None | `TypeError` | `test_callable_returns_none` |
| Key function raises | Exception propagates | `test_key_function_exception` |
| C function crashes | Undefined (document) | N/A |

## Memory Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_comparator_dealloc` | No memory leak on dealloc | ⬜ |
| `test_context_ref_held` | prevent_gc keeps context alive | ⬜ |
| `test_context_ref_released` | Context released on comparator dealloc | ⬜ |
| `test_callable_ref_held` | Callable kept alive | ⬜ |

## Concurrency Tests

| Test | Scenario | Threads | Status |
|------|----------|---------|--------|
| `test_concurrent_comparison` | Same comparator, multiple threads | 4 | ⬜ |
| `test_concurrent_construction` | Multiple comparators created | 4 | ⬜ |
| `test_container_concurrent` | Container with comparator under load | 8 | ⬜ |

## Coverage Gaps

| Gap | Reason | Plan |
|-----|--------|------|
| Invalid C function behavior | Cannot safely test | Document as UB |
| All Python types | Combinatorial explosion | Property tests |
| Locale-aware string compare | Not supported | Document limitation |

## Test Infrastructure

- Unit tests: pytest with fixtures for each comparator type
- Property tests: Hypothesis with custom strategies
- Performance tests: pytest-benchmark
- Memory tests: tracemalloc or valgrind
- Cython tests: Separate test module requiring Cython build
