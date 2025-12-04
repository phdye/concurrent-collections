# mimalloc_glue — Test Coverage

## Overview

Testing strategy validates allocation correctness, cross-thread safety, alignment guarantees, and statistics accuracy.

## Test Categories

### Unit Tests — Basic Allocation

| Test | Covers | Status |
|------|--------|--------|
| `test_alloc_returns_non_null` | `cc_alloc(64)` returns valid pointer | ⬜ |
| `test_alloc_zero_size_returns_null` | `cc_alloc(0)` returns NULL | ⬜ |
| `test_alloc_large_size` | `cc_alloc(1MB)` works | ⬜ |
| `test_alloc_very_large_fails_gracefully` | `cc_alloc(SIZE_MAX)` returns NULL | ⬜ |
| `test_calloc_returns_zeroed` | `cc_calloc` memory is zeroed | ⬜ |
| `test_calloc_overflow_returns_null` | `cc_calloc(SIZE_MAX, 2)` returns NULL | ⬜ |

Legend: ⬜ Not implemented, 🔶 Partial, ✅ Complete

### Unit Tests — Alignment

| Test | Covers | Status |
|------|--------|--------|
| `test_alloc_aligned_8` | 8-byte alignment | ⬜ |
| `test_alloc_aligned_16` | 16-byte alignment | ⬜ |
| `test_alloc_aligned_64` | 64-byte (cache line) alignment | ⬜ |
| `test_alloc_aligned_4096` | Page alignment | ⬜ |
| `test_alloc_node_cache_aligned` | `cc_alloc_node` returns cache-aligned | ⬜ |
| `test_alloc_alignment_is_power_of_2` | Non-power-of-2 behavior documented | ⬜ |

### Unit Tests — Free

| Test | Covers | Status |
|------|--------|--------|
| `test_free_null_is_safe` | `cc_free(NULL, 0)` is no-op | ⬜ |
| `test_free_returns_memory` | Freed memory can be reallocated | ⬜ |
| `test_free_unsized_works` | `cc_free_unsized` works | ⬜ |
| `test_free_different_sizes` | Free various allocation sizes | ⬜ |

### Unit Tests — Statistics

| Test | Covers | Status |
|------|--------|--------|
| `test_stats_disabled_by_default` | No overhead when disabled | ⬜ |
| `test_stats_enable_disable` | Enable/disable toggle works | ⬜ |
| `test_stats_alloc_count_increments` | Count increases on alloc | ⬜ |
| `test_stats_free_count_increments` | Count increases on free | ⬜ |
| `test_stats_bytes_tracked` | Byte tracking accurate | ⬜ |
| `test_stats_current_allocated` | Current = alloc - free | ⬜ |
| `test_stats_reset` | Reset zeros all counters | ⬜ |
| `test_stats_snapshot_consistency` | Snapshot is point-in-time | ⬜ |

### Concurrency Tests — Same Thread

| Test | Covers | Threads | Status |
|------|--------|---------|--------|
| `test_single_thread_many_allocs` | 10K allocations | 1 | ⬜ |
| `test_single_thread_alloc_free_cycle` | Alloc-free-alloc pattern | 1 | ⬜ |
| `test_single_thread_mixed_sizes` | Various sizes interleaved | 1 | ⬜ |

### Concurrency Tests — Cross-Thread Free

| Test | Covers | Threads | Status |
|------|--------|---------|--------|
| `test_cross_thread_free_basic` | Alloc T1, free T2 | 2 | ⬜ |
| `test_cross_thread_free_many` | Many cross-thread frees | 4 | ⬜ |
| `test_cross_thread_free_random` | Random alloc/free distribution | 8 | ⬜ |
| `test_cross_thread_free_stress` | High volume cross-thread | 16 | ⬜ |

### Concurrency Tests — Multi-Thread Allocation

| Test | Covers | Threads | Status |
|------|--------|---------|--------|
| `test_parallel_alloc` | Many threads allocating | 8 | ⬜ |
| `test_parallel_alloc_free` | Many threads alloc + free | 8 | ⬜ |
| `test_parallel_stats` | Stats accuracy under concurrency | 8 | ⬜ |
| `test_no_contention_bottleneck` | Thread-local heaps work | 16 | ⬜ |

### Integration Tests — SMR Pattern

| Test | Covers | Status |
|------|--------|--------|
| `test_smr_retire_pattern` | Alloc → use → retire → free | ⬜ |
| `test_smr_delayed_free` | Significant delay between retire and free | ⬜ |
| `test_smr_batch_free` | Free many nodes at once | ⬜ |
| `test_smr_cross_thread_retire` | Thread A allocs, B retires, C frees | ⬜ |

### Memory Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_no_leak_simple` | Single alloc/free doesn't leak | ⬜ |
| `test_no_leak_stress` | Many alloc/free cycles don't leak | ⬜ |
| `test_asan_no_use_after_free` | ASAN detects UAF | ⬜ |
| `test_asan_no_double_free` | ASAN detects double free | ⬜ |
| `test_msan_no_uninitialized` | MSAN validates calloc zeroes | ⬜ |

### Performance Tests

| Test | Metric | Target | Status |
|------|--------|--------|--------|
| `perf_alloc_latency` | ns/alloc | < 50ns | ⬜ |
| `perf_free_latency` | ns/free | < 50ns | ⬜ |
| `perf_cross_thread_free_latency` | ns/free | < 200ns | ⬜ |
| `perf_aligned_alloc_latency` | ns/alloc | < 100ns | ⬜ |
| `perf_throughput_single_thread` | allocs/sec | > 10M | ⬜ |
| `perf_throughput_multi_thread` | allocs/sec | > 50M (8 threads) | ⬜ |

## Edge Cases

| Case | Expected Behavior | Test |
|------|-------------------|------|
| Allocate 1 byte | Works, returns aligned | `test_alloc_one_byte` |
| Allocate SIZE_MAX | Returns NULL | `test_alloc_max_size` |
| Free NULL | No-op | `test_free_null` |
| Alignment non-power-of-2 | Undefined (document) | N/A |
| Stats overflow | Wraps (uint64_t) | `test_stats_overflow` |

## Error Paths

| Error Condition | Expected Result | Test |
|-----------------|-----------------|------|
| Out of memory | Returns NULL | `test_oom_handling` |
| Zero size | Returns NULL | `test_zero_size` |
| Invalid alignment | Undefined | Documented |
| Double free | UB (ASAN catches) | `test_asan_double_free` |

## Platform Tests

| Platform | Required Tests | Status |
|----------|----------------|--------|
| Linux x86-64 | All | ⬜ |
| Linux ARM64 | All | ⬜ |
| macOS x86-64 | All | ⬜ |
| macOS ARM64 | All | ⬜ |
| Windows x86-64 | All | ⬜ |

## Test Infrastructure

- **Unit Tests**: pytest with C extension
- **Concurrency Tests**: threading module, barrier synchronization
- **Memory Tests**: ASAN, MSAN, Valgrind
- **Performance Tests**: pytest-benchmark, custom timing

## Coverage Gaps

| Gap | Reason | Plan |
|-----|--------|------|
| Non-power-of-2 alignment | Undefined behavior | Document only |
| Thread cancellation | Not supported | Document limitation |
| Signal handler allocation | Not safe | Document limitation |

## Test Data Generators

```python
# Allocation sizes to test
SIZES = [1, 8, 16, 64, 128, 256, 1024, 4096, 65536, 1048576]

# Alignment values to test
ALIGNMENTS = [8, 16, 32, 64, 128, 256, 4096]

# Thread counts to test
THREAD_COUNTS = [1, 2, 4, 8, 16, 32]
```
