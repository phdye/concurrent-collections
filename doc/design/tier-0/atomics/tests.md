# atomics — Test Coverage

## Overview

Testing focuses on correctness of atomic operations across platforms and verification of memory ordering behavior under concurrency.

## Test Categories

### Unit Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_ptr_load_store` | Basic load/store round-trip | ⬜ |
| `test_ptr_exchange` | Exchange returns old value | ⬜ |
| `test_ptr_cas_success` | CAS succeeds when expected matches | ⬜ |
| `test_ptr_cas_failure` | CAS fails and updates expected | ⬜ |
| `test_size_fetch_add` | Atomic increment returns old value | ⬜ |
| `test_size_fetch_sub` | Atomic decrement returns old value | ⬜ |
| `test_u128_cas` | 128-bit CAS (x86-64 only) | ⬜ |

### Stress Tests

| Test | Scenario | Threads | Status |
|------|----------|---------|--------|
| `stress_counter` | Concurrent increments | 8 | ⬜ |
| `stress_cas_contention` | High-contention CAS loop | 8 | ⬜ |
| `stress_producer_consumer` | Single-slot handoff | 2 | ⬜ |

### Memory Ordering Tests

| Test | Verifies | Status |
|------|----------|--------|
| `test_release_acquire` | Acquire sees release writes | ⬜ |
| `test_seq_cst_total_order` | SeqCst operations totally ordered | ⬜ |
| `test_relaxed_no_ordering` | Relaxed has no ordering (negative test) | ⬜ |

### Sanitizer Tests

| Sanitizer | Test Suite | Status |
|-----------|------------|--------|
| TSAN | All stress tests | ⬜ |
| ASAN | All tests | ⬜ |

## Edge Cases

| Case | Expected Behavior | Test |
|------|-------------------|------|
| CAS on NULL expected | Works, compares NULL | `test_cas_null` |
| Store NULL | Works | `test_store_null` |
| Weak CAS spurious failure | May happen, no crash | `test_cas_weak_spurious` |
| Max size_t increment | Wraps to 0 | `test_overflow` |

## Platform-Specific Tests

| Platform | Tests | Notes |
|----------|-------|-------|
| x86-64 | 128-bit CAS tests | Requires CMPXCHG16B |
| MSVC | All tests via intrinsics | Different codegen |

## Coverage Gaps

| Gap | Reason | Plan |
|-----|--------|------|
| consume ordering | Rarely used, hard to test | Document as "best-effort" |
| ARM64 LSE vs LL/SC | Need both hardware types | Test on multiple ARM systems |
