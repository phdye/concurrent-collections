# backoff — Test Coverage

## Overview

Testing strategy focuses on correctness of exponential growth, boundary conditions, reset behavior, and platform-specific pause instruction availability. Performance testing validates that backoff improves throughput under contention.

## Test Categories

### Unit Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_init_sets_fields` | Init sets min, max, current correctly | ⬜ |
| `test_init_current_equals_min` | current starts at min | ⬜ |
| `test_backoff_doubles_current` | current doubles after backoff | ⬜ |
| `test_backoff_caps_at_max` | current never exceeds max | ⬜ |
| `test_backoff_stays_at_max` | Repeated backoff stays at max | ⬜ |
| `test_reset_restores_min` | Reset sets current to min | ⬜ |
| `test_reset_after_max` | Reset from max to min works | ⬜ |
| `test_macro_init` | CC_BACKOFF_INIT macro works | ⬜ |
| `test_pause_executes` | cc_pause doesn't crash | ⬜ |

Legend: ⬜ Not implemented, 🔶 Partial, ✅ Complete

### Boundary Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_min_equals_max` | min == max stays constant | ⬜ |
| `test_min_one` | min = 1 works correctly | ⬜ |
| `test_max_large` | Large max (2^20) handled | ⬜ |
| `test_power_of_two_max` | Power of 2 max reached exactly | ⬜ |
| `test_non_power_of_two_max` | Non-power-of-2 max capped correctly | ⬜ |

### Stress Tests

| Test | Scenario | Threads | Duration | Status |
|------|----------|---------|----------|--------|
| `stress_backoff_contention` | CAS loop with backoff | 8 | 5s | ⬜ |
| `stress_backoff_vs_no_backoff` | Compare throughput | 8 | 5s | ⬜ |

### Platform Tests

| Test | Platform | Covers | Status |
|------|----------|--------|--------|
| `test_pause_x86_64` | x86-64 | `pause` instruction used | ⬜ |
| `test_pause_arm64` | ARM64 | `yield` instruction used | ⬜ |
| `test_pause_portable` | Other | Compiles and runs | ⬜ |

## Edge Cases

| Case | Expected Behavior | Test |
|------|-------------------|------|
| min == max == 1 | Single pause, no growth | `test_min_equals_max` |
| Immediate reset | current stays at min | `test_immediate_reset` |
| Very large max | No overflow | `test_max_large` |
| Repeated reset | Idempotent | `test_repeated_reset` |

## Error Paths

| Error Condition | Expected Result | Test |
|-----------------|-----------------|------|
| min == 0 | Undefined (assert in debug) | `test_min_zero_asserts` |
| min > max | Undefined (assert in debug) | `test_min_gt_max_asserts` |
| NULL pointer | Undefined (crash) | N/A |

## Performance Tests

### Throughput Comparison

| Test | Scenario | Metric | Status |
|------|----------|--------|--------|
| `perf_backoff_helps` | High contention CAS | ops/sec improvement | ⬜ |
| `perf_backoff_neutral` | Low contention CAS | No significant overhead | ⬜ |

### Expected Results

Under high contention (8+ threads on 4 cores):
- With backoff: 2-5x throughput improvement
- Without backoff: Cache line bouncing degrades performance

Under low contention (1-2 threads):
- With backoff: < 5% overhead
- Without backoff: Baseline

## Integration Tests

| Test | Covers | Dependencies | Status |
|------|--------|--------------|--------|
| `test_skiplist_uses_backoff` | SkipList CAS loops use backoff | skiplist_lockfree | ⬜ |
| `test_treiber_uses_backoff` | Treiber stack uses backoff | treiber | ⬜ |

## Sequence Tests

| Test | Sequence | Expected current Values | Status |
|------|----------|------------------------|--------|
| `test_growth_sequence` | 5 backoffs, min=1, max=1024 | 1,2,4,8,16 | ⬜ |
| `test_growth_to_max` | 12 backoffs, min=1, max=1024 | ...,1024,1024 | ⬜ |
| `test_reset_mid_growth` | 3 backoffs, reset, 2 backoffs | 1,2,4,1,2 | ⬜ |

## Coverage Gaps

| Gap | Reason | Plan |
|-----|--------|------|
| Pause instruction timing | Hardware-dependent | Manual benchmarking |
| Power consumption | Requires specialized tools | Out of scope |

## Test Infrastructure

- Unit tests: Standard C test framework (Unity or similar)
- Platform tests: Conditional compilation or runtime detection
- Performance tests: Dedicated benchmark harness
- Debug assertions: Compile with `-DDEBUG` to enable
