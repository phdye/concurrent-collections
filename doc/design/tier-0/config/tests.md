# config — Test Coverage

## Overview

Testing strategy focuses on GIL detection accuracy, backend selection logic, environment variable handling, and configuration stability. Tests must run on both GIL-enabled and free-threaded Python builds.

## Test Categories

### Unit Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_gil_detection_accurate` | GIL state matches actual runtime | ⬜ |
| `test_backend_auto_selection` | Auto selects based on GIL state | ⬜ |
| `test_backend_force_lock_free` | Force lock-free works | ⬜ |
| `test_backend_force_locked` | Force locked works | ⬜ |
| `test_queue_backend_auto` | Auto selects SCQ or LCRQ | ⬜ |
| `test_queue_backend_scq_always_available` | SCQ available on all platforms | ⬜ |
| `test_queue_backend_lcrq_x86_only` | LCRQ only on x86-64 | ⬜ |
| `test_arch_detection` | Correct architecture reported | ⬜ |
| `test_feature_detection_cmpxchg16b` | CMPXCHG16B detected on x86-64 | ⬜ |
| `test_feature_detection_lse` | LSE detected on ARM64 | ⬜ |
| `test_smr_scheme_default` | Default is IBR | ⬜ |
| `test_smr_scheme_configurable` | Can switch to DEBRA | ⬜ |
| `test_retire_threshold_configurable` | Threshold can be changed | ⬜ |
| `test_statistics_disabled_default` | Stats disabled by default | ⬜ |
| `test_statistics_enableable` | Stats can be enabled | ⬜ |

Legend: ⬜ Not implemented, 🔶 Partial, ✅ Complete

### Environment Variable Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_env_force_backend` | `CONCURRENT_COLLECTIONS_FORCE_BACKEND` | ⬜ |
| `test_env_queue_backend` | `CONCURRENT_COLLECTIONS_QUEUE_BACKEND` | ⬜ |
| `test_env_smr_scheme` | `CONCURRENT_COLLECTIONS_SMR_SCHEME` | ⬜ |
| `test_env_retire_threshold` | `CONCURRENT_COLLECTIONS_RETIRE_THRESHOLD` | ⬜ |
| `test_env_enable_stats` | `CONCURRENT_COLLECTIONS_ENABLE_STATS` | ⬜ |
| `test_env_invalid_ignored` | Invalid env values ignored gracefully | ⬜ |
| `test_env_precedence` | Env overrides programmatic defaults | ⬜ |

### Integration Tests

| Test | Covers | Dependencies | Status |
|------|--------|--------------|--------|
| `test_container_uses_active_backend` | Containers respect config | SkipListMap | ⬜ |
| `test_queue_uses_active_queue_backend` | Queues respect config | LockFreeQueue | ⬜ |
| `test_smr_uses_config_scheme` | SMR uses configured scheme | smr_ibr, smr_debra | ⬜ |

### Property-Based Tests

| Property | Generator | Invariant Checked | Status |
|----------|-----------|-------------------|--------|
| `prop_gil_detection_stable` | Multiple calls | Same result every time | ⬜ |
| `prop_backend_consistent` | Random config changes | active_backend always valid | ⬜ |

## Edge Cases

| Case | Expected Behavior | Test |
|------|-------------------|------|
| Module imported twice | Same config instance | `test_singleton_config` |
| Config changed mid-operation | Existing containers unaffected | `test_config_change_isolation` |
| LCRQ requested on ARM64 | RuntimeError | `test_lcrq_unavailable_error` |
| Invalid force_backend value | ValueError | `test_invalid_backend_error` |
| Empty environment variable | Treated as unset | `test_empty_env_ignored` |

## Error Paths

| Error Condition | Expected Result | Test |
|-----------------|-----------------|------|
| Invalid backend string | `ValueError` | `test_invalid_backend_error` |
| Invalid queue backend | `ValueError` | `test_invalid_queue_backend_error` |
| LCRQ on non-x86 | `RuntimeError` | `test_lcrq_unavailable_error` |
| Negative retire threshold | `ValueError` | `test_invalid_retire_threshold` |

## Platform-Specific Tests

| Platform | Tests | Notes |
|----------|-------|-------|
| Linux x86-64 | CMPXCHG16B detection, LCRQ availability | Full feature set |
| Linux ARM64 | LSE detection, LCRQ unavailable | No double-width CAS |
| macOS x86-64 | Same as Linux x86-64 | |
| macOS ARM64 | Same as Linux ARM64 | Apple Silicon |
| Windows x86-64 | CMPXCHG16B, LCRQ | MSVC intrinsics |

## GIL-Specific Tests

| Test | GIL Enabled | GIL Disabled | Status |
|------|-------------|--------------|--------|
| `test_gil_state_reported` | False | True | ⬜ |
| `test_default_backend_locked` | ✓ | | ⬜ |
| `test_default_backend_lock_free` | | ✓ | ⬜ |

## Coverage Gaps

| Gap | Reason | Plan |
|-----|--------|------|
| Signal handling in DEBRA | Complex to test | Manual verification |
| Hot config reload | Not supported | N/A |

## Test Infrastructure

- Tests must run on both Python 3.13 and 3.13t
- Platform detection tests need CI on multiple platforms
- Environment variable tests need subprocess isolation
- GIL-specific tests need both Python builds in CI
