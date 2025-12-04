# arch_detect — Test Coverage

## Overview

Testing strategy focuses on verifying correct detection across platforms and graceful handling of edge cases. Platform-specific tests run on CI runners for each target.

## Test Categories

### Unit Tests

| Test | Covers | Status |
|------|--------|--------|
| `test_arch_enum_values` | Enum values are distinct and expected | ⬜ |
| `test_init_idempotent` | Multiple init calls are safe | ⬜ |
| `test_arch_name_not_null` | `cc_get_arch_name()` returns valid string | ⬜ |
| `test_features_not_null` | `cc_get_cpu_features()` returns valid pointer | ⬜ |
| `test_cache_line_reasonable` | Cache line size is 32, 64, or 128 | ⬜ |

Legend: ⬜ Not implemented, 🔶 Partial, ✅ Complete

### Platform-Specific Tests

| Test | Platform | Covers | Status |
|------|----------|--------|--------|
| `test_x86_64_detected` | Linux/macOS/Windows x86-64 | Arch is `ARCH_X86_64` | ⬜ |
| `test_arm64_detected` | Linux/macOS ARM64 | Arch is `ARCH_ARM64` | ⬜ |
| `test_cmpxchg16b_modern_x86` | x86-64 (Core i-series, Ryzen) | Feature detected true | ⬜ |
| `test_lse_apple_silicon` | macOS ARM64 | LSE detected true | ⬜ |
| `test_lse_graviton` | Linux ARM64 (Graviton) | LSE detected true | ⬜ |

### Integration Tests

| Test | Covers | Dependencies | Status |
|------|--------|--------------|--------|
| `test_python_config_arch` | Python API exposes correct arch | config module | ⬜ |
| `test_python_config_features` | Python API exposes feature dict | config module | ⬜ |

### Stress Tests

None required — this module has no concurrency.

### Property-Based Tests

| Property | Generator | Invariant Checked | Status |
|----------|-----------|-------------------|--------|
| `prop_init_always_succeeds` | Random call count | No exceptions | ⬜ |
| `prop_queries_consistent` | Random query order | Same results each time | ⬜ |

## Edge Cases

| Case | Expected Behavior | Test |
|------|-------------------|------|
| Very old x86-64 CPU without CMPXCHG16B | `cmpxchg16b = false` | `test_old_x86_fallback` |
| ARM64 without LSE (pre-v8.1) | `lse = false` | `test_old_arm_fallback` |
| Unknown architecture | `ARCH_UNKNOWN`, conservative features | `test_unknown_arch` |
| Init called from multiple threads | No crash, consistent results | `test_concurrent_init` |
| `/proc/cpuinfo` missing (ARM Linux) | Fallback detection or defaults | `test_no_proc_cpuinfo` |

## Error Paths

| Error Condition | Expected Result | Test |
|-----------------|-----------------|------|
| CPUID fails | Use defaults | `test_cpuid_fallback` |
| File read fails | Use defaults | `test_file_fallback` |

## Platform Matrix

| Platform | Runner | Specific Tests |
|----------|--------|----------------|
| Linux x86-64 | ubuntu-latest | `test_x86_64_detected`, `test_cmpxchg16b_*` |
| Linux ARM64 | ubuntu-24.04-arm | `test_arm64_detected`, `test_lse_*` |
| macOS x86-64 | macos-13 | `test_x86_64_detected`, `test_cmpxchg16b_*` |
| macOS ARM64 | macos-14 | `test_arm64_detected`, `test_lse_apple_silicon` |
| Windows x86-64 | windows-latest | `test_x86_64_detected`, `test_cmpxchg16b_*` |

## Test Infrastructure

- CPUID mocking not required (test on real hardware via CI matrix)
- For `/proc/cpuinfo` testing on ARM, may need container with modified `/proc`

## Coverage Gaps

| Gap | Reason | Plan |
|-----|--------|------|
| RISC-V testing | No CI runners available | Add when GitHub provides RISC-V runners |
| Very old x86 CPUs | Hardware not available | Rely on CPUID documentation |
| ARMv8.0 without LSE | Hardware rare | Document as untested, use conservative defaults |
