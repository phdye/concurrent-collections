# Tier 0: Platform & Utilities

## Overview

Tier 0 provides the foundational abstractions that all higher tiers depend on. These modules have no internal dependencies—they rely only on Rust's standard library and target platform capabilities.

**Implementation Language:** Rust (via PyO3 for Python bindings)

## Modules

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `arch_detect` | CPU architecture detection via `cfg(target_arch)`, runtime feature detection | Low | ⬜ |
| `atomics` | Atomic operations via `std::sync::atomic`, memory orderings | Medium | ⬜ |
| `backoff` | Exponential backoff, `std::hint::spin_loop` | Low | ⬜ |
| `config` | Runtime configuration, GIL detection, backend selection | Medium | ⬜ |

## Dependencies

```
Rust std / target platform
       │
       ▼
┌──────────────────────────────────────────────┐
│                   Tier 0                      │
│  ┌────────────┐ ┌────────────┐ ┌──────────┐  │
│  │arch_detect │ │  atomics   │ │ backoff  │  │
│  └────────────┘ └────────────┘ └──────────┘  │
│                 ┌────────────┐                │
│                 │   config   │                │
│                 └────────────┘                │
└──────────────────────────────────────────────┘
       │
       ▼
    Tier 1+
```

## Completion Criteria

- [ ] All modules have design.md, spec.md, tests.md
- [ ] `arch_detect` correctly identifies x86-64, aarch64, other via `cfg(target_arch)`
- [ ] `arch_detect` runtime detection for CMPXCHG16B (x86-64), LSE (aarch64)
- [ ] `atomics` provides `AtomicPtr`, `AtomicUsize` with memory ordering control
- [ ] `atomics` compiles on Linux, macOS, Windows
- [ ] `backoff` provides tunable exponential backoff
- [ ] `backoff` uses `std::hint::spin_loop()` for optimal pause
- [ ] `config` detects Python GIL state at runtime via PyO3
- [ ] `config` supports environment variable overrides via `std::env`
- [ ] `cargo test` passes on all target platforms
- [ ] `cargo clippy` clean

## Platform Requirements

| Platform | Rust Target | Notes |
|----------|-------------|-------|
| Linux x86-64 | x86_64-unknown-linux-gnu | Full feature support |
| Linux ARM64 | aarch64-unknown-linux-gnu | LSE atomics on ARMv8.1+ |
| macOS x86-64 | x86_64-apple-darwin | Full feature support |
| macOS ARM64 | aarch64-apple-darwin | Apple Silicon |
| Windows x86-64 | x86_64-pc-windows-msvc | Full feature support |

## Key Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Atomic abstraction | `std::sync::atomic` primary | Rust's built-in atomics are portable and correct |
| Feature detection | Compile-time `cfg()` + runtime `is_x86_feature_detected!` | Best of both worlds |
| GIL detection | PyO3 `Python::with_gil()` + `sys._is_gil_enabled()` | Official Python 3.13 API |
| Config storage | `once_cell::sync::Lazy` for global, thread-local for overrides | Thread-safe initialization |

## Rust Crate Dependencies

| Crate | Purpose | Version |
|-------|---------|---------|
| `pyo3` | Python bindings | 0.20+ |
| `once_cell` | Lazy static initialization | 1.18+ |

## Example Rust Code

```rust
// arch_detect example
#[cfg(target_arch = "x86_64")]
pub fn has_cmpxchg16b() -> bool {
    #[cfg(target_feature = "cmpxchg16b")]
    { true }
    #[cfg(not(target_feature = "cmpxchg16b"))]
    { std::arch::is_x86_feature_detected!("cmpxchg16b") }
}

// atomics example
use std::sync::atomic::{AtomicPtr, Ordering};

pub struct AtomicBox<T> {
    ptr: AtomicPtr<T>,
}

impl<T> AtomicBox<T> {
    pub fn compare_exchange(
        &self,
        current: *mut T,
        new: *mut T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<*mut T, *mut T> {
        self.ptr.compare_exchange(current, new, success, failure)
    }
}

// backoff example
pub struct Backoff {
    step: u32,
    max_step: u32,
}

impl Backoff {
    pub fn spin(&mut self) {
        for _ in 0..(1 << self.step.min(self.max_step)) {
            std::hint::spin_loop();
        }
        self.step += 1;
    }
}
```
