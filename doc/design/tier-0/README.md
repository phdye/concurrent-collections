# Tier 0: Platform & Utilities

## Overview

Tier 0 provides the foundational abstractions that all higher tiers depend on. These modules have no internal dependencies—they rely only on the C compiler, standard library, and target platform.

## Modules

| Module | Description | Complexity | Status |
|--------|-------------|------------|--------|
| `arch_detect` | CPU architecture detection, feature flags | Low | ⬜ |
| `atomics` | Atomic operations, memory barriers | Medium | ⬜ |
| `backoff` | Exponential backoff, spin strategies | Low | ⬜ |
| `config` | Runtime configuration, GIL detection | Medium | ⬜ |

## Dependencies

```
Platform/Compiler
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
- [ ] `arch_detect` correctly identifies x86-64, ARM64, other
- [ ] `arch_detect` detects CMPXCHG16B (x86-64), LSE (ARM64)
- [ ] `atomics` provides load/store/CAS/FAA with memory order control
- [ ] `atomics` compiles on Linux, macOS, Windows
- [ ] `backoff` provides tunable exponential backoff
- [ ] `backoff` uses platform-optimal pause instruction
- [ ] `config` detects GIL state at runtime
- [ ] `config` supports environment variable overrides
- [ ] Unit tests pass on all target platforms

## Platform Requirements

| Platform | Compiler | Notes |
|----------|----------|-------|
| Linux | GCC 10+, Clang 12+ | C11 atomics required |
| macOS | Apple Clang 13+ | C11 atomics required |
| Windows | MSVC 2019+, Clang | Interlocked intrinsics |

## Key Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Atomic abstraction | C11 atomics primary, platform intrinsics fallback | Portability with escape hatch |
| GIL detection | `sys._is_gil_enabled()` with fallback | Official Python 3.13 API |
| Config storage | Thread-local + global | Per-thread override capability |
