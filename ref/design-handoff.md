# Design Handoff — concurrent_collections

## Session Date

2024-12-04

## Purpose

This document captures the current state of design preparation for `concurrent_collections` to enable seamless continuation in another session.

---

## Completed Work

### 1. Design Document Review & Update

**Input**: `doc/Design.v2.md` (original design document)

**Output**: `doc/Design.v3.md` (updated with resolved decisions)

**Changes Made**:
- Version bumped to 2.0 Draft
- Added `FrozenSkipListMap`/`FrozenSkipListSet` to module structure
- Added `Comparator` class for custom ordering
- Added `recipes.BoundedSkipListMap` for bounded use case
- Added adaptive backend selection (GIL detection)
- Expanded API sections with new types and methods
- Added Section 4.2: Adaptive Backend Selection
- Added Section 4.3: Dual Implementation Strategy
- Added Section 4.7: Iterator Semantics
- Added Section 5: Custom Comparator System (with Cython examples)
- Added Section 7: Performance Characteristics (benchmarks for both GIL states)
- Added Appendix A: Resolved Design Decisions
- Removed rollout plan (all-at-once release)

### 2. Resolved Design Questions

Four open questions from v2 were resolved:

| Question | Resolution | Details |
|----------|------------|---------|
| Iterator semantics | Weakly consistent + `snapshot()` | Default iteration is weakly consistent; `snapshot()` returns `FrozenSkipListMap` for point-in-time consistency |
| Custom comparators | Natural default + Cython path | Natural ordering by default; Python callables supported; C comparators via Cython for performance; comprehensive Cython documentation with 4 examples |
| Bounded containers | Unbounded + recipes subclass | Core containers unbounded; `BoundedSkipListMap` in `concurrent_collections.recipes` |
| GIL adaptation | Detect & adapt | Runtime GIL detection; dual backends (lock-free and locked); comprehensive benchmark documentation |

### 3. Documentation Framework

**Created**: `ref/complete-design.md`

Comprehensive instructions for creating design documentation for new software projects:
- Design vs implementation separation principle
- Design capture document structure
- Module order document structure  
- Per-module documentation requirements
- Implementation tracking documents
- Templates for all document types
- Process guidelines
- Checklists and pitfall avoidance

**Key Principle Established**: 
- `doc/design/` — Reusable design documents (no status tracking)
- `doc/implementation/` — Status tracking documents

---

## Current State

### Documents Present

| Document | Location | Status |
|----------|----------|--------|
| Original design | `doc/Design.v2.md` | Complete (superseded) |
| Updated design | `doc/Design.v3.md` | Complete |
| Documentation instructions | `ref/complete-design.md` | Complete |
| This handoff | `ref/design-handoff.md` | Complete |

### Documents NOT Yet Created

The formal design document structure per `ref/complete-design.md` has not been created:

| Document | Location | Status |
|----------|----------|--------|
| Design capture | `doc/design/design-capture.md` | Not created |
| Module order | `doc/design/module-order.md` | Not created |
| Per-module specs | `doc/design/tier-N/<module>/` | Not created |
| Progress tracking | `doc/implementation/progress.md` | Not created |
| Templates | `doc/design/_templates/` | Not created |

---

## Next Steps

### Option A: Formalize Design Structure

Convert `doc/Design.v3.md` into the formal structure defined in `ref/complete-design.md`:

1. Create directory structure:
   ```
   doc/
     design/
       design-capture.md
       module-order.md
       _templates/
       tier-0/
       tier-1/
       ...
     implementation/
       progress.md
       handoff.md
   ```

2. Extract content from `Design.v3.md` into:
   - `design-capture.md` — Project configuration, scope, decisions
   - `module-order.md` — Tier definitions, module list, completion criteria
   - Per-module directories with `design.md`, `spec.md`, `tests.md`

3. Define tiers for concurrent_collections:
   - Tier 0: Foundation (SMR, atomics, platform detection)
   - Tier 1: Core structures (SkipList, BST internals)
   - Tier 2: Python bindings (SkipListMap, TreeMap, etc.)
   - Tier 3: Queue/Stack family
   - Tier 4: Utilities (Comparator, config, recipes)

### Option B: Begin Implementation Planning

If design is considered sufficient in `Design.v3.md` form:

1. Create `doc/implementation/progress.md` to track work
2. Define implementation order
3. Set up build infrastructure
4. Begin Tier 0 implementation

### Option C: Refine Design Further

Areas that could use more detail:

1. **SMR internals** — IBR/DEBRA+ detailed design
2. **C extension structure** — File organization, build system
3. **Test infrastructure** — Stress test framework, linearizability checker
4. **Benchmark suite** — Standard benchmarks, comparison methodology

---

## Context for Next Session

### Project Roots

| Path Type | Path |
|-----------|------|
| Windows | `C:\-\cygwin\root\home\phdyex\my-repos\python\concurrent-collections` |
| Cygwin | `/home/phdyex/my-repos/python/concurrent-collections` |

### Key Files to Review

1. `doc/Design.v3.md` — Current authoritative design
2. `ref/complete-design.md` — How to structure formal design docs
3. `CLAUDE.md` — Project instructions (ClaudeFlow framework)

### User Preferences

- Ask clarifying questions before giving detailed answers
- Design documents must not contain implementation status
- All-at-once release (no phased rollout)

### Technical Decisions Made

| Topic | Decision |
|-------|----------|
| Target Python | 3.13+ (free-threaded and GIL-enabled) |
| License | BSD-3-Clause |
| Primary algorithm (ordered) | Fraser's lock-free skip list |
| Secondary algorithm (ordered) | Natarajan-Mittal BST |
| Queue algorithms | SCQ (portable), LCRQ (x86-64), wCQ (wait-free) |
| Stack algorithm | Treiber with elimination |
| SMR primary | Interval-Based Reclamation (IBR) |
| SMR secondary | DEBRA+ (configurable) |
| Memory allocator | mimalloc (CPython's allocator) |
| GIL handling | Runtime detection, dual backends |
| Iterator default | Weakly consistent |
| Snapshot type | FrozenSkipListMap (immutable, hashable) |
| Comparator default | Natural ordering (`__lt__`) |
| Bounded containers | Recipes module, not core |

---

## Questions for Next Session

1. **Formalization priority**: Should we formalize the design structure before implementation, or is `Design.v3.md` sufficient to begin?

2. **Tier boundaries**: The suggested tiers above are a starting point. Should they be refined based on actual dependency analysis?

3. **Implementation language**: The design assumes C extension. Should we consider:
   - Pure C with Python C API?
   - C++ with pybind11?
   - Cython for some components?
   - Rust with PyO3?

4. **CI/CD setup**: When should build infrastructure be established relative to design completion?

---

## Files Modified This Session

| File | Action |
|------|--------|
| `doc/Design.v3.md` | Created (new version of design) |
| `ref/complete-design.md` | Created (documentation instructions) |
| `ref/design-handoff.md` | Created (this document) |
