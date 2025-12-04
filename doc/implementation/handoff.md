# Session Handoff

## Last Updated

2025-12-04

---

## Session Summary

Completed Tier 2 (Memory Management) design documentation:
- `mimalloc_glue` module: design.md, spec.md, tests.md
- `smr_ibr` module: design.md, spec.md, tests.md, spec.tla
- `smr_debra` module: design.md, spec.md, tests.md, spec.tla

All three Tier 2 modules now have complete design documentation including:
- Architecture and algorithm documentation
- Formal contracts and invariants
- Test coverage plans
- TLA+ formal specifications (for SMR modules)

---

## Next Priorities

1. **Begin Tier 3 design documentation**
   - `skiplist_lockfree` module docs (with TLA+ spec)
   - `skiplist_locked` module docs
   - `treiber` stack docs (with TLA+ spec)
   - Queue algorithms (scq, lcrq, wcq)
   - BST algorithms

2. **Set up build infrastructure**
   - Create pyproject.toml
   - Configure C extension build
   - Set up pytest infrastructure

3. **Begin Tier 0 implementation**
   - Start with `arch_detect` (simplest)
   - Then `config` (depends on arch_detect)
   - Then `atomics` and `backoff`

---

## Open Implementation Questions

| Question | Context | Impact |
|----------|---------|--------|
| Build system | setup.py vs pyproject.toml vs both | Affects packaging workflow |
| C extension approach | Pure C vs Cython vs pybind11 vs PyO3 | Affects code structure, build complexity |
| Test framework | pytest vs unittest vs both | Affects test organization |
| CI platform | GitHub Actions vs other | Affects workflow files |
| SMR default | IBR vs DEBRA+ | Affects default behavior |

---

## Blockers

None currently.

---

## Notes for Next Session

### Key Documents

| Document | Purpose |
|----------|---------|
| `doc/Design.v3.md` | Authoritative high-level design |
| `doc/design/design-capture.md` | Project configuration and decisions |
| `doc/design/porting-order.md` | Module list and tier definitions |
| `ref/complete-design.md` | Documentation methodology |
| `ref/design-handoff.md` | Historical handoff (updated) |

### Tier 0-2 Module Status

| Module | Design | Spec | Tests | TLA+ | Platform |
|--------|--------|------|-------|------|----------|
| arch_detect | ✅ | ✅ | ✅ | N/A | ✅ |
| atomics | ✅ | ✅ | ✅ | N/A | ✅ |
| backoff | ✅ | ✅ | ✅ | N/A | N/A |
| config | ✅ | ✅ | ✅ | N/A | N/A |
| comparator | ✅ | ✅ | ✅ | N/A | N/A |
| mimalloc_glue | ✅ | ✅ | ✅ | N/A | N/A |
| smr_ibr | ✅ | ✅ | ✅ | ✅ | N/A |
| smr_debra | ✅ | ✅ | ✅ | ✅ | N/A |

### Tier 2 Key Design Decisions

| Module | Decision | Choice |
|--------|----------|--------|
| mimalloc_glue | Allocator | mimalloc (CPython 3.13t default) |
| mimalloc_glue | Stats | Optional, disabled by default |
| smr_ibr | Limbo lists | 3 (ring buffer by epoch % 3) |
| smr_ibr | Retire threshold | 64 nodes |
| smr_debra | Neutralization signal | SIGURG |
| smr_debra | Windows fallback | IBR (no signals) |
| smr_debra | Stall threshold | 100 epochs |

### TLA+ Specifications Created

| Module | File | Key Properties Verified |
|--------|------|------------------------|
| smr_ibr | spec.tla | NoUseAfterFree, NoDoubleFree, EpochMonotonic |
| smr_debra | spec.tla | NoUseAfterFree, NeutralizationSafety, BoundedPending |

### Design Decisions Pending

From `doc/design/design-capture.md` Open Questions:
- SMR thread registration (explicit vs automatic)
- Frozen snapshot allocation (copy vs compact array)
- Queue unbounded growth (linked segments vs realloc)
- LCRQ segment size (fixed vs configurable)
- Backoff tuning (fixed vs adaptive)
