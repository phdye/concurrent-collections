# Complete Design Documentation — Instructions

## Purpose

This document provides instructions for creating comprehensive technical design documentation for new software projects. The methodology produces documentation suitable for:

- Guiding implementation from scratch
- Enabling future porting to other languages/platforms
- Supporting formal verification
- Facilitating team handoffs and onboarding
- Establishing test coverage requirements

The approach is language, platform, and OS agnostic.

---

## Design vs Implementation Separation

**Critical Principle**: Design documents are reusable blueprints. They must not contain implementation status, progress tracking, or completion checkboxes.

| Location | Contents | Status Tracking |
|----------|----------|-----------------|
| `doc/design/` | Architecture, specifications, requirements | **NO** |
| `doc/implementation/` | Progress, status, completion tracking | **YES** |

**Rationale**:
- Design documents can be reused for multiple implementations (different languages, platforms)
- Status tracking pollutes version control history of stable design docs
- Separating concerns enables parallel implementations from same design
- Clean designs serve as reference documentation after implementation

---

## Document Set Overview

A complete project consists of design documents (reusable) and implementation documents (status tracking):

### Design Documents (`doc/design/`)

| Document | Purpose |
|----------|---------|
| `design-capture.md` | Project configuration, scope, decisions, structure |
| `module-order.md` | Module inventory, dependency tiers, requirements |
| `<tier>/<module>/` | Per-module specifications and documentation |

### Implementation Documents (`doc/implementation/`)

| Document | Purpose |
|----------|---------|
| `progress.md` | Overall implementation status and tracking |
| `status/<module>.md` | Per-module implementation status (optional) |
| `decisions.md` | Implementation-specific decisions (not design decisions) |
| `handoff.md` | Session handoff notes and next priorities |

---

## Part 1: Design Capture Document

The design capture document is the project's technical home base. It provides context, tracks design decisions, and defines the documentation structure.

**Location**: `doc/design/design-capture.md`

### 1.1 Required Sections

#### Project Configuration

Define the project identity and documentation locations:

```markdown
## Project Configuration

| Field | Value |
|-------|-------|
| Project Name | [Human-readable project name] |
| Design Docs Root | `doc/design/` |
| Implementation Docs Root | `doc/implementation/` |
| Module Order | `doc/design/module-order.md` |
| Templates Directory | `doc/design/_templates/` |
```

#### Scope Definition

Explicitly state what is and is not in scope:

```markdown
### Scope

| Category | Status | Notes |
|----------|--------|-------|
| [Feature/Component A] | ✅ | [Why included, constraints] |
| [Feature/Component B] | ✅ | [Why included, constraints] |
| [Feature/Component C] | ⏸️ | [Why deferred, trigger for inclusion] |
| [Feature/Component D] | ❌ | [Why excluded] |

Legend: ✅ In scope, ⏸️ Deferred, ❌ Excluded
```

**Guidance:**
- Be explicit about boundaries — ambiguity causes scope creep
- Deferred items should have clear criteria for future inclusion
- Excluded items should explain *why* to prevent repeated discussions

#### Formal Specification Method

If using formal methods, declare the approach:

```markdown
### Formal Specification Method

| Primary | Secondary | Notes |
|---------|-----------|-------|
| [Method] | [Method] | [Rationale for selection] |
```

**Common choices:**
- **TLA+**: Concurrency, distributed systems, state machines
- **Alloy**: Structural constraints, relational models
- **Z/VDM**: Sequential algorithms, data refinement
- **Coq/Lean**: Proofs, type-driven development
- **Property-based testing**: Lightweight alternative to formal proofs

**Guidance:**
- Match the method to the problem domain
- Not all projects need formal methods — be pragmatic
- If not using formal methods, document the testing strategy instead

#### Reference Materials

List authoritative sources:

```markdown
### Reference Materials

| Source | Purpose |
|--------|---------|
| [Paper/Book/Code] | [What it provides] |
| [Standard/RFC] | [What it defines] |
```

**Guidance:**
- Include both conceptual references (papers, books) and concrete references (code, standards)
- For new designs without existing references, cite the problem domain literature

#### Related Documents

Link to companion documentation:

```markdown
### Related Documents

| Document | Purpose |
|----------|---------|
| [Document path] | [Relationship to this project] |
```

#### Dependent Projects

If other projects depend on this one:

```markdown
### Dependent Projects

| Project | Location | Dependency |
|---------|----------|------------|
| [Project name] | [Path] | [What they need from us] |
```

### 1.2 Tier Overview

Provide a high-level view of the dependency structure:

```markdown
## Tier Overview

| Tier | Category | Description |
|------|----------|-------------|
| 0 | [Name] | [One-line description] |
| 1 | [Name] | [One-line description] |
| ... | ... | ... |
```

Include a visual dependency diagram:

```markdown
### Tier Dependencies

```
Tier 0: [Name]          ← [Key concepts]
           │
           ▼
Tier 1: [Name]          ← [Key concepts]
           │
           ▼
...
```
```

**Guidance on tier design:**
- Tier 0 should have no internal dependencies (only external/platform)
- Each tier depends only on lower tiers
- Aim for 4-6 tiers maximum
- Tiers should represent meaningful capability milestones

### 1.3 Module Breakdown by Tier

List all modules with descriptions and complexity estimates:

```markdown
## Module Breakdown by Tier

### Tier 0: [Category Name]

| Module | Description | Complexity |
|--------|-------------|------------|
| [module_name] | [What it does] | Low/Medium/High |
```

**Complexity guidance:**
- **Low**: Well-understood, straightforward implementation
- **Medium**: Some design decisions, moderate algorithm complexity
- **High**: Novel algorithms, significant concurrency, complex invariants

**Note**: No status columns — status tracking belongs in `doc/implementation/progress.md`

### 1.4 Open Design Questions

Track unresolved design decisions:

```markdown
## Open Design Questions

| Question | Options | Impact |
|----------|---------|--------|
| [Decision needed] | [Option A, Option B, ...] | [What it affects] |
```

**Guidance:**
- Capture questions as they arise — don't let them get lost
- Document the options considered, not just the question
- When resolved, move to a "Resolved Design Decisions" section (don't delete)

### 1.5 Resolved Design Decisions

Document decisions made:

```markdown
## Resolved Design Decisions

| Decision | Choice | Rationale | Alternatives Considered |
|----------|--------|-----------|-------------------------|
| [Topic] | [What we chose] | [Why] | [What we didn't choose] |
```

### 1.6 Module Completion Requirements

Define what "complete" means for each module (as requirements, not tracked status):

```markdown
## Module Completion Requirements

### Required Documents Per Module

| File | Purpose | Required |
|------|---------|----------|
| `design.md` | Architecture, algorithms, data structures | **MANDATORY** |
| `spec.md` | Contracts, invariants, behavior | **MANDATORY** |
| `tests.md` | Test coverage requirements | **MANDATORY** |

### Conditional Documents

| File | When Required |
|------|---------------|
| [filename] | [Condition for requirement] |
```

**Common conditional documents:**
- `spec.tla+` / `spec.alloy` — When formal verification is used
- `perf.md` — For performance-critical modules
- `platform.md` — For platform-specific implementations
- `security.md` — For security-sensitive modules
- `migration.md` — For modules with compatibility concerns

### 1.7 File Structure

Document the expected directory layout:

```markdown
## File Structure

```
doc/
  design/                     # Reusable design documents (no status)
    design-capture.md         # This document
    module-order.md           # Module list and tiers
    _templates/               # Document templates
    tier-0/
      README.md               # Tier overview
      module_a/
        design.md
        spec.md
        tests.md
      module_b/
        ...
    tier-1/
      ...
  
  implementation/             # Status tracking documents
    progress.md               # Overall status
    handoff.md                # Session handoff notes
    decisions.md              # Implementation decisions
    status/                   # Per-module status (optional)
      module_a.md
```
```

---

## Part 2: Module Order Document

The module order document is the authoritative module inventory and implementation sequence.

**Location**: `doc/design/module-order.md`

### 2.1 Required Sections

#### Overview

Summarize the tiers:

```markdown
## Overview

This document defines the authoritative module list and implementation order. 
Modules are organized into dependency tiers — lower tiers must be complete 
before higher tiers can begin.

## Tier Summary

| Tier | Category | Modules | Description |
|------|----------|---------|-------------|
| 0 | [Name] | [Count] | [Brief description] |
| 1 | [Name] | [Count] | [Brief description] |
```

#### Per-Tier Module Lists

For each tier, list modules with requirements (not status):

```markdown
## Tier N: [Category Name]

Dependencies: [List of required lower tiers]

| Module | Description | Complexity |
|--------|-------------|------------|
| `module_name` | [What it does] | Low/Med/High |

### Tier N Completion Criteria

Requirements for tier completion (verified during implementation):

- [Specific measurable criterion]
- [Specific measurable criterion]
- [Tests passing / properties verified]
```

**Guidance on completion criteria:**
- State as requirements, not checkboxes
- Must be objectively verifiable
- Include both functional and non-functional requirements
- Reference formal properties if using formal methods

#### Key Invariants (Optional)

For complex tiers, document critical invariants:

```markdown
### Key Invariants

[Formal or semi-formal statements of properties that must hold]
```

#### Cross-Cutting Concerns

Document concerns that span multiple tiers:

```markdown
## Cross-Cutting Concerns

| Concern | Affected Tiers | Notes |
|---------|----------------|-------|
| [Concern name] | [Tier list] | [How to address] |
```

**Common cross-cutting concerns:**
- Error handling strategy
- Logging/observability
- Performance targets
- Security requirements
- Platform abstraction

#### Milestones

Define meaningful checkpoints:

```markdown
## Milestones

| Milestone | Tiers Required | Capability Achieved |
|-----------|----------------|---------------------|
| M1 | Tier 0 | [What becomes possible] |
| M2 | Tier 0-1 | [What becomes possible] |
```

---

## Part 3: Per-Module Documentation

Each module requires its own documentation set within its directory.

**Location**: `doc/design/<tier>/<module>/`

### 3.1 design.md (Mandatory)

The architecture and implementation guide:

```markdown
# [Module Name] — Design

## Overview

[2-3 sentence description of what this module does and why it exists]

## Dependencies

| Dependency | Purpose |
|------------|---------|
| [Module/Library] | [What we use it for] |

## Architecture

[Diagrams and prose describing the structure]

### Data Structures

[Key data structures with field descriptions]

### Algorithms

[Key algorithms with complexity analysis]

### Concurrency Model

[Thread safety, synchronization approach — if applicable]

## API Surface

[Public interface summary — detailed docs may be separate]

## Design Decisions

| Decision | Choice | Rationale | Alternatives Considered |
|----------|--------|-----------|-------------------------|
| [Topic] | [What we chose] | [Why] | [What we didn't choose] |

## Open Questions

[Module-specific unresolved design issues]
```

### 3.2 spec.md (Mandatory)

Behavioral specification and contracts:

```markdown
# [Module Name] — Specification

## Overview

[What behavior this module guarantees]

## Preconditions

[What must be true before using this module]

## Postconditions

[What will be true after operations complete]

## Invariants

[Properties that always hold]

## Error Conditions

| Condition | Behavior |
|-----------|----------|
| [What can go wrong] | [How module responds] |

## Contracts by Operation

### [Operation Name]

**Signature:** [Type signature or prototype]

**Preconditions:**
- [Condition 1]
- [Condition 2]

**Postconditions:**
- [Condition 1]
- [Condition 2]

**Errors:**
- [Error condition] → [Response]

## Thread Safety

[Concurrency guarantees — if applicable]

## Performance Bounds

[Complexity guarantees — if applicable]
```

### 3.3 tests.md (Mandatory)

Test coverage requirements (not status):

```markdown
# [Module Name] — Test Requirements

## Overview

[Testing strategy for this module]

## Required Test Categories

### Unit Tests

| Test | Covers |
|------|--------|
| [test_name] | [What it must verify] |

### Integration Tests

| Test | Covers |
|------|--------|
| [test_name] | [What it must verify] |

### Property Tests

| Property | Generator |
|----------|-----------|
| [property_name] | [Input generation approach] |

### Required Edge Cases

| Case | Expected Behavior |
|------|-------------------|
| [Edge case] | [What should happen] |

## Coverage Requirements

[Minimum coverage thresholds or specific coverage rules]
```

### 3.4 Conditional Documents

#### spec.tla+ / spec.alloy (When using formal methods)

Formal specification in the chosen notation. Include:
- State variables
- Initial conditions
- Transitions/operations
- Safety properties
- Liveness properties (if applicable)

#### perf.md (Performance-critical modules)

```markdown
# [Module Name] — Performance Requirements

## Targets

| Operation | Target | Measurement Method |
|-----------|--------|-------------------|
| [op_name] | [metric] | [How to measure] |

## Benchmark Requirements

[Required benchmarks and baseline expectations]

## Optimization Constraints

[What optimizations are permitted/required]
```

#### platform.md (Platform-specific implementations)

```markdown
# [Module Name] — Platform Specifics

## Platform Matrix

| Platform | Implementation Approach | Constraints |
|----------|------------------------|-------------|
| [Platform] | [Approach] | [Constraints] |

## Platform Detection

[How to detect platform at build/runtime]

## Abstraction Layer

[How platform differences are hidden from callers]
```

---

## Part 4: Implementation Documents

Implementation documents track progress and are separate from reusable design.

**Location**: `doc/implementation/`

### 4.1 progress.md

Track overall implementation status:

```markdown
# Implementation Progress

## Overview

| Tier | Status | Notes |
|------|--------|-------|
| 0 | ⬜/🔶/✅ | [Current state] |
| 1 | ⬜/🔶/✅ | [Current state] |

Legend: ⬜ Not started, 🔶 In progress, ✅ Complete

## Module Status

### Tier 0

| Module | Design | Implementation | Tests | Status |
|--------|--------|----------------|-------|--------|
| [name] | ✅ | 🔶 | ⬜ | [Notes] |

## Completion Criteria Verification

### Tier 0

- [ ] [Criterion from design doc]
- [ ] [Criterion from design doc]

## Current Focus

[What is actively being worked on]

## Blockers

[What is blocking progress]
```

### 4.2 handoff.md

Session handoff notes:

```markdown
# Session Handoff

## Last Updated

[Date/time]

## Session Summary

[What was accomplished]

## Next Priorities

1. [Priority 1]
2. [Priority 2]

## Open Implementation Questions

[Questions that arose during implementation — not design questions]

## Blockers

[What is blocking progress]

## Notes for Next Session

[Anything the next person/session needs to know]
```

### 4.3 decisions.md

Implementation-specific decisions (not design decisions):

```markdown
# Implementation Decisions

These are implementation choices, not design choices. Design decisions 
belong in `doc/design/design-capture.md`.

| Decision | Choice | Rationale | Date |
|----------|--------|-----------|------|
| [Topic] | [What we chose] | [Why] | [When] |
```

---

## Part 5: Process Guidelines

### 5.1 Starting a New Project

1. **Create `doc/design/design-capture.md`** with project configuration and scope
2. **Draft tier structure** — identify natural dependency layers
3. **Create `doc/design/module-order.md`** with module list
4. **Identify open design questions** — capture uncertainties early
5. **Create directory structure** and templates
6. **Create `doc/implementation/progress.md`** — empty, ready for tracking
7. **Begin Tier 0 design** — design documents before implementation

### 5.2 Module Development Workflow

For each module:

1. **Create design.md** — architecture before implementation
2. **Create spec.md** — define behavior before coding
3. **Create tests.md** — define test requirements
4. **Update `doc/implementation/progress.md`** — mark design complete
5. **Implement** — following the design
6. **Write tests** — achieving required coverage
7. **Update `doc/implementation/progress.md`** — mark implementation complete

### 5.3 Tier Advancement

Before starting a new tier:

1. All lower tier modules must be complete (per `progress.md`)
2. Completion criteria must be verified
3. Cross-cutting concerns for that tier must be addressed
4. Dependent projects should be notified of milestone

### 5.4 Design Evolution

Designs evolve. When changes are needed:

1. **Update design documents** — design.md, spec.md as needed
2. **Update tests.md** — add/modify test requirements
3. **Note in design-capture.md** — update decisions/open questions
4. **Consider ripple effects** — check dependent modules/projects

Implementation documents track that changes occurred; design documents reflect current design.

### 5.5 Handoff Protocol

When transferring work to another person or session:

1. Update `doc/implementation/progress.md` with current status
2. Update `doc/implementation/handoff.md` with:
   - What was accomplished
   - Next priorities
   - Any blockers
   - Notes for next session
3. Ensure design documents are current (not ahead of or behind implementation)

---

## Part 6: Templates

### 6.1 design-capture.md Template

```markdown
# Design Capture — [Project Name]

## Purpose

[1-2 paragraphs describing the project and documentation goals]

---

## Project Configuration

| Field | Value |
|-------|-------|
| Project Name | |
| Design Docs Root | `doc/design/` |
| Implementation Docs Root | `doc/implementation/` |
| Module Order | `doc/design/module-order.md` |
| Templates Directory | `doc/design/_templates/` |

### Scope

| Category | Status | Notes |
|----------|--------|-------|
| | | |

Legend: ✅ In scope, ⏸️ Deferred, ❌ Excluded

### Formal Specification Method

| Primary | Secondary | Notes |
|---------|-----------|-------|
| | | |

### Reference Materials

| Source | Purpose |
|--------|---------|
| | |

### Related Documents

| Document | Purpose |
|----------|---------|
| | |

### Dependent Projects

| Project | Location | Dependency |
|---------|----------|------------|
| | | |

---

## Tier Overview

| Tier | Category | Description |
|------|----------|-------------|
| 0 | | |
| 1 | | |

### Tier Dependencies

```
[ASCII diagram]
```

---

## Module Breakdown by Tier

### Tier 0: [Name]

| Module | Description | Complexity |
|--------|-------------|------------|
| | | |

[Repeat for each tier]

---

## Open Design Questions

| Question | Options | Impact |
|----------|---------|--------|
| | | |

---

## Resolved Design Decisions

| Decision | Choice | Rationale | Alternatives |
|----------|--------|-----------|--------------|
| | | | |

---

## Module Completion Requirements

### Required Documents Per Module

| File | Purpose | Required |
|------|---------|----------|
| `design.md` | Architecture, algorithms, data structures | **MANDATORY** |
| `spec.md` | Contracts, invariants, behavior | **MANDATORY** |
| `tests.md` | Test coverage requirements | **MANDATORY** |

### Conditional Documents

| File | When Required |
|------|---------------|
| | |

---

## File Structure

```
[Directory tree]
```

---

## Notes

[Design-relevant notes only]
```

### 6.2 module-order.md Template

```markdown
# [Project Name] — Module Order

## Overview

[Brief description of what this document tracks]

## Tier Summary

| Tier | Category | Modules | Description |
|------|----------|---------|-------------|
| | | | |

---

## Tier 0: [Name]

Dependencies: None (foundation)

| Module | Description | Complexity |
|--------|-------------|------------|
| | | |

### Tier 0 Completion Criteria

- [Criterion]
- [Criterion]

[Repeat for each tier]

---

## Cross-Cutting Concerns

| Concern | Affected Tiers | Notes |
|---------|----------------|-------|
| | | |

---

## Milestones

| Milestone | Tiers Required | Capability Achieved |
|-----------|----------------|---------------------|
| | | |

---

## Revision History

| Date | Author | Changes |
|------|--------|---------|
| | | Initial version |
```

### 6.3 progress.md Template

```markdown
# Implementation Progress

## Last Updated

[Date]

## Overview

| Tier | Status | Notes |
|------|--------|-------|
| 0 | ⬜ | |
| 1 | ⬜ | |

Legend: ⬜ Not started, 🔶 In progress, ✅ Complete

## Module Status

### Tier 0

| Module | Design | Implementation | Tests | Notes |
|--------|--------|----------------|-------|-------|
| | ⬜ | ⬜ | ⬜ | |

## Completion Criteria Verification

### Tier 0

- [ ] [Criterion from module-order.md]

## Current Focus

[Active work]

## Blockers

[Impediments]
```

### 6.4 handoff.md Template

```markdown
# Session Handoff

## Last Updated

[Date/time]

## Session Summary

[What was accomplished]

## Next Priorities

1. 
2. 

## Open Implementation Questions

[Non-design questions]

## Blockers

[Impediments]

## Notes for Next Session

[Context for next person/session]
```

### 6.5 Module design.md Template

```markdown
# [Module Name] — Design

## Overview

[Brief description]

## Dependencies

| Dependency | Purpose |
|------------|---------|
| | |

## Architecture

[Structure description]

### Data Structures

[Key structures]

### Algorithms

[Key algorithms]

## API Surface

[Public interface]

## Design Decisions

| Decision | Choice | Rationale | Alternatives |
|----------|--------|-----------|--------------|
| | | | |

## Open Questions

[Unresolved design issues]
```

### 6.6 Module spec.md Template

```markdown
# [Module Name] — Specification

## Overview

[Behavioral summary]

## Invariants

[Always-true properties]

## Contracts by Operation

### [Operation]

**Preconditions:**
- 

**Postconditions:**
- 

**Errors:**
- 

## Thread Safety

[Concurrency guarantees]
```

### 6.7 Module tests.md Template

```markdown
# [Module Name] — Test Requirements

## Required Tests

### Unit Tests

| Test | Covers |
|------|--------|
| | |

### Edge Cases

| Case | Expected Behavior |
|------|-------------------|
| | |

## Coverage Requirements

[Minimum thresholds or rules]
```

---

## Appendix A: Checklist for Complete Documentation

Use this checklist to verify documentation completeness:

### Design Documents (`doc/design/`)

- [ ] design-capture.md exists and is current
- [ ] module-order.md exists and is current
- [ ] All tiers defined with clear boundaries
- [ ] All modules listed with complexity estimates
- [ ] Open design questions tracked
- [ ] Resolved decisions documented
- [ ] Scope explicitly defined
- [ ] File structure documented and followed
- [ ] **No status tracking in design documents**

### Per Tier

- [ ] README.md exists with tier overview
- [ ] Completion criteria defined (as requirements)
- [ ] All modules have directories

### Per Module

- [ ] design.md exists (mandatory)
- [ ] spec.md exists (mandatory)
- [ ] tests.md exists (mandatory)
- [ ] Conditional documents present where required
- [ ] **No status tracking in module documents**

### Implementation Documents (`doc/implementation/`)

- [ ] progress.md exists with current status
- [ ] handoff.md updated after each session
- [ ] All status tracking is here, not in design docs

---

## Appendix B: Common Pitfalls

| Pitfall | Symptom | Prevention |
|---------|---------|------------|
| Status in design docs | Checkboxes in design files | Enforce separation, review PRs |
| Scope creep | Tiers keep growing | Define scope explicitly, review additions |
| Documentation drift | Docs don't match implementation | Update docs as part of implementation |
| Orphan modules | Modules without clear tier | Require tier assignment at creation |
| Circular dependencies | Tiers depend on each other | Review dependencies before adding modules |
| Missing test requirements | Coverage gaps discovered late | Require tests.md before implementation |
| Stale open questions | Questions never resolved | Review during each session |
| Implicit decisions | Team disagrees on approach | Document decisions explicitly |

---

## Appendix C: Adapting for Different Project Types

### Libraries/Frameworks

- Tiers often map to abstraction layers
- API surface documentation is critical
- Include compatibility/migration concerns

### Applications

- Tiers may map to features or subsystems
- Include deployment/configuration documentation
- Consider operational concerns (monitoring, debugging)

### Distributed Systems

- Strongly recommend formal methods (TLA+)
- Include failure mode analysis per module
- Document consistency/ordering guarantees

### Performance-Critical Systems

- Require perf.md for all modules
- Include benchmark requirements in completion criteria
- Document complexity bounds in specs

### Security-Critical Systems

- Require security.md for sensitive modules
- Include threat model documentation
- Document trust boundaries explicitly

---

## Appendix D: Quick Reference — What Goes Where

| Content Type | Location | Example |
|--------------|----------|---------|
| Module architecture | `doc/design/<tier>/<module>/design.md` | Data structures, algorithms |
| Behavioral contracts | `doc/design/<tier>/<module>/spec.md` | Pre/postconditions, invariants |
| Test requirements | `doc/design/<tier>/<module>/tests.md` | Required test cases |
| Project scope | `doc/design/design-capture.md` | In/out/deferred features |
| Design decisions | `doc/design/design-capture.md` | Choices with rationale |
| Module list | `doc/design/module-order.md` | Tiers, dependencies |
| Completion criteria | `doc/design/module-order.md` | Requirements per tier |
| **Implementation status** | `doc/implementation/progress.md` | ✅/🔶/⬜ tracking |
| **Session notes** | `doc/implementation/handoff.md` | Current focus, blockers |
| **Implementation decisions** | `doc/implementation/decisions.md` | Build choices, tooling |
