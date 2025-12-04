# Design Capture — Actor Model Runtime

## Purpose

This document provides continuity for the Actor Model design capture project. The goal is to create comprehensive documentation with formal specifications for an Actor Model runtime that can support Erlang/OTP semantics, organized by dependency tier.

---

## Project Configuration

| Field | Value |
|-------|-------|
| Project Name | Actor Model Runtime Specification |
| Reference Implementation | BEAM (Erlang Runtime) |
| Design Docs Root | `phdye/actor-model/design/` |
| Authoritative Tier List | `phdye/actor-model/porting-order.md` |
| Templates Directory | `phdye/actor-model/design/_templates/` |

### Scope

| Category | In Scope | Notes |
|----------|----------|-------|
| Process primitives | ✅ | Creation, identity, isolation, termination |
| Message passing | ✅ | Async send, selective receive, FIFO ordering |
| Failure handling | ✅ | Links, monitors, exit signals, trapping |
| Scheduling | ✅ | Preemption, fairness, priorities |
| Support primitives | ✅ | References, timers, registry, process dictionary |
| Distribution | ⏸️ | Deferred; single-node first |
| BEAM-specific internals | ❌ | Implementation details, not semantics |

Legend: ✅ In scope, ⏸️ Deferred, ❌ Excluded

### Formal Specification Method

| Primary | Secondary | Notes |
|---------|-----------|-------|
| TLA+ | Alloy | TLA+ for concurrency semantics; Alloy for structural invariants |

**Rationale:** Actor model primitives are inherently concurrent. TLA+ excels at modeling message ordering, failure propagation, and safety/liveness properties.

### Reference Materials

| Source | Purpose |
|--------|---------|
| `erts/emulator/beam/` | BEAM implementation reference |
| `erts/preloaded/src/erlang.erl` | Erlang BIF definitions |
| Joe Armstrong's Thesis | Actor model semantics |
| Erlang Reference Manual | Process/message semantics |

### Related Documents

| Document | Purpose |
|----------|---------|
| `phdye/actor-model-spec.md` | **Draft** — to be reorganized into tier structure |
| `phdye/otp-functionality.md` | Context: what OTP needs from Actor Model |
| `phdye/actor-model/progress-tracking.md` | Tier completion status and history |

### Dependent Projects

| Project | Location | Dependency |
|---------|----------|------------|
| **OTP Port** | `phdye/design-capture.md` | Requires Actor Model completion |

---

## Tier Overview

| Tier | Category | Description |
|------|----------|-------------|
| 0 | Foundation | Process identity, basic state, memory model |
| 1 | Message Passing | Send, receive, mailbox, selective receive |
| 2 | Failure Handling | Links, monitors, exit signals, trapping |
| 3 | Scheduling | Preemption, fairness, priorities, reductions |
| 4 | Support Primitives | References, timers, registry, process dictionary |

### Tier Dependencies

```
Tier 0: Foundation          ← Process identity, state, isolation
           │
           ▼
Tier 1: Message Passing     ← Send, receive, mailbox, selective receive
           │
           ▼
Tier 2: Failure Handling    ← Links, monitors, exit signals
           │
           ▼
Tier 3: Scheduling          ← Preemption, fairness, priorities
           │
           ▼
Tier 4: Support Primitives  ← References, timers, registry
           │
           ▼
[OTP Project]               ← DEPENDENT PROJECT
```

---

## Module Breakdown by Tier

### Tier 0: Foundation

| Module | Description | Complexity |
|--------|-------------|------------|
| process_identity | PID structure, uniqueness, addressing | Low |
| process_state | Process control block, flags, status | Medium |
| process_lifecycle | Spawn, init, terminate | Medium |
| memory_model | Isolation, heap per process | High |

### Tier 1: Message Passing

| Module | Description | Complexity |
|--------|-------------|------------|
| mailbox | Queue structure, storage | Medium |
| send | Async dispatch, ordering guarantees | Medium |
| receive_basic | Blocking receive, timeout | Medium |
| selective_receive | Pattern matching, message filtering | High |

### Tier 2: Failure Handling

| Module | Description | Complexity |
|--------|-------------|------------|
| links | Bidirectional failure coupling | Medium |
| monitors | Unidirectional observation | Medium |
| exit_signals | Signal types, propagation | High |
| trap_exit | Exit trapping, signal conversion | Medium |

### Tier 3: Scheduling

| Module | Description | Complexity |
|--------|-------------|------------|
| scheduler | Run queue, process selection | High |
| preemption | Reduction counting, yielding | High |
| priorities | Priority levels, queue management | Medium |
| fairness | Starvation prevention | Medium |

### Tier 4: Support Primitives

| Module | Description | Complexity |
|--------|-------------|------------|
| references | Unique token generation | Low |
| timers | send_after, start_timer, cancel | Medium |
| registry | Name registration, lookup | Medium |
| process_dictionary | Per-process key-value store | Low |

---

## Open Design Questions

| Question | Options | Impact | Status |
|----------|---------|--------|--------|
| Process implementation | Green threads vs OS threads vs hybrid | Scalability, complexity | Open |
| Message copying | Full copy vs shared immutables vs COW | Isolation, performance | Open |
| Mailbox structure | Lock-free queue vs mutex-protected | Concurrent send perf | Open |
| Scheduler architecture | M:N threading, work stealing, cooperative | Fairness, preemption | Open |
| GC strategy | Per-process, generational, ref-counting | Pause behavior | Open |
| Selective receive impl | Scan mailbox vs index by pattern | Receive performance | Open |

---

## Module Completion Requirements

### Required Documents Per Module

| File | Purpose | Required |
|------|---------|----------|
| `design.md` | Architecture, algorithms, data structures | **MANDATORY** |
| `spec.md` | Informal specification, contracts, invariants | **MANDATORY** |
| `spec.tla+` | Formal TLA+ specification | **MANDATORY** |
| `tests.md` | Test coverage mapping | **MANDATORY** |

### Conditional Documents

| File | When Required |
|------|---------------|
| `perf.md` | All Tier 0-3 modules (performance critical) |
| `platform.md` | Platform-specific implementations |
| `beam_reference.md` | Document BEAM implementation details |

---

## Formal Specification Guidance

### TLA+ Required For

All Actor Model modules require TLA+ specifications:

| Module Category | Key Properties to Model |
|-----------------|------------------------|
| Message Passing | FIFO ordering, no loss, eventual delivery |
| Failure Handling | Signal propagation, link symmetry, monitor semantics |
| Scheduling | Fairness, no starvation, preemption |
| Process Lifecycle | State transitions, termination semantics |

### TLA+ Patterns for Actor Model

```tla
\* Core state
VARIABLES
    processes,    \* Set of live PIDs
    mailbox,      \* [PID -> Seq(Message)]
    links,        \* Set of {PID, PID} pairs
    monitors      \* [Reference -> {observer: PID, target: PID}]

\* FIFO per sender (critical invariant)
FIFO_Ordering ==
    \A sender, receiver \in processes:
        \A i, j \in 1..Len(sent[sender][receiver]):
            i < j => DeliveredBefore(i, j)

\* Link symmetry
LinkSymmetry ==
    \A p, q \in processes:
        {p, q} \in links <=> {q, p} \in links

\* Exit signal propagation
ExitPropagation ==
    \A p \in dying_processes:
        \A q \in processes:
            {p, q} \in links =>
                (trapping[q] => ExitMsgInMailbox(q, p))
                /\ (~trapping[q] => q \in dying_processes')
```

---

## File Structure

```
phdye/
  actor-model-spec.md         # Draft material (to be reorganized)
  
  actor-model/
    design-capture.md         # THIS DOCUMENT
    porting-order.md          # Tier/module list
    
    design/
      _templates/
      tier-0/
        README.md
        process_identity/
        process_state/
        process_lifecycle/
        memory_model/
      tier-1/
        README.md
        mailbox/
        send/
        receive_basic/
        selective_receive/
      tier-2/
        README.md
        links/
        monitors/
        exit_signals/
        trap_exit/
      tier-3/
        README.md
        scheduler/
        preemption/
        priorities/
        fairness/
      tier-4/
        README.md
        references/
        timers/
        registry/
        process_dictionary/
```

---

## Semantic Requirements for OTP Compatibility

The Actor Model must provide these guarantees for OTP to function:

| Requirement | Specification | OTP Usage |
|-------------|---------------|-----------|
| Async send | Send never blocks sender | gen_server cast |
| Selective receive | Match patterns against mailbox | gen_server call |
| FIFO per sender | Messages from A to B arrive in order | Protocol correctness |
| Link bidirectionality | If A linked to B, B linked to A | Supervision |
| Monitor unidirectionality | Observer notified, target unaware | gen_server call |
| Exit signal propagation | Linked processes receive exit | Supervision trees |
| Trap exit conversion | Exit signals become messages | Supervisors |
| Unique references | make_ref() globally unique | Call correlation |
| Timer delivery | Messages delivered after delay | Timeouts |
| Registry atomicity | Register/unregister atomic | Named processes |

---

## Session Handoff Checklist

- [ ] All modules worked on have ALL MANDATORY files
- [ ] TLA+ specifications parse and type-check
- [ ] Safety/liveness properties defined
- [ ] Tier completion table updated
- [ ] Open design questions updated
- [ ] Next priority identified
- [ ] OTP project notified if milestone reached

---

## Milestones for OTP Unblocking

OTP can begin work when these Actor Model milestones are complete:

| Milestone | Tiers Required | OTP Tier Unblocked |
|-----------|----------------|-------------------|
| M1: Basic processes | Tier 0, Tier 1 (partial) | None (foundation) |
| M2: Full messaging | Tier 1 complete | OTP Tier 0 |
| M3: Failure handling | Tier 2 complete | OTP Tier 1-2 |
| M4: Full runtime | Tier 3-4 complete | All OTP tiers |

