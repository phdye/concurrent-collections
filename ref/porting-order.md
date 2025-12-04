# Actor Model — Porting Order

## Overview

This document defines the authoritative module list and porting order for the Actor Model runtime. Modules are organized into dependency tiers — lower tiers must be complete before higher tiers can begin.

---

## Tier Summary

| Tier | Category | Modules | Draft Source |
|------|----------|---------|--------------|
| 0 | Foundation | 4 | `actor-model-spec.md` §1 |
| 1 | Message Passing | 4 | `actor-model-spec.md` §2 |
| 2 | Failure Handling | 4 | `actor-model-spec.md` §3 |
| 3 | Scheduling | 4 | `actor-model-spec.md` §4 |
| 4 | Support Primitives | 5 | `actor-model-spec.md` §5 |

**Deferred:** Distribution (`actor-model-spec.md` §6)

---

## Tier 0: Foundation

No internal dependencies. Target platform provides threads, memory, synchronization.

| Module | Description | Draft Reference | Complexity |
|--------|-------------|-----------------|------------|
| `process_identity` | PID structure, uniqueness, comparison, serialization | §1.1 | Low |
| `process_state` | Process control block, flags, status, trap_exit flag | §1.3, §3.3 | Medium |
| `process_lifecycle` | spawn, init, terminate, exit reasons | §1.2, §1.4 | Medium |
| `memory_model` | Heap isolation, message copying semantics | §1.3 | High |

### Tier 0 Completion Criteria

- [ ] PID generation is unique and fast
- [ ] Process state is isolated
- [ ] spawn/terminate semantics defined and tested
- [ ] Memory isolation guarantees specified in TLA+

---

## Tier 1: Message Passing

Depends on: Tier 0

| Module | Description | Draft Reference | Complexity |
|--------|-------------|-----------------|------------|
| `mailbox` | Per-process message queue, FIFO ordering | §2.3 | Medium |
| `send` | Async dispatch, ordering guarantees, dead process handling | §2.1 | Medium |
| `receive_basic` | Blocking receive, timeout | §2.2 | Medium |
| `selective_receive` | Pattern matching, queue scanning, preservation | §2.2 | High |

### Tier 1 Completion Criteria

- [ ] FIFO ordering per sender-receiver pair proven in TLA+
- [ ] Send never blocks
- [ ] Receive blocks correctly with timeout
- [ ] Selective receive preserves non-matching messages

### Key Invariants (TLA+)

```tla
\* Messages from A to B arrive in send order
FIFO_Per_Sender ==
    \A a, b \in Processes:
        \A i, j \in SentIndices(a, b):
            i < j => ArrivesBefore(a, b, i, j)

\* Send never blocks
SendNonBlocking ==
    \A p \in Processes, m \in Messages:
        ENABLED Send(p, m)

\* Non-matching messages preserved
SelectivePreservation ==
    \A p \in Processes, pattern \in Patterns:
        LET matched == SelectiveReceive(p, pattern)
            remaining == mailbox'[p]
        IN \A m \in remaining: ~Matches(m, pattern)
```

---

## Tier 2: Failure Handling

Depends on: Tier 0, Tier 1

| Module | Description | Draft Reference | Complexity |
|--------|-------------|-----------------|------------|
| `links` | Bidirectional coupling, link/unlink operations | §3.1 | Medium |
| `monitors` | Unidirectional observation, references, demonitor | §3.2 | Medium |
| `exit_signals` | Signal types (normal, kill, other), propagation rules | §3.4 | High |
| `trap_exit` | Exit trapping, signal-to-message conversion | §3.3 | Medium |

### Tier 2 Completion Criteria

- [ ] Link symmetry proven in TLA+
- [ ] Exit propagation to linked processes correct
- [ ] Monitor DOWN messages delivered correctly
- [ ] kill signal untrappable, other signals trappable
- [ ] spawn_link atomic

### Key Invariants (TLA+)

```tla
\* Links are symmetric
LinkSymmetry ==
    \A p, q \in Processes:
        Linked(p, q) <=> Linked(q, p)

\* Exit propagation
ExitPropagation ==
    \A p \in TerminatingProcesses:
        LET reason == ExitReason(p)
        IN \A q \in LinkedTo(p):
            IF reason = normal THEN
                \* Normal exit: no propagation (unless trapping)
                TRUE
            ELSE IF Trapping(q) THEN
                \* Trapping: convert to message
                {'EXIT', p, reason} \in mailbox'[q]
            ELSE
                \* Not trapping: propagate termination
                q \in TerminatingProcesses'

\* Kill is untrappable
KillUntrappable ==
    \A p \in Processes:
        ReceivedKill(p) => p \in TerminatingProcesses'
```

---

## Tier 3: Scheduling

Depends on: Tier 0, Tier 1, Tier 2

| Module | Description | Draft Reference | Complexity |
|--------|-------------|-----------------|------------|
| `scheduler` | Run queue management, process selection | §4.3 | High |
| `preemption` | Reduction counting, yield points, time slicing | §4.1 | High |
| `priorities` | Priority levels (low/normal/high/max), queue separation | §4.2 | Medium |
| `fairness` | Starvation prevention, bounded waiting | §4.1 | Medium |

### Tier 3 Completion Criteria

- [ ] No process starvation (liveness in TLA+)
- [ ] Preemption occurs within bounded reductions
- [ ] Priority levels respected
- [ ] Multi-core utilization (if applicable)

### Key Properties (TLA+)

```tla
\* Fairness: every runnable process eventually runs
Fairness ==
    \A p \in Processes:
        Runnable(p) ~> Scheduled(p)

\* Bounded preemption
BoundedExecution ==
    \A p \in Processes:
        Running(p) => Reductions(p) <= MAX_REDUCTIONS

\* Priority ordering
PriorityRespected ==
    \A p, q \in RunnableProcesses:
        Priority(p) > Priority(q) =>
            ScheduledBefore(p, q) \/ ~Runnable(p)
```

---

## Tier 4: Support Primitives

Depends on: Tier 0, Tier 1

| Module | Description | Draft Reference | Complexity |
|--------|-------------|-----------------|------------|
| `references` | Unique token generation (make_ref) | §5.1 | Low |
| `timers` | send_after, start_timer, cancel_timer, read_timer | §5.2 | Medium |
| `registry` | Name registration, whereis, registered | §5.3 | Medium |
| `process_dictionary` | Per-process key-value store | §5.4 | Low |
| `process_info` | self, is_process_alive, process_info, processes | §5.5 | Low |

### Tier 4 Completion Criteria

- [ ] References globally unique
- [ ] Timers fire correctly after delay
- [ ] Registry operations atomic
- [ ] process_dictionary isolated per process

---

## Deferred: Distribution

Not in initial scope. To be specified after single-node implementation complete.

| Module | Description | Draft Reference |
|--------|-------------|-----------------|
| `node_identity` | Node naming, connection | §6.1 |
| `remote_spawn` | Spawn on remote node | §6.2 |
| `remote_messaging` | Transparent remote send | §6.1 |
| `node_monitors` | Node up/down detection | §6.3 |

---

## Cross-Cutting Concerns

These apply across all tiers:

| Concern | Reference | Notes |
|---------|-----------|-------|
| Performance targets | §7.1 | <1μs spawn, send, context switch |
| Reliability | §7.2 | No message loss, isolation guarantee |
| Open questions | §8 | Design decisions to resolve |

---

## Module Document Requirements

Each module directory must contain:

| File | Required | Notes |
|------|----------|-------|
| `design.md` | **Yes** | Architecture, algorithms |
| `spec.md` | **Yes** | Informal specification |
| `spec.tla+` | **Yes** | Formal specification |
| `tests.md` | **Yes** | Test coverage |
| `perf.md` | Tier 0-3 | Performance requirements |
| `beam_reference.md` | Optional | BEAM implementation notes |

---

## OTP Unblocking Milestones

| Milestone | Tiers | OTP Can Begin |
|-----------|-------|---------------|
| M1 | Tier 0 + Tier 1 | — (foundation only) |
| M2 | + Tier 2 | OTP Tier 0-2 (behaviors, supervision) |
| M3 | + Tier 3 + Tier 4 | All OTP tiers |

---

## Revision History

| Date | Author | Changes |
|------|--------|---------|
| 2025-12-03 | phdye | Initial porting order |
