---------------------------- MODULE SCQ ----------------------------
(*
 * TLA+ Specification for Scalable Circular Queue (SCQ)
 *
 * Models:
 * 1. FIFO ordering
 * 2. Lock-free progress
 * 3. Bounded capacity
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Items,          \* Set of items
    Threads,        \* Thread identifiers
    Capacity,       \* Queue capacity
    NULL

VARIABLES
    slots,          \* slots[i] = item or NULL
    slotCycle,      \* slotCycle[i] = cycle when slot was written
    head,           \* Dequeue position
    tail,           \* Enqueue position
    pc,             \* Thread program counter
    arg,            \* Thread operation argument
    result,         \* Thread operation result
    history         \* Operation history for verification

vars == <<slots, slotCycle, head, tail, pc, arg, result, history>>

-----------------------------------------------------------------------------
(* Helpers *)

Index(pos) == pos % Capacity
Cycle(pos) == pos \div Capacity

PCs == {"idle", "enqueue_reserve", "enqueue_cas", "dequeue_reserve",
        "dequeue_cas", "done"}

-----------------------------------------------------------------------------
(* Initialization *)

Init ==
    /\ slots = [i \in 0..(Capacity-1) |-> NULL]
    /\ slotCycle = [i \in 0..(Capacity-1) |-> 0]
    /\ head = 0
    /\ tail = 0
    /\ pc = [t \in Threads |-> "idle"]
    /\ arg = [t \in Threads |-> NULL]
    /\ result = [t \in Threads |-> NULL]
    /\ history = <<>>

-----------------------------------------------------------------------------
(* Enqueue operation *)

EnqueueStart(t, item) ==
    /\ pc[t] = "idle"
    /\ item \in Items
    /\ arg' = [arg EXCEPT ![t] = item]
    /\ pc' = [pc EXCEPT ![t] = "enqueue_reserve"]
    /\ UNCHANGED <<slots, slotCycle, head, tail, result, history>>

EnqueueReserve(t) ==
    /\ pc[t] = "enqueue_reserve"
    /\ LET pos == tail
           idx == Index(pos)
           cyc == Cycle(pos)
       IN /\ tail' = tail + 1
          /\ IF pos - head < Capacity
             THEN pc' = [pc EXCEPT ![t] = "enqueue_cas"]
             ELSE \* Queue full
                  /\ result' = [result EXCEPT ![t] = FALSE]
                  /\ pc' = [pc EXCEPT ![t] = "done"]
                  /\ history' = Append(history, <<"enqueue", arg[t], FALSE>>)
                  /\ UNCHANGED <<slots, slotCycle>>
    /\ UNCHANGED <<head, arg>>

EnqueueCAS(t) ==
    /\ pc[t] = "enqueue_cas"
    /\ LET pos == tail - 1  \* Our reserved position
           idx == Index(pos)
           cyc == Cycle(pos)
       IN IF slotCycle[idx] < cyc \/ slots[idx] = NULL
          THEN \* Slot available
               /\ slots' = [slots EXCEPT ![idx] = arg[t]]
               /\ slotCycle' = [slotCycle EXCEPT ![idx] = cyc]
               /\ result' = [result EXCEPT ![t] = TRUE]
               /\ history' = Append(history, <<"enqueue", arg[t], TRUE>>)
               /\ pc' = [pc EXCEPT ![t] = "done"]
          ELSE \* Retry (simplified)
               /\ pc' = [pc EXCEPT ![t] = "enqueue_reserve"]
               /\ UNCHANGED <<slots, slotCycle, result, history>>
    /\ UNCHANGED <<head, tail, arg>>

-----------------------------------------------------------------------------
(* Dequeue operation *)

DequeueStart(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "dequeue_reserve"]
    /\ UNCHANGED <<slots, slotCycle, head, tail, arg, result, history>>

DequeueReserve(t) ==
    /\ pc[t] = "dequeue_reserve"
    /\ LET pos == head
           idx == Index(pos)
       IN /\ head' = head + 1
          /\ IF pos < tail
             THEN pc' = [pc EXCEPT ![t] = "dequeue_cas"]
             ELSE \* Queue empty
                  /\ result' = [result EXCEPT ![t] = NULL]
                  /\ pc' = [pc EXCEPT ![t] = "done"]
                  /\ history' = Append(history, <<"dequeue", NULL, FALSE>>)
                  /\ UNCHANGED <<slots, slotCycle>>
    /\ UNCHANGED <<tail, arg>>

DequeueCAS(t) ==
    /\ pc[t] = "dequeue_cas"
    /\ LET pos == head - 1  \* Our reserved position
           idx == Index(pos)
           cyc == Cycle(pos)
       IN IF slots[idx] # NULL /\ slotCycle[idx] = cyc
          THEN \* Item available
               /\ result' = [result EXCEPT ![t] = slots[idx]]
               /\ slots' = [slots EXCEPT ![idx] = NULL]
               /\ history' = Append(history, <<"dequeue", slots[idx], TRUE>>)
               /\ pc' = [pc EXCEPT ![t] = "done"]
          ELSE \* Retry
               /\ pc' = [pc EXCEPT ![t] = "dequeue_reserve"]
               /\ UNCHANGED <<slots, result, history>>
    /\ UNCHANGED <<slotCycle, head, tail, arg>>

-----------------------------------------------------------------------------
(* Complete operation *)

Complete(t) ==
    /\ pc[t] = "done"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ arg' = [arg EXCEPT ![t] = NULL]
    /\ result' = [result EXCEPT ![t] = NULL]
    /\ UNCHANGED <<slots, slotCycle, head, tail, history>>

-----------------------------------------------------------------------------
(* Next state *)

Next ==
    \E t \in Threads:
        \/ \E item \in Items: EnqueueStart(t, item)
        \/ EnqueueReserve(t)
        \/ EnqueueCAS(t)
        \/ DequeueStart(t)
        \/ DequeueReserve(t)
        \/ DequeueCAS(t)
        \/ Complete(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety Properties *)

\* FIFO: Items dequeued in enqueue order
FIFO ==
    LET enqueued == SelectSeq(history, LAMBDA e: e[1] = "enqueue" /\ e[3] = TRUE)
        dequeued == SelectSeq(history, LAMBDA e: e[1] = "dequeue" /\ e[3] = TRUE)
    IN \A i, j \in 1..Len(dequeued):
        i < j =>
            \E ei, ej \in 1..Len(enqueued):
                /\ enqueued[ei][2] = dequeued[i][2]
                /\ enqueued[ej][2] = dequeued[j][2]
                /\ ei < ej

\* Bounded capacity
Bounded ==
    tail - head <= Capacity

\* No lost items
NoLoss ==
    LET enqueued == {e[2]: e \in {history[i]: i \in 1..Len(history)} :
                     e[1] = "enqueue" /\ e[3] = TRUE}
        dequeued == {e[2]: e \in {history[i]: i \in 1..Len(history)} :
                     e[1] = "dequeue" /\ e[3] = TRUE}
        inQueue == {slots[i]: i \in DOMAIN slots} \ {NULL}
    IN enqueued = dequeued \cup inQueue

-----------------------------------------------------------------------------
(* Liveness *)

\* Lock-freedom
LockFreedom ==
    []<>(\E t \in Threads: pc[t] = "done")

-----------------------------------------------------------------------------
(* Invariants *)

TypeInvariant ==
    /\ head \in Nat
    /\ tail \in Nat
    /\ head <= tail

SafetyInvariant ==
    /\ TypeInvariant
    /\ Bounded
    /\ FIFO

=============================================================================
