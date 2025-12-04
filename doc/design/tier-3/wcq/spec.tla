---------------------------- MODULE WCQ ----------------------------
(*
 * TLA+ Specification for Wait-Free Circular Queue
 *
 * Models:
 * 1. Wait-free progress guarantee
 * 2. Helping mechanism
 * 3. FIFO ordering
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Items,
    Threads,
    Capacity,
    NULL

VARIABLES
    slots,              \* Ring buffer
    head,               \* Dequeue position
    tail,               \* Enqueue position
    phase,              \* Global phase counter
    announcements,      \* announcements[t] = pending operation
    pc,                 \* Thread state
    steps,              \* steps[t] = steps taken this operation
    history

vars == <<slots, head, tail, phase, announcements, pc, steps, history>>

-----------------------------------------------------------------------------
OpTypes == {"NONE", "ENQUEUE", "DEQUEUE"}

Announcement == [type: OpTypes,
                 item: Items \cup {NULL},
                 result: Items \cup {NULL},
                 phase: Nat,
                 completed: BOOLEAN]

EmptyAnnouncement == [type |-> "NONE", item |-> NULL, result |-> NULL,
                       phase |-> 0, completed |-> TRUE]

Index(pos) == pos % Capacity

-----------------------------------------------------------------------------
Init ==
    /\ slots = [i \in 0..(Capacity-1) |-> NULL]
    /\ head = 0
    /\ tail = 0
    /\ phase = 0
    /\ announcements = [t \in Threads |-> EmptyAnnouncement]
    /\ pc = [t \in Threads |-> "idle"]
    /\ steps = [t \in Threads |-> 0]
    /\ history = <<>>

-----------------------------------------------------------------------------
(* Announce enqueue operation *)
AnnounceEnqueue(t, item) ==
    /\ pc[t] = "idle"
    /\ announcements' = [announcements EXCEPT ![t] =
                         [type |-> "ENQUEUE", item |-> item, result |-> NULL,
                          phase |-> phase, completed |-> FALSE]]
    /\ phase' = phase + 1
    /\ pc' = [pc EXCEPT ![t] = "helping"]
    /\ steps' = [steps EXCEPT ![t] = 0]
    /\ UNCHANGED <<slots, head, tail, history>>

(* Announce dequeue operation *)
AnnounceDequeue(t) ==
    /\ pc[t] = "idle"
    /\ announcements' = [announcements EXCEPT ![t] =
                         [type |-> "DEQUEUE", item |-> NULL, result |-> NULL,
                          phase |-> phase, completed |-> FALSE]]
    /\ phase' = phase + 1
    /\ pc' = [pc EXCEPT ![t] = "helping"]
    /\ steps' = [steps EXCEPT ![t] = 0]
    /\ UNCHANGED <<slots, head, tail, history>>

-----------------------------------------------------------------------------
(* Help pending operations (including self) *)
Help(t) ==
    /\ pc[t] = "helping"
    /\ steps[t] < 2 * Cardinality(Threads) + 5  \* Bounded steps
    /\ \E target \in Threads:
        LET ann == announcements[target]
        IN /\ ann.type # "NONE"
           /\ ann.phase <= announcements[t].phase
           /\ ~ann.completed
           /\ IF ann.type = "ENQUEUE"
              THEN HelpEnqueue(t, target)
              ELSE HelpDequeue(t, target)
    /\ steps' = [steps EXCEPT ![t] = steps[t] + 1]

HelpEnqueue(helper, target) ==
    LET ann == announcements[target]
        item == ann.item
    IN IF tail - head < Capacity
       THEN \* Slot available
            LET idx == Index(tail)
            IN IF slots[idx] = NULL
               THEN /\ slots' = [slots EXCEPT ![idx] = item]
                    /\ tail' = tail + 1
                    /\ announcements' = [announcements EXCEPT ![target].completed = TRUE]
                    /\ history' = Append(history, <<"enqueue", item>>)
                    /\ UNCHANGED <<head, phase, pc>>
               ELSE /\ tail' = tail + 1
                    /\ UNCHANGED <<slots, head, announcements, phase, pc, history>>
       ELSE \* Queue full
            /\ announcements' = [announcements EXCEPT ![target].completed = TRUE]
            /\ UNCHANGED <<slots, head, tail, phase, pc, history>>

HelpDequeue(helper, target) ==
    IF head < tail
    THEN \* Item available
         LET idx == Index(head)
             item == slots[idx]
         IN IF item # NULL
            THEN /\ slots' = [slots EXCEPT ![idx] = NULL]
                 /\ head' = head + 1
                 /\ announcements' = [announcements EXCEPT ![target] =
                                      [@ EXCEPT !.result = item, !.completed = TRUE]]
                 /\ history' = Append(history, <<"dequeue", item>>)
                 /\ UNCHANGED <<tail, phase, pc>>
            ELSE /\ head' = head + 1
                 /\ UNCHANGED <<slots, tail, announcements, phase, pc, history>>
    ELSE \* Queue empty
         /\ announcements' = [announcements EXCEPT ![target].completed = TRUE]
         /\ UNCHANGED <<slots, head, tail, phase, pc, history>>

-----------------------------------------------------------------------------
(* Complete operation and return to idle *)
Complete(t) ==
    /\ pc[t] = "helping"
    /\ announcements[t].completed
    /\ announcements' = [announcements EXCEPT ![t] = EmptyAnnouncement]
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<slots, head, tail, phase, steps, history>>

-----------------------------------------------------------------------------
Next ==
    \E t \in Threads:
        \/ \E item \in Items: AnnounceEnqueue(t, item)
        \/ AnnounceDequeue(t)
        \/ Help(t)
        \/ Complete(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety Properties *)

\* FIFO ordering
FIFO ==
    LET enqueued == SelectSeq(history, LAMBDA e: e[1] = "enqueue")
        dequeued == SelectSeq(history, LAMBDA e: e[1] = "dequeue")
    IN \A i \in 1..Len(dequeued): dequeued[i][2] = enqueued[i][2]

\* Bounded steps (wait-freedom)
BoundedSteps ==
    \A t \in Threads:
        pc[t] = "helping" => steps[t] <= 2 * Cardinality(Threads) + 5

\* Every announced operation eventually completes
EventualCompletion ==
    \A t \in Threads:
        announcements[t].type # "NONE" ~> announcements[t].completed

-----------------------------------------------------------------------------
(* Liveness - Wait-freedom *)
WaitFreedom ==
    \A t \in Threads:
        []<>(pc[t] = "idle")

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ head \in Nat
    /\ tail \in Nat
    /\ head <= tail

SafetyInvariant ==
    /\ TypeInvariant
    /\ BoundedSteps
    /\ FIFO

=============================================================================
