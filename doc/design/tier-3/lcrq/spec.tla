---------------------------- MODULE LCRQ ----------------------------
(*
 * TLA+ Specification for LCRQ (Linked Concurrent Ring Queue)
 *
 * Models the essential aspects:
 * 1. FIFO ordering
 * 2. Linked ring segments
 * 3. Lock-free progress
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Items,
    Threads,
    RingSize,
    NULL

VARIABLES
    rings,          \* Set of ring segments
    headRing,       \* Current head ring
    tailRing,       \* Current tail ring
    ringHead,       \* ringHead[r] = dequeue position in ring r
    ringTail,       \* ringTail[r] = enqueue position in ring r
    ringNext,       \* ringNext[r] = next ring or NULL
    slots,          \* slots[r][i] = item or NULL
    pc,
    arg,
    result,
    history

vars == <<rings, headRing, tailRing, ringHead, ringTail, ringNext,
          slots, pc, arg, result, history>>

-----------------------------------------------------------------------------
Init ==
    /\ rings = {"ring0"}
    /\ headRing = "ring0"
    /\ tailRing = "ring0"
    /\ ringHead = [r \in {"ring0"} |-> 0]
    /\ ringTail = [r \in {"ring0"} |-> 0]
    /\ ringNext = [r \in {"ring0"} |-> NULL]
    /\ slots = [r \in {"ring0"} |-> [i \in 0..(RingSize-1) |-> NULL]]
    /\ pc = [t \in Threads |-> "idle"]
    /\ arg = [t \in Threads |-> NULL]
    /\ result = [t \in Threads |-> NULL]
    /\ history = <<>>

-----------------------------------------------------------------------------
(* Enqueue to tail ring or allocate new ring *)

Enqueue(t, item) ==
    /\ pc[t] = "idle"
    /\ item \in Items
    /\ LET r == tailRing
           pos == ringTail[r]
           idx == pos % RingSize
       IN IF pos - ringHead[r] < RingSize
          THEN \* Slot available
               /\ slots' = [slots EXCEPT ![r][idx] = item]
               /\ ringTail' = [ringTail EXCEPT ![r] = pos + 1]
               /\ history' = Append(history, <<"enqueue", item>>)
               /\ UNCHANGED <<rings, headRing, tailRing, ringHead, ringNext>>
          ELSE \* Ring full, allocate new
               LET newRing == "ring" \o ToString(Cardinality(rings))
               IN /\ rings' = rings \cup {newRing}
                  /\ ringHead' = ringHead @@ (newRing :> 0)
                  /\ ringTail' = ringTail @@ (newRing :> 1)
                  /\ ringNext' = [ringNext EXCEPT ![r] = newRing] @@
                                 (newRing :> NULL)
                  /\ slots' = slots @@ (newRing :>
                              [i \in 0..(RingSize-1) |->
                               IF i = 0 THEN item ELSE NULL])
                  /\ tailRing' = newRing
                  /\ history' = Append(history, <<"enqueue", item>>)
                  /\ UNCHANGED <<headRing>>
    /\ UNCHANGED <<pc, arg, result>>

-----------------------------------------------------------------------------
(* Dequeue from head ring or advance to next *)

Dequeue(t) ==
    /\ pc[t] = "idle"
    /\ LET r == headRing
           pos == ringHead[r]
           idx == pos % RingSize
       IN IF pos < ringTail[r] /\ slots[r][idx] # NULL
          THEN \* Item available
               /\ result' = [result EXCEPT ![t] = slots[r][idx]]
               /\ slots' = [slots EXCEPT ![r][idx] = NULL]
               /\ ringHead' = [ringHead EXCEPT ![r] = pos + 1]
               /\ history' = Append(history, <<"dequeue", slots[r][idx]>>)
               /\ UNCHANGED <<rings, headRing, tailRing, ringTail, ringNext>>
          ELSE IF ringNext[r] # NULL
               THEN \* Advance to next ring
                    /\ headRing' = ringNext[r]
                    /\ UNCHANGED <<rings, tailRing, ringHead, ringTail,
                                   ringNext, slots, result, history>>
               ELSE \* Empty
                    /\ result' = [result EXCEPT ![t] = NULL]
                    /\ UNCHANGED <<rings, headRing, tailRing, ringHead,
                                   ringTail, ringNext, slots, history>>
    /\ UNCHANGED <<pc, arg>>

-----------------------------------------------------------------------------
Next ==
    \E t \in Threads:
        \/ \E item \in Items: Enqueue(t, item)
        \/ Dequeue(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

\* FIFO ordering
FIFO ==
    LET ops == history
        enqueued == SelectSeq(ops, LAMBDA e: e[1] = "enqueue")
        dequeued == SelectSeq(ops, LAMBDA e: e[1] = "dequeue")
    IN Len(dequeued) <= Len(enqueued) /\
       \A i \in 1..Len(dequeued): dequeued[i][2] = enqueued[i][2]

\* Rings are properly linked
RingsLinked ==
    \A r \in rings:
        ringNext[r] = NULL \/ ringNext[r] \in rings

TypeInvariant ==
    /\ headRing \in rings
    /\ tailRing \in rings

=============================================================================
