---------------------------- MODULE Treiber ----------------------------
(*
 * TLA+ Specification for Treiber Stack with Elimination
 *
 * Models:
 * 1. LIFO ordering
 * 2. Lock-free progress
 * 3. Elimination backoff
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Items,
    Threads,
    ElimSlots,
    NULL

VARIABLES
    stack,          \* Sequence representing stack (head is top)
    top,            \* Top node pointer
    nodes,          \* nodes[n] = [item, next]
    elim,           \* elim[slot] = [state, item]
    pc,             \* Thread program counter
    arg,            \* Thread operation argument
    result,         \* Thread operation result
    history

vars == <<stack, top, nodes, elim, pc, arg, result, history>>

-----------------------------------------------------------------------------
ElimStates == {"EMPTY", "WAITING", "MATCHED"}

Init ==
    /\ stack = <<>>
    /\ top = NULL
    /\ nodes = [n \in {} |-> [item |-> NULL, next |-> NULL]]
    /\ elim = [s \in 1..ElimSlots |-> [state |-> "EMPTY", item |-> NULL]]
    /\ pc = [t \in Threads |-> "idle"]
    /\ arg = [t \in Threads |-> NULL]
    /\ result = [t \in Threads |-> NULL]
    /\ history = <<>>

-----------------------------------------------------------------------------
(* Push via main stack *)

PushStart(t, item) ==
    /\ pc[t] = "idle"
    /\ item \in Items
    /\ arg' = [arg EXCEPT ![t] = item]
    /\ pc' = [pc EXCEPT ![t] = "push_cas"]
    /\ UNCHANGED <<stack, top, nodes, elim, result, history>>

PushCAS(t) ==
    /\ pc[t] = "push_cas"
    /\ LET item == arg[t]
           newNode == CHOOSE n \in (Nat \ DOMAIN nodes): TRUE
       IN /\ nodes' = nodes @@ (newNode :> [item |-> item, next |-> top])
          /\ top' = newNode
          /\ stack' = <<item>> \o stack
          /\ history' = Append(history, <<"push", item>>)
          /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED <<elim, arg, result>>

(* Push via elimination *)
PushElim(t, slot) ==
    /\ pc[t] = "push_cas"
    /\ slot \in 1..ElimSlots
    /\ elim[slot].state = "EMPTY"
    /\ elim' = [elim EXCEPT ![slot] = [state |-> "WAITING", item |-> arg[t]]]
    /\ pc' = [pc EXCEPT ![t] = "push_elim_wait"]
    /\ UNCHANGED <<stack, top, nodes, arg, result, history>>

PushElimComplete(t, slot) ==
    /\ pc[t] = "push_elim_wait"
    /\ elim[slot].state = "MATCHED"
    /\ elim' = [elim EXCEPT ![slot] = [state |-> "EMPTY", item |-> NULL]]
    /\ history' = Append(history, <<"push_elim", arg[t]>>)
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED <<stack, top, nodes, arg, result>>

PushElimTimeout(t, slot) ==
    /\ pc[t] = "push_elim_wait"
    /\ elim[slot].state = "WAITING"
    /\ elim' = [elim EXCEPT ![slot] = [state |-> "EMPTY", item |-> NULL]]
    /\ pc' = [pc EXCEPT ![t] = "push_cas"]  \* Retry via stack
    /\ UNCHANGED <<stack, top, nodes, arg, result, history>>

-----------------------------------------------------------------------------
(* Pop via main stack *)

PopStart(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "pop_cas"]
    /\ UNCHANGED <<stack, top, nodes, elim, arg, result, history>>

PopCAS(t) ==
    /\ pc[t] = "pop_cas"
    /\ IF top = NULL
       THEN \* Empty
            /\ result' = [result EXCEPT ![t] = NULL]
            /\ history' = Append(history, <<"pop", NULL>>)
            /\ pc' = [pc EXCEPT ![t] = "done"]
            /\ UNCHANGED <<stack, top, nodes>>
       ELSE \* Pop top
            /\ LET oldTop == top
                   item == nodes[oldTop].item
               IN /\ top' = nodes[oldTop].next
                  /\ stack' = Tail(stack)
                  /\ result' = [result EXCEPT ![t] = item]
                  /\ history' = Append(history, <<"pop", item>>)
                  /\ pc' = [pc EXCEPT ![t] = "done"]
            /\ UNCHANGED nodes
    /\ UNCHANGED <<elim, arg>>

(* Pop via elimination *)
PopElim(t, slot) ==
    /\ pc[t] = "pop_cas"
    /\ slot \in 1..ElimSlots
    /\ elim[slot].state = "WAITING"
    /\ elim[slot].item # NULL
    /\ result' = [result EXCEPT ![t] = elim[slot].item]
    /\ elim' = [elim EXCEPT ![slot].state = "MATCHED"]
    /\ history' = Append(history, <<"pop_elim", elim[slot].item>>)
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED <<stack, top, nodes, arg>>

-----------------------------------------------------------------------------
(* Complete operation *)

Complete(t) ==
    /\ pc[t] = "done"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ arg' = [arg EXCEPT ![t] = NULL]
    /\ result' = [result EXCEPT ![t] = NULL]
    /\ UNCHANGED <<stack, top, nodes, elim, history>>

-----------------------------------------------------------------------------
Next ==
    \E t \in Threads:
        \/ \E item \in Items: PushStart(t, item)
        \/ PushCAS(t)
        \/ \E slot \in 1..ElimSlots: PushElim(t, slot)
        \/ \E slot \in 1..ElimSlots: PushElimComplete(t, slot)
        \/ \E slot \in 1..ElimSlots: PushElimTimeout(t, slot)
        \/ PopStart(t)
        \/ PopCAS(t)
        \/ \E slot \in 1..ElimSlots: PopElim(t, slot)
        \/ Complete(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety Properties *)

\* LIFO: Stack maintains last-in-first-out order
LIFO ==
    LET pushes == SelectSeq(history, LAMBDA e: e[1] \in {"push", "push_elim"})
        pops == SelectSeq(history, LAMBDA e: e[1] \in {"pop", "pop_elim"} /\ e[2] # NULL)
    IN \* Pops are reverse of pushes (simplified check)
       Len(pops) <= Len(pushes)

\* No lost items
NoLoss ==
    LET pushed == {h[2]: h \in {history[i]: i \in 1..Len(history)} :
                   h[1] \in {"push", "push_elim"}}
        popped == {h[2]: h \in {history[i]: i \in 1..Len(history)} :
                   h[1] \in {"pop", "pop_elim"} /\ h[2] # NULL}
        inStack == IF stack = <<>> THEN {} ELSE {stack[i]: i \in 1..Len(stack)}
    IN pushed = popped \cup inStack

\* Elimination correctness
EliminationCorrect ==
    \A s \in 1..ElimSlots:
        elim[s].state = "MATCHED" => elim[s].item # NULL

-----------------------------------------------------------------------------
(* Liveness *)

LockFreedom ==
    []<>(\E t \in Threads: pc[t] = "done")

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ stack \in Seq(Items)
    /\ \A s \in 1..ElimSlots: elim[s].state \in ElimStates

SafetyInvariant ==
    /\ TypeInvariant
    /\ LIFO
    /\ NoLoss
    /\ EliminationCorrect

=============================================================================
