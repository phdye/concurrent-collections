--------------------------- MODULE [ModuleName] ---------------------------
(*
 * [Module Name] — TLA+ Specification
 * 
 * Purpose: [What this spec verifies]
 * 
 * Properties verified:
 *   - [Property 1]
 *   - [Property 2]
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Threads,        \* Set of thread identifiers
    Keys,           \* Set of possible keys (for maps/sets)
    Values,         \* Set of possible values (for maps)
    MaxOps          \* Bound for model checking

VARIABLES
    \* Data structure state
    state,          \* The abstract state of the data structure
    
    \* Per-thread state
    pc,             \* Program counter per thread
    local,          \* Local variables per thread
    
    \* History for linearizability
    history         \* Sequence of completed operations

vars == <<state, pc, local, history>>

-----------------------------------------------------------------------------
(* Type Invariants *)

TypeInvariant ==
    /\ state \in [type specification]
    /\ pc \in [Threads -> {"idle", "op1", "op2", ...}]
    /\ local \in [Threads -> [local var specification]]
    /\ history \in Seq([op: {"op1", "op2"}, args: ..., result: ...])

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ state = [initial state]
    /\ pc = [t \in Threads |-> "idle"]
    /\ local = [t \in Threads |-> [initial local state]]
    /\ history = <<>>

-----------------------------------------------------------------------------
(* Operations *)

(* Operation 1: [Description] *)
Op1_Start(t, args) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "op1_running"]
    /\ local' = [local EXCEPT ![t] = [args |-> args]]
    /\ UNCHANGED <<state, history>>

Op1_Complete(t) ==
    /\ pc[t] = "op1_running"
    /\ \* State transition
       state' = [new state based on operation]
    /\ \* Record in history
       history' = Append(history, [op |-> "op1", 
                                    thread |-> t,
                                    args |-> local[t].args,
                                    result |-> [result]])
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED local

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \E t \in Threads:
        \/ Op1_Start(t, CHOOSE args \in ArgsSet: TRUE)
        \/ Op1_Complete(t)
        \* ... more operations

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety Properties *)

(* Invariant 1: [Description] *)
Invariant1 ==
    [property that must always hold]

(* Invariant 2: [Description] *)
Invariant2 ==
    [another property]

Safety == TypeInvariant /\ Invariant1 /\ Invariant2

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* Every started operation eventually completes *)
OperationsComplete ==
    \A t \in Threads:
        pc[t] # "idle" ~> pc[t] = "idle"

(* Lock-free: some thread always makes progress *)
LockFreeProgress ==
    []<>(\E t \in Threads: pc[t] = "idle" /\ pc'[t] # "idle")

Liveness == OperationsComplete /\ LockFreeProgress

-----------------------------------------------------------------------------
(* Linearizability *)

(* 
 * A history is linearizable if operations can be ordered such that:
 * 1. The order respects real-time (non-overlapping ops maintain order)
 * 2. The sequential execution is legal per the abstract spec
 *)

IsLinearizable(h) ==
    \E order \in Permutations(h):
        /\ RespectsRealTime(order)
        /\ LegalSequentialExecution(order)

LinearizabilityInvariant ==
    IsLinearizable(history)

=============================================================================
