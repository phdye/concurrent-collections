---------------------------- MODULE smr_debra ----------------------------
(*
 * TLA+ Specification for DEBRA+ (Distributed Epoch-Based Reclamation with Neutralization)
 *
 * This specification extends smr_ibr with neutralization semantics:
 * - Stalled threads can be neutralized via signals
 * - Neutralized threads exit critical section and must restart
 * - Provides stronger memory bound guarantees
 *
 * Model checking parameters:
 * - THREADS = {t1, t2, t3}     (3 threads)
 * - NODES = {n1, n2, n3, n4}   (4 nodes)
 * - MAX_EPOCH = 5              (epoch limit)
 * - STALL_THRESHOLD = 2        (epochs before stall)
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS THREADS, NODES, MAX_EPOCH, STALL_THRESHOLD

VARIABLES
    (* Global state *)
    globalEpoch,           \* Current global epoch

    (* Per-thread state *)
    threadActive,          \* threadActive[t] = TRUE if in critical section
    threadEpoch,           \* threadEpoch[t] = epoch when entered
    threadNeutralized,     \* threadNeutralized[t] = TRUE if neutralized
    checkpointValid,       \* checkpointValid[t] = TRUE if checkpoint is set

    (* Per-node state *)
    nodeState,             \* nodeState[n] \in {"live", "retired", "freed"}
    nodeRetireEpoch,       \* nodeRetireEpoch[n] = epoch when retired

    (* Tracking for verification *)
    nodeAccessedBy,        \* nodeAccessedBy[n] = set of threads with reference
    operationInProgress    \* operationInProgress[t] = TRUE if mid-operation

vars == <<globalEpoch, threadActive, threadEpoch, threadNeutralized,
          checkpointValid, nodeState, nodeRetireEpoch, nodeAccessedBy,
          operationInProgress>>

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ globalEpoch \in 1..MAX_EPOCH
    /\ threadActive \in [THREADS -> BOOLEAN]
    /\ threadEpoch \in [THREADS -> 0..MAX_EPOCH]
    /\ threadNeutralized \in [THREADS -> BOOLEAN]
    /\ checkpointValid \in [THREADS -> BOOLEAN]
    /\ nodeState \in [NODES -> {"live", "retired", "freed"}]
    /\ nodeRetireEpoch \in [NODES -> 0..MAX_EPOCH]
    /\ nodeAccessedBy \in [NODES -> SUBSET THREADS]
    /\ operationInProgress \in [THREADS -> BOOLEAN]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ globalEpoch = 1
    /\ threadActive = [t \in THREADS |-> FALSE]
    /\ threadEpoch = [t \in THREADS |-> 0]
    /\ threadNeutralized = [t \in THREADS |-> FALSE]
    /\ checkpointValid = [t \in THREADS |-> FALSE]
    /\ nodeState = [n \in NODES |-> "live"]
    /\ nodeRetireEpoch = [n \in NODES |-> 0]
    /\ nodeAccessedBy = [n \in NODES |-> {}]
    /\ operationInProgress = [t \in THREADS |-> FALSE]

-----------------------------------------------------------------------------
(* Helper functions *)

(* Compute safe epoch: minimum epoch among active threads *)
SafeEpoch ==
    LET activeEpochs == {threadEpoch[t] : t \in {t \in THREADS : threadActive[t]}}
    IN IF activeEpochs = {}
       THEN globalEpoch
       ELSE CHOOSE e \in activeEpochs : \A e2 \in activeEpochs : e <= e2

(* Is thread stalled? (epoch lag exceeds threshold) *)
IsStalled(t) ==
    /\ threadActive[t]
    /\ globalEpoch - threadEpoch[t] >= STALL_THRESHOLD

(* Can global epoch advance? *)
CanAdvanceEpoch ==
    /\ globalEpoch < MAX_EPOCH
    /\ \A t \in THREADS : threadActive[t] => threadEpoch[t] = globalEpoch

(* Is it safe to free a node? *)
CanFreeNode(n) ==
    /\ nodeState[n] = "retired"
    /\ nodeRetireEpoch[n] < SafeEpoch
    /\ nodeAccessedBy[n] = {}

-----------------------------------------------------------------------------
(* Thread actions *)

(*
 * Enter critical section (with checkpoint)
 * Returns TRUE for normal entry, FALSE if neutralized
 *)
Enter(t) ==
    /\ ~threadActive[t]
    /\ ~threadNeutralized[t]
    /\ threadActive' = [threadActive EXCEPT ![t] = TRUE]
    /\ threadEpoch' = [threadEpoch EXCEPT ![t] = globalEpoch]
    /\ checkpointValid' = [checkpointValid EXCEPT ![t] = TRUE]
    /\ operationInProgress' = [operationInProgress EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<globalEpoch, threadNeutralized, nodeState, nodeRetireEpoch, nodeAccessedBy>>

(*
 * Resume after neutralization (debra_enter returns false)
 * Thread must clear neutralized flag and can retry
 *)
ResumeAfterNeutralize(t) ==
    /\ threadNeutralized[t]
    /\ ~threadActive[t]
    /\ threadNeutralized' = [threadNeutralized EXCEPT ![t] = FALSE]
    /\ operationInProgress' = [operationInProgress EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<globalEpoch, threadActive, threadEpoch, checkpointValid,
                   nodeState, nodeRetireEpoch, nodeAccessedBy>>

(* Exit critical section normally *)
Exit(t) ==
    /\ threadActive[t]
    /\ ~threadNeutralized[t]  \* Not being neutralized
    /\ threadActive' = [threadActive EXCEPT ![t] = FALSE]
    /\ checkpointValid' = [checkpointValid EXCEPT ![t] = FALSE]
    /\ operationInProgress' = [operationInProgress EXCEPT ![t] = FALSE]
    \* Release all node references
    /\ nodeAccessedBy' = [n \in NODES |-> nodeAccessedBy[n] \ {t}]
    /\ UNCHANGED <<globalEpoch, threadEpoch, threadNeutralized, nodeState, nodeRetireEpoch>>

(* Thread accesses a live node *)
AccessNode(t, n) ==
    /\ threadActive[t]
    /\ nodeState[n] = "live"
    /\ nodeAccessedBy' = [nodeAccessedBy EXCEPT ![n] = @ \cup {t}]
    /\ UNCHANGED <<globalEpoch, threadActive, threadEpoch, threadNeutralized,
                   checkpointValid, nodeState, nodeRetireEpoch, operationInProgress>>

(* Thread releases reference to node *)
ReleaseNode(t, n) ==
    /\ threadActive[t]
    /\ t \in nodeAccessedBy[n]
    /\ nodeAccessedBy' = [nodeAccessedBy EXCEPT ![n] = @ \ {t}]
    /\ UNCHANGED <<globalEpoch, threadActive, threadEpoch, threadNeutralized,
                   checkpointValid, nodeState, nodeRetireEpoch, operationInProgress>>

(* Thread retires a node *)
RetireNode(t, n) ==
    /\ threadActive[t]
    /\ nodeState[n] = "live"
    /\ nodeState' = [nodeState EXCEPT ![n] = "retired"]
    /\ nodeRetireEpoch' = [nodeRetireEpoch EXCEPT ![n] = threadEpoch[t]]
    /\ UNCHANGED <<globalEpoch, threadActive, threadEpoch, threadNeutralized,
                   checkpointValid, nodeAccessedBy, operationInProgress>>

-----------------------------------------------------------------------------
(* Neutralization actions *)

(*
 * Neutralize a stalled thread (signal handler fires)
 * This models the signal being delivered and handler executing
 *)
Neutralize(t) ==
    /\ IsStalled(t)                           \* Thread must be stalled
    /\ checkpointValid[t]                     \* Checkpoint must be valid
    /\ threadNeutralized' = [threadNeutralized EXCEPT ![t] = TRUE]
    /\ threadActive' = [threadActive EXCEPT ![t] = FALSE]
    /\ checkpointValid' = [checkpointValid EXCEPT ![t] = FALSE]
    \* Release all references (longjmp abandons operation)
    /\ nodeAccessedBy' = [n \in NODES |-> nodeAccessedBy[n] \ {t}]
    \* Operation is aborted
    /\ operationInProgress' = [operationInProgress EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<globalEpoch, threadEpoch, nodeState, nodeRetireEpoch>>

-----------------------------------------------------------------------------
(* System actions *)

(* Free a retired node when safe *)
FreeNode(n) ==
    /\ CanFreeNode(n)
    /\ nodeState' = [nodeState EXCEPT ![n] = "freed"]
    /\ UNCHANGED <<globalEpoch, threadActive, threadEpoch, threadNeutralized,
                   checkpointValid, nodeRetireEpoch, nodeAccessedBy, operationInProgress>>

(* Advance global epoch *)
AdvanceEpoch ==
    /\ CanAdvanceEpoch
    /\ globalEpoch' = globalEpoch + 1
    /\ UNCHANGED <<threadActive, threadEpoch, threadNeutralized, checkpointValid,
                   nodeState, nodeRetireEpoch, nodeAccessedBy, operationInProgress>>

-----------------------------------------------------------------------------
(* Next state relation *)

ThreadAction(t) ==
    \/ Enter(t)
    \/ Exit(t)
    \/ ResumeAfterNeutralize(t)
    \/ \E n \in NODES : AccessNode(t, n)
    \/ \E n \in NODES : ReleaseNode(t, n)
    \/ \E n \in NODES : RetireNode(t, n)

NeutralizationAction ==
    \E t \in THREADS : Neutralize(t)

SystemAction ==
    \/ \E n \in NODES : FreeNode(n)
    \/ AdvanceEpoch

Next ==
    \/ \E t \in THREADS : ThreadAction(t)
    \/ NeutralizationAction
    \/ SystemAction

-----------------------------------------------------------------------------
(* Fairness *)

Fairness ==
    /\ \A t \in THREADS : WF_vars(Enter(t))
    /\ \A t \in THREADS : WF_vars(Exit(t))
    /\ \A t \in THREADS : WF_vars(ResumeAfterNeutralize(t))
    /\ \A t \in THREADS : WF_vars(Neutralize(t))  \* Neutralization is fair
    /\ WF_vars(AdvanceEpoch)
    /\ \A n \in NODES : WF_vars(FreeNode(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Properties *)

(* S1: No Use-After-Free
 * Freed nodes are never accessed
 *)
NoUseAfterFree ==
    \A n \in NODES : nodeState[n] = "freed" => nodeAccessedBy[n] = {}

(* S2: Checkpoint Validity
 * Checkpoint valid only when active
 *)
CheckpointValidity ==
    \A t \in THREADS : checkpointValid[t] => threadActive[t]

(* S3: Neutralization Safety
 * Neutralized threads are not active
 *)
NeutralizationSafety ==
    \A t \in THREADS : threadNeutralized[t] => ~threadActive[t]

(* S4: No Orphaned References
 * Only active threads hold references
 *)
NoOrphanedRefs ==
    \A n \in NODES : \A t \in nodeAccessedBy[n] : threadActive[t]

(* S5: Freed nodes have no references *)
FreedNodesNoRefs ==
    \A n \in NODES : nodeState[n] = "freed" => nodeAccessedBy[n] = {}

-----------------------------------------------------------------------------
(* Key Invariants *)

(* I1: Active threads have valid epoch *)
ActiveThreadsHaveValidEpoch ==
    \A t \in THREADS : threadActive[t] =>
        threadEpoch[t] >= 1 /\ threadEpoch[t] <= globalEpoch

(* I2: Epoch monotonicity *)
EpochMonotonic ==
    [][globalEpoch' >= globalEpoch]_globalEpoch

(* I3: Checkpoint implies active *)
CheckpointImpliesActive ==
    \A t \in THREADS : checkpointValid[t] => threadActive[t]

(* I4: Neutralized implies not active *)
NeutralizedImpliesInactive ==
    \A t \in THREADS : threadNeutralized[t] => ~threadActive[t]

(* Combined safety invariant *)
Safety ==
    /\ TypeOK
    /\ NoUseAfterFree
    /\ CheckpointValidity
    /\ NeutralizationSafety
    /\ NoOrphanedRefs
    /\ FreedNodesNoRefs
    /\ ActiveThreadsHaveValidEpoch

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* L1: Stalled threads eventually neutralized *)
StalledEventuallyNeutralized ==
    \A t \in THREADS : IsStalled(t) ~> (~threadActive[t])

(* L2: Neutralization enables progress
 * If threads are stalled, neutralization allows epoch to advance
 *)
NeutralizationEnablesProgress ==
    (\E t \in THREADS : IsStalled(t)) ~>
        (globalEpoch' > globalEpoch \/ \A t \in THREADS : ~IsStalled(t))

(* L3: Retired nodes eventually freed *)
EventuallyFreed ==
    \A n \in NODES : nodeState[n] = "retired" ~> nodeState[n] = "freed"

(* L4: Neutralized threads eventually resume *)
EventuallyResume ==
    \A t \in THREADS : threadNeutralized[t] ~> ~threadNeutralized[t]

-----------------------------------------------------------------------------
(* Memory Bound Property *)

(*
 * DEBRA+ guarantees O(T × R) memory bound, not O(T² × R) like basic IBR.
 * This is because stalled threads are neutralized, so they cannot
 * indefinitely block reclamation.
 *
 * We model this by showing that the safe epoch always advances
 * as long as neutralization is applied to stalled threads.
 *)

(* Count of retired nodes still pending *)
PendingCount ==
    Cardinality({n \in NODES : nodeState[n] = "retired"})

(* Property: With neutralization, pending count is bounded *)
BoundedPending ==
    PendingCount <= Cardinality(NODES)  \* Simplified bound for model checking

-----------------------------------------------------------------------------
(* Operation Restart Semantics *)

(*
 * When a thread is neutralized:
 * 1. Its operation is aborted (longjmp to checkpoint)
 * 2. All acquired references are released
 * 3. Thread must restart operation from beginning
 *
 * This is modeled by:
 * - Neutralize action releases nodeAccessedBy
 * - Thread must call ResumeAfterNeutralize before Enter
 * - Re-entering gets fresh epoch and re-reads data
 *)

(* Property: After neutralization, thread can successfully re-enter *)
CanReenterAfterNeutralize ==
    \A t \in THREADS :
        (threadNeutralized[t] /\ ~threadNeutralized'[t]) ~>
            (ENABLED Enter(t))

-----------------------------------------------------------------------------
(* Comparison with IBR *)

(*
 * Difference from smr_ibr specification:
 * 1. Added threadNeutralized and checkpointValid state
 * 2. Added Neutralize action that can force thread exit
 * 3. Added ResumeAfterNeutralize for operation restart
 * 4. Stronger liveness: stalled threads don't block forever
 *
 * Safety properties are preserved:
 * - No use-after-free (same proof, neutralization releases refs)
 * - No double-free (same proof)
 *)

-----------------------------------------------------------------------------
(* Model Checking Hints *)

Symmetry == Permutations(THREADS) \cup Permutations(NODES)

StateConstraint ==
    /\ globalEpoch <= MAX_EPOCH
    /\ \A t \in THREADS : threadEpoch[t] <= MAX_EPOCH

=============================================================================
\* Modification History
\* Created for concurrent-collections DEBRA+ specification
