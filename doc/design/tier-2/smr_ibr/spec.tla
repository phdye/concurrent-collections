---------------------------- MODULE smr_ibr ----------------------------
(*
 * TLA+ Specification for Interval-Based Reclamation (IBR)
 *
 * This specification verifies the safety properties of IBR:
 * - No use-after-free: A node is never freed while any thread may access it
 * - No double-free: Each node is freed exactly once
 *
 * Model checking parameters:
 * - THREADS = {t1, t2, t3}     (3 threads sufficient to expose races)
 * - NODES = {n1, n2, n3, n4}   (4 nodes for reclamation testing)
 * - MAX_EPOCH = 5              (demonstrates epoch advancement)
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS THREADS, NODES, MAX_EPOCH

VARIABLES
    (* Global state *)
    globalEpoch,           \* Current global epoch (Nat)

    (* Per-thread state *)
    threadActive,          \* threadActive[t] = TRUE if t is in critical section
    threadEpoch,           \* threadEpoch[t] = epoch when t entered (or 0)

    (* Per-node state *)
    nodeState,             \* nodeState[n] \in {"live", "retired", "freed"}
    nodeRetireEpoch,       \* nodeRetireEpoch[n] = epoch when retired (or 0)

    (* Tracking for safety verification *)
    nodeAccessedBy         \* nodeAccessedBy[n] = set of threads currently accessing n

vars == <<globalEpoch, threadActive, threadEpoch, nodeState, nodeRetireEpoch, nodeAccessedBy>>

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ globalEpoch \in 1..MAX_EPOCH
    /\ threadActive \in [THREADS -> BOOLEAN]
    /\ threadEpoch \in [THREADS -> 0..MAX_EPOCH]
    /\ nodeState \in [NODES -> {"live", "retired", "freed"}]
    /\ nodeRetireEpoch \in [NODES -> 0..MAX_EPOCH]
    /\ nodeAccessedBy \in [NODES -> SUBSET THREADS]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ globalEpoch = 1
    /\ threadActive = [t \in THREADS |-> FALSE]
    /\ threadEpoch = [t \in THREADS |-> 0]
    /\ nodeState = [n \in NODES |-> "live"]
    /\ nodeRetireEpoch = [n \in NODES |-> 0]
    /\ nodeAccessedBy = [n \in NODES |-> {}]

-----------------------------------------------------------------------------
(* Helper functions *)

(* Compute safe epoch: minimum epoch among active threads *)
SafeEpoch ==
    LET activeEpochs == {threadEpoch[t] : t \in {t \in THREADS : threadActive[t]}}
    IN IF activeEpochs = {}
       THEN globalEpoch
       ELSE CHOOSE e \in activeEpochs : \A e2 \in activeEpochs : e <= e2

(* Can the global epoch advance? All active threads must be at current epoch *)
CanAdvanceEpoch ==
    /\ globalEpoch < MAX_EPOCH
    /\ \A t \in THREADS : threadActive[t] => threadEpoch[t] = globalEpoch

(* Is it safe to free a node retired in given epoch? *)
CanFreeNode(n) ==
    /\ nodeState[n] = "retired"
    /\ nodeRetireEpoch[n] < SafeEpoch
    /\ nodeAccessedBy[n] = {}  \* No thread currently accessing

-----------------------------------------------------------------------------
(* Thread actions *)

(* Thread enters critical section *)
Enter(t) ==
    /\ ~threadActive[t]                    \* Precondition: not already active
    /\ threadActive' = [threadActive EXCEPT ![t] = TRUE]
    /\ threadEpoch' = [threadEpoch EXCEPT ![t] = globalEpoch]
    /\ UNCHANGED <<globalEpoch, nodeState, nodeRetireEpoch, nodeAccessedBy>>

(* Thread exits critical section *)
Exit(t) ==
    /\ threadActive[t]                     \* Precondition: currently active
    /\ threadActive' = [threadActive EXCEPT ![t] = FALSE]
    \* Release all node references
    /\ nodeAccessedBy' = [n \in NODES |-> nodeAccessedBy[n] \ {t}]
    /\ UNCHANGED <<globalEpoch, threadEpoch, nodeState, nodeRetireEpoch>>

(* Thread accesses a live node (acquires reference) *)
AccessNode(t, n) ==
    /\ threadActive[t]                     \* Must be in critical section
    /\ nodeState[n] = "live"               \* Node must be live (not yet retired)
    /\ nodeAccessedBy' = [nodeAccessedBy EXCEPT ![n] = @ \cup {t}]
    /\ UNCHANGED <<globalEpoch, threadActive, threadEpoch, nodeState, nodeRetireEpoch>>

(* Thread releases reference to a node *)
ReleaseNode(t, n) ==
    /\ threadActive[t]
    /\ t \in nodeAccessedBy[n]
    /\ nodeAccessedBy' = [nodeAccessedBy EXCEPT ![n] = @ \ {t}]
    /\ UNCHANGED <<globalEpoch, threadActive, threadEpoch, nodeState, nodeRetireEpoch>>

(* Thread retires a node (marks for deferred reclamation) *)
RetireNode(t, n) ==
    /\ threadActive[t]                     \* Must be in critical section
    /\ nodeState[n] = "live"               \* Can only retire live nodes
    /\ nodeState' = [nodeState EXCEPT ![n] = "retired"]
    /\ nodeRetireEpoch' = [nodeRetireEpoch EXCEPT ![n] = threadEpoch[t]]
    \* Note: other threads may still have references (nodeAccessedBy unchanged)
    /\ UNCHANGED <<globalEpoch, threadActive, threadEpoch, nodeAccessedBy>>

(* System frees a retired node (when safe) *)
FreeNode(n) ==
    /\ CanFreeNode(n)
    /\ nodeState' = [nodeState EXCEPT ![n] = "freed"]
    /\ UNCHANGED <<globalEpoch, threadActive, threadEpoch, nodeRetireEpoch, nodeAccessedBy>>

(* Global epoch advances *)
AdvanceEpoch ==
    /\ CanAdvanceEpoch
    /\ globalEpoch' = globalEpoch + 1
    /\ UNCHANGED <<threadActive, threadEpoch, nodeState, nodeRetireEpoch, nodeAccessedBy>>

-----------------------------------------------------------------------------
(* Next state relation *)

ThreadAction(t) ==
    \/ Enter(t)
    \/ Exit(t)
    \/ \E n \in NODES : AccessNode(t, n)
    \/ \E n \in NODES : ReleaseNode(t, n)
    \/ \E n \in NODES : RetireNode(t, n)

SystemAction ==
    \/ \E n \in NODES : FreeNode(n)
    \/ AdvanceEpoch

Next ==
    \/ \E t \in THREADS : ThreadAction(t)
    \/ SystemAction

-----------------------------------------------------------------------------
(* Fairness *)

Fairness ==
    /\ \A t \in THREADS : WF_vars(Enter(t))
    /\ \A t \in THREADS : WF_vars(Exit(t))
    /\ WF_vars(AdvanceEpoch)
    /\ \A n \in NODES : WF_vars(FreeNode(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Properties *)

(* S1: No Use-After-Free
 * A freed node is never accessed by any thread.
 * More precisely: if a node is freed, no thread has a reference to it.
 *)
NoUseAfterFree ==
    \A n \in NODES : nodeState[n] = "freed" => nodeAccessedBy[n] = {}

(* S2: No Double-Free
 * Once a node is freed, it stays freed (monotonicity).
 * Implied by the state transition: retired -> freed is one-way.
 *)
NoDoubleFree ==
    \A n \in NODES :
        nodeState[n] = "freed" => nodeState'[n] = "freed" \/ UNCHANGED nodeState

(* Alternative formulation: freed nodes never become live or retired again *)
NoDoubleFreeAlt ==
    [][
        \A n \in NODES :
            nodeState[n] = "freed" => nodeState'[n] = "freed"
    ]_vars

(* S3: Epoch Monotonicity
 * Global epoch never decreases.
 *)
EpochMonotonic ==
    [][globalEpoch' >= globalEpoch]_globalEpoch

(* S4: Safe Epoch Property
 * A node is only freed if all active threads have epoch > retire epoch.
 *)
SafeEpochProperty ==
    \A n \in NODES :
        (nodeState[n] = "retired" /\ nodeState'[n] = "freed") =>
            \A t \in THREADS :
                threadActive[t] => threadEpoch[t] > nodeRetireEpoch[n]

-----------------------------------------------------------------------------
(* Key Invariants *)

(* I1: Active threads have valid epoch *)
ActiveThreadsHaveValidEpoch ==
    \A t \in THREADS : threadActive[t] => threadEpoch[t] >= 1 /\ threadEpoch[t] <= globalEpoch

(* I2: Retired nodes have valid retire epoch *)
RetiredNodesHaveValidEpoch ==
    \A n \in NODES : nodeState[n] = "retired" =>
        nodeRetireEpoch[n] >= 1 /\ nodeRetireEpoch[n] <= globalEpoch

(* I3: Only active threads can have references *)
OnlyActiveThreadsHaveRefs ==
    \A n \in NODES : \A t \in nodeAccessedBy[n] : threadActive[t]

(* I4: Freed nodes have no references *)
FreedNodesNoRefs ==
    \A n \in NODES : nodeState[n] = "freed" => nodeAccessedBy[n] = {}

(* Combined safety invariant *)
Safety ==
    /\ TypeOK
    /\ NoUseAfterFree
    /\ ActiveThreadsHaveValidEpoch
    /\ RetiredNodesHaveValidEpoch
    /\ OnlyActiveThreadsHaveRefs
    /\ FreedNodesNoRefs

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* L1: Eventually all retired nodes are freed (under fairness) *)
EventuallyFreed ==
    \A n \in NODES : nodeState[n] = "retired" ~> nodeState[n] = "freed"

(* L2: Epoch eventually advances (if threads cooperate) *)
EpochProgress ==
    globalEpoch < MAX_EPOCH ~> globalEpoch' > globalEpoch

-----------------------------------------------------------------------------
(* Model Checking Hints *)

(* Symmetry: threads and nodes are symmetric *)
Symmetry == Permutations(THREADS) \cup Permutations(NODES)

(* State constraint to limit state space *)
StateConstraint ==
    /\ globalEpoch <= MAX_EPOCH
    /\ \A t \in THREADS : threadEpoch[t] <= MAX_EPOCH

=============================================================================
\* Modification History
\* Created for concurrent-collections IBR specification
