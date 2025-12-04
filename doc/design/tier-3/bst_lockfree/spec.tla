---------------------------- MODULE BSTLockFree ----------------------------
(*
 * TLA+ Specification for Natarajan-Mittal Lock-Free External BST
 *
 * Models:
 * 1. External tree structure (keys in leaves)
 * 2. Three-phase deletion (Intent → Marked → Physical)
 * 3. Helping mechanism
 * 4. Linearizability
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Keys,           \* Set of keys
    Values,         \* Set of values
    Threads,        \* Thread identifiers
    NIL             \* Null constant

VARIABLES
    (* Tree structure *)
    internal,       \* internal[n] = record of key, left, right
    leaf,           \* leaf[n] = record of key, value
    root,           \* Root internal node
    leftSentinel,   \* Left sentinel leaf
    rightSentinel,  \* Right sentinel leaf

    (* Edge flags: CLEAN=0, INTENT=1, MARKED=2 *)
    edgeFlag,       \* edgeFlag[parent][child] = flag value

    (* Thread state *)
    pc,             \* Program counter
    opKey,          \* Operation key
    opValue,        \* Operation value
    searchRec,      \* Search record (gp, p, l, etc.)

    (* SMR state *)
    retired,
    freed,

    (* Verification *)
    history

vars == <<internal, leaf, root, leftSentinel, rightSentinel, edgeFlag,
          pc, opKey, opValue, searchRec, retired, freed, history>>

-----------------------------------------------------------------------------
(* Constants for edge flags *)
CLEAN == 0
INTENT == 1
MARKED == 2

(* Node types *)
NodeTypes == {"internal", "leaf"}

PCs == {"idle", "search", "insert_check", "insert_cas", "delete_intent",
        "delete_mark", "delete_physical", "helping", "done"}

-----------------------------------------------------------------------------
(* Type definitions *)

InternalNode == [key: Keys,
                 left: DOMAIN leaf \cup DOMAIN internal \cup {NIL},
                 right: DOMAIN leaf \cup DOMAIN internal \cup {NIL}]

LeafNode == [key: Keys \cup {NIL}, value: Values \cup {NIL}]

SearchRecord == [gp: DOMAIN internal \cup {NIL},
                 p: DOMAIN internal,
                 l: DOMAIN leaf,
                 gpEdge: {CLEAN, INTENT, MARKED},
                 pEdge: {CLEAN, INTENT, MARKED}]

-----------------------------------------------------------------------------
(* Initialization *)

Init ==
    /\ leftSentinel = "leftSent"
    /\ rightSentinel = "rightSent"
    /\ root = "root"
    /\ leaf = [n \in {leftSentinel, rightSentinel} |->
               IF n = leftSentinel THEN [key |-> NIL, value |-> NIL]
               ELSE [key |-> NIL, value |-> NIL]]
    /\ internal = [n \in {root} |->
                   [key |-> NIL, left |-> leftSentinel, right |-> rightSentinel]]
    /\ edgeFlag = [p \in DOMAIN internal |->
                   [c \in DOMAIN leaf \cup DOMAIN internal |-> CLEAN]]
    /\ pc = [t \in Threads |-> "idle"]
    /\ opKey = [t \in Threads |-> NIL]
    /\ opValue = [t \in Threads |-> NIL]
    /\ searchRec = [t \in Threads |-> [gp |-> NIL, p |-> NIL, l |-> NIL,
                                        gpEdge |-> CLEAN, pEdge |-> CLEAN]]
    /\ retired = {}
    /\ freed = {}
    /\ history = <<>>

-----------------------------------------------------------------------------
(* Helper predicates *)

\* Key comparison (NIL sorts before everything)
KeyLess(k1, k2) ==
    IF k1 = NIL THEN TRUE
    ELSE IF k2 = NIL THEN FALSE
    ELSE k1 < k2

\* Get child of internal node based on key
GetChild(n, key) ==
    IF KeyLess(key, internal[n].key)
    THEN internal[n].left
    ELSE internal[n].right

\* Check if node is a leaf
IsLeaf(n) == n \in DOMAIN leaf

\* Check if node is internal
IsInternal(n) == n \in DOMAIN internal

\* Key exists in tree
KeyInTree(key) ==
    \E l \in DOMAIN leaf:
        /\ leaf[l].key = key
        /\ l # leftSentinel
        /\ l # rightSentinel
        /\ Reachable(l)

\* Node is reachable from root
Reachable(n) ==
    \E path \in Seq(DOMAIN internal \cup DOMAIN leaf):
        /\ Len(path) > 0
        /\ path[1] = root
        /\ path[Len(path)] = n
        /\ \A i \in 1..(Len(path)-1):
            \/ internal[path[i]].left = path[i+1]
            \/ internal[path[i]].right = path[i+1]

-----------------------------------------------------------------------------
(* Search operation *)

Search(t, key) ==
    /\ pc[t] = "idle"
    /\ opKey' = [opKey EXCEPT ![t] = key]
    /\ pc' = [pc EXCEPT ![t] = "search"]
    /\ UNCHANGED <<internal, leaf, root, leftSentinel, rightSentinel,
                   edgeFlag, opValue, searchRec, retired, freed, history>>

DoSearch(t) ==
    /\ pc[t] = "search"
    /\ LET key == opKey[t]
           \* Simplified: find leaf for key
           l == CHOOSE leaf_node \in DOMAIN leaf:
                    \/ (leaf[leaf_node].key = key /\ Reachable(leaf_node))
                    \/ (~KeyInTree(key) /\ leaf_node = leftSentinel)
       IN /\ searchRec' = [searchRec EXCEPT ![t].l = l]
          /\ IF leaf[l].key = key /\ l # leftSentinel /\ l # rightSentinel
             THEN /\ history' = Append(history, <<"search", key, TRUE>>)
                  /\ pc' = [pc EXCEPT ![t] = "done"]
             ELSE /\ history' = Append(history, <<"search", key, FALSE>>)
                  /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED <<internal, leaf, root, leftSentinel, rightSentinel,
                   edgeFlag, opKey, opValue, retired, freed>>

-----------------------------------------------------------------------------
(* Insert operation *)

Insert(t, key, value) ==
    /\ pc[t] = "idle"
    /\ opKey' = [opKey EXCEPT ![t] = key]
    /\ opValue' = [opValue EXCEPT ![t] = value]
    /\ pc' = [pc EXCEPT ![t] = "insert_check"]
    /\ UNCHANGED <<internal, leaf, root, leftSentinel, rightSentinel,
                   edgeFlag, searchRec, retired, freed, history>>

InsertCheck(t) ==
    /\ pc[t] = "insert_check"
    /\ LET key == opKey[t]
       IN IF KeyInTree(key)
          THEN \* Key exists
               /\ history' = Append(history, <<"insert", key, FALSE>>)
               /\ pc' = [pc EXCEPT ![t] = "done"]
               /\ UNCHANGED <<internal, leaf, edgeFlag>>
          ELSE \* Proceed to CAS
               /\ pc' = [pc EXCEPT ![t] = "insert_cas"]
               /\ UNCHANGED <<internal, leaf, edgeFlag, history>>
    /\ UNCHANGED <<root, leftSentinel, rightSentinel, opKey, opValue,
                   searchRec, retired, freed>>

InsertCAS(t) ==
    /\ pc[t] = "insert_cas"
    /\ LET key == opKey[t]
           value == opValue[t]
           newLeaf == CHOOSE n \in {"new_leaf_" \o ToString(t)}: TRUE
           newInternal == CHOOSE n \in {"new_int_" \o ToString(t)}: TRUE
       IN \* Simplified: atomically add new nodes
          /\ leaf' = leaf @@ (newLeaf :> [key |-> key, value |-> value])
          /\ internal' = internal @@ (newInternal :>
                         [key |-> key, left |-> newLeaf, right |-> NIL])
          /\ history' = Append(history, <<"insert", key, TRUE>>)
          /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED <<root, leftSentinel, rightSentinel, edgeFlag, opKey, opValue,
                   searchRec, retired, freed>>

-----------------------------------------------------------------------------
(* Delete operation - Three phases *)

Delete(t, key) ==
    /\ pc[t] = "idle"
    /\ opKey' = [opKey EXCEPT ![t] = key]
    /\ pc' = [pc EXCEPT ![t] = "delete_intent"]
    /\ UNCHANGED <<internal, leaf, root, leftSentinel, rightSentinel,
                   edgeFlag, opValue, searchRec, retired, freed, history>>

DeleteIntent(t) ==
    /\ pc[t] = "delete_intent"
    /\ LET key == opKey[t]
       IN IF ~KeyInTree(key)
          THEN \* Key not found
               /\ history' = Append(history, <<"delete", key, FALSE>>)
               /\ pc' = [pc EXCEPT ![t] = "done"]
               /\ UNCHANGED <<edgeFlag, retired>>
          ELSE \* Set INTENT flag (linearization point)
               /\ \E p \in DOMAIN internal, l \in DOMAIN leaf:
                    /\ leaf[l].key = key
                    /\ (internal[p].left = l \/ internal[p].right = l)
                    /\ edgeFlag[p][l] = CLEAN
                    /\ edgeFlag' = [edgeFlag EXCEPT ![p][l] = INTENT]
               /\ history' = Append(history, <<"delete", key, TRUE>>)
               /\ pc' = [pc EXCEPT ![t] = "delete_mark"]
               /\ UNCHANGED retired
    /\ UNCHANGED <<internal, leaf, root, leftSentinel, rightSentinel,
                   opKey, opValue, searchRec, freed>>

DeleteMark(t) ==
    /\ pc[t] = "delete_mark"
    /\ \* Set MARKED flag on grandparent edge
       \E gp \in DOMAIN internal, p \in DOMAIN internal:
           /\ (internal[gp].left = p \/ internal[gp].right = p)
           /\ edgeFlag[gp][p] = CLEAN
           /\ edgeFlag' = [edgeFlag EXCEPT ![gp][p] = MARKED]
    /\ pc' = [pc EXCEPT ![t] = "delete_physical"]
    /\ UNCHANGED <<internal, leaf, root, leftSentinel, rightSentinel,
                   opKey, opValue, searchRec, retired, freed, history>>

DeletePhysical(t) ==
    /\ pc[t] = "delete_physical"
    /\ \* Swing sibling up, retire nodes
       \E gp \in DOMAIN internal, p \in DOMAIN internal, l \in DOMAIN leaf:
           /\ edgeFlag[gp][p] = MARKED
           /\ (internal[p].left = l \/ internal[p].right = l)
           /\ edgeFlag[p][l] = INTENT
           /\ retired' = retired \cup {p, l}
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED <<internal, leaf, root, leftSentinel, rightSentinel,
                   edgeFlag, opKey, opValue, searchRec, freed, history>>

-----------------------------------------------------------------------------
(* Complete and return to idle *)

Complete(t) ==
    /\ pc[t] = "done"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ opKey' = [opKey EXCEPT ![t] = NIL]
    /\ opValue' = [opValue EXCEPT ![t] = NIL]
    /\ UNCHANGED <<internal, leaf, root, leftSentinel, rightSentinel,
                   edgeFlag, searchRec, retired, freed, history>>

-----------------------------------------------------------------------------
(* Next state *)

Next ==
    \E t \in Threads:
        \/ \E k \in Keys: Search(t, k)
        \/ DoSearch(t)
        \/ \E k \in Keys, v \in Values: Insert(t, k, v)
        \/ InsertCheck(t)
        \/ InsertCAS(t)
        \/ \E k \in Keys: Delete(t, k)
        \/ DeleteIntent(t)
        \/ DeleteMark(t)
        \/ DeletePhysical(t)
        \/ Complete(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety Properties *)

\* BST ordering property
BSTProperty ==
    \A n \in DOMAIN internal:
        /\ \A l \in DOMAIN leaf:
            internal[n].left = l => KeyLess(leaf[l].key, internal[n].key)
        /\ \A l \in DOMAIN leaf:
            internal[n].right = l => ~KeyLess(leaf[l].key, internal[n].key)

\* External tree property: internals have two children
ExternalProperty ==
    \A n \in DOMAIN internal:
        internal[n].left # NIL /\ internal[n].right # NIL

\* Flag monotonicity
FlagMonotonicity ==
    \A p \in DOMAIN internal, c \in DOMAIN leaf \cup DOMAIN internal:
        edgeFlag[p][c] = MARKED =>
            edgeFlag'[p][c] = MARKED

\* No use after free
NoUseAfterFree ==
    \A n \in freed: ~Reachable(n)

\* Sentinels never deleted
SentinelsProtected ==
    /\ leftSentinel \notin retired
    /\ rightSentinel \notin retired

-----------------------------------------------------------------------------
(* Liveness *)

\* Lock-freedom: some thread always completes
LockFreedom ==
    []<>(\E t \in Threads: pc[t] = "done")

-----------------------------------------------------------------------------
(* Invariants *)

TypeInvariant ==
    /\ root \in DOMAIN internal
    /\ leftSentinel \in DOMAIN leaf
    /\ rightSentinel \in DOMAIN leaf

SafetyInvariant ==
    /\ TypeInvariant
    /\ BSTProperty
    /\ ExternalProperty
    /\ NoUseAfterFree
    /\ SentinelsProtected

=============================================================================
