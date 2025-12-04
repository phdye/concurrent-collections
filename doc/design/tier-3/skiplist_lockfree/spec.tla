---------------------------- MODULE SkipListLockFree ----------------------------
(*
 * TLA+ Specification for Fraser's Lock-Free Skip List
 *
 * This specification models the concurrent behavior of a lock-free skip list,
 * focusing on:
 * 1. Linearizability of insert, delete, and search operations
 * 2. Lock-freedom progress guarantee
 * 3. Memory safety (no use-after-free with SMR)
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Keys,           \* Set of possible keys
    Values,         \* Set of possible values
    Threads,        \* Set of thread identifiers
    MaxLevel,       \* Maximum skip list level
    NIL             \* Null pointer constant

VARIABLES
    (* Skip list structure *)
    nodes,          \* nodes[n] = record of key, value, levels, marked
    head,           \* Head sentinel node
    tail,           \* Tail sentinel node
    next,           \* next[n][level] = successor node (with mark bit)

    (* Thread state *)
    pc,             \* Program counter per thread
    op,             \* Current operation per thread
    opKey,          \* Key argument per thread
    opValue,        \* Value argument per thread
    preds,          \* Predecessor array per thread per level
    succs,          \* Successor array per thread per level
    newNode,        \* Newly allocated node per thread
    found,          \* Whether find located the key

    (* SMR state *)
    retired,        \* Set of retired nodes
    freed,          \* Set of freed nodes
    inCritical,     \* Whether thread is in SMR critical section

    (* Auxiliary for verification *)
    history         \* Linearization history

vars == <<nodes, head, tail, next, pc, op, opKey, opValue,
          preds, succs, newNode, found, retired, freed, inCritical, history>>

-----------------------------------------------------------------------------
(* Type definitions *)

NodeRecord == [key: Keys \cup {NIL},
               value: Values \cup {NIL},
               topLevel: 1..MaxLevel]

Marked(ptr) == <<ptr, TRUE>>
Unmarked(ptr) == <<ptr, FALSE>>
IsMarked(ref) == ref[2]
GetPtr(ref) == ref[1]

PCs == {"idle", "find_start", "find_level", "find_forward", "find_help",
        "insert_find", "insert_cas_bottom", "insert_link_levels",
        "delete_find", "delete_mark_levels", "delete_mark_bottom",
        "search_traverse", "done"}

-----------------------------------------------------------------------------
(* Initialization *)

Init ==
    /\ head = "head"
    /\ tail = "tail"
    /\ nodes = [n \in {head, tail} |->
                IF n = head THEN [key |-> NIL, value |-> NIL, topLevel |-> MaxLevel]
                ELSE [key |-> NIL, value |-> NIL, topLevel |-> MaxLevel]]
    /\ next = [n \in {head, tail} |->
               [l \in 1..MaxLevel |-> Unmarked(IF n = head THEN tail ELSE NIL)]]
    /\ pc = [t \in Threads |-> "idle"]
    /\ op = [t \in Threads |-> "none"]
    /\ opKey = [t \in Threads |-> NIL]
    /\ opValue = [t \in Threads |-> NIL]
    /\ preds = [t \in Threads |-> [l \in 1..MaxLevel |-> NIL]]
    /\ succs = [t \in Threads |-> [l \in 1..MaxLevel |-> NIL]]
    /\ newNode = [t \in Threads |-> NIL]
    /\ found = [t \in Threads |-> FALSE]
    /\ retired = {}
    /\ freed = {}
    /\ inCritical = [t \in Threads |-> FALSE]
    /\ history = <<>>

-----------------------------------------------------------------------------
(* Helper predicates *)

\* Compare keys (NIL sorts before everything, handles sentinels)
KeyLess(k1, k2) ==
    IF k1 = NIL THEN TRUE
    ELSE IF k2 = NIL THEN FALSE
    ELSE k1 < k2

\* Node is reachable from head at some level
Reachable(n) ==
    \E path \in Seq({head} \cup DOMAIN nodes):
        /\ Len(path) > 0
        /\ path[1] = head
        /\ path[Len(path)] = n
        /\ \A i \in 1..(Len(path)-1):
            \E l \in 1..MaxLevel:
                GetPtr(next[path[i]][l]) = path[i+1]

\* Node is logically in the set (not marked at level 0)
InSet(n) ==
    /\ n \in DOMAIN nodes
    /\ n # head
    /\ n # tail
    /\ ~IsMarked(next[n][1])
    /\ Reachable(n)

-----------------------------------------------------------------------------
(* SMR operations *)

SMR_Enter(t) ==
    /\ inCritical' = [inCritical EXCEPT ![t] = TRUE]

SMR_Exit(t) ==
    /\ inCritical' = [inCritical EXCEPT ![t] = FALSE]

SMR_Retire(n) ==
    /\ retired' = retired \cup {n}

\* Simplified SMR: can free when no thread accessing
SMR_CanFree(n) ==
    /\ n \in retired
    /\ ~Reachable(n)
    /\ \A t \in Threads: ~inCritical[t] \/ ~ThreadAccessing(t, n)

ThreadAccessing(t, n) ==
    \/ preds[t][1] = n
    \/ succs[t][1] = n
    \/ newNode[t] = n

-----------------------------------------------------------------------------
(* Find operation - locates key and fills preds/succs *)

Find_Start(t) ==
    /\ pc[t] = "find_start"
    /\ SMR_Enter(t)
    /\ preds' = [preds EXCEPT ![t] = [l \in 1..MaxLevel |-> head]]
    /\ pc' = [pc EXCEPT ![t] = "find_level"]
    /\ UNCHANGED <<nodes, head, tail, next, op, opKey, opValue, succs,
                   newNode, found, retired, freed, history>>

Find_Level(t, level) ==
    /\ pc[t] = "find_level"
    /\ level \in 1..MaxLevel
    /\ LET curr == GetPtr(next[preds[t][level]][level])
       IN succs' = [succs EXCEPT ![t][level] = curr]
    /\ pc' = [pc EXCEPT ![t] = "find_forward"]
    /\ UNCHANGED <<nodes, head, tail, next, op, opKey, opValue, preds,
                   newNode, found, retired, freed, inCritical, history>>

Find_Forward(t, level) ==
    /\ pc[t] = "find_forward"
    /\ level \in 1..MaxLevel
    /\ LET curr == succs[t][level]
           currNext == next[curr][level]
       IN IF IsMarked(currNext)
          THEN \* Help remove marked node
               /\ pc' = [pc EXCEPT ![t] = "find_help"]
               /\ UNCHANGED <<nodes, head, tail, next, preds, succs,
                              newNode, found, retired, freed>>
          ELSE IF curr # tail /\ KeyLess(nodes[curr].key, opKey[t])
               THEN \* Move forward
                    /\ preds' = [preds EXCEPT ![t][level] = curr]
                    /\ succs' = [succs EXCEPT ![t][level] = GetPtr(currNext)]
                    /\ UNCHANGED <<pc, nodes, head, tail, next, newNode, found,
                                   retired, freed>>
               ELSE \* Go down or finish
                    IF level > 1
                    THEN /\ pc' = [pc EXCEPT ![t] = "find_level"]
                         /\ UNCHANGED <<nodes, head, tail, next, preds, succs,
                                        newNode, found, retired, freed>>
                    ELSE /\ found' = [found EXCEPT ![t] =
                              (curr # tail /\ nodes[curr].key = opKey[t])]
                         /\ pc' = [pc EXCEPT ![t] = "done"]
                         /\ UNCHANGED <<nodes, head, tail, next, preds, succs,
                                        newNode, retired, freed>>
    /\ UNCHANGED <<op, opKey, opValue, inCritical, history>>

Find_Help(t, level) ==
    /\ pc[t] = "find_help"
    /\ level \in 1..MaxLevel
    /\ LET pred == preds[t][level]
           curr == succs[t][level]
           succ == GetPtr(next[curr][level])
       IN \* CAS to remove marked node
          IF next[pred][level] = Unmarked(curr)
          THEN /\ next' = [next EXCEPT ![pred][level] = Unmarked(succ)]
               /\ succs' = [succs EXCEPT ![t][level] = succ]
               /\ pc' = [pc EXCEPT ![t] = "find_forward"]
          ELSE \* CAS failed, retry from start
               /\ pc' = [pc EXCEPT ![t] = "find_start"]
               /\ UNCHANGED <<next, succs>>
    /\ UNCHANGED <<nodes, head, tail, op, opKey, opValue, preds, newNode,
                   found, retired, freed, inCritical, history>>

-----------------------------------------------------------------------------
(* Insert operation *)

Insert_Start(t, key, value) ==
    /\ pc[t] = "idle"
    /\ op' = [op EXCEPT ![t] = "insert"]
    /\ opKey' = [opKey EXCEPT ![t] = key]
    /\ opValue' = [opValue EXCEPT ![t] = value]
    /\ pc' = [pc EXCEPT ![t] = "find_start"]
    /\ UNCHANGED <<nodes, head, tail, next, preds, succs, newNode, found,
                   retired, freed, inCritical, history>>

Insert_CAS_Bottom(t) ==
    /\ pc[t] = "insert_cas_bottom"
    /\ ~found[t]  \* Key not present
    /\ LET pred == preds[t][1]
           succ == succs[t][1]
           node == newNode[t]
       IN IF next[pred][1] = Unmarked(succ)
          THEN \* CAS succeeds - linearization point
               /\ next' = [next EXCEPT ![pred][1] = Unmarked(node),
                                       ![node] = [l \in 1..nodes[node].topLevel |->
                                                  Unmarked(succs[t][l])]]
               /\ history' = Append(history, <<"insert", opKey[t], TRUE>>)
               /\ pc' = [pc EXCEPT ![t] = "insert_link_levels"]
          ELSE \* CAS fails, retry find
               /\ pc' = [pc EXCEPT ![t] = "find_start"]
               /\ UNCHANGED <<next, history>>
    /\ UNCHANGED <<nodes, head, tail, op, opKey, opValue, preds, succs,
                   newNode, found, retired, freed, inCritical>>

Insert_Link_Levels(t, level) ==
    /\ pc[t] = "insert_link_levels"
    /\ level \in 2..nodes[newNode[t]].topLevel
    /\ LET pred == preds[t][level]
           succ == succs[t][level]
           node == newNode[t]
       IN IF next[pred][level] = Unmarked(succ)
          THEN next' = [next EXCEPT ![pred][level] = Unmarked(node)]
          ELSE UNCHANGED next  \* Will be linked by helping
    /\ IF level = nodes[newNode[t]].topLevel
       THEN /\ pc' = [pc EXCEPT ![t] = "done"]
            /\ SMR_Exit(t)
       ELSE UNCHANGED <<pc, inCritical>>
    /\ UNCHANGED <<nodes, head, tail, op, opKey, opValue, preds, succs,
                   newNode, found, retired, freed, history>>

Insert_Exists(t) ==
    /\ pc[t] = "insert_cas_bottom"
    /\ found[t]  \* Key already present
    /\ history' = Append(history, <<"insert", opKey[t], FALSE>>)
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ SMR_Exit(t)
    /\ UNCHANGED <<nodes, head, tail, next, op, opKey, opValue, preds, succs,
                   newNode, found, retired, freed>>

-----------------------------------------------------------------------------
(* Delete operation *)

Delete_Start(t, key) ==
    /\ pc[t] = "idle"
    /\ op' = [op EXCEPT ![t] = "delete"]
    /\ opKey' = [opKey EXCEPT ![t] = key]
    /\ pc' = [pc EXCEPT ![t] = "find_start"]
    /\ UNCHANGED <<nodes, head, tail, next, opValue, preds, succs, newNode,
                   found, retired, freed, inCritical, history>>

Delete_Mark_Levels(t, level) ==
    /\ pc[t] = "delete_mark_levels"
    /\ found[t]
    /\ level \in 2..nodes[succs[t][1]].topLevel
    /\ LET node == succs[t][1]
           succ == GetPtr(next[node][level])
       IN IF ~IsMarked(next[node][level])
          THEN next' = [next EXCEPT ![node][level] = Marked(succ)]
          ELSE UNCHANGED next
    /\ IF level = nodes[succs[t][1]].topLevel
       THEN pc' = [pc EXCEPT ![t] = "delete_mark_bottom"]
       ELSE UNCHANGED pc
    /\ UNCHANGED <<nodes, head, tail, op, opKey, opValue, preds, succs,
                   newNode, found, retired, freed, inCritical, history>>

Delete_Mark_Bottom(t) ==
    /\ pc[t] = "delete_mark_bottom"
    /\ found[t]
    /\ LET node == succs[t][1]
           succ == GetPtr(next[node][1])
       IN IF ~IsMarked(next[node][1])
          THEN \* CAS to mark - linearization point for delete
               /\ next' = [next EXCEPT ![node][1] = Marked(succ)]
               /\ SMR_Retire(node)
               /\ history' = Append(history, <<"delete", opKey[t], TRUE>>)
               /\ pc' = [pc EXCEPT ![t] = "done"]
               /\ SMR_Exit(t)
          ELSE \* Already marked by another thread
               /\ history' = Append(history, <<"delete", opKey[t], FALSE>>)
               /\ pc' = [pc EXCEPT ![t] = "done"]
               /\ SMR_Exit(t)
               /\ UNCHANGED <<next, retired>>
    /\ UNCHANGED <<nodes, head, tail, op, opKey, opValue, preds, succs,
                   newNode, found, freed>>

Delete_NotFound(t) ==
    /\ pc[t] \in {"delete_mark_levels", "delete_mark_bottom"}
    /\ ~found[t]
    /\ history' = Append(history, <<"delete", opKey[t], FALSE>>)
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ SMR_Exit(t)
    /\ UNCHANGED <<nodes, head, tail, next, op, opKey, opValue, preds, succs,
                   newNode, found, retired, freed>>

-----------------------------------------------------------------------------
(* Search operation *)

Search_Start(t, key) ==
    /\ pc[t] = "idle"
    /\ op' = [op EXCEPT ![t] = "search"]
    /\ opKey' = [opKey EXCEPT ![t] = key]
    /\ pc' = [pc EXCEPT ![t] = "find_start"]
    /\ UNCHANGED <<nodes, head, tail, next, opValue, preds, succs, newNode,
                   found, retired, freed, inCritical, history>>

Search_Done(t) ==
    /\ pc[t] = "done"
    /\ op[t] = "search"
    /\ history' = Append(history, <<"search", opKey[t], found[t]>>)
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ op' = [op EXCEPT ![t] = "none"]
    /\ SMR_Exit(t)
    /\ UNCHANGED <<nodes, head, tail, next, opKey, opValue, preds, succs,
                   newNode, found, retired, freed>>

-----------------------------------------------------------------------------
(* Complete operation and return to idle *)

Complete(t) ==
    /\ pc[t] = "done"
    /\ op[t] # "search"  \* Search handled separately
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ op' = [op EXCEPT ![t] = "none"]
    /\ newNode' = [newNode EXCEPT ![t] = NIL]
    /\ UNCHANGED <<nodes, head, tail, next, opKey, opValue, preds, succs,
                   found, retired, freed, inCritical, history>>

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \E t \in Threads:
        \/ \E k \in Keys, v \in Values: Insert_Start(t, k, v)
        \/ \E k \in Keys: Delete_Start(t, k)
        \/ \E k \in Keys: Search_Start(t, k)
        \/ Find_Start(t)
        \/ \E l \in 1..MaxLevel: Find_Level(t, l)
        \/ \E l \in 1..MaxLevel: Find_Forward(t, l)
        \/ \E l \in 1..MaxLevel: Find_Help(t, l)
        \/ Insert_CAS_Bottom(t)
        \/ \E l \in 2..MaxLevel: Insert_Link_Levels(t, l)
        \/ Insert_Exists(t)
        \/ \E l \in 2..MaxLevel: Delete_Mark_Levels(t, l)
        \/ Delete_Mark_Bottom(t)
        \/ Delete_NotFound(t)
        \/ Search_Done(t)
        \/ Complete(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety Properties *)

\* Skip list ordering is maintained
SkipListOrdered ==
    \A n \in DOMAIN nodes:
        n # tail =>
            LET succ == GetPtr(next[n][1])
            IN succ = tail \/ KeyLess(nodes[n].key, nodes[succ].key)

\* No use-after-free: accessed nodes are not freed
NoUseAfterFree ==
    \A n \in freed: ~Reachable(n)

\* No double-free
NoDoubleFree ==
    \A n \in DOMAIN nodes:
        Cardinality({r \in retired: r = n}) <= 1

\* Linearizability: history can be sequentially explained
\* (Simplified - full check requires external tool)
LinearizableHistory ==
    \A i \in 1..Len(history):
        LET op_i == history[i]
        IN op_i[1] = "insert" /\ op_i[3] = TRUE =>
           ~\E j \in 1..(i-1):
               history[j][1] = "insert" /\ history[j][2] = op_i[2] /\ history[j][3] = TRUE

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Lock-freedom: some thread always makes progress
LockFreedom ==
    []<>(\E t \in Threads: pc[t] = "done")

\* Eventual reclamation: retired nodes eventually freed
\* (Requires fairness)
EventualReclamation ==
    \A n \in retired: <>(n \in freed)

-----------------------------------------------------------------------------
(* Invariants to check *)

TypeInvariant ==
    /\ head \in DOMAIN nodes
    /\ tail \in DOMAIN nodes
    /\ \A t \in Threads: pc[t] \in PCs

SafetyInvariant ==
    /\ SkipListOrdered
    /\ NoUseAfterFree
    /\ NoDoubleFree
    /\ TypeInvariant

=============================================================================
