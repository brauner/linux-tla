------------------------------- MODULE MntNs -------------------------------
(***************************************************************************)
(* The lifetime of one mount namespace N under its three counters and the  *)
(* namespace tree:                                                         *)
(*                                                                         *)
(*   __ns_ref          keeps the struct alive: the nsproxy of every task   *)
(*                     in N, every nsfs inode of N, and the transient      *)
(*                     references of lookups.  The last put tears the      *)
(*                     mounts down (put_mnt_ns()) and frees the namespace   *)
(*                     (free_mnt_ns(): proc inum, ns tree, RCU callback)   *)
(*   __ns_ref_active   "somebody uses it": +1 per attached nsproxy and per *)
(*                     nsfs inode; 0 -> 1 and 1 -> 0 cascade to the owning *)
(*                     user namespace U (kernel/nscommon.c)                 *)
(*   passive           mnt_namespace's own count for {list,stat}mount():   *)
(*                     the initial reference goes with the RCU callback    *)
(*                     after the tree removal, which is what lets          *)
(*                     lookup_mnt_ns() increment it unconditionally        *)
(*                                                                         *)
(* Tasks:                                                                  *)
(*   T   the task living in N: exits (deactivate_nsproxy(): active put,    *)
(*       then put_mnt_ns())                                                *)
(*   F   opens /proc/<T>/ns/mnt (mntns_get() under task_lock,             *)
(*       path_from_stashed(): a new nsfs inode takes the reference and    *)
(*       an active reference, resurrecting N if it was inactive; a        *)
(*       stashed inode is reused), closes it; the dentry stays stashed    *)
(*       until pruned (nsfs_evict(): active put, then the reference)      *)
(*   L   listns(): ns_tree_lookup_rcu() + ns_get_unless_inactive(), then   *)
(*       the put (outside the RCU section since 2ec2aff3c8e2)              *)
(*   Q   NS_MNT_GET_NEXT from the initial namespace: the tree neighbour    *)
(*       under RCU, ns_ref_get(), then an nsfs file on it                  *)
(*   S   statmount(mnt_ns_id): lookup_mnt_ns() (passive++), namespace_sem  *)
(*       shared, mnt_ns_empty(), mnt_ns_release()                          *)
(*   the RCU callback mnt_ns_release_rcu()                                 *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
    FIX_ACTIVE_CHECK,    \* listns() takes only active namespaces (56ea4e86832d)
    FIX_TREE_FIRST,      \* mnt_ns_tree_remove(): out of the tree before call_rcu()
    FIX_CASCADE,         \* the active count cascades to the owner (3a18f809184b)
    FIX_ACTIVE_FIRST,    \* deactivate_nsproxy() drops the active count before the reference
    FIX_EVICT_FIRST,     \* nsfs_evict() drops the active count before the reference
    FIX_PASSIVE_RCU,     \* the initial passive reference goes with an RCU callback (9ea0a46ca2c3 era)
    FIX_PUT_OUTSIDE_RCU  \* listns() drops its reference outside rcu_read_lock() (2ec2aff3c8e2)

T == "T"
F == "F"
L == "L"
Q == "Q"
S == "S"
Tasks == {T, F, L, Q, S}
NoTask == "none"

VARIABLES
    ref,       \* N.__ns_ref
    active,    \* N.__ns_ref_active
    passive,   \* N.passive
    uactive,   \* U.__ns_ref_active: 1 for U's own user, plus 1 while N is active
    intree,    \* N is in the namespace tree
    inum,      \* N's proc inum is allocated
    mounts,    \* N still has its mounts
    freed,     \* N was kfree'd
    inode,     \* an nsfs inode for N exists (holds a reference and an active reference)
    files,     \* open files on that inode
    nsem,      \* namespace_sem exclusive holder
    nsreaders, \* namespace_sem shared holders
    rcu,       \* [Tasks -> BOOLEAN]
    gp,        \* the RCU callback: [on, wait]
    pc,        \* [Tasks -> label]
    ret,       \* [Tasks -> label]: where the teardown returns to
    hold,      \* [Tasks -> BOOLEAN]: the task holds a reference of its own
    bad        \* the first protocol violation seen, or ""

vars == <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files,
          nsem, nsreaders, rcu, gp, pc, ret, hold, bad>>

Readers == {t \in Tasks : rcu[t]}
NsFree == nsem = NoTask /\ nsreaders = {}
Flag(cond, name) == IF bad = "" /\ cond THEN name ELSE bad

(* ---- the counters ------------------------------------------------------- *)

\* __ns_ref_active_get(): a resurrection takes an active reference on the owner
ActiveGet ==
    /\ active' = active + 1
    /\ uactive' = IF active = 0 /\ FIX_CASCADE THEN uactive + 1 ELSE uactive
\* __ns_ref_active_put(): the last one drops the owner's
ActivePut ==
    /\ active' = active - 1
    /\ uactive' = IF active = 1 /\ FIX_CASCADE THEN uactive - 1 ELSE uactive

Init ==
    /\ ref = 1 /\ active = 1 /\ passive = 1 /\ uactive = 2
    /\ intree = TRUE /\ inum = TRUE /\ mounts = TRUE /\ freed = FALSE
    /\ inode = FALSE /\ files = 0
    /\ nsem = NoTask /\ nsreaders = {}
    /\ rcu = [t \in Tasks |-> FALSE]
    /\ gp = [on |-> FALSE, wait |-> {}]
    /\ pc = [t \in Tasks |-> CASE t = T -> "t_run" [] t = F -> "f_open" [] t = L -> "l_lookup"
                               [] t = Q -> "q_lookup" [] t = S -> "s_lookup"]
    /\ ret = [t \in Tasks |-> "done"]
    /\ hold = [t \in Tasks |-> FALSE]
    /\ bad = ""

(* ---- put_mnt_ns() and the teardown ------------------------------------- *)

\* ns_ref_put(): the last reference starts the teardown, in the caller's
\* context; sleeping there is a bug if the caller is inside rcu_read_lock()
RefPut(t, next) ==
    /\ ref' = ref - 1
    /\ IF ref = 1
       THEN /\ pc' = [pc EXCEPT ![t] = "td_nsem"] /\ ret' = [ret EXCEPT ![t] = next]
            /\ bad' = Flag(rcu[t], "sleep in rcu")
       ELSE /\ pc' = [pc EXCEPT ![t] = next] /\ UNCHANGED <<ret, bad>>

\* namespace_lock() for the teardown
TdNsem(t) ==
    /\ pc[t] = "td_nsem" /\ NsFree
    /\ nsem' = t
    /\ bad' = Flag(active > 0, "active without ref")
    /\ pc' = [pc EXCEPT ![t] = "td_tree"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsreaders, rcu, gp, ret, hold>>

\* umount_tree(ns->root, UMOUNT_CONNECTED), then namespace_unlock() drops
\* namespace_sem and frees the namespace: proc inum, then either the tree
\* removal followed by call_rcu(), or the other way round (the mutation)
TdTree(t) ==
    /\ pc[t] = "td_tree"
    /\ mounts' = FALSE
    /\ nsem' = NoTask
    /\ inum' = FALSE
    /\ IF FIX_TREE_FIRST
       THEN intree' = FALSE /\ pc' = [pc EXCEPT ![t] = "td_rcu"]
       ELSE UNCHANGED intree /\ pc' = [pc EXCEPT ![t] = "td_rcu_first"]
    /\ UNCHANGED <<ref, active, passive, uactive, freed, inode, files, nsreaders, rcu, gp, ret, hold, bad>>

\* call_rcu(&ns->ns.ns_rcu, mnt_ns_release_rcu), or mnt_ns_release() at once
TdRcu(t) ==
    /\ pc[t] = "td_rcu"
    /\ IF FIX_PASSIVE_RCU
       THEN gp' = [on |-> TRUE, wait |-> Readers] /\ UNCHANGED <<passive, freed>>
       ELSE passive' = passive - 1 /\ freed' = (passive = 1) /\ UNCHANGED gp
    /\ pc' = [pc EXCEPT ![t] = ret[t]]
    /\ UNCHANGED <<ref, active, uactive, intree, inum, mounts, inode, files, nsem, nsreaders, rcu, ret, hold, bad>>

\* the mutation: call_rcu() first, the tree removal after it
TdRcuFirst(t) ==
    /\ pc[t] = "td_rcu_first"
    /\ gp' = [on |-> TRUE, wait |-> Readers]
    /\ pc' = [pc EXCEPT ![t] = "td_tree_late"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, rcu, ret, hold, bad>>
TdTreeLate(t) ==
    /\ pc[t] = "td_tree_late"
    /\ intree' = FALSE
    /\ pc' = [pc EXCEPT ![t] = ret[t]]
    /\ UNCHANGED <<ref, active, passive, uactive, inum, mounts, freed, inode, files, nsem, nsreaders, rcu, gp, ret, hold, bad>>

Teardown(t) == TdNsem(t) \/ TdTree(t) \/ TdRcu(t) \/ TdRcuFirst(t) \/ TdTreeLate(t)

\* mnt_ns_release_rcu(): the initial passive reference
RcuRelease ==
    /\ gp.on /\ gp.wait = {}
    /\ gp' = [on |-> FALSE, wait |-> {}]
    /\ passive' = passive - 1
    /\ freed' = (passive = 1)
    /\ UNCHANGED <<ref, active, uactive, intree, inum, mounts, inode, files, nsem, nsreaders, rcu, pc, ret, hold, bad>>

RcuOut(t) == rcu' = [rcu EXCEPT ![t] = FALSE] /\ gp' = [gp EXCEPT !.wait = @ \ {t}]

(* ---- the nsfs inode ----------------------------------------------------- *)

\* path_from_stashed() with a reference in hand: a stashed inode is reused
\* and the reference dropped (nsfs_put_data()), else a new inode takes the
\* reference and an active reference (nsfs_init_inode())
Open(t, next) ==
    /\ files' = files + 1
    /\ IF inode
       THEN /\ inode' = inode /\ UNCHANGED <<active, uactive>>
            /\ RefPut(t, next)
       ELSE /\ inode' = TRUE /\ ActiveGet
            /\ pc' = [pc EXCEPT ![t] = next] /\ UNCHANGED <<ref, ret, bad>>
    /\ hold' = [hold EXCEPT ![t] = FALSE]

\* the last close leaves the dentry stashed; nsfs_evict() when it is pruned
Close(t, next) ==
    /\ files' = files - 1
    /\ pc' = [pc EXCEPT ![t] = next]

\* stashed_dentry_prune() -> nsfs_evict(): active put, then ops->put() (the
\* mutation reverses them); the reference put may start the teardown, which
\* runs in the prune context as if it were a task of its own: use S's
\* teardown slot when S is done, else wait
EvictActive ==
    /\ inode /\ files = 0 /\ pc[S] = "done"
    /\ IF FIX_EVICT_FIRST
       THEN ActivePut /\ pc' = [pc EXCEPT ![S] = "ev_ref"] /\ UNCHANGED <<ref, ret, bad>>
       ELSE RefPut(S, "ev_active") /\ UNCHANGED <<active, uactive>>
    /\ UNCHANGED <<passive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, rcu, gp, hold>>
EvictRef ==
    /\ pc[S] = "ev_ref"
    /\ inode' = FALSE
    /\ RefPut(S, "done")
    /\ UNCHANGED <<active, passive, uactive, intree, inum, mounts, freed, files, nsem, nsreaders, rcu, gp, hold>>
EvictActiveLate ==
    /\ pc[S] = "ev_active"
    /\ inode' = FALSE
    /\ ActivePut
    /\ pc' = [pc EXCEPT ![S] = "done"]
    /\ UNCHANGED <<ref, passive, intree, inum, mounts, freed, files, nsem, nsreaders, rcu, gp, ret, hold, bad>>
Evict == EvictActive \/ EvictRef \/ EvictActiveLate

(* ---- T: the task in N ----------------------------------------------------- *)

\* deactivate_nsproxy(): nsproxy_ns_active_put(), then put_mnt_ns()
TExit ==
    /\ pc[T] = "t_run"
    /\ IF FIX_ACTIVE_FIRST
       THEN ActivePut /\ pc' = [pc EXCEPT ![T] = "t_ref"] /\ UNCHANGED <<ref, ret, bad>>
       ELSE RefPut(T, "t_active") /\ UNCHANGED <<active, uactive>>
    /\ UNCHANGED <<passive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, rcu, gp, hold>>
TRef ==
    /\ pc[T] = "t_ref"
    /\ RefPut(T, "done")
    /\ UNCHANGED <<active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, rcu, gp, hold>>
TActiveLate ==
    /\ pc[T] = "t_active"
    /\ ActivePut
    /\ pc' = [pc EXCEPT ![T] = "done"]
    /\ UNCHANGED <<ref, passive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, rcu, gp, ret, hold, bad>>
TaskT == TExit \/ TRef \/ TActiveLate

(* ---- F: /proc/<T>/ns/mnt ------------------------------------------------- *)

\* mntns_get() under task_lock(): only while T still has its nsproxy
FOpen ==
    /\ pc[F] = "f_open"
    /\ IF pc[T] = "t_run"
       THEN /\ ref' = ref + 1
            /\ hold' = [hold EXCEPT ![F] = TRUE]
            /\ pc' = [pc EXCEPT ![F] = "f_stash"]
       ELSE pc' = [pc EXCEPT ![F] = "done"] /\ UNCHANGED <<ref, hold>>
    /\ UNCHANGED <<active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, rcu, gp, ret, bad>>
FStash ==
    /\ pc[F] = "f_stash"
    /\ Open(F, "f_close")
    /\ UNCHANGED <<passive, intree, inum, mounts, freed, nsem, nsreaders, rcu, gp>>
FClose ==
    /\ pc[F] = "f_close"
    /\ Close(F, "done")
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, nsem, nsreaders, rcu, gp, ret, hold, bad>>
TaskF == FOpen \/ FStash \/ FClose

(* ---- L: listns() --------------------------------------------------------- *)

\* ns_tree_lookup_rcu() under rcu_read_lock()
LFind ==
    /\ pc[L] = "l_lookup"
    /\ rcu' = [rcu EXCEPT ![L] = TRUE]
    /\ pc' = [pc EXCEPT ![L] = IF intree THEN "l_get" ELSE "l_miss"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, gp, ret, hold, bad>>
\* ns_get_unless_inactive(): the active count, then refcount_inc_not_zero()
LGet ==
    /\ pc[L] = "l_get"
    /\ IF ref > 0 /\ (active > 0 \/ ~FIX_ACTIVE_CHECK)
       THEN /\ ref' = ref + 1 /\ hold' = [hold EXCEPT ![L] = TRUE]
            /\ bad' = IF bad # "" THEN bad ELSE IF freed THEN "use after free"
                      ELSE IF active = 0 THEN "listed inactive" ELSE ""
            /\ pc' = [pc EXCEPT ![L] = IF FIX_PUT_OUTSIDE_RCU THEN "l_unlock" ELSE "l_put"]
       ELSE /\ bad' = Flag(freed, "use after free")
            /\ pc' = [pc EXCEPT ![L] = "l_miss"] /\ UNCHANGED <<ref, hold>>
    /\ UNCHANGED <<active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, rcu, gp, ret>>
LMiss ==
    /\ pc[L] = "l_miss"
    /\ RcuOut(L)
    /\ pc' = [pc EXCEPT ![L] = "done"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, ret, hold, bad>>
LUnlock ==
    /\ pc[L] = "l_unlock"
    /\ RcuOut(L)
    /\ pc' = [pc EXCEPT ![L] = "l_put"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, ret, hold, bad>>
\* the reference is dropped once the id is copied out
LPut ==
    /\ pc[L] = "l_put"
    /\ hold' = [hold EXCEPT ![L] = FALSE]
    /\ RefPut(L, IF rcu[L] THEN "l_unlock_late" ELSE "done")
    /\ UNCHANGED <<active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, rcu, gp>>
LUnlockLate ==
    /\ pc[L] = "l_unlock_late"
    /\ RcuOut(L)
    /\ pc' = [pc EXCEPT ![L] = "done"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, ret, hold, bad>>
TaskL == LFind \/ LGet \/ LMiss \/ LUnlock \/ LPut \/ LUnlockLate

(* ---- Q: NS_MNT_GET_NEXT --------------------------------------------------- *)

\* get_sequential_mnt_ns(): the tree neighbour under RCU, then ns_ref_get()
QFind ==
    /\ pc[Q] = "q_lookup"
    /\ rcu' = [rcu EXCEPT ![Q] = TRUE]
    /\ pc' = [pc EXCEPT ![Q] = IF intree THEN "q_get" ELSE "q_miss"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, gp, ret, hold, bad>>
QGet ==
    /\ pc[Q] = "q_get"
    /\ RcuOut(Q)
    /\ bad' = Flag(freed, "use after free")
    /\ IF ref > 0
       THEN ref' = ref + 1 /\ hold' = [hold EXCEPT ![Q] = TRUE] /\ pc' = [pc EXCEPT ![Q] = "q_open"]
       ELSE pc' = [pc EXCEPT ![Q] = "done"] /\ UNCHANGED <<ref, hold>>
    /\ UNCHANGED <<active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, ret>>
QMiss ==
    /\ pc[Q] = "q_miss"
    /\ RcuOut(Q)
    /\ pc' = [pc EXCEPT ![Q] = "done"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, ret, hold, bad>>
QOpen ==
    /\ pc[Q] = "q_open"
    /\ Open(Q, "q_close")
    /\ UNCHANGED <<passive, intree, inum, mounts, freed, nsem, nsreaders, rcu, gp>>
QClose ==
    /\ pc[Q] = "q_close"
    /\ Close(Q, "done")
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, nsem, nsreaders, rcu, gp, ret, hold, bad>>
TaskQ == QFind \/ QGet \/ QMiss \/ QOpen \/ QClose

(* ---- S: statmount(mnt_ns_id) ---------------------------------------------- *)

\* lookup_mnt_ns(): ns_tree_lookup_rcu(), then refcount_inc(&passive),
\* both under rcu_read_lock()
SFind ==
    /\ pc[S] = "s_lookup"
    /\ rcu' = [rcu EXCEPT ![S] = TRUE]
    /\ pc' = [pc EXCEPT ![S] = IF intree THEN "s_get" ELSE "s_miss"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, gp, ret, hold, bad>>
SGet ==
    /\ pc[S] = "s_get"
    /\ RcuOut(S)
    /\ passive' = passive + 1
    /\ bad' = Flag(freed \/ passive = 0, "passive inc on a dead namespace")
    /\ pc' = [pc EXCEPT ![S] = "s_sem"]
    /\ UNCHANGED <<ref, active, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, ret, hold>>
SMiss ==
    /\ pc[S] = "s_miss"
    /\ RcuOut(S)
    /\ pc' = [pc EXCEPT ![S] = "done"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, nsreaders, ret, hold, bad>>
\* namespace_sem shared: an emptied namespace is -ENOENT, else the mounts are read
SSem ==
    /\ pc[S] = "s_sem" /\ nsem = NoTask
    /\ nsreaders' = nsreaders \cup {S}
    /\ bad' = Flag(freed, "use after free")
    /\ pc' = [pc EXCEPT ![S] = "s_work"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, rcu, gp, ret, hold>>
SWork ==
    /\ pc[S] = "s_work"
    /\ nsreaders' = nsreaders \ {S}
    /\ bad' = Flag(freed, "use after free")
    /\ pc' = [pc EXCEPT ![S] = "s_release"]
    /\ UNCHANGED <<ref, active, passive, uactive, intree, inum, mounts, freed, inode, files, nsem, rcu, gp, ret, hold>>
\* mnt_ns_release()
SRelease ==
    /\ pc[S] = "s_release"
    /\ passive' = passive - 1
    /\ freed' = (freed \/ passive = 1)
    /\ pc' = [pc EXCEPT ![S] = "done"]
    /\ UNCHANGED <<ref, active, uactive, intree, inum, mounts, inode, files, nsem, nsreaders, rcu, gp, ret, hold, bad>>
TaskS == SFind \/ SGet \/ SMiss \/ SSem \/ SWork \/ SRelease

(* ---- the specification -------------------------------------------------- *)

Settled == /\ \A t \in Tasks : pc[t] = "done"
           /\ ~gp.on /\ ~inode
Next ==
    \/ TaskT \/ TaskF \/ TaskL \/ TaskQ \/ TaskS \/ Evict \/ RcuRelease
    \/ \E t \in Tasks : Teardown(t)
    \/ (Settled /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

(* ---- what is checked ------------------------------------------------------ *)

TypeOK == ref >= 0 /\ active >= 0 /\ passive >= 0 /\ uactive >= 0 /\ files >= 0

\* the counters: an active namespace is referenced; the owner's active
\* count carries exactly one for N while N is active (3a18f809184b)
ActiveRef == active > 0 => ref > 0
OwnerOK == uactive = 1 + (IF active > 0 THEN 1 ELSE 0)

\* the protocol checks recorded by the actions: no use after free, no
\* passive increment on a namespace whose last passive reference is gone,
\* no teardown inside rcu_read_lock(), no reference put that leaves an
\* active count behind, and listns() never hands out a namespace nobody
\* uses (56ea4e86832d)
ProtocolOK == bad = ""

\* once everything is over the namespace is gone: nothing leaks
Reaped == Settled => freed

=============================================================================
