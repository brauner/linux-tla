----------------------------- MODULE LockMount -----------------------------
(***************************************************************************)
(* Mounting on a dentry that is being removed: do_lock_mount() and         *)
(* get_mountpoint() against vfs_rmdir(), d_invalidate() and a lazy umount. *)
(*                                                                         *)
(* Objects: a constant dentry tree of one filesystem (plus the root dentry *)
(* of the filesystem being mounted), the mounts, and per dentry the        *)
(* DCACHE_MOUNTED and DCACHE_CANT_MOUNT flags, whether it is unhashed      *)
(* (unlinked), whether its struct mountpoint exists and who has it pinned  *)
(* (the pinned_mountpoint entries of m_list; the mounts on m_list are the  *)
(* mounts whose mnt_mp is the dentry).                                     *)
(*                                                                         *)
(* Tasks:                                                                  *)
(*   mounters  do_lock_mount() for a fixed path (no MOVE_MOUNT_BENEATH):   *)
(*             where_to_mount() under mount_lock, the temporary mntget(),  *)
(*             inode_lock(), namespace_lock(), the second where_to_mount() *)
(*             and the -EAGAIN retry, cant_mount()/is_mounted(),           *)
(*             get_mountpoint() with lookup_mountpoint()/d_set_mounted()   *)
(*             and the -EBUSY retry, do_add_mount()'s checks,              *)
(*             attach_recursive_mnt(), unlock_mount()                      *)
(*   R         vfs_rmdir(): inode_lock(), is_local_mountpoint() (mounts of *)
(*             its own namespace only), dont_mount(), detach_mounts(),     *)
(*             inode_unlock(), d_delete()                                  *)
(*   D         d_invalidate(): __d_drop() first, then detach_mounts() on   *)
(*             every dentry below with DCACHE_MOUNTED until none is left   *)
(*   U         umount2(MNT_DETACH) of the first new mount                  *)
(*   and namespace_unlock()'s mntput() of every mount put on `unmounted`,  *)
(*   with cleanup_mnt()'s put of the stuck children                        *)
(*                                                                         *)
(* Locks: i_rwsem of the mountpoint dentry, namespace_sem (exclusive, and  *)
(* shared for is_local_mountpoint()), mount_lock (read_seqlock_excl and    *)
(* write sections alike: nobody samples the seqcount here, so a section   *)
(* is one atomic step).  rename_lock and d_lock are inside those steps.    *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
    Dentries, DParent,   \* the dentry forest; a root is its own parent
    NewRoot,             \* the root dentry of the filesystem being mounted
    MntIds,              \* mount ids
    Roots,               \* [ns -> mount id]: the root mount of each namespace
    Mounters,            \* the mounter tasks
    MInfo,               \* [Mounters -> [ns, pm, pd, budget]]: namespace, path, mounts to make
    RmdirTarget,         \* the dentry R removes (NoDentry: no rmdir task)
    InvalTarget,         \* the dentry D invalidates (NoDentry: no such task)
    UmountTarget,        \* the mount U detaches (NoMnt: no such task)
    FIX_RECHECK,         \* do_lock_mount() repeats where_to_mount() under the locks (90006f21b78a)
    FIX_UNLINKED,        \* get_mountpoint() refuses an unlinked dentry that is a mountpoint
    FIX_DONT_MOUNT,      \* do_lock_mount() honours DCACHE_CANT_MOUNT
    FIX_LOOKUP_UNLINKED, \* lookup_mountpoint() finds the mountpoint of an unlinked dentry (1e9c75fb9c47)
    MaxLoops             \* retries of do_lock_mount() and rounds of d_invalidate() a task may take

NoMnt == 0
NoDentry == "none"
NoTask == "none"
R == "R"
D == "D"
U == "U"
Tasks == Mounters \cup (IF RmdirTarget = NoDentry THEN {} ELSE {R})
                  \cup (IF InvalTarget = NoDentry THEN {} ELSE {D})
                  \cup (IF UmountTarget = NoMnt THEN {} ELSE {U})
Namespaces == DOMAIN Roots

VARIABLES
    mnt,       \* [MntIds -> [alive, freed, parent, mp, root, hashed, ns, umount, count]]
    den,       \* [Dentries -> [unhashed, mounted, cant, mp, pins]]
    ilock,     \* [Dentries -> task or NoTask]: i_rwsem
    nsem,      \* holder of namespace_sem (exclusive) or NoTask
    nsreaders, \* tasks holding namespace_sem shared
    pc,        \* [Tasks -> label]
    ret,       \* [Tasks -> label]: where detach_mounts() returns to
    wm,        \* [Tasks -> [m, d]]: where_to_mount()'s answer
    tmp,       \* [Tasks -> mount or NoMnt]: do_lock_mount()'s temporary reference
    err,       \* [Tasks -> string]
    dt,        \* [Tasks -> dentry]: detach_mounts()'s target
    todo,      \* [Tasks -> SUBSET MntIds]: the `unmounted` list namespace_unlock() will put
    budget,    \* [Tasks -> Nat]: mounts a mounter still makes
    made,      \* [Tasks -> SUBSET MntIds]: the mounts a mounter made
    loops,     \* [Tasks -> Nat]: -EAGAIN retries of a mounter, detach rounds of D
    bad        \* the first structural check that failed, or ""

vars == <<mnt, den, ilock, nsem, nsreaders, pc, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>

(* ---- the tree --------------------------------------------------------- *)

Live == {x \in MntIds : mnt[x].alive}
HasParent(x) == mnt[x].parent # x
\* __lookup_mnt(): the hashed mount at (p, d)
LookupMnt(p, d) ==
    LET S == {x \in Live : mnt[x].hashed /\ mnt[x].parent = p /\ mnt[x].mp = d /\ x # p}
    IN IF S = {} THEN NoMnt ELSE CHOOSE x \in S : TRUE
\* topmost_overmount(): follow the mounts on the root dentry
RECURSIVE Topmost(_)
Topmost(x) == LET o == LookupMnt(x, mnt[x].root) IN IF o = NoMnt THEN x ELSE Topmost(o)
\* the mounts on the dentry's m_list: attached there, or unmounted but still connected
Mlist(d) == {x \in Live : HasParent(x) /\ mnt[x].mp = d}
Subtree(x) == {y \in Live : y = x \/ (HasParent(y) /\ mnt[y].parent = x)}   \* depth 2 suffices here
Children(x) == {y \in Live : y # x /\ HasParent(y) /\ mnt[y].parent = x}
RECURSIVE Ancestors(_)
Ancestors(d) == IF DParent[d] = d THEN {} ELSE {DParent[d]} \cup Ancestors(DParent[d])
Below(d) == {e \in Dentries : e = d \/ d \in Ancestors(e)}

\* where_to_mount(path, beneath = false)
WhereToMount(pm, pd) ==
    LET q == LookupMnt(pm, pd)
    IN IF q = NoMnt THEN [m |-> pm, d |-> pd]
       ELSE LET t == Topmost(q) IN [m |-> t, d |-> mnt[t].root]

FreeId == CHOOSE x \in MntIds \ Live : \A y \in MntIds \ Live : x <= y

(* ---- mutators --------------------------------------------------------- *)

\* __umount_mnt(): out of the hash, its own parent, off m_list; the
\* mountpoint goes when nothing is left on it (maybe_free_mountpoint)
UmountMnt(mt, dn, x) ==
    LET d == mt[x].mp
        mt1 == [mt EXCEPT ![x].hashed = FALSE, ![x].parent = x, ![x].mp = mt[x].root]
        left == {y \in MntIds : mt1[y].alive /\ mt1[y].parent # y /\ mt1[y].mp = d}
        dn1 == IF left = {} /\ dn[d].pins = {} /\ dn[d].mp
               THEN [dn EXCEPT ![d].mounted = FALSE, ![d].mp = FALSE] ELSE dn
    IN [mt |-> mt1, dn |-> dn1]

\* __umount_mnt() over a set
RECURSIVE UmountAll(_, _, _)
UmountAll(mt, dn, S) ==
    IF S = {} THEN [mt |-> mt, dn |-> dn]
    ELSE LET y == CHOOSE y \in S : TRUE
             r == UmountMnt(mt, dn, y)
         IN UmountAll(r.mt, r.dn, S \ {y})

\* umount_tree(x, how): MNT_UMOUNT and out of the namespace for the tree;
\* x itself is disconnected (its parent stays mounted); children are
\* disconnected unless how = "connected"
UmountTree(mt, dn, x, how) ==
    LET tree == {y \in MntIds : mt[y].alive /\ (y = x \/ (mt[y].parent = x /\ y # x))}
        mt1 == [y \in MntIds |-> IF y \in tree THEN [mt[y] EXCEPT !.umount = TRUE, !.ns = 0] ELSE mt[y]]
        disc == IF how = "connected" THEN {} ELSE tree \ {x}
        r == UmountAll(mt1, dn, {x} \cup disc)
    IN [mt |-> r.mt, dn |-> r.dn, put |-> {x} \cup disc]

\* mntput(): the last reference frees the mount; cleanup_mnt() then
\* disconnects and puts the stuck children (the unmounted ones still
\* connected to it)
RECURSIVE Put(_, _, _)
Put(mt, dn, S) ==
    IF S = {} THEN [mt |-> mt, dn |-> dn]
    ELSE LET x == CHOOSE x \in S : TRUE
             c == mt[x].count - 1
         IN IF c > 0
            THEN Put([mt EXCEPT ![x].count = c], dn, S \ {x})
            ELSE LET stuck == {y \in MntIds : mt[y].alive /\ y # x /\ mt[y].parent = x}
                     mt1 == [mt EXCEPT ![x].count = 0, ![x].alive = FALSE, ![x].freed = TRUE,
                                       ![x].hashed = FALSE]
                     r == UmountAll(mt1, dn, stuck)
                 IN Put(r.mt, r.dn, (S \ {x}) \cup stuck)

(* ---- init ------------------------------------------------------------- *)

Fresh == [alive |-> FALSE, freed |-> FALSE, parent |-> 0, mp |-> NoDentry, root |-> NoDentry,
          hashed |-> FALSE, ns |-> 0, umount |-> FALSE, count |-> 0]
RootDentry == CHOOSE d \in Dentries : DParent[d] = d /\ d # NewRoot
\* the root mount of each namespace is referenced by the namespace and by
\* the path of every mounter starting on it
InitCount(x) == 1 + Cardinality({t \in Mounters : MInfo[t].pm = x})

Init ==
    /\ mnt = [x \in MntIds |-> IF \E n \in Namespaces : Roots[n] = x
                                THEN [Fresh EXCEPT !.alive = TRUE, !.parent = x, !.mp = RootDentry,
                                                   !.root = RootDentry, !.hashed = FALSE,
                                                   !.ns = CHOOSE n \in Namespaces : Roots[n] = x,
                                                   !.count = InitCount(x)]
                                ELSE Fresh]
    /\ den = [d \in Dentries |-> [unhashed |-> FALSE, mounted |-> FALSE, cant |-> FALSE,
                                  mp |-> FALSE, pins |-> {}]]
    /\ ilock = [d \in Dentries |-> NoTask]
    /\ nsem = NoTask
    /\ nsreaders = {}
    /\ pc = [t \in Tasks |-> IF t \in Mounters THEN "m_start"
                             ELSE IF t = R THEN "r_ilock" ELSE IF t = D THEN "d_drop" ELSE "u_nsem"]
    /\ ret = [t \in Tasks |-> "done"]
    /\ wm = [t \in Tasks |-> [m |-> NoMnt, d |-> NoDentry]]
    /\ tmp = [t \in Tasks |-> NoMnt]
    /\ err = [t \in Tasks |-> ""]
    /\ dt = [t \in Tasks |-> NoDentry]
    /\ todo = [t \in Tasks |-> {}]
    /\ budget = [t \in Tasks |-> IF t \in Mounters THEN MInfo[t].budget ELSE 0]
    /\ made = [t \in Tasks |-> {}]
    /\ loops = [t \in Tasks |-> 0]
    /\ bad = ""

(* ---- shared pieces ---------------------------------------------------- *)

NsFree == nsem = NoTask /\ nsreaders = {}

\* namespace_unlock(): drop namespace_sem, then mntput() everything on
\* `unmounted` (the puts take mount_lock, one atomic step each here)
NsUnlock(t, next) ==
    /\ nsem' = NoTask
    /\ LET r == Put(mnt, den, todo[t])
       IN mnt' = r.mt /\ den' = r.dn
    /\ todo' = [todo EXCEPT ![t] = {}]
    /\ pc' = [pc EXCEPT ![t] = next]

\* __detach_mounts(dentry) under namespace_sem and mount_lock: every
\* mount on m_list goes; unmounted-but-connected ones are just
\* disconnected, mounted ones are unmounted with their trees connected
RECURSIVE DetachAll(_, _, _, _)
DetachAll(mt, dn, put, S) ==
    IF S = {} THEN [mt |-> mt, dn |-> dn, put |-> put]
    ELSE LET x == CHOOSE x \in S : TRUE
             r == IF mt[x].umount
                  THEN LET u == UmountMnt(mt, dn, x) IN [mt |-> u.mt, dn |-> u.dn, put |-> {x}]
                  ELSE UmountTree(mt, dn, x, "connected")
         IN DetachAll(r.mt, r.dn, put \cup r.put, S \ {x})

DetachBody(t) ==
    LET d == dt[t]
        found == den[d].mp /\ (FIX_LOOKUP_UNLINKED \/ ~den[d].unhashed)
    IN IF ~found
       THEN UNCHANGED <<mnt, den, todo>>
       ELSE LET dn0 == [den EXCEPT ![d].pins = @ \cup {t}]     \* the pin of lookup_mountpoint()
                r == DetachAll(mnt, dn0, {}, Mlist(d))
                dn1 == [r.dn EXCEPT ![d].pins = @ \ {t}]        \* unpin_mountpoint()
                left == {y \in MntIds : r.mt[y].alive /\ r.mt[y].parent # y /\ r.mt[y].mp = d}
                dn2 == IF left = {} /\ dn1[d].pins = {} /\ dn1[d].mp
                       THEN [dn1 EXCEPT ![d].mounted = FALSE, ![d].mp = FALSE] ELSE dn1
            IN /\ mnt' = r.mt /\ den' = dn2
               /\ todo' = [todo EXCEPT ![t] = @ \cup r.put]

\* detach_mounts(dentry): the inline test, then __detach_mounts()
DmStart(t) ==
    /\ pc[t] = "dm_start"
    /\ pc' = [pc EXCEPT ![t] = IF den[dt[t]].mounted THEN "dm_nsem" ELSE ret[t]]
    /\ UNCHANGED <<mnt, den, ilock, nsem, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>
DmNsem(t) ==
    /\ pc[t] = "dm_nsem" /\ NsFree
    /\ nsem' = t
    /\ pc' = [pc EXCEPT ![t] = "dm_body"]
    /\ UNCHANGED <<mnt, den, ilock, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>
DmBody(t) ==
    /\ pc[t] = "dm_body"
    /\ DetachBody(t)
    /\ pc' = [pc EXCEPT ![t] = "dm_unlock"]
    /\ UNCHANGED <<ilock, nsem, nsreaders, ret, wm, tmp, err, dt, budget, made, loops, bad>>
DmUnlock(t) ==
    /\ pc[t] = "dm_unlock"
    /\ NsUnlock(t, ret[t])
    /\ UNCHANGED <<ilock, nsreaders, ret, wm, tmp, err, dt, budget, made, loops, bad>>
Detach(t) == DmStart(t) \/ DmNsem(t) \/ DmBody(t) \/ DmUnlock(t)

(* ---- the mounter -------------------------------------------------------- *)

Pm(t) == MInfo[t].pm
Pd(t) == MInfo[t].pd

MStart(t) ==
    /\ pc[t] = "m_start"
    /\ pc' = [pc EXCEPT ![t] = IF budget[t] = 0 THEN "done" ELSE "lm_w1"]
    /\ UNCHANGED <<mnt, den, ilock, nsem, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>

\* where_to_mount() under read_seqlock_excl, with mntget()/dget() of the
\* answer when it is not the path's own mount
LmW1(t) ==
    /\ pc[t] = "lm_w1"
    /\ LET w == WhereToMount(Pm(t), Pd(t))
       IN /\ wm' = [wm EXCEPT ![t] = w]
          /\ IF w.m # Pm(t)
             THEN tmp' = [tmp EXCEPT ![t] = w.m] /\ mnt' = [mnt EXCEPT ![w.m].count = @ + 1]
             ELSE tmp' = [tmp EXCEPT ![t] = NoMnt] /\ UNCHANGED mnt
    /\ pc' = [pc EXCEPT ![t] = "lm_ilock"]
    /\ UNCHANGED <<den, ilock, nsem, nsreaders, ret, err, dt, todo, budget, made, loops, bad>>

LmIlock(t) ==
    /\ pc[t] = "lm_ilock" /\ ilock[wm[t].d] = NoTask
    /\ ilock' = [ilock EXCEPT ![wm[t].d] = t]
    /\ pc' = [pc EXCEPT ![t] = "lm_nsem"]
    /\ UNCHANGED <<mnt, den, nsem, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>

LmNsem(t) ==
    /\ pc[t] = "lm_nsem" /\ NsFree
    /\ nsem' = t
    /\ pc' = [pc EXCEPT ![t] = "lm_w2"]
    /\ UNCHANGED <<mnt, den, ilock, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>

\* the second where_to_mount() and the checks: -EAGAIN if the place moved,
\* -ENOENT if the dentry is dead or the path's mount is unmounted
LmW2(t) ==
    /\ pc[t] = "lm_w2"
    /\ LET w == WhereToMount(Pm(t), Pd(t))
           moved == FIX_RECHECK /\ w # wm[t]
           dead == (FIX_DONT_MOUNT /\ den[wm[t].d].cant) \/ mnt[Pm(t)].ns = 0
       IN IF moved THEN err' = [err EXCEPT ![t] = "EAGAIN"] /\ pc' = [pc EXCEPT ![t] = "lm_fail"]
          ELSE IF dead THEN err' = [err EXCEPT ![t] = "ENOENT"] /\ pc' = [pc EXCEPT ![t] = "lm_fail"]
          ELSE UNCHANGED err /\ pc' = [pc EXCEPT ![t] = "gm_start"]
    /\ UNCHANGED <<mnt, den, ilock, nsem, nsreaders, ret, wm, tmp, dt, todo, budget, made, loops, bad>>

\* get_mountpoint(): an existing mountpoint is looked up (and refused on
\* an unlinked dentry), else d_set_mounted() races for the flag
GmStart(t) ==
    /\ pc[t] = "gm_start"
    /\ LET d == wm[t].d
       IN IF den[d].mounted
          THEN IF FIX_UNLINKED /\ den[d].unhashed
               THEN err' = [err EXCEPT ![t] = "ENOENT"] /\ pc' = [pc EXCEPT ![t] = "lm_fail"]
               ELSE UNCHANGED err /\ pc' = [pc EXCEPT ![t] = "gm_lookup"]
          ELSE UNCHANGED err /\ pc' = [pc EXCEPT ![t] = "gm_set"]
    /\ UNCHANGED <<mnt, den, ilock, nsem, nsreaders, ret, wm, tmp, dt, todo, budget, made, loops, bad>>

\* lookup_mountpoint() under mount_lock: pin it, or fall through to
\* d_set_mounted() when the flag was set by a mountpoint that is gone
GmLookup(t) ==
    /\ pc[t] = "gm_lookup"
    /\ LET d == wm[t].d
       IN IF den[d].mp /\ (FIX_LOOKUP_UNLINKED \/ ~den[d].unhashed)
          THEN den' = [den EXCEPT ![d].pins = @ \cup {t}] /\ pc' = [pc EXCEPT ![t] = "lm_ok"]
          ELSE UNCHANGED den /\ pc' = [pc EXCEPT ![t] = "gm_set"]
    /\ UNCHANGED <<mnt, ilock, nsem, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>

\* d_set_mounted() under rename_lock and the d_locks
GmSet(t) ==
    /\ pc[t] = "gm_set"
    /\ LET d == wm[t].d
       IN IF \E a \in Ancestors(d) : den[a].unhashed /\ DParent[a] # a
          THEN err' = [err EXCEPT ![t] = "ENOENT"] /\ pc' = [pc EXCEPT ![t] = "lm_fail"] /\ UNCHANGED den
          ELSE IF den[d].unhashed /\ DParent[d] # d
          THEN err' = [err EXCEPT ![t] = "ENOENT"] /\ pc' = [pc EXCEPT ![t] = "lm_fail"] /\ UNCHANGED den
          ELSE IF den[d].mounted
          THEN UNCHANGED <<err, den>> /\ pc' = [pc EXCEPT ![t] = "gm_lookup"]    \* -EBUSY: goto mountpoint
          ELSE UNCHANGED err /\ den' = [den EXCEPT ![d].mounted = TRUE] /\ pc' = [pc EXCEPT ![t] = "gm_create"]
    /\ UNCHANGED <<mnt, ilock, nsem, nsreaders, ret, wm, tmp, dt, todo, budget, made, loops, bad>>

\* the new struct mountpoint goes into the hash under mount_lock, pinned
GmCreate(t) ==
    /\ pc[t] = "gm_create"
    /\ den' = [den EXCEPT ![wm[t].d].mp = TRUE, ![wm[t].d].pins = @ \cup {t}]
    /\ pc' = [pc EXCEPT ![t] = "lm_ok"]
    /\ UNCHANGED <<mnt, ilock, nsem, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>

\* do_lock_mount() failed: unlock, drop the temporaries, retry on -EAGAIN
LmFail(t) ==
    /\ pc[t] = "lm_fail"
    /\ nsem' = NoTask
    /\ ilock' = [ilock EXCEPT ![wm[t].d] = NoTask]
    /\ IF tmp[t] # NoMnt
       THEN LET r == Put(mnt, den, {tmp[t]}) IN mnt' = r.mt /\ den' = r.dn
       ELSE UNCHANGED <<mnt, den>>
    /\ tmp' = [tmp EXCEPT ![t] = NoMnt]
    /\ IF err[t] = "EAGAIN"
       THEN pc' = [pc EXCEPT ![t] = "lm_w1"] /\ UNCHANGED budget /\ loops' = [loops EXCEPT ![t] = @ + 1]
       ELSE pc' = [pc EXCEPT ![t] = "m_start"] /\ budget' = [budget EXCEPT ![t] = @ - 1] /\ UNCHANGED loops
    /\ UNCHANGED <<nsreaders, ret, wm, err, dt, todo, made, bad>>

\* do_lock_mount() succeeded: the temporaries are dropped under
\* namespace_sem ("refcounts won't reach zero")
LmOk(t) ==
    /\ pc[t] = "lm_ok"
    /\ IF tmp[t] # NoMnt
       THEN LET r == Put(mnt, den, {tmp[t]}) IN mnt' = r.mt /\ den' = r.dn
       ELSE UNCHANGED <<mnt, den>>
    /\ tmp' = [tmp EXCEPT ![t] = NoMnt]
    /\ pc' = [pc EXCEPT ![t] = "am_check"]
    /\ UNCHANGED <<ilock, nsem, nsreaders, ret, wm, err, dt, todo, budget, made, loops, bad>>

\* do_add_mount(): the parent must be in the caller's namespace
AmCheck(t) ==
    /\ pc[t] = "am_check"
    /\ IF mnt[wm[t].m].ns # MInfo[t].ns
       THEN err' = [err EXCEPT ![t] = "EINVAL"] /\ pc' = [pc EXCEPT ![t] = "um_unlock"]
       ELSE UNCHANGED err /\ pc' = [pc EXCEPT ![t] = "am_attach"]
    /\ UNCHANGED <<mnt, den, ilock, nsem, nsreaders, ret, wm, tmp, dt, todo, budget, made, loops, bad>>

\* attach_recursive_mnt() under mount_lock: the new mount is hashed at the
\* pinned place; the checks record what must be true at that moment
AmAttach(t) ==
    /\ pc[t] = "am_attach"
    /\ LET x == FreeId
           p == wm[t].m
           d == wm[t].d
           mt1 == [mnt EXCEPT ![x] = [Fresh EXCEPT !.alive = TRUE, !.parent = p, !.mp = d, !.root = NewRoot,
                                                     !.hashed = TRUE, !.ns = MInfo[t].ns, !.count = 1]]
           \* the place must be free, the parent mounted, the dentry a live mountpoint
           \* with this task's pin, and the mount must be what the path now shows
           checks == /\ LookupMnt(p, d) = NoMnt
                     /\ mnt[p].ns # 0 /\ ~mnt[p].umount
                     /\ den[d].mounted /\ den[d].mp /\ t \in den[d].pins
                     /\ ~den[d].cant
       IN /\ mnt' = mt1
          /\ made' = [made EXCEPT ![t] = @ \cup {x}]
          /\ bad' = IF bad = "" /\ ~checks THEN "attach" ELSE bad
    /\ budget' = [budget EXCEPT ![t] = @ - 1]
    /\ err' = [err EXCEPT ![t] = ""]
    /\ pc' = [pc EXCEPT ![t] = "um_unlock"]
    /\ UNCHANGED <<den, ilock, nsem, nsreaders, ret, wm, tmp, dt, todo, loops>>

\* unlock_mount(): inode_unlock(), unpin under mount_lock (the mountpoint
\* goes if nothing is left on it), namespace_unlock()
UmUnlock(t) ==
    /\ pc[t] = "um_unlock"
    /\ LET d == wm[t].d
           dn1 == [den EXCEPT ![d].pins = @ \ {t}]
           dn2 == IF Mlist(d) = {} /\ dn1[d].pins = {} /\ dn1[d].mp
                  THEN [dn1 EXCEPT ![d].mounted = FALSE, ![d].mp = FALSE] ELSE dn1
       IN den' = dn2
    /\ ilock' = [ilock EXCEPT ![wm[t].d] = NoTask]
    /\ nsem' = NoTask
    /\ pc' = [pc EXCEPT ![t] = "m_start"]
    /\ UNCHANGED <<mnt, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>

Mount(t) == MStart(t) \/ LmW1(t) \/ LmIlock(t) \/ LmNsem(t) \/ LmW2(t) \/ GmStart(t) \/ GmLookup(t)
            \/ GmSet(t) \/ GmCreate(t) \/ LmFail(t) \/ LmOk(t) \/ AmCheck(t) \/ AmAttach(t) \/ UmUnlock(t)

(* ---- vfs_rmdir() -------------------------------------------------------- *)

RIlock ==
    /\ pc[R] = "r_ilock" /\ ilock[RmdirTarget] = NoTask
    /\ ilock' = [ilock EXCEPT ![RmdirTarget] = R]
    /\ pc' = [pc EXCEPT ![R] = "r_local"]
    /\ UNCHANGED <<mnt, den, nsem, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>

\* is_local_mountpoint(): d_mountpoint() first, then the mounts of R's
\* namespace under namespace_sem shared
RLocal ==
    /\ pc[R] = "r_local" /\ nsem = NoTask
    /\ LET d == RmdirTarget
           busy == den[d].mounted /\ \E x \in Live : mnt[x].ns = 1 /\ HasParent(x) /\ mnt[x].mp = d /\ mnt[x].hashed
       IN IF busy
          THEN ilock' = [ilock EXCEPT ![d] = NoTask] /\ err' = [err EXCEPT ![R] = "EBUSY"]
               /\ pc' = [pc EXCEPT ![R] = "done"] /\ UNCHANGED <<den, dt, ret>>
          ELSE \* ->rmdir(), S_DEAD, dont_mount(), then detach_mounts()
               /\ den' = [den EXCEPT ![d].cant = TRUE]
               /\ dt' = [dt EXCEPT ![R] = d] /\ ret' = [ret EXCEPT ![R] = "r_unlock"]
               /\ pc' = [pc EXCEPT ![R] = "dm_start"] /\ UNCHANGED <<ilock, err>>
    /\ UNCHANGED <<mnt, nsem, nsreaders, wm, tmp, todo, budget, made, loops, bad>>

\* inode_unlock(), then d_delete() without it: the dentry is unhashed
RUnlock ==
    /\ pc[R] = "r_unlock"
    /\ ilock' = [ilock EXCEPT ![RmdirTarget] = NoTask]
    /\ pc' = [pc EXCEPT ![R] = "r_delete"]
    /\ UNCHANGED <<mnt, den, nsem, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>
RDelete ==
    /\ pc[R] = "r_delete"
    /\ den' = [den EXCEPT ![RmdirTarget].unhashed = TRUE]
    /\ pc' = [pc EXCEPT ![R] = "done"]
    /\ UNCHANGED <<mnt, ilock, nsem, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>

Rmdir == RIlock \/ RLocal \/ RUnlock \/ RDelete

(* ---- d_invalidate() ----------------------------------------------------- *)

DDrop ==
    /\ pc[D] = "d_drop"
    /\ IF den[InvalTarget].unhashed
       THEN pc' = [pc EXCEPT ![D] = "done"] /\ UNCHANGED den
       ELSE den' = [den EXCEPT ![InvalTarget].unhashed = TRUE] /\ pc' = [pc EXCEPT ![D] = "d_find"]
    /\ UNCHANGED <<mnt, ilock, nsem, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>

\* d_walk(find_submount): a dentry below with DCACHE_MOUNTED, if any
DFind ==
    /\ pc[D] = "d_find"
    /\ LET V == {v \in Below(InvalTarget) : den[v].mounted}
       IN IF V = {}
          THEN pc' = [pc EXCEPT ![D] = "done"] /\ UNCHANGED <<dt, ret>>
          ELSE /\ dt' = [dt EXCEPT ![D] = CHOOSE v \in V : TRUE]
               /\ ret' = [ret EXCEPT ![D] = "d_find"]
               /\ pc' = [pc EXCEPT ![D] = "dm_start"]
    /\ loops' = [loops EXCEPT ![D] = IF pc'[D] = "dm_start" THEN @ + 1 ELSE @]
    /\ UNCHANGED <<mnt, den, ilock, nsem, nsreaders, wm, tmp, err, todo, budget, made, bad>>

Inval == DDrop \/ DFind

(* ---- umount2(MNT_DETACH) ------------------------------------------------ *)

\* umount2(MNT_DETACH) once the target is mounted; nothing to do if the
\* mounters are done without it
UNsem ==
    /\ pc[U] = "u_nsem"
    /\ IF mnt[UmountTarget].alive /\ mnt[UmountTarget].hashed /\ mnt[UmountTarget].ns # 0
       THEN NsFree /\ nsem' = U /\ pc' = [pc EXCEPT ![U] = "u_tree"]
       ELSE (\A t \in Mounters : pc[t] = "done") /\ UNCHANGED nsem /\ pc' = [pc EXCEPT ![U] = "done"]
    /\ UNCHANGED <<mnt, den, ilock, nsreaders, ret, wm, tmp, err, dt, todo, budget, made, loops, bad>>
UTree ==
    /\ pc[U] = "u_tree"
    /\ LET r == UmountTree(mnt, den, UmountTarget, "detach")
       IN mnt' = r.mt /\ den' = r.dn /\ todo' = [todo EXCEPT ![U] = r.put]
    /\ pc' = [pc EXCEPT ![U] = "u_unlock"]
    /\ UNCHANGED <<ilock, nsem, nsreaders, ret, wm, tmp, err, dt, budget, made, loops, bad>>
UUnlock ==
    /\ pc[U] = "u_unlock"
    /\ NsUnlock(U, "done")
    /\ UNCHANGED <<ilock, nsreaders, ret, wm, tmp, err, dt, budget, made, loops, bad>>
Umount == UNsem \/ UTree \/ UUnlock

(* ---- the specification ------------------------------------------------- *)

TaskStep(t) ==
    \/ Detach(t)
    \/ (t \in Mounters /\ Mount(t))
    \/ (t = R /\ Rmdir)
    \/ (t = D /\ Inval)
    \/ (t = U /\ Umount)

Settled == \A t \in Tasks : pc[t] = "done"
Next == (\E t \in Tasks : TaskStep(t)) \/ (Settled /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ \A t \in Tasks : WF_vars(TaskStep(t))
SpecWFNext == Init /\ [][Next]_vars /\ WF_vars(Next)
SpecNoFair == Init /\ [][Next]_vars

(* ---- what is checked --------------------------------------------------- *)

TypeOK ==
    /\ nsem \in Tasks \cup {NoTask}
    /\ \A x \in MntIds : mnt[x].count >= 0
    /\ \A t \in Tasks : tmp[t] # NoMnt => mnt[tmp[t]].alive

\* at most one hashed mount per (parent, mountpoint) (ffdc52fbbd58)
HashUnique == \A x, y \in Live : (mnt[x].hashed /\ mnt[y].hashed /\ x # y)
                                 => (mnt[x].parent # mnt[y].parent \/ mnt[x].mp # mnt[y].mp)

\* DCACHE_MOUNTED is set exactly while the struct mountpoint exists, except
\* for the window between d_set_mounted() and the insertion; the mountpoint
\* exists exactly while something is on its m_list
MountpointOK ==
    \A d \in Dentries :
        /\ den[d].mp => den[d].mounted
        /\ den[d].mounted => (den[d].mp \/ \E t \in Mounters : pc[t] = "gm_create" /\ wm[t].d = d)
        /\ den[d].mp => (Mlist(d) # {} \/ den[d].pins # {})
        /\ (Mlist(d) # {} \/ den[d].pins # {}) => den[d].mp

\* a pinned_mountpoint exists only while its owner holds namespace_sem, so
\* __detach_mounts() never mistakes one for a mount
PinsUnderNsem == \A d \in Dentries : \A t \in den[d].pins : nsem = t

\* nobody keeps a pointer to a freed mount
NoUAF == /\ \A t \in Tasks : tmp[t] # NoMnt => ~mnt[tmp[t]].freed
         /\ \A t \in Mounters : pc[t] \in {"lm_ok", "am_check", "am_attach"} => ~mnt[wm[t].m].freed
         /\ \A x \in Live : HasParent(x) => ~mnt[mnt[x].parent].freed

\* the structural checks at attach time
AttachOK == bad = ""

\* every mount a mounter made was visible at its path when it was made
\* (checked at attach through `bad`), and after everything settled no
\* mount is left hashed on an unlinked or dead dentry
NoOrphans == Settled => \A x \in Live : mnt[x].hashed /\ mnt[x].ns # 0 => ~den[mnt[x].mp].unhashed /\ ~den[mnt[x].mp].cant

\* the loops terminate: do_lock_mount()'s -EAGAIN retry and d_invalidate()'s
\* rounds stay within the budget (a bounded stand-in for liveness; TLC's
\* fairness evaluation stalls on the d_invalidate() loop)
Bounded == \A t \in Tasks : loops[t] <= MaxLoops
AllDone == <>Settled

=============================================================================
