----------------------------- MODULE MountOps -----------------------------
(***************************************************************************)
(* The mount syscalls of fs/namespace.c as one atomic step each, on top of *)
(* the algorithms of Propagation.  Family A of the plan: everything here    *)
(* runs under namespace_sem in the kernel, so there is nothing to           *)
(* interleave; the state space is the set of reachable mount               *)
(* configurations, and every step checks the operational result against   *)
(* the declarative rules.                                                  *)
(*                                                                         *)
(* Actions and the kernel entry points they stand for:                     *)
(*   NewMount      do_new_mount()/do_add_mount()/graft_tree(); with auto   *)
(*                 the finish_automount() variant (MNT_SHRINKABLE + expiry)*)
(*   Bind          do_loopback()/__do_loopback() (bind and rbind)          *)
(*   Move          do_move_mount(), attached source or anonymous root,     *)
(*                 MOVE_MOUNT_BENEATH via can_move_mount_beneath()         *)
(*   Umount        do_umount(): plain, MNT_DETACH, MNT_EXPIRE;             *)
(*                 shrink_submounts()/select_submounts()                   *)
(*   ChangeType    do_change_type()                                        *)
(*   SetGroup      do_set_group() (MOVE_MOUNT_SET_GROUP)                   *)
(*   CloneNs       copy_mnt_ns() (CLONE_NEWNS, CLONE_EMPTY_MNTNS)          *)
(*   OpenTree      open_tree(OPEN_TREE_CLONE)/get_detached_copy()          *)
(*   Fsmount       fsmount() into an anonymous namespace                   *)
(*   OpenTreeNs    open_tree(OPEN_TREE_NAMESPACE)/fsmount(FSMOUNT_NAMESPACE)*)
(*                 via create_new_namespace()/lock_mount_exact()           *)
(*   Setns         mntns_install()                                         *)
(*   CloseFd       __fput() -> dissolve_on_fput()                          *)
(*   PivotRoot     path_pivot_root() + chroot_fs_refs()                    *)
(*   Rmdir         vfs_rmdir() -> is_local_mountpoint()/detach_mounts()/   *)
(*                 __detach_mounts()                                       *)
(*   Expire        mark_mounts_for_expiry()                                *)
(*   Touch, Chdir, OpenFd, Chroot   path walks and the references they     *)
(*                 leave (mntput() clearing mnt_expiry_mark, fs->pwd,      *)
(*                 open files, fs->root)                                   *)
(*   the epilogue of every action: namespace_unlock()'s final mntput()s   *)
(*                 (a detached mount nobody references goes, its stuck     *)
(*                 children with it: mntput_no_expire_slowpath/cleanup_mnt)*)
(*                 and put_mnt_ns() when a namespace loses its last user   *)
(*                                                                         *)
(* Toggles:                                                                *)
(*   FIX_PUT_MNT_NS_DISCONNECT  put_mnt_ns() uses umount_tree(root, 0)     *)
(*                 (the staged revert of 0342482a4d15); FALSE keeps the    *)
(*                 tree connected (UMOUNT_CONNECTED)                       *)
(*   CHECK_DOC     also check the documentation where it disagrees with    *)
(*                 the code: sharedsubtree.rst 5f for umount and 5g for    *)
(*                 unbindable mounts of a cloned namespace                 *)
(***************************************************************************)
EXTENDS Propagation

CONSTANTS
    Procs,          \* processes, each in one user namespace
    ProcUser,       \* [Procs -> Nat], 1 is the initial user namespace
    InitSb,         \* the superblock of the initial nullfs root
    RootSb,         \* the superblock of the real rootfs mounted on it
    MountSbs,       \* superblocks a mount(2) may bring in
    MaxOps,         \* free syscalls per behaviour, after the prelude
    MaxFds,         \* open files per process
    Prelude,        \* a sequence of scripted syscalls that builds the starting topology
    FIX_PUT_MNT_NS_DISCONNECT,
    CHECK_DOC

InitUser == 1

VARIABLES
    mt,       \* the mount table
    nst,      \* namespaces: [alive, root, user, anon, origin]
    pr,       \* processes: [ns, root, cwd, fds, nsfds]
    ddead,    \* dentries removed by rmdir
    covers,   \* per process: every (parent, mountpoint) a MNT_LOCKED mount hid from it
    ops,      \* syscalls so far
    ok,       \* every declarative check so far held
    hist,     \* what happened, for the witnesses and the traces
    reach,    \* per process: the positions its walks can reach (a cache)
    step      \* the next step of the prelude, or past its end

vars == <<mt, nst, pr, ddead, covers, ops, ok, hist, reach, step>>

InPrelude == step <= Len(Prelude)

Pos == [mnt: MntIds, dentry: Dentries]
Fd == [mnt: MntIds, dentry: Dentries, tree: BOOLEAN]
NsRec == [alive: BOOLEAN, root: MntIds \cup {NoMnt}, user: Nat, anon: BOOLEAN, origin: NsIds \cup {NoNs}]
ProcRec == [ns: NsIds, root: Pos, cwd: Pos, fds: SUBSET Fd, nsfds: SUBSET NsIds]
Kinds == {"none", "mount", "bind", "move", "umount", "chtype", "setgroup", "clonens",
          "opentree", "fsmount", "opentreens", "setns", "closefd", "pivot", "rmdir",
          "expire", "walk"}
HistRec == [kind: Kinds, tucked: BOOLEAN, locktransfer: BOOLEAN, reparented: BOOLEAN,
            slaveofslave: BOOLEAN, skippedmaster: BOOLEAN, lockedkept: BOOLEAN,
            connected: BOOLEAN, syncbusy: BOOLEAN, busymismatch: BOOLEAN, putns: BOOLEAN, expired: BOOLEAN,
            trimmed: BOOLEAN]

HistNone == [kind |-> "none", tucked |-> FALSE, locktransfer |-> FALSE, reparented |-> FALSE,
             slaveofslave |-> FALSE, skippedmaster |-> FALSE, lockedkept |-> FALSE,
             connected |-> FALSE, syncbusy |-> FALSE, busymismatch |-> FALSE, putns |-> FALSE, expired |-> FALSE,
             trimmed |-> FALSE]

NsAnon == [n \in NsIds \cup {NoNs} |-> IF n = NoNs THEN FALSE ELSE nst[n].anon]
NsUser == [n \in NsIds \cup {NoNs} |-> IF n = NoNs THEN 0 ELSE nst[n].user]

(* ---- references -------------------------------------------------------- *)

\* the processes' references on a mount: fs->root, fs->pwd, open files
Refs(m) == Cardinality({p \in Procs : pr[p].root.mnt = m})
           + Cardinality({p \in Procs : pr[p].cwd.mnt = m})
           + Cardinality(UNION {{f \in pr[p].fds : f.mnt = m} : p \in Procs})
RefTable == [m \in MntIds |-> Refs(m)]

NsUsers(n) == {p \in Procs : pr[p].ns = n} \cup {p \in Procs : n \in pr[p].nsfds}

(* ---- the epilogue: final mntput()s and put_mnt_ns() -------------------- *)

\* namespace_unlock()'s mntput() of a disconnected mount, and the cascade
\* of mntput_no_expire_slowpath()/cleanup_mnt() over its stuck children:
\* a detached, unmounted mount that nobody references is freed; each
\* connected child is unhashed and put in turn.
Unreferenced(t, refs, m) ==
    t[m].alive /\ t[m].umount /\ t[m].parent = NoMnt /\ refs[m] = 0
RECURSIVE Collect(_, _)
Collect(t, refs) ==
    LET dead == {m \in Live(t) : Unreferenced(t, refs, m)}
    IN IF dead = {} THEN t
       ELSE LET m == CHOOSE x \in dead : TRUE
                kids == t[m].children
                t1 == [x \in MntIds |-> IF Contains(kids, x)
                                        THEN [t[x] EXCEPT !.parent = NoMnt, !.mp = t[x].root,
                                                          !.hashed = FALSE]
                                        ELSE t[x]]
                t2 == [t1 EXCEPT ![m] = Dead(m)]
            IN Collect(t2, refs)

\* put_mnt_ns(): the last user of a namespace is gone
PutNs(t, n) ==
    UmountTree(t, nst[n].root,
               IF FIX_PUT_MNT_NS_DISCONNECT THEN UmountHow(FALSE, FALSE, FALSE)
               ELSE UmountHow(FALSE, FALSE, TRUE)).mt

LockedPositions(t) == {[mnt |-> t[x].parent, mp |-> t[x].mp] : x \in {y \in Live(t) : t[y].locked /\ t[y].parent # NoMnt}}

(* ---- path walks: what a process can reach ------------------------------ *)

\* handle_mounts(): step onto a dentry and cross whatever is mounted there
Cross(t, m, d) ==
    LET c == LookupMnt(t, m, d)
    IN IF c = NoMnt THEN [mnt |-> m, dentry |-> d]
       ELSE LET top == Topmost(t, c) IN [mnt |-> top, dentry |-> t[top].root]

\* a component below the current position
Down(t, dd, pos) ==
    {Cross(t, pos.mnt, c) : c \in {x \in DChildren(pos.dentry) : x \notin dd}}

\* choose_mountpoint(): climb to the first parent whose mountpoint is not
\* that parent's root, stopping at the process root; returns the parent
\* and the mountpoint, or NoMnt when the walk is at the root of everything
RECURSIVE Climb(_, _, _)
Climb(t, m, root) ==
    IF ~HasParent(t, m) THEN [p |-> NoMnt, d |-> t[m].root]
    ELSE LET p == t[m].parent
             d == t[m].mp
         IN IF root.mnt = p /\ root.dentry = d THEN [p |-> NoMnt, d |-> d]
            ELSE IF d # t[p].root THEN [p |-> p, d |-> d]
            ELSE Climb(t, p, root)

\* follow_dotdot(): ".." from pos with the process root root; a walk that
\* fails path_connected() stays where it is
Up(t, pos, root) ==
    IF pos = root THEN pos
    ELSE IF pos.dentry = t[pos.mnt].root
    THEN LET c == Climb(t, pos.mnt, root)
         IN IF c.p = NoMnt THEN pos
            ELSE LET parent == DParent[c.d]
                 IN IF IsSubdir(parent, t[c.p].root) THEN Cross(t, c.p, parent) ELSE pos
    ELSE LET parent == DParent[pos.dentry]
         IN IF IsSubdir(parent, t[pos.mnt].root) THEN Cross(t, pos.mnt, parent) ELSE pos

Anchors(p) == {pr[p].root, pr[p].cwd} \cup {[mnt |-> f.mnt, dentry |-> f.dentry] : f \in pr[p].fds}

RECURSIVE ReachClosure(_, _, _, _)
ReachClosure(t, dd, root, S) ==
    LET next == S \cup UNION {Down(t, dd, x) : x \in S} \cup {Up(t, x, root) : x \in S}
    IN IF next = S THEN S ELSE ReachClosure(t, dd, root, next)
Reachable(p) == reach[p]
ReachNow(p) == ReachClosure(mt, ddead, pr[p].root, Anchors(p))

\* positions on a mount of the process's namespace (check_mnt())
InNs(p, pos) == mt[pos.mnt].ns = pr[p].ns
\* the root of a mount, as a path (path_mounted())
IsMountRoot(pos) == pos.dentry = mt[pos.mnt].root

Hides(c, pos) == c.mnt = pos.mnt /\ IsSubdir(pos.dentry, c.mp)
Hidden(p, pos) == \E c \in covers[p] : Hides(c, pos)

(* ---- permissions ------------------------------------------------------- *)

\* ns_capable(ns->user_ns, CAP_SYS_ADMIN) for a process in userns u
Capable(u, n) == u = InitUser \/ nst[n].user = u
MayMount(p) == Capable(ProcUser[p], pr[p].ns)
\* may_change_propagation(): mounted, and admin in the owning user namespace
MayChangePropagation(p, m) == mt[m].ns # NoNs /\ Capable(ProcUser[p], mt[m].ns)
\* check_anonymous_mnt()
CheckAnonymousMnt(p, m) ==
    LET n == mt[m].ns
    IN n # NoNs /\ nst[n].anon /\ (nst[n].origin = NoNs \/ nst[n].origin = pr[p].ns)
\* may_copy_tree()
MayCopyTree(p, m) == InNs(p, [mnt |-> m, dentry |-> mt[m].root]) \/ (mt[m].ns # NoNs /\ CheckAnonymousMnt(p, m))
\* may_use_mount()
MayUseMount(p, m) == mt[m].ns = pr[p].ns \/ CheckAnonymousMnt(p, m)
\* anon_ns_root()
AnonNsRoot(m) == mt[m].ns # NoNs /\ nst[mt[m].ns].anon /\ nst[mt[m].ns].root = m

HasLockedChildren(t, m, d) ==
    \E c \in ToSet(t[m].children) : IsSubdir(t[c].mp, d) /\ t[c].locked
TreeContainsUnbindable(t, m) == \E x \in Subtree(t, m) : t[x].unbind
\* propagation_would_overmount(from, to, mp)
PropagationWouldOvermount(t, from, to, d) ==
    /\ t[from].shared
    /\ t[to].root = d
    /\ \E m \in ToSet(<<to>> \o MasterChain(t, to)) : Peers(t, from, m)

(* ---- the common tail of every action ---------------------------------- *)

\* namespace_unlock() and what follows it, then put_mnt_ns() for every
\* namespace without users; the covers ghost follows the locked mounts
\* uncover: positions whose lock the kernel lifted itself (propagate_mount_unlock())
FinishUncover(t, ns1, pr1, dd, hrec, uncover) ==
    LET refs == [m \in MntIds |->
                    Cardinality({p \in Procs : pr1[p].root.mnt = m})
                    + Cardinality({p \in Procs : pr1[p].cwd.mnt = m})
                    + Cardinality(UNION {{f \in pr1[p].fds : f.mnt = m} : p \in Procs})]
        t1 == Collect(t, refs)
        \* namespaces nobody uses any more: put_mnt_ns()
        gone == {n \in NsIds : ns1[n].alive /\ ~ns1[n].anon /\ n # 1 /\
                   {p \in Procs : pr1[p].ns = n} = {} /\ {p \in Procs : n \in pr1[p].nsfds} = {}}
        n0 == IF gone = {} THEN NoNs ELSE CHOOSE x \in gone : \A y \in gone : x <= y
        t2 == IF n0 = NoNs THEN t1 ELSE Collect(PutNs(t1, n0), refs)
        ns2 == [n \in NsIds |-> IF n = n0 THEN [ns1[n] EXCEPT !.alive = FALSE] ELSE ns1[n]]
        \* an anonymous namespace whose root left it is gone as well
        ns3 == [n \in NsIds |-> IF ns2[n].alive /\ ns2[n].anon /\
                                    (~t2[ns2[n].root].alive \/ t2[ns2[n].root].ns # n)
                                 THEN [ns2[n] EXCEPT !.alive = FALSE] ELSE ns2[n]]
        \* references to freed mounts are gone (the kernel holds them; the
        \* model only ever frees unreferenced mounts, so this is a no-op)
        \* a lock hides a position from a process only if the process could
        \* not reach it when the lock appeared; a cover dies with its mount
        Anchors1(p) == {pr1[p].root, pr1[p].cwd} \cup {[mnt |-> f.mnt, dentry |-> f.dentry] : f \in pr1[p].fds}
        Reach1(p) == ReachClosure(t2, dd, pr1[p].root, Anchors1(p))
        newc == LockedPositions(t2) \ UNION {covers[p] : p \in Procs}
    IN /\ mt' = t2
       /\ nst' = ns3
       /\ pr' = pr1
       /\ ddead' = dd
       /\ covers' = [p \in Procs |->
                       {c \in covers[p] : t2[c.mnt].alive /\ c \notin uncover}
                       \cup {c \in newc : c \notin uncover /\ ~\E pos \in Reach1(p) : Hides(c, pos)}]
       /\ ops' = IF InPrelude THEN ops ELSE ops + 1
       /\ step' = step + 1
       /\ hist' = [hrec EXCEPT !.putns = hrec.putns \/ n0 # NoNs]
       /\ reach' = [p \in Procs |-> Reach1(p)]

Finish(t, ns1, pr1, dd, hrec) == FinishUncover(t, ns1, pr1, dd, hrec, {})

Budget == IF InPrelude THEN TRUE ELSE ops < MaxOps

RoomFor(k) == Cardinality(FreeIds(mt)) >= k
NsRoom(n) == \E x \in NsIds : ~nst[x].alive

(* ---- mount(2) ---------------------------------------------------------- *)

\* do_lock_mount()/where_to_mount(): a mount on a position goes on top of
\* the topmost overmount already there (a process root or cwd may sit
\* beneath one); with `beneath` it goes where the topmost overmount of
\* the path's mount is attached.
WhereToMount(pos, beneath) ==
    IF beneath
    THEN LET m == Topmost(mt, pos.mnt) IN [parent |-> mt[m].parent, d |-> mt[m].mp, top |-> m]
    ELSE LET q == LookupMnt(mt, pos.mnt, pos.dentry)
         IN IF q # NoMnt THEN LET m == Topmost(mt, q) IN [parent |-> m, d |-> mt[m].root, top |-> NoMnt]
            ELSE [parent |-> pos.mnt, d |-> pos.dentry, top |-> NoMnt]
\* cant_mount() and is_mounted() of the path's mount; a dead dentry cannot
\* be mounted on
CanMountOn(R, pos) == pos \in R /\ WhereToMount(pos, FALSE).d \notin ddead /\ mt[pos.mnt].ns # NoNs

NewMount(p, R, pos, sb, auto) ==
    /\ Budget
    /\ MayMount(p)
    /\ CanMountOn(R, pos)
    /\ LET w == WhereToMount(pos, FALSE)
           P == w.parent
           d == w.d
       IN /\ mt[P].ns = pr[p].ns                                   \* check_mnt(parent)
          /\ ~(mt[P].sb = sb /\ mt[P].root = d)                     \* -EBUSY
          /\ RoomFor(1 + Cardinality(ExpectedReceivers(mt, NsAnon, P, d)))
          /\ LET id == NewId(mt)
                 t0 == [mt EXCEPT ![id] = [Fresh(id, sb, SbRoot[sb]) EXCEPT !.shrink = auto, !.onexp = auto]]
                 r == AttachRecursive(t0, NsUser, NsAnon, ProcUser[p], id, P, d)
             IN /\ r.err \in {"", "NULLDEREF"}
                /\ ok' = (ok /\ r.err = "" /\ CopiesOK(t0, r.mt, NsAnon, P, d, id))
                /\ Finish(IF r.err = "" THEN r.mt ELSE mt, nst, pr, ddead,
                    [HistNone EXCEPT !.kind = "mount",
                        !.tucked = LookupMnt(mt, P, d) # NoMnt,
                        !.slaveofslave = \E x \in Live(r.mt) \ Live(mt) :
                                            r.mt[x].master # NoMnt /\ r.mt[r.mt[x].master].master # NoMnt
                                            /\ r.mt[x].master \notin Live(mt)])

(* ---- bind / rbind ------------------------------------------------------ *)

Bind(p, R, src, dst, rec) ==
    /\ Budget
    /\ MayMount(p)
    /\ src \in R
    /\ CanMountOn(R, dst)
    /\ LET w == WhereToMount(dst, FALSE)
           P == w.parent
           d == w.d
       IN /\ mt[P].ns = pr[p].ns
          /\ ~mt[src.mnt].unbind
          /\ MayCopyTree(p, src.mnt)
          /\ rec \/ ~HasLockedChildren(mt, src.mnt, src.dentry)
          /\ RoomFor(Cardinality(Subtree(mt, src.mnt)) *
                     (1 + Cardinality(ExpectedReceivers(mt, NsAnon, P, d))))
          /\ LET flag == CL_NONE
                 c == IF rec THEN CopyTree(mt, src.mnt, src.dentry, flag)
                      ELSE LET r == CloneMnt(mt, src.mnt, src.dentry, flag) IN [mt |-> r.mt, id |-> r.id, err |-> ""]
             IN /\ c.err = ""
                /\ LET r == AttachRecursive(c.mt, NsUser, NsAnon, ProcUser[p], c.id, P, d)
                   IN /\ r.err \in {"", "NULLDEREF"}
                      /\ ok' = (ok /\ r.err = "" /\ CopiesOK(c.mt, r.mt, NsAnon, P, d, c.id))
                      /\ Finish(IF r.err = "" THEN r.mt ELSE mt, nst, pr, ddead,
                                [HistNone EXCEPT !.kind = "bind",
                                    !.tucked = LookupMnt(mt, P, d) # NoMnt,
                                    !.slaveofslave = \E x \in Live(r.mt) \ Live(c.mt) :
                                                        r.mt[x].master # NoMnt /\ r.mt[r.mt[x].master].master # NoMnt
                                                        /\ r.mt[x].master \notin Live(c.mt),
                                    !.skippedmaster = \E n \in ExpectedReceivers(mt, NsAnon, P, d) :
                                                        mt[n].master # NoMnt /\
                                                        mt[n].master \notin ExpectedReceivers(mt, NsAnon, P, d)
                                                        /\ mt[n].master \notin PeerGroup(mt, P)])

(* ---- move_mount(2) ----------------------------------------------------- *)

Move(p, R, src, dst, beneath) ==
    /\ Budget
    /\ MayMount(p)
    /\ src \in R /\ IsMountRoot(src)
    /\ CanMountOn(R, dst)
    /\ LET old == src.mnt
           w == WhereToMount(dst, beneath)
           X == w.top
           P == w.parent
           d == w.d
       IN /\ IF beneath THEN IsMountRoot(dst) /\ HasParent(mt, X) ELSE TRUE
          /\ IF InNs(p, src)
             THEN /\ HasParent(mt, old) /\ ~mt[old].locked
                  /\ ~mt[mt[old].parent].shared
                  /\ mt[P].ns = pr[p].ns
             ELSE /\ AnonNsRoot(old)
                  /\ mt[old].ns # mt[P].ns
                  /\ MayUseMount(p, P)
          /\ IF beneath                                    \* can_move_mount_beneath()
             THEN /\ mt[old].over = NoMnt
                  /\ ~MountIsAncestor(mt, X, old)
                  /\ ~PropagationWouldOvermount(mt, P, X, d)
                  /\ ~(InNs(p, src) /\ PropagationWouldOvermount(mt, P, old, d))
             ELSE TRUE
          /\ ~(mt[P].shared /\ TreeContainsUnbindable(mt, old))
          /\ ~MountIsAncestor(mt, old, P)
          /\ RoomFor(Cardinality(Subtree(mt, old)) * Cardinality(ExpectedReceivers(mt, NsAnon, P, d)))
          /\ LET r == AttachRecursive(mt, NsUser, NsAnon, ProcUser[p], old, P, d)
             IN /\ r.err \in {"", "NULLDEREF"}
                /\ ok' = (ok /\ r.err = "" /\ CopiesOK(mt, r.mt, NsAnon, P, d, old))
                /\ Finish(IF r.err = "" THEN r.mt ELSE mt, nst, pr, ddead,
                          [HistNone EXCEPT !.kind = "move",
                              !.tucked = beneath \/ LookupMnt(mt, P, d) # NoMnt,
                              !.locktransfer = beneath /\ mt[X].locked])

(* ---- umount(2) --------------------------------------------------------- *)

\* select_submounts(): shrinkable leaves that are not busy, depth first
RECURSIVE Select(_, _, _)
Select(t, refs, m) ==
    LET kids == t[m].children
        Pick(c) == IF ~t[c].shrink THEN <<>>
                   ELSE IF t[c].children # <<>> THEN Select(t, refs, c)
                   ELSE IF ~PropagateMountBusy(t, refs, c, 0) THEN <<c>> ELSE <<>>
    IN Concat([i \in 1..Len(kids) |-> Pick(kids[i])])

RECURSIVE UmountEach(_, _, _)
UmountEach(t, s, how) ==
    IF s = <<>> THEN t
    ELSE LET m == Head(s)
             t1 == IF t[m].umount THEN t ELSE UmountTree(t, m, how).mt
         IN UmountEach(t1, Tail(s), how)

\* shrink_submounts()
ShrinkSubmounts(t, refs, m) == UmountEach(t, Select(t, refs, m), UmountHow(TRUE, TRUE, FALSE))

Victims(tb, ta) == {x \in Live(tb) : ~tb[x].umount /\ ta[x].umount}

\* the covers propagate_mount_unlock() lifts when m is unmounted: the
\* cognates of m that were locked (5d88457eb5b8: if it is fine to unmount
\* here, it is fine to reveal the mountpoint everywhere it propagated to)
Unlocked(t, m) ==
    LET u == PropagateMountUnlock(t, m)
    IN {[mnt |-> t[x].parent, mp |-> t[x].mp] : x \in {y \in Live(t) : t[y].locked /\ ~u[y].locked}}

\* one umount_tree() with propagation, checked against the specification
CheckedUmount(tb, ta, m) ==
    /\ UmountVictimsOK(tb, ta, ExpectedVictims(tb, m))
    /\ CHECK_DOC => Victims(tb, ta) = DocUmountVictims(tb, m)

Umount(p, R, m, mode) ==
    /\ Budget
    /\ MayMount(p)
    /\ [mnt |-> m, dentry |-> mt[m].root] \in R
    /\ mt[m].over = NoMnt                             \* LOOKUP_MOUNTPOINT ends on the top
    /\ mt[m].ns = pr[p].ns
    /\ ~mt[m].locked
    /\ HasParent(mt, m)
    /\ ~(mode # "lazy" /\ pr[p].root.mnt = m)        \* do_umount_root(): no tree change
    /\ IF mode = "expire"
       THEN /\ mt[m].children = <<>> /\ Refs(m) = 0
            /\ IF ~mt[m].expmark
               THEN /\ ok' = ok
                    /\ Finish([mt EXCEPT ![m].expmark = TRUE], nst, pr, ddead,
                              [HistNone EXCEPT !.kind = "umount"])
               ELSE LET r == UmountTree(mt, m, UmountHow(TRUE, TRUE, FALSE))
                    IN /\ ok' = (ok /\ CheckedUmount(mt, r.mt, m))
                       /\ FinishUncover(r.mt, nst, pr, ddead,
                                 [HistNone EXCEPT !.kind = "umount", !.expired = TRUE], Unlocked(mt, m))
       ELSE IF mode = "lazy"
       THEN LET r == UmountTree(mt, m, UmountHow(FALSE, TRUE, FALSE))
            IN /\ ok' = (ok /\ CheckedUmount(mt, r.mt, m))
               /\ FinishUncover(r.mt, nst, pr, ddead,
                         [HistNone EXCEPT !.kind = "umount",
                             !.connected = \E x \in Victims(mt, r.mt) : r.mt[x].parent # NoMnt,
                             !.lockedkept = \E x \in Cognates(mt, Subtree(mt, m)) :
                                              mt[x].locked /\ ~r.mt[x].umount /\ mt[x].parent # NoMnt
                                              /\ ~r.mt[mt[x].parent].umount,
                             !.reparented = \E x \in Live(mt) : ~r.mt[x].umount /\ r.mt[x].alive
                                              /\ r.mt[x].parent # mt[x].parent], Unlocked(mt, m))
       ELSE LET t1 == ShrinkSubmounts(mt, RefTable, m)
                busy == PropagateMountBusy(t1, RefTable, m, 1)
                mism == BusyMirror(t1, RefTable, m) # BusyExact(t1, RefTable, m)
            IN IF busy
               THEN /\ ok' = ok
                    /\ Finish(t1, nst, pr, ddead, [HistNone EXCEPT !.kind = "umount", !.busymismatch = mism])
               ELSE LET r == UmountTree(t1, m, UmountHow(TRUE, TRUE, FALSE))
                    IN /\ ok' = (ok /\ CheckedUmount(t1, r.mt, m))
                       /\ FinishUncover(r.mt, nst, pr, ddead,
                                 [HistNone EXCEPT !.kind = "umount",
                                     !.busymismatch = mism,
                                     !.syncbusy = \E x \in Victims(t1, r.mt) : Refs(x) > 0,
                                     !.reparented = \E x \in Live(t1) : ~r.mt[x].umount /\ r.mt[x].alive
                                                      /\ r.mt[x].parent # t1[x].parent,
                                     !.trimmed = \E x \in Cognates(t1, Subtree(t1, m)) :
                                                   ~r.mt[x].umount /\ t1[x].children # <<>>], Unlocked(t1, m))

(* ---- mount --make-* ---------------------------------------------------- *)

TypeAfter(before, type) ==
    IF type = "shared" THEN "shared"
    ELSE IF type = "private" THEN "private"
    ELSE IF type = "unbindable" THEN "unbindable"
    ELSE \* make-slave: shared with peers -> slave, alone -> private, else unchanged
         IF before = "shared" THEN "slave-or-private"
         ELSE IF before = "shared+slave" THEN "slave" ELSE before
TypeOf(t, m) ==
    IF t[m].unbind THEN "unbindable"
    ELSE IF t[m].shared /\ t[m].master # NoMnt THEN "shared+slave"
    ELSE IF t[m].shared THEN "shared"
    ELSE IF t[m].master # NoMnt THEN "slave" ELSE "private"

RECURSIVE ChangeEach(_, _, _)
ChangeEach(t, s, type) ==
    IF s = <<>> THEN t ELSE ChangeEach(ChangeMntPropagation(t, Head(s), type), Tail(s), type)

\* make-slave over the set S, one mount at a time: x ends up with a master
\* iff a peer of x outside S survives or x's master chain leaves S; a peer
\* group that lies entirely inside S has nobody left to be a slave of
RECURSIVE KeepsMaster(_, _, _)
KeepsMaster(t, x, S) ==
    \/ t[x].shared /\ \E y \in PeerGroup(t, x) \ {x} : y \notin S
    \/ /\ t[x].master # NoMnt
       /\ (t[x].master \notin S \/ KeepsMaster(t, t[x].master, S))

ChangeType(p, R, m, type, rec) ==
    /\ Budget
    /\ [mnt |-> m, dentry |-> mt[m].root] \in R
    /\ MayChangePropagation(p, m)
    /\ LET s == IF rec THEN Preorder(mt, m) ELSE <<m>>
           t0 == IF type = "shared" THEN InventGroupIds(mt, m, rec) ELSE mt
           t1 == ChangeEach(t0, s, type)
           TableOK == \A x \in ToSet(s) :
               LET exp == TypeAfter(TypeOf(mt, x), type)
                   got == TypeOf(t1, x)
               IN IF exp \in {"slave-or-private", "slave"}
                  THEN got = IF KeepsMaster(mt, x, ToSet(s)) THEN "slave" ELSE "private"
                  ELSE IF exp = "shared" /\ TypeOf(mt, x) \in {"slave", "shared+slave"}
                  THEN got = "shared+slave"
                  ELSE got = exp
       IN /\ ok' = (ok /\ TableOK)
          /\ Finish(t1, nst, pr, ddead, [HistNone EXCEPT !.kind = "chtype"])

\* MOVE_MOUNT_SET_GROUP
SetGroup(p, R, from, to) ==
    /\ Budget
    /\ from # to
    /\ [mnt |-> from, dentry |-> mt[from].root] \in R
    /\ [mnt |-> to, dentry |-> mt[to].root] \in R
    /\ MayChangePropagation(p, from) /\ MayChangePropagation(p, to)
    /\ mt[from].sb = mt[to].sb
    /\ IsSubdir(mt[to].root, mt[from].root)
    /\ ~HasLockedChildren(mt, from, mt[to].root)
    /\ ~mt[to].shared /\ mt[to].master = NoMnt
    /\ FIX_SET_GROUP_UNBINDABLE => ~mt[to].unbind       \* F4: an unbindable target slips through
    /\ mt[from].shared \/ mt[from].master # NoMnt
    /\ LET t1 == IF mt[from].master # NoMnt
                 THEN SlaveAddBehind(SetMaster(mt, to, mt[from].master), from, to) ELSE mt
           t2 == IF mt[from].shared
                 THEN SetMntShared(RingInsertAfter(SetGid(t1, to, mt[from].gid), from, to), to) ELSE t1
       IN /\ ok' = (ok /\ (mt[from].shared => Peers(t2, from, to)) /\ t2[to].master = mt[from].master)
          /\ Finish(t2, nst, pr, ddead, [HistNone EXCEPT !.kind = "setgroup"])

(* ---- namespaces -------------------------------------------------------- *)

\* the copy of x in a tree copied in next_mnt() order
CopyOf(told, oldroot, tnew, newroot, x) ==
    LET po == Preorder(told, oldroot)
        pn == Preorder(tnew, newroot)
    IN pn[Index(po, x)]

\* sharedsubtree.rst 5g against clone_mnt() with CL_SLAVE across user
\* namespaces; DocUnbindable is 5g as written
CloneNsOK(told, oldroot, tnew, newroot, userdiff) ==
    LET po == Preorder(told, oldroot)
        pn == Preorder(tnew, newroot)
    IN /\ Len(po) = Len(pn)
       /\ \A i \in 1..Len(po) :
            LET a == po[i]
                b == pn[i]
            IN /\ tnew[b].sb = told[a].sb /\ tnew[b].root = told[a].root
               /\ ~userdiff => (/\ (told[a].shared => Peers(tnew, a, b))
                                /\ (~told[a].shared => tnew[b].gid = 0)
                                /\ tnew[b].master = told[a].master)
               /\ userdiff => (/\ tnew[b].gid = 0
                               /\ (told[a].shared => tnew[b].master = a)
                               /\ (~told[a].shared => tnew[b].master = told[a].master)
                               /\ ((i > 1 /\ ~tnew[b].onexp) => tnew[b].locked))
               /\ CHECK_DOC => (tnew[b].unbind = told[a].unbind)

CloneNs(p, empty) ==
    /\ Budget
    /\ NsRoom(0)
    /\ ~nst[pr[p].ns].anon
    /\ LET old == pr[p].ns
           oldroot == nst[old].root
           userdiff == ProcUser[p] # nst[old].user
           flag == CL(userdiff, FALSE, FALSE, ~empty, ~empty)
       IN /\ RoomFor(IF empty THEN 1 ELSE Cardinality(Subtree(mt, oldroot)))
          /\ LET n == CHOOSE x \in NsIds : ~nst[x].alive
                 c == IF empty THEN LET r == CloneMnt(mt, oldroot, mt[oldroot].root, flag)
                                    IN [mt |-> r.mt, id |-> r.id, err |-> ""]
                      ELSE CopyTree(mt, oldroot, mt[oldroot].root, flag)
             IN /\ c.err = ""
                /\ LET t1 == IF userdiff THEN LockMntTree(c.mt, c.id) ELSE c.mt
                       t2 == [x \in MntIds |-> IF x \in Subtree(t1, c.id)
                                               THEN [t1[x] EXCEPT !.ns = n, !.attached = TRUE] ELSE t1[x]]
                       \* copy_mnt_ns() switches fs->root and fs->pwd to the copies of
                       \* mounts it finds in the tree; a reference elsewhere stays
                       Map(pos) == IF empty THEN [mnt |-> c.id, dentry |-> t2[c.id].root]
                                   ELSE IF pos.mnt \in Subtree(mt, oldroot)
                                   THEN [mnt |-> CopyOf(mt, oldroot, t2, c.id, pos.mnt), dentry |-> pos.dentry]
                                   ELSE pos
                       pr1 == [pr EXCEPT ![p] = [ns |-> n, root |-> Map(pr[p].root), cwd |-> Map(pr[p].cwd),
                                                 fds |-> pr[p].fds, nsfds |-> pr[p].nsfds]]
                       ns1 == [nst EXCEPT ![n] = [alive |-> TRUE, root |-> c.id, user |-> ProcUser[p],
                                                  anon |-> FALSE, origin |-> NoNs]]
                   IN /\ ok' = (ok /\ (empty \/ CloneNsOK(mt, oldroot, t2, c.id, userdiff)))
                      /\ Finish(t2, ns1, pr1, ddead, [HistNone EXCEPT !.kind = "clonens"])

\* open_tree(OPEN_TREE_CLONE): a detached copy in an anonymous namespace,
\* referenced by a file
OpenTree(p, R, pos, rec) ==
    /\ Budget
    /\ NsRoom(0)
    /\ MayMount(p)
    /\ Cardinality(pr[p].fds) < MaxFds
    /\ pos \in R
    /\ ~mt[pos.mnt].unbind
    /\ MayCopyTree(p, pos.mnt)
    /\ rec \/ ~HasLockedChildren(mt, pos.mnt, pos.dentry)
    /\ RoomFor(Cardinality(Subtree(mt, pos.mnt)))
    /\ LET n == CHOOSE x \in NsIds : ~nst[x].alive
           src == mt[pos.mnt].ns
           origin == IF src = NoNs THEN NoNs ELSE IF nst[src].anon THEN nst[src].origin ELSE src
           c == IF rec THEN CopyTree(mt, pos.mnt, pos.dentry, CL_NONE)
                ELSE LET r == CloneMnt(mt, pos.mnt, pos.dentry, CL_NONE) IN [mt |-> r.mt, id |-> r.id, err |-> ""]
       IN /\ c.err = ""
          /\ LET t1 == [x \in MntIds |-> IF x \in Subtree(c.mt, c.id)
                                         THEN [c.mt[x] EXCEPT !.ns = n, !.attached = TRUE] ELSE c.mt[x]]
                 ns1 == [nst EXCEPT ![n] = [alive |-> TRUE, root |-> c.id, user |-> ProcUser[p],
                                            anon |-> TRUE, origin |-> origin]]
                 pr1 == [pr EXCEPT ![p].fds = pr[p].fds \cup {[mnt |-> c.id, dentry |-> t1[c.id].root, tree |-> TRUE]}]
             IN /\ ok' = ok
                /\ Finish(t1, ns1, pr1, ddead, [HistNone EXCEPT !.kind = "opentree"])

\* fsmount(): a brand new mount in an anonymous namespace
Fsmount(p, sb) ==
    /\ Budget
    /\ NsRoom(0)
    /\ MayMount(p)
    /\ Cardinality(pr[p].fds) < MaxFds
    /\ RoomFor(1)
    /\ LET n == CHOOSE x \in NsIds : ~nst[x].alive
           id == NewId(mt)
           t1 == [mt EXCEPT ![id] = [Fresh(id, sb, SbRoot[sb]) EXCEPT !.ns = n, !.attached = TRUE]]
           ns1 == [nst EXCEPT ![n] = [alive |-> TRUE, root |-> id, user |-> ProcUser[p],
                                      anon |-> TRUE, origin |-> NoNs]]
           pr1 == [pr EXCEPT ![p].fds = pr[p].fds \cup {[mnt |-> id, dentry |-> SbRoot[sb], tree |-> TRUE]}]
       IN /\ ok' = ok
          /\ Finish(t1, ns1, pr1, ddead, [HistNone EXCEPT !.kind = "fsmount"])

\* open_tree(OPEN_TREE_NAMESPACE) / fsmount(FSMOUNT_NAMESPACE):
\* create_new_namespace().  new = TRUE is the fsmount variant with a fresh
\* mount of sb; otherwise a copy of pos.
OpenTreeNs(p, R, pos, rec, new, sb) ==
    /\ Budget
    /\ NsRoom(0)
    /\ ~nst[pr[p].ns].anon
    /\ new \/ (pos \in R /\ ~mt[pos.mnt].unbind /\ MayCopyTree(p, pos.mnt)
               /\ (rec \/ ~HasLockedChildren(mt, pos.mnt, pos.dentry)))
    /\ RoomFor(1 + (IF new THEN 1 ELSE Cardinality(Subtree(mt, pos.mnt))))
    /\ LET old == pr[p].ns
           oldroot == nst[old].root
           userdiff == ProcUser[p] # nst[old].user
           flag == CL(userdiff, FALSE, FALSE, FALSE, FALSE)
           n == CHOOSE x \in NsIds : ~nst[x].alive
           r0 == CloneMnt(mt, oldroot, mt[oldroot].root, flag)
           nsroot == r0.id
           locked == \E x \in Subtree(mt, oldroot) : x \in AncestorMnts(mt, Topmost(mt, oldroot)) \cup {Topmost(mt, oldroot)}
                                                  /\ x # oldroot /\ mt[x].locked
           c == IF new
                THEN LET id == NewId(r0.mt)
                     IN [mt |-> [r0.mt EXCEPT ![id] = Fresh(id, sb, SbRoot[sb])], id |-> id, err |-> ""]
                ELSE IF rec THEN CopyTree(r0.mt, pos.mnt, pos.dentry, flag)
                ELSE LET r == CloneMnt(r0.mt, pos.mnt, pos.dentry, flag) IN [mt |-> r.mt, id |-> r.id, err |-> ""]
       IN /\ c.err = ""
          /\ LET t1 == IF locked THEN SetLocked(c.mt, c.id, TRUE) ELSE c.mt
                 t2 == AttachMnt(t1, c.id, nsroot, t1[nsroot].root)
                 t3 == IF userdiff THEN LockMntTree(t2, nsroot) ELSE t2
                 t4 == [x \in MntIds |-> IF x \in Subtree(t3, nsroot)
                                         THEN [t3[x] EXCEPT !.ns = n, !.attached = TRUE] ELSE t3[x]]
                 ns1 == [nst EXCEPT ![n] = [alive |-> TRUE, root |-> nsroot, user |-> ProcUser[p],
                                            anon |-> FALSE, origin |-> NoNs]]
                 pr1 == [pr EXCEPT ![p].nsfds = pr[p].nsfds \cup {n}]
             IN /\ ok' = ok
                /\ Finish(t4, ns1, pr1, ddead, [HistNone EXCEPT !.kind = "opentreens"])

\* setns(2) into a mount namespace: mntns_install()
Setns(p, n) ==
    /\ Budget
    /\ nst[n].alive /\ ~nst[n].anon /\ n # pr[p].ns
    /\ Capable(ProcUser[p], n)
    /\ n = 1 \/ n \in pr[p].nsfds \/ \E q \in Procs : pr[q].ns = n
    /\ LET root == Cross(mt, nst[n].root, mt[nst[n].root].root)
           pr1 == [pr EXCEPT ![p] = [ns |-> n, root |-> root, cwd |-> root, fds |-> pr[p].fds,
                                     nsfds |-> pr[p].nsfds \ {n}]]
       IN /\ ok' = ok
          /\ Finish(mt, nst, pr1, ddead, [HistNone EXCEPT !.kind = "setns"])

\* a process created inside namespace n (fork in a process of n, possibly
\* after unshare(CLONE_NEWUSER)): only the prelude uses it
Spawn(p, n) ==
    /\ InPrelude
    /\ nst[n].alive /\ ~nst[n].anon /\ n # pr[p].ns
    /\ LET root == Cross(mt, nst[n].root, mt[nst[n].root].root)
           pr1 == [pr EXCEPT ![p] = [ns |-> n, root |-> root, cwd |-> root, fds |-> {}, nsfds |-> {}]]
       IN /\ ok' = ok
          /\ Finish(mt, nst, pr1, ddead, [HistNone EXCEPT !.kind = "setns"])

\* close(2) of an open_tree/fsmount file: dissolve_on_fput()
CloseFd(p, f) ==
    /\ Budget
    /\ f \in pr[p].fds
    /\ LET pr1 == [pr EXCEPT ![p].fds = pr[p].fds \ {f}]
           dissolve == f.tree /\ AnonNsRoot(f.mnt)
           t1 == IF dissolve THEN UmountTree(mt, f.mnt, UmountHow(FALSE, FALSE, TRUE)).mt ELSE mt
           ns1 == IF dissolve THEN [nst EXCEPT ![mt[f.mnt].ns].alive = FALSE] ELSE nst
       IN /\ ok' = ok
          /\ Finish(t1, ns1, pr1, ddead, [HistNone EXCEPT !.kind = "closefd"])

(* ---- pivot_root(2) ----------------------------------------------------- *)

PivotRoot(p, R, new, putold) ==
    /\ Budget
    /\ MayMount(p)
    /\ new \in R /\ IsMountRoot(new)
    /\ CanMountOn(R, putold)
    /\ LET w == WhereToMount(putold, FALSE)
           oldMnt == w.parent
           oldD == w.d
           newMnt == new.mnt
           root == pr[p].root
           rootMnt == root.mnt
           exParent == mt[newMnt].parent
           rootParent == mt[rootMnt].parent
       IN /\ ~mt[oldMnt].shared
          /\ HasParent(mt, newMnt) /\ ~mt[exParent].shared
          /\ HasParent(mt, rootMnt) /\ ~mt[rootParent].shared
          /\ mt[rootMnt].ns = pr[p].ns /\ mt[newMnt].ns = pr[p].ns
          /\ ~mt[newMnt].locked
          /\ newMnt # rootMnt /\ oldMnt # rootMnt
          /\ IsMountRoot(root)
          /\ IsPathReachable(mt, oldMnt, oldD, new)
          /\ IsPathReachable(mt, newMnt, new.dentry, root)
          /\ LET rootMp == mt[rootMnt].mp
                 t1 == UmountMnt(mt, newMnt)
                 t2 == IF mt[rootMnt].locked
                       THEN SetLocked(SetLocked(t1, newMnt, TRUE), rootMnt, FALSE) ELSE t1
                 t3 == AttachMnt(t2, newMnt, rootParent, rootMp)
                 t4 == UmountMnt(t3, rootMnt)
                 t5 == AttachMnt(t4, rootMnt, oldMnt, oldD)
                 t6 == SetOnexp(t5, newMnt, FALSE)
                 \* chroot_fs_refs(): every task whose root or pwd was the old root
                 pr1 == [q \in Procs |-> [pr[q] EXCEPT !.root = IF pr[q].root = root THEN new ELSE pr[q].root,
                                                       !.cwd = IF pr[q].cwd = root THEN new ELSE pr[q].cwd]]
             IN /\ ok' = ok
                /\ Finish(t6, nst, pr1, ddead,
                          [HistNone EXCEPT !.kind = "pivot", !.locktransfer = mt[rootMnt].locked])

(* ---- rmdir(2) of a mountpoint: __detach_mounts() ----------------------- *)

RECURSIVE DetachAll(_, _)
DetachAll(t, d) ==
    LET at == {x \in Live(t) : t[x].hashed /\ t[x].mp = d}
    IN IF at = {} THEN t
       ELSE LET x == CHOOSE y \in at : TRUE
                t1 == IF t[x].umount THEN UmountMnt(t, x)
                      ELSE UmountTree(t, x, UmountHow(FALSE, FALSE, TRUE)).mt
            IN DetachAll(t1, d)

Rmdir(p, R, pos) ==
    /\ Budget
    /\ pos \in R
    /\ pos.dentry \notin ddead
    /\ DParent[pos.dentry] # pos.dentry
    /\ DChildren(pos.dentry) \subseteq ddead
    /\ pos.dentry # mt[pos.mnt].root
    \* is_local_mountpoint(): -EBUSY
    /\ ~\E x \in Live(mt) : mt[x].ns = pr[p].ns /\ mt[x].attached /\ mt[x].mp = pos.dentry /\ mt[x].hashed
    /\ LET t1 == DetachAll(mt, pos.dentry)
       IN /\ ok' = ok
          /\ Finish(t1, nst, pr, ddead \cup {pos.dentry}, [HistNone EXCEPT !.kind = "rmdir"])

(* ---- expiry ------------------------------------------------------------ *)

\* mark_mounts_for_expiry(): mounted, already marked and not busy -> out;
\* mounted and unmarked -> marked
Expire ==
    /\ Budget
    /\ \E m \in Live(mt) : mt[m].onexp
    /\ LET cands == {m \in Live(mt) : mt[m].onexp /\ mt[m].ns # NoNs}
           marked == {m \in cands : mt[m].expmark}
           grave == {m \in marked : ~PropagateMountBusy(mt, RefTable, m, 0)}
           t1 == [x \in MntIds |-> IF x \in cands \ marked THEN [mt[x] EXCEPT !.expmark = TRUE] ELSE mt[x]]
           roots == SelectSeq([n \in 1..Cardinality(NsIds) |-> n], LAMBDA n : n \in NsIds /\ nst[n].alive)
           order == SelectSeq(Concat([i \in 1..Len(roots) |-> Preorder(t1, nst[roots[i]].root)]),
                              LAMBDA x : x \in grave)
           t2 == UmountEach(t1, order, UmountHow(TRUE, TRUE, FALSE))
       IN /\ ok' = (ok /\ (Cardinality(grave) > 1 \/ \A m \in grave : UmountVictimsOK(t1, t2, ExpectedVictims(t1, m))))
          /\ FinishUncover(t2, nst, pr, ddead, [HistNone EXCEPT !.kind = "expire", !.expired = grave # {}],
                           UNION {Unlocked(t1, m) : m \in grave})

(* ---- walks and references ---------------------------------------------- *)

\* a path walk through m: mntput() clears the expiry mark
Touch(p, R, m) ==
    /\ Budget
    /\ mt[m].expmark
    /\ \E pos \in R : pos.mnt = m
    /\ ok' = ok
    /\ Finish([mt EXCEPT ![m].expmark = FALSE], nst, pr, ddead, [HistNone EXCEPT !.kind = "walk"])

Chdir(p, R, pos) ==
    /\ Budget
    /\ pos \in R /\ pos # pr[p].cwd
    /\ ok' = ok
    /\ Finish(mt, nst, [pr EXCEPT ![p].cwd = pos], ddead, [HistNone EXCEPT !.kind = "walk"])

Chroot(p, R, pos) ==
    /\ Budget
    /\ MayMount(p)
    /\ pos \in R /\ pos # pr[p].root
    /\ ok' = ok
    /\ Finish(mt, nst, [pr EXCEPT ![p].root = pos], ddead, [HistNone EXCEPT !.kind = "walk"])

OpenFd(p, R, pos) ==
    /\ Budget
    /\ Cardinality(pr[p].fds) < MaxFds
    /\ pos \in R
    /\ ~\E f \in pr[p].fds : f.mnt = pos.mnt /\ f.dentry = pos.dentry
    /\ ok' = ok
    /\ Finish(mt, nst, [pr EXCEPT ![p].fds = pr[p].fds \cup {[mnt |-> pos.mnt, dentry |-> pos.dentry, tree |-> FALSE]}],
              ddead, [HistNone EXCEPT !.kind = "walk"])

(* ---- the state machine ------------------------------------------------- *)

InitMt ==
    LET m1 == CHOOSE x \in MntIds : \A y \in MntIds : x <= y
        m2 == CHOOSE x \in MntIds \ {m1} : \A y \in MntIds \ {m1} : x <= y
        t0 == [m \in MntIds |-> Dead(m)]
        t1 == [t0 EXCEPT ![m1] = [Fresh(m1, InitSb, SbRoot[InitSb]) EXCEPT !.ns = 1, !.attached = TRUE],
                         ![m2] = [Fresh(m2, RootSb, SbRoot[RootSb]) EXCEPT !.ns = 1, !.attached = TRUE]]
    IN AttachMnt(t1, m2, m1, SbRoot[InitSb])

Init ==
    /\ mt = InitMt
    /\ nst = [n \in NsIds |-> IF n = 1 THEN [alive |-> TRUE, root |-> CHOOSE x \in MntIds : \A y \in MntIds : x <= y,
                                            user |-> InitUser, anon |-> FALSE, origin |-> NoNs]
                              ELSE [alive |-> FALSE, root |-> NoMnt, user |-> 0, anon |-> FALSE, origin |-> NoNs]]
    /\ pr = [p \in Procs |-> LET r == Cross(mt, nst[1].root, SbRoot[InitSb])
                             IN [ns |-> 1, root |-> r, cwd |-> r, fds |-> {}, nsfds |-> {}]]
    /\ ddead = {}
    /\ covers = [p \in Procs |-> {}]
    /\ ops = 0
    /\ ok = TRUE
    /\ hist = HistNone
    /\ reach = [p \in Procs |-> ReachNow(p)]
    /\ step = 1

AllPos == [mnt: MntIds, dentry: Dentries]
Types == {"shared", "slave", "private", "unbindable"}

\* one scripted syscall of the prelude
Scripted(s) ==
    LET p == s.p
        R == Reachable(p)
    IN CASE s.kind = "mount"      -> NewMount(p, R, s.pos, s.sb, s.auto)
         [] s.kind = "bind"       -> Bind(p, R, s.src, s.dst, s.rec)
         [] s.kind = "move"       -> Move(p, R, s.src, s.dst, s.beneath)
         [] s.kind = "umount"     -> Umount(p, R, s.m, s.mode)
         [] s.kind = "chtype"     -> ChangeType(p, R, s.m, s.type, s.rec)
         [] s.kind = "setgroup"   -> SetGroup(p, R, s.from, s.to)
         [] s.kind = "clonens"    -> CloneNs(p, s.empty)
         [] s.kind = "opentree"   -> OpenTree(p, R, s.pos, s.rec)
         [] s.kind = "fsmount"    -> Fsmount(p, s.sb)
         [] s.kind = "opentreens" -> OpenTreeNs(p, R, s.pos, s.rec, s.new, s.sb)
         [] s.kind = "setns"      -> Setns(p, s.n)
         [] s.kind = "spawn"      -> Spawn(p, s.n)
         [] s.kind = "closefd"    -> CloseFd(p, s.f)
         [] s.kind = "pivot"      -> PivotRoot(p, R, s.new, s.putold)
         [] s.kind = "rmdir"      -> Rmdir(p, R, s.pos)
         [] s.kind = "expire"     -> Expire
         [] s.kind = "chdir"      -> Chdir(p, R, s.pos)
         [] s.kind = "chroot"     -> Chroot(p, R, s.pos)
         [] s.kind = "openfd"     -> OpenFd(p, R, s.pos)

\* a prelude step that cannot fire leaves a one-state run: the summaries
\* flag that (ENABLED would tell, but it hangs TLC's trace printing)
PreludeStep == Scripted(Prelude[step])

FreeStep ==
    \/ Expire
    \/ \E p \in Procs :
        LET R == Reachable(p) IN
        \/ \E pos \in R, sb \in MountSbs, auto \in BOOLEAN : NewMount(p, R, pos, sb, auto)
        \/ \E src, dst \in R, rec \in BOOLEAN : Bind(p, R, src, dst, rec)
        \/ \E src, dst \in R, beneath \in BOOLEAN : Move(p, R, src, dst, beneath)
        \/ \E m \in MntIds, mode \in {"sync", "lazy", "expire"} : Umount(p, R, m, mode)
        \/ \E m \in MntIds, type \in Types, rec \in BOOLEAN : ChangeType(p, R, m, type, rec)
        \/ \E from, to \in MntIds : SetGroup(p, R, from, to)
        \/ \E empty \in BOOLEAN : CloneNs(p, empty)
        \/ \E pos \in R, rec \in BOOLEAN : OpenTree(p, R, pos, rec)
        \/ \E sb \in MountSbs : Fsmount(p, sb)
        \/ \E pos \in R, rec, new \in BOOLEAN, sb \in MountSbs : OpenTreeNs(p, R, pos, rec, new, sb)
        \/ \E n \in NsIds : Setns(p, n)
        \/ \E f \in pr[p].fds : CloseFd(p, f)
        \/ \E new, putold \in R : PivotRoot(p, R, new, putold)
        \/ \E pos \in R : Rmdir(p, R, pos)
        \/ \E m \in MntIds : Touch(p, R, m)
        \/ \E pos \in R : Chdir(p, R, pos) \/ Chroot(p, R, pos) \/ OpenFd(p, R, pos)

Next == IF InPrelude THEN PreludeStep ELSE FreeStep

Spec == Init /\ [][Next]_vars

(* ---- invariants -------------------------------------------------------- *)

TypeOK ==
    /\ mt \in [MntIds -> MountRec]
    /\ nst \in [NsIds -> NsRec]
    /\ pr \in [Procs -> ProcRec]
    /\ ops \in 0..MaxOps
    /\ step \in 1..(Len(Prelude) + MaxOps + 1)
    /\ ok \in BOOLEAN
    /\ hist \in HistRec

\* the cached reachable sets are the real ones (smoke runs only, it is slow)
ReachOK == reach = [p \in Procs |-> ReachNow(p)]

\* I1: the algorithms agree with the specification
AlgebraOK == ok

\* I2: the structure of the tree and of the propagation graph
Structure == StructureOK(mt)

\* the iterators enumerate exactly the declarative propagation set
IteratorsOK ==
    \A m \in Live(mt) : mt[m].ns # NoNs /\ ~mt[m].umount =>
        ToSet(PropagationOrder(mt, m)) = RecvSet(mt, m)

\* namespaces: a live namespace's root is attached to it, every attached
\* mount's namespace is alive, every process is in a live namespace
NsOK ==
    /\ \A n \in NsIds : nst[n].alive => (mt[nst[n].root].alive /\ mt[nst[n].root].ns = n
                                         /\ mt[nst[n].root].attached /\ ~HasParent(mt, nst[n].root))
    /\ \A m \in Live(mt) : mt[m].attached => nst[mt[m].ns].alive
    /\ \A m \in Live(mt) : mt[m].attached => nst[mt[m].ns].root \in AncestorMnts(mt, m) \cup {m}
    /\ \A p \in Procs : nst[pr[p].ns].alive /\ ~nst[pr[p].ns].anon

\* every reference points at a live mount, and a detached mount is only
\* alive while something references it
RefsOK ==
    /\ \A p \in Procs : \A a \in Anchors(p) : mt[a.mnt].alive
    /\ \A m \in Live(mt) : (mt[m].umount /\ ~HasParent(mt, m)) => Refs(m) > 0

\* I3: an unprivileged process never reaches anything a locked mount hid
CoverOK ==
    \A p \in Procs : ProcUser[p] # InitUser => \A pos \in Reachable(p) : ~Hidden(p, pos)

\* a synchronous umount never takes out a mount somebody still references
SyncUmountNotBusy == ~hist.syncbusy
\* the proposed propagate_mount_busy() agrees with the exact rule
BusyMirrorOK == ~hist.busymismatch

(* ---- witnesses: the interesting states are reachable ------------------- *)

NoTuck          == ~hist.tucked
NoLockTransfer  == ~hist.locktransfer
NoReparent      == ~hist.reparented
NoSlaveOfSlave  == ~hist.slaveofslave
NoSkippedMaster == ~hist.skippedmaster
NoLockedKept    == ~hist.lockedkept
NoConnected     == ~hist.connected
NoPutNs         == ~hist.putns
NoExpiry        == ~hist.expired
NoTrim          == ~hist.trimmed
NoCovers        == \A p \in Procs : covers[p] = {}

=============================================================================
