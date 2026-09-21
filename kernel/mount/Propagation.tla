---------------------------- MODULE Propagation ----------------------------
(***************************************************************************)
(* fs/pnode.c and the tree surgery of fs/namespace.c, as functions over    *)
(* the mount table: every algorithm takes a table and returns the table    *)
(* it leaves behind.  Everything here runs under namespace_sem in the      *)
(* kernel, so one syscall is one atomic step of the state machine that     *)
(* uses these operators (MountOps).                                        *)
(*                                                                         *)
(* Operational side (fs/pnode.c at 50d05c7c76c9 unless noted):             *)
(*   CloneMnt            clone_mnt()                    fs/namespace.c    *)
(*   CopyTree            copy_tree()                    fs/namespace.c    *)
(*   PropagateMnt        propagate_mnt(), need_secondary(), find_master() *)
(*   AttachRecursive     attach_recursive_mnt()         fs/namespace.c    *)
(*   ChangeMntPropagation change_mnt_propagation(), transfer_propagation()*)
(*   BulkMakePrivate     bulk_make_private(), trace_transfers(),          *)
(*                       set_destinations()                                *)
(*   PropagateUmount     propagate_umount(), gather_candidates(),          *)
(*                       trim_one(), trim_ancestors(), handle_locked(),    *)
(*                       reparent(), umount_one()                          *)
(*   PropagateMountUnlock propagate_mount_unlock()                         *)
(*   PropagateMountBusy  propagate_mount_busy()                            *)
(*   UmountTree          umount_tree(), disconnect_mount()   fs/namespace.c*)
(*                                                                         *)
(* Declarative side:                                                       *)
(*   ExpectedReceivers, CopiesOK      sharedsubtree.rst 5b/5d/5e (D2)      *)
(*   MaxNonShifting, MaxNonRevealing  propagate_umount.txt (D3)            *)
(*   DocUmountVictims                 sharedsubtree.rst 5f as written      *)
(*                                                                         *)
(* Mutation toggles (FIX_* FALSE reproduces the bug named):                *)
(*   FIX_TRIM_ANCESTORS   keep trim_ancestors(): without it a candidate   *)
(*                        with a surviving descendant is taken, shifting   *)
(*                        the survivor (the non-shifting rule)             *)
(*   FIX_HANDLE_LOCKED    keep handle_locked(): without it locked          *)
(*                        candidates go while their parent stays           *)
(*                        (0c56fe31420c, the non-revealing rule)           *)
(*   FIX_REPARENT_LATE    reparent after the set is final (570487d3faf2)   *)
(*   FIX_FIND_MASTER_STOP find_master() stops at peers of the source       *)
(*                        (11933cf1d91d)                                   *)
(*   FIX_TUCK_LOCK        a tucked-under locked mount hands MNT_LOCKED to  *)
(*                        the mount that covers it (c62a4766937e)          *)
(*   FIX_CLONE_UNBINDABLE clone_mnt() keeps T_UNBINDABLE (the F1 fix,   *)
(*                        not upstream)                                   *)
(*   FIX_SET_GROUP_UNBINDABLE do_set_group() refuses an unbindable       *)
(*                        target (the F4 fix, not upstream)              *)
(*   FIX_BUSY_VICTIMS     propagate_mount_busy() checks every mount that  *)
(*                        propagate_umount() would pull out, not only    *)
(*                        the copies without children and the ones      *)
(*                        covered by a single overmount (F5, not        *)
(*                        upstream)                                      *)
(***************************************************************************)
EXTENDS MountTree

CONSTANTS FIX_TRIM_ANCESTORS, FIX_HANDLE_LOCKED, FIX_REPARENT_LATE,
          FIX_FIND_MASTER_STOP, FIX_TUCK_LOCK, FIX_CLONE_UNBINDABLE,
          FIX_SET_GROUP_UNBINDABLE, FIX_BUSY_VICTIMS

(* ---- CL_* flags as a record ------------------------------------------- *)

ClFlags == [slave: BOOLEAN, private: BOOLEAN, mkshared: BOOLEAN,
            unbind: BOOLEAN, expire: BOOLEAN]
CL(s, p, m, u, e) == [slave |-> s, private |-> p, mkshared |-> m, unbind |-> u, expire |-> e]
CL_NONE == CL(FALSE, FALSE, FALSE, FALSE, FALSE)

(* ---- field mutators ---------------------------------------------------- *)

SetParent(mt, m, p, d)   == [mt EXCEPT ![m].parent = p, ![m].mp = d]
SetHashed(mt, m, b)      == [mt EXCEPT ![m].hashed = b]
SetOver(mt, m, o)        == [mt EXCEPT ![m].over = o]
SetChildren(mt, m, s)    == [mt EXCEPT ![m].children = s]
SetNs(mt, m, n, a)       == [mt EXCEPT ![m].ns = n, ![m].attached = a]
SetGid(mt, m, g)         == [mt EXCEPT ![m].gid = g]
SetShared(mt, m, b)      == [mt EXCEPT ![m].shared = b]
SetUnbind(mt, m, b)      == [mt EXCEPT ![m].unbind = b]
SetMarked(mt, m, b)      == [mt EXCEPT ![m].marked = b]
SetCand(mt, m, b)        == [mt EXCEPT ![m].cand = b]
SetMaster(mt, m, x)      == [mt EXCEPT ![m].master = x]
SetNpeer(mt, m, x)       == [mt EXCEPT ![m].npeer = x]
SetSlaves(mt, m, s)      == [mt EXCEPT ![m].slaves = s]
SetLocked(mt, m, b)      == [mt EXCEPT ![m].locked = b]
SetUmount(mt, m, b)      == [mt EXCEPT ![m].umount = b]
SetOnexp(mt, m, b)       == [mt EXCEPT ![m].onexp = b]

\* set_mnt_shared()
SetMntShared(mt, m) == [mt EXCEPT ![m].shared = TRUE, ![m].unbind = FALSE]

\* list_add(&new->mnt_share, &old->mnt_share): new right after old in the ring
RingInsertAfter(mt, old, new) ==
    [mt EXCEPT ![new].npeer = mt[old].npeer, ![old].npeer = new]
\* list_del_init(&m->mnt_share)
RingRemove(mt, m) ==
    LET prev == CHOOSE x \in Live(mt) : mt[x].npeer = m
    IN [mt EXCEPT ![prev].npeer = mt[m].npeer, ![m].npeer = m]
\* hlist_del_init(&m->mnt_slave): off whichever list the node is on (the
\* master pointer may already point elsewhere, as in trace_transfers())
SlaveDel(mt, m) ==
    [x \in MntIds |-> IF Contains(mt[x].slaves, m) THEN [mt[x] EXCEPT !.slaves = SeqDel(mt[x].slaves, m)] ELSE mt[x]]
\* hlist_add_head(&m->mnt_slave, &master->mnt_slave_list)
SlaveAddHead(mt, master, m) ==
    [mt EXCEPT ![master].slaves = <<m>> \o mt[master].slaves]
\* hlist_add_behind(&m->mnt_slave, &old->mnt_slave)
SlaveAddBehind(mt, old, m) ==
    [mt EXCEPT ![mt[old].master].slaves = InsertAfter(mt[mt[old].master].slaves, old, m)]

UsedGids(mt) == {mt[m].gid : m \in Live(mt)} \ {0}
\* mnt_alloc_group_id(): the smallest unused id
NewGid(mt) == CHOOSE g \in 1..(Cardinality(Live(mt)) + 1) : g \notin UsedGids(mt)

(* ---- attaching, unhashing ---------------------------------------------- *)

\* mnt_set_mountpoint(parent, mp, child): parent and mountpoint, not hashed
SetMountpoint(mt, parent, d, child) == SetParent(mt, child, parent, d)

\* make_visible(): hash it, record it as the overmount when it sits on the root,
\* append it to the parent's children
MakeVisible(mt, m) ==
    LET p == mt[m].parent
        mt1 == IF mt[m].mp = mt[p].root THEN SetOver(mt, p, m) ELSE mt
        mt2 == SetHashed(mt1, m, TRUE)
    IN SetChildren(mt2, p, mt2[p].children \o <<m>>)

\* attach_mnt(m, parent, mp)
AttachMnt(mt, m, parent, d) == MakeVisible(SetMountpoint(mt, parent, d, m), m)

\* __umount_mnt(m): take it out of the tree, it becomes its own parent
UmountMnt(mt, m) ==
    LET p == mt[m].parent
        mt1 == IF mt[p].over = m THEN SetOver(mt, p, NoMnt) ELSE mt
        mt2 == SetChildren(mt1, p, SeqDel(mt1[p].children, m))
        mt3 == SetHashed(mt2, m, FALSE)
    IN SetParent(mt3, m, NoMnt, mt3[m].root)

\* mnt_change_mountpoint(parent, mp, m): move a hashed mount elsewhere.  The
\* old parent's overmount field is not cleared here (make_visible() of the
\* mount taking the place already replaced it).
ChangeMountpoint(mt, parent, d, m) ==
    LET p == mt[m].parent
        mt1 == SetChildren(mt, p, SeqDel(mt[p].children, m))
        mt2 == SetHashed(mt1, m, FALSE)
    IN AttachMnt(mt2, m, parent, d)

\* commit_tree(m): put the subtree into the parent's namespace if the root
\* is not attached yet, then make it visible
CommitTree(mt, m) ==
    LET n == mt[mt[m].parent].ns
        mt1 == IF mt[m].attached THEN mt
               ELSE [x \in MntIds |-> IF x \in Subtree(mt, m)
                                     THEN [mt[x] EXCEPT !.ns = n, !.attached = TRUE]
                                     ELSE mt[x]]
    IN MakeVisible(mt1, m)

\* lock_mnt_tree(m): every mount below m that is not on an expiry list
LockMntTree(mt, m) ==
    [x \in MntIds |-> IF x \in Subtree(mt, m) /\ x # m /\ ~mt[x].onexp
                      THEN [mt[x] EXCEPT !.locked = TRUE] ELSE mt[x]]

\* invent_group_ids(m, recurse): a group id for every member without one,
\* in next_mnt() order
RECURSIVE InventIds(_, _)
InventIds(mt, s) ==
    IF s = <<>> THEN mt
    ELSE LET m == Head(s)
             mt1 == IF mt[m].gid = 0 THEN SetGid(mt, m, NewGid(mt)) ELSE mt
         IN InventIds(mt1, Tail(s))
InventGroupIds(mt, m, recurse) == InventIds(mt, IF recurse THEN Preorder(mt, m) ELSE <<m>>)

(* ---- clone_mnt(), copy_tree() ------------------------------------------ *)

\* clone_mnt(old, root, flag): a new mount of old's superblock with root
\* as its root; group id and propagation links per the CL_* flags
CloneMnt(mt, old, root, flag) ==
    LET id == NewId(mt)
        gid0 == IF flag.slave \/ flag.private THEN 0 ELSE mt[old].gid
        gid == IF flag.mkshared /\ gid0 = 0 THEN NewGid(mt) ELSE gid0
        \* T_UNBINDABLE is lost by clone_mnt() since 406fea799925 (F1);
        \* with the fix the copy keeps it unless it is made shared
        rec == [Fresh(id, mt[old].sb, root) EXCEPT !.shrink = mt[old].shrink,
                                                  !.gid = gid, !.shared = gid # 0,
                                                  !.unbind = FIX_CLONE_UNBINDABLE /\ mt[old].unbind /\ gid = 0]
        mt1 == [mt EXCEPT ![id] = rec]
    IN IF flag.private THEN [mt |-> mt1, id |-> id]
       ELSE LET mt2 == IF Peers(mt1, id, old) THEN RingInsertAfter(mt1, old, id) ELSE mt1
                mt3 == IF flag.slave /\ mt[old].gid # 0
                       THEN SlaveAddHead(SetMaster(mt2, id, old), old, id)
                       ELSE IF mt[old].master # NoMnt
                       THEN SlaveAddBehind(SetMaster(mt2, id, mt[old].master), old, id)
                       ELSE mt2
            IN [mt |-> mt3, id |-> id]

\* the walk of copy_tree() over one subtree: clone src under the copy of its
\* parent, then its children in order.  st = [mt, copyof, err]
RECURSIVE CopySub(_, _, _)
RECURSIVE CopyKids(_, _, _)
CopyKids(st, kids, flag) ==
    IF kids = <<>> \/ st.err # "" THEN st ELSE CopyKids(CopySub(st, Head(kids), flag), Tail(kids), flag)
CopySub(st, src, flag) ==
    LET mt == st.mt IN
    IF st.err # "" THEN st
    ELSE IF ~flag.unbind /\ mt[src].unbind
    THEN IF mt[src].locked THEN [st EXCEPT !.err = "EPERM"] ELSE st   \* skip_mnt_tree()
    ELSE LET r == CloneMnt(mt, src, mt[src].root, flag)
             dst == r.id
             mt1 == [r.mt EXCEPT ![dst].locked = mt[src].locked,
                                 ![dst].onexp = flag.expire /\ mt[src].onexp]
             mt2 == AttachMnt(mt1, dst, st.copyof[mt[src].parent], mt[src].mp)
             st1 == [mt |-> mt2, copyof |-> st.copyof @@ (src :> dst), err |-> ""]
         IN CopyKids(st1, mt[src].children, flag)

\* copy_tree(src_root, dentry, flag): the copy's root, or an error
CopyTree(mt, srcroot, dentry, flag) ==
    IF ~flag.unbind /\ mt[srcroot].unbind THEN [mt |-> mt, id |-> NoMnt, err |-> "EINVAL"]
    ELSE LET r == CloneMnt(mt, srcroot, dentry, flag)
             kids == SelectSeq(mt[srcroot].children, LAMBDA c : IsSubdir(mt[c].mp, dentry))
             st == CopyKids([mt |-> r.mt, copyof |-> (srcroot :> r.id), err |-> ""], kids, flag)
         IN IF st.err # "" THEN [mt |-> mt, id |-> NoMnt, err |-> st.err]
            ELSE [mt |-> st.mt, id |-> r.id, err |-> ""]

(* ---- propagate_mnt() --------------------------------------------------- *)

\* need_secondary(m, dest_mp); nsanon is the namespace table's anon flag
NeedSecondary(mt, nsanon, m, d) ==
    /\ ~IsMntNew(mt, m)
    /\ IsSubdir(d, mt[m].root)
    /\ ~nsanon[mt[m].ns]

\* mnt_parent of a mount that is its own parent is itself
ParentOrSelf(mt, m) == IF mt[m].parent = NoMnt THEN m ELSE mt[m].parent

\* find_master(m, last_copy, original): the copy the new copy for m hangs off
RECURSIVE FmAscend(_, _)
FmAscend(mt, m) ==
    LET p == mt[m].master
    IN IF p = NoMnt \/ mt[p].marked THEN [m |-> m, p |-> p] ELSE FmAscend(mt, p)
RECURSIVE FmDescend(_, _, _, _, _)
FmDescend(mt, last, original, m, p) ==
    IF FIX_FIND_MASTER_STOP /\ Peers(mt, last, original) THEN last
    ELSE IF last = NoMnt THEN NoMnt                       \* would be a NULL deref
    ELSE LET parent == ParentOrSelf(mt, last)
         IN IF mt[parent].master = p
            THEN IF ~Peers(mt, parent, m) THEN mt[last].master ELSE last
            ELSE FmDescend(mt, mt[last].master, original, m, p)
FindMaster(mt, m, last, original) ==
    LET a == FmAscend(mt, m) IN FmDescend(mt, last, original, a.m, a.p)

\* the do { } while ((n = next_peer(n)) != m) loop over one peer group;
\* st = [mt, list, copy, type, err]
RECURSIVE PeerLoop(_, _, _, _, _, _)
PeerLoop(st, nsanon, n, m, d, source) ==
    IF st.err # "" THEN st
    ELSE LET st1 ==
             IF ~NeedSecondary(st.mt, nsanon, n, d) THEN st
             ELSE LET copy == IF st.type.slave THEN FindMaster(st.mt, n, st.copy, source) ELSE st.copy
                  IN IF copy = NoMnt THEN [st EXCEPT !.err = "NULLDEREF"]
                     ELSE LET r == CopyTree(st.mt, copy, st.mt[copy].root, st.type)
                          IN IF r.err # "" THEN [st EXCEPT !.err = r.err]
                             ELSE LET mt1 == SetMountpoint(r.mt, n, d, r.id)
                                      mt2 == IF mt1[n].master # NoMnt
                                             THEN SetMarked(mt1, mt1[n].master, TRUE) ELSE mt1
                                  IN [st EXCEPT !.mt = mt2, !.list = <<r.id>> \o st.list, !.copy = r.id,
                                                !.type = CL(FALSE, FALSE, TRUE, FALSE, FALSE), !.err = ""]
             next == NextPeer(st1.mt, n)
         IN IF next = m THEN st1 ELSE PeerLoop(st1, nsanon, next, m, d, source)

\* the outer loop over peer groups, depth first (next_group())
RECURSIVE GroupLoop(_, _, _, _, _)
GroupLoop(st, nsanon, m, dest, d) ==
    IF m = NoMnt \/ st.err # "" THEN st
    ELSE LET source == st.source
             st1 == IF m = dest
                    THEN LET n == NextPeer(st.mt, m)
                         IN IF n = m THEN st
                            ELSE PeerLoop([st EXCEPT !.copy = source,
                                           !.type = CL(FALSE, FALSE, TRUE, FALSE, FALSE)],
                                          nsanon, n, m, d, source)
                    ELSE PeerLoop([st EXCEPT !.type = CL(TRUE, FALSE, st.mt[m].shared, FALSE, FALSE)],
                                  nsanon, m, m, d, source)
         IN IF st1.err # "" THEN st1
            ELSE GroupLoop(st1, nsanon, NextGroup(st1.mt, m, dest), dest, d)

\* propagate_mnt(dest, dest_mp, source): [mt, list, err]; list is the
\* tree_list, most recent copy first
PropagateMnt(mt, nsanon, dest, d, source) ==
    LET mt0 == IF mt[dest].master # NoMnt THEN SetMarked(mt, mt[dest].master, TRUE) ELSE mt
        st == GroupLoop([mt |-> mt0, list |-> <<>>, copy |-> source, source |-> source,
                         type |-> CL_NONE, err |-> ""], nsanon, dest, dest, d)
        \* the marks come off even on failure (the caller destroys the copies)
        mt1 == [x \in MntIds |-> IF x \in (UNION {{st.mt[st.mt[n].parent].master} : n \in ToSet(st.list)}
                                            \cup {st.mt[dest].master}) /\ x # NoMnt
                                 THEN [st.mt[x] EXCEPT !.marked = FALSE] ELSE st.mt[x]]
    IN [mt |-> mt1, list |-> st.list, err |-> st.err]

(* ---- attach_recursive_mnt() -------------------------------------------- *)

\* the loop over tree_list: lock across user namespaces, commit, tuck
RECURSIVE TuckLoop(_, _, _, _)
TuckLoop(mt, list, userns, nsuser) ==
    IF list = <<>> THEN mt
    ELSE LET child == Head(list)
             p == mt[child].parent
             mt1 == IF nsuser[mt[p].ns] # userns THEN LockMntTree(mt, child) ELSE mt
             q == LookupMnt(mt1, p, mt1[child].mp)
             mt2 == CommitTree(mt1, child)
             mt3 == IF q = NoMnt THEN mt2
                    ELSE LET r == Topmost(mt2, child)
                             mt2a == IF FIX_TUCK_LOCK /\ mt2[q].locked
                                     THEN SetLocked(SetLocked(mt2, child, TRUE), q, FALSE)
                                     ELSE mt2
                         IN ChangeMountpoint(mt2a, r, mt2a[r].root, q)
         IN TuckLoop(mt3, Tail(list), userns, nsuser)

\* attach_recursive_mnt(source, {parent P, mountpoint d}); userns is the
\* caller's user namespace, nsuser/nsanon the namespace table's fields.
\* Returns [mt, err, emptied]: emptied is the anonymous namespace the source
\* came from, or NoNs.
AttachRecursive(mt, nsuser, nsanon, userns, source, P, d) ==
    LET moving == HasParent(mt, source)
        sharedDest == mt[P].shared
        mt1 == IF sharedDest THEN InventGroupIds(mt, source, TRUE) ELSE mt
        pm == IF sharedDest THEN PropagateMnt(mt1, nsanon, P, d, source)
              ELSE [mt |-> mt1, list |-> <<>>, err |-> ""]
    IN IF pm.err # "" THEN [mt |-> mt, err |-> pm.err, emptied |-> NoNs]
       ELSE LET mt2 == pm.mt
                mt3 == IF sharedDest
                       THEN [x \in MntIds |-> IF x \in Subtree(mt2, source)
                                              THEN [mt2[x] EXCEPT !.shared = TRUE, !.unbind = FALSE]
                                              ELSE mt2[x]]
                       ELSE mt2
                emptied == IF ~moving /\ mt3[source].ns # NoNs THEN mt3[source].ns ELSE NoNs
                mt4 == IF moving THEN SetOnexp(UmountMnt(mt3, source), source, FALSE)
                       ELSE IF emptied # NoNs
                       THEN [x \in MntIds |-> IF x \in Subtree(mt3, source)
                                              THEN [mt3[x] EXCEPT !.attached = FALSE] ELSE mt3[x]]
                       ELSE mt3
                mt5 == SetMountpoint(mt4, P, d, source)
                mt6 == TuckLoop(mt5, <<source>> \o pm.list, userns, nsuser)
            IN [mt |-> mt6, err |-> "", emptied |-> emptied]

(* ---- change_mnt_propagation(), bulk_make_private() --------------------- *)

\* transfer_propagation(mnt, to): mnt's slaves go to `to` (spliced at the
\* head of its list, in order), or become masterless
TransferPropagation(mt, m, to) ==
    LET s == mt[m].slaves
        mt1 == [x \in MntIds |-> IF Contains(s, x) THEN [mt[x] EXCEPT !.master = to] ELSE mt[x]]
        mt2 == SetSlaves(mt1, m, <<>>)
    IN IF to = NoMnt \/ s = <<>> THEN mt2 ELSE SetSlaves(mt2, to, s \o mt2[to].slaves)

\* change_mnt_propagation(mnt, type), type \in {"shared","slave","private","unbindable"}
ChangeMntPropagation(mt, m, type) ==
    IF type = "shared" THEN SetMntShared(mt, m)
    ELSE LET m0 == mt[m].master
             r == IF mt[m].shared
                  THEN IF mt[m].npeer = m
                       THEN [mt |-> SetGid(mt, m, 0), master |-> m0]
                       ELSE LET nxt == NextPeer(mt, m)
                            IN [mt |-> SetGid(RingRemove(mt, m), m, 0), master |-> nxt]
                  ELSE [mt |-> mt, master |-> m0]
             mt1 == IF mt[m].shared
                    THEN TransferPropagation(SetShared(r.mt, m, FALSE), m, r.master)
                    ELSE r.mt
             mt2 == SlaveDel(mt1, m)
         IN IF type = "slave"
            THEN IF r.master # NoMnt THEN SlaveAddHead(SetMaster(mt2, m, r.master), r.master, m)
                 ELSE SetMaster(mt2, m, NoMnt)
            ELSE SetUnbind(SetMaster(mt2, m, NoMnt), m, type = "unbindable")

\* trace_transfers(m): sever m's peer link (or release its group) and its
\* slave link, mark it, and return the destination for its slaves
RECURSIVE TraceTransfers(_, _)
TraceTransfers(mt, m) ==
    LET nxt == NextPeer(mt, m)
        r == IF nxt # m
             THEN [mt |-> SetMaster(SetGid(RingRemove(mt, m), m, 0), m, nxt), next |-> nxt]
             ELSE [mt |-> IF mt[m].shared THEN SetGid(mt, m, 0) ELSE mt, next |-> mt[m].master]
        mt1 == SetMarked(SetShared(SlaveDel(r.mt, m), m, FALSE), m, TRUE)
    IN IF r.next = NoMnt \/ ~WillBeUnmounted(mt1, r.next) THEN [mt |-> mt1, dest |-> r.next]
       ELSE IF mt1[r.next].marked THEN [mt |-> mt1, dest |-> mt1[r.next].master]
       ELSE TraceTransfers(mt1, r.next)

\* set_destinations(m, master): point the chain of masters at the destination
RECURSIVE SetDestinations(_, _, _)
SetDestinations(mt, m, master) ==
    LET nxt == mt[m].master
    IN IF nxt = master THEN mt ELSE SetDestinations(SetMaster(mt, m, master), nxt, master)

RECURSIVE BmpFirst(_, _)
BmpFirst(mt, s) ==
    IF s = <<>> THEN mt
    ELSE LET m == Head(s)
             mt1 == IF mt[m].marked THEN mt
                    ELSE LET r == TraceTransfers(mt, m) IN SetDestinations(r.mt, m, r.dest)
         IN BmpFirst(mt1, Tail(s))
RECURSIVE BmpSecond(_, _)
BmpSecond(mt, s) ==
    IF s = <<>> THEN mt
    ELSE LET m == Head(s)
             mt1 == SetMarked(SetMaster(TransferPropagation(mt, m, mt[m].master), m, NoMnt), m, FALSE)
         IN BmpSecond(mt1, Tail(s))
\* bulk_make_private(set): take every victim out of the propagation graph
BulkMakePrivate(mt, s) == BmpSecond(BmpFirst(mt, s), s)

(* ---- propagate_umount() ------------------------------------------------ *)

IsCandidate(mt, m) == m # NoMnt /\ mt[m].cand

\* umount_one(m, to_umount)
UmountOne(mt, m) ==
    LET p == mt[m].parent
        mt1 == SetUmount(mt, m, TRUE)
        mt2 == IF p = NoMnt THEN mt1 ELSE SetChildren(mt1, p, SeqDel(mt1[p].children, m))
    IN [mt2 EXCEPT ![m].attached = FALSE]

\* remove_from_candidate_list(m)
RemoveFromCandidates(mt, m) == [mt EXCEPT ![m].marked = FALSE, ![m].cand = FALSE]

\* the inner walk of gather_candidates() over Propagation(parent(m))
RECURSIVE GatherWalk(_, _, _, _, _)
GatherWalk(st, q, p, d, m) ==
    IF q = NoMnt THEN st
    ELSE LET child == LookupMnt(st.mt, q, d)
         IN IF child = NoMnt THEN GatherWalk(st, PropagationNext(st.mt, q, p), p, d, m)
            ELSE IF st.mt[child].cand
            THEN GatherWalk(st, SkipPropagationSubtree(st.mt, q, p), p, d, m)
            ELSE LET mt1 == SetCand(st.mt, child, TRUE)
                     cands == IF ~WillBeUnmounted(mt1, child) THEN <<child>> \o st.cands ELSE st.cands
                 IN GatherWalk([mt |-> mt1, cands |-> cands], PropagationNext(mt1, q, p), p, d, m)
RECURSIVE GatherLoop(_, _)
GatherLoop(st, s) ==
    IF s = <<>> THEN st
    ELSE LET m == Head(s)
         IN IF st.mt[m].cand THEN GatherLoop(st, Tail(s))
            ELSE LET mt1 == SetCand(st.mt, m, TRUE)
                     p == mt1[m].parent
                     st1 == GatherWalk([mt |-> mt1, cands |-> st.cands],
                                       PropagationNext(mt1, p, p), p, mt1[m].mp, m)
                 IN GatherLoop(st1, Tail(s))
\* gather_candidates(set): [mt, cands]
GatherCandidates(mt, s) ==
    LET st == GatherLoop([mt |-> mt, cands |-> <<>>], s)
        mt1 == [x \in MntIds |-> IF Contains(s, x) THEN [st.mt[x] EXCEPT !.cand = FALSE] ELSE st.mt[x]]
    IN [mt |-> mt1, cands |-> st.cands]

\* trim_ancestors(m)
RECURSIVE TrimAncestors(_, _)
TrimAncestors(mt, m) ==
    LET p == mt[m].parent
    IN IF ~IsCandidate(mt, p) THEN mt
       ELSE IF mt[m].marked THEN mt
       ELSE LET mt1 == SetMarked(mt, m, TRUE)
                mt2 == IF m # mt1[p].over THEN SetCand(mt1, p, FALSE) ELSE mt1
            IN TrimAncestors(mt2, p)

\* trim_one(m, to_umount): st = [mt, cands, tou]
TrimOne(st, m) ==
    LET mt == st.mt IN
    IF ~mt[m].cand THEN [st EXCEPT !.mt = RemoveFromCandidates(mt, m), !.cands = SeqDel(st.cands, m)]
    ELSE LET kids == mt[m].children
             nonc == SelectSeq(kids, LAMBDA n : ~mt[n].cand)
             found == nonc # <<>>
             removeThis == \E i \in 1..Len(nonc) : nonc[i] # mt[m].over
             leaf == ~found /\ ~mt[m].locked /\ kids = <<>>
             mt1 == IF found /\ FIX_TRIM_ANCESTORS THEN TrimAncestors(mt, m) ELSE mt
         IN IF removeThis
            THEN [mt |-> RemoveFromCandidates(mt1, m), cands |-> SeqDel(st.cands, m), tou |-> st.tou]
            ELSE IF leaf
            THEN [mt |-> UmountOne(RemoveFromCandidates(mt1, m), m), cands |-> SeqDel(st.cands, m),
                  tou |-> st.tou \o <<m>>]
            ELSE [st EXCEPT !.mt = mt1]
RECURSIVE TrimLoop(_, _)
TrimLoop(st, s) == IF s = <<>> THEN st ELSE TrimLoop(TrimOne(st, Head(s)), Tail(s))

\* handle_locked(m, to_umount)
RECURSIVE HlAscend(_, _, _, _)
HlAscend(st, p, m, cutoff) ==
    IF ~IsCandidate(st.mt, p) THEN [st |-> st, p |-> p, cutoff |-> cutoff]
    ELSE LET st1 == [st EXCEPT !.mt = RemoveFromCandidates(st.mt, p), !.cands = SeqDel(st.cands, p)]
             c == IF ~st1.mt[p].locked THEN st1.mt[p].parent ELSE cutoff
         IN HlAscend(st1, st1.mt[p].parent, m, c)
RECURSIVE HlCommit(_, _, _)
HlCommit(st, m, cutoff) ==
    IF m = cutoff THEN st
    ELSE HlCommit([st EXCEPT !.mt = UmountOne(st.mt, m), !.tou = st.tou \o <<m>>], st.mt[m].parent, cutoff)
HandleLocked(st, m) ==
    IF ~st.mt[m].cand THEN [st EXCEPT !.mt = RemoveFromCandidates(st.mt, m), !.cands = SeqDel(st.cands, m)]
    ELSE LET a == HlAscend(st, m, m, m)
             cutoff == IF a.p # NoMnt /\ WillBeUnmounted(a.st.mt, a.p) THEN a.p ELSE a.cutoff
         IN IF FIX_HANDLE_LOCKED THEN HlCommit(a.st, m, cutoff)
            ELSE HlCommit(a.st, m, IF a.p # NoMnt THEN a.p ELSE NoMnt)   \* take the whole chain
RECURSIVE LockedLoop(_)
LockedLoop(st) == IF st.cands = <<>> THEN st ELSE LockedLoop(HandleLocked(st, Head(st.cands)))

\* reparent(over): slide a surviving overmount down to where the bottom of
\* the doomed stack was attached
RECURSIVE ReparentTarget(_, _, _)
ReparentTarget(mt, p, d) ==
    IF ~WillBeUnmounted(mt, p) THEN [p |-> p, d |-> d]
    ELSE ReparentTarget(mt, mt[p].parent, mt[p].mp)
Reparent(mt, m) ==
    LET t == ReparentTarget(mt, mt[m].parent, mt[m].mp)
    IN ChangeMountpoint(mt, t.p, t.d, m)
RECURSIVE ReparentLoop(_, _)
ReparentLoop(mt, s) ==
    IF s = <<>> THEN mt
    ELSE LET m == Head(s)
             over == mt[m].over
             mt1 == IF over # NoMnt /\ ~WillBeUnmounted(mt, over) THEN Reparent(mt, over) ELSE mt
         IN ReparentLoop(mt1, Tail(s))

\* propagate_umount(set): the extended set, in order; [mt, set]
PropagateUmount(mt, s) ==
    LET g == GatherCandidates(mt, s)
        st1 == TrimLoop([mt |-> g.mt, cands |-> g.cands, tou |-> <<>>], g.cands)
        \* FIX_REPARENT_LATE off: reparent before the set is final (570487d3faf2)
        st1b == IF FIX_REPARENT_LATE THEN st1 ELSE [st1 EXCEPT !.mt = ReparentLoop(st1.mt, st1.tou)]
        st2 == LockedLoop(st1b)
        mt3 == IF FIX_REPARENT_LATE THEN ReparentLoop(st2.mt, st2.tou)
               ELSE ReparentLoop(st2.mt, SelectSeq(st2.tou, LAMBDA x : ~Contains(st1.tou, x)))
    IN [mt |-> mt3, set |-> s \o st2.tou]


(* ---- propagate_mount_unlock(), propagate_mount_busy() ------------------ *)

\* propagate_mount_unlock(mnt): the cognates of mnt lose MNT_LOCKED
PropagateMountUnlock(mt, m) ==
    LET p == mt[m].parent
        cog == {LookupMnt(mt, q, mt[m].mp) : q \in ToSet(PropagationOrder(mt, p))} \ {NoMnt}
    IN [x \in MntIds |-> IF x \in cog THEN [mt[x] EXCEPT !.locked = FALSE] ELSE mt[x]]

\* the mounts a synchronous umount of the leaf m pulls out besides m: what
\* umount_tree() hands to propagate_umount() after propagate_mount_unlock()
SyncVictims(mt, m) ==
    LET mt0 == PropagateMountUnlock(mt, m)
        mt1 == [mt0 EXCEPT ![m].umount = TRUE, ![m].attached = FALSE]
        mt2 == [x \in MntIds |-> [mt1[x] EXCEPT !.children = SelectSeq(mt1[x].children, LAMBDA c : c # m)]]
    IN ToSet(PropagateUmount(mt2, <<m>>).set) \ {m}

\* propagate_mount_busy(mnt, refcnt): refs is the number of references
\* beyond the namespace's own on each mount (anchors); the caller's own
\* path reference is the difference between refcnt 2 and 1
\* the exact rule: a synchronous umount of the leaf m is busy iff a mount
\* it would pull out has references beyond its own
BusyExact(mt, refs, m) ==
    \/ mt[m].children # <<>>
    \/ refs[m] > 0
    \/ /\ mt[m].parent # NoMnt
       /\ \E x \in SyncVictims(mt, m) : refs[x] > 0

\* the proposed propagate_mount_busy(): the same decision without running
\* propagate_umount().  Every candidate is unlocked by then, so the
\* candidates are the mounts at m's mountpoint below the receivers of its
\* parent; they form chains, a candidate that is a receiver itself having
\* the next one below it.  A candidate goes when all of its children are
\* the next candidate or its overmount (trim_one()), unless the next
\* candidate is not its overmount and some candidate further down has a
\* child outside the chain (trim_ancestors()).  The victim m itself does
\* not count as a child: umount_tree() hides it from its parent before
\* propagate_umount() runs, and the parent is a candidate when it sits at
\* m's mountpoint under a receiver.
Receivers(mt, m) == ToSet(PropagationOrder(mt, mt[m].parent))
NextCandidate(mt, R, c, d) == IF c \in R THEN LookupMnt(mt, c, d) ELSE NoMnt
RECURSIVE FoundBelow(_, _, _, _, _)
FoundBelow(mt, R, c, d, m) ==
    LET nxt == NextCandidate(mt, R, c, d)
    IN \/ \E n \in ToSet(mt[c].children) : n # nxt /\ n # m
       \/ (nxt # NoMnt /\ FoundBelow(mt, R, nxt, d, m))
PulledOut(mt, R, c, d, m) ==
    LET nxt == NextCandidate(mt, R, c, d)
    IN /\ \A n \in ToSet(mt[c].children) : n = nxt \/ n = mt[c].over \/ n = m
       /\ ~(nxt # NoMnt /\ nxt # mt[c].over /\ FoundBelow(mt, R, nxt, d, m))
BusyMirror(mt, refs, m) ==
    \/ mt[m].children # <<>>
    \/ refs[m] > 0
    \/ /\ mt[m].parent # NoMnt
       /\ LET R == Receivers(mt, m)
              d == mt[m].mp
          IN \E q \in R : LET c == LookupMnt(mt, q, d)
                          IN c # NoMnt /\ PulledOut(mt, R, c, d, m) /\ refs[c] > 0

PropagateMountBusy(mt, refs, m, own) ==
    IF FIX_BUSY_VICTIMS THEN BusyMirror(mt, refs, m)
    ELSE \/ mt[m].children # <<>>
         \/ refs[m] > 0
         \/ /\ mt[m].parent # NoMnt
            /\ \E q \in ToSet(PropagationOrder(mt, mt[m].parent)) :
                 LET child == LookupMnt(mt, q, mt[m].mp)
                 IN /\ child # NoMnt
                    /\ \/ mt[child].children = <<>>
                       \/ (Len(mt[child].children) = 1 /\ mt[child].over # NoMnt)
                    /\ refs[child] > 0

(* ---- umount_tree() ----------------------------------------------------- *)

\* how = [sync, propagate, connected]
UmountHow(s, p, c) == [sync |-> s, propagate |-> p, connected |-> c]

\* disconnect_mount(mnt, how)
DisconnectMount(mt, m, how) ==
    IF how.sync THEN TRUE
    ELSE IF ~HasParent(mt, m) THEN TRUE
    ELSE IF ~mt[mt[m].parent].umount THEN TRUE
    ELSE IF how.connected THEN FALSE
    ELSE IF mt[m].locked THEN FALSE
    ELSE TRUE

RECURSIVE UmountLoop(_, _, _, _)
UmountLoop(mt, s, how, unmounted) ==
    IF s = <<>> THEN [mt |-> mt, unmounted |-> unmounted]
    ELSE LET p == Head(s)
             mt1 == [mt EXCEPT ![p].onexp = FALSE, ![p].ns = NoNs, ![p].attached = FALSE]
             disc == DisconnectMount(mt1, p, how)
             mt2 == IF HasParent(mt1, p)
                    THEN IF ~disc
                         THEN SetChildren(mt1, mt1[p].parent, mt1[mt1[p].parent].children \o <<p>>)
                         ELSE UmountMnt(mt1, p)
                    ELSE mt1
         IN UmountLoop(mt2, Tail(s), how, IF disc THEN unmounted \cup {p} ELSE unmounted)

\* umount_tree(mnt, how): [mt, unmounted] where unmounted is the set of
\* mounts whose namespace reference namespace_unlock() will drop
UmountTree(mt, m, how) ==
    LET mt0 == IF how.propagate THEN PropagateMountUnlock(mt, m) ELSE mt
        victims == Preorder(mt0, m)
        mt1 == [x \in MntIds |-> IF Contains(victims, x)
                                 THEN [mt0[x] EXCEPT !.umount = TRUE, !.attached = FALSE] ELSE mt0[x]]
        \* hide them from their parents' children lists
        mt2 == [x \in MntIds |-> [mt1[x] EXCEPT !.children = SelectSeq(mt1[x].children,
                                                                LAMBDA c : ~Contains(victims, c))]]
        pu == IF how.propagate THEN PropagateUmount(mt2, victims) ELSE [mt |-> mt2, set |-> victims]
        mt3 == BulkMakePrivate(pu.mt, pu.set)
    IN UmountLoop(mt3, pu.set, how, {})

(* ======================================================================= *)
(*                      The declarative specification                      *)
(* ======================================================================= *)

\* D1/D2: who gets a copy when something is attached at (P, d)
ExpectedReceivers(mt, nsanon, P, d) ==
    {n \in RecvSet(mt, P) : NeedSecondary(mt, nsanon, n, d)}

\* the master chain of n, nearest first
RECURSIVE MasterChain(_, _)
MasterChain(mt, n) ==
    IF mt[n].master = NoMnt THEN <<>> ELSE <<mt[n].master>> \o MasterChain(mt, mt[n].master)

\* the nearest peer group up n's master chain that contains a receiver or
\* the destination's group
RECURSIVE FirstGroupIn(_, _, _)
FirstGroupIn(mt, chain, S) ==
    IF chain = <<>> THEN {}
    ELSE IF PeerGroup(mt, Head(chain)) \cap S # {} THEN PeerGroup(mt, Head(chain))
    ELSE FirstGroupIn(mt, Tail(chain), S)

\* the tree below m in next_mnt() order, pruned to the mounts in T: the
\* mounts tucked under a copy (and whatever hangs off them) are not part of
\* the copy
RECURSIVE PreorderIn(_, _, _)
PreorderIn(mt, m, T) ==
    <<m>> \o Concat([i \in 1..Len(mt[m].children) |->
                     IF mt[m].children[i] \in T THEN PreorderIn(mt, mt[m].children[i], T) ELSE <<>>])

\* the shape of a tree as a sequence of (root, mountpoint) in next_mnt() order
Shape(mt, m, T) == [i \in 1..Len(PreorderIn(mt, m, T)) |->
                       [root |-> mt[PreorderIn(mt, m, T)[i]].root, mp |-> mt[PreorderIn(mt, m, T)[i]].mp]]

\* CopiesOK(mtb, mta, ...): after attaching S at (P, d) in mtb, giving mta:
\*  - exactly one new tree at (n, d) for every expected receiver n and none
\*    elsewhere,
\*  - every copy has the shape of S,
\*  - position by position, the copies' propagation graph is the receivers'
\*    graph: peers of receivers are peers, copies at P's peers are peers of
\*    S, the master of a copy is a copy at the nearest receiving group up
\*    the master chain (or S's group), and a copy is shared iff its
\*    receiver is.
CopiesOK(mtb, mta, nsanon, P, d, S) ==
    LET R == ExpectedReceivers(mtb, nsanon, P, d)
        New == Live(mta) \ Live(mtb)
        CopyAt(n) == {c \in New : mta[c].parent = n /\ mta[c].mp = d /\ mta[c].hashed}
        Cp(n) == CHOOSE c \in CopyAt(n) : TRUE
        GP == PeerGroup(mtb, P)
        \* the mounts that make up S: a moved S existed before, a new one is
        \* part of New; the copies are the rest of New.  A moved S that is a
        \* peer of P receives a copy of itself, which is not part of its shape
        Src == IF S \in Live(mtb) THEN Subtree(mtb, S) ELSE New
        PreS == PreorderIn(mta, S, Src)
        Pre(x) == PreorderIn(mta, x, New)
        Expected(n, i) ==
            LET g == FirstGroupIn(mtb, MasterChain(mtb, n), R \cup GP)
            IN IF g \cap GP # {}
               THEN {PreS[i]} \cup {Pre(Cp(x))[i] : x \in GP \cap R}
               ELSE {Pre(Cp(x))[i] : x \in g \cap R}
    IN /\ \A n \in R : Cardinality(CopyAt(n)) = 1
       /\ \A c \in New : mta[c].parent \in R \cup New \/ (mta[c].parent = P /\ c = S)
       /\ \A n \in R : Shape(mta, Cp(n), New) = Shape(mta, S, Src)
       /\ \A n \in R : \A i \in 1..Len(PreS) :
            LET c == Pre(Cp(n))[i]
            IN /\ mta[c].shared = mtb[n].shared
               /\ \A n2 \in R : Peers(mta, c, Pre(Cp(n2))[i]) <=> Peers(mtb, n, n2)
               /\ Peers(mta, c, PreS[i]) <=> (n \in GP)
               /\ (~(n \in GP)) => mta[c].master \in Expected(n, i)
               /\ (n \in GP) => mta[c].master = mta[PreS[i]].master

\* D3: the cognates of a closed set U (propagate_umount.txt "Finding candidates")
Cognates(mt, U) ==
    (UNION {{LookupMnt(mt, q, mt[m].mp) : q \in RecvSet(mt, mt[m].parent)} : m \in U}) \ ({NoMnt} \cup U)

\* "strictly inside": a child not overmounting the root
StrictKids(mt, x) == {c \in ToSet(mt[x].children) : mt[c].mp # mt[x].root}
Forbidden(mt, x, T) == \E c \in StrictKids(mt, x) : Subtree(mt, c) \ T # {}
\* the maximal non-shifting subset: drop forbidden elements until none is left
RECURSIVE MaxNonShifting(_, _)
MaxNonShifting(mt, T) ==
    LET F == {x \in T : Forbidden(mt, x, T)}
    IN IF F = {} THEN T ELSE MaxNonShifting(mt, T \ F)
\* the maximal non-revealing subset: a locked element whose parent stays goes
RECURSIVE MaxNonRevealing(_, _)
MaxNonRevealing(mt, T) ==
    LET F == {x \in T : mt[x].locked /\ mt[x].parent \notin T}
    IN IF F = {} THEN T ELSE MaxNonRevealing(mt, T \ F)

\* the set umount(2) of the tree rooted at m must take out, computed on the
\* table with the cognates of m already unlocked (propagate_mount_unlock)
ExpectedVictims(mt, m) ==
    LET mt0 == PropagateMountUnlock(mt, m)
        U == Subtree(mt0, m)
    IN MaxNonRevealing(mt0, MaxNonShifting(mt0, U \cup Cognates(mt0, U)))

\* sharedsubtree.rst 5f as written: the cognates of the mount itself that
\* have no submounts
\* 5f describes one mount without sub-mounts; for a tree the rule is applied
\* to every mount of it, each propagating from its own parent
DocUmountVictims(mt, m) ==
    LET U == Subtree(mt, m)
        Cog(x) == {LookupMnt(mt, q, mt[x].mp) : q \in RecvSet(mt, mt[x].parent)} \ ({NoMnt} \cup U)
    IN U \cup {c \in UNION {Cog(x) : x \in U} : mt[c].children = <<>>}

\* where a surviving overmount of a victim must end up: on the first
\* surviving ancestor, at the mountpoint of the bottom of the doomed stack
RECURSIVE SurvivorTarget(_, _, _, _)
SurvivorTarget(mt, T, p, d) ==
    IF p \notin T THEN [p |-> p, d |-> d] ELSE SurvivorTarget(mt, T, mt[p].parent, mt[p].mp)

\* the destination of the slaves of a victim v: a surviving peer if any,
\* else that of v's master
RECURSIVE Dest(_, _, _)
Dest(mt, T, v) ==
    LET surv == PeerGroup(mt, v) \ T
    IN IF surv # {} THEN surv
       ELSE IF mt[v].master = NoMnt THEN {NoMnt}
       ELSE IF mt[v].master \in T THEN Dest(mt, T, mt[v].master)
       ELSE {mt[v].master}

\* UmountVictimsOK(mtb, mta, T): after an umount that had to take out exactly T
UmountVictimsOK(mtb, mta, T) ==
    /\ {x \in Live(mtb) : ~mtb[x].umount /\ mta[x].umount} = T
    /\ \A x \in T : mta[x].gid = 0 /\ ~mta[x].shared /\ mta[x].master = NoMnt
                    /\ mta[x].slaves = <<>> /\ mta[x].npeer = x
    /\ \A x \in T : LET o == mtb[x].over IN
         (o # NoMnt /\ o \notin T) =>
            LET t == SurvivorTarget(mtb, T, mtb[o].parent, mtb[o].mp)
            IN mta[o].parent = t.p /\ mta[o].mp = t.d /\ mta[o].hashed
    /\ \A s \in Live(mtb) \ T :
         (mtb[s].master \in T) => mta[s].master \in Dest(mtb, T, mtb[s].master)
    /\ \A s \in Live(mtb) \ T :
         (mtb[s].master \notin T) => mta[s].master = mtb[s].master
    /\ \A s \in Live(mtb) \ T : mta[s].gid = mtb[s].gid /\ mta[s].shared = mtb[s].shared

=============================================================================
