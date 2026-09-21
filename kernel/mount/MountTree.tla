---------------------------- MODULE MountTree ----------------------------
(***************************************************************************)
(* The mount tree of fs/namespace.c, as the mount code sees it.            *)
(*                                                                         *)
(* Tree: master at 50d05c7c76c9 (v7.3-rc3) plus the staged revert of       *)
(* put_mnt_ns() to umount_tree(ns->root, 0).                               *)
(*                                                                         *)
(* One record per mount id.  The fields are the struct mount fields of     *)
(* fs/mount.h that the propagation code and the walkers read:             *)
(*                                                                         *)
(*   sb, root        mnt.mnt_sb, mnt.mnt_root                              *)
(*   parent, mp      mnt_parent (NoMnt when the mount is its own parent),  *)
(*                   mnt_mountpoint (the root dentry when detached)        *)
(*   hashed          on the mount_hashtable chain for (parent, mp)         *)
(*   children        mnt_mounts, in mnt_child order (list_add_tail)        *)
(*   over            overmount, the child mounted on this mount's root     *)
(*   ns, attached    mnt_ns; membership of the ns->mounts rbtree           *)
(*                   (mnt_ns_attached(), cleared by move_from_ns())        *)
(*   gid, shared,    mnt_group_id, T_SHARED, T_UNBINDABLE, T_MARKED,       *)
(*   unbind, marked, T_UMOUNT_CANDIDATE                                    *)
(*   cand                                                                  *)
(*   master          mnt_master                                            *)
(*   npeer           the next entry of the circular mnt_share list          *)
(*   slaves          mnt_slave_list, an hlist: head insertion              *)
(*   locked, umount  MNT_LOCKED, MNT_UMOUNT                                *)
(*   shrink, onexp,  MNT_SHRINKABLE, on an expiry list, mnt_expiry_mark    *)
(*   expmark                                                               *)
(*                                                                         *)
(* Dentries are a constant forest: DSb gives the superblock, DParent the   *)
(* parent (itself for a superblock root).  A struct mountpoint is not     *)
(* modelled: since d72c773237c0 it lives while something is attached at    *)
(* the dentry, which is derived state here.                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    MntIds,     \* mount ids, a set of naturals not containing 0
    NsIds,      \* namespace ids, a set of naturals not containing 0
    Sbs,        \* superblocks
    Dentries,   \* every dentry of every superblock
    DSb,        \* [Dentries -> Sbs]
    DParent,    \* [Dentries -> Dentries], a superblock root is its own parent
    SbRoot      \* [Sbs -> Dentries]

NoMnt == 0
NoNs  == 0

ASSUME NoMnt \notin MntIds /\ NoNs \notin NsIds
ASSUME \A d \in Dentries : DSb[DParent[d]] = DSb[d]
ASSUME \A s \in Sbs : DParent[SbRoot[s]] = SbRoot[s] /\ DSb[SbRoot[s]] = s

(* ---- sequences as lists ------------------------------------------------ *)

ToSet(s) == {s[i] : i \in 1..Len(s)}
Contains(s, x) == \E i \in 1..Len(s) : s[i] = x
Index(s, x) == CHOOSE i \in 1..Len(s) : s[i] = x
SeqDel(s, x) == SelectSeq(s, LAMBDA y : y # x)
\* list_add(new, old) / hlist_add_behind(new, old): new goes right after old
InsertAfter(s, x, new) ==
    LET i == Index(s, x) IN SubSeq(s, 1, i) \o <<new>> \o SubSeq(s, i + 1, Len(s))

RECURSIVE Concat(_)
Concat(ss) == IF ss = <<>> THEN <<>> ELSE Head(ss) \o Concat(Tail(ss))

(* ---- dentries ---------------------------------------------------------- *)

RECURSIVE AncestorsOrSelf(_)
AncestorsOrSelf(d) ==
    IF DParent[d] = d THEN {d} ELSE {d} \cup AncestorsOrSelf(DParent[d])

\* is_subdir(d, r): d is r or below r in the same superblock
IsSubdir(d, r) == DSb[d] = DSb[r] /\ r \in AncestorsOrSelf(d)

DChildren(d) == {c \in Dentries : DParent[c] = d /\ c # d}

(* ---- the mount record -------------------------------------------------- *)

MountRec ==
    [alive: BOOLEAN, sb: Sbs, root: Dentries,
     parent: MntIds \cup {NoMnt}, mp: Dentries, hashed: BOOLEAN,
     children: Seq(MntIds), over: MntIds \cup {NoMnt},
     ns: NsIds \cup {NoNs}, attached: BOOLEAN,
     gid: Nat, shared: BOOLEAN, unbind: BOOLEAN, marked: BOOLEAN, cand: BOOLEAN,
     master: MntIds \cup {NoMnt}, npeer: MntIds, slaves: Seq(MntIds),
     locked: BOOLEAN, umount: BOOLEAN,
     shrink: BOOLEAN, onexp: BOOLEAN, expmark: BOOLEAN]

SomeSb == CHOOSE s \in Sbs : TRUE

\* a free slot; every field canonical so that freed mounts do not multiply states
Dead(m) ==
    [alive |-> FALSE, sb |-> SomeSb, root |-> SbRoot[SomeSb],
     parent |-> NoMnt, mp |-> SbRoot[SomeSb], hashed |-> FALSE,
     children |-> <<>>, over |-> NoMnt,
     ns |-> NoNs, attached |-> FALSE,
     gid |-> 0, shared |-> FALSE, unbind |-> FALSE, marked |-> FALSE, cand |-> FALSE,
     master |-> NoMnt, npeer |-> m, slaves |-> <<>>,
     locked |-> FALSE, umount |-> FALSE,
     shrink |-> FALSE, onexp |-> FALSE, expmark |-> FALSE]

\* alloc_vfsmnt() + setup_mnt(): a fresh, detached, private mount of sb at root
Fresh(m, sb, root) ==
    [Dead(m) EXCEPT !.alive = TRUE, !.sb = sb, !.root = root, !.mp = root]

Live(mt) == {m \in MntIds : mt[m].alive}
FreeIds(mt) == {m \in MntIds : ~mt[m].alive}
\* canonical allocation: the smallest free id
NewId(mt) == CHOOSE m \in FreeIds(mt) : \A x \in FreeIds(mt) : m <= x

HasParent(mt, m) == mt[m].parent # NoMnt          \* mnt_has_parent()
IsMntShared(mt, m) == mt[m].shared                 \* IS_MNT_SHARED()
IsMntSlave(mt, m) == mt[m].master # NoMnt          \* IS_MNT_SLAVE()
IsMntNew(mt, m) == mt[m].ns = NoNs                 \* IS_MNT_NEW()
Peers(mt, a, b) == mt[a].gid = mt[b].gid /\ mt[a].gid # 0   \* peers()
WillBeUnmounted(mt, m) == mt[m].umount             \* will_be_unmounted()

(* ---- the hash and the tree --------------------------------------------- *)

\* __lookup_mnt(parent, dentry): the hashed mount attached at (p, d)
LookupMnt(mt, p, d) ==
    LET S == {x \in Live(mt) : mt[x].hashed /\ mt[x].parent = p /\ mt[x].mp = d}
    IN IF S = {} THEN NoMnt ELSE CHOOSE x \in S : TRUE

\* topmost_overmount()
RECURSIVE Topmost(_, _)
Topmost(mt, m) == IF mt[m].over = NoMnt THEN m ELSE Topmost(mt, mt[m].over)

\* the subtree in next_mnt() order: a mount, then each child's subtree in
\* mnt_mounts order (depth first, pre-order)
RECURSIVE Preorder(_, _)
Preorder(mt, m) ==
    <<m>> \o Concat([i \in 1..Len(mt[m].children) |-> Preorder(mt, mt[m].children[i])])

Subtree(mt, m) == ToSet(Preorder(mt, m))

RECURSIVE AncestorMnts(_, _)
AncestorMnts(mt, m) ==
    IF mt[m].parent = NoMnt THEN {} ELSE {mt[m].parent} \cup AncestorMnts(mt, mt[m].parent)

\* mount_is_ancestor(a, b): a is b or an ancestor of b
MountIsAncestor(mt, a, b) == a = b \/ a \in AncestorMnts(mt, b)

\* is_path_reachable(mnt, dentry, root): climb to root->mnt, then is_subdir
RECURSIVE IsPathReachable(_, _, _, _)
IsPathReachable(mt, m, d, root) ==
    IF m = root.mnt THEN IsSubdir(d, root.dentry)
    ELSE IF mt[m].parent = NoMnt THEN FALSE
    ELSE IsPathReachable(mt, mt[m].parent, mt[m].mp, root)

(* ---- the propagation graph, operationally ------------------------------ *)

\* the peer ring of m, following mnt_share
RECURSIVE RingFrom(_, _, _)
RingFrom(mt, m, x) ==
    IF mt[x].npeer = m THEN {x} ELSE {x} \cup RingFrom(mt, m, mt[x].npeer)
Ring(mt, m) == RingFrom(mt, m, m)

NextPeer(mt, m) == mt[m].npeer                     \* next_peer()
FirstSlave(mt, m) == Head(mt[m].slaves)            \* first_slave()
\* next_slave(): the next entry of the master's slave hlist, NoMnt at the end
\* (an hlist node that is on no list has next == NULL)
NextSlave(mt, m) ==
    IF mt[m].master = NoMnt THEN NoMnt
    ELSE LET s == mt[mt[m].master].slaves
             i == Index(s, m)
         IN IF i < Len(s) THEN s[i + 1] ELSE NoMnt
HasNextSlave(mt, m) == NextSlave(mt, m) # NoMnt    \* m->mnt_slave.next != NULL

\* __propagation_next(m, origin)
RECURSIVE PropNextUp(_, _, _)
PropNextUp(mt, m, origin) ==
    LET master == mt[m].master
    IN IF master = mt[origin].master
       THEN LET next == NextPeer(mt, m) IN IF next = origin THEN NoMnt ELSE next
       ELSE IF HasNextSlave(mt, m) THEN NextSlave(mt, m)
       ELSE PropNextUp(mt, master, origin)

\* propagation_next(m, origin)
PropagationNext(mt, m, origin) ==
    IF ~IsMntNew(mt, m) /\ mt[m].slaves # <<>> THEN FirstSlave(mt, m)
    ELSE PropNextUp(mt, m, origin)

\* skip_propagation_subtree(m, origin)
RECURSIVE SkipPeersOf(_, _, _, _)
SkipPeersOf(mt, m, p, origin) ==
    IF p # NoMnt /\ Peers(mt, m, p) THEN SkipPeersOf(mt, m, PropNextUp(mt, p, origin), origin)
    ELSE p
SkipPropagationSubtree(mt, m, origin) == SkipPeersOf(mt, m, PropNextUp(mt, m, origin), origin)

\* next_group(m, origin): the first mount of the next peer group, depth first
RECURSIVE NextGroupInner(_, _, _)
RECURSIVE NextGroupUp(_, _, _)
RECURSIVE NextGroup(_, _, _)
\* the inner loop: walk the peers of the current group looking for slaves,
\* stop at the last peer of the segment
NextGroupInner(mt, m, origin) ==
    IF ~IsMntNew(mt, m) /\ mt[m].slaves # <<>> THEN [found |-> TRUE, m |-> FirstSlave(mt, m)]
    ELSE LET next == NextPeer(mt, m)
         IN IF mt[m].gid = mt[origin].gid
            THEN IF next = origin THEN [found |-> TRUE, m |-> NoMnt]
                 ELSE NextGroupInner(mt, next, origin)
            ELSE IF NextSlave(mt, m) # next THEN [found |-> FALSE, m |-> m]
            ELSE NextGroupInner(mt, next, origin)
\* the second loop: m is the last peer of its group
NextGroupUp(mt, m, origin) ==
    LET master == mt[m].master
    IN IF HasNextSlave(mt, m) THEN [found |-> TRUE, m |-> NextSlave(mt, m)]
       ELSE LET m2 == NextPeer(mt, master)
            IN IF mt[master].gid = mt[origin].gid THEN [found |-> FALSE, m |-> m2]
               ELSE IF NextSlave(mt, master) = m2 THEN [found |-> FALSE, m |-> m2]
               ELSE NextGroupUp(mt, master, origin)
NextGroup(mt, m, origin) ==
    LET r1 == NextGroupInner(mt, m, origin)
    IN IF r1.found THEN r1.m
       ELSE LET r2 == NextGroupUp(mt, r1.m, origin)
            IN IF r2.found THEN r2.m
               ELSE IF r2.m = origin THEN NoMnt
               ELSE NextGroup(mt, r2.m, origin)

\* everything propagation_next() enumerates from origin, in that order
RECURSIVE PropWalk(_, _, _)
PropWalk(mt, m, origin) ==
    IF m = NoMnt THEN <<>> ELSE <<m>> \o PropWalk(mt, PropagationNext(mt, m, origin), origin)
PropagationOrder(mt, origin) == PropWalk(mt, PropagationNext(mt, origin, origin), origin)

(* ---- the propagation graph, declaratively ------------------------------ *)

PeerGroup(mt, m) == IF mt[m].gid = 0 THEN {m} ELSE {x \in Live(mt) : mt[x].gid = mt[m].gid}
SlavesOfGroup(mt, m) == {x \in Live(mt) : mt[x].master \in PeerGroup(mt, m)}

\* the mounts that receive propagation from m: m's peers, their slaves, the
\* peers and slaves of those, and so on (sharedsubtree.rst 5a)
RECURSIVE RecvClosure(_, _)
RecvClosure(mt, S) ==
    LET next == S \cup UNION {PeerGroup(mt, x) : x \in S}
                  \cup UNION {SlavesOfGroup(mt, x) : x \in S}
    IN IF next = S THEN S ELSE RecvClosure(mt, next)
RecvSet(mt, m) == RecvClosure(mt, {m}) \ {m}

(* ---- structural invariants (fs/mount.h and sharedsubtree.rst) ---------- *)

\* at most one hashed mount per (parent, mountpoint)     1064f874abc0, ffdc52fbbd58
OneMountPerMountpoint(mt) ==
    \A a, b \in Live(mt) :
        (mt[a].hashed /\ mt[b].hashed /\ mt[a].parent = mt[b].parent /\ mt[a].mp = mt[b].mp) => a = b

\* the children list is exactly the hashed mounts with this parent, and the
\* overmount field is the child on the root                  make_visible()
ChildrenOK(mt) ==
    \A p \in Live(mt) :
        /\ ToSet(mt[p].children) = {c \in Live(mt) : mt[c].parent = p /\ mt[c].hashed}
        /\ \A i, j \in 1..Len(mt[p].children) : mt[p].children[i] = mt[p].children[j] => i = j
        \* an unmounted mount keeps whatever mnt_change_mountpoint() left
        \* there when its surviving overmount was reparented (not cleared
        \* in the kernel either)
        /\ ~mt[p].umount => mt[p].over = LookupMnt(mt, p, mt[p].root)

\* a mountpoint lies in the parent's superblock, under the parent's root
MountpointOK(mt) ==
    \A c \in Live(mt) : HasParent(mt, c) => IsSubdir(mt[c].mp, mt[mt[c].parent].root)

\* the parent of a live mount is live; no cycles
ParentOK(mt) ==
    \A c \in Live(mt) : HasParent(mt, c) => mt[mt[c].parent].alive /\ c \notin AncestorMnts(mt, c)

\* T_SHARED <=> a group id                                     5235d448c48e, f6cc2f4e3d30
SharedOK(mt) ==
    \A m \in Live(mt) : mt[m].shared <=> mt[m].gid # 0

\* the peer ring is exactly the group; a non-shared mount rings with itself
RingOK(mt) ==
    \A m \in Live(mt) :
        /\ mt[m].npeer \in Live(mt)
        /\ Ring(mt, m) = PeerGroup(mt, m)

\* slave lists: n is on m's list iff n's master is m; no duplicates; only
\* shared mounts have slaves; peers share one master and form a contiguous
\* segment of its list                                    sharedsubtree.rst D2-D4
SlavesOK(mt) ==
    \A m \in Live(mt) :
        /\ ToSet(mt[m].slaves) = {n \in Live(mt) : mt[n].master = m}
        /\ \A i, j \in 1..Len(mt[m].slaves) : mt[m].slaves[i] = mt[m].slaves[j] => i = j
        /\ mt[m].slaves # <<>> => mt[m].shared
        /\ mt[m].master # NoMnt => mt[mt[m].master].alive
        /\ \A n \in PeerGroup(mt, m) : mt[n].master = mt[m].master
        /\ (mt[m].master # NoMnt /\ mt[m].gid # 0) =>
              LET s == mt[mt[m].master].slaves
                  idx == {i \in 1..Len(s) : s[i] \in PeerGroup(mt, m)}
              IN \A i \in idx : \A j \in idx : \A k \in i..j : k \in idx

\* unbindable is private
UnbindableOK(mt) ==
    \A m \in Live(mt) : mt[m].unbind => (~mt[m].shared /\ mt[m].master = NoMnt)

\* nothing is left marked between operations
MarksClear(mt) == \A m \in Live(mt) : ~mt[m].marked /\ ~mt[m].cand

\* MNT_UMOUNT means out of every namespace; an attached mount is in one
UmountOK(mt) ==
    \A m \in Live(mt) :
        /\ mt[m].umount => (mt[m].ns = NoNs /\ ~mt[m].attached)
        /\ mt[m].attached => mt[m].ns # NoNs

\* a connected mount under an unmounted parent is itself unmounted
\* (disconnect_mount(): "umounted mounts may not be connected to mounted mounts")
ConnectedOK(mt) ==
    \A c \in Live(mt) :
        (HasParent(mt, c) /\ mt[mt[c].parent].umount) => mt[c].umount

\* MNT_LOCKED only on mounts with a parent (d08fa7f44ae7); a stuck child
\* of a freed parent keeps the bit and has none, but it is out of every
\* namespace by then
LockedOK(mt) == \A m \in Live(mt) : (mt[m].locked /\ ~mt[m].umount) => HasParent(mt, m)

StructureOK(mt) ==
    /\ OneMountPerMountpoint(mt)
    /\ ChildrenOK(mt)
    /\ MountpointOK(mt)
    /\ ParentOK(mt)
    /\ SharedOK(mt)
    /\ RingOK(mt)
    /\ SlavesOK(mt)
    /\ UnbindableOK(mt)
    /\ MarksClear(mt)
    /\ UmountOK(mt)
    /\ ConnectedOK(mt)
    /\ LockedOK(mt)

=============================================================================
