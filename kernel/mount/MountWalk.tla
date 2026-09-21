----------------------------- MODULE MountWalk -----------------------------
(***************************************************************************)
(* The RCU path walk against mount, lazy umount and move of one mount.     *)
(*                                                                         *)
(* Dentries are a constant forest: the root filesystem S (root R, A below *)
(* it, B below A, An a negative dentry below A) and the filesystem F that  *)
(* gets mounted (root F, Fa below it, Fn negative).  No renames, no        *)
(* symlinks, no automounts; d_seq never changes.                           *)
(*                                                                         *)
(* Walkers run one fixed program each, a sequence of dentries and "..".    *)
(* In RCU mode a step is one lockless read: path_init() samples m_seq,     *)
(* __follow_mount_rcu() reads DCACHE_MOUNTED and __lookup_mnt() (which may *)
(* miss while a mount_lock writer runs: the hash chains are being          *)
(* rewritten) and rechecks m_seq after a hop and after a miss,             *)
(* follow_dotdot_rcu() with choose_mountpoint_rcu() reads mnt_parent and   *)
(* mnt_mountpoint and rechecks m_seq, a negative dentry is -ENOENT with no *)
(* recheck (step_into()), a scoped ".." rechecks m_seq for -EAGAIN         *)
(* (handle_dots()), and complete_walk() legitimizes the result against     *)
(* m_seq.  A failed recheck is -ECHILD: the walk restarts in REF mode,     *)
(* where every hop takes a reference under the seqcount (lookup_mnt(),     *)
(* choose_mountpoint()).                                                   *)
(*                                                                         *)
(* Writers, one mount_lock write section each, its stores one step at a    *)
(* time so an unvalidated reader can see the section half applied:        *)
(* attach (d_set_mounted() outside the section, then the hash insert),    *)
(* lazy umount (unhash, mnt_parent = self, DCACHE_MOUNTED cleared with the *)
(* mountpoint, then synchronize_rcu() and the put that frees the mount),   *)
(* move (unhash, new parent and mountpoint, rehash, old mountpoint freed). *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
    Dentries, DParent, DName, DSb, SbRoot, Negative,   \* the forest: names are per directory
    RootSb, NewSb,       \* the root filesystem and the one the mounter mounts
    MntIds,              \* mount ids; 1 is the root mount
    Walkers, WProg, WRoot, WScoped,             \* the walkers: program, root, scoped?
    MaxRestarts,
    Mounts,              \* mounts the mounter makes (0..2), at any place it can reach
    CHANGE,              \* "none", "umount" or "move": what happens to the victim
    Victim,              \* the mount the changer works on
    FIX_RECHECK_MISS,    \* m_seq rechecked after a miss of __lookup_mnt() (b37199e626b3)
    FIX_RECHECK_HOP,     \* m_seq rechecked after crossing into a mount (20aac6c60981)
    FIX_RECHECK_DOTDOT,  \* m_seq rechecked after choose_mountpoint_rcu() (aed434ada685)
    FIX_SCOPED_EAGAIN,   \* the -EAGAIN check of a scoped ".." (handle_dots())
    FIX_RCU_FREE         \* the put after umount waits for the grace period

NoMnt == 0
NoD == "none"
M == "M"
C == "C"
Tasks == Walkers \cup {M, C}
RootMnt == 1

VARIABLES
    mnt,       \* [MntIds -> [alive, freed, parent, mp, root, hashed, ns, count]]
    mounted,   \* [Dentries -> BOOLEAN]: DCACHE_MOUNTED
    seqv,      \* mount_lock's seqcount
    rcu,       \* [Tasks -> BOOLEAN]
    gp,        \* synchronize_rcu(): [on, wait]
    pc,        \* [Tasks -> label]
    mode,      \* [Walkers -> "rcu" | "ref"]
    path,      \* [Walkers -> [mnt, d]]
    nxt,       \* [Walkers -> dentry]: the component being entered
    ip,        \* [Walkers -> Nat]: the program counter
    mseq,      \* [Walkers -> Nat]: nd->m_seq
    restarts,  \* [Walkers -> Nat]
    res,       \* [Walkers -> result]: [mnt, d] or an errno string, "" while walking
    held,      \* [Walkers -> mount or NoMnt]: the reference a REF walker holds
    tgt,       \* the mounter's target [mnt, d]
    ctgt,      \* the changer's target [mnt, d]
    victim,    \* the mount the changer works on
    budget,    \* mounts the mounter still makes
    hist,      \* witnesses: [miss, esc, climb]
    rok,       \* [Walkers -> BOOLEAN]: the result matched the sequential walk when it was produced
    todo,      \* the mounts whose namespace reference the changer still has to drop
    seen       \* [Walkers -> SUBSET result]: the sequential results at the instants since path_init()

vars == <<mnt, mounted, seqv, rcu, gp, pc, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo, seen>>

(* ---- the tree --------------------------------------------------------- *)

Live == {x \in MntIds : mnt[x].alive}
HasParent(x) == mnt[x].parent # x
Children(d) == {e \in Dentries : DParent[e] = d /\ e # d}
\* the child of d called n, or NoD
Child(d, n) == LET S == {e \in Children(d) : DName[e] = n} IN IF S = {} THEN NoD ELSE CHOOSE e \in S : TRUE
Root(x) == mnt[x].root
\* __lookup_mnt() as the hash really is
LookupMnt(p, d) ==
    LET S == {x \in Live : mnt[x].hashed /\ mnt[x].parent = p /\ mnt[x].mp = d /\ x # p}
    IN IF S = {} THEN NoMnt ELSE CHOOSE x \in S : TRUE
RECURSIVE Topmost(_)
Topmost(x) == LET o == LookupMnt(x, Root(x)) IN IF o = NoMnt THEN x ELSE Topmost(o)
Writing == seqv % 2 = 1

\* the sequential walk of a program from a root over the current tree:
\* what a lookup with everything locked would produce
RECURSIVE Cross(_, _)
Cross(m, d) == LET o == LookupMnt(m, d) IN IF o = NoMnt THEN [mnt |-> m, d |-> d] ELSE Cross(o, Root(o))
RECURSIVE Climb(_, _)
Climb(m, root) ==
    IF ~HasParent(m) THEN [found |-> FALSE, mnt |-> m, d |-> Root(m)]
    ELSE LET p == mnt[m].parent
             mp == mnt[m].mp
         IN IF p = root.mnt /\ mp = root.d THEN [found |-> FALSE, mnt |-> m, d |-> Root(m)]
            ELSE IF mp # Root(p) THEN [found |-> TRUE, mnt |-> p, d |-> mp]
            ELSE Climb(p, root)
DotDot(pos, root) ==
    IF pos = root THEN pos
    ELSE IF pos.d = Root(pos.mnt)
         THEN LET c == Climb(pos.mnt, root)
              IN IF c.found THEN [mnt |-> c.mnt, d |-> DParent[c.d]] ELSE pos
         ELSE [mnt |-> pos.mnt, d |-> DParent[pos.d]]
\* results: a position with an empty error, or an errno
Err(e) == [err |-> e, mnt |-> NoMnt, d |-> NoD]
Ok(pos) == [err |-> "", mnt |-> pos.mnt, d |-> pos.d]
RECURSIVE Resolve(_, _, _)
Resolve(prog, pos, root) ==
    IF prog = <<>> THEN Ok(pos)
    ELSE LET x == Head(prog)
             c == IF x = ".." THEN NoD ELSE Child(pos.d, x)
         IN IF x = ".." THEN Resolve(Tail(prog), DotDot(pos, root), root)
            ELSE IF c = NoD \/ c \in Negative THEN Err("ENOENT")
            ELSE Resolve(Tail(prog), Cross(pos.mnt, c), root)

\* is_path_reachable(): pos is under root
RECURSIVE UnderD(_, _)
UnderD(d, a) == IF d = a THEN TRUE ELSE IF DParent[d] = d THEN FALSE ELSE UnderD(DParent[d], a)
RECURSIVE Under(_, _)
Under(pos, root) ==
    IF pos.mnt = root.mnt THEN UnderD(pos.d, root.d)
    ELSE IF ~HasParent(pos.mnt) THEN FALSE
    ELSE Under([mnt |-> mnt[pos.mnt].parent, d |-> mnt[pos.mnt].mp], root)

FreeId == CHOOSE x \in MntIds \ Live : \A y \in MntIds \ Live : x <= y

\* the sequential result a locked walk would get right now
Now(w) == Resolve(WProg[w], WRoot[w], WRoot[w])

(* ---- init --------------------------------------------------------------- *)

Fresh == [alive |-> FALSE, freed |-> FALSE, parent |-> 0, mp |-> NoD, root |-> NoD,
          hashed |-> FALSE, ns |-> FALSE, count |-> 0]
Init ==
    /\ mnt = [x \in MntIds |-> IF x = RootMnt
                                THEN [Fresh EXCEPT !.alive = TRUE, !.parent = x, !.mp = SbRoot[RootSb],
                                                   !.root = SbRoot[RootSb], !.ns = TRUE, !.count = 1]
                                ELSE Fresh]
    /\ mounted = [d \in Dentries |-> FALSE]
    /\ seqv = 0
    /\ rcu = [t \in Tasks |-> FALSE]
    /\ gp = [on |-> FALSE, wait |-> {}]
    /\ pc = [t \in Tasks |-> IF t \in Walkers THEN "w_init" ELSE IF t = M THEN "m_pick" ELSE "c_pick"]
    /\ mode = [w \in Walkers |-> "rcu"]
    /\ path = [w \in Walkers |-> WRoot[w]]
    /\ nxt = [w \in Walkers |-> NoD]
    /\ ip = [w \in Walkers |-> 1]
    /\ mseq = [w \in Walkers |-> 0]
    /\ restarts = [w \in Walkers |-> 0]
    /\ res = [w \in Walkers |-> Err("walking")]
    /\ held = [w \in Walkers |-> NoMnt]
    /\ tgt = [mnt |-> NoMnt, d |-> NoD]
    /\ ctgt = [mnt |-> NoMnt, d |-> NoD]
    /\ victim = NoMnt
    /\ budget = Mounts
    /\ hist = [miss |-> FALSE, esc |-> FALSE, climb |-> FALSE]
    /\ rok = [w \in Walkers |-> TRUE]
    /\ todo = {}
    /\ seen = [w \in Walkers |-> {}]

Readers == {t \in Tasks : rcu[t]}
RcuOut(w) == rcu' = [rcu EXCEPT ![w] = FALSE] /\ gp' = [gp EXCEPT !.wait = @ \ {w}]

(* ---- the RCU walker ----------------------------------------------------- *)

\* -ECHILD: leave RCU, start over in REF mode from the root
Restart(w) ==
    /\ RcuOut(w)
    /\ mode' = [mode EXCEPT ![w] = "ref"]
    /\ path' = [path EXCEPT ![w] = WRoot[w]]
    /\ ip' = [ip EXCEPT ![w] = 1]
    /\ restarts' = [restarts EXCEPT ![w] = @ + 1]
    /\ pc' = [pc EXCEPT ![w] = "r_comp"]
    /\ held' = [held EXCEPT ![w] = RootMnt]
    /\ mnt' = [mnt EXCEPT ![RootMnt].count = @ + 1]

\* path_init(): rcu_read_lock(), nd->m_seq = read_seqbegin(&mount_lock)
WInit(w) ==
    /\ pc[w] = "w_init" /\ ~Writing
    /\ rcu' = [rcu EXCEPT ![w] = TRUE]
    /\ mseq' = [mseq EXCEPT ![w] = seqv]
    /\ seen' = [seen EXCEPT ![w] = {Now(w)}]
    /\ pc' = [pc EXCEPT ![w] = "w_comp"]
    /\ UNCHANGED <<mnt, mounted, seqv, gp, mode, path, nxt, ip, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo>>

\* the next component: a child dentry (a negative one is -ENOENT with no
\* recheck, a missing one goes through lookup_slow(), i.e. unlazy first)
\* or "..", or the end of the program: complete_walk()
WComp(w) ==
    /\ pc[w] = "w_comp"
    /\ IF ip[w] > Len(WProg[w])
       THEN pc' = [pc EXCEPT ![w] = "w_complete"] /\ UNCHANGED nxt
       ELSE LET x == WProg[w][ip[w]]
                c == IF x = ".." THEN NoD ELSE Child(path[w].d, x)
            IN IF x = ".." THEN pc' = [pc EXCEPT ![w] = "w_dotdot"] /\ UNCHANGED nxt
               ELSE IF c = NoD THEN pc' = [pc EXCEPT ![w] = "w_slow"] /\ UNCHANGED nxt
               ELSE nxt' = [nxt EXCEPT ![w] = c] /\ pc' = [pc EXCEPT ![w] = "w_mounts"]
    /\ UNCHANGED <<mnt, mounted, seqv, rcu, gp, mode, path, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo, seen>>

\* lookup_slow() needs REF mode: try_to_unlazy(), then -ENOENT
WSlow(w) ==
    /\ pc[w] = "w_slow"
    /\ IF seqv = mseq[w]
       THEN /\ RcuOut(w) /\ res' = [res EXCEPT ![w] = Err("ENOENT")] /\ pc' = [pc EXCEPT ![w] = "done"]
            /\ rok' = [rok EXCEPT ![w] = Resolve(WProg[w], WRoot[w], WRoot[w]) = Err("ENOENT")]
            /\ UNCHANGED <<mode, path, ip, restarts, held, mnt, seen>>
       ELSE Restart(w) /\ UNCHANGED <<res, rok, seen>>
    /\ UNCHANGED <<mounted, seqv, nxt, mseq, tgt, ctgt, victim, budget, hist, todo, seen>>

\* __follow_mount_rcu(): DCACHE_MOUNTED, __lookup_mnt() (a miss is possible
\* while a writer runs), the rechecks; then step_into()'s -ENOENT for a
\* negative dentry without any recheck
WMounts(w) ==
    /\ pc[w] = "w_mounts"
    /\ LET d == nxt[w]
           m == path[w].mnt
       IN IF ~mounted[d]
          THEN \* nothing mounted here as far as the flag says: no recheck
               /\ hist' = [hist EXCEPT !.esc = @ \/ Writing]
               /\ pc' = [pc EXCEPT ![w] = "w_step"]
               /\ UNCHANGED <<path, nxt, mode, ip, restarts, held, mnt, rcu, gp, seen>>
          ELSE \E q \in ({LookupMnt(m, d)} \cup (IF Writing THEN {NoMnt} ELSE {})) :
               IF q = NoMnt
               THEN /\ hist' = [hist EXCEPT !.miss = @ \/ (LookupMnt(m, d) # NoMnt)]
                    /\ IF FIX_RECHECK_MISS /\ seqv # mseq[w]
                       THEN Restart(w) /\ UNCHANGED nxt
                       ELSE pc' = [pc EXCEPT ![w] = "w_step"] /\ UNCHANGED <<path, nxt, mode, ip, restarts, held, mnt, rcu, gp, seen>>
               ELSE /\ UNCHANGED hist
                    /\ IF FIX_RECHECK_HOP /\ seqv # mseq[w]
                       THEN Restart(w) /\ UNCHANGED nxt
                       ELSE /\ path' = [path EXCEPT ![w] = [mnt |-> q, d |-> Root(q)]]
                            /\ nxt' = [nxt EXCEPT ![w] = Root(q)]
                            /\ UNCHANGED <<pc, mode, ip, restarts, held, mnt, rcu, gp, seen>>
    /\ UNCHANGED <<mounted, seqv, mseq, res, tgt, ctgt, victim, budget, rok, todo, seen>>

WStep(w) ==
    /\ pc[w] = "w_step"
    /\ IF nxt[w] \in Negative
       THEN /\ RcuOut(w) /\ res' = [res EXCEPT ![w] = Err("ENOENT")] /\ pc' = [pc EXCEPT ![w] = "done"]
            /\ rok' = [rok EXCEPT ![w] = Err("ENOENT") \in seen[w] \cup {Now(w)}]
            /\ UNCHANGED <<path, ip, seen>>
       ELSE /\ path' = [path EXCEPT ![w] = [mnt |-> path[w].mnt, d |-> nxt[w]]]
            /\ ip' = [ip EXCEPT ![w] = @ + 1]
            /\ pc' = [pc EXCEPT ![w] = "w_comp"]
            /\ UNCHANGED <<rcu, gp, res, rok, seen>>
    /\ UNCHANGED <<mnt, mounted, seqv, mode, nxt, mseq, restarts, held, tgt, ctgt, victim, budget, hist, todo, seen>>

\* follow_dotdot_rcu(): in_root, or choose_mountpoint_rcu() over the current
\* mnt_parent/mnt_mountpoint values, then the recheck, then the parent dentry;
\* a scoped walk rechecks m_seq for -EAGAIN afterwards
WDotDot(w) ==
    /\ pc[w] = "w_dotdot"
    /\ LET pos == path[w]
           root == WRoot[w]
           climbed == pos # root /\ pos.d = Root(pos.mnt)
           c == Climb(pos.mnt, root)
           inroot == pos = root \/ (climbed /\ ~c.found)
           newpos == IF inroot THEN pos
                     ELSE IF climbed THEN [mnt |-> c.mnt, d |-> DParent[c.d]]
                     ELSE [mnt |-> pos.mnt, d |-> DParent[pos.d]]
           mismatch == seqv # mseq[w]
           fail == mismatch /\ (inroot \/ (climbed /\ FIX_RECHECK_DOTDOT))
           eagain == WScoped[w] /\ FIX_SCOPED_EAGAIN /\ mismatch
       IN IF fail
          THEN Restart(w) /\ UNCHANGED <<res, hist, rok, todo, seen>>
          ELSE IF eagain
          THEN /\ RcuOut(w) /\ res' = [res EXCEPT ![w] = Err("EAGAIN")] /\ pc' = [pc EXCEPT ![w] = "done"]
               /\ UNCHANGED <<mode, path, ip, restarts, held, mnt, hist, rok, todo, seen>>
          ELSE /\ path' = [path EXCEPT ![w] = newpos]
               /\ ip' = [ip EXCEPT ![w] = @ + 1]
               /\ hist' = [hist EXCEPT !.climb = @ \/ (climbed /\ c.found)]
               /\ pc' = [pc EXCEPT ![w] = "w_comp"]
               /\ UNCHANGED <<rcu, gp, mode, restarts, held, mnt, res, seen>>
    /\ UNCHANGED <<mounted, seqv, nxt, mseq, tgt, ctgt, victim, budget, rok, todo, seen>>

\* complete_walk(): try_to_unlazy() legitimizes the result against m_seq
WComplete(w) ==
    /\ pc[w] = "w_complete"
    /\ IF seqv = mseq[w]
       THEN /\ RcuOut(w)
            /\ res' = [res EXCEPT ![w] = Ok(path[w])]
            /\ rok' = [rok EXCEPT ![w] = Resolve(WProg[w], WRoot[w], WRoot[w]) = Ok(path[w])]
            /\ held' = [held EXCEPT ![w] = path[w].mnt]
            /\ mnt' = [mnt EXCEPT ![path[w].mnt].count = @ + 1]
            /\ pc' = [pc EXCEPT ![w] = "done"]
            /\ UNCHANGED <<mode, path, ip, restarts, seen>>
       ELSE Restart(w) /\ UNCHANGED <<res, rok, seen>>
    /\ UNCHANGED <<mounted, seqv, nxt, mseq, tgt, ctgt, victim, budget, hist, todo, seen>>

RcuWalk(w) == WInit(w) \/ WComp(w) \/ WSlow(w) \/ WMounts(w) \/ WStep(w) \/ WDotDot(w) \/ WComplete(w)

(* ---- the REF walker ------------------------------------------------------ *)

\* a reference moves from the old mount to the new one
Rebase(w, m) ==
    /\ held' = [held EXCEPT ![w] = m]
    /\ mnt' = [mnt EXCEPT ![held[w]].count = @ - 1, ![m].count = @ + 1]

\* one component in REF mode: lookup_mnt() until nothing is mounted (each
\* one under the seqcount with a reference), or follow_dotdot() with
\* choose_mountpoint(), or the end
RComp(w) ==
    /\ pc[w] = "r_comp" /\ ~Writing
    /\ IF ip[w] > Len(WProg[w])
       THEN /\ res' = [res EXCEPT ![w] = Ok(path[w])] /\ pc' = [pc EXCEPT ![w] = "done"]
            /\ UNCHANGED <<path, ip, held, mnt, seen>>
       ELSE LET x == WProg[w][ip[w]]
                pos == path[w]
            IN IF x = ".."
               THEN LET np == DotDot(pos, WRoot[w])
                    IN /\ path' = [path EXCEPT ![w] = np] /\ ip' = [ip EXCEPT ![w] = @ + 1]
                       /\ IF np.mnt # pos.mnt THEN Rebase(w, np.mnt) ELSE UNCHANGED <<held, mnt, seen>>
                       /\ UNCHANGED <<res, pc, seen>>
               ELSE IF Child(pos.d, x) = NoD \/ Child(pos.d, x) \in Negative
               THEN /\ res' = [res EXCEPT ![w] = Err("ENOENT")] /\ pc' = [pc EXCEPT ![w] = "done"]
                    /\ UNCHANGED <<path, ip, held, mnt, seen>>
               ELSE LET np == Cross(pos.mnt, Child(pos.d, x))
                    IN /\ path' = [path EXCEPT ![w] = np] /\ ip' = [ip EXCEPT ![w] = @ + 1]
                       /\ IF np.mnt # pos.mnt THEN Rebase(w, np.mnt) ELSE UNCHANGED <<held, mnt, seen>>
                       /\ UNCHANGED <<res, pc, seen>>
    /\ UNCHANGED <<mounted, seqv, rcu, gp, mode, nxt, mseq, restarts, tgt, ctgt, victim, budget, hist, rok, todo, seen>>

(* ---- the mounter ------------------------------------------------------- *)

\* do_lock_mount(): where the new mount goes; d_set_mounted() before the
\* write section
MPick ==
    /\ pc[M] = "m_pick"
    /\ IF budget = 0 THEN pc' = [pc EXCEPT ![M] = "done"] /\ UNCHANGED <<tgt, mounted, seen>>
       ELSE \E p \in Live, d \in Dentries :
            /\ mnt[p].ns /\ DSb[d] = DSb[Root(p)] /\ d \notin Negative
            /\ LET w == Cross(p, d) IN
               /\ tgt' = w
               /\ mounted' = [mounted EXCEPT ![w.d] = TRUE]
               /\ pc' = [pc EXCEPT ![M] = "m_lock"]
    /\ UNCHANGED <<mnt, seqv, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, ctgt, victim, budget, hist, rok, todo, seen>>
\* lock_mount_hash(), the attach, unlock_mount_hash()
MLock ==
    /\ pc[M] = "m_lock" /\ ~Writing
    /\ seqv' = seqv + 1
    /\ pc' = [pc EXCEPT ![M] = "m_attach"]
    /\ UNCHANGED <<mnt, mounted, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo, seen>>
MAttach ==
    /\ pc[M] = "m_attach"
    /\ LET x == FreeId
       IN mnt' = [mnt EXCEPT ![x] = [Fresh EXCEPT !.alive = TRUE, !.parent = tgt.mnt, !.mp = tgt.d,
                                                    !.root = SbRoot[NewSb], !.hashed = TRUE, !.ns = TRUE, !.count = 1]]
    /\ budget' = budget - 1
    /\ pc' = [pc EXCEPT ![M] = "m_unlock"]
    /\ UNCHANGED <<mounted, seqv, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, hist, rok, todo, seen>>
Walking(w) == mode[w] = "rcu" /\ pc[w] \notin {"w_init", "done"}
MUnlock ==
    /\ pc[M] = "m_unlock"
    /\ seqv' = seqv + 1
    /\ seen' = [w \in Walkers |-> IF Walking(w) THEN seen[w] \cup {Now(w)} ELSE seen[w]]
    /\ pc' = [pc EXCEPT ![M] = "m_pick"]
    /\ UNCHANGED <<mnt, mounted, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo>>
Mounter == MPick \/ MLock \/ MAttach \/ MUnlock

(* ---- the changer: lazy umount or move of the first new mount ------------ *)

Subtree(x) == {y \in Live : y = x \/ (HasParent(y) /\ mnt[y].parent = x)}
\* maybe_free_mountpoint(): DCACHE_MOUNTED goes with the last mount on the
\* dentry, unless the mounter's pinned_mountpoint is still on its m_list
Unmounted(mt, d) == /\ \A y \in MntIds : ~(mt[y].alive /\ mt[y].parent # y /\ mt[y].mp = d)
                    /\ ~(pc[M] \in {"m_lock", "m_attach"} /\ tgt.d = d)

CPick ==
    /\ pc[C] = "c_pick"
    /\ IF CHANGE = "none" THEN pc' = [pc EXCEPT ![C] = "done"] /\ UNCHANGED <<victim, mounted, ctgt, seen>>
       ELSE /\ mnt[Victim].alive /\ mnt[Victim].hashed /\ mnt[Victim].ns
            /\ victim' = Victim
            /\ IF CHANGE = "umount"
               THEN pc' = [pc EXCEPT ![C] = "c_lock"] /\ UNCHANGED <<mounted, ctgt, seen>>
               ELSE \E p \in Live, d \in Dentries :
                    /\ mnt[p].ns /\ p \notin Subtree(Victim) /\ DSb[d] = DSb[Root(p)] /\ d \notin Negative
                    /\ LET w == Cross(p, d) IN
                       /\ w.mnt \notin Subtree(Victim) /\ ~(w.mnt = mnt[Victim].parent /\ w.d = mnt[Victim].mp)
                       /\ ctgt' = w
                       /\ mounted' = [mounted EXCEPT ![w.d] = TRUE]
                       /\ pc' = [pc EXCEPT ![C] = "c_lock"]
    /\ UNCHANGED <<mnt, seqv, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, tgt, budget, hist, rok, todo, seen>>
CLock ==
    /\ pc[C] = "c_lock" /\ ~Writing
    /\ seqv' = seqv + 1
    /\ pc' = [pc EXCEPT ![C] = IF CHANGE = "umount" THEN "c_unhash" ELSE "c_mv_unhash"]
    /\ UNCHANGED <<mnt, mounted, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo, seen>>
\* umount_tree(UMOUNT_PROPAGATE): the tree leaves the namespace and the hash
CUnhash ==
    /\ pc[C] = "c_unhash"
    /\ LET tree == Subtree(victim)
           mt1 == [y \in MntIds |-> IF y \in tree
                                     THEN [mnt[y] EXCEPT !.hashed = FALSE, !.ns = FALSE, !.parent = y, !.mp = mnt[y].root]
                                     ELSE mnt[y]]
       IN /\ mnt' = mt1
          /\ mounted' = [d \in Dentries |-> mounted[d] /\ ~Unmounted(mt1, d)]
          /\ todo' = tree
    /\ pc' = [pc EXCEPT ![C] = "c_unlock"]
    /\ UNCHANGED <<seqv, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, seen>>
\* the move: unhash, new parent and mountpoint, rehash, old mountpoint gone
CMvUnhash ==
    /\ pc[C] = "c_mv_unhash"
    /\ mnt' = [mnt EXCEPT ![victim].hashed = FALSE]
    /\ pc' = [pc EXCEPT ![C] = "c_mv_set"]
    /\ UNCHANGED <<mounted, seqv, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo, seen>>
CMvSet ==
    /\ pc[C] = "c_mv_set"
    /\ mnt' = [mnt EXCEPT ![victim].parent = ctgt.mnt, ![victim].mp = ctgt.d]
    /\ pc' = [pc EXCEPT ![C] = "c_mv_hash"]
    /\ UNCHANGED <<mounted, seqv, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo, seen>>
CMvHash ==
    /\ pc[C] = "c_mv_hash"
    /\ mnt' = [mnt EXCEPT ![victim].hashed = TRUE]
    /\ mounted' = [d \in Dentries |-> mounted[d] /\ ~Unmounted(mnt', d)]
    /\ pc' = [pc EXCEPT ![C] = "c_unlock"]
    /\ UNCHANGED <<seqv, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo, seen>>
CUnlock ==
    /\ pc[C] = "c_unlock"
    /\ seqv' = seqv + 1
    /\ seen' = [w \in Walkers |-> IF Walking(w) THEN seen[w] \cup {Now(w)} ELSE seen[w]]
    /\ pc' = [pc EXCEPT ![C] = IF CHANGE = "umount" THEN "c_gp" ELSE "done"]
    /\ UNCHANGED <<mnt, mounted, rcu, gp, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo>>
\* namespace_unlock(): synchronize_rcu_expedited(), then the puts
CGp ==
    /\ pc[C] = "c_gp"
    /\ IF FIX_RCU_FREE THEN gp' = [on |-> TRUE, wait |-> Readers] ELSE UNCHANGED gp
    /\ pc' = [pc EXCEPT ![C] = "c_put"]
    /\ UNCHANGED <<mnt, mounted, seqv, rcu, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, todo, seen>>
CPut ==
    /\ pc[C] = "c_put" /\ gp.wait = {}
    /\ gp' = [on |-> FALSE, wait |-> {}]
    /\ mnt' = [y \in MntIds |-> IF y \in todo
                                    THEN [mnt[y] EXCEPT !.count = @ - 1, !.alive = (mnt[y].count > 1),
                                                        !.freed = (mnt[y].count = 1)]
                                    ELSE mnt[y]]
    /\ todo' = {}
    /\ pc' = [pc EXCEPT ![C] = "done"]
    /\ UNCHANGED <<mounted, seqv, rcu, mode, path, nxt, ip, mseq, restarts, res, held, tgt, ctgt, victim, budget, hist, rok, seen>>
Changer == CPick \/ CLock \/ CUnhash \/ CMvUnhash \/ CMvSet \/ CMvHash \/ CUnlock \/ CGp \/ CPut

(* ---- the specification -------------------------------------------------- *)

Settled == \A t \in Tasks : pc[t] = "done"
Next ==
    \/ \E w \in Walkers : (mode[w] = "rcu" /\ RcuWalk(w)) \/ (mode[w] = "ref" /\ RComp(w))
    \/ Mounter \/ Changer
    \/ (Settled /\ UNCHANGED vars)
Spec == Init /\ [][Next]_vars

(* ---- what is checked ------------------------------------------------------ *)

Touch(w) == IF pc[w] = "done" THEN res[w].mnt ELSE path[w].mnt
\* W1: no walker's current or final mount is freed
NoUAF == \A w \in Walkers : Touch(w) # NoMnt => ~mnt[Touch(w)].freed

\* W4: a walk that completed in RCU mode saw no mount change, so its result
\* was the sequential walk over the tree at that moment; the -ENOENT of a
\* negative dentry, which is returned without a recheck, must be that too
RcuResultOK == \A w \in Walkers : rok[w]

\* W5: a scoped walk never escapes its root
ScopedOK == \A w \in Walkers : (WScoped[w] /\ pc[w] = "done" /\ res[w].err = "")
                               => Under([mnt |-> res[w].mnt, d |-> res[w].d], WRoot[w])
\* ... nor is it ever outside the root while walking
ScopedPathOK == \A w \in Walkers : WScoped[w] => Under(path[w], WRoot[w])

\* W7: bounded restarts
Bounded == \A w \in Walkers : restarts[w] <= MaxRestarts

\* the ledger: the namespace's reference plus the REF walkers' ones
Ledger == \A x \in MntIds : mnt[x].alive =>
            mnt[x].count = (IF mnt[x].ns \/ x \in todo THEN 1 ELSE 0) + Cardinality({w \in Walkers : held[w] = x})

NoMiss == ~hist.miss
NoEscape == ~hist.esc
NoClimb == ~hist.climb

=============================================================================
