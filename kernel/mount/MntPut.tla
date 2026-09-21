------------------------------ MODULE MntPut ------------------------------
(***************************************************************************)
(* The reference count of one mount under concurrent lockless use:         *)
(* __legitimize_mnt() against do_umount() and against the final mntput().  *)
(*                                                                         *)
(* One mount M, mounted in a namespace.  Tasks:                            *)
(*   U        the umounter: do_umount() (sync, or MNT_DETACH when LAZY),   *)
(*            namespace_unlock() with its grace period and the namespace's *)
(*            mntput(), then the path_put() of its own reference           *)
(*   Walkers  RCU path walkers: read_seqbegin(mount_lock), __lookup_mnt(), *)
(*            __legitimize_mnt(), use the mount, mntput()                  *)
(*   Holders  tasks that hold a reference from the start (an open file):   *)
(*            mntget()/mntput() pairs, migration between CPUs, the final   *)
(*            mntput()                                                     *)
(*                                                                         *)
(* Memory model (TSO): every store goes into the storing CPU's FIFO store  *)
(* buffer and becomes visible to the other CPUs when it is flushed; the    *)
(* storing CPU reads its own buffered stores (forwarding).  smp_mb() and   *)
(* the atomic RMW inside spin_lock() wait until the buffer is empty.  The  *)
(* spinlock release is a plain store, so a later lock taker sees every     *)
(* store of the previous holder.  Migration and the RCU grace period       *)
(* guarantee (a reader's stores are visible to the updater after the       *)
(* grace period) flush the buffer.  mnt_count is one counter per CPU,      *)
(* summed CPU by CPU by mnt_get_count() (9ea0a46ca2c3).                    *)
(*                                                                         *)
(* Constants switch the pieces of the protocol off one by one: the three   *)
(* smp_mb() (__legitimize_mnt(), mntput_no_expire_slowpath(), do_umount()  *)
(* -- 65781e19dcfc), the synchronize_rcu_expedited() before the puts in    *)
(* namespace_unlock() and the rcu_read_lock() around the mnt_ns fast path  *)
(* (9ea0a46ca2c3), the MNT_SYNC_UMOUNT and MNT_DOOMED tests under          *)
(* mount_lock in __legitimize_mnt() (48a066e72d97, 119e1ef80ecf,           *)
(* 250cf3693060).                                                          *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
    TaskList,       \* the tasks, as a sequence: the umounter "U" first
    Walkers,        \* the walker tasks
    Holders,        \* the holder tasks
    NCPU,           \* CPUs 1..NCPU; mnt_get_count() reads them in order
    GetBudget,      \* mntget()/mntput() pairs a holder may do
    MIGRATE,        \* holders may migrate between CPUs
    MigBudget,      \* how often a holder may migrate
    LAZY,           \* umount2(MNT_DETACH) instead of a synchronous umount
    FIX_MB_LEGIT,   \* smp_mb() in __legitimize_mnt()
    FIX_MB_UMOUNT,  \* smp_mb() in do_umount() before the refcount checks
    FIX_MB_PUT,     \* smp_mb() in mntput_no_expire_slowpath()
    FIX_RCU_DELAY,  \* synchronize_rcu_expedited() in namespace_unlock()
    FIX_PUT_RCU,    \* rcu_read_lock() around the mnt_ns test in mntput_no_expire()
    FIX_SYNC_FLAG,  \* __legitimize_mnt() fails on MNT_SYNC_UMOUNT
    FIX_DOOMED_FLAG \* __legitimize_mnt() fails on MNT_DOOMED

U == "U"
Tasks == {TaskList[i] : i \in 1..Len(TaskList)}
NoTask == "none"
CPUs == 1..NCPU
ASSUME U \in Tasks /\ Walkers \subseteq Tasks /\ Holders \subseteq Tasks
       /\ U \notin Walkers /\ U \notin Holders /\ Walkers \cap Holders = {}

VARIABLES
    seqv,     \* mount_lock's seqcount as the other CPUs see it
    cntv,     \* [CPUs -> Int]: mnt_pcp->mnt_count as the other CPUs see it
    lockv,    \* mount_lock's spinlock as the other CPUs see it: holder or NoTask
    m,        \* the mount: hashed, ns (mnt_ns != NULL), umount, sync, doomed, freed
    buf,      \* [Tasks -> Seq(store)]: the store buffer of the task's CPU
    cpu,      \* [Tasks -> CPUs]
    rcu,      \* [Tasks -> BOOLEAN]: inside rcu_read_lock()
    gp,       \* synchronize_rcu_expedited(): [on, wait] -- the readers it waits for
    gpfree,   \* call_rcu(delayed_free_vfsmnt): the same
    pc,       \* [Tasks -> label]
    ret,      \* [Tasks -> label]: where mntput() returns to
    sq,       \* [Tasks -> Nat]: a walker's read_seqbegin() sample
    acc,      \* [Tasks -> Int]: mnt_get_count()'s running sum
    ci,       \* [Tasks -> Nat]: mnt_get_count()'s next CPU
    refs,     \* [Tasks -> Nat]: references the task holds (the ledger)
    nsref,    \* the namespace's reference has not been dropped yet
    nsput,    \* U is dropping the namespace's reference
    gets,     \* [Tasks -> Nat]: mntget() calls a holder has made
    migs,     \* [Tasks -> Nat]: migrations a holder has made
    cleaner,  \* the task that ran cleanup_mnt()
    uresult   \* "", "ok" or "busy"

vars == <<seqv, cntv, lockv, m, buf, cpu, rcu, gp, gpfree, pc, ret, sq, acc, ci,
          refs, nsref, nsput, gets, migs, cleaner, uresult>>

(* ---- the store buffers ------------------------------------------------- *)

\* a store: seq := v, cnt[c] += d, hashed := v, ns := v, lock := v
StSeq(v)    == [f |-> "seq", v |-> v]
StCnt(c, d) == [f |-> "cnt", c |-> c, d |-> d]
StHash(v)   == [f |-> "hashed", v |-> v]
StNs(v)     == [f |-> "ns", v |-> v]
StLock(v)   == [f |-> "lock", v |-> v]

\* the visible state as a record, so that stores can be applied in order
Vis == [seqv |-> seqv, cntv |-> cntv, lockv |-> lockv, m |-> m]
Apply(s, e) ==
    CASE e.f = "seq"    -> [s EXCEPT !.seqv = e.v]
      [] e.f = "cnt"    -> [s EXCEPT !.cntv[e.c] = @ + e.d]
      [] e.f = "hashed" -> [s EXCEPT !.m.hashed = e.v]
      [] e.f = "ns"     -> [s EXCEPT !.m.ns = e.v]
      [] e.f = "lock"   -> [s EXCEPT !.lockv = e.v]
RECURSIVE ApplyAll(_, _)
ApplyAll(s, es) == IF es = <<>> THEN s ELSE ApplyAll(Apply(s, Head(es)), Tail(es))

RECURSIVE SumD(_)
SumD(s) == IF s = <<>> THEN 0 ELSE Head(s) + SumD(Tail(s))
\* the task's own buffered increments of one counter (store forwarding)
Buffered(t, c) == SumD([i \in 1..Len(buf[t]) |->
                        IF buf[t][i].f = "cnt" /\ buf[t][i].c = c THEN buf[t][i].d ELSE 0])
\* what a load of cnt[c] by t returns
SeenCnt(t, c) == cntv[c] + Buffered(t, c)
\* the count as it will be once every buffer has drained
Total == SumD([c \in 1..NCPU |-> cntv[c]])
         + SumD([i \in 1..Len(TaskList) |->
                 SumD([c \in 1..NCPU |-> Buffered(TaskList[i], c)])])

Push(t, e) == buf' = [buf EXCEPT ![t] = Append(@, e)]
Empty(t) == buf[t] = <<>>

\* everything t has stored becomes visible: after a full barrier, an
\* atomic RMW, a migration, or the end of a grace period that waited for t
Drained(t, extra) ==
    LET r == ApplyAll(Vis, buf[t] \o extra)
    IN /\ seqv' = r.seqv /\ cntv' = r.cntv /\ lockv' = r.lockv /\ m' = r.m
       /\ buf' = [buf EXCEPT ![t] = <<>>]
Unchanged_vis == UNCHANGED <<seqv, cntv, lockv, m>>

\* a grace period is a full memory barrier on every CPU: everything any
\* task has stored before it starts is visible when it ends
RECURSIVE ApplyTasks(_, _)
ApplyTasks(s, i) == IF i > Len(TaskList) THEN s ELSE ApplyTasks(ApplyAll(s, buf[TaskList[i]]), i + 1)
DrainedAll ==
    LET r == ApplyTasks(Vis, 1)
    IN /\ seqv' = r.seqv /\ cntv' = r.cntv /\ lockv' = r.lockv /\ m' = r.m
       /\ buf' = [t \in Tasks |-> <<>>]

(* ---- RCU --------------------------------------------------------------- *)

\* rcu_read_unlock(): the grace periods waiting for t stop waiting; the
\* RCU guarantee makes t's stores visible to whoever waited
RcuOut(t) ==
    /\ rcu' = [rcu EXCEPT ![t] = FALSE]
    /\ gp' = [gp EXCEPT !.wait = @ \ {t}]
    /\ gpfree' = [gpfree EXCEPT !.wait = @ \ {t}]
Waited(t) == t \in gp.wait \/ t \in gpfree.wait
Readers == {t \in Tasks : rcu[t]}

(* ---- mount_lock -------------------------------------------------------- *)

\* lock_mount_hash() = write_seqlock(): the atomic RMW of spin_lock()
\* drains the buffer; the seqcount increment is a plain store
Lock(t) ==
    /\ lockv = NoTask /\ Empty(t)
    /\ lockv' = t
    /\ Push(t, StSeq(seqv + 1))
    /\ UNCHANGED <<seqv, cntv, m>>
\* the seqcount as t sees it: its own increment may still sit in its buffer
SeenSeq(t) == LET ss == SelectSeq(buf[t], LAMBDA e : e.f = "seq")
              IN IF ss = <<>> THEN seqv ELSE ss[Len(ss)].v
\* unlock_mount_hash() = write_sequnlock(): two plain stores
UnlockStores(t) == <<StSeq(SeenSeq(t) + 1), StLock(NoTask)>>

(* ---- the labels -------------------------------------------------------- *)

\* the labels at which a task reads or writes the mount (__lookup_mnt() only
\* walks the hash, which the mount left before it could be freed)
Touching == {"w_l1", "w_l2", "w_mb", "w_l4", "w_lock", "w_flags", "w_use",
             "p_enter", "p_fast", "p_lock", "p_mb", "p_dec", "p_sum", "p_check", "p_cleanup",
             "u_lock", "u_mb", "u_sum", "u_busy", "u_tree", "u_unlock", "u_nsput"}
Done == {"done", "lost", "w_none"}

(* ---- init -------------------------------------------------------------- *)

Init ==
    /\ seqv = 0
    \* the namespace's and U's references on CPU 1, the holders' on CPU 2
    /\ cntv = [c \in CPUs |-> IF c = 1 THEN 2 ELSE IF c = 2 THEN Cardinality(Holders) ELSE 0]
    /\ lockv = NoTask
    /\ m = [hashed |-> TRUE, ns |-> TRUE, umount |-> FALSE, sync |-> FALSE,
            doomed |-> FALSE, freed |-> FALSE]
    /\ buf = [t \in Tasks |-> <<>>]
    /\ cpu = [t \in Tasks |-> IF t \in Holders THEN 2 ELSE 1]
    /\ rcu = [t \in Tasks |-> FALSE]
    /\ gp = [on |-> FALSE, wait |-> {}]
    /\ gpfree = [on |-> FALSE, wait |-> {}]
    /\ pc = [t \in Tasks |-> IF t = U THEN "u_lock" ELSE IF t \in Walkers THEN "w_start" ELSE "h_idle"]
    /\ ret = [t \in Tasks |-> "done"]
    /\ sq = [t \in Tasks |-> 0]
    /\ acc = [t \in Tasks |-> 0]
    /\ ci = [t \in Tasks |-> 1]
    /\ refs = [t \in Tasks |-> IF t = U \/ t \in Holders THEN 1 ELSE 0]
    /\ nsref = TRUE
    /\ nsput = FALSE
    /\ gets = [t \in Tasks |-> 0]
    /\ migs = [t \in Tasks |-> 0]
    /\ cleaner = NoTask
    /\ uresult = ""

(* ---- the memory system ------------------------------------------------- *)

\* one store leaves a buffer
Flush(t) ==
    /\ ~Empty(t)
    /\ LET r == Apply(Vis, Head(buf[t]))
       IN seqv' = r.seqv /\ cntv' = r.cntv /\ lockv' = r.lockv /\ m' = r.m
    /\ buf' = [buf EXCEPT ![t] = Tail(@)]
    /\ UNCHANGED <<cpu, rcu, gp, gpfree, pc, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* delayed_free_vfsmnt(): the RCU callback runs after its grace period
RcuFree ==
    /\ gpfree.on /\ gpfree.wait = {}
    /\ gpfree' = [on |-> FALSE, wait |-> {}]
    /\ m' = [m EXCEPT !.freed = TRUE]
    /\ UNCHANGED <<seqv, cntv, lockv, buf, cpu, rcu, gp, pc, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

(* ---- mntput() ---------------------------------------------------------- *)
(* entered at "p_enter" with ret[t] set; the ledger entry it drops is the   *)
(* namespace's when nsput, else one of t's own                             *)

DropRef(t) ==
    IF t = U /\ nsput THEN nsref' = FALSE /\ UNCHANGED refs
    ELSE refs' = [refs EXCEPT ![t] = @ - 1] /\ UNCHANGED nsref

\* mntput_no_expire(): rcu_read_lock(), READ_ONCE(mnt->mnt_ns)
PutEnter(t) ==
    /\ pc[t] = "p_enter"
    /\ rcu' = [rcu EXCEPT ![t] = FIX_PUT_RCU]
    /\ pc' = [pc EXCEPT ![t] = IF m.ns THEN "p_fast" ELSE "p_lock"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, gp, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* the fast path: mnt_add_count(mnt, -1) with nothing held but RCU
PutFast(t) ==
    /\ pc[t] = "p_fast"
    /\ IF Waited(t) THEN Drained(t, <<StCnt(cpu[t], -1)>>)
       ELSE Push(t, StCnt(cpu[t], -1)) /\ Unchanged_vis
    /\ DropRef(t)
    /\ RcuOut(t)
    /\ pc' = [pc EXCEPT ![t] = ret[t]]
    /\ UNCHANGED <<cpu, ret, sq, acc, ci, nsput, gets, migs, cleaner, uresult>>

\* mntput_no_expire_slowpath(): lock_mount_hash()
PutLock(t) ==
    /\ pc[t] = "p_lock"
    /\ Lock(t)
    /\ pc' = [pc EXCEPT ![t] = "p_mb"]
    /\ UNCHANGED <<cpu, rcu, gp, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* smp_mb(): "if __legitimize_mnt() has not seen us grab mount_lock, we'll
\* see their refcount increment here"
PutMb(t) ==
    /\ pc[t] = "p_mb"
    /\ FIX_MB_PUT => Empty(t)
    /\ pc' = [pc EXCEPT ![t] = "p_dec"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gp, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* mnt_add_count(mnt, -1), then mnt_get_count() starts
PutDec(t) ==
    /\ pc[t] = "p_dec"
    /\ Push(t, StCnt(cpu[t], -1))
    /\ DropRef(t)
    /\ acc' = [acc EXCEPT ![t] = 0]
    /\ ci' = [ci EXCEPT ![t] = 1]
    /\ pc' = [pc EXCEPT ![t] = "p_sum"]
    /\ Unchanged_vis
    /\ UNCHANGED <<cpu, rcu, gp, gpfree, ret, sq, nsput, gets, migs, cleaner, uresult>>

\* mnt_get_count(): one CPU per step
SumStep(t, next) ==
    /\ IF ci[t] <= NCPU
       THEN /\ acc' = [acc EXCEPT ![t] = @ + SeenCnt(t, ci[t])]
            /\ ci' = [ci EXCEPT ![t] = @ + 1]
            /\ UNCHANGED pc
       ELSE /\ pc' = [pc EXCEPT ![t] = next]
            /\ UNCHANGED <<acc, ci>>
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gp, gpfree, ret, sq, refs, nsref, nsput, gets, migs, cleaner, uresult>>

PutSum(t) == pc[t] = "p_sum" /\ SumStep(t, "p_check")

\* count != 0: not the last reference; MNT_DOOMED already: somebody else's
\* job; else MNT_DOOMED, unlock, and cleanup_mnt() from task work
PutCheck(t) ==
    /\ pc[t] = "p_check"
    /\ IF acc[t] # 0 \/ m.doomed
       THEN /\ Drained(t, UnlockStores(t))
            /\ pc' = [pc EXCEPT ![t] = ret[t]]
       ELSE LET r == ApplyAll(Vis, buf[t] \o UnlockStores(t))
            IN /\ seqv' = r.seqv /\ cntv' = r.cntv /\ lockv' = r.lockv
               /\ m' = [r.m EXCEPT !.doomed = TRUE]
               /\ buf' = [buf EXCEPT ![t] = <<>>]
               /\ pc' = [pc EXCEPT ![t] = "p_cleanup"]
    /\ RcuOut(t)
    /\ UNCHANGED <<cpu, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* cleanup_mnt(): call_rcu(&mnt->mnt_rcu, delayed_free_vfsmnt)
PutCleanup(t) ==
    /\ pc[t] = "p_cleanup"
    /\ gpfree' = [on |-> TRUE, wait |-> Readers]
    /\ cleaner' = t
    /\ pc' = [pc EXCEPT ![t] = ret[t]]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gp, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, uresult>>

Put(t) == PutEnter(t) \/ PutFast(t) \/ PutLock(t) \/ PutMb(t) \/ PutDec(t)
          \/ PutSum(t) \/ PutCheck(t) \/ PutCleanup(t)

(* ---- the walker: __follow_mount_rcu() + __legitimize_mnt() ------------- *)

\* path_init(): rcu_read_lock(), nd->m_seq = read_seqbegin(&mount_lock)
\* (read_seqbegin() spins while the count is odd)
WStart(t) ==
    /\ pc[t] = "w_start"
    /\ seqv % 2 = 0
    /\ rcu' = [rcu EXCEPT ![t] = TRUE]
    /\ sq' = [sq EXCEPT ![t] = seqv]
    /\ pc' = [pc EXCEPT ![t] = "w_lookup"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, gp, gpfree, ret, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* the walker reaches the mount by __lookup_mnt() (the hash is read
\* locklessly) or as the fs->pwd of a task sharing its fs_struct, read under
\* fs->seq with no reference of its own; that task may chdir() away and
\* drop the reference at any time (its chdir() is HPut)
ViaPwd == \E h \in Holders : refs[h] > 0 /\ pc[h] = "h_idle"
WLookup(t) ==
    /\ pc[t] = "w_lookup"
    /\ IF m.hashed \/ ViaPwd
       THEN pc' = [pc EXCEPT ![t] = "w_l1"] /\ UNCHANGED <<rcu, gp, gpfree>>
       ELSE pc' = [pc EXCEPT ![t] = "w_none"] /\ RcuOut(t)
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* __legitimize_mnt(): if (read_seqretry(&mount_lock, seq)) return 1
WL1(t) ==
    /\ pc[t] = "w_l1"
    /\ IF seqv # sq[t]
       THEN pc' = [pc EXCEPT ![t] = "lost"] /\ RcuOut(t)
       ELSE pc' = [pc EXCEPT ![t] = "w_l2"] /\ UNCHANGED <<rcu, gp, gpfree>>
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* mnt_add_count(mnt, 1)
WL2(t) ==
    /\ pc[t] = "w_l2"
    /\ Push(t, StCnt(cpu[t], 1))
    /\ refs' = [refs EXCEPT ![t] = @ + 1]
    /\ pc' = [pc EXCEPT ![t] = "w_mb"]
    /\ Unchanged_vis
    /\ UNCHANGED <<cpu, rcu, gp, gpfree, ret, sq, acc, ci, nsref, nsput, gets, migs, cleaner, uresult>>

\* smp_mb(); // see mntput_no_expire() and do_umount()
WMb(t) ==
    /\ pc[t] = "w_mb"
    /\ FIX_MB_LEGIT => Empty(t)
    /\ pc' = [pc EXCEPT ![t] = "w_l4"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gp, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* if (likely(!read_seqretry(&mount_lock, seq))) return 0
WL4(t) ==
    /\ pc[t] = "w_l4"
    /\ pc' = [pc EXCEPT ![t] = IF seqv = sq[t] THEN "w_use" ELSE "w_lock"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gp, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* lock_mount_hash()
WLock(t) ==
    /\ pc[t] = "w_lock"
    /\ Lock(t)
    /\ pc' = [pc EXCEPT ![t] = "w_flags"]
    /\ UNCHANGED <<cpu, rcu, gp, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* MNT_SYNC_UMOUNT | MNT_DOOMED: drop the count under the lock, return 1;
\* else unlock and return -1: the caller will mntput()
WFlags(t) ==
    /\ pc[t] = "w_flags"
    /\ IF (FIX_SYNC_FLAG /\ m.sync) \/ (FIX_DOOMED_FLAG /\ m.doomed)
       THEN /\ Drained(t, <<StCnt(cpu[t], -1)>> \o UnlockStores(t))
            /\ refs' = [refs EXCEPT ![t] = @ - 1]
            /\ pc' = [pc EXCEPT ![t] = "lost"]
            /\ UNCHANGED ret
       ELSE /\ Drained(t, UnlockStores(t))
            /\ ret' = [ret EXCEPT ![t] = "lost"]
            /\ pc' = [pc EXCEPT ![t] = "p_enter"]
            /\ UNCHANGED refs
    /\ RcuOut(t)
    /\ UNCHANGED <<cpu, sq, acc, ci, nsref, nsput, gets, migs, cleaner, uresult>>

\* legitimized: leave RCU, use the mount, then mntput()
WUse(t) ==
    /\ pc[t] = "w_use"
    /\ RcuOut(t)
    /\ ret' = [ret EXCEPT ![t] = "done"]
    /\ pc' = [pc EXCEPT ![t] = "p_enter"]
    /\ IF Waited(t) THEN Drained(t, <<>>) ELSE Unchanged_vis /\ UNCHANGED buf
    /\ UNCHANGED <<cpu, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

Walk(t) == WStart(t) \/ WLookup(t) \/ WL1(t) \/ WL2(t) \/ WMb(t) \/ WL4(t)
           \/ WLock(t) \/ WFlags(t) \/ WUse(t)

(* ---- the holder: mntget(), migration, mntput() ------------------------- *)

\* path_get() on a path the task holds: mnt_add_count(mnt, 1) with nothing
\* held but that reference
HGet(t) ==
    /\ pc[t] = "h_idle" /\ refs[t] > 0 /\ gets[t] < GetBudget
    /\ Push(t, StCnt(cpu[t], 1))
    /\ refs' = [refs EXCEPT ![t] = @ + 1]
    /\ gets' = [gets EXCEPT ![t] = @ + 1]
    /\ Unchanged_vis
    /\ UNCHANGED <<cpu, rcu, gp, gpfree, pc, ret, sq, acc, ci, nsref, nsput, migs, cleaner, uresult>>

\* the scheduler moves the task: its stores are visible before it runs again
HMigrate(t) ==
    /\ MIGRATE /\ pc[t] = "h_idle" /\ migs[t] < MigBudget
    /\ \E c \in CPUs \ {cpu[t]} : cpu' = [cpu EXCEPT ![t] = c]
    /\ migs' = [migs EXCEPT ![t] = @ + 1]
    /\ Drained(t, <<>>)
    /\ UNCHANGED <<rcu, gp, gpfree, pc, ret, sq, acc, ci, refs, nsref, nsput, gets, cleaner, uresult>>

HPut(t) ==
    /\ pc[t] = "h_idle" /\ refs[t] > 0
    /\ ret' = [ret EXCEPT ![t] = "h_idle"]
    /\ pc' = [pc EXCEPT ![t] = "p_enter"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gp, gpfree, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

HDone(t) ==
    /\ pc[t] = "h_idle" /\ refs[t] = 0
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gp, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

Hold(t) == HGet(t) \/ HMigrate(t) \/ HPut(t) \/ HDone(t)

(* ---- the umounter: do_umount(), namespace_unlock(), path_put() --------- *)

\* namespace_lock(); lock_mount_hash()
ULock ==
    /\ pc[U] = "u_lock"
    /\ Lock(U)
    /\ pc' = [pc EXCEPT ![U] = IF LAZY THEN "u_tree" ELSE "u_mb"]
    /\ UNCHANGED <<cpu, rcu, gp, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* smp_mb(); // paired with __legitimize_mnt()
UMb ==
    /\ pc[U] = "u_mb"
    /\ FIX_MB_UMOUNT => Empty(U)
    /\ acc' = [acc EXCEPT ![U] = 0]
    /\ ci' = [ci EXCEPT ![U] = 1]
    /\ pc' = [pc EXCEPT ![U] = "u_sum"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gp, gpfree, ret, sq, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* propagate_mount_busy(mnt, 2): mnt_get_count(mnt) > 2 is busy
USum == pc[U] = "u_sum" /\ SumStep(U, "u_busy")

UBusy ==
    /\ pc[U] = "u_busy"
    /\ IF acc[U] > 2
       THEN /\ Drained(U, UnlockStores(U))
            /\ uresult' = "busy"
            /\ ret' = [ret EXCEPT ![U] = "done"]
            /\ pc' = [pc EXCEPT ![U] = "p_enter"]
       ELSE /\ Unchanged_vis /\ UNCHANGED buf
            /\ pc' = [pc EXCEPT ![U] = "u_tree"]
            /\ UNCHANGED <<uresult, ret>>
    /\ UNCHANGED <<cpu, rcu, gp, gpfree, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner>>

\* umount_tree(): MNT_UMOUNT, unhash, WRITE_ONCE(mnt_ns, NULL),
\* MNT_SYNC_UMOUNT for a synchronous umount, the mount goes on `unmounted`
UTree ==
    /\ pc[U] = "u_tree"
    /\ m' = [m EXCEPT !.umount = TRUE, !.sync = ~LAZY]
    /\ buf' = [buf EXCEPT ![U] = @ \o <<StHash(FALSE), StNs(FALSE)>>]
    /\ uresult' = "ok"
    /\ pc' = [pc EXCEPT ![U] = "u_unlock"]
    /\ UNCHANGED <<seqv, cntv, lockv, cpu, rcu, gp, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner>>

\* unlock_mount_hash()
UUnlock ==
    /\ pc[U] = "u_unlock"
    /\ Drained(U, UnlockStores(U))
    /\ pc' = [pc EXCEPT ![U] = "u_nsunlock"]
    /\ UNCHANGED <<cpu, rcu, gp, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* namespace_unlock(): up_write() then synchronize_rcu_expedited() -- both
\* full barriers -- before the mntput() of the unmounted mount
UNsUnlock ==
    /\ pc[U] = "u_nsunlock"
    /\ Empty(U)
    /\ IF FIX_RCU_DELAY
       THEN /\ gp' = [on |-> TRUE, wait |-> Readers] /\ pc' = [pc EXCEPT ![U] = "u_gpwait"]
            /\ DrainedAll
       ELSE /\ UNCHANGED gp /\ pc' = [pc EXCEPT ![U] = "u_nsput"]
            /\ Unchanged_vis /\ UNCHANGED buf
    /\ UNCHANGED <<cpu, rcu, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

UGpWait ==
    /\ pc[U] = "u_gpwait"
    /\ gp.wait = {}
    /\ gp' = [on |-> FALSE, wait |-> {}]
    /\ pc' = [pc EXCEPT ![U] = "u_nsput"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gpfree, ret, sq, acc, ci, refs, nsref, nsput, gets, migs, cleaner, uresult>>

\* the namespace's reference: mntput(&m->mnt) for every mount on `unmounted`
UNsPut ==
    /\ pc[U] = "u_nsput"
    /\ nsput' = TRUE
    /\ ret' = [ret EXCEPT ![U] = "u_ret"]
    /\ pc' = [pc EXCEPT ![U] = "p_enter"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gp, gpfree, sq, acc, ci, refs, nsref, gets, migs, cleaner, uresult>>

\* do_umount() returned: path_umount() drops the caller's own reference
URet ==
    /\ pc[U] = "u_ret"
    /\ nsput' = FALSE
    /\ ret' = [ret EXCEPT ![U] = "done"]
    /\ pc' = [pc EXCEPT ![U] = "p_enter"]
    /\ Unchanged_vis
    /\ UNCHANGED <<buf, cpu, rcu, gp, gpfree, sq, acc, ci, refs, nsref, gets, migs, cleaner, uresult>>

Umount == ULock \/ UMb \/ USum \/ UBusy \/ UTree \/ UUnlock \/ UNsUnlock \/ UGpWait \/ UNsPut \/ URet

(* ---- the specification ------------------------------------------------- *)

TaskStep(t) ==
    \/ Put(t)
    \/ (t \in Walkers /\ Walk(t))
    \/ (t \in Holders /\ Hold(t))
    \/ (t = U /\ Umount)

Next ==
    \/ \E t \in Tasks : TaskStep(t) \/ Flush(t)
    \/ RcuFree

Spec == Init /\ [][Next]_vars
        /\ \A t \in Tasks : WF_vars(TaskStep(t)) /\ WF_vars(Flush(t))
        /\ WF_vars(RcuFree)

(* ---- what is checked --------------------------------------------------- *)

IsStore(e) == \/ (e.f = "seq" /\ e.v \in Nat)
              \/ (e.f = "cnt" /\ e.c \in CPUs /\ e.d \in {-1, 1})
              \/ (e.f \in {"hashed", "ns"} /\ e.v \in BOOLEAN)
              \/ (e.f = "lock" /\ e.v = NoTask)
Labels == Touching \cup Done \cup {"w_start", "w_lookup", "h_idle", "u_nsunlock", "u_gpwait", "u_ret"}
TypeOK ==
    /\ seqv \in Nat /\ cntv \in [CPUs -> Int] /\ lockv \in Tasks \cup {NoTask}
    /\ m \in [hashed: BOOLEAN, ns: BOOLEAN, umount: BOOLEAN, sync: BOOLEAN, doomed: BOOLEAN, freed: BOOLEAN]
    /\ \A t \in Tasks : \A i \in 1..Len(buf[t]) : IsStore(buf[t][i])
    /\ cpu \in [Tasks -> CPUs] /\ rcu \in [Tasks -> BOOLEAN]
    /\ pc \in [Tasks -> Labels] /\ ret \in [Tasks -> Labels]
    /\ refs \in [Tasks -> Nat] /\ nsref \in BOOLEAN /\ uresult \in {"", "ok", "busy"}

\* a walker's count between mnt_add_count() and the decision is transient,
\* and so is the one it drops itself after __legitimize_mnt() returned -1
Transient(t) == t \in Walkers /\ (pc[t] \in {"w_mb", "w_l4", "w_lock", "w_flags"} \/ ret[t] = "lost")
RealRefs == SumD([i \in 1..Len(TaskList) |->
                  IF Transient(TaskList[i]) THEN 0 ELSE refs[TaskList[i]]])

\* the ledger: the counters add up to the references
Ledger == Total = (IF nsref THEN 1 ELSE 0) + SumD([i \in 1..Len(TaskList) |-> refs[TaskList[i]]])

\* W1: nobody touches a freed mount
NoUAF == m.freed => \A t \in Tasks : pc[t] \notin Touching

\* W2: MNT_DOOMED means the last reference is gone; the summed count is
\* never negative (the WARN_ON in mntput_no_expire_slowpath())
DoomedIsLast == m.doomed => ~nsref /\ RealRefs = 0
NoNegative == \A t \in Tasks : pc[t] = "p_check" => acc[t] >= 0

\* W3: a synchronous umount that succeeded left no reference behind but the
\* namespace's and the caller's, and the caller's own mntput() is the last
\* one -- the filesystem is shut down before umount(2) returns
SyncClean == (uresult = "ok" /\ ~LAZY) =>
                 /\ \A t \in Tasks \ {U} : ~Transient(t) => refs[t] = 0
                 /\ cleaner # NoTask => cleaner = U

\* W7: the mount is freed unless the umount was refused
Freed == <>(m.freed \/ uresult = "busy")
AllDone == <>(\A t \in Tasks : pc[t] \in Done)

=============================================================================
