---------------------------- MODULE Coredump ----------------------------
(***************************************************************************)
(* One thread group under the coredump rendezvous, the signal code around  *)
(* it and the code that creates and tears down threads while it runs.      *)
(*                                                                         *)
(* Tree: work.coredump.close_files.fixes at 938c2dd45269 on top of         *)
(* c7b1fa3db4a1 (vfs-7.4.coredump).  Every FIX_* constant switches one     *)
(* patch of "coredump & signals: an impossible affair" on or off, so TLC   *)
(* reproduces the bug that patch fixes when its constant is FALSE and       *)
(* proves the property when it is TRUE.                                    *)
(*                                                                         *)
(*   FIX_RCU_RELEASE          coredump: hold RCU while releasing parked    *)
(*                            threads (coredump_finish)                    *)
(*   FIX_SIGPENDING_DUMPCORE  signal: only SIGKILL and the freezers        *)
(*                            interrupt a coredumping task                 *)
(*                            (signal_pending, dump_interrupted)           *)
(*   FIX_RETARGET_GROUP_EXIT  signal: don't retarget shared signals in a   *)
(*                            dying thread group (retarget_shared_pending) *)
(*   FIX_WORKER_NODUMP        signal: fix coredump deadlock with           *)
(*                            PF_USER_WORKER (get_signal)                  *)
(*   FIX_PTRACE_MASK          ptrace: refuse to change the signal mask of  *)
(*                            a user worker (PTRACE_SETSIGMASK)            *)
(*   FIX_EXEC_CANCEL_FIRST    exec: cancel io_uring requests before        *)
(*                            de_thread() (begin_new_exec)                 *)
(*   FIX_GATE_SIGNALED        fork: move the coredump and exec checks into *)
(*                            create_io_thread() (PF_SIGNALED gate)        *)
(*   FIX_GATE_POSTCOREDUMP    fork: don't create io threads once           *)
(*                            PF_POSTCOREDUMP is set                       *)
(*                                                                         *)
(* Modelled code, one action per siglock critical section or per          *)
(* unsynchronised step:                                                    *)
(*   kernel/signal.c   __send_signal_locked/prepare_signal/complete_signal *)
(*                     get_signal, retarget_shared_pending, exit_signals,  *)
(*                     sigprocmask/__set_task_blocked, do_sigtimedwait,    *)
(*                     zap_other_threads, signal_pending, recalc_sigpending*)
(*   fs/coredump.c     vfs_coredump, coredump_wait, zap_threads,           *)
(*                     zap_process, coredump_wait_inactive, dump_emit,     *)
(*                     dump_interrupted, coredump_finish                   *)
(*   kernel/exit.c     do_exit, synchronize_group_exit, coredump_task_exit,*)
(*                     do_group_exit, exit_notify, release_task            *)
(*   kernel/fork.c     copy_process (group join, signal checks, flag       *)
(*                     inheritance), create_io_thread                      *)
(*   fs/exec.c         begin_new_exec, de_thread                           *)
(*   io_uring/io-wq.c  io_wq_worker, io_worker_exit, io_queue_worker_create*)
(*                     create_worker_cb/cont, io_wq_exit_start,            *)
(*                     io_wq_exit_workers, io_should_retry_thread          *)
(*   io_uring/cancel.c io_uring_cancel_generic (exit, exec and SQPOLL)     *)
(*   io_uring/sqpoll.c io_sq_thread (exit path)                            *)
(*   kernel/ptrace.c   PTRACE_SETSIGMASK                                   *)
(*   kernel/freezer.c, kernel/cgroup/freezer.c  freeze wakeups            *)
(*                                                                         *)
(* Abstractions:                                                           *)
(*   - Four signal classes: KILL (SIGKILL), CORE (a coredump signal such   *)
(*     as SIGSEGV), TERM (fatal without a core), USR (a handled signal).   *)
(*     No job control stops, no SIGCONT, no ptrace stops.  The tracer is   *)
(*     reduced to what it can do to a user worker: change its mask and    *)
(*     queue a signal on it.                                               *)
(*   - Every legacy signal queue is a set (legacy_queue() drops dups).     *)
(*   - Memory is sequentially consistent.  The one ordering bug of the     *)
(*     series (io-wq exit bit vs task work) is in IoWqExitBit.tla.         *)
(*   - Freezing is a monotone, group wide event that only matters to the   *)
(*     dumper, so it can only happen while a dump is being written.        *)
(*     Frozen tasks are not stopped in the model.                          *)
(*   - Task work is only create_worker_cb()/create_worker_cont().  It runs *)
(*     at get_signal() entry, in the io_uring cancel loops and in exit.    *)
(*   - task_struct memory is freed by an explicit "grace period" step that *)
(*     cannot run while the dumper holds rcu_read_lock().  Only a thread   *)
(*     the dumper still has to wake is ever freed; nothing else looks.     *)
(*   - The core is Chunks writes.  A write may block (pipe or socket full) *)
(*     and then fails on signal_pending(), as pipe_write() does.           *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS
    Threads,        \* thread ids of the group
    Role,           \* [Threads -> {"user", "sqpoll", "iowq", "slot"}]
    Owner0,         \* [Threads -> Threads \cup {NoThread}]: wq->task of a live io-wq worker
    RingOwners,     \* threads with an io_uring task context and an io-wq
    Leader,         \* the thread group leader
    NoThread,
    Chunks,         \* writes that make a complete core
    BudgetKILL, BudgetCORE, BudgetTERM, BudgetUSR,   \* signals the environment may send
    ExecBudget, TracerBudget, RetryBudget,
    FIX_RCU_RELEASE, FIX_SIGPENDING_DUMPCORE, FIX_RETARGET_GROUP_EXIT,
    FIX_WORKER_NODUMP, FIX_PTRACE_MASK, FIX_EXEC_CANCEL_FIRST,
    FIX_GATE_SIGNALED, FIX_GATE_POSTCOREDUMP

Signals    == {"KILL", "CORE", "TERM", "USR"}
FatalSigs  == {"KILL", "CORE", "TERM"}    \* sig_fatal(): SIG_DFL and the default kills
AllButKill == {"CORE", "TERM", "USR"}     \* siginitsetinv(KILL|STOP) of a user worker
FlagSet    == {"SIGNALED", "POSTCOREDUMP", "DUMPCORE", "EXITING"}
Roles      == {"user", "sqpoll", "iowq", "slot"}

ASSUME Leader \in Threads /\ Role[Leader] = "user"
ASSUME NoThread \notin Threads
ASSUME RingOwners \subseteq Threads
ASSUME Chunks \in Nat /\ Chunks >= 1

VARIABLES
    pc,             \* where each thread is
    flags,          \* PF_ flags that matter here
    pending,        \* per thread private pending set
    shared,         \* signal->shared_pending
    blocked,        \* ->blocked
    realblocked,    \* ->real_blocked while in sigtimedwait()
    sigpending,     \* TIF_SIGPENDING
    notify,         \* TIF_NOTIFY_SIGNAL
    group,          \* signal_struct: SIGNAL_GROUP_EXIT, group_exec_task, notify_count, quick_threads
    core,           \* signal->core_state: threads_remaining and the parked list
    dumper,         \* the thread that ran zap_threads()
    counted,        \* the threads zap_process() counted
    decremented,    \* threads that decremented threads_remaining
    released,       \* core_thread->task was set to NULL by coredump_finish()
    release_list,   \* parked threads coredump_finish() still has to wake
    rcu_reader,     \* coredump_finish() is inside guard(rcu)
    freed,          \* the task_struct is gone
    wqexit,         \* IO_WQ_BIT_EXIT of the owner's io-wq
    twq,            \* worker creation task work queued on the owner, and delayed retries
    owner,          \* wq->task of an io-wq worker
    refput,         \* the worker dropped its wq->worker_refs (io_worker_exit)
    dump,           \* the core: written chunks and the outcome
    freeze,         \* "none", "pm" (PM or cgroup v1) or "cg2" (JOBCTL_TRAP_FREEZE)
    hist,           \* history for the properties
    budget          \* bounds on the environment

vars == <<pc, flags, pending, shared, blocked, realblocked, sigpending, notify,
          group, core, dumper, counted, decremented, released, release_list,
          rcu_reader, freed, wqexit, twq, owner, refput, dump, freeze, hist,
          budget>>

PCs == {"none", "run", "sigwait",
        "dump_wait", "dump_write", "dump_finish", "dump_release",
        "exec_cancel_tw", "exec_wait_workers", "exec_dethread", "exec_wait",
        "exec_post", "exec_late_tw", "exec_late_wait",
        "sq_cancel", "sq_cancel_tw", "sq_wait_workers",
        "wq_exit",
        "exit_sync", "parked", "exit_cancel", "exit_cancel_tw",
        "exit_wait_workers", "exit_signals", "exit_notify", "zombie", "dead"}

DumpStates     == {"dump_wait", "dump_write", "dump_finish", "dump_release"}
ExecWindow     == {"exec_post", "exec_late_tw", "exec_late_wait"}
TaskWorkPoints == {"run", "exit_cancel_tw", "sq_cancel_tw", "exec_cancel_tw",
                   "exec_late_tw"}

(***************************************************************************)
(* Derived predicates                                                      *)
(***************************************************************************)
Live(t)      == pc[t] \notin {"none", "dead"}            \* on signal->thread_head
Alive(t)     == pc[t] \notin {"none", "dead", "zombie"}  \* not past exit_notify()
IsWorker(t)  == Role[t] \in {"sqpoll", "iowq", "slot"}    \* PF_USER_WORKER
IsIoWq(t)    == Role[t] \in {"iowq", "slot"}              \* holds a wq->worker_refs
OthersLive(t) == {u \in Threads : u # t /\ Live(u)}
GroupEmpty(t) == OthersLive(t) = {}

HoldsRef(w)    == IsIoWq(w) /\ pc[w] # "none" /\ ~refput[w]
DumperPc       == IF dumper = NoThread THEN "none" ELSE pc[dumper]
Dumping        == DumperPc \in DumpStates

\* twq[o] holds the creation task work queued on owner o: a worker id for
\* its create_worker_cb(), "cont" for a queued create_worker_cont(), and
\* "retry" for a create_worker_cont() that still sits in delayed work.
\* Each of them holds a wq->worker_refs reference.
Runnable(o) == twq[o] \ {"retry"}
WorkersDone(o) == /\ \A w \in Threads : (IsIoWq(w) /\ owner[w] = o) => ~HoldsRef(w)
                  /\ twq[o] = {}

Freezing == freeze # "none"

\* fatal_signal_pending()
FatalPending(t) == sigpending[t] /\ "KILL" \in pending[t]

\* signal_pending() with the PF_DUMPCORE rule of the series
SignalPending(t) ==
    \/ notify[t]
    \/ /\ sigpending[t]
       /\ \/ ~FIX_SIGPENDING_DUMPCORE
          \/ "DUMPCORE" \notin flags[t]
          \/ "KILL" \in pending[t]
          \/ Freezing

\* dump_interrupted(): fatal signal, freezing(), and with the fix the cgroup v2 trap
DumpInterrupted(t) ==
    \/ FatalPending(t)
    \/ freeze = "pm"
    \/ (FIX_SIGPENDING_DUMPCORE /\ freeze = "cg2")

\* recalc_sigpending(): keeps TIF_SIGPENDING while freezing() or a trap is set
Recalc(pend, sh, bl) == Freezing \/ (pend \ bl) # {} \/ (sh \ bl) # {}

\* prepare_signal(): a dying group takes SIGKILL only, and only while it dumps
Accepts(sig) == group.exit => (core.active /\ sig = "KILL")

\* wants_signal()
Wants(sig, t) == Alive(t) /\ sig \notin blocked[t] /\ "EXITING" \notin flags[t]

\* exit_to_user_mode_loop() runs get_signal() and task work before user
\* code runs again, so a new syscall only starts with nothing pending
InUserMode(t) == pc[t] = "run" /\ ~sigpending[t] /\ ~notify[t]

(***************************************************************************)
(* Frames                                                                  *)
(***************************************************************************)
UnchangedCore == UNCHANGED <<core, dumper, counted, decremented, released,
                             release_list, rcu_reader, dump>>
UnchangedWq   == UNCHANGED <<wqexit, twq, owner, refput>>
UnchangedEnv  == UNCHANGED <<freeze, hist, budget>>
UnchangedMask == UNCHANGED <<blocked, realblocked>>

(***************************************************************************)
(* Signal generation: kill(2), tgkill(2), a fault, a ptrace injection      *)
(***************************************************************************)

\* complete_signal() once a thread t wants the signal.  A fatal signal
\* without a core starts the group exit right away and wakes everybody
\* with SIGKILL.  Anything else wakes t to dequeue it.
CompleteSignal(sig, t, pend) ==
    IF sig \in {"KILL", "TERM"} /\ sig \notin realblocked[t]
    THEN /\ group' = [group EXCEPT !.exit = TRUE]
         /\ pending' = [u \in Threads |->
                          IF Live(u) THEN pend[u] \cup {"KILL"} ELSE pend[u]]
         /\ sigpending' = [u \in Threads |->
                          IF Live(u) THEN TRUE ELSE sigpending[u]]
         /\ hist' = [hist EXCEPT !.kill = @ \/ sig = "KILL"]
    ELSE /\ pending' = pend
         /\ sigpending' = [sigpending EXCEPT ![t] = TRUE]
         /\ UNCHANGED <<group, hist>>

\* kill(pid, sig): __send_signal_locked() on the shared queue
SendGroup(sig) ==
    /\ sig \in Signals
    /\ budget[sig] > 0
    /\ \E t \in Threads : Live(t)
    /\ budget' = [budget EXCEPT ![sig] = @ - 1]
    /\ IF ~Accepts(sig) \/ sig \in shared
       THEN UNCHANGED <<pending, shared, sigpending, group, hist>>
       ELSE /\ shared' = shared \cup {sig}
            /\ IF \E t \in Threads : Wants(sig, t)
               THEN \E t \in Threads : /\ Wants(sig, t)
                                       /\ CompleteSignal(sig, t, pending)
               ELSE UNCHANGED <<pending, sigpending, group, hist>>
    /\ UNCHANGED <<pc, flags, notify, freed, freeze>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq

\* tgkill(tgid, tid, sig), a synchronous fault, or a tracer's injection:
\* __send_signal_locked() on the private queue, PIDTYPE_PID
SendThread(t, sig) ==
    /\ sig \in Signals
    /\ budget[sig] > 0
    /\ Alive(t)
    /\ budget' = [budget EXCEPT ![sig] = @ - 1]
    /\ IF ~Accepts(sig) \/ sig \in pending[t]
       THEN UNCHANGED <<pending, sigpending, group, hist>>
       ELSE LET pend == [pending EXCEPT ![t] = @ \cup {sig}]
            IN IF Wants(sig, t)
               THEN CompleteSignal(sig, t, pend)
               ELSE /\ pending' = pend            \* wants_signal() false: queued, nobody woken
                    /\ UNCHANGED <<sigpending, group, hist>>
    /\ UNCHANGED <<pc, flags, shared, notify, freed, freeze>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq

(***************************************************************************)
(* get_signal() and what a fatal signal leads to                           *)
(***************************************************************************)

\* A user worker returns from get_signal() on a fatal signal and runs its
\* own exit: io_wq_worker() breaks out to io_worker_exit(), io_sq_thread()
\* to io_uring_cancel_generic(true, sqd).
WorkerLeave(t) ==
    pc' = [pc EXCEPT ![t] = IF Role[t] = "sqpoll" THEN "sq_cancel" ELSE "wq_exit"]

\* do_group_exit(): zap_other_threads() unless a group action is under way
DoGroupExit(t, pend, sp) ==
    /\ pc' = [pc EXCEPT ![t] = "exit_sync"]
    /\ IF group.exit \/ group.exec # NoThread
       THEN /\ pending' = pend
            /\ sigpending' = sp
            /\ UNCHANGED group
       ELSE /\ group' = [group EXCEPT !.exit = TRUE]
            /\ pending' = [u \in Threads |->
                             IF u # t /\ Alive(u) THEN pend[u] \cup {"KILL"}
                             ELSE pend[u]]
            /\ sigpending' = [u \in Threads |->
                             IF u # t /\ Alive(u) THEN TRUE ELSE sp[u]]

\* vfs_coredump() -> coredump_wait() -> zap_threads()/zap_process()
VfsCoredump(t, pend, sp) ==
    IF ~group.exit /\ group.exec = NoThread
    THEN LET zapped == {u \in Threads : u # t /\ Live(u)
                                        /\ "POSTCOREDUMP" \notin flags[u]}
             nr == Cardinality(zapped)
         IN /\ group' = [group EXCEPT !.exit = TRUE]
            /\ core' = [active |-> TRUE, remaining |-> nr, tasks |-> {}]
            /\ dumper' = t
            /\ counted' = zapped
            /\ pending' = [u \in Threads |->
                             IF u \in zapped THEN pend[u] \cup {"KILL"} ELSE pend[u]]
            /\ sigpending' = [u \in Threads |->
                             IF u \in zapped THEN TRUE
                             ELSE IF u = t THEN FALSE       \* clear_tsk_thread_flag(TIF_SIGPENDING)
                             ELSE sp[u]]
            /\ flags' = [flags EXCEPT ![t] = @ \cup {"SIGNALED", "DUMPCORE"}]
            /\ pc' = [pc EXCEPT ![t] = IF nr > 0 THEN "dump_wait" ELSE "dump_write"]
            /\ dump' = [written |-> 0, result |-> "none"]
    ELSE \* -EAGAIN: no dump, the thread dies like on any fatal signal
         /\ flags' = [flags EXCEPT ![t] = @ \cup {"SIGNALED"}]
         /\ UNCHANGED <<core, dumper, counted, dump>>
         /\ IF IsWorker(t)
            THEN /\ WorkerLeave(t)
                 /\ pending' = pend
                 /\ sigpending' = sp
                 /\ UNCHANGED group
            ELSE DoGroupExit(t, pend, sp)

\* The "fatal:" label of get_signal()
Fatal(t, sig, pend, sp) ==
    IF IsWorker(t) /\ FIX_WORKER_NODUMP
    THEN \* the PF_USER_WORKER test sits before the coredump block
         /\ flags' = [flags EXCEPT ![t] = @ \cup {"SIGNALED"}]
         /\ WorkerLeave(t)
         /\ pending' = pend
         /\ sigpending' = sp
         /\ UNCHANGED <<group, core, dumper, counted, dump>>
    ELSE IF sig = "CORE"
    THEN VfsCoredump(t, pend, sp)
    ELSE /\ flags' = [flags EXCEPT ![t] = @ \cup {"SIGNALED"}]
         /\ UNCHANGED <<core, dumper, counted, dump>>
         /\ IF IsWorker(t)
            THEN /\ WorkerLeave(t)
                 /\ pending' = pend
                 /\ sigpending' = sp
                 /\ UNCHANGED group
            ELSE DoGroupExit(t, pend, sp)

\* One pass of the get_signal() loop under siglock.  get_signal() starts
\* with clear_notify_signal() and task_work_run(), so the dequeue only
\* happens once HandleNotify() and CreateWorker() have drained both.
GetSignal(t) ==
    /\ pc[t] = "run"
    /\ sigpending[t]
    /\ ~notify[t]
    /\ Runnable(t) = {}
    /\ IF group.exit \/ group.exec # NoThread
       THEN \* "Has this task already been marked for death?"
            LET pend == [pending EXCEPT ![t] = @ \ {"KILL"}]
                sp == [sigpending EXCEPT ![t] = Recalc(pend[t], shared, blocked[t])]
            IN /\ Fatal(t, "KILL", pend, sp)
               /\ UNCHANGED shared
       ELSE LET priv == pending[t] \ blocked[t]
                shd  == shared \ blocked[t]
            IN IF priv # {}
               THEN \E s \in priv :
                      LET pend == [pending EXCEPT ![t] = @ \ {s}]
                          sp == [sigpending EXCEPT ![t] = Recalc(pend[t], shared, blocked[t])]
                      IN /\ UNCHANGED shared
                         /\ IF s = "USR"
                            THEN /\ pending' = pend /\ sigpending' = sp
                                 /\ UNCHANGED <<pc, flags, group, core, dumper, counted, dump>>
                            ELSE Fatal(t, s, pend, sp)
               ELSE IF shd # {}
               THEN \E s \in shd :
                      LET sh == shared \ {s}
                          sp == [sigpending EXCEPT ![t] = Recalc(pending[t], sh, blocked[t])]
                      IN /\ shared' = sh
                         /\ IF s = "USR"
                            THEN /\ pending' = pending /\ sigpending' = sp
                                 /\ UNCHANGED <<pc, flags, group, core, dumper, counted, dump>>
                            ELSE Fatal(t, s, pending, sp)
               ELSE \* nothing to dequeue: recalc_sigpending() and back to user mode
                    /\ sigpending' = [sigpending EXCEPT ![t] = Recalc(pending[t], shared, blocked[t])]
                    /\ UNCHANGED <<pc, flags, pending, shared, group, core, dumper, counted, dump>>
    /\ UNCHANGED <<notify, freed, decremented, released, release_list, rcu_reader>>
    /\ UnchangedMask /\ UnchangedWq /\ UnchangedEnv

\* clear_notify_signal() at get_signal() entry / exit_to_user_mode
HandleNotify(t) ==
    /\ pc[t] = "run"
    /\ notify[t]
    /\ notify' = [notify EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<pc, flags, pending, shared, sigpending, group, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

(***************************************************************************)
(* Signal masks: sigprocmask() and sigtimedwait()                          *)
(***************************************************************************)

\* retarget_shared_pending(tsk, which): wake one other thread that can take
\* a shared pending signal tsk just blocked.  The kernel walks the thread
\* list and stops at the first taker; the choice is nondeterministic here.
RetargetWake(t, which) ==
    LET rt == shared \cap which
        cand == {u \in Threads : u # t /\ Live(u) /\ "EXITING" \notin flags[u]
                                 /\ (rt \ blocked[u]) # {}}
    IN IF (FIX_RETARGET_GROUP_EXIT /\ group.exit) \/ rt = {} \/ cand = {}
       THEN sigpending' = sigpending
       ELSE \E u \in cand : sigpending' = [sigpending EXCEPT ![u] = TRUE]

\* sigprocmask(SIG_BLOCK, {USR}): __set_task_blocked() retargets what it
\* newly blocks, then recalc_sigpending()
BlockUsr(t) ==
    /\ Role[t] = "user"
    /\ InUserMode(t)
    /\ "USR" \notin blocked[t]
    /\ blocked' = [blocked EXCEPT ![t] = @ \cup {"USR"}]
    /\ IF sigpending[t] /\ ~GroupEmpty(t)
       THEN RetargetWake(t, {"USR"})
       ELSE sigpending' = sigpending
    /\ UNCHANGED <<pc, flags, pending, shared, realblocked, notify, group, freed>>
    /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* sigprocmask(SIG_UNBLOCK, {USR})
UnblockUsr(t) ==
    /\ Role[t] = "user"
    /\ InUserMode(t)
    /\ "USR" \in blocked[t]
    /\ blocked' = [blocked EXCEPT ![t] = @ \ {"USR"}]
    /\ sigpending' = [sigpending EXCEPT ![t] =
                        @ \/ Recalc(pending[t], shared, blocked'[t])]
    /\ UNCHANGED <<pc, flags, pending, shared, realblocked, notify, group, freed>>
    /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* do_sigtimedwait() for USR with USR blocked: nothing queued, so unblock
\* USR for the sleep and remember the real mask
SigWaitEnter(t) ==
    /\ Role[t] = "user"
    /\ InUserMode(t)
    /\ "USR" \in blocked[t]
    /\ "USR" \notin pending[t] /\ "USR" \notin shared
    /\ realblocked' = [realblocked EXCEPT ![t] = blocked[t]]
    /\ blocked' = [blocked EXCEPT ![t] = @ \ {"USR"}]
    /\ sigpending' = [sigpending EXCEPT ![t] = Recalc(pending[t], shared, blocked'[t])]
    /\ pc' = [pc EXCEPT ![t] = "sigwait"]
    /\ UNCHANGED <<flags, pending, shared, notify, group, freed>>
    /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* Back from the sleep (signal, zap or timeout): __set_task_blocked()
\* restores the real mask, which retargets USR, then the wait dequeues
\* with its own mask.
SigWaitWake(t) ==
    /\ pc[t] = "sigwait"
    /\ IF sigpending[t] /\ ~GroupEmpty(t)
       THEN RetargetWake(t, realblocked[t] \ blocked[t])
       ELSE sigpending' = sigpending
    /\ blocked' = [blocked EXCEPT ![t] = realblocked[t]]
    /\ realblocked' = [realblocked EXCEPT ![t] = {}]
    /\ IF "USR" \in pending[t]
       THEN /\ pending' = [pending EXCEPT ![t] = @ \ {"USR"}]
            /\ UNCHANGED shared
       ELSE IF "USR" \in shared
       THEN /\ shared' = shared \ {"USR"}
            /\ UNCHANGED pending
       ELSE UNCHANGED <<pending, shared>>
    /\ pc' = [pc EXCEPT ![t] = "run"]
    /\ UNCHANGED <<flags, notify, group, freed>>
    /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* PTRACE_SETSIGMASK on a user worker: refused with the fix
TracerClearMask(w) ==
    /\ IsWorker(w)
    /\ Alive(w)
    /\ ~FIX_PTRACE_MASK
    /\ budget.tracer > 0
    /\ budget' = [budget EXCEPT !.tracer = @ - 1]
    /\ blocked' = [blocked EXCEPT ![w] = {}]
    /\ sigpending' = [sigpending EXCEPT ![w] = @ \/ Recalc(pending[w], shared, {})]
    /\ UNCHANGED <<pc, flags, pending, shared, realblocked, notify, group, freed,
                   freeze, hist>>
    /\ UnchangedCore /\ UnchangedWq

(***************************************************************************)
(* Freezers: freeze_task() -> fake_signal_wake_up(), cgroup_freeze_task()  *)
(***************************************************************************)
\* Only a freeze that lands on a running dump is visible to the model:
\* before the dump the frozen thread would not start one, and the model
\* has no thaw.
Freeze(kind) ==
    /\ kind \in {"pm", "cg2"}
    /\ freeze = "none"
    /\ DumperPc \in {"dump_wait", "dump_write"}
    /\ freeze' = kind
    /\ sigpending' = [t \in Threads |-> IF Alive(t) THEN TRUE ELSE sigpending[t]]
    /\ hist' = [hist EXCEPT !.freeze_mid_dump = DumperPc \in {"dump_wait", "dump_write"}]
    /\ UNCHANGED <<pc, flags, pending, shared, notify, group, freed, budget>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq

(***************************************************************************)
(* The dumper: coredump_wait_inactive(), the writes, coredump_finish()     *)
(***************************************************************************)

\* wait_var_event_state(TASK_UNINTERRUPTIBLE|TASK_FREEZABLE) returns
DumpWaitDone(t) ==
    /\ pc[t] = "dump_wait"
    /\ core.remaining = 0
    /\ pc' = [pc EXCEPT ![t] = "dump_write"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* dump_emit(): dump_interrupted() first, then a write that may have to
\* wait for room and then fails on signal_pending()
DumpChunk(t) ==
    /\ pc[t] = "dump_write"
    /\ IF DumpInterrupted(t)
       THEN /\ dump' = [dump EXCEPT !.result = "truncated"]
            /\ pc' = [pc EXCEPT ![t] = "dump_finish"]
       ELSE \/ /\ SignalPending(t)                    \* blocked and interrupted
               /\ dump' = [dump EXCEPT !.result = "truncated"]
               /\ pc' = [pc EXCEPT ![t] = "dump_finish"]
            \/ /\ dump.written + 1 < Chunks           \* the write went through
               /\ dump' = [dump EXCEPT !.written = @ + 1]
               /\ UNCHANGED pc
            \/ /\ dump.written + 1 = Chunks
               /\ dump' = [dump EXCEPT !.written = @ + 1, !.result = "complete"]
               /\ pc' = [pc EXCEPT ![t] = "dump_finish"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   core, dumper, counted, decremented, released, release_list,
                   rcu_reader>>
    /\ UnchangedMask /\ UnchangedWq /\ UnchangedEnv

\* coredump_finish(): detach core_state under siglock, then release the
\* parked threads under rcu_read_lock() with the fix
DumpFinish(t) ==
    /\ pc[t] = "dump_finish"
    /\ release_list' = core.tasks
    /\ core' = [active |-> FALSE, remaining |-> 0, tasks |-> {}]
    /\ rcu_reader' = FIX_RCU_RELEASE
    /\ pc' = [pc EXCEPT ![t] = "dump_release"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   dumper, counted, decremented, released, dump>>
    /\ UnchangedMask /\ UnchangedWq /\ UnchangedEnv

\* curr->task = NULL: from here on the parked thread may leave
ReleaseClear(t, u) ==
    /\ pc[t] = "dump_release"
    /\ u \in release_list
    /\ ~released[u]
    /\ released' = [released EXCEPT ![u] = TRUE]
    /\ UNCHANGED <<pc, flags, pending, shared, sigpending, notify, group, freed,
                   core, dumper, counted, decremented, release_list, rcu_reader, dump>>
    /\ UnchangedMask /\ UnchangedWq /\ UnchangedEnv

\* wake_up_process(task): touches the task_struct
ReleaseWake(t, u) ==
    /\ pc[t] = "dump_release"
    /\ u \in release_list
    /\ released[u]
    /\ release_list' = release_list \ {u}
    /\ UNCHANGED <<pc, flags, pending, shared, sigpending, notify, group, freed,
                   core, dumper, counted, decremented, released, rcu_reader, dump>>
    /\ UnchangedMask /\ UnchangedWq /\ UnchangedEnv

\* The dumper is done: a user worker returns from get_signal() (unfixed
\* tree only), everybody else calls do_group_exit()
ReleaseDone(t) ==
    /\ pc[t] = "dump_release"
    /\ release_list = {}
    /\ rcu_reader' = FALSE
    /\ IF IsWorker(t)
       THEN /\ WorkerLeave(t)
            /\ UNCHANGED <<pending, sigpending, group>>
       ELSE DoGroupExit(t, pending, sigpending)
    /\ UNCHANGED <<flags, shared, notify, freed, core, dumper, counted,
                   decremented, released, release_list, dump>>
    /\ UnchangedMask /\ UnchangedWq /\ UnchangedEnv

(***************************************************************************)
(* do_exit()                                                               *)
(***************************************************************************)

\* exit(2)
ExitSyscall(t) ==
    /\ Role[t] = "user"
    /\ InUserMode(t)
    /\ pc' = [pc EXCEPT ![t] = "exit_sync"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* exit_group(2)
ExitGroupSyscall(t) ==
    /\ Role[t] = "user"
    /\ InUserMode(t)
    /\ DoGroupExit(t, pending, sigpending)
    /\ UNCHANGED <<flags, shared, notify, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* synchronize_group_exit() and coredump_task_exit(): the last thread to
\* leave marks the group, PF_POSTCOREDUMP goes on under siglock together
\* with the core_state read.  With core_state set the thread decrements
\* threads_remaining; only a PF_SIGNALED thread joins the list and parks.
SyncGroupExit(t) ==
    /\ pc[t] = "exit_sync"
    /\ LET q == group.quick - 1
       IN group' = [group EXCEPT !.quick = q, !.exit = @ \/ q = 0]
    /\ flags' = [flags EXCEPT ![t] = @ \cup {"POSTCOREDUMP"}]
    /\ IF core.active
       THEN /\ decremented' = [decremented EXCEPT ![t] = TRUE]
            /\ IF "SIGNALED" \in flags[t]
               THEN /\ core' = [core EXCEPT !.remaining = @ - 1, !.tasks = @ \cup {t}]
                    /\ pc' = [pc EXCEPT ![t] = "parked"]
               ELSE /\ core' = [core EXCEPT !.remaining = @ - 1]
                    /\ pc' = [pc EXCEPT ![t] = "exit_cancel"]
       ELSE /\ pc' = [pc EXCEPT ![t] = "exit_cancel"]
            /\ UNCHANGED <<core, decremented>>
    /\ UNCHANGED <<pending, shared, sigpending, notify, freed, dumper, counted,
                   released, release_list, rcu_reader, dump>>
    /\ UnchangedMask /\ UnchangedWq /\ UnchangedEnv

\* The parked loop sees self.task == NULL.  Any wakeup, also a spurious
\* one, gets it there; it does not wait for wake_up_process().
Unpark(t) ==
    /\ pc[t] = "parked"
    /\ released[t]
    /\ pc' = [pc EXCEPT ![t] = "exit_cancel"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* io_uring_files_cancel(): io_wq_exit_start() sets IO_WQ_BIT_EXIT, the
\* cancel loop may run task work, io_wq_exit_workers() cancels queued
\* creations and waits for wq->worker_done
ExitCancel(t) ==
    /\ pc[t] = "exit_cancel"
    /\ IF t \in RingOwners
       THEN /\ wqexit' = [wqexit EXCEPT ![t] = TRUE]
            /\ pc' = [pc EXCEPT ![t] = "exit_cancel_tw"]
       ELSE /\ pc' = [pc EXCEPT ![t] = "exit_signals"]
            /\ UNCHANGED wqexit
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   twq, owner, refput>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedEnv

ExitCancelWait(t) ==
    /\ pc[t] = "exit_cancel_tw"
    /\ twq' = [twq EXCEPT ![t] = @ \cap {"retry"}]   \* io_wq_cancel_tw_create()
    /\ pc' = [pc EXCEPT ![t] = "exit_wait_workers"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   wqexit, owner, refput>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedEnv

ExitWorkersDone(t) ==
    /\ pc[t] = "exit_wait_workers"
    /\ WorkersDone(t)                                \* wait_for_completion(worker_done)
    /\ pc' = [pc EXCEPT ![t] = "exit_signals"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* exit_signals(): PF_EXITING; a thread with a signal pending retargets
\* the shared ones it did not block, unless the group is already dying
ExitSignals(t) ==
    /\ pc[t] = "exit_signals"
    /\ flags' = [flags EXCEPT ![t] = @ \cup {"EXITING"}]
    /\ IF GroupEmpty(t) \/ group.exit \/ ~sigpending[t]
       THEN sigpending' = sigpending
       ELSE RetargetWake(t, Signals \ blocked[t])
    /\ pc' = [pc EXCEPT ![t] = "exit_notify"]
    /\ UNCHANGED <<pending, shared, notify, group, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* exit_notify() and release_task(): a leader with live siblings stays a
\* zombie, everybody else is released, which is where __exit_signal()
\* drops notify_count for de_thread()
ExitNotify(t) ==
    /\ pc[t] = "exit_notify"
    /\ IF t = Leader /\ ~GroupEmpty(t)
       THEN /\ pc' = [pc EXCEPT ![t] = "zombie"]
            /\ UNCHANGED group
       ELSE /\ pc' = [u \in Threads |->
                        IF u = t THEN "dead"
                        ELSE IF u = Leader /\ pc[Leader] = "zombie"
                                /\ OthersLive(t) = {Leader}
                        THEN "dead"                   \* the parent reaps the zombie leader
                        ELSE pc[u]]
            /\ group' = [group EXCEPT !.notify_count =
                           IF @ > 0 /\ t # Leader THEN @ - 1 ELSE @]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* An RCU grace period after release_task(): delayed_put_task_struct().
\* Only a thread the dumper still has to wake can be hurt by it, so the
\* model frees only those; freeing anybody else changes nothing it checks.
Freed(t) ==
    /\ pc[t] = "dead"
    /\ t \in release_list
    /\ ~freed[t]
    /\ ~rcu_reader
    /\ freed' = [freed EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<pc, flags, pending, shared, sigpending, notify, group>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

(***************************************************************************)
(* io-wq workers and the SQPOLL thread                                     *)
(***************************************************************************)

\* io_wq_worker() sees IO_WQ_BIT_EXIT
WorkerSeesExit(w) ==
    /\ IsIoWq(w)
    /\ pc[w] = "run"
    /\ wqexit[owner[w]]
    /\ pc' = [pc EXCEPT ![w] = "wq_exit"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* A worker blocks inside a request with more work queued:
\* io_wq_worker_sleeping() -> io_wq_dec_running() -> io_queue_worker_create()
\* adds create_worker_cb() to the owner with TWA_SIGNAL, unless the wq is
\* on its way out.
WorkerQueuesCreate(w) ==
    /\ IsIoWq(w)
    /\ pc[w] = "run"
    /\ ~wqexit[owner[w]]
    /\ w \notin twq[owner[w]]                        \* worker->create_state
    /\ twq' = [twq EXCEPT ![owner[w]] = @ \cup {w}]
    /\ notify' = [notify EXCEPT ![owner[w]] = TRUE]
    /\ hist' = [hist EXCEPT !.notify_dumper = @ \/ (owner[w] = dumper /\ Dumping)]
    /\ UNCHANGED <<pc, flags, pending, shared, sigpending, group, freed,
                   wqexit, owner, refput, freeze, budget>>
    /\ UnchangedMask /\ UnchangedCore

\* io_worker_exit(): cancel the worker's own queued creation, drop the
\* wq reference (this is what completes wq->worker_done), then do_exit()
WorkerExit(w) ==
    /\ pc[w] = "wq_exit"
    /\ twq' = [twq EXCEPT ![owner[w]] = @ \ {w}]
    /\ refput' = [refput EXCEPT ![w] = TRUE]
    /\ pc' = [pc EXCEPT ![w] = "exit_sync"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   wqexit, owner>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedEnv

\* io_sq_thread() after get_signal(): io_uring_cancel_generic(true, sqd)
SqCancel(s) ==
    /\ pc[s] = "sq_cancel"
    /\ wqexit' = [wqexit EXCEPT ![s] = TRUE]
    /\ pc' = [pc EXCEPT ![s] = "sq_cancel_tw"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   twq, owner, refput>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedEnv

SqCancelWait(s) ==
    /\ pc[s] = "sq_cancel_tw"
    /\ twq' = [twq EXCEPT ![s] = @ \cap {"retry"}]
    /\ pc' = [pc EXCEPT ![s] = "sq_wait_workers"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   wqexit, owner, refput>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedEnv

SqWorkersDone(s) ==
    /\ pc[s] = "sq_wait_workers"
    /\ WorkersDone(s)
    /\ pc' = [pc EXCEPT ![s] = "exit_sync"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

(***************************************************************************)
(* Worker creation: create_worker_cb()/create_worker_cont() as task work,  *)
(* create_io_worker() -> create_io_thread() -> copy_process()              *)
(***************************************************************************)

\* copy_process() for a CLONE_THREAD io thread: the child inherits the
\* creator's flags (only PF_SUPERPRIV|PF_WQ_WORKER|PF_IDLE|PF_NO_SETAFFINITY
\* are cleared), blocks everything but SIGKILL/SIGSTOP and joins the group
NewWorker(c, n) ==
    /\ pc' = [pc EXCEPT ![n] = "run"]
    /\ owner' = [owner EXCEPT ![n] = c]
    /\ flags' = [flags EXCEPT ![n] = flags[c]]
    /\ blocked' = [blocked EXCEPT ![n] = AllButKill]
    /\ pending' = [pending EXCEPT ![n] = {}]
    /\ sigpending' = [sigpending EXCEPT ![n] = FALSE]
    /\ notify' = [notify EXCEPT ![n] = FALSE]
    /\ refput' = [refput EXCEPT ![n] = FALSE]
    /\ group' = [group EXCEPT !.quick = @ + 1]

CreateWorker(c) ==
    /\ c \in RingOwners
    /\ pc[c] \in TaskWorkPoints
    /\ Runnable(c) # {}
    /\ \E item \in Runnable(c) :
        LET tw1 == [twq EXCEPT ![c] = @ \ {item}]
        IN \/ \* create_worker_cb(): io_acct_activate_free_worker() woke an
              \* idle worker instead of creating one
              /\ item # "cont"
              /\ \E w \in Threads : IsIoWq(w) /\ owner[w] = c /\ pc[w] = "run" /\ w # item
              /\ twq' = tw1
              /\ UNCHANGED <<pc, flags, pending, sigpending, notify, group,
                             blocked, owner, refput, budget>>
           \/ \* create_io_thread()
              IF (FIX_GATE_SIGNALED /\ "SIGNALED" \in flags[c])
                 \/ (FIX_GATE_POSTCOREDUMP /\ "POSTCOREDUMP" \in flags[c])
              THEN \* -EINTR, io_should_retry_thread() gives up
                   /\ twq' = tw1
                   /\ UNCHANGED <<pc, flags, pending, sigpending, notify, group,
                                  blocked, owner, refput, budget>>
              ELSE IF sigpending[c]
              THEN \* copy_process(): -ERESTARTNOINTR while TIF_SIGPENDING is set,
                   \* retried through queue_create_worker_retry() unless fatal
                   /\ IF ~FatalPending(c) /\ budget.retry > 0
                      THEN /\ twq' = [tw1 EXCEPT ![c] = @ \cup {"retry"}]
                           /\ budget' = [budget EXCEPT !.retry = @ - 1]
                      ELSE /\ twq' = tw1
                           /\ UNCHANGED budget
                   /\ UNCHANGED <<pc, flags, pending, sigpending, notify, group,
                                  blocked, owner, refput>>
              ELSE \/ \E n \in Threads :
                        /\ Role[n] = "slot" /\ pc[n] = "none"
                        /\ twq' = tw1
                        /\ NewWorker(c, n)
                        /\ UNCHANGED budget
                   \/ \* no worker slot left (nr_workers == max_workers)
                      /\ \A n \in Threads : Role[n] = "slot" => pc[n] # "none"
                      /\ twq' = tw1
                      /\ UNCHANGED <<pc, flags, pending, sigpending, notify, group,
                                     blocked, owner, refput, budget>>
    /\ UNCHANGED <<shared, realblocked, freed, wqexit, freeze, hist>>
    /\ UnchangedCore

\* The delayed work fires: io_workqueue_create() -> io_queue_worker_create()
\* queues create_worker_cont() with TWA_SIGNAL, or gives up and drops the
\* reference when the wq is already on its way out
RetryFires(c) ==
    /\ "retry" \in twq[c]
    /\ IF wqexit[c]
       THEN /\ twq' = [twq EXCEPT ![c] = @ \ {"retry"}]
            /\ UNCHANGED <<notify, hist>>
       ELSE /\ twq' = [twq EXCEPT ![c] = (@ \ {"retry"}) \cup {"cont"}]
            /\ notify' = [notify EXCEPT ![c] = TRUE]
            /\ hist' = [hist EXCEPT !.notify_dumper = @ \/ (c = dumper /\ Dumping)]
    /\ UNCHANGED <<pc, flags, pending, shared, sigpending, group, freed,
                   wqexit, owner, refput, freeze, budget>>
    /\ UnchangedMask /\ UnchangedCore

(***************************************************************************)
(* execve(2): begin_new_exec() and de_thread()                             *)
(***************************************************************************)

ExecStart(e) ==
    /\ Role[e] = "user"
    /\ InUserMode(e)
    /\ budget.exec > 0
    /\ budget' = [budget EXCEPT !.exec = @ - 1]
    /\ IF FIX_EXEC_CANCEL_FIRST /\ e \in RingOwners
       THEN /\ wqexit' = [wqexit EXCEPT ![e] = TRUE]     \* io_uring_task_cancel()
            /\ pc' = [pc EXCEPT ![e] = "exec_cancel_tw"]
       ELSE /\ pc' = [pc EXCEPT ![e] = "exec_dethread"]
            /\ UNCHANGED wqexit
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   twq, owner, refput, freeze, hist>>
    /\ UnchangedMask /\ UnchangedCore

ExecCancelWait(e) ==
    /\ pc[e] = "exec_cancel_tw"
    /\ twq' = [twq EXCEPT ![e] = @ \cap {"retry"}]
    /\ pc' = [pc EXCEPT ![e] = "exec_wait_workers"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   wqexit, owner, refput>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedEnv

ExecWorkersDone(e) ==
    /\ pc[e] = "exec_wait_workers"
    /\ WorkersDone(e)
    /\ pc' = [pc EXCEPT ![e] = "exec_dethread"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* de_thread(): refuse if a group action is under way, else become
\* group_exec_task, SIGKILL the siblings and count them
DeThread(e) ==
    /\ pc[e] = "exec_dethread"
    /\ IF GroupEmpty(e)
       THEN /\ pc' = [pc EXCEPT ![e] = "exec_post"]
            /\ UNCHANGED <<pending, sigpending, group>>
       ELSE IF group.exit \/ group.exec # NoThread
       THEN /\ pc' = [pc EXCEPT ![e] = "run"]          \* -EAGAIN
            /\ UNCHANGED <<pending, sigpending, group>>
       ELSE /\ group' = [group EXCEPT
                          !.exec = e,
                          !.notify_count = Cardinality(OthersLive(e))
                                           - (IF e = Leader THEN 0 ELSE 1)]
            /\ pending' = [u \in Threads |->
                             IF u # e /\ Alive(u) THEN pending[u] \cup {"KILL"}
                             ELSE pending[u]]
            /\ sigpending' = [u \in Threads |->
                             IF u # e /\ Alive(u) THEN TRUE ELSE sigpending[u]]
            /\ pc' = [pc EXCEPT ![e] = "exec_wait"]
    /\ UNCHANGED <<flags, shared, notify, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* notify_count reached zero and, for a non-leader, the leader is a
\* zombie it can release
DeThreadDone(e) ==
    /\ pc[e] = "exec_wait"
    /\ group.notify_count = 0
    /\ e = Leader \/ pc[Leader] = "zombie"
    /\ group' = [group EXCEPT !.exec = NoThread]
    /\ pc' = [u \in Threads |->
                IF u = e THEN "exec_post"
                ELSE IF u = Leader THEN "dead"          \* release_task(leader)
                ELSE pc[u]]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* __fatal_signal_pending() while waiting: give the group back
DeThreadKilled(e) ==
    /\ pc[e] = "exec_wait"
    /\ "KILL" \in pending[e]
    /\ group' = [group EXCEPT !.exec = NoThread, !.notify_count = 0]
    /\ pc' = [pc EXCEPT ![e] = "run"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

\* After de_thread(): the unfixed tree cancels io_uring here, which runs
\* task work in what is supposed to be a single-threaded process
ExecPost(e) ==
    /\ pc[e] = "exec_post"
    /\ IF ~FIX_EXEC_CANCEL_FIRST /\ e \in RingOwners
       THEN /\ wqexit' = [wqexit EXCEPT ![e] = TRUE]
            /\ pc' = [pc EXCEPT ![e] = "exec_late_tw"]
       ELSE /\ pc' = [pc EXCEPT ![e] = "run"]
            /\ UNCHANGED wqexit
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   twq, owner, refput>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedEnv

ExecLateWait(e) ==
    /\ pc[e] = "exec_late_tw"
    /\ twq' = [twq EXCEPT ![e] = @ \cap {"retry"}]
    /\ pc' = [pc EXCEPT ![e] = "exec_late_wait"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed,
                   wqexit, owner, refput>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedEnv

ExecLateDone(e) ==
    /\ pc[e] = "exec_late_wait"
    /\ WorkersDone(e)
    /\ pc' = [pc EXCEPT ![e] = "run"]
    /\ UNCHANGED <<flags, pending, shared, sigpending, notify, group, freed>>
    /\ UnchangedMask /\ UnchangedCore /\ UnchangedWq /\ UnchangedEnv

(***************************************************************************)
(* The specification                                                       *)
(***************************************************************************)

Init ==
    /\ pc = [t \in Threads |-> IF Role[t] = "slot" THEN "none" ELSE "run"]
    /\ flags = [t \in Threads |-> {}]
    /\ pending = [t \in Threads |-> {}]
    /\ shared = {}
    /\ blocked = [t \in Threads |-> IF IsWorker(t) THEN AllButKill ELSE {}]
    /\ realblocked = [t \in Threads |-> {}]
    /\ sigpending = [t \in Threads |-> FALSE]
    /\ notify = [t \in Threads |-> FALSE]
    /\ group = [exit |-> FALSE, exec |-> NoThread, notify_count |-> 0,
                quick |-> Cardinality({t \in Threads : Role[t] # "slot"})]
    /\ core = [active |-> FALSE, remaining |-> 0, tasks |-> {}]
    /\ dumper = NoThread
    /\ counted = {}
    /\ decremented = [t \in Threads |-> FALSE]
    /\ released = [t \in Threads |-> FALSE]
    /\ release_list = {}
    /\ rcu_reader = FALSE
    /\ freed = [t \in Threads |-> FALSE]
    /\ wqexit = [t \in Threads |-> FALSE]
    /\ twq = [t \in Threads |-> {}]
    /\ owner = Owner0
    /\ refput = [t \in Threads |-> FALSE]
    /\ dump = [written |-> 0, result |-> "none"]
    /\ freeze = "none"
    /\ hist = [kill |-> FALSE, notify_dumper |-> FALSE, freeze_mid_dump |-> FALSE]
    /\ budget = [KILL |-> BudgetKILL, CORE |-> BudgetCORE,
                 TERM |-> BudgetTERM, USR |-> BudgetUSR,
                 exec |-> ExecBudget, tracer |-> TracerBudget,
                 retry |-> RetryBudget]

\* Steps a thread takes on its own once it can; each of them is fair
ThreadStep(t) ==
    \/ GetSignal(t) \/ HandleNotify(t) \/ SigWaitWake(t)
    \/ DumpWaitDone(t) \/ DumpChunk(t) \/ DumpFinish(t)
    \/ (\E u \in Threads : ReleaseClear(t, u) \/ ReleaseWake(t, u))
    \/ ReleaseDone(t)
    \/ SyncGroupExit(t) \/ Unpark(t) \/ ExitCancel(t) \/ ExitCancelWait(t)
    \/ ExitWorkersDone(t) \/ ExitSignals(t) \/ ExitNotify(t)
    \/ WorkerSeesExit(t) \/ WorkerExit(t)
    \/ SqCancel(t) \/ SqCancelWait(t) \/ SqWorkersDone(t)
    \/ CreateWorker(t) \/ RetryFires(t)
    \/ ExecCancelWait(t) \/ ExecWorkersDone(t) \/ DeThread(t) \/ DeThreadDone(t)
    \/ DeThreadKilled(t) \/ ExecPost(t) \/ ExecLateWait(t) \/ ExecLateDone(t)

ThreadFairness(t) ==
    /\ WF_vars(GetSignal(t)) /\ WF_vars(HandleNotify(t)) /\ WF_vars(SigWaitWake(t))
    /\ WF_vars(DumpWaitDone(t)) /\ WF_vars(DumpChunk(t)) /\ WF_vars(DumpFinish(t))
    /\ \A u \in Threads : WF_vars(ReleaseClear(t, u)) /\ WF_vars(ReleaseWake(t, u))
    /\ WF_vars(ReleaseDone(t))
    /\ WF_vars(SyncGroupExit(t)) /\ WF_vars(Unpark(t)) /\ WF_vars(ExitCancel(t))
    /\ WF_vars(ExitCancelWait(t)) /\ WF_vars(ExitWorkersDone(t))
    /\ WF_vars(ExitSignals(t)) /\ WF_vars(ExitNotify(t))
    /\ WF_vars(WorkerSeesExit(t)) /\ WF_vars(WorkerExit(t))
    /\ WF_vars(SqCancel(t)) /\ WF_vars(SqCancelWait(t)) /\ WF_vars(SqWorkersDone(t))
    /\ WF_vars(CreateWorker(t)) /\ WF_vars(RetryFires(t))
    /\ WF_vars(ExecCancelWait(t)) /\ WF_vars(ExecWorkersDone(t))
    /\ WF_vars(DeThread(t)) /\ WF_vars(DeThreadDone(t)) /\ WF_vars(DeThreadKilled(t))
    /\ WF_vars(ExecPost(t)) /\ WF_vars(ExecLateWait(t)) /\ WF_vars(ExecLateDone(t))

\* Steps the environment or user space takes; nothing forces them
EnvStep ==
    \/ \E sig \in Signals : SendGroup(sig)
    \/ \E t \in Threads, sig \in Signals : SendThread(t, sig)
    \/ \E t \in Threads : BlockUsr(t) \/ UnblockUsr(t) \/ SigWaitEnter(t)
                          \/ TracerClearMask(t) \/ ExitSyscall(t)
                          \/ ExitGroupSyscall(t) \/ ExecStart(t)
                          \/ WorkerQueuesCreate(t) \/ Freed(t)
    \/ \E k \in {"pm", "cg2"} : Freeze(k)

Next == EnvStep \/ \E t \in Threads : ThreadStep(t)

Fairness == \A t \in Threads : ThreadFairness(t)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

TypeOK ==
    /\ pc \in [Threads -> PCs]
    /\ flags \in [Threads -> SUBSET FlagSet]
    /\ pending \in [Threads -> SUBSET Signals]
    /\ shared \in SUBSET Signals
    /\ blocked \in [Threads -> SUBSET Signals]
    /\ realblocked \in [Threads -> SUBSET Signals]
    /\ sigpending \in [Threads -> BOOLEAN]
    /\ notify \in [Threads -> BOOLEAN]
    /\ group.exit \in BOOLEAN
    /\ group.exec \in Threads \cup {NoThread}
    /\ group.notify_count \in Int
    /\ group.quick \in Int
    /\ core.active \in BOOLEAN
    /\ core.remaining \in Int
    /\ core.tasks \in SUBSET Threads
    /\ dumper \in Threads \cup {NoThread}
    /\ counted \in SUBSET Threads
    /\ release_list \in SUBSET Threads
    /\ owner \in [Threads -> Threads \cup {NoThread}]
    /\ twq \in [Threads -> SUBSET (Threads \cup {"cont", "retry"})]
    /\ dump.written \in 0..Chunks
    /\ dump.result \in {"none", "complete", "truncated"}
    /\ freeze \in {"none", "pm", "cg2"}

\* threads_remaining never goes below zero
RemainingNonNegative == core.active => core.remaining >= 0

\* threads_remaining is exactly the counted threads that have not
\* announced themselves yet (fork: don't create io threads once
\* PF_POSTCOREDUMP is set; fork: move the checks into create_io_thread())
CountConsistent ==
    core.active =>
        core.remaining = Cardinality({t \in counted : ~decremented[t]})

\* only a thread zap_process() counted ever decrements
OnlyCountedDecrement == \A t \in Threads : decremented[t] => t \in counted

\* the dumper leaves coredump_wait_inactive() only after every counted
\* thread went through coredump_task_exit()
ReleasedAfterAllParked ==
    (dumper # NoThread /\ DumperPc # "dump_wait")
        => \A t \in counted : decremented[t]

\* coredump_finish() never wakes a freed task_struct
\* (coredump: hold RCU while releasing parked threads)
NoUseAfterFree ==
    \A u \in release_list : released[u] => ~freed[u]

\* after de_thread() the exec'ing thread is alone and stays alone until
\* it is done (exec: cancel io_uring requests before de_thread())
SingleThreadedExec ==
    \A e \in Threads : pc[e] \in ExecWindow =>
        \A t \in Threads : t # e => pc[t] \in {"none", "dead"}

\* a user worker never dumps core (signal: fix coredump deadlock with
\* PF_USER_WORKER)
WorkerNeverDumps == \A t \in Threads : IsWorker(t) => pc[t] \notin DumpStates

\* a user worker keeps the mask copy_process() gave it (ptrace: refuse to
\* change the signal mask of a user worker)
WorkerMaskIntact ==
    \A t \in Threads : (IsWorker(t) /\ pc[t] # "none") => blocked[t] = AllButKill

\* a truncated core has a reason: SIGKILL, a freezer, or task work landing
\* on the dumper (signal: only SIGKILL and the freezers interrupt a
\* coredumping task; signal: don't retarget shared signals in a dying
\* thread group)
TruncationJustified ==
    dump.result = "truncated" => (hist.kill \/ Freezing \/ hist.notify_dumper)

\* the stricter version without the task work escape; fails on this tree
\* because TIF_NOTIFY_SIGNAL still counts as signal_pending() for a
\* PF_DUMPCORE task
TruncationJustifiedStrict ==
    dump.result = "truncated" => (hist.kill \/ Freezing)

\* a freeze that arrives before the last write aborts the dump, for every
\* freezer and whether the core goes to a file or a pipe
FreezeAbortsDump == hist.freeze_mid_dump => dump.result # "complete"

AllDead == \A t \in Threads : pc[t] \in {"none", "dead"}

\* A SIGKILL that complete_signal() fanned out tears the group down,
\* whatever state it is in.  (A tgkill() to a thread that is already
\* PF_EXITING is not fanned out: wants_signal() refuses it and the group
\* lives on.  That is how the kernel behaves and not what this checks.)
KillTerminates == [](hist.kill => <>AllDead)

\* a dump that started ends (no rendezvous deadlock)
DumpEnds == [](dumper # NoThread => <>(~Dumping))

=============================================================================
