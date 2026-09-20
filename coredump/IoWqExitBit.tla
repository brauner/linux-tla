--------------------------- MODULE IoWqExitBit ---------------------------
(***************************************************************************)
(* io-wq: order the exit bit against worker creation task work             *)
(*                                                                         *)
(* Two actors race on one io-wq:                                           *)
(*                                                                         *)
(*   exiter   the wq owner in io_uring_cancel_generic():                   *)
(*            io_wq_exit_start()   set_bit(IO_WQ_BIT_EXIT)                 *)
(*                                 [smp_mb__after_atomic() with the fix]   *)
(*            io_wq_exit_workers() io_wq_cancel_tw_create(): loads         *)
(*                                 task->task_works and cancels queued     *)
(*                                 creations, then waits for worker_done   *)
(*                                                                         *)
(*   creator  a worker in io_queue_worker_create():                        *)
(*            test_bit(EXIT) -> fail if set                                *)
(*            task_work_add() (cmpxchg, full barrier)                      *)
(*            test_bit(EXIT) -> io_wq_cancel_tw_create() if set            *)
(*                                                                         *)
(* A queued creation holds a wq->worker_refs reference, so one that stays  *)
(* queued after the cancel makes the exiter wait for worker_done forever.  *)
(*                                                                         *)
(* Memory model: the exiter's set_bit() goes through a store buffer and    *)
(* becomes visible to the creator only when it is flushed.  The exiter     *)
(* reads its own store early (forwarding).  A full barrier flushes the     *)
(* buffer before the next load.  task_work_add() is a cmpxchg, so the      *)
(* creator's add is visible at once and its later load is ordered after    *)
(* it.  This is the store->load reordering that weakly ordered             *)
(* architectures allow across set_bit() and the spin_lock() inside         *)
(* task_work_cancel_match(), which is only an acquire.                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT FIX_BARRIER

VARIABLES
    exit_visible,   \* IO_WQ_BIT_EXIT as every other CPU sees it
    exit_buffered,  \* the exiter's set_bit() still sits in its store buffer
    queued,         \* the creation item is on task->task_works
    creator,        \* "check1", "add", "check2", "done"
    exiter          \* "set", "cancel", "wait", "done"

vars == <<exit_visible, exit_buffered, queued, creator, exiter>>

ExitSeenByExiter == exit_visible \/ exit_buffered

Init ==
    /\ exit_visible = FALSE
    /\ exit_buffered = FALSE
    /\ queued = FALSE
    /\ creator = "check1"
    /\ exiter = "set"

\* The store buffer drains at some point
Flush ==
    /\ exit_buffered
    /\ exit_visible' = TRUE
    /\ exit_buffered' = FALSE
    /\ UNCHANGED <<queued, creator, exiter>>

\* io_wq_exit_start(): set_bit(), and with the fix a full barrier right
\* after it, so the store is visible before io_wq_exit_workers() loads
ExiterSet ==
    /\ exiter = "set"
    /\ IF FIX_BARRIER
       THEN exit_visible' = TRUE /\ exit_buffered' = FALSE
       ELSE exit_visible' = exit_visible /\ exit_buffered' = TRUE
    /\ exiter' = "cancel"
    /\ UNCHANGED <<queued, creator>>

\* io_wq_cancel_tw_create(): task_work_cancel_match() loads the list
ExiterCancel ==
    /\ exiter = "cancel"
    /\ queued' = FALSE
    /\ exiter' = "wait"
    /\ UNCHANGED <<exit_visible, exit_buffered, creator>>

\* wait_for_completion(&wq->worker_done) returns only without a queued
\* creation holding a reference
ExiterWait ==
    /\ exiter = "wait"
    /\ ~queued
    /\ exiter' = "done"
    /\ UNCHANGED <<exit_visible, exit_buffered, queued, creator>>

\* "raced with exit, just ignore create call"
CreatorCheck1 ==
    /\ creator = "check1"
    /\ creator' = IF exit_visible THEN "done" ELSE "add"
    /\ UNCHANGED <<exit_visible, exit_buffered, queued, exiter>>

\* task_work_add(wq->task, &worker->create_work, TWA_SIGNAL)
CreatorAdd ==
    /\ creator = "add"
    /\ queued' = TRUE
    /\ creator' = "check2"
    /\ UNCHANGED <<exit_visible, exit_buffered, exiter>>

\* "EXIT may have been set after checking it above, check after adding"
CreatorCheck2 ==
    /\ creator = "check2"
    /\ queued' = IF exit_visible THEN FALSE ELSE queued
    /\ creator' = "done"
    /\ UNCHANGED <<exit_visible, exit_buffered, exiter>>

Next ==
    \/ Flush
    \/ ExiterSet \/ ExiterCancel \/ ExiterWait
    \/ CreatorCheck1 \/ CreatorAdd \/ CreatorCheck2

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Flush) /\ WF_vars(ExiterSet) /\ WF_vars(ExiterCancel)
        /\ WF_vars(ExiterWait)
        /\ WF_vars(CreatorCheck1) /\ WF_vars(CreatorAdd) /\ WF_vars(CreatorCheck2)

\* Once both sides ran, nothing may still be queued while the exiter waits
NoStrandedCreate ==
    (exiter = "wait" /\ creator = "done" /\ ~exit_buffered) => ~queued

\* The exiter gets out of io_wq_exit_workers()
ExiterFinishes == <>(exiter = "done")

=============================================================================
