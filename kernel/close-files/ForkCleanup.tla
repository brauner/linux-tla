--------------------------- MODULE ForkCleanup ---------------------------
(***************************************************************************)
(* fork: release the files of a failed fork after sched_cancel_fork()     *)
(*                                                                         *)
(* sched_fork() -> scx_pre_fork() takes scx_fork_rwsem for read and       *)
(* copy_process() holds it until sched_post_fork() or                     *)
(* sched_cancel_fork().  The child's descriptor table is a dup_fd() copy   *)
(* and may hold the last reference to a sched_ext link.  Its release is    *)
(* bpf_scx_unreg() -> scx_disable() + kthread_flush_work(disable_work),    *)
(* and scx_disable_workfn() takes scx_fork_rwsem for write.               *)
(*                                                                         *)
(*   files_first   as merged: exit_files() at bad_fork_cleanup_files,      *)
(*                 before sched_cancel_fork()                              *)
(*   cancel_first  the fix: sched_cancel_fork() drops the read side, then  *)
(*                 exit_files() runs                                       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT ORDER
ASSUME ORDER \in {"files_first", "cancel_first"}

VARIABLES forker,    \* "fork", "fail", "release", "wait", "cancel", "done"
          work,      \* "idle", "queued", "running", "done"
          readers,   \* read holders of scx_fork_rwsem
          writer     \* the disable work holds it for write

vars == <<forker, work, readers, writer>>

Init ==
    /\ forker = "fork"
    /\ work = "idle"
    /\ readers = 0
    /\ writer = FALSE

\* sched_fork() -> scx_pre_fork(): percpu_down_read()
ForkTakesRead ==
    /\ forker = "fork" /\ ~writer
    /\ readers' = readers + 1
    /\ forker' = "fail"
    /\ UNCHANGED <<work, writer>>

\* copy_process() fails after that; which cleanup step comes first
\* depends on ORDER
ForkFails ==
    /\ forker = "fail"
    /\ forker' = IF ORDER = "files_first" THEN "release" ELSE "cancel"
    /\ UNCHANGED <<work, readers, writer>>

\* exit_files() -> ... -> bpf_scx_unreg(): scx_disable() queues the work,
\* scx_flush_disable_work() waits for it
ForkReleases ==
    /\ forker = "release"
    /\ work' = "queued"
    /\ forker' = "wait"
    /\ UNCHANGED <<readers, writer>>

ForkWaitsForWork ==
    /\ forker = "wait" /\ work = "done"
    /\ forker' = IF ORDER = "files_first" THEN "cancel" ELSE "done"
    /\ UNCHANGED <<work, readers, writer>>

\* sched_cancel_fork() -> scx_cancel_fork(): percpu_up_read()
ForkCancels ==
    /\ forker = "cancel"
    /\ readers' = readers - 1
    /\ forker' = IF ORDER = "files_first" THEN "done" ELSE "release"
    /\ UNCHANGED <<work, writer>>

\* scx_disable_workfn(): percpu_down_write() waits for every reader
WorkTakesWrite ==
    /\ work = "queued" /\ readers = 0 /\ ~writer
    /\ writer' = TRUE
    /\ work' = "running"
    /\ UNCHANGED <<forker, readers>>

WorkDone ==
    /\ work = "running"
    /\ writer' = FALSE
    /\ work' = "done"
    /\ UNCHANGED <<forker, readers>>

Next == ForkTakesRead \/ ForkFails \/ ForkReleases \/ ForkWaitsForWork
        \/ ForkCancels \/ WorkTakesWrite \/ WorkDone

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

ForkCleanupCompletes == <>(forker = "done")

=============================================================================
