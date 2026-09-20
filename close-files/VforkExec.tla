---------------------------- MODULE VforkExec ----------------------------
(***************************************************************************)
(* A vfork() child that execs while it holds the last reference to a file *)
(* whose ->flush() or ->release() needs the parent to run.                 *)
(*                                                                         *)
(* The parent sleeps in wait_for_vfork_done() until the child's            *)
(* exec_mmap() -> mm_exit_exec_release() -> complete_vfork_done().  In     *)
(* begin_new_exec() the close-on-exec walk sits before exec_mmap():        *)
(*   deferred   before 64cdb497e727: ->flush() in the walk, the final      *)
(*              ->release() from task work at the return to user mode,    *)
(*              after the parent was released                             *)
(*   sync       64cdb497e727: ->flush() and ->release() in the walk, both  *)
(*              before the parent is released                              *)
(* exit(2) is the other way out of a vfork child: exit_mm() releases the  *)
(* parent before exit_files() closes anything.                            *)
(*                                                                         *)
(* NeedsParent names the operation on the file that can only complete    *)
(* while the parent runs: "flush" (a FUSE file the parent serves),        *)
(* "release" (a ublk device the parent serves, a TCP socket the parent     *)
(* must drain with SO_LINGER) or "none".                                  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS CLOEXEC_PUT,   \* "deferred" or "sync"
          NeedsParent    \* "flush", "release" or "none"

ASSUME CLOEXEC_PUT \in {"deferred", "sync"}
ASSUME NeedsParent \in {"flush", "release", "none"}

VARIABLES parent,   \* "waiting" in wait_for_vfork_done(), or "running"
          child,    \* where the child is
          route     \* "exec" or "exit"

vars == <<parent, child, route>>

Init ==
    /\ parent = "waiting"
    /\ child = "start"
    /\ route \in {"exec", "exit"}

CanRun(op) == NeedsParent # op \/ parent = "running"

\* execve(): de_thread() is done, close_cloexec_files() runs
ExecFlush ==
    /\ route = "exec" /\ child = "start"
    /\ CanRun("flush")
    /\ child' = IF CLOEXEC_PUT = "sync" THEN "release_inline" ELSE "mmap"
    /\ UNCHANGED <<parent, route>>

ExecReleaseInline ==
    /\ child = "release_inline"
    /\ CanRun("release")
    /\ child' = "mmap"
    /\ UNCHANGED <<parent, route>>

\* exec_mmap(): mm_exit_exec_release() completes vfork_done
ExecMmap ==
    /\ child = "mmap"
    /\ parent' = "running"
    /\ child' = IF CLOEXEC_PUT = "deferred" THEN "taskwork" ELSE "done"
    /\ UNCHANGED route

\* return to user mode: the deferred final put runs
ExecTaskWork ==
    /\ child = "taskwork"
    /\ CanRun("release")
    /\ child' = "done"
    /\ UNCHANGED <<parent, route>>

\* exit(2): exit_mm() first, exit_files() after
ExitMm ==
    /\ route = "exit" /\ child = "start"
    /\ parent' = "running"
    /\ child' = "files"
    /\ UNCHANGED route

ExitFiles ==
    /\ child = "files"
    /\ CanRun("flush") /\ CanRun("release")
    /\ child' = "done"
    /\ UNCHANGED <<parent, route>>

Next == ExecFlush \/ ExecReleaseInline \/ ExecMmap \/ ExecTaskWork
        \/ ExitMm \/ ExitFiles

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The child gets through, so the parent gets out of vfork()
ChildCompletes == <>(child = "done")

\* The exit route never depends on the parent
ExitRouteCompletes == (route = "exit") => <>(child = "done")

=============================================================================
