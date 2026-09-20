---------------------------- MODULE Executor ----------------------------
(***************************************************************************)
(* One service started by the service manager through systemd-executor,   *)
(* and everything the manager hears about it afterwards: the messages the *)
(* executor sends before execve(), the SIGCHLD of every process it        *)
(* creates, the cgroup running empty, and the order in which the manager  *)
(* dispatches all of that against the state machine of the service.       *)
(*                                                                         *)
(* Tree: systemd v262-rc2-60-ge96ff3b5b9.                                  *)
(*                                                                         *)
(* Modelled code:                                                          *)
(*   src/core/execute.c      exec_spawn (posix_spawn of the pinned         *)
(*                           executor, the process starts in the cgroup)   *)
(*   src/core/exec-invoke.c  exec_invoke: send_user_lookup, setup_pam and  *)
(*                           the (sd-pam) child, setup_private_pids and    *)
(*                           the pidref handoff, exec_fd_mark_hot,         *)
(*                           send_handoff_timestamp, fexecve_or_execve,    *)
(*                           the EXIT_* codes of the failing steps         *)
(*   src/core/service.c      service_spawn_internal, service_enter_start,  *)
(*                           service_dispatch_exec_io, service_sigchld_    *)
(*                           event, service_notify_cgroup_empty_event,     *)
(*                           service_notify_pidref, service_handoff_       *)
(*                           timestamp, service_dispatch_timer, service_   *)
(*                           enter_{start_post,running,stop,signal,        *)
(*                           stop_post,dead}, service_set_state, the       *)
(*                           SERVICE_STATE_WITH_MAIN_PROCESS() rule        *)
(*   src/core/manager.c      the event sources and their EVENT_PRIORITY_*  *)
(*                           (manager.h), manager_dispatch_signal_fd,      *)
(*                           manager_dispatch_sigchld (waitid(P_ALL)),     *)
(*                           manager_dispatch_{user_lookup,handoff_        *)
(*                           timestamp,pidref_transport}_fd               *)
(*   src/core/cgroup.c       cgroup.events inotify, the cgroup empty queue *)
(*   src/core/unit.c         unit_kill_context (KillMode=), unit_watch_    *)
(*                           pidref, the JOB_START result in unit_notify   *)
(*   src/shared/barrier.c    the barrier between setup_pam() and (sd-pam)  *)
(*   src/basic/process-util.c pidref_safe_fork(FORK_DETACH)                *)
(*   kernel                  pipes: EOF once the last writer is gone,      *)
(*                           O_CLOEXEC on execve; SIGCHLD; zombies and     *)
(*                           reparenting to the reaper; PR_SET_PDEATHSIG   *)
(*                           and its kill permission check;                *)
(*                           cgroup.events "populated"                     *)
(*                                                                         *)
(* Switches:                                                               *)
(*   Prio                    the priority table of manager.h; the          *)
(*                           Prio*Late tables move one source below the   *)
(*                           SIGCHLD handling                              *)
(*   FIX_COLD_MARK           exec_fd_mark_hot(false) after a failed         *)
(*                           execve()                                      *)
(*   FIX_PAM_CLOSES_EXEC_FD  (sd-pam) closes exec_fd, commit 5863f1da42     *)
(*   FIX_PPID_CHECK          (sd-pam) checks getppid() before sigwait()    *)
(*   BARRIER                 setup_pam() waits for the barrier of (sd-pam) *)
(*   PAM_WAITS_FOR_PARENT    hypothetical: (sd-pam) keeps waiting when a   *)
(*                           SIGTERM finds its parent alive                *)
(*   FIX_PIDNS_PARENT_CLOSES_EXEC_FD  hypothetical: the pid namespace      *)
(*                           parent drops exec_fd before it lets the child *)
(*                           go on                                         *)
(*                                                                         *)
(* Abstractions:                                                           *)
(*   - One unit, one ExecStart=, no ExecStartPre/Post=, ExecStop/Post=,    *)
(*     no notify socket, no PIDFile=, ExitType=main, SendSIGKILL=yes,      *)
(*     Restart=no, no stop timeouts (a signalled process eventually dies). *)
(*   - exec_invoke() is a sequence of phases; each may fail with the       *)
(*     EXIT_* code the real step uses.  Everything between two phases that *)
(*     the manager cannot observe is folded into the phase.                *)
(*   - The executor starts inside the cgroup (CLONE_INTO_CGROUP).  Every   *)
(*     process of the model is in the unit's cgroup; "populated" is        *)
(*     whether any of them is alive, zombies do not count (cgroup_exit()). *)
(*   - Datagram sockets are FIFOs, one per socket.  A datagram is readable *)
(*     the moment it is sent, a pipe byte the moment it is written, EOF    *)
(*     the moment the last write end is closed, SIGCHLD the moment a child *)
(*     of the manager exits or a zombie is reparented to it.  The manager  *)
(*     dispatches the highest-priority readable source; that is what       *)
(*     sd_event_wait()/sd_event_dispatch() do with level-triggered sources *)
(*     and a full event queue.                                             *)
(*   - The (sd-pam) child cannot fail on its own; its privilege drop may.  *)
(*   - The intermediary of the FORK_DETACH double fork is not modelled;    *)
(*     the pid namespace child is a child of the manager from birth.       *)
(*   - The environment (a payload exit, systemctl stop, TimeoutStartSec=)  *)
(*     is never forced to act.                                             *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Type,             \* "simple", "exec" or "oneshot"
    PAM,              \* PAMName= is set: setup_pam() forks (sd-pam)
    PIDNS,            \* PrivatePIDs=yes: setup_private_pids() forks, the parent exits
    User,             \* User= is set: send_user_lookup(), enforce_user(), (sd-pam) drops privileges
    RemainAfterExit,
    KillMode,         \* "control-group" or "mixed"
    Prio,             \* [Events -> Int]: EVENT_PRIORITY_* of manager.h, the lowest number dispatches first
    StopBudget,       \* systemctl stop requests the environment may issue
    TimeoutBudget,    \* TimeoutStartSec= expiries the environment may fire
    PayloadStatuses,  \* exit statuses the payload may exit with, a subset of {0, 1}
    PamDropMayFail,   \* fully_set_uid_gid() in (sd-pam) may fail
    FIX_COLD_MARK,
    FIX_PAM_CLOSES_EXEC_FD,
    FIX_PPID_CHECK,
    BARRIER,
    PAM_WAITS_FOR_PARENT,
    FIX_PIDNS_PARENT_CLOSES_EXEC_FD

ASSUME Type \in {"simple", "exec", "oneshot"}
ASSUME KillMode \in {"control-group", "mixed"}
ASSUME PayloadStatuses \subseteq {0, 1}
ASSUME StopBudget \in Nat /\ TimeoutBudget \in Nat

Mgr    == "mgr"
Procs  == {"E", "C", "P"}   \* the executor, the pid namespace child, (sd-pam)
Events == {"user_lookup", "cg_inotify", "pidref", "handoff", "exec_fd",
           "sigchld", "signals", "cg_empty", "timer"}

\* manager.h: EVENT_PRIORITY_USER_LOOKUP ... EVENT_PRIORITY_CGROUP_EMPTY, timers at
\* SD_EVENT_PRIORITY_NORMAL.  "sigchld" is the deferred source that reaps,
\* "signals" the signalfd that enables it.
PrioDefault ==
    ("user_lookup" :> -12) @@ ("cg_inotify" :> -10) @@ ("pidref" :> -8) @@
    ("handoff" :> -7) @@ ("exec_fd" :> -6) @@ ("sigchld" :> -4) @@
    ("signals" :> -3) @@ ("cg_empty" :> -2) @@ ("timer" :> 0)
PrioExecFdLate     == [PrioDefault EXCEPT !["exec_fd"] = -1]
PrioPidrefLate     == [PrioDefault EXCEPT !["pidref"] = -1]
PrioHandoffLate    == [PrioDefault EXCEPT !["handoff"] = -1]
PrioUserLookupLate == [PrioDefault EXCEPT !["user_lookup"] = -1]

ASSUME \A e \in Events : Prio[e] \in Int

\* src/shared/exit-status.h
EXIT_FDS       == 202
EXIT_EXEC      == 203
EXIT_USER      == 217
EXIT_CGROUP    == 219
EXIT_PAM       == 224
EXIT_NAMESPACE == 226
EXIT_SECCOMP   == 228

ExecPCs == {"init", "creds", "setup", "pam", "pamsync", "ns", "nsexit", "sandbox",
            "hot", "handoff", "execve", "payload"}
PamPCs  == {"closefd", "drop", "prctl", "place", "check", "wait", "close", "exit"}
PCs     == ExecPCs \cup PamPCs \cup {"none", "dead"}

States == {"start", "running", "exited", "stop_sigterm", "stop_sigkill",
           "final_sigterm", "final_sigkill", "dead", "failed"}
Results == {"success", "exit-code", "signal", "timeout"}

VARIABLES
    \* the Service object in the manager
    state,          \* ServiceState (SERVICE_STOP_POST is never rested in: no ExecStopPost=)
    result,         \* s->result
    mainPid,        \* s->main_pid, "none" once pidref_done()
    job,            \* the start job: "running", "done", "failed", "canceled"
    timerArmed,     \* TimeoutStartSec= timer armed
    timerFired,     \* it expired and waits to be dispatched
    execFdSrc,      \* s->exec_fd_event_source exists
    hot,            \* s->exec_fd_hot
    watched,        \* the pids in u->pids / m->watch_pids
    uidKnown,       \* unit_notify_user_lookup() ran
    handoffRec,     \* exec_status_handoff() ran for the main process
    mainStatus,     \* s->main_exec_status: code and status of the main process
    sigchldDefer,   \* m->sigchld_event_source enabled
    sigPending,     \* SIGCHLD pending on the manager's signalfd
    cgInotify,      \* an inotify event on cgroup.events waits to be dispatched
    cgEmptyQ,       \* the unit is in m->cgroup_empty_queue
    \* the processes and the kernel
    pc,             \* [Procs -> PCs]
    uid,            \* [Procs -> {"root", "user"}]
    pdeath,         \* [Procs -> BOOLEAN]: PR_SET_PDEATHSIG SIGTERM armed
    parent,         \* [Procs -> Procs \cup {Mgr}]
    exitst,         \* [Procs -> [code, status]]: what waitid() will report
    unreaped,       \* dead and not yet reaped
    pipeW,          \* processes holding the write end of exec_fd
    pipeB,          \* bytes in the exec_fd pipe not read by the manager
    ulQ, hoQ, prQ,  \* user lookup, handoff timestamp and pidref sockets: sender pids
    sigterm,        \* [Procs -> BOOLEAN]: SIGTERM pending
    sigkill,        \* [Procs -> BOOLEAN]: SIGKILL pending
    session,        \* the PAM session: "none", "open", "closed"
    placed,         \* (sd-pam) placed its barrier
    dropFailed,     \* fully_set_uid_gid() failed in (sd-pam)
    \* history and bounds
    hist,           \* execd, lost, uidLate, handoffLost
    budget          \* stop, timeout

vars == <<state, result, mainPid, job, timerArmed, timerFired, execFdSrc, hot,
          watched, uidKnown, handoffRec, mainStatus, sigchldDefer, sigPending,
          cgInotify, cgEmptyQ, pc, uid, pdeath, parent, exitst, unreaped, pipeW,
          pipeB, ulQ, hoQ, prQ, sigterm, sigkill, session, placed, dropFailed,
          hist, budget>>

MgrAll == <<state, result, mainPid, job, timerArmed, execFdSrc, hot, watched,
            timerFired, uidKnown, handoffRec, mainStatus, sigchldDefer, cgEmptyQ>>
DieTuple == <<pc, exitst, unreaped, pipeW, parent, sigterm, sigPending, cgInotify>>
ProcRest == <<uid, pdeath, sigkill, session, placed, dropFailed>>
Queues   == <<ulQ, hoQ, prQ, pipeB>>
Env      == <<hist, budget>>

(***************************************************************************)
(* Derived predicates                                                      *)
(***************************************************************************)
Alive(p)  == pc[p] \notin {"none", "dead"}
AliveSet  == {p \in Procs : Alive(p)}
\* a pending fatal signal is delivered before any further user code runs;
\* (sd-pam) has SIGTERM blocked for sigwait(), the payload may handle it
NoFatal(p) == ~sigkill[p] /\ (p = "P" \/ ~sigterm[p])
Exists(p) == Alive(p) \/ p \in unreaped          \* /proc/$PID still exists
Zombies   == {p \in unreaped : parent[p] = Mgr}   \* what waitid(P_ALL) may return
Payload   == IF PIDNS THEN "C" ELSE "E"           \* the process that execve()s

InQueue(q, p) == \E i \in DOMAIN q : q[i] = p

\* The readable sources of the manager's event loop.
Ready(ev) ==
    CASE ev = "user_lookup" -> ulQ # <<>>
      [] ev = "pidref"      -> prQ # <<>>
      [] ev = "handoff"     -> hoQ # <<>>
      [] ev = "exec_fd"     -> execFdSrc /\ (pipeB # <<>> \/ pipeW = {})
      [] ev = "sigchld"     -> sigchldDefer
      [] ev = "signals"     -> sigPending
      [] ev = "cg_inotify"  -> cgInotify
      [] ev = "cg_empty"    -> cgEmptyQ
      [] ev = "timer"       -> timerFired /\ timerArmed

\* sd_event_dispatch(): the pending source with the lowest priority number
Top(ev) == Ready(ev) /\ \A e \in Events : Ready(e) => Prio[e] >= Prio[ev]

(***************************************************************************)
(* The Service state machine, as functions on a record of its fields.     *)
(* A record also carries the signals the manager sends (unit_kill_context) *)
(***************************************************************************)
MgrRec == [state |-> state, result |-> result, main |-> mainPid, job |-> job,
           timer |-> timerArmed, execFd |-> execFdSrc, hot |-> hot,
           watched |-> watched, term |-> {}, kill |-> {}]

Sticky(r, f) == IF r.result = "success" THEN f ELSE r.result

\* SERVICE_STATE_WITH_MAIN_PROCESS(), SERVICE_EXITED/DEAD/FAILED are not in it
WithMain(st) == st \in {"start", "running", "stop_sigterm", "stop_sigkill",
                        "final_sigterm", "final_sigkill"}
Inactive(st) == st \in {"dead", "failed"}
Active(st)   == st \in {"running", "exited"}

\* service_set_state() and the JOB_START rule of unit_notify()/unit_process_job():
\* an active state finishes the job as done; a job still running when the unit
\* turns inactive without ever having been active finishes as done, or as
\* failed if the unit is failed.
SetState(r, st) ==
    [r EXCEPT !.state = st,
              !.job = IF r.job # "running" THEN r.job
                      ELSE IF Active(st) \/ st = "dead" THEN "done"
                      ELSE IF st = "failed" THEN "failed"
                      ELSE "running",
              !.main = IF WithMain(st) THEN r.main ELSE "none",
              !.watched = IF Inactive(st) THEN {}
                          ELSE IF WithMain(st) THEN r.watched ELSE r.watched \ {r.main},
              !.execFd = IF st = "start" THEN r.execFd ELSE FALSE,
              !.timer = IF st = "start" THEN r.timer ELSE FALSE]

\* unit_kill_context(): the main pid if it still exists (kill() succeeds on a
\* zombie), and the cgroup members except main for KillMode=control-group, or
\* for the SIGKILL operation of KillMode=mixed
KillTargets(r, op) ==
    LET main == IF r.main # "none" /\ Exists(r.main) THEN {r.main} ELSE {}
        cg   == IF KillMode = "control-group" \/ op = "kill"
                THEN AliveSet \ {r.main} ELSE {}
    IN main \cup cg

EnterDead(r, f) ==
    LET r1 == [r EXCEPT !.result = Sticky(r, f)]
    IN SetState(r1, IF r1.result = "success" THEN "dead" ELSE "failed")

RECURSIVE EnterSignal(_, _, _), EnterStopPost(_, _)

\* service_enter_signal(): if nothing was signalled, fall through to the next
\* stage right away (SendSIGKILL=yes)
EnterSignal(r, st, f) ==
    LET r1 == [r EXCEPT !.result = Sticky(r, f)]
        op == IF st \in {"stop_sigkill", "final_sigkill"} THEN "kill" ELSE "terminate"
        tg == KillTargets(r1, op)
    IN IF tg # {}
       THEN [SetState(r1, st) EXCEPT !.term = IF op = "terminate" THEN tg ELSE {},
                                     !.kill = IF op = "kill" THEN tg ELSE {}]
       ELSE CASE st = "stop_sigterm"  -> EnterSignal(r1, "stop_sigkill", "success")
              [] st = "stop_sigkill"  -> EnterStopPost(r1, "success")
              [] st = "final_sigterm" -> EnterSignal(r1, "final_sigkill", "success")
              [] st = "final_sigkill" -> EnterDead(r1, "success")

\* service_enter_stop_post(): no ExecStopPost=
EnterStopPost(r, f) == EnterSignal([r EXCEPT !.result = Sticky(r, f)], "final_sigterm", "success")

\* service_enter_stop(): no ExecStop=
EnterStop(r, f) == EnterSignal([r EXCEPT !.result = Sticky(r, f)], "stop_sigterm", "success")

\* main_pid_good() > 0: the pid is known and not yet reaped
ServiceGood(r) == r.main # "none"

EnterRunning(r, f) ==
    LET r1 == [r EXCEPT !.result = Sticky(r, f)]
    IN IF r1.result # "success" THEN EnterSignal(r1, "stop_sigterm", f)
       ELSE IF ServiceGood(r1) THEN SetState(r1, "running")
       ELSE IF RemainAfterExit THEN SetState(r1, "exited")
       ELSE EnterStop(r1, "success")

\* service_enter_start_post(): no ExecStartPost=
EnterStartPost(r) == EnterRunning(r, "success")

\* is_clean_exit(): EXIT_CLEAN_DAEMON also accepts SIGTERM; oneshot uses EXIT_CLEAN_COMMAND
Clean(code, st) == IF code = "exited" THEN st = 0 ELSE Type # "oneshot" /\ st = "TERM"
Failure(code, st) == IF Clean(code, st) THEN "success"
                     ELSE IF code = "exited" THEN "exit-code" ELSE "signal"

\* service_sigchld_event() for s->main_pid
MainExit(r, code, st) ==
    LET f  == Failure(code, st)
        r1 == [r EXCEPT !.execFd = FALSE, !.main = "none", !.result = Sticky(r, f)]
    IN CASE r.state = "start" ->
                IF Type = "oneshot"
                THEN IF f = "success" THEN EnterStartPost(r1)
                     ELSE EnterSignal(r1, "stop_sigterm", f)
                ELSE EnterRunning(r1, f)            \* SERVICE_EXEC falls through to SERVICE_RUNNING
         [] r.state = "running" -> EnterRunning(r1, f)
         [] r.state \in {"stop_sigterm", "stop_sigkill"} -> EnterStopPost(r1, f)
         [] r.state \in {"final_sigterm", "final_sigkill"} -> EnterDead(r1, f)

\* service_notify_cgroup_empty_event(); main_pid_good() <= 0 is r.main = "none"
CgEmpty(r) ==
    CASE r.state = "running" -> EnterRunning(r, "success")
      [] r.state \in {"stop_sigterm", "stop_sigkill"} ->
             IF r.main = "none" THEN EnterStopPost(r, "success") ELSE r
      [] r.state \in {"final_sigterm", "final_sigkill"} ->
             IF r.main = "none" THEN EnterDead(r, "success") ELSE r
      [] OTHER -> r

\* Write a record back and deliver the signals it carries
Apply(r) ==
    /\ state' = r.state /\ result' = r.result /\ mainPid' = r.main /\ job' = r.job
    /\ timerArmed' = r.timer /\ execFdSrc' = r.execFd /\ hot' = r.hot
    /\ watched' = r.watched
    /\ timerFired' = IF r.timer THEN timerFired ELSE FALSE
    /\ sigterm' = [q \in Procs |-> sigterm[q] \/ q \in r.term]
    /\ sigkill' = [q \in Procs |-> sigkill[q] \/ q \in r.kill]

(***************************************************************************)
(* The kernel: a process dies                                              *)
(***************************************************************************)
\* exit(): a zombie for its parent; children are reparented to the reaper,
\* PR_SET_PDEATHSIG fires if the dying parent may kill the child
\* (kill_ok_by_cred(): root, or the same uid), a reparented zombie is
\* announced to the reaper, cgroup.events flips when the last process leaves.
Die(p, code, st) ==
    /\ pc' = [pc EXCEPT ![p] = "dead"]
    /\ exitst' = [exitst EXCEPT ![p] = [code |-> code, status |-> st]]
    /\ unreaped' = unreaped \cup {p}
    /\ pipeW' = pipeW \ {p}
    /\ parent' = [q \in Procs |-> IF parent[q] = p THEN Mgr ELSE parent[q]]
    /\ sigterm' = [q \in Procs |-> sigterm[q] \/
                       (q # p /\ Alive(q) /\ parent[q] = p /\ pdeath[q] /\
                        (uid[p] = "root" \/ uid[p] = uid[q]))]
    /\ sigPending' = (sigPending \/ parent[p] = Mgr \/ \E q \in unreaped : parent[q] = p)
    /\ cgInotify' = (cgInotify \/ AliveSet \ {p} = {})

Advance(p, nx) ==
    /\ pc' = [pc EXCEPT ![p] = nx]
    /\ UNCHANGED <<exitst, unreaped, pipeW, parent, sigterm, sigPending, cgInotify>>

(***************************************************************************)
(* exec_invoke() in the executor (E, or C after the pid namespace fork)    *)
(***************************************************************************)
ExecFail(p, code) ==
    /\ Die(p, "exited", code)
    /\ UNCHANGED <<ProcRest, Queues, Env, MgrAll>>

\* the fd shuffling, signal mask reset, close_remaining_fds(), setsid()
InitPhase(p) ==
    /\ pc[p] = "init"
    /\ \/ Advance(p, "creds") /\ UNCHANGED <<ProcRest, Queues, Env, MgrAll>>
       \/ ExecFail(p, EXIT_FDS)

\* get_user_creds() and send_user_lookup()
Creds(p) ==
    /\ pc[p] = "creds"
    /\ \/ /\ Advance(p, "setup")
          /\ ulQ' = IF User THEN Append(ulQ, p) ELSE ulQ
          /\ UNCHANGED <<ProcRest, hoQ, prQ, pipeB, Env, MgrAll>>
       \/ ExecFail(p, EXIT_USER)

\* cg_attach(), stdio, scheduling, exec directories, credentials, keyring
Setup(p) ==
    /\ pc[p] = "setup"
    /\ \/ Advance(p, "pam") /\ UNCHANGED <<ProcRest, Queues, Env, MgrAll>>
       \/ ExecFail(p, EXIT_CGROUP)

\* setup_pam(): pam_open_session(), then the fork of (sd-pam), which
\* inherits every fd including exec_fd
Pam(p) ==
    /\ pc[p] = "pam"
    /\ IF ~PAM
       THEN Advance(p, "ns") /\ UNCHANGED <<ProcRest, Queues, Env, MgrAll>>
       ELSE \/ ExecFail(p, EXIT_PAM)
            \/ /\ session' = "open"
               /\ pc' = [pc EXCEPT ![p] = "pamsync", !["P"] = "closefd"]
               /\ parent' = [parent EXCEPT !["P"] = p]
               /\ pipeW' = IF Type = "exec" THEN pipeW \cup {"P"} ELSE pipeW
               /\ uid' = [uid EXCEPT !["P"] = uid[p]]
               /\ UNCHANGED <<exitst, unreaped, sigterm, sigPending, cgInotify,
                              pdeath, sigkill, placed, dropFailed, Queues, Env, MgrAll>>

\* barrier_place_and_sync(): wait for barrier_place() of the child, or for
\* the pipe HUP of a child that is gone
PamSync(p) ==
    /\ pc[p] = "pamsync"
    /\ ~BARRIER \/ placed \/ ~Alive("P")
    /\ Advance(p, "ns")
    /\ UNCHANGED <<ProcRest, Queues, Env, MgrAll>>

\* setup_private_pids(): pidref_safe_fork(FORK_NEW_PIDNS|FORK_DETACH), the
\* child is a child of the manager from birth, the parent sends the child's
\* pidref to the manager ...
NsFork(p) ==
    /\ p = "E"
    /\ pc' = [pc EXCEPT !["E"] = "nsexit", !["C"] = "sandbox"]
    /\ parent' = [parent EXCEPT !["C"] = Mgr]
    /\ pipeW' = IF Type # "exec" THEN pipeW
                ELSE IF FIX_PIDNS_PARENT_CLOSES_EXEC_FD THEN (pipeW \ {"E"}) \cup {"C"}
                ELSE pipeW \cup {"C"}
    /\ prQ' = Append(prQ, "E")
    /\ uid' = [uid EXCEPT !["C"] = uid["E"]]
    /\ UNCHANGED <<exitst, unreaped, sigterm, sigPending, cgInotify, pdeath, sigkill,
                   session, placed, dropFailed, ulQ, hoQ, pipeB, Env, MgrAll>>

\* ... and _exit(EXIT_SUCCESS)s.  Children of the parent, (sd-pam) among
\* them, are reparented and get their PR_SET_PDEATHSIG.
NsExit(p) ==
    /\ pc[p] = "nsexit"
    /\ Die(p, "exited", 0)
    /\ UNCHANGED <<ProcRest, Queues, Env, MgrAll>>

Ns(p) ==
    /\ pc[p] = "ns"
    /\ IF ~PIDNS
       THEN Advance(p, "sandbox") /\ UNCHANGED <<ProcRest, Queues, Env, MgrAll>>
       ELSE ExecFail(p, EXIT_NAMESPACE) \/ NsFork(p)

\* the second user lookup is folded into the first; capabilities,
\* apply_root_directory(), enforce_user(), seccomp
Sandbox(p) ==
    /\ pc[p] = "sandbox"
    /\ \/ /\ Advance(p, "hot")
          /\ uid' = [uid EXCEPT ![p] = IF User THEN "user" ELSE "root"]
          /\ UNCHANGED <<pdeath, sigkill, session, placed, dropFailed, Queues, Env, MgrAll>>
       \/ ExecFail(p, EXIT_SECCOMP)

\* exec_fd_mark_hot(true)
Hot(p) ==
    /\ pc[p] = "hot"
    /\ Advance(p, "handoff")
    /\ pipeB' = IF Type = "exec" THEN Append(pipeB, 1) ELSE pipeB
    /\ UNCHANGED <<ProcRest, ulQ, hoQ, prQ, Env, MgrAll>>

\* send_handoff_timestamp()
Handoff(p) ==
    /\ pc[p] = "handoff"
    /\ Advance(p, "execve")
    /\ hoQ' = Append(hoQ, p)
    /\ UNCHANGED <<ProcRest, ulQ, prQ, pipeB, Env, MgrAll>>

\* fexecve_or_execve(): O_CLOEXEC closes exec_fd; on failure
\* exec_fd_mark_hot(false) and EXIT_EXEC
Execve(p) ==
    /\ pc[p] = "execve"
    /\ \/ /\ pc' = [pc EXCEPT ![p] = "payload"]
          /\ pipeW' = pipeW \ {p}
          /\ hist' = [hist EXCEPT !.execd = TRUE]
          /\ UNCHANGED <<exitst, unreaped, parent, sigterm, sigPending, cgInotify,
                         ProcRest, Queues, budget, MgrAll>>
       \/ /\ pipeB' = IF FIX_COLD_MARK /\ Type = "exec" THEN Append(pipeB, 0) ELSE pipeB
          /\ Die(p, "exited", EXIT_EXEC)
          /\ UNCHANGED <<ProcRest, ulQ, hoQ, prQ, Env, MgrAll>>

\* the payload exits on its own, possibly from a SIGTERM handler
PayloadExit(p, st) ==
    /\ pc[p] = "payload"
    /\ ~sigkill[p]
    /\ st \in PayloadStatuses
    /\ Die(p, "exited", st)
    /\ UNCHANGED <<ProcRest, Queues, Env, MgrAll>>

\* a pending fatal signal takes effect; (sd-pam) blocks SIGTERM and consumes
\* it with sigwait(), so only SIGKILL kills it here
Killed(p) ==
    /\ Alive(p)
    /\ sigkill[p] \/ (sigterm[p] /\ p # "P")
    /\ Die(p, "killed", IF sigkill[p] THEN "KILL" ELSE "TERM")
    /\ UNCHANGED <<ProcRest, Queues, Env, MgrAll>>

ExecStep(p) ==
    /\ NoFatal(p)
    /\ \/ InitPhase(p) \/ Creds(p) \/ Setup(p) \/ Pam(p) \/ PamSync(p) \/ Ns(p)
       \/ NsExit(p) \/ Sandbox(p) \/ Hot(p) \/ Handoff(p) \/ Execve(p)

(***************************************************************************)
(* The (sd-pam) child of setup_pam()                                       *)
(***************************************************************************)
PamStep(nx) ==
    /\ pc' = [pc EXCEPT !["P"] = nx]
    /\ UNCHANGED <<exitst, unreaped, parent, sigPending, cgInotify, Env, MgrAll>>

\* close_many(fds) and safe_close(exec_fd)
PCloseFd ==
    /\ pc["P"] = "closefd"
    /\ PamStep("drop")
    /\ pipeW' = IF FIX_PAM_CLOSES_EXEC_FD THEN pipeW \ {"P"} ELSE pipeW
    /\ UNCHANGED <<sigterm, ProcRest, Queues>>

\* fully_set_uid_gid(): a failure is only logged
PDrop ==
    /\ pc["P"] = "drop"
    /\ PamStep("prctl")
    /\ \/ /\ uid' = [uid EXCEPT !["P"] = IF User THEN "user" ELSE "root"]
          /\ dropFailed' = FALSE
       \/ /\ PamDropMayFail /\ User
          /\ dropFailed' = TRUE
          /\ UNCHANGED uid
    /\ UNCHANGED <<sigterm, pipeW, pdeath, sigkill, session, placed, Queues>>

\* prctl(PR_SET_PDEATHSIG, SIGTERM)
PPrctl ==
    /\ pc["P"] = "prctl"
    /\ PamStep("place")
    /\ pdeath' = [pdeath EXCEPT !["P"] = TRUE]
    /\ UNCHANGED <<sigterm, pipeW, uid, sigkill, session, placed, dropFailed, Queues>>

\* barrier_place()
PPlace ==
    /\ pc["P"] = "place"
    /\ PamStep("check")
    /\ placed' = TRUE
    /\ UNCHANGED <<sigterm, pipeW, uid, pdeath, sigkill, session, dropFailed, Queues>>

\* if (getppid() == parent_pid) sigwait(SIGTERM)
PCheck ==
    /\ pc["P"] = "check"
    /\ PamStep(IF ~FIX_PPID_CHECK \/ parent["P"] # Mgr THEN "wait" ELSE "close")
    /\ UNCHANGED <<sigterm, pipeW, ProcRest, Queues>>

\* sigwait() returns
PWait ==
    /\ pc["P"] = "wait"
    /\ sigterm["P"]
    /\ sigterm' = [sigterm EXCEPT !["P"] = FALSE]
    /\ PamStep(IF PAM_WAITS_FOR_PARENT /\ parent["P"] # Mgr THEN "wait" ELSE "close")
    /\ UNCHANGED <<pipeW, ProcRest, Queues>>

\* if (getppid() != parent_pid) pam_close_session_and_delete_credentials()
PClose ==
    /\ pc["P"] = "close"
    /\ PamStep("exit")
    /\ session' = IF parent["P"] = Mgr THEN "closed" ELSE session
    /\ UNCHANGED <<sigterm, pipeW, uid, pdeath, sigkill, placed, dropFailed, Queues>>

\* pam_end(PAM_DATA_SILENT); _exit(0)
PExit ==
    /\ pc["P"] = "exit"
    /\ Die("P", "exited", 0)
    /\ UNCHANGED <<ProcRest, Queues, Env, MgrAll>>

PamProc ==
    /\ NoFatal("P")
    /\ PCloseFd \/ PDrop \/ PPrctl \/ PPlace \/ PCheck \/ PWait \/ PClose \/ PExit

(***************************************************************************)
(* The manager's event loop, one dispatched source per step                *)
(***************************************************************************)
KeepMgr == UNCHANGED <<state, result, mainPid, job, timerArmed, execFdSrc, hot,
                       watched, timerFired, sigterm, sigkill>>

\* manager_dispatch_user_lookup_fd() -> unit_notify_user_lookup(); the unit
\* is found by the name in the datagram, dead or not
DispatchUserLookup ==
    /\ Top("user_lookup")
    /\ ulQ' = Tail(ulQ)
    /\ uidKnown' = TRUE
    /\ hist' = [hist EXCEPT !.uidLate = @ \/ Inactive(state)]
    /\ KeepMgr
    /\ UNCHANGED <<handoffRec, mainStatus, sigchldDefer, sigPending, cgInotify, cgEmptyQ,
                   pc, uid, pdeath, parent, exitst, unreaped, pipeW, pipeB, hoQ, prQ,
                   session, placed, dropFailed, budget>>

\* manager_dispatch_pidref_transport_fd() -> service_notify_pidref(): the
\* parent must still exist to be pinned, and must be the main pid
DispatchPidref ==
    /\ Top("pidref")
    /\ LET par == Head(prQ) IN
       /\ prQ' = Tail(prQ)
       /\ IF Exists(par) /\ mainPid = par
          THEN /\ mainPid' = "C"
               /\ watched' = (watched \ {par}) \cup {"C"}
          ELSE UNCHANGED <<mainPid, watched>>
    /\ UNCHANGED <<state, result, job, timerArmed, execFdSrc, hot, timerFired, sigterm,
                   sigkill, uidKnown, handoffRec, mainStatus, sigchldDefer, sigPending,
                   cgInotify, cgEmptyQ, pc, uid, pdeath, parent, exitst, unreaped, pipeW,
                   pipeB, ulQ, hoQ, session, placed, dropFailed, Env>>

\* manager_dispatch_handoff_timestamp_fd() -> service_handoff_timestamp():
\* recorded only for the current main (or control) pid
DispatchHandoff ==
    /\ Top("handoff")
    /\ LET s == Head(hoQ) IN
       /\ hoQ' = Tail(hoQ)
       /\ IF s = mainPid
          THEN handoffRec' = TRUE /\ UNCHANGED hist
          ELSE hist' = [hist EXCEPT !.handoffLost = TRUE] /\ UNCHANGED handoffRec
    /\ KeepMgr
    /\ UNCHANGED <<uidKnown, mainStatus, sigchldDefer, sigPending, cgInotify, cgEmptyQ,
                   pc, uid, pdeath, parent, exitst, unreaped, pipeW, pipeB, ulQ, prQ,
                   session, placed, dropFailed, budget>>

\* service_dispatch_exec_io(): read every byte, the last one is the new hot
\* flag; then EOF, if the write ends are all gone, drops the source and, if
\* hot and still Type=exec in SERVICE_START, starts the service
DispatchExecFd ==
    /\ Top("exec_fd")
    /\ LET lastHot == IF pipeB = <<>> THEN hot ELSE pipeB[Len(pipeB)] = 1
           r0 == [MgrRec EXCEPT !.hot = lastHot]
           r1 == [r0 EXCEPT !.execFd = FALSE, !.hot = FALSE]
       IN /\ pipeB' = <<>>
          /\ IF pipeW = {}
             THEN Apply(IF lastHot /\ Type = "exec" /\ state = "start"
                        THEN EnterStartPost(r1) ELSE r1)
             ELSE Apply(r0)
    /\ UNCHANGED <<uidKnown, handoffRec, mainStatus, sigchldDefer, sigPending, cgInotify,
                   cgEmptyQ, pc, uid, pdeath, parent, exitst, unreaped, pipeW, ulQ, hoQ,
                   prQ, session, placed, dropFailed, Env>>

\* manager_dispatch_signal_fd(): SIGCHLD enables the deferred reaper
DispatchSignals ==
    /\ Top("signals")
    /\ sigPending' = FALSE
    /\ sigchldDefer' = TRUE
    /\ KeepMgr
    /\ UNCHANGED <<uidKnown, handoffRec, mainStatus, cgInotify, cgEmptyQ, pc, uid, pdeath,
                   parent, exitst, unreaped, pipeW, Queues, session, placed, dropFailed, Env>>

\* manager_dispatch_sigchld(): waitid(P_ALL, WNOWAIT) picks any zombie, the
\* unit is found through the cgroup or watch_pids, unit_unwatch_pidref(),
\* service_sigchld_event(), then the reap.  A message from the process that
\* is still queued, or an exec_fd event the handler drops on the floor, is
\* recorded as lost.
Reap(z) ==
    /\ unreaped' = unreaped \ {z}
    /\ hist' = [hist EXCEPT !.lost = @ \/ InQueue(ulQ, z) \/ InQueue(hoQ, z)
                                       \/ InQueue(prQ, z)
                                       \/ (z = mainPid /\ Ready("exec_fd"))]
    /\ LET r0 == [MgrRec EXCEPT !.watched = watched \ {z}] IN
       IF z = mainPid
       THEN Apply(MainExit(r0, exitst[z].code, exitst[z].status)) /\ mainStatus' = exitst[z]
       ELSE Apply(r0) /\ UNCHANGED mainStatus

DispatchSigchld ==
    /\ Top("sigchld")
    /\ IF Zombies = {}
       THEN /\ sigchldDefer' = FALSE
            /\ KeepMgr
            /\ UNCHANGED <<mainStatus, unreaped, hist>>
       ELSE /\ \E z \in Zombies : Reap(z)
            /\ UNCHANGED sigchldDefer
    /\ UNCHANGED <<uidKnown, handoffRec, sigPending, cgInotify, cgEmptyQ, pc, uid, pdeath,
                   parent, exitst, pipeW, Queues, session, placed, dropFailed, budget>>

\* on_cgroup_inotify_event() -> unit_check_cgroup_events(): re-read
\* "populated", queue or dequeue the unit
DispatchCgInotify ==
    /\ Top("cg_inotify")
    /\ cgInotify' = FALSE
    /\ cgEmptyQ' = (AliveSet = {})
    /\ KeepMgr
    /\ UNCHANGED <<uidKnown, handoffRec, mainStatus, sigchldDefer, sigPending, pc, uid,
                   pdeath, parent, exitst, unreaped, pipeW, Queues, session, placed,
                   dropFailed, Env>>

\* on_cgroup_empty_event(): an inactive unit prunes, an active one is told
DispatchCgEmpty ==
    /\ Top("cg_empty")
    /\ cgEmptyQ' = FALSE
    /\ Apply(IF Inactive(state) THEN MgrRec ELSE CgEmpty(MgrRec))
    /\ UNCHANGED <<uidKnown, handoffRec, mainStatus, sigchldDefer, sigPending, cgInotify,
                   pc, uid, pdeath, parent, exitst, unreaped, pipeW, Queues, session,
                   placed, dropFailed, Env>>

\* service_dispatch_timer() in SERVICE_START, TimeoutStartFailureMode=terminate
DispatchTimer ==
    /\ Top("timer")
    /\ Apply(EnterSignal(MgrRec, "stop_sigterm", "timeout"))
    /\ UNCHANGED <<uidKnown, handoffRec, mainStatus, sigchldDefer, sigPending, cgInotify,
                   cgEmptyQ, pc, uid, pdeath, parent, exitst, unreaped, pipeW, Queues,
                   session, placed, dropFailed, Env>>

ManagerStep ==
    \/ DispatchUserLookup \/ DispatchPidref \/ DispatchHandoff \/ DispatchExecFd
    \/ DispatchSignals \/ DispatchSigchld \/ DispatchCgInotify \/ DispatchCgEmpty
    \/ DispatchTimer

(***************************************************************************)
(* The environment                                                         *)
(***************************************************************************)
\* systemctl stop: service_stop() -> service_enter_signal(SERVICE_STOP_SIGTERM)
\* or service_enter_stop(); the stop job replaces a running start job
StopRequest ==
    /\ budget.stop > 0
    /\ state \in {"start", "running", "exited"}
    /\ budget' = [budget EXCEPT !.stop = @ - 1]
    /\ LET r == EnterSignal(MgrRec, "stop_sigterm", "success") IN
       Apply([r EXCEPT !.job = IF job = "running" THEN "canceled" ELSE r.job])
    /\ UNCHANGED <<uidKnown, handoffRec, mainStatus, sigchldDefer, sigPending, cgInotify,
                   cgEmptyQ, pc, uid, pdeath, parent, exitst, unreaped, pipeW, Queues,
                   session, placed, dropFailed, hist>>

\* TimeoutStartSec= expires
TimeoutFire ==
    /\ budget.timeout > 0
    /\ timerArmed /\ ~timerFired
    /\ timerFired' = TRUE
    /\ budget' = [budget EXCEPT !.timeout = @ - 1]
    /\ UNCHANGED <<state, result, mainPid, job, timerArmed, execFdSrc, hot, watched,
                   uidKnown, handoffRec, mainStatus, sigchldDefer, sigPending, cgInotify,
                   cgEmptyQ, pc, uid, pdeath, parent, exitst, unreaped, pipeW, Queues,
                   sigterm, sigkill, session, placed, dropFailed, hist>>

(***************************************************************************)
(* The specification                                                       *)
(***************************************************************************)
Init ==
    /\ state = IF Type = "simple" THEN "running" ELSE "start"
    /\ job = IF Type = "simple" THEN "done" ELSE "running"
    /\ result = "success"
    /\ mainPid = "E"
    /\ watched = {"E"}
    /\ timerArmed = (Type # "simple")
    /\ timerFired = FALSE
    /\ execFdSrc = (Type = "exec")
    /\ hot = FALSE
    /\ uidKnown = FALSE
    /\ handoffRec = FALSE
    /\ mainStatus = [code |-> "none", status |-> 0]
    /\ sigchldDefer = FALSE
    /\ sigPending = FALSE
    /\ cgInotify = TRUE          \* "populated" went 0 -> 1 with the spawn
    /\ cgEmptyQ = FALSE
    /\ pc = [p \in Procs |-> IF p = "E" THEN "init" ELSE "none"]
    /\ uid = [p \in Procs |-> "root"]
    /\ pdeath = [p \in Procs |-> FALSE]
    /\ parent = [p \in Procs |-> Mgr]
    /\ exitst = [p \in Procs |-> [code |-> "none", status |-> 0]]
    /\ unreaped = {}
    /\ pipeW = IF Type = "exec" THEN {"E"} ELSE {}
    /\ pipeB = <<>>
    /\ ulQ = <<>> /\ hoQ = <<>> /\ prQ = <<>>
    /\ sigterm = [p \in Procs |-> FALSE]
    /\ sigkill = [p \in Procs |-> FALSE]
    /\ session = "none"
    /\ placed = FALSE
    /\ dropFailed = FALSE
    /\ hist = [execd |-> FALSE, lost |-> FALSE, uidLate |-> FALSE, handoffLost |-> FALSE]
    /\ budget = [stop |-> StopBudget, timeout |-> TimeoutBudget]

Next ==
    \/ \E p \in {"E", "C"} : ExecStep(p) \/ Killed(p) \/ \E st \in {0, 1} : PayloadExit(p, st)
    \/ PamProc \/ Killed("P")
    \/ ManagerStep
    \/ StopRequest \/ TimeoutFire

\* Every step a process or the manager takes on its own is fair; whether a
\* phase fails, a payload exits, a stop or a timeout happens is left to
\* the environment.
Fairness ==
    /\ WF_vars(ManagerStep)
    /\ \A p \in {"E", "C"} : WF_vars(ExecStep(p)) /\ WF_vars(Killed(p))
    /\ WF_vars(PamProc) /\ WF_vars(Killed("P"))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ state \in States
    /\ result \in Results
    /\ mainPid \in Procs \cup {"none"}
    /\ job \in {"running", "done", "failed", "canceled"}
    /\ pc \in [Procs -> PCs]
    /\ uid \in [Procs -> {"root", "user"}]
    /\ parent \in [Procs -> Procs \cup {Mgr}]
    /\ pipeW \subseteq Procs
    /\ unreaped \subseteq Procs
    /\ session \in {"none", "open", "closed"}
    /\ \A i \in DOMAIN pipeB : pipeB[i] \in {0, 1}

\* A message the executor sent, or an exec_fd byte or EOF, is never still
\* unread when the manager reaps the process that produced it: every source
\* the executor writes to is dispatched before its SIGCHLD.
NoLostMessage == ~hist.lost

\* The handoff timestamp of the payload is attributed to the main process.
HandoffRecorded == ~hist.handoffLost

\* The uid/gid resolution never arrives after the unit went inactive.
NoLateUserLookup == ~hist.uidLate

\* Type=exec: the unit is active only after execve() succeeded, and its
\* start job is done only then.
ActiveImpliesExeced == (Type = "exec" /\ Active(state)) => hist.execd
JobDoneImpliesExeced == (Type = "exec" /\ job = "done") => hist.execd

\* Type=exec: a payload that execve()d and failed right away is
\* "succeeded to start, then failed", not "failed to start": the start job
\* does not fail unless a stop or a timeout intervened.
JobFailedImpliesNotExeced ==
    (Type = "exec" /\ job = "failed" /\ budget.stop = StopBudget /\ budget.timeout = TimeoutBudget)
    => ~hist.execd

\* The manager signals a live executor or payload only on a stop request
\* or a timeout; in particular the pid namespace parent exiting after the
\* pidref handoff never makes the manager kill the child.  (A parent that
\* is about to _exit() anyway may be caught by a cgroup kill the child's
\* own failure triggered.)
ExecutorSignaledOnlyOnRequest ==
    (\E p \in {"E", "C"} : Alive(p) /\ pc[p] # "nsexit" /\ (sigterm[p] \/ sigkill[p]))
    => budget.stop < StopBudget \/ budget.timeout < TimeoutBudget

\* Once main_pid is the pid namespace child it stays that, and a main pid is
\* a process the manager has a claim on.
MainPidIsTracked == mainPid # "none" => mainPid \in watched

\* An inactive unit has no process left.
InactiveImpliesNoProcess == Inactive(state) => AliveSet = {}

\* While the manager waits in a stop state for its main process, that
\* process has been sent the stop signal.
StopReachesMain ==
    (state \in {"stop_sigterm", "stop_sigkill"} /\ mainPid # "none" /\ Alive(mainPid))
    => sigterm[mainPid] \/ sigkill[mainPid]

\* The PAM session is closed only after the process that runs the payload is gone.
SessionNotClosedWhilePayloadAlive == session = "closed" => \A p \in {"E", "C"} : ~Alive(p)

\* Liveness: Type=exec, once execve() succeeded the start job completes.
JobCompletes == (Type = "exec") => [](hist.execd => <>(job # "running"))

\* Liveness: once the process that owns the PAM session is gone, the
\* session is closed.
SessionEventuallyClosed ==
    [](session = "open" /\ ~Alive("E") /\ ~Alive("C") => <>(session = "closed"))

=============================================================================
