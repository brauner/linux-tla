---------------------------- MODULE TtyHangup ----------------------------
(***************************************************************************)
(* exit: hang up the tty before closing the files                         *)
(*                                                                         *)
(* A session leader holds the last open of its controlling tty; a job in  *)
(* the foreground process group closed its own tty descriptors but is     *)
(* still in the session.  The leader exits.                               *)
(*                                                                         *)
(*   files_first   as merged (d99d38540bf0): exit_files() -> tty_release() *)
(*                 drops tty->count to 0, session_clear_tty() clears       *)
(*                 signal->tty for the session without a signal, and       *)
(*                 disassociate_ctty(1) afterwards finds no tty            *)
(*   hangup_first  the fix, and the order the deferred puts gave before:   *)
(*                 disassociate_ctty(1) -> tty_vhangup_session() ->        *)
(*                 __tty_hangup(exit_session = 1) sends SIGHUP to the      *)
(*                 foreground group while the file is still open           *)
(*                                                                         *)
(* For a pty the master's open keeps the slave's count above zero, so     *)
(* session_clear_tty() never runs from the leader's release and           *)
(* disassociate_ctty() takes the kill_pgrp() branch in either order.      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS ORDER, PTY
ASSUME ORDER \in {"files_first", "hangup_first"}
ASSUME PTY \in BOOLEAN

VARIABLES leader,      \* "exit", "step2", "done"
          count,       \* tty->count
          sessionTty,  \* signal->tty of the session members points at the tty
          pgrp,        \* tty->ctrl.pgrp is set
          jobSighup    \* the foreground job received SIGHUP

vars == <<leader, count, sessionTty, pgrp, jobSighup>>

Init ==
    /\ leader = "exit"
    /\ count = IF PTY THEN 2 ELSE 1     \* the master's open on a pty
    /\ sessionTty = TRUE
    /\ pgrp = TRUE
    /\ jobSighup = FALSE

\* disassociate_ctty(1)
Disassociate ==
    /\ IF sessionTty
       THEN /\ jobSighup' = (jobSighup \/ pgrp)   \* tty_signal_session_leader()'s kill_pgrp(),
                                                  \* or kill_pgrp() for a pty
            /\ sessionTty' = FALSE
            /\ pgrp' = FALSE
       ELSE \* get_current_tty() is NULL and tty_old_pgrp was never set
            UNCHANGED <<jobSighup, sessionTty, pgrp>>
    /\ UNCHANGED count

\* exit_files() -> tty_release()
ReleaseTty ==
    /\ count' = count - 1
    /\ IF count = 1
       THEN sessionTty' = FALSE                   \* session_clear_tty(), no signal
       ELSE UNCHANGED sessionTty
    /\ UNCHANGED <<pgrp, jobSighup>>

Step1 ==
    /\ leader = "exit"
    /\ IF ORDER = "files_first" THEN ReleaseTty ELSE Disassociate
    /\ leader' = "step2"

Step2 ==
    /\ leader = "step2"
    /\ IF ORDER = "files_first" THEN Disassociate ELSE ReleaseTty
    /\ leader' = "done"

Next == Step1 \/ Step2

Spec == Init /\ [][Next]_vars

\* The foreground job is hung up when its session leader exits
JobHungUp == leader = "done" => jobSighup

=============================================================================
