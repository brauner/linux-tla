--------------------------- MODULE CorePattern ---------------------------
(***************************************************************************)
(* coredump: parse a snapshot of core_pattern                              *)
(*                                                                         *)
(* proc_dostring_coredump() used to let proc_dostring() write straight     *)
(* into core_pattern[] while coredump_parse() read it in pieces: the first *)
(* byte picks the mode (pipe, socket or file), the rest is consumed later. *)
(* A pattern is reduced to those two pieces here.  The unfixed writer      *)
(* stores them one after the other, the unfixed reader loads them one     *)
(* after the other.  With the fix both sides copy under core_pattern_lock. *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS FIX_SNAPSHOT,
          Old,          \* e.g. [mode |-> "pipe", path |-> "/usr/bin/helper"]
          New           \* e.g. [mode |-> "file", path |-> "/tmp/core.%p"]

VARIABLES
    pattern,    \* core_pattern[] as stored: mode and path
    writer,     \* "idle", "mid", "done"
    reader,     \* "idle", "mid", "done"
    seen_mode,  \* what coredump_parse() read first
    seen_path   \* what it consumed later

vars == <<pattern, writer, reader, seen_mode, seen_path>>

Init ==
    /\ pattern = Old
    /\ writer = "idle"
    /\ reader = "idle"
    /\ seen_mode = "none"
    /\ seen_path = "none"

\* sysctl write: byte by byte without the fix, whole under the lock with it
WriterStart ==
    /\ writer = "idle"
    /\ IF FIX_SNAPSHOT
       THEN pattern' = New /\ writer' = "done"
       ELSE pattern' = [pattern EXCEPT !.mode = New.mode] /\ writer' = "mid"
    /\ UNCHANGED <<reader, seen_mode, seen_path>>

WriterFinish ==
    /\ writer = "mid"
    /\ pattern' = [pattern EXCEPT !.path = New.path]
    /\ writer' = "done"
    /\ UNCHANGED <<reader, seen_mode, seen_path>>

\* coredump_parse(): a snapshot with the fix, two loads without it
ReaderStart ==
    /\ reader = "idle"
    /\ IF FIX_SNAPSHOT
       THEN seen_mode' = pattern.mode /\ seen_path' = pattern.path /\ reader' = "done"
       ELSE seen_mode' = pattern.mode /\ seen_path' = seen_path /\ reader' = "mid"
    /\ UNCHANGED <<pattern, writer>>

ReaderFinish ==
    /\ reader = "mid"
    /\ seen_path' = pattern.path
    /\ reader' = "done"
    /\ UNCHANGED <<pattern, writer, seen_mode>>

Next == WriterStart \/ WriterFinish \/ ReaderStart \/ ReaderFinish

Spec == Init /\ [][Next]_vars

\* The dump is parsed from a pattern that was published as a whole
ConsistentParse ==
    reader = "done" =>
        [mode |-> seen_mode, path |-> seen_path] \in {Old, New}

=============================================================================
