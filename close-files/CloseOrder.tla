---------------------------- MODULE CloseOrder ----------------------------
(***************************************************************************)
(* The order in which a dying descriptor table closes its files, against  *)
(* releases and flushes that wait for another file of the same table.     *)
(*                                                                         *)
(* Three disciplines close the same table:                                 *)
(*   deferred    before "fs: make close_files() synchronous": the walk     *)
(*               runs ->flush() for fd 1..N and queues every final put on *)
(*               task work; task work is a LIFO list, so the ->release()s  *)
(*               run N..1 after the walk.                                  *)
(*   ascending   d99d38540bf0 / 6ee9e7d4fbc8 / 64cdb497e727 as merged:    *)
(*               ->flush() and ->release() inline for fd 1..N.             *)
(*   descending  "fs: close files from the highest descriptor down":       *)
(*               ->flush() and ->release() inline for fd N..1.             *)
(*                                                                         *)
(* A dependency relWaits[i] = {j} says the release of fd i only completes *)
(* once fd j has been released (the pipe end whose pipe_release() needs   *)
(* the mutex a peer's splice holds until the socket j gives EOF, the tap  *)
(* device the AF_LLC socket references, ...).  flushWaits[i] = {j} says   *)
(* the same for ->flush() of fd i (a self-served FUSE file whose flush     *)
(* only returns once the /dev/fuse fd j is released and the connection    *)
(* aborted).  TLC picks every dependency pattern over N descriptors.       *)
(*                                                                         *)
(* A discipline is stuck when it reaches a step whose dependencies are    *)
(* not met: the exiting task sleeps in that ->flush() or ->release()       *)
(* forever.                                                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N

Fds == 1..N
Disciplines == {"deferred", "ascending", "descending"}

\* One flush and one release per fd, 2N steps per discipline
Steps(d) ==
    CASE d = "deferred" ->
            [k \in 1..N |-> <<"flush", k>>]
            \o [k \in 1..N |-> <<"release", N + 1 - k>>]
      [] d = "ascending" ->
            [k \in 1..(2 * N) |->
                IF k % 2 = 1 THEN <<"flush", (k + 1) \div 2>>
                             ELSE <<"release", k \div 2>>]
      [] d = "descending" ->
            [k \in 1..(2 * N) |->
                IF k % 2 = 1 THEN <<"flush", N + 1 - (k + 1) \div 2>>
                             ELSE <<"release", N + 1 - k \div 2>>]

VARIABLES relWaits, flushWaits, pos, released

vars == <<relWaits, flushWaits, pos, released>>

Deps == {w \in [Fds -> SUBSET Fds] : \A i \in Fds : i \notin w[i]}

Init ==
    /\ relWaits \in Deps
    /\ flushWaits \in Deps
    /\ pos = [d \in Disciplines |-> 1]
    /\ released = [d \in Disciplines |-> {}]

Done(d) == pos[d] > 2 * N

NeedsOf(d) ==
    LET s == Steps(d)[pos[d]]
    IN IF s[1] = "flush" THEN flushWaits[s[2]] ELSE relWaits[s[2]]

Stuck(d) == ~Done(d) /\ ~(NeedsOf(d) \subseteq released[d])

Settled(d) == Done(d) \/ Stuck(d)

Step(d) ==
    /\ ~Done(d)
    /\ NeedsOf(d) \subseteq released[d]
    /\ LET s == Steps(d)[pos[d]]
       IN released' = [released EXCEPT ![d] = IF s[1] = "release" THEN @ \cup {s[2]} ELSE @]
    /\ pos' = [pos EXCEPT ![d] = @ + 1]
    /\ UNCHANGED <<relWaits, flushWaits>>

Next == \E d \in Disciplines : Step(d)

Spec == Init /\ [][Next]_vars

NoFlushDeps == \A i \in Fds : flushWaits[i] = {}

\* Without flush dependencies the descending walk hangs exactly where the
\* deferred puts hung: the fix restores the old order.
DescendingMatchesDeferredOnReleases ==
    (NoFlushDeps /\ Settled("descending") /\ Settled("deferred"))
        => (Stuck("descending") <=> Stuck("deferred"))

\* With flush dependencies the descending walk never hangs where the
\* deferred puts did not: synchronous close only removes hangs here.
DescendingNoWorseThanDeferred ==
    (Settled("descending") /\ Settled("deferred"))
        => (Stuck("descending") => Stuck("deferred"))

\* The merged ascending walk hangs where the old order did not: a lower
\* descriptor whose release waits for a higher one, the pipe end before
\* the socket.
AscendingNoWorseThanDeferred ==
    (Settled("ascending") /\ Settled("deferred"))
        => (Stuck("ascending") => Stuck("deferred"))

\* It is not the old order in the other direction either: a flush that
\* waits for a lower descriptor's release now completes.
AscendingMatchesDeferred ==
    (Settled("ascending") /\ Settled("deferred"))
        => (Stuck("ascending") <=> Stuck("deferred"))

\* The descending walk is not identical to the old order either: a flush
\* that waits for a higher descriptor's release now completes.
DescendingMatchesDeferred ==
    (Settled("descending") /\ Settled("deferred"))
        => (Stuck("descending") <=> Stuck("deferred"))

=============================================================================
