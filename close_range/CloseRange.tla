----------------------------- MODULE CloseRange -----------------------------
(***************************************************************************)
(* Every table of up to NWords words against every range and every flag   *)
(* combination: one table per initial state, one range per step.  The     *)
(* invariants quantify over the flags and over whether the table is shared *)
(* and print the combination that fails.                                   *)
(***************************************************************************)
EXTENDS FdTable

CONSTANTS NWords, FlagSet

VARIABLES table, range, pc
vars == <<table, range, pc>>

Tables == UNION {Table(W * k) : k \in 1..NWords}
Ranges == RangesUpTo(W * NWords)
Cases == {c \in FlagSet \X BOOLEAN : c[1].unshare \/ ~c[2]}  \* shared only matters with CLOSE_RANGE_UNSHARE

Init == table \in Tables /\ range = NoRange /\ pc = "pick"
Pick == pc = "pick" /\ \E r \in Ranges : range' = r /\ pc' = "check" /\ UNCHANGED table
Next == Pick
Spec == Init /\ [][Next]_vars

Check(P(_, _)) ==
    pc = "check" => \A c \in Cases :
        P(c[1], c[2]) \/ Print(<<"fails for", c[1], "shared", c[2]>>, FALSE)

(* the table the caller ends up with is what the flags mean *)
RefinesP(f, s) == SameTable(CloseRange(table, range, f, s).cur, Meaning(table, range, f, s))
Refines == Check(RefinesP)

(* a clone's bitmaps are consistent: no file without an open bit, full_fds_bits exact *)
CloneOKP(f, s) ==
    LET res == CloseRange(table, range, f, s)
    IN res.unshared => /\ SlotsOK(res.clone) /\ FullBitsOK(res.clone)
                       /\ res.clone.max % W = 0 /\ res.clone.max >= NR_OPEN_DEFAULT
CloneOK == Check(CloneOKP)

(* dup_fd() takes a reference only on descriptors that make it into the clone *)
NoRefOnDroppedP(f, s) ==
    LET res == CloseRange(table, range, f, s)
    IN res.unshared => res.drop.null \/
                       \A d \in res.clone.refs : ~Selected(table, res.drop, f, d)
NoRefOnDropped == Check(NoRefOnDroppedP)

(* the clone reaches the last descriptor it carries over and nothing more *)
SizedP(f, s) ==
    LET res == CloseRange(table, range, f, s)
    IN res.unshared => SizedExactly(table, res.drop, f, res.clone)
Sized == Check(SizedP)

=============================================================================
