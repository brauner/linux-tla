---------------------------- MODULE MntWriters ----------------------------
(***************************************************************************)
(* WRITE_HOLD: mnt_get_write_access() against mnt_make_readonly() and      *)
(* sb_prepare_remount_readonly() on one mount.                             *)
(*                                                                         *)
(* Writers (mnt_get_write_access()): this_cpu_inc(mnt_writers), smp_mb(),  *)
(* spin while WRITE_HOLD, smp_rmb(), mnt_is_readonly() (s_readonly_remount *)
(* first, then MNT_READONLY / SB_RDONLY), on failure this_cpu_dec().  Then *)
(* the write, then mnt_put_write_access().                                 *)
(*                                                                         *)
(* The holder, under mount_lock (read_seqlock_excl): mnt_hold_writers()    *)
(* sets WRITE_HOLD, smp_mb(), sums the per-CPU counts; with no writer it   *)
(* sets MNT_READONLY (mnt_make_readonly()) or s_readonly_remount           *)
(* (sb_prepare_remount_readonly(), the remount then sets SB_RDONLY and     *)
(* sb_end_ro_state_change() clears s_readonly_remount), then smp_wmb() and *)
(* the clear of WRITE_HOLD (mnt_unhold_writers()).  WRITE_HOLD lives in    *)
(* the low bit of ->mnt_pprev_for_sb and is set and cleared in one         *)
(* mount_lock scope (3371fa2f2713).                                        *)
(*                                                                         *)
(* Memory model: TSO with per-task store buffers as in MntPut.tla.  The    *)
(* smp_rmb()/smp_wmb() pairs are no-ops under TSO (loads and stores each   *)
(* stay in order); they are the business of the herd7 litmus tests.       *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
    Writers,      \* the writer tasks
    WCpu,         \* [Writers -> CPUs]
    NCPU,
    HMODE,        \* "mnt": mnt_make_readonly(); "sb": sb_prepare_remount_readonly() + remount
    FIX_MB_GET,   \* smp_mb() after this_cpu_inc() in mnt_get_write_access()
    FIX_MB_HOLD,  \* smp_mb() after setting WRITE_HOLD in mnt_hold_writers()
    FIX_SBRO      \* mnt_is_readonly() tests s_readonly_remount (d7439fb1f433)

H == "H"
Tasks == Writers \cup {H}
NoTask == "none"
CPUs == 1..NCPU
ASSUME H \notin Writers

VARIABLES
    cntv,    \* [CPUs -> Int]: mnt_writers as the other CPUs see it
    holdv,   \* WRITE_HOLD as the other CPUs see it
    rov,     \* MNT_READONLY as the other CPUs see it
    sbrov,   \* s_readonly_remount as the other CPUs see it
    sbrdv,   \* SB_RDONLY as the other CPUs see it
    lockv,   \* mount_lock's spinlock: holder or NoTask
    buf,     \* [Tasks -> Seq(store)]
    pc,      \* [Tasks -> label]
    acc,     \* the holder's running sum
    ci,      \* the holder's next CPU
    result   \* the holder's result: "", "ok", "busy"

vars == <<cntv, holdv, rov, sbrov, sbrdv, lockv, buf, pc, acc, ci, result>>

(* ---- the store buffers -------------------------------------------------- *)

StCnt(c, d) == [f |-> "cnt", c |-> c, d |-> d]
St(f, v)    == [f |-> f, v |-> v]

Vis == [cntv |-> cntv, holdv |-> holdv, rov |-> rov, sbrov |-> sbrov, sbrdv |-> sbrdv, lockv |-> lockv]
Apply(s, e) ==
    CASE e.f = "cnt"  -> [s EXCEPT !.cntv[e.c] = @ + e.d]
      [] e.f = "hold" -> [s EXCEPT !.holdv = e.v]
      [] e.f = "ro"   -> [s EXCEPT !.rov = e.v]
      [] e.f = "sbro" -> [s EXCEPT !.sbrov = e.v]
      [] e.f = "sbrd" -> [s EXCEPT !.sbrdv = e.v]
      [] e.f = "lock" -> [s EXCEPT !.lockv = e.v]
RECURSIVE ApplyAll(_, _)
ApplyAll(s, es) == IF es = <<>> THEN s ELSE ApplyAll(Apply(s, Head(es)), Tail(es))
RECURSIVE SumD(_)
SumD(s) == IF s = <<>> THEN 0 ELSE Head(s) + SumD(Tail(s))
Buffered(t, c) == SumD([i \in 1..Len(buf[t]) |->
                        IF buf[t][i].f = "cnt" /\ buf[t][i].c = c THEN buf[t][i].d ELSE 0])
SeenCnt(t, c) == cntv[c] + Buffered(t, c)
\* the holder's own view of the flags (store forwarding)
Seen(t, f, cur) == LET ss == SelectSeq(buf[t], LAMBDA e : e.f = f) IN IF ss = <<>> THEN cur ELSE ss[Len(ss)].v

Push(t, e) == buf' = [buf EXCEPT ![t] = Append(@, e)]
Push2(t, e1, e2) == buf' = [buf EXCEPT ![t] = Append(Append(@, e1), e2)]
Empty(t) == buf[t] = <<>>
Drained(t, extra) ==
    LET r == ApplyAll(Vis, buf[t] \o extra)
    IN /\ cntv' = r.cntv /\ holdv' = r.holdv /\ rov' = r.rov /\ sbrov' = r.sbrov /\ sbrdv' = r.sbrdv
       /\ lockv' = r.lockv
       /\ buf' = [buf EXCEPT ![t] = <<>>]
UnchangedVis == UNCHANGED <<cntv, holdv, rov, sbrov, sbrdv, lockv>>

Init ==
    /\ cntv = [c \in CPUs |-> 0]
    /\ holdv = FALSE /\ rov = FALSE /\ sbrov = FALSE /\ sbrdv = FALSE
    /\ lockv = NoTask
    /\ buf = [t \in Tasks |-> <<>>]
    /\ pc = [t \in Tasks |-> IF t = H THEN "h_lock" ELSE "w_inc"]
    /\ acc = 0 /\ ci = 1
    /\ result = ""

Flush(t) ==
    /\ ~Empty(t)
    /\ LET r == Apply(Vis, Head(buf[t]))
       IN cntv' = r.cntv /\ holdv' = r.holdv /\ rov' = r.rov /\ sbrov' = r.sbrov /\ sbrdv' = r.sbrdv /\ lockv' = r.lockv
    /\ buf' = [buf EXCEPT ![t] = Tail(@)]
    /\ UNCHANGED <<pc, acc, ci, result>>

(* ---- the writer --------------------------------------------------------- *)

\* this_cpu_inc(mnt_writers)
WInc(w) ==
    /\ pc[w] = "w_inc"
    /\ Push(w, StCnt(WCpu[w], 1))
    /\ pc' = [pc EXCEPT ![w] = "w_mb"]
    /\ UnchangedVis /\ UNCHANGED <<acc, ci, result>>
\* smp_mb()
WMb(w) ==
    /\ pc[w] = "w_mb"
    /\ FIX_MB_GET => Empty(w)
    /\ pc' = [pc EXCEPT ![w] = "w_spin"]
    /\ UnchangedVis /\ UNCHANGED <<buf, acc, ci, result>>
\* while (WRITE_HOLD) cpu_relax(): the step waits for the bit to clear
WSpin(w) ==
    /\ pc[w] = "w_spin" /\ ~holdv
    /\ pc' = [pc EXCEPT ![w] = "w_check"]
    /\ UnchangedVis /\ UNCHANGED <<buf, acc, ci, result>>
\* smp_rmb(); mnt_is_readonly(): s_readonly_remount, then the flags
WCheck(w) ==
    /\ pc[w] = "w_check"
    /\ LET readonly == (FIX_SBRO /\ sbrov) \/ rov \/ sbrdv
       IN IF readonly
          THEN Push(w, StCnt(WCpu[w], -1)) /\ pc' = [pc EXCEPT ![w] = "done"]
          ELSE UNCHANGED buf /\ pc' = [pc EXCEPT ![w] = "w_active"]
    /\ UnchangedVis /\ UNCHANGED <<acc, ci, result>>
\* the write is done: mnt_put_write_access()
WPut(w) ==
    /\ pc[w] = "w_active"
    /\ Push(w, StCnt(WCpu[w], -1))
    /\ pc' = [pc EXCEPT ![w] = "done"]
    /\ UnchangedVis /\ UNCHANGED <<acc, ci, result>>
Write(w) == WInc(w) \/ WMb(w) \/ WSpin(w) \/ WCheck(w) \/ WPut(w)

(* ---- the holder ----------------------------------------------------------- *)

\* read_seqlock_excl(&mount_lock): the atomic RMW drains the buffer
HLock ==
    /\ pc[H] = "h_lock" /\ lockv = NoTask /\ Empty(H)
    /\ lockv' = H
    /\ pc' = [pc EXCEPT ![H] = "h_hold"]
    /\ UNCHANGED <<cntv, holdv, rov, sbrov, sbrdv, buf, acc, ci, result>>
\* set_write_hold()
HHold ==
    /\ pc[H] = "h_hold"
    /\ Push(H, St("hold", TRUE))
    /\ pc' = [pc EXCEPT ![H] = "h_mb"]
    /\ UnchangedVis /\ UNCHANGED <<acc, ci, result>>
\* smp_mb()
HMb ==
    /\ pc[H] = "h_mb"
    /\ FIX_MB_HOLD => Empty(H)
    /\ acc' = 0 /\ ci' = 1
    /\ pc' = [pc EXCEPT ![H] = "h_sum"]
    /\ UnchangedVis /\ UNCHANGED <<buf, result>>
\* mnt_get_writers(): one CPU per step
HSum ==
    /\ pc[H] = "h_sum"
    /\ IF ci <= NCPU
       THEN acc' = acc + SeenCnt(H, ci) /\ ci' = ci + 1 /\ UNCHANGED pc
       ELSE pc' = [pc EXCEPT ![H] = "h_decide"] /\ UNCHANGED <<acc, ci>>
    /\ UnchangedVis /\ UNCHANGED <<buf, result>>
\* -EBUSY: mnt_unhold_writers(); else MNT_READONLY or s_readonly_remount
\* (smp_wmb() keeps the store order, which TSO gives anyway), then
\* clear_write_hold(); read_sequnlock_excl() lets every store drain
HDecide ==
    /\ pc[H] = "h_decide"
    /\ IF acc > 0
       THEN /\ result' = "busy"
            /\ Drained(H, <<St("hold", FALSE), St("lock", NoTask)>>)
            /\ pc' = [pc EXCEPT ![H] = "done"]
       ELSE /\ result' = "ok"
            /\ IF HMODE = "mnt"
               THEN /\ Drained(H, <<St("ro", TRUE), St("hold", FALSE), St("lock", NoTask)>>)
                    /\ pc' = [pc EXCEPT ![H] = "done"]
               ELSE /\ Drained(H, <<St("sbro", TRUE), St("hold", FALSE), St("lock", NoTask)>>)
                    /\ pc' = [pc EXCEPT ![H] = "h_remount"]
    /\ UNCHANGED <<acc, ci>>
\* the remount proper: SB_RDONLY, then sb_end_ro_state_change()
HRemount ==
    /\ pc[H] = "h_remount"
    /\ Push2(H, St("sbrd", TRUE), St("sbro", FALSE))
    /\ pc' = [pc EXCEPT ![H] = "done"]
    /\ UnchangedVis /\ UNCHANGED <<acc, ci, result>>
Hold == HLock \/ HHold \/ HMb \/ HSum \/ HDecide \/ HRemount

(* ---- the specification ---------------------------------------------------- *)

Settled == \A t \in Tasks : pc[t] = "done" /\ Empty(t)
Next ==
    \/ \E w \in Writers : Write(w)
    \/ Hold
    \/ \E t \in Tasks : Flush(t)
    \/ (Settled /\ UNCHANGED vars)
Spec == Init /\ [][Next]_vars

(* ---- what is checked ------------------------------------------------------- *)

Active == {w \in Writers : pc[w] = "w_active"}

\* nobody writes on a mount that was made read-only: once MNT_READONLY is
\* visible, or s_readonly_remount marks a remount in progress, or SB_RDONLY
\* is visible, no writer holds write access
ReadOnlyOK == (rov \/ sbrov \/ sbrdv) => Active = {}

\* the holder's decision was right: "ok" only with no writer active
DecisionOK == result = "ok" => Active = {}

\* the counts add up: every increment still buffered or visible belongs to
\* a writer between its increment and its decrement
SetToSeqW == CHOOSE s \in [1..Cardinality(Writers) -> Writers] : \A w \in Writers : \E i \in DOMAIN s : s[i] = w
Ledger == SumD([c \in 1..NCPU |-> cntv[c]])
          + SumD([i \in 1..Len(SetToSeqW) |-> SumD([c \in 1..NCPU |-> Buffered(SetToSeqW[i], c)])])
          = Cardinality({w \in Writers : pc[w] \in {"w_mb", "w_spin", "w_check", "w_active"}})

\* WRITE_HOLD is only set while the holder is inside mount_lock (3371fa2f2713)
HoldUnderLock == holdv => lockv = H

=============================================================================
