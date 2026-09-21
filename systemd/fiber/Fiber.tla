---------------------------- MODULE Fiber ----------------------------
(***************************************************************************)
(* systemd's fiber runtime: src/libsystemd/sd-future/{fiber.c,sd-future.c},*)
(* sd-event/event-future.c and the sd-event dispatch rules they rely on.   *)
(*                                                                         *)
(* One event loop, a few fibers and the futures they create.  Fibers run   *)
(* arbitrary programs drawn from a small set of operations (yield, wait    *)
(* for an io/timer/bus future, spawn a child, await a fiber, cancel one,   *)
(* request exit, timeout scopes, bare suspend) with _cleanup_-style        *)
(* unwinding: every future a fiber owns is released with                   *)
(* sd_future_cancel_wait_unref() when the scope that created it ends.      *)
(* The loop dispatches one source per iteration in sd-event's order        *)
(* (priority, then the iteration the source became pending in, ties        *)
(* arbitrary); kernel events fire nondeterministically.  Every candidate   *)
(* fix is a switch, off by default, so the configurations can show both    *)
(* the trace and the proof.                                                *)
(*                                                                         *)
(* Model of the C code as of systemd v262-rc3 (e96ff3b5b9).                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
  FiberOrder,        \* sequence of all fiber ids, in allocation order
  TopLevel,          \* fibers main creates before it runs the loop
  FloatingTop,       \* those of TopLevel created with ret=NULL (fire-and-forget)
  ExtOrder,          \* sequence of io/timer/bus future and deadline timer ids, allocation order
  WaitOrder,         \* sequence of wait future ids, allocation order (all ids are distinct strings)
  FiberPrioSeq,      \* priority of each fiber, aligned with FiberOrder
  Budget,            \* operations a fiber may perform before it has to return
  Ops,               \* the operations fibers may use (subset of AllOps)
  MainMayExit,       \* main, or a signal handler, may call sd_event_exit() between iterations
  MainMayCancel,     \* main may sd_future_cancel() a top-level fiber between iterations
  MainCancelMax,     \* … at most this many times in a behavior (0: unbounded; bound it for liveness,
                     \*   an environment that cancels a fiber forever starves everything else)
  ExitOnIdle,        \* sd_event_set_exit_on_idle()
  AllowIgnoreErrors, \* a fiber may ignore a negative return value and carry on
  ChildMayFail,      \* child fibers may return an error
  \* candidate fixes
  FixFreePending,      \* sd_future_free() of a pending future resolves it instead of asserting
  FixCwuLoop,          \* sd_future_cancel_wait_unref() waits until the future is really resolved
  FixExitArmed,        \* every live fiber keeps its exit source armed, so an exiting loop always drives it
  FixRecancel,         \* a cancellation or deadline swallowed while waiting in cancel_wait_unref() is redelivered
  FixStickyError,      \* sd_fiber_resume() of a queued fiber keeps an error result instead of dropping it
  FixNoChildTrampoline,\* a child's completion does not resume its creator
  FixAwaitLoop         \* sleep/io/await re-suspend when woken by an unrelated future

AllOps == {"yield", "ext", "spawn", "spawnfl", "awaitf", "cancel", "exit", "tobegin", "toend", "bare"}

NONE == "none"
MAIN == "main"
CANCEL == "cancel"
OK == 0
CANCELED == -1
ETIME == -2
EFAIL == -3

Range(s) == {s[i] : i \in DOMAIN s}
Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
LexLE(a, b) == a[1] < b[1] \/ (a[1] = b[1] /\ a[2] <= b[2])

FiberIds == Range(FiberOrder)
ExtIds == Range(ExtOrder)
WaitIds == Range(WaitOrder)
Ids == FiberIds \cup ExtIds \cup WaitIds
FiberIndex(g) == CHOOSE i \in DOMAIN FiberOrder : FiberOrder[i] = g
Prio(g) == FiberPrioSeq[FiberIndex(g)]
\* allocation picks the first free id, so that the ids are interchangeable
MinFib(P) == FiberOrder[Min({i \in DOMAIN FiberOrder : FiberOrder[i] \in P})]
MinExt(P) == ExtOrder[Min({i \in DOMAIN ExtOrder : ExtOrder[i] \in P})]
MinWait(P) == WaitOrder[Min({i \in DOMAIN WaitOrder : WaitOrder[i] \in P})]

ASSUME TopLevel \subseteq FiberIds /\ FloatingTop \subseteq TopLevel
ASSUME ExtIds \cap WaitIds = {} /\ ExtIds \cap FiberIds = {} /\ WaitIds \cap FiberIds = {}
ASSUME Ops \subseteq AllOps
ASSUME Len(FiberPrioSeq) = Len(FiberOrder)

VARIABLE st

(***************************************************************************)
(* Records                                                                 *)
(***************************************************************************)

\* A future.  kind: "fiber" (the id is the fiber's), "ext" (io/timer/bus, resolves 0),
\* "deadline" (SD_FIBER_TIMEOUT timer, resolves -ETIME), "wait" (sd_future_new_wait), "free".
\* cb is the fiber resumed on resolution (fiber_resume_trampoline), held says whether the
\* handle reference (the creator's _cleanup_ variable, or main's) is still held.
FreeFut == [kind |-> "free", state |-> "resolved", result |-> 0, cb |-> NONE, waiters |-> {},
            target |-> NONE, srcOn |-> FALSE, fired |-> FALSE, obsIter |-> -1, prio |-> 0,
            held |-> FALSE, fireResult |-> 0, dropped |-> FALSE]
FiberFut(cb, held) ==
  [FreeFut EXCEPT !.kind = "fiber", !.state = "pending", !.cb = cb, !.held = held]
ExtFut(kind, cb, prio, fr) ==
  [FreeFut EXCEPT !.kind = kind, !.state = "pending", !.cb = cb, !.srcOn = TRUE,
                  !.prio = prio, !.held = TRUE, !.fireResult = fr]
WaitFut(cb, target) ==
  [FreeFut EXCEPT !.kind = "wait", !.state = "pending", !.cb = cb, !.target = target, !.held = TRUE]

\* A fiber.  state follows FiberState in fiber.c plus "none" (slot unused) and "freed".
\* cstack is the stack of futures the fiber's scopes own (cleaned up LIFO), mode/unwindTo/
\* after/retval describe an unwinding in progress, cont/opkind/opfut/optarget/cwuWait what
\* the fiber was doing when it switched out, wakeVal/wakeSrc how it was resumed.
NoFib == [state |-> "none", result |-> 0, deferOn |-> FALSE, deferIter |-> 0, exitOn |-> FALSE,
          floating |-> FALSE, creator |-> NONE, prio |-> 0, budget |-> 0, cstack |-> <<>>,
          mode |-> "normal", unwindTo |-> 0, after |-> "return", retval |-> 0,
          cont |-> "none", opkind |-> NONE, opfut |-> NONE, optarget |-> NONE, cwuWait |-> NONE,
          wakeVal |-> 0, wakeSrc |-> NONE, pendingVal |-> 0, swallowedVal |-> 0]
NewFib(creator, prio, fl, exitOn, iter) ==
  [NoFib EXCEPT !.state = "initial", !.deferOn = TRUE, !.deferIter = iter, !.exitOn = exitOn,
                !.floating = fl, !.creator = creator, !.prio = prio, !.budget = Budget]

Alive(S, g) == S.fib[g].state \notin {"none", "freed"}
Crash(S, why) == IF S.crash = "" THEN [S EXCEPT !.crash = why] ELSE S

\* sd_future n_ref: the handle, the floating self-reference, and one per wait future on it
Refs(S, x) == (IF S.fut[x].held THEN 1 ELSE 0)
            + (IF x \in FiberIds /\ S.fib[x].floating THEN 1 ELSE 0)
            + Cardinality({w \in WaitIds : S.fut[w].kind = "wait" /\ S.fut[w].target = x})

(***************************************************************************)
(* fiber.c / sd-future.c primitives, as state transformers                 *)
(***************************************************************************)

\* sd_event_source_set_enabled(fiber_current_event_source(g), SD_EVENT_ONESHOT):
\* the exit source while the loop is dispatching exit sources, the defer source otherwise
Arm(S, g) == [S EXCEPT !.fib[g].deferOn = @ \/ ~S.exiting,
                       !.fib[g].exitOn = @ \/ S.exiting \/ FixExitArmed]

\* sd_fiber_resume(g, v), reached through fiber_resume_trampoline() from future src.
\* Only a suspended fiber is resumed; everything else drops the result.
Resume(S, g, v, src) ==
  IF S.fut[g].kind # "fiber" THEN Crash(S, "resume-of-freed-fiber")
  ELSE LET fr == S.fib[g] IN
       IF fr.state = "suspended" THEN
          Arm([S EXCEPT !.fib[g].state = "ready", !.fib[g].result = v, !.fib[g].wakeSrc = src], g)
       ELSE IF FixStickyError /\ fr.state = "ready" /\ S.phase # g /\ fr.result >= 0 /\ v < 0 THEN
          [S EXCEPT !.fib[g].result = v, !.fib[g].wakeSrc = src]
       ELSE IF src \in ExtIds /\ S.fut[src].kind = "deadline" /\ fr.state = "ready" THEN
          [S EXCEPT !.fut[src].dropped = TRUE]
       ELSE S

ResolveWaiter(S, w, v) ==
  LET S1 == [S EXCEPT !.fut[w].state = "resolved", !.fut[w].result = v] IN
  IF S.fut[w].cb # NONE THEN Resume(S1, S.fut[w].cb, v, w) ELSE S1

RECURSIVE ResolveWaiters(_, _, _)
ResolveWaiters(S, W, v) ==
  IF W = {} THEN S
  ELSE LET w == CHOOSE w \in W : TRUE IN ResolveWaiters(ResolveWaiter(S, w, v), W \ {w}, v)

\* sd_future_resolve(x, v): the callback first, then every wait future on x
ResolveFut(S, x, v) ==
  IF S.fut[x].state # "pending" THEN S
  ELSE LET fr == S.fut[x]
           S1 == [S EXCEPT !.fut[x].state = "resolved", !.fut[x].result = v, !.fut[x].waiters = {}]
           S2 == IF fr.cb # NONE THEN Resume(S1, fr.cb, v, x) ELSE S1
       IN ResolveWaiters(S2, fr.waiters, v)

\* sd_future_free() of a fiber or io/timer/deadline future whose last reference went away.
\* As written it resolves a pending future first, which takes a reference on an object
\* with n_ref == 0 (sd_future_ref() asserts).  fiber_free() then insists the stack is unwound.
FreeOther(S, x) ==
  IF S.fut[x].state = "pending" /\ ~FixFreePending THEN Crash(S, "free-of-pending-future")
  ELSE LET S1 == ResolveFut(S, x, CANCELED) IN
       IF x \in FiberIds THEN
          LET S2 == IF S1.fib[x].state \in {"initial", "completed"} THEN S1
                    ELSE Crash(S1, "fiber-free-with-live-stack")
          IN [S2 EXCEPT !.fut[x] = FreeFut,
                        !.fib[x] = [S2.fib[x] EXCEPT !.state = "freed", !.deferOn = FALSE,
                                                     !.exitOn = FALSE, !.floating = FALSE]]
       ELSE [S1 EXCEPT !.fut[x] = FreeFut]

MaybeFreeOther(S, x) == IF Refs(S, x) = 0 THEN FreeOther(S, x) ELSE S

\* wait_future_free(): leave the target's waiter set, drop the reference on the target
FreeWait(S, w) ==
  LET t == S.fut[w].target
      S1 == [S EXCEPT !.fut[t].waiters = @ \ {w}, !.fut[w] = FreeFut]
  IN MaybeFreeOther(S1, t)

\* sd_future_unref() of the handle
Unref(S, x) ==
  LET S1 == [S EXCEPT !.fut[x].held = FALSE] IN
  IF Refs(S1, x) > 0 THEN S1
  ELSE IF S1.fut[x].kind = "wait" THEN FreeWait(S1, x) ELSE FreeOther(S1, x)

\* fiber_resolve(): sources gone, the floating self-reference dropped after the resolution
CompleteFiber(S, g, v) ==
  LET S1 == [S EXCEPT !.fib[g].state = "completed", !.fib[g].result = v,
                      !.fib[g].deferOn = FALSE, !.fib[g].exitOn = FALSE]
      S2 == ResolveFut(S1, g, v)
      S3 == [S2 EXCEPT !.fib[g].floating = FALSE]
  IN MaybeFreeOther(S3, g)

\* sd_future_cancel() on a fiber future (fiber_cancel()); the caller is never g itself
Cancel(S, g) ==
  LET fr == S.fib[g] IN
  IF S.fut[g].kind # "fiber" \/ S.fut[g].state = "resolved" \/ fr.state \in {"completed", "cancelled"}
  THEN S
  ELSE IF fr.state = "initial" THEN CompleteFiber(S, g, CANCELED)
  ELSE [S EXCEPT !.fib[g].state = "cancelled",
                 !.fib[g].deferOn = @ \/ ~S.exiting,
                 !.fib[g].exitOn = @ \/ S.exiting \/ FixExitArmed]

\* io_future_cancel() / time_future_cancel() / wait_future_cancel(): synchronous resolution
CancelNonFiber(S, x) ==
  IF S.fut[x].state # "pending" THEN S
  ELSE IF S.fut[x].kind = "wait" THEN
     ResolveFut([S EXCEPT !.fut[S.fut[x].target].waiters = @ \ {x}], x, CANCELED)
  ELSE ResolveFut([S EXCEPT !.fut[x].srcOn = FALSE, !.fut[x].fired = FALSE, !.fut[x].obsIter = -1],
                  x, CANCELED)

\* sd_future_cancel_wait_unref() when nothing has to be waited for
CwuSync(S, x) == Unref(CancelNonFiber(S, x), x)

\* The tail of fiber_run() after the fiber switched out with state ns
SwitchOut(S, f, ns) ==
  LET S1 == [S EXCEPT !.fib[f].state = ns, !.fib[f].wakeSrc = NONE]
      S2 == CASE ns = "completed" -> CompleteFiber(S1, f, S.fib[f].retval)
              [] ns \in {"ready", "cancelled"} -> Arm(S1, f)
              [] OTHER -> S1
  IN [S2 EXCEPT !.phase = "idle", !.exiting = FALSE]

\* fiber_run() entering f: what the pending fiber_swap() returns
\* As written the -ECANCELED return leaves a stashed resume value in place (it surfaces from
\* a later yield); FixRecancel consumes it and keeps an error for the next wait.
Enter(S, f, viaExit) ==
  LET fr == S.fib[f]
      canc == fr.state = "cancelled"
      keep == canc /\ FixRecancel /\ fr.result < 0 /\ fr.pendingVal = 0
  IN [S EXCEPT !.phase = f, !.exiting = viaExit,
               !.fib[f].wakeVal = IF canc THEN CANCELED ELSE fr.result,
               !.fib[f].wakeSrc = IF canc THEN CANCEL ELSE fr.wakeSrc,
               !.fib[f].result = IF canc /\ ~FixRecancel THEN fr.result ELSE 0,
               !.fib[f].pendingVal = IF keep THEN fr.result ELSE fr.pendingVal]

(***************************************************************************)
(* The fiber programs                                                      *)
(***************************************************************************)

PopTop(S, f) == [S EXCEPT !.fib[f].cstack = SubSeq(@, 1, Len(@) - 1)]
ClearOp(S, f) == [S EXCEPT !.fib[f].cont = "none", !.fib[f].opkind = NONE,
                           !.fib[f].opfut = NONE, !.fib[f].optarget = NONE]
UnwindTo(S, f, d, after, rv) ==
  [ClearOp(S, f) EXCEPT !.fib[f].mode = "unwind", !.fib[f].unwindTo = d,
                        !.fib[f].after = after, !.fib[f].retval = rv]

\* What a fiber does with an operation's return value: propagate an error by unwinding
\* and returning it, or (if allowed) ignore it and carry on
Decide(S, f, v) ==
  IF v >= 0 THEN {ClearOp(S, f)}
  ELSE {UnwindTo(S, f, 0, "return", v)} \cup (IF AllowIgnoreErrors THEN {ClearOp(S, f)} ELSE {})

Running(f) == st.phase = f
CanOp(f) == Running(f) /\ st.fib[f].mode = "normal" /\ st.fib[f].cont = "none"
Bud(f) == st.fib[f].budget
Spend(S, f) == [S EXCEPT !.fib[f].budget = @ - 1]
FreeExt == {x \in ExtIds : st.fut[x].kind = "free"}
FreeWaitIds == {w \in WaitIds : st.fut[w].kind = "free"}
FreeFibs == {g \in FiberIds : st.fib[g].state = "none"}
Children(f) == {x \in Range(st.fib[f].cstack) : x \in FiberIds}
\* futures a fiber can act on: its owned children, and the top-level fibers main handed it
Handles(f) == Children(f) \cup {t \in TopLevel \ {f} : t \notin FloatingTop /\ st.fut[t].kind = "fiber"}
Deadlines(f) == {x \in Range(st.fib[f].cstack) : x \in ExtIds /\ st.fut[x].kind = "deadline"}
\* a cancellation or deadline swallowed inside cancel_wait_unref(), waiting to be delivered
\* by the next wait (FixRecancel)
Pending(f) == FixRecancel /\ st.fib[f].pendingVal # 0
PendingVal(f) == st.fib[f].pendingVal
Deliver(S, f) == [S EXCEPT !.fib[f].pendingVal = 0]

\* sd_fiber_yield()
OpYield(f) ==
  /\ CanOp(f) /\ "yield" \in Ops /\ Bud(f) > 0
  /\ LET S0 == Spend(st, f) IN
     IF Pending(f) THEN \E T \in Decide(Deliver(S0, f), f, PendingVal(f)) : st' = T
     ELSE st' = SwitchOut([S0 EXCEPT !.fib[f].cont = "op", !.fib[f].opkind = "yield"], f, "ready")

\* sd_fiber_sleep() / sd_fiber_read() / bus_call_suspend(): a future on the loop, then suspend
OpAwaitExt(f) ==
  /\ CanOp(f) /\ "ext" \in Ops /\ Bud(f) > 0
  /\ LET S0 == Spend(st, f) IN
     IF st.exiting THEN \E T \in Decide(S0, f, CANCELED) : st' = T   \* future_new_*() refuses
     ELSE IF Pending(f) THEN \E T \in Decide(Deliver(S0, f), f, PendingVal(f)) : st' = T
     ELSE /\ FreeExt # {}
          /\ LET x == MinExt(FreeExt) IN
             st' = SwitchOut([S0 EXCEPT !.fut[x] = ExtFut("ext", f, st.fib[f].prio, OK),
                                        !.fib[f].cstack = Append(@, x),
                                        !.fib[f].cont = "op", !.fib[f].opkind = "ext",
                                        !.fib[f].opfut = x],
                             f, "suspended")

\* sd_fiber_new() on a fiber: owned (handle kept, cancel_wait_unref at scope end) or floating
OpSpawn(f, fl) ==
  /\ CanOp(f) /\ Bud(f) > 0
  /\ IF fl THEN "spawnfl" \in Ops ELSE "spawn" \in Ops
  /\ LET S0 == Spend(st, f) IN
     IF st.exiting THEN \E T \in Decide(S0, f, CANCELED) : st' = T
     ELSE /\ FreeFibs # {}
          /\ LET g == MinFib(FreeFibs) IN
             st' = [S0 EXCEPT !.fib[g] = NewFib(f, Prio(g), fl, FixExitArmed, st.iter),
                              !.fut[g] = FiberFut(IF FixNoChildTrampoline THEN NONE ELSE f, ~fl),
                              !.fib[f].cstack = IF fl THEN @ ELSE Append(@, g)]

\* sd_fiber_await(g)
OpAwaitFiber(f, g) ==
  /\ CanOp(f) /\ "awaitf" \in Ops /\ Bud(f) > 0 /\ g \in Handles(f)
  /\ LET S0 == Spend(st, f) IN
     IF st.fut[g].state = "resolved" THEN \E T \in Decide(S0, f, st.fut[g].result) : st' = T
     ELSE IF Pending(f) THEN \E T \in Decide(Deliver(S0, f), f, PendingVal(f)) : st' = T
     ELSE /\ FreeWaitIds # {}
          /\ LET w == MinWait(FreeWaitIds) IN
             st' = SwitchOut([S0 EXCEPT !.fut[w] = WaitFut(f, g), !.fut[g].waiters = @ \cup {w},
                                        !.fib[f].cstack = Append(@, w),
                                        !.fib[f].cont = "op", !.fib[f].opkind = "awaitf",
                                        !.fib[f].opfut = w, !.fib[f].optarget = g],
                             f, "suspended")

\* sd_future_cancel(g) from a fiber
OpCancel(f, g) ==
  /\ CanOp(f) /\ "cancel" \in Ops /\ Bud(f) > 0 /\ g \in Handles(f)
  /\ st.fut[g].state = "pending"
  /\ st' = Cancel(Spend(st, f), g)

\* sd_event_exit()
OpExit(f) ==
  /\ CanOp(f) /\ "exit" \in Ops /\ Bud(f) > 0 /\ ~st.exitReq
  /\ st' = [Spend(st, f) EXCEPT !.exitReq = TRUE]

\* SD_FIBER_TIMEOUT() / the start of SD_FIBER_WITH_TIMEOUT(): a deadline timer on the stack
OpTimeoutBegin(f) ==
  /\ CanOp(f) /\ "tobegin" \in Ops /\ Bud(f) > 0
  /\ LET S0 == Spend(st, f) IN
     IF st.exiting THEN st' = S0     \* sd_fiber_timeout() returns NULL: the scope is a no-op
     ELSE /\ FreeExt # {}
          /\ LET x == MinExt(FreeExt) IN
             st' = [S0 EXCEPT !.fut[x] = ExtFut("deadline", f, st.fib[f].prio, ETIME),
                              !.fib[f].cstack = Append(@, x)]

\* the end of an SD_FIBER_WITH_TIMEOUT() block: cleanups down to and including the timer
OpTimeoutEnd(f) ==
  /\ CanOp(f) /\ "toend" \in Ops /\ Bud(f) > 0 /\ Deadlines(f) # {}
  /\ LET cs == st.fib[f].cstack
         p == Max({i \in DOMAIN cs : cs[i] \in Deadlines(f)})
     IN st' = UnwindTo(Spend(st, f), f, p - 1, "block", 0)

\* sd_fiber_suspend() with nothing but a cancellation or a deadline to wake it
OpBare(f) ==
  /\ CanOp(f) /\ "bare" \in Ops /\ Bud(f) > 0
  /\ LET S0 == Spend(st, f) IN
     IF Pending(f) THEN \E T \in Decide(Deliver(S0, f), f, PendingVal(f)) : st' = T
     ELSE st' = SwitchOut([S0 EXCEPT !.fib[f].cont = "op", !.fib[f].opkind = "bare"], f, "suspended")

RetVals(f) == {OK} \cup (IF ChildMayFail /\ st.fib[f].creator # MAIN THEN {EFAIL} ELSE {})
\* return from the fiber function: run the cleanups, then complete
OpReturn(f) ==
  /\ CanOp(f)
  /\ \E rv \in RetVals(f) : st' = UnwindTo(st, f, 0, "return", rv)

\* The fiber was resumed inside an operation: consume the value it was resumed with
ContinueOp(f) ==
  /\ Running(f) /\ st.fib[f].cont = "op"
  /\ LET fr == st.fib[f]
         v == fr.wakeVal
         src == fr.wakeSrc
         \* the future the operation waits for, and whether it has resolved
         own == IF fr.opkind = "ext" THEN fr.opfut ELSE fr.optarget
         ownDone == fr.opkind \in {"ext", "awaitf"} /\ st.fut[own].state = "resolved"
         \* a yield needs no resume at all; everything else must have been woken by its own
         \* future, its cancellation, or a deadline scope it is inside of
         legit == \/ src \in {CANCEL} \cup Deadlines(f)
                  \/ (fr.opkind = "yield" /\ src = NONE)
                  \/ (fr.opkind # "yield" /\ src \in {fr.opfut, fr.optarget})
         \* the flag records a wakeup the fiber's code actually sees
         S0 == IF legit THEN st ELSE [st EXCEPT !.spurious = TRUE]
     IN CASE fr.opkind = "yield" ->
              \* 0, -ECANCELED, or the -ETIME of one of the fiber's own expired deadlines
              LET S1 == IF v \in {OK, CANCELED} \/ (v = ETIME /\ src \in Deadlines(f)) THEN S0
                        ELSE [S0 EXCEPT !.badYield = TRUE]
              IN \E T \in Decide(S1, f, v) : st' = T
          [] fr.opkind \in {"ext", "awaitf"} /\ FixAwaitLoop ->
              \* the wait loop: a cancellation ends it, the own future's resolution ends it
              \* with the own result, an expired deadline scope ends it with -ETIME, any
              \* other wakeup is absorbed by suspending again
              IF src = CANCEL THEN \E T \in Decide(PopTop(CwuSync(st, fr.opfut), f), f, CANCELED) : st' = T
              ELSE IF ownDone THEN \E T \in Decide(PopTop(CwuSync(st, fr.opfut), f), f, st.fut[own].result) : st' = T
              ELSE IF src \in Deadlines(f) THEN \E T \in Decide(PopTop(CwuSync(st, fr.opfut), f), f, v) : st' = T
              ELSE st' = SwitchOut(st, f, "suspended")
          [] fr.opkind \in {"ext", "awaitf"} ->
              \E T \in Decide(PopTop(CwuSync(S0, fr.opfut), f), f, v) : st' = T
          [] OTHER -> \E T \in Decide(S0, f, v) : st' = T

\* The fiber was resumed inside sd_future_cancel_wait_unref(x) (x a fiber future it cancelled)
ContinueCwu(f) ==
  /\ Running(f) /\ st.fib[f].cont = "cwu"
  /\ LET fr == st.fib[f]
         x == fr.optarget
         \* what the wait consumed that the fiber's code should still see: its cancellation,
         \* or the expiry of a deadline scope it is inside of (cancellation wins)
         sw == IF fr.wakeVal = CANCELED \/ fr.swallowedVal = CANCELED THEN CANCELED
               ELSE IF fr.wakeVal = ETIME /\ fr.wakeSrc \in Deadlines(f) THEN ETIME
               ELSE fr.swallowedVal
         S0 == [st EXCEPT !.fib[f].swallowedVal = sw]
     IN IF FixCwuLoop /\ st.fut[x].state = "pending"
        THEN st' = SwitchOut(S0, f, "suspended")
        ELSE LET S1 == IF fr.cwuWait # NONE THEN CwuSync(S0, fr.cwuWait) ELSE S0
                 S2 == PopTop(Unref(S1, x), f)
             IN st' = [S2 EXCEPT !.fib[f].cont = "none", !.fib[f].optarget = NONE,
                                 !.fib[f].cwuWait = NONE, !.fib[f].swallowedVal = 0,
                                 !.fib[f].pendingVal = IF FixRecancel /\ sw # 0 THEN sw ELSE @,
                                 !.lostCancel = @ \/ (sw = CANCELED /\ fr.after = "block" /\ ~FixRecancel)]

\* One cleanup of an unwinding: sd_future_cancel_wait_unref() of the top of the stack
Unwind(f) ==
  /\ Running(f) /\ st.fib[f].mode = "unwind" /\ st.fib[f].cont = "none"
  /\ LET fr == st.fib[f]
         n == Len(fr.cstack)
     IN IF n = fr.unwindTo THEN
           IF fr.after = "return"
           THEN st' = SwitchOut([st EXCEPT !.fib[f].mode = "normal"], f, "completed")
           ELSE st' = [st EXCEPT !.fib[f].mode = "normal"]
        ELSE LET x == fr.cstack[n] IN
           IF x \notin FiberIds \/ st.fut[x].state = "resolved" THEN st' = PopTop(CwuSync(st, x), f)
           ELSE LET S1 == Cancel(st, x) IN
                IF S1.fut[x].state = "resolved" THEN st' = PopTop(Unref(S1, x), f)
                ELSE IF S1.fut[x].cb = f THEN   \* fast path: the child's trampoline wakes us
                   st' = SwitchOut([S1 EXCEPT !.fib[f].cont = "cwu", !.fib[f].optarget = x,
                                              !.fib[f].cwuWait = NONE], f, "suspended")
                ELSE /\ FreeWaitIds # {}      \* slow path: sd_fiber_await()
                     /\ LET w == MinWait(FreeWaitIds) IN
                        st' = SwitchOut([S1 EXCEPT !.fut[w] = WaitFut(f, x),
                                                   !.fut[x].waiters = @ \cup {w},
                                                   !.fib[f].cont = "cwu", !.fib[f].optarget = x,
                                                   !.fib[f].cwuWait = w], f, "suspended")

FiberStep(f) ==
  \/ OpYield(f) \/ OpAwaitExt(f) \/ OpSpawn(f, FALSE) \/ OpSpawn(f, TRUE)
  \/ \E g \in FiberIds : OpAwaitFiber(f, g) \/ OpCancel(f, g)
  \/ OpExit(f) \/ OpTimeoutBegin(f) \/ OpTimeoutEnd(f) \/ OpBare(f) \/ OpReturn(f)
  \/ ContinueOp(f) \/ ContinueCwu(f) \/ Unwind(f)

(***************************************************************************)
(* The event loop                                                          *)
(***************************************************************************)

OnlineDefer(S) == {g \in FiberIds : Alive(S, g) /\ S.fib[g].deferOn}
OnlineExt(S) == {x \in ExtIds : S.fut[x].kind \in {"ext", "deadline"} /\ S.fut[x].srcOn}
\* event_loop_idle(): no enabled source other than exit sources
Idle(S) == OnlineDefer(S) = {} /\ OnlineExt(S) = {}

\* Iteration numbers only matter relative to each other: renumber them densely
Norm(T) ==
  LET aliveF == {g \in FiberIds : Alive(T, g)}
      obsX == {x \in ExtIds : T.fut[x].kind \in {"ext", "deadline"} /\ T.fut[x].obsIter >= 0}
      vals == {T.iter} \cup {T.fib[g].deferIter : g \in aliveF} \cup {T.fut[x].obsIter : x \in obsX}
      R(v) == Cardinality({u \in vals : u < v})
  IN [T EXCEPT !.iter = R(T.iter),
               !.fib = [g \in FiberIds |-> IF g \in aliveF THEN [T.fib[g] EXCEPT !.deferIter = R(@)]
                                                            ELSE T.fib[g]],
               !.fut = [x \in Ids |-> IF x \in obsX THEN [T.fut[x] EXCEPT !.obsIter = R(@)]
                                                    ELSE T.fut[x]]]

\* sd_event_run(): prepare (exit-on-idle, the iteration counter), wait (observe what fired),
\* dispatch one source: dispatch_exit() once exit was requested, else the first pending
\* source by (priority, pending iteration)
Dispatch ==
  /\ st.phase = "idle" /\ ~st.finished
  /\ LET exitNow == st.exitReq \/ (ExitOnIdle /\ Idle(st))
         newIter == st.iter + 1
         S0 == [st EXCEPT !.iter = newIter, !.exitReq = @ \/ exitNow]
     IN IF exitNow THEN
           LET cands == {g \in FiberIds : Alive(st, g) /\ st.fib[g].exitOn} IN
           IF cands = {} THEN st' = [st EXCEPT !.finished = TRUE, !.exitReq = TRUE]
           ELSE \E g \in cands :
                  /\ \A h \in cands : st.fib[g].prio <= st.fib[h].prio
                  /\ LET S1 == [S0 EXCEPT !.fib[g].exitOn = FALSE, !.exiting = TRUE]
                         fr == st.fib[g]
                         \* fiber_on_exit(): cancel first; an already cancelled fiber is run
                         T == IF fr.state = "completed" THEN [S1 EXCEPT !.exiting = FALSE]
                              ELSE IF fr.state # "cancelled" THEN [Cancel(S1, g) EXCEPT !.exiting = FALSE]
                              ELSE Enter(S1, g, TRUE)
                     IN st' = Norm(T)
        ELSE
           LET S1 == [S0 EXCEPT !.fut = [x \in Ids |->
                         IF x \in ExtIds /\ st.fut[x].kind \in {"ext", "deadline"} /\ st.fut[x].srcOn
                            /\ st.fut[x].fired /\ st.fut[x].obsIter < 0
                         THEN [st.fut[x] EXCEPT !.obsIter = newIter] ELSE st.fut[x]]]
               extC == {x \in OnlineExt(S1) : S1.fut[x].obsIter >= 0}
               cands == OnlineDefer(S1) \cup extC
               Key(c) == IF c \in FiberIds THEN <<S1.fib[c].prio, S1.fib[c].deferIter>>
                                            ELSE <<S1.fut[c].prio, S1.fut[c].obsIter>>
           IN /\ cands # {}
              /\ \E c \in cands :
                   /\ \A d \in cands : LexLE(Key(c), Key(d))
                   /\ IF c \in FiberIds THEN
                         LET S2 == [S1 EXCEPT !.fib[c].deferOn = FALSE, !.fib[c].deferIter = newIter]
                             fr == st.fib[c]
                             T == IF fr.state = "completed" THEN S2   \* fiber_run() returns -ESTALE
                                  ELSE IF fr.state \notin {"initial", "ready", "cancelled"}
                                  THEN Crash(S2, "fiber-run-bad-state")
                                  ELSE Enter(S2, c, FALSE)
                         IN st' = Norm(T)
                      ELSE
                         LET S2 == [S1 EXCEPT !.fut[c].srcOn = FALSE, !.fut[c].fired = FALSE,
                                              !.fut[c].obsIter = -1]
                         IN st' = Norm(ResolveFut(S2, c, st.fut[c].fireResult))

\* the kernel: an io/timer/bus event, or a deadline expiring
Fire(x) ==
  /\ st.fut[x].kind \in {"ext", "deadline"} /\ st.fut[x].srcOn /\ ~st.fut[x].fired
  /\ st.fut[x].state = "pending"
  /\ st' = [st EXCEPT !.fut[x].fired = TRUE]

\* main between two sd_event_run() calls, or a signal handler
MainExit ==
  /\ MainMayExit /\ st.phase = "idle" /\ ~st.finished /\ ~st.exitReq
  /\ st' = [st EXCEPT !.exitReq = TRUE]

MainCancel(g) ==
  /\ MainMayCancel /\ st.phase = "idle" /\ ~st.finished
  /\ MainCancelMax = 0 \/ st.mainCancels < MainCancelMax
  /\ g \in TopLevel \ FloatingTop /\ st.fut[g].kind = "fiber" /\ st.fut[g].state = "pending"
  /\ st' = [Cancel(st, g) EXCEPT !.mainCancels = IF MainCancelMax = 0 THEN 0 ELSE @ + 1]

Done == st.finished /\ UNCHANGED st

Init ==
  st = [fib |-> [g \in FiberIds |-> IF g \in TopLevel
                                    THEN NewFib(MAIN, Prio(g), g \in FloatingTop, TRUE, 0)
                                    ELSE NoFib],
        fut |-> [x \in Ids |-> IF x \in TopLevel THEN FiberFut(NONE, x \notin FloatingTop) ELSE FreeFut],
        phase |-> "idle", exiting |-> FALSE, exitReq |-> FALSE, finished |-> FALSE, iter |-> 0,
        mainCancels |-> 0,
        crash |-> "", spurious |-> FALSE, badYield |-> FALSE, lostCancel |-> FALSE]

Next ==
  \/ Dispatch
  \/ \E f \in FiberIds : FiberStep(f)
  \/ \E x \in ExtIds : Fire(x)
  \/ MainExit
  \/ \E g \in FiberIds : MainCancel(g)
  \/ Done

Fairness ==
  /\ WF_st(Dispatch)
  /\ \A f \in FiberIds : WF_st(FiberStep(f))
  /\ \A x \in ExtIds : WF_st(Fire(x))
  /\ WF_st(MainExit)

Spec == Init /\ [][Next]_st /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* no assertion in fiber.c / sd-future.c fires and no freed future is touched
NoCrash == st.crash = ""

\* a fiber suspended in sleep/io/await is only ever woken by its own future, its cancellation
\* or a deadline scope it is inside of
NoSpuriousWakeup == ~st.spurious

\* sd_fiber_yield() returns 0 or -ECANCELED
YieldReturnsZeroOrCanceled == ~st.badYield

\* a cancellation that arrives while a fiber waits in cancel_wait_unref() is not lost
NoLostCancel == ~st.lostCancel

\* an expired SD_FIBER_TIMEOUT still bounds every later wait in its scope
NoVoidDeadline ==
  \A x \in ExtIds :
    (st.fut[x].kind = "deadline" /\ st.fut[x].dropped) =>
      LET g == st.fut[x].cb IN
      ~(x \in Range(st.fib[g].cstack) /\ st.fib[g].state = "suspended" /\ st.fib[g].mode = "normal")

\* when the loop is finished every fiber's stack has been unwound (or never entered):
\* main's final sd_future_unref() is safe and nothing leaks
FinishedImpliesUnwound ==
  st.finished => \A g \in FiberIds : st.fib[g].state \in {"none", "initial", "completed", "freed"}

Safe == NoCrash /\ FinishedImpliesUnwound

EventuallyFinished == <>st.finished
ExitFinishes == st.exitReq ~> st.finished
CancelledCompletes ==
  \A g \in FiberIds : (st.fib[g].state = "cancelled") ~> (st.fib[g].state \in {"completed", "freed"})
DeadlineLeavesScope ==
  \A g \in FiberIds, x \in ExtIds :
    (st.fut[x].kind = "deadline" /\ st.fut[x].cb = g /\ st.fut[x].state = "resolved"
     /\ x \in Range(st.fib[g].cstack))
    ~> (x \notin Range(st.fib[g].cstack))

=============================================================================
