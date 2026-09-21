#!/usr/bin/env python3
"""Generate the TLC configurations for Fiber.tla: one per finding (the switch
or the operation set that exposes it against the code as it is), and green
configurations with the candidate fixes on, plus ablations that show which
fix each property needs."""
import pathlib

SAFETY = ["NoCrash", "NoSpuriousWakeup", "YieldReturnsZeroOrCanceled", "NoLostCancel",
          "NoVoidDeadline", "FinishedImpliesUnwound"]
LIVENESS = ["EventuallyFinished", "ExitFinishes", "CancelledCompletes", "DeadlineLeavesScope"]

ALL_OPS = ["yield", "ext", "spawn", "spawnfl", "awaitf", "cancel", "exit", "tobegin", "toend", "bare"]

FIXES = dict(FixFreePending=True, FixCwuLoop=True, FixExitArmed=True, FixRecancel=True,
             FixStickyError=True, FixNoChildTrampoline=True, FixAwaitLoop=True)
NOFIX = {k: False for k in FIXES}

DEFAULTS = dict(FiberOrder=["f1", "f2", "f3"], TopLevel=["f1", "f2"], FloatingTop=[],
                ExtOrder=["x1", "x2"], WaitOrder=["w1", "w2", "w3"], FiberPrioSeq=[0, 0, 0], Budget=2,
                Ops=ALL_OPS, MainMayExit=True, MainMayCancel=False, MainCancelMax=0, ExitOnIdle=False,
                AllowIgnoreErrors=False, ChildMayFail=False, **NOFIX)

def ops(*names):
    return dict(Ops=list(names))

def without(fix):
    return dict(FIXES, **{fix: False})

CANCELLERS = dict(MainMayCancel=True, ChildMayFail=True)

# name: (overrides, invariants, properties, expectation, description)
CONFIGS = {
    # ---- the code as it is: one configuration per finding -------------------------------
    "asis_smoke": (ops("yield", "ext"), ["NoCrash", "FinishedImpliesUnwound"], [], "pass",
                   "two top-level fibers that only yield and sleep, exit from main: nothing to find"),
    "asis_cwu_exit_race": (ops("spawn", "yield"), ["NoCrash"], [], "violation",
                   "a parent waiting in cancel_wait_unref() for its cancelled child when sd_event_exit() arrives: the exit source cancels the parent, the child's defer source is never dispatched again, the parent's unref of the still-pending child frees it (assertion)"),
    "asis_cwu_cancel_race": (dict(MainMayCancel=True, **ops("spawn", "yield")), ["NoCrash"], [], "violation",
                   "the parent is cancelled while it waits for the child's cancellation: cancel_wait_unref() returns early and unrefs the pending child"),
    "asis_cwu_sibling_race": (ops("spawn", "yield", "cancel"), ["NoCrash"], [], "violation",
                   "the same, with a sibling fiber doing the cancelling from inside the loop"),
    "asis_spurious_child": (ops("spawn", "ext"), ["NoCrash", "NoSpuriousWakeup"], [], "violation",
                   "a child's completion resumes its creator out of an unrelated sleep/io wait (fiber_resume_trampoline is the default callback of every future created on a fiber)"),
    "asis_spurious_child_fails": (dict(ChildMayFail=True, **ops("spawn", "ext")), ["NoCrash", "NoSpuriousWakeup"], [], "violation",
                   "the child fails: the parent's sleep returns the child's error"),
    "asis_uaf_floating_child": (dict(TopLevel=["f1"], FloatingTop=["f1"], **ops("spawnfl", "yield")), ["NoCrash"], [], "violation",
                   "a floating fiber spawns a floating child and completes: the child's completion resumes the freed parent"),
    "asis_stranded_floating_child": (dict(TopLevel=["f1"], **ops("spawnfl", "ext")), ["NoCrash", "FinishedImpliesUnwound"], [], "violation",
                   "a floating child created on a fiber has no exit source and no owner: it is never unwound when the loop exits"),
    "asis_void_deadline": (dict(TopLevel=["f1"], Budget=4, **ops("tobegin", "yield", "bare")), ["NoCrash", "NoVoidDeadline"], [], "violation",
                   "the SD_FIBER_TIMEOUT deadline fires while the fiber is queued after a yield: sd_fiber_resume() drops -ETIME, the next wait in the scope is unbounded"),
    "asis_void_deadline_live": (dict(TopLevel=["f1"], Budget=4, MainMayExit=False, **ops("tobegin", "yield", "bare")), ["NoCrash"], ["DeadlineLeavesScope"], "violation",
                   "the same without an exit from main: the loop blocks forever with the fiber suspended inside the expired scope (a deadlock for TLC)"),
    "asis_void_deadline_io": (dict(TopLevel=["f1"], Budget=4, ExtOrder=["x1", "x2", "x3"], **ops("tobegin", "ext", "yield", "bare")), ["NoCrash", "NoVoidDeadline"], [], "violation",
                   "the deadline fires in the same iteration as the io the fiber waits for, the fiber yields afterwards: -ETIME is dropped"),
    "asis_lost_cancel": (dict(MainMayCancel=True, Budget=4, **ops("tobegin", "spawn", "toend", "yield")), ["NoLostCancel"], [], "violation",
                   "cancelled while cancel_wait_unref() waits at the end of an SD_FIBER_WITH_TIMEOUT block: the cancellation is swallowed and the fiber carries on"),
    "asis_lost_cancel_exit": (dict(Budget=5, **ops("tobegin", "spawn", "toend", "yield", "bare")), ["FinishedImpliesUnwound"], [], "violation",
                   "the swallowed cancellation came from the exit source: the fiber suspends again and is never unwound"),
    "asis_stale_yield": (dict(TopLevel=["f1"], MainMayCancel=True, AllowIgnoreErrors=True, Budget=3, **ops("tobegin", "bare", "yield")), ["NoCrash", "YieldReturnsZeroOrCanceled"], [], "violation",
                   "a resume value stashed before a cancellation is not consumed by the -ECANCELED return and surfaces from a later sd_fiber_yield()"),
    "asis_all": (dict(Budget=3, **CANCELLERS), SAFETY, [], "violation",
                 "every operation and every safety property against the code as it is (TLC stops at the first violation)"),
    # ---- the fixes ------------------------------------------------------------------------
    # Every operation with three operations per fiber is beyond a full BFS (hundreds of millions
    # of states, a state queue of hundreds of GB), so the green configurations are the whole
    # operation set with two operations per fiber, and scenario families with more.
    "fixed_all": (dict(Budget=2, **CANCELLERS, **FIXES), SAFETY, [], "pass",
                  "every operation, every safety property, every fix, two operations per fiber"),
    "fixed_all_live": (dict(Budget=2, **FIXES), SAFETY, ["EventuallyFinished", "ExitFinishes"], "pass",
                  "every operation, every fix, the loop finishes and every fiber with it (cancellation by main is fixed_cancel_live's job: with it the liveness graph is three times the size)"),
    "fixed_prio": (dict(Budget=3, FiberPrioSeq=[0, 1, 0], **CANCELLERS, **FIXES), SAFETY, [], "pass",
                  "distinct priorities, three operations: the second top-level fiber runs after the first and its child"),
    "fixed_prio_child_low": (dict(Budget=3, FiberPrioSeq=[0, 0, 1], **CANCELLERS, **FIXES), SAFETY, [], "pass",
                  "children at lower priority than their parents, three operations"),
    "fixed_idle": (dict(Budget=2, ExitOnIdle=True, MainMayExit=False, MainCancelMax=2, **CANCELLERS, **FIXES), SAFETY, ["EventuallyFinished"], "pass",
                  "sd_event_set_exit_on_idle() instead of an explicit exit"),
    "fixed_floating": (dict(Budget=2, FloatingTop=["f1"], MainCancelMax=2, **CANCELLERS, **FIXES), SAFETY, ["EventuallyFinished"], "pass",
                  "a floating top-level fiber (run_main_fiber(), varlink method fibers)"),
    "fixed_ignore_errors": (dict(AllowIgnoreErrors=True, Budget=2, **CANCELLERS, **FIXES, **ops(*[o for o in ALL_OPS if o not in ("bare", "awaitf")])), SAFETY, [], "pass",
                  "fibers that ignore errors (including -ECANCELED) and carry on; no bare suspends and no awaits (two fibers ignoring their cancellation and awaiting each other is a plain deadlock)"),
    "fixed_four_fibers": (dict(FiberOrder=["f1", "f2", "f3", "f4"], FiberPrioSeq=[0, 0, 0, 0], WaitOrder=["w1", "w2", "w3", "w4"], Budget=2, MainMayCancel=True, **ops("spawn", "yield", "ext", "awaitf", "cancel"), **FIXES), SAFETY, [], "pass",
                  "two top-level fibers and two child slots (grandchildren): spawning, waiting, cancelling"),
    "fixed_deadline": (dict(FiberOrder=["f1", "f2"], FiberPrioSeq=[0, 0], TopLevel=["f1"], Budget=4, ExtOrder=["x1", "x2", "x3"], **ops("tobegin", "ext", "yield", "bare", "toend", "spawn"), **FIXES), SAFETY, [], "pass",
                  "timeout scopes, four operations, one top-level fiber and one child slot: every deadline is delivered"),
    "fixed_deadline_live": (dict(TopLevel=["f1"], Budget=3, ExtOrder=["x1", "x2"], **ops("tobegin", "ext", "yield", "bare", "toend"), **FIXES), SAFETY, ["DeadlineLeavesScope", "EventuallyFinished"], "pass",
                  "timeout scopes, three operations: the fiber leaves every expired scope"),
    "fixed_cancel": (dict(Budget=3, MainMayCancel=True, **ops("spawn", "yield", "cancel", "awaitf", "tobegin", "toend", "bare"), **FIXES), SAFETY, [], "pass",
                  "cancellation from main, siblings and exit, three operations"),
    "fixed_cancel_live": (dict(Budget=3, MainMayCancel=True, MainCancelMax=2, **ops("spawn", "yield", "cancel", "awaitf"), **FIXES), SAFETY, ["CancelledCompletes", "EventuallyFinished"], "pass",
                  "cancellation from main (at most twice), siblings and exit: every cancelled fiber completes"),
    "fixed_children": (dict(Budget=3, ChildMayFail=True, **ops("spawn", "spawnfl", "awaitf", "ext", "yield"), **FIXES), SAFETY, [], "pass",
                  "owned and floating children that may fail, awaited or not, three operations"),
    "fixed_exit": (dict(Budget=3, **ops("spawn", "yield", "ext", "exit", "bare"), **FIXES), SAFETY, [], "pass",
                  "exit requested from a fiber or from main while fibers sleep, wait or hold children, three operations"),
    # ---- ablations: all fixes but one -----------------------------------------------------
    "abl_no_freepending": (dict(Budget=2, **CANCELLERS, **without("FixFreePending")), SAFETY, [], "pass",
                  "without the sd_future_free() fix: with the other fixes no pending future is ever dropped (the fix matters on error paths the model has no operation for)"),
    "abl_no_cwuloop": (dict(Budget=3, MainMayCancel=True, **ops("spawn", "yield", "cancel"), **without("FixCwuLoop")), SAFETY, [], "violation",
                  "without cancel_wait_unref() waiting for the resolution: the premature wakeup unrefs a live fiber"),
    "abl_no_exitarmed": (dict(Budget=3, **ops("spawnfl", "spawn", "ext", "yield"), **without("FixExitArmed")), SAFETY, [], "violation",
                  "without an always-armed exit source: fibers created on a fiber are stranded when the loop exits"),
    "abl_no_exitarmed_cancel": (dict(Budget=3, MainMayCancel=True, **ops("spawn", "yield", "awaitf"), **without("FixExitArmed")), SAFETY, [], "violation",
                  "the same with a cancel from main after the exit source fired once"),
    "abl_no_recancel": (dict(Budget=4, MainMayCancel=True, **ops("tobegin", "spawn", "toend", "yield"), **without("FixRecancel")), SAFETY, [], "violation",
                  "without redelivering a swallowed cancellation"),
    "abl_no_recancel_exit": (dict(Budget=5, **ops("tobegin", "spawn", "toend", "yield", "bare"), **without("FixRecancel")), SAFETY, [], "violation",
                  "without redelivering a swallowed cancellation, the exit source fired once: stranded"),
    "abl_no_sticky": (dict(TopLevel=["f1"], Budget=4, **ops("tobegin", "yield", "bare"), **without("FixStickyError")), SAFETY, [], "violation",
                  "without keeping an error result for a queued fiber: the deadline is dropped"),
    "abl_no_childtramp": (dict(Budget=2, **ops("spawn", "ext", "awaitf"), **without("FixNoChildTrampoline")), SAFETY, [], "pass",
                  "with children still resuming their creator on completion: the wait loops absorb the spurious wakeups"),
    "abl_no_childtramp_floating": (dict(TopLevel=["f1"], FloatingTop=["f1"], **ops("spawnfl", "yield"), **without("FixNoChildTrampoline")), SAFETY, [], "violation",
                  "with children still resuming their creator: a floating child resumes its freed floating parent"),
    "abl_no_awaitloop": (dict(Budget=2, **CANCELLERS, **without("FixAwaitLoop")), SAFETY, [], "pass",
                  "without re-suspending on unrelated wakeups: with no child trampoline nothing unrelated wakes a fiber up"),
}

def fmt(v):
    if isinstance(v, bool):
        return "TRUE" if v else "FALSE"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        return f'"{v}"'
    raise TypeError(v)

def fmt_seq(v):
    return "<<" + ", ".join(fmt(x) for x in v) + ">>"

def fmt_set(v):
    return "{" + ", ".join(fmt(x) for x in v) + "}"

here = pathlib.Path(__file__).resolve().parent
for old in list(here.glob("*.cfg")) + list(here.glob("MC_*.tla")):
    stem = old.stem[3:] if old.stem.startswith("MC_") else old.stem
    if stem not in CONFIGS:
        old.unlink()
# TLC's configuration files take only scalars, so sequences and sets of strings
# come from a generated MC_<name>.tla that the configuration refers to with <-.
for name, (over, invs, props, expect, desc) in CONFIGS.items():
    c = dict(DEFAULTS, **over)
    mc = [f"---- MODULE MC_{name} ----",
          f"\\* generated by gen-cfgs.py, expected: {expect}",
          "EXTENDS Fiber"]
    for k in ["FiberOrder", "FiberPrioSeq", "ExtOrder", "WaitOrder"]:
        mc.append(f"MC_{k} == {fmt_seq(c[k])}")
    for k in ["TopLevel", "FloatingTop", "Ops"]:
        mc.append(f"MC_{k} == {fmt_set(c[k])}")
    mc.append("====")
    (here / f"MC_{name}.tla").write_text("\n".join(mc) + "\n")
    lines = [f"\\* generated by gen-cfgs.py, expected: {expect}",
             f"\\* {desc}",
             "SPECIFICATION Spec", "CONSTANTS"]
    for k in ["FiberOrder", "FiberPrioSeq", "ExtOrder", "WaitOrder", "TopLevel", "FloatingTop", "Ops"]:
        lines.append(f"  {k} <- MC_{k}")
    for k in ["Budget", "MainMayExit", "MainMayCancel", "MainCancelMax", "ExitOnIdle", "AllowIgnoreErrors",
              "ChildMayFail"] + list(FIXES):
        lines.append(f"  {k} = {fmt(c[k])}")
    if invs:
        lines.append("INVARIANTS")
        lines += [f"  {i}" for i in invs]
    if props:
        lines.append("PROPERTIES")
        lines += [f"  {p}" for p in props]
    (here / f"{name}.cfg").write_text("\n".join(lines) + "\n")
    print(name, expect)
