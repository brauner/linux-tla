#!/usr/bin/env python3
"""Generate the TLC configurations: green configurations per service type
and per feature, and one configuration per bug, race or refused setting
with the switch that exposes it."""
import pathlib

SAFETY = ["TypeOK", "NoLostMessage", "HandoffRecorded", "NoLateUserLookup",
          "ActiveImpliesExeced", "JobDoneImpliesExeced", "JobFailedImpliesNotExeced",
          "ExecutorSignaledOnlyOnRequest", "MainPidIsTracked", "StopReachesMain",
          "InactiveImpliesNoProcess", "SessionNotClosedWhilePayloadAlive"]
LIVENESS = ["JobCompletes", "SessionEventuallyClosed"]

DEFAULTS = dict(Type="exec", PAM=False, PIDNS=False, User=True, RemainAfterExit=False,
                KillMode="control-group", Prio="PrioDefault", StopBudget=1, TimeoutBudget=1,
                PayloadStatuses="{0, 1}", PamDropMayFail=False,
                FIX_COLD_MARK=True, FIX_PAM_CLOSES_EXEC_FD=True, FIX_PPID_CHECK=True,
                BARRIER=True, PAM_WAITS_FOR_PARENT=False, FIX_PIDNS_PARENT_CLOSES_EXEC_FD=False)

QUIET = dict(StopBudget=0, TimeoutBudget=0)   # nothing but the payload ever ends the service

# name: (overrides, invariants, properties, expectation, description)
CONFIGS = {
    # the service types
    "simple_fixed":   (dict(Type="simple"), SAFETY, LIVENESS, "pass",
                       "Type=simple with User=, a stop: every property"),
    "simple_remain":  (dict(Type="simple", RemainAfterExit=True), SAFETY, LIVENESS, "pass",
                       "Type=simple with RemainAfterExit=yes"),
    "exec_fixed":     ({}, SAFETY, LIVENESS, "pass",
                       "Type=exec with User=, a stop and a start timeout: every property"),
    "exec_remain":    (dict(RemainAfterExit=True), SAFETY, LIVENESS, "pass",
                       "Type=exec with RemainAfterExit=yes"),
    "oneshot_fixed":  (dict(Type="oneshot", RemainAfterExit=True), SAFETY, LIVENESS, "pass",
                       "Type=oneshot with RemainAfterExit=yes"),
    "oneshot_noremain": (dict(Type="oneshot"), SAFETY, LIVENESS, "pass",
                       "Type=oneshot without RemainAfterExit="),
    # the exec_fd protocol and the event priorities
    "exec_no_cold":   (dict(FIX_COLD_MARK=False), ["ActiveImpliesExeced"], [], "violation",
                       "no exec_fd_mark_hot(false) after a failed execve(): ActiveImpliesExeced (the EOF of the exit counts as the execve)"),
    "exec_execfd_late": (dict(Prio="PrioExecFdLate"), ["JobFailedImpliesNotExeced"], [], "violation",
                       "exec_fd below SIGCHLD: JobFailedImpliesNotExeced (a payload that execve()d and exited 1 fails the start job)"),
    "exec_execfd_late_lost": (dict(Prio="PrioExecFdLate"), ["NoLostMessage"], [], "violation",
                       "exec_fd below SIGCHLD: NoLostMessage (the reap drops the readable exec_fd)"),
    "exec_handoff_late": (dict(Prio="PrioHandoffLate"), ["HandoffRecorded"], [], "violation",
                       "handoff timestamp below SIGCHLD: HandoffRecorded (the process is reaped before its timestamp is read)"),
    "exec_ul_late":   (dict(Prio="PrioUserLookupLate"), ["NoLateUserLookup"], [], "violation",
                       "user lookup below SIGCHLD: NoLateUserLookup (the uid arrives after the unit failed)"),
    # PrivatePIDs= and the pidref handoff
    "simple_pidns":   (dict(Type="simple", PIDNS=True, **QUIET), SAFETY, LIVENESS, "pass",
                       "Type=simple with PrivatePIDs=yes: the pidref handoff"),
    "exec_pidns":     (dict(PIDNS=True, **QUIET), ["JobFailedImpliesNotExeced"], [], "violation",
                       "Type=exec with PrivatePIDs=yes: JobFailedImpliesNotExeced (the parent still holds exec_fd between the errno write and its _exit(); a payload that execve()s and dies in that window fails the start job)"),
    "exec_pidns_fix": (dict(PIDNS=True, FIX_PIDNS_PARENT_CLOSES_EXEC_FD=True, **QUIET), SAFETY, LIVENESS, "pass",
                       "Type=exec with PrivatePIDs=yes, the parent drops exec_fd before the child goes on: every property"),
    "simple_pidns_late": (dict(Type="simple", PIDNS=True, Prio="PrioPidrefLate", **QUIET), ["ExecutorSignaledOnlyOnRequest"], [], "violation",
                       "pidref below SIGCHLD: ExecutorSignaledOnlyOnRequest (the parent's exit stops the service and kills the child)"),
    "exec_pidns_stop": (dict(PIDNS=True, KillMode="mixed"), ["StopReachesMain"], [], "violation",
                       "PrivatePIDs=yes with KillMode=mixed, a stop or a timeout between the fork and the parent's exit: StopReachesMain (SIGTERM went to the parent, the manager waits for the child)"),
    "exec_pidns_stop_cg": (dict(PIDNS=True, FIX_PIDNS_PARENT_CLOSES_EXEC_FD=True), SAFETY, LIVENESS, "pass",
                       "PrivatePIDs=yes with KillMode=control-group, a stop and a timeout: the cgroup kill reaches the child"),
    # PAMName= and (sd-pam)
    "exec_pam_cg":    (dict(PAM=True, **QUIET), SAFETY, LIVENESS, "pass",
                       "PAMName= with KillMode=control-group, nothing but the payload ends the service: every property"),
    "simple_pam_cg":  (dict(Type="simple", PAM=True, **QUIET), SAFETY, LIVENESS, "pass",
                       "Type=simple with PAMName=, KillMode=control-group"),
    "oneshot_pam_cg": (dict(Type="oneshot", PAM=True, RemainAfterExit=True, **QUIET), SAFETY, LIVENESS, "pass",
                       "Type=oneshot with PAMName=, KillMode=control-group, RemainAfterExit=yes"),
    "exec_pam_cg_stop": (dict(PAM=True, TimeoutBudget=0), ["SessionEventuallyClosed"], "violation",
                       "KillMode=control-group and a stop: SessionEventuallyClosed (SIGTERM reaches (sd-pam) while its parent lives, it exits without closing)"),
    "exec_pam_cg_timeout": (dict(PAM=True, StopBudget=0), ["SessionEventuallyClosed"], "violation",
                       "KillMode=control-group and a start timeout: SessionEventuallyClosed (the same race)"),
    "exec_pam_cg_wait": (dict(PAM=True, PAM_WAITS_FOR_PARENT=True), SAFETY, LIVENESS, "pass",
                       "KillMode=control-group, a stop and a timeout, a (sd-pam) that keeps waiting for its parent after a SIGTERM"),
    "exec_pam_mixed": (dict(PAM=True, KillMode="mixed", **QUIET), ["SessionEventuallyClosed"], "violation",
                       "KillMode=mixed, nothing but the payload ends the service: SessionEventuallyClosed (the next kill operation after the main process is gone is the SIGKILL of the cgroup)"),
    "exec_pam_dropfail_cg": (dict(PAM=True, PamDropMayFail=True, **QUIET), SAFETY, LIVENESS, "pass",
                       "KillMode=control-group, fully_set_uid_gid() fails in (sd-pam): no PDEATHSIG from an unprivileged parent, the cgroup SIGTERM closes the session"),
    "exec_pam_noppid": (dict(PAM=True, FIX_PPID_CHECK=False, **QUIET), SAFETY, LIVENESS, "pass",
                       "no getppid() check in (sd-pam): the barrier and the cgroup SIGTERM cover the window"),
    "exec_pam_nobarrier": (dict(PAM=True, BARRIER=False, **QUIET), ["JobFailedImpliesNotExeced"], [], "violation",
                       "Type=exec, no barrier in setup_pam(): JobFailedImpliesNotExeced ((sd-pam) still holds exec_fd when the payload execve()s and exits, the EOF comes too late)"),
    "simple_pam_nobarrier": (dict(Type="simple", PAM=True, BARRIER=False, **QUIET), SAFETY, LIVENESS, "pass",
                       "Type=simple, no barrier in setup_pam(): nothing depends on it, the getppid() check and the cgroup SIGTERM cover the PDEATHSIG window"),
    "simple_pam_nobarrier_noppid": (dict(Type="simple", PAM=True, BARRIER=False, FIX_PPID_CHECK=False, **QUIET), SAFETY, LIVENESS, "pass",
                       "Type=simple, neither barrier nor getppid() check: the cgroup SIGTERM alone covers the window"),
    "exec_pam_noclosefd": (dict(PAM=True, FIX_PAM_CLOSES_EXEC_FD=False, **QUIET), ["TypeOK"], ["JobCompletes"], "violation",
                       "(sd-pam) keeps exec_fd (before 5863f1da42): JobCompletes (no EOF while (sd-pam) lives)"),
    "exec_pam_pidns": (dict(PAM=True, PIDNS=True, **QUIET), ["SessionNotClosedWhilePayloadAlive"], [], "violation",
                       "PAMName= with PrivatePIDs=yes, refused by unit_verify_contexts(): SessionNotClosedWhilePayloadAlive (the pidref parent's exit fires PDEATHSIG)"),
}

def fmt(v):
    if isinstance(v, bool):
        return "TRUE" if v else "FALSE"
    if isinstance(v, int):
        return str(v)
    return v

here = pathlib.Path(__file__).resolve().parent
for old in here.glob("*.cfg"):
    if old.stem not in CONFIGS:
        old.unlink()
for name, entry in CONFIGS.items():
    if len(entry) == 5:
        over, invs, props, expect, desc = entry
    else:  # (overrides, properties, expectation, description): liveness only, TypeOK as invariant
        over, props, expect, desc = entry
        invs = ["TypeOK"]
    c = dict(DEFAULTS, **over)
    lines = [f"\\* generated by gen-cfgs.py, expected: {expect}",
             f"\\* {desc}",
             "SPECIFICATION Spec", "CONSTANTS"]
    for k in ["Type", "KillMode"]:
        lines.append(f'  {k} = "{c[k]}"')
    for k in ["PAM", "PIDNS", "User", "RemainAfterExit", "StopBudget", "TimeoutBudget",
              "PamDropMayFail", "FIX_COLD_MARK", "FIX_PAM_CLOSES_EXEC_FD", "FIX_PPID_CHECK",
              "BARRIER", "PAM_WAITS_FOR_PARENT", "FIX_PIDNS_PARENT_CLOSES_EXEC_FD"]:
        lines.append(f"  {k} = {fmt(c[k])}")
    lines.append(f"  PayloadStatuses = {c['PayloadStatuses']}")
    lines.append(f"  Prio <- {c['Prio']}")
    if invs:
        lines.append("INVARIANTS")
        lines += [f"  {i}" for i in invs]
    if props:
        lines.append("PROPERTIES")
        lines += [f"  {p}" for p in props]
    (here / f"{name}.cfg").write_text("\n".join(lines) + "\n")
    print(name, expect)
