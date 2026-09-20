#!/usr/bin/env python3
"""Replace the RESULTS_TABLE marker in README.md with the summaries in logs/."""
import pathlib, re
here = pathlib.Path(__file__).resolve().parent
rows = []
for f in ["summary.txt", "summary-bugs.txt"]:
    p = here / "logs" / f
    if not p.exists():
        continue
    for line in p.read_text().splitlines()[1:]:
        parts = line.split()
        if len(parts) < 4 or parts[0] == "BUGS-DONE":
            continue
        rows.append(parts)
desc = {
 "signals_fixed": "every fix on, all properties",
 "cdhole_fixed": "every fix on, all properties",
 "plain_fixed": "every fix on, all invariants (full budgets)",
 "plain_live": "every fix on, all invariants and both liveness properties (no USR signal, no retry)",
 "sqpoll_fixed": "every fix on, all properties",
 "signals_no_rcu": "FIX_RCU_RELEASE off: NoUseAfterFree",
 "signals_no_retarget": "FIX_RETARGET_GROUP_EXIT and FIX_SIGPENDING_DUMPCORE off: TruncationJustified",
 "signals_retarget_only": "only FIX_RETARGET_GROUP_EXIT off: TruncationJustified (the signal_pending() rule covers the retarget)",
 "signals_sigpending_only": "only FIX_SIGPENDING_DUMPCORE off: TruncationJustified (nothing but the retarget sets TIF_SIGPENDING on the dumper)",
 "signals_no_freezer": "FIX_SIGPENDING_DUMPCORE off: FreezeAbortsDump (a cgroup v2 freeze lets a file dump complete)",
 "sqpoll_deadlock": "FIX_WORKER_NODUMP and FIX_PTRACE_MASK off: DumpEnds (the io-wq worker of an SQPOLL ring dumps, the SQPOLL thread waits for it)",
 "sqpoll_mask_only": "only FIX_WORKER_NODUMP off: DumpEnds (the mask keeps the worker from ever dequeuing the signal)",
 "sqpoll_no_gate_signaled": "FIX_GATE_SIGNALED off: CountConsistent (the SQPOLL thread creates an uncounted worker from its cancel loop)",
 "plain_strict": "every fix on: TruncationJustifiedStrict (TIF_NOTIFY_SIGNAL from a worker creation cuts the dump)",
 "plain_no_exec_cancel": "FIX_EXEC_CANCEL_FIRST off: SingleThreadedExec (a create_worker_cont() survives de_thread())",
 "cdhole_no_gate": "FIX_GATE_POSTCOREDUMP off: CountConsistent (the exit(2) thread creates an uncounted worker)",
}
out = ["| Configuration | Checks | Expected | Result | Distinct states | TLC time (32 workers) |", "|---|---|---|---|---|---|"]
seen = set()
for parts in rows:
    cfg, expect, result = parts[0], parts[1], parts[2]
    states = parts[3] if len(parts) >= 6 else ""
    took = parts[4] if len(parts) >= 6 else ""
    if cfg in seen:
        continue
    seen.add(cfg)
    out.append(f"| `{cfg}` | {desc.get(cfg, '')} | {expect} | {result} | {states} | {took} |")
extra = """
`IoWqExitBit_fixed` passes and `IoWqExitBit_nobarrier` violates
`NoStrandedCreate` with the store buffering trace (set_bit() buffered,
the cancel loads an empty list, the creator sees the bit clear before and
after its add, the store lands).  `CorePattern_fixed` passes and
`CorePattern_torn` violates `ConsistentParse` with the file mode of the
new pattern combined with the helper path of the old one.
"""
readme = here / "README.md"
s = readme.read_text()
s = s.replace("RESULTS_TABLE", "\n".join(out) + "\n" + extra)
readme.write_text(s)
print("\n".join(out))
