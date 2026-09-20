#!/usr/bin/env python3
"""Boot a throwaway mkosi VM of a systemd tree and run integration subtests from
another tree in it, as root, without rebuilding the image:

    ./vm-run-tests.py --tree DIR --tests-from DIR TEST-07-PID1.foo.sh TEST-07-PID1.bar.sh=TESTCASE_REGEX ...

The scripts (and the test-control.sh/util.sh they source) are handed to the VM
as credentials, copied next to the image's own testdata units and run one by
one; the RESULT lines they produce are printed at the end together with the
journal of whatever failed.  Used to check that the tests for the executor
fixes fail on a systemd without them (the image of another tree) and pass with
them."""
import argparse, os, pathlib, shlex, signal, subprocess, time

here = pathlib.Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument("--tree", default=os.path.expanduser("~/src/git/systemd-worktrees/work.systemd.keyring"))
ap.add_argument("--tests-from", default=os.path.expanduser("~/src/git/systemd-worktrees/work.systemd.executor.races"))
ap.add_argument("--cpus", default="4")
ap.add_argument("--machine", default="runtests", help="VM name, distinct per concurrent run")
ap.add_argument("--installed", action="store_true", help="run the scripts the image carries instead of passing them in")
ap.add_argument("--out", default=str(here / "logs"))
ap.add_argument("--timeout", type=int, default=900)
ap.add_argument("scripts", nargs="+", help="script name, optionally =REGEX for TEST_MATCH_SUBTEST and TEST_MATCH_TESTCASE")
args = ap.parse_args()
scripts = [(a.split("=", 1) + [""])[:2] for a in args.scripts]
out = pathlib.Path(args.out).resolve()
out.mkdir(exist_ok=True)
journal = out / "vm-run-tests.journal"
journal.unlink(missing_ok=True)
units = pathlib.Path(args.tests_from) / "test/units"

creds = []
if not args.installed:
    for name in ["test-control.sh", "util.sh", *(n for n, _ in scripts)]:
        creds += ["--credential", f"test.{name}=" + shlex.quote((units / name).read_text())]

for n, m in scripts:
    if any(c in m for c in '"$`\\\'') or "'" in n:
        raise SystemExit(f"unsupported character in {n}={m}")
run = "; ".join(f'if TEST_MATCH_SUBTEST="{m}" TEST_MATCH_TESTCASE="{m}" "$D/{n}"; then echo "RESULT PASS {n}"; else echo "RESULT FAIL {n}"; fi'
                for n, m in scripts)
unit = f"""[Unit]
Description=run integration subtests
After=multi-user.target
Wants=multi-user.target
SuccessAction=poweroff-force
FailureAction=poweroff-force

[Service]
Type=oneshot
TimeoutStartSec={args.timeout - 60}
ImportCredential=test.*
StandardOutput=journal+console
StandardError=journal+console
ExecStart=/bin/bash -c 'D=/usr/lib/systemd/tests/testdata/units; mkdir -p "$D"; for f in "$CREDENTIALS_DIRECTORY"/test.*; do n=$${{f##*/test.}}; cp "$f" "$D/$n"; chmod +x "$D/$n"; done; {run}; exit 0'
"""
cmd = ["mkosi", "--directory", args.tree, "--machine", args.machine, "--ephemeral=yes",
       "--runtime-network=none", "--runtime-build-sources=no", "--tools-tree=no", "--tpm=no",
       "--register=no", "--console=read-only", "--forward-journal", str(journal), "--cpus", args.cpus,
       "--credential", "systemd.extra-unit.runtests.service=" + shlex.quote(unit), *creds,
       "--kernel-command-line-extra",
       "systemd.hostname=runtests systemd.unit=runtests.service "
       "systemd.mask=systemd-networkd-wait-online.service systemd.mask=serial-getty@.service "
       "systemd.show_status=error systemd.crash_shell=0 systemd.crash_action=poweroff loglevel=4",
       "vm"]
t = time.time()
with open(out / "vm-run-tests.out", "w") as log:
    p = subprocess.Popen(cmd, cwd=args.tree, stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                         start_new_session=True)
    try:
        rc = p.wait(timeout=args.timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGTERM)
        time.sleep(5)
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        rc = "timeout"
print(f"mkosi: exit {rc} after {time.time() - t:.0f}s, output in {out / 'vm-run-tests.out'}, journal in {journal}")
lines = subprocess.run(["journalctl", "--file", str(journal), "-o", "cat", "--no-pager", "-u", "runtests.service"],
                       capture_output=True, text=True).stdout.splitlines()
for line in lines:
    if line.startswith("RESULT ") or "assert" in line.lower() or line.startswith("+ ") and ("exit" in line or "test " in line):
        print(line)
