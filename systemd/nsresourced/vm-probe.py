#!/usr/bin/env python3
"""Boot a throwaway mkosi VM of a systemd tree, run probe-fdstore-root.py in it
as root, and print the PROBE lines it logged:

    ./vm-probe.py [--tree DIR] [--out DIR] [--cmdline 'extra kernel arguments']

The tree needs a built image in build/mkosi.output whose kernel has the BPF
LSM (a CentOS 9 kernel does not load nsresourced's BPF object).  The guest
powers off by itself when the probe is done or after three minutes; the
forwarded journal and mkosi's output land in --out (logs/ by default)."""
import argparse, os, pathlib, shlex, signal, subprocess, sys, time

here = pathlib.Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument("--tree", default=os.path.expanduser("~/src/git/systemd-worktrees/systemd"))
ap.add_argument("--out", default=str(here / "logs"))
ap.add_argument("--cmdline", default="")
ap.add_argument("--timeout", type=int, default=480)
args = ap.parse_args()
out = pathlib.Path(args.out)
out.mkdir(exist_ok=True)
journal = out / "vm-probe.journal"
journal.unlink(missing_ok=True)

unit = """[Unit]
Description=fd store probe
After=multi-user.target
Wants=multi-user.target
SuccessAction=poweroff-force
FailureAction=poweroff-force

[Service]
Type=oneshot
TimeoutStartSec=180
LoadCredential=probe.py
StandardOutput=journal+console
StandardError=journal+console
ExecStart=/bin/sh -c 'echo PROBE lsm: $(cat /sys/kernel/security/lsm 2>&1); echo PROBE kernel: $(uname -r); systemctl start systemd-nsresourced.socket; python3 "$CREDENTIALS_DIRECTORY/probe.py"'
"""
cmd = ["mkosi", "--directory", args.tree, "--machine", "fdprobe", "--ephemeral=yes",
       "--runtime-network=none", "--runtime-build-sources=no", "--tools-tree=no", "--tpm=no",
       "--register=no", "--console=read-only", "--forward-journal", str(journal),
       "--credential", "systemd.extra-unit.fdprobe.service=" + shlex.quote(unit),
       "--credential", "probe.py=" + shlex.quote((here / "probe-fdstore-root.py").read_text()),
       "--kernel-command-line-extra",
       "systemd.hostname=fdprobe systemd.unit=fdprobe.service "
       "systemd.mask=systemd-networkd-wait-online.service systemd.mask=serial-getty@.service "
       "systemd.show_status=error systemd.crash_shell=0 systemd.crash_action=poweroff loglevel=4 " + args.cmdline,
       "vm"]
t = time.time()
with open(out / "vm-probe.out", "w") as log:
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
print(f"mkosi: exit {rc} after {time.time() - t:.0f}s, output in {out / 'vm-probe.out'}, journal in {journal}")
lines = subprocess.run(["journalctl", "--file", str(journal), "-o", "cat", "--no-pager", "-u", "fdprobe.service"],
                       capture_output=True, text=True).stdout.splitlines()
for line in lines:
    if line.startswith("PROBE") or "Traceback" in line or "Error" in line or "error" in line.lower():
        print(line)
