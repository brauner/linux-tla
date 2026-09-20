#!/usr/bin/env python3
"""probe-fdstore.py for a throwaway VM, run as root: allocate a 64K range for an
empty user namespace, drop every reference the client holds, and print what the
registry and PID 1's fd store do with the namespace; then stop and start
systemd-nsresourced to see when the entry is reaped.  Every line starts with
PROBE so that vm-probe.py can pick them out of the journal."""
import array, ctypes, json, os, socket, subprocess, sys, time

CLONE_NEWUSER = 0x10000000


def sh(cmd):
    return subprocess.run(cmd, shell=True, capture_output=True, text=True).stdout.strip()


def out(msg):
    print("PROBE " + msg, flush=True)


# A child creates the namespace and passes the fd back, then exits: the parent's
# fd is the only reference the client side holds.
a, b = socket.socketpair(socket.AF_UNIX, socket.SOCK_SEQPACKET)
pid = os.fork()
if pid == 0:
    a.close()
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.unshare(CLONE_NEWUSER) != 0:
        os._exit(ctypes.get_errno())
    fd = os.open("/proc/self/ns/user", os.O_RDONLY | os.O_CLOEXEC)
    b.sendmsg([b"x"], [(socket.SOL_SOCKET, socket.SCM_RIGHTS, array.array("i", [fd]))])
    os._exit(0)
b.close()
a.settimeout(10)
try:
    msg, anc, _, _ = a.recvmsg(1, socket.CMSG_LEN(4))
except (socket.timeout, OSError) as e:
    anc = []
_, status = os.waitpid(pid, 0)
fds = [array.array("i", d)[0] for l, t, d in anc if t == socket.SCM_RIGHTS]
if not fds:
    out(f"child failed to create the namespace, wait status {status}")
    sys.exit(1)
userns_fd = fds[0]
ino = os.stat(userns_fd).st_ino
out(f"userns inode {ino}")

s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
s.settimeout(60)
s.connect("/run/systemd/io.systemd.NamespaceResource")
req = json.dumps({"method": "io.systemd.NamespaceResource.AllocateUserRange",
                  "parameters": {"name": "fdprobe", "mangleName": True, "size": 65536,
                                 "userNamespaceFileDescriptor": 0}}).encode() + b"\0"
s.sendmsg([req], [(socket.SOL_SOCKET, socket.SCM_RIGHTS, array.array("i", [userns_fd]))])
reply = b""
while not reply.endswith(b"\0"):
    c = s.recv(65536)
    if not c:
        break
    reply += c
out("reply: " + reply.decode(errors="replace").strip("\0"))
if b'"error"' in reply:
    sys.exit(1)


def status(tag):
    reg = sh("ls /run/systemd/nsresource/registry 2>&1").replace("\n", " ")
    held = sh(f"ls -l /proc/1/fd 2>/dev/null | grep -c 'user:\\[{ino}\\]'")
    store = sh("systemctl show -p NFileDescriptorStore systemd-nsresourced.service")
    out(f"[{tag}] registry: {reg}")
    out(f"[{tag}] pid1 holds user:[{ino}]: {held}; {store}")


for pid in sh("pgrep -f 'systemd-nsresource(d|work)'").split():
    comm = sh(f"cat /proc/{pid}/comm")
    env = sh(f"tr '\\0' '\\n' < /proc/{pid}/environ | grep -E '^(NOTIFY_SOCKET|LISTEN_FDS)='").replace("\n", " ")
    out(f"env of {comm}[{pid}]: {env or 'no NOTIFY_SOCKET'}")
status("registered")
s.close()
os.close(userns_fd)
out("client dropped its fd and the connection")
for i in range(3):
    time.sleep(2)
    status(f"t+{2 * (i + 1)}s")
out("stopping systemd-nsresourced.service and .socket: the fd store goes with the unit")
sh("systemctl stop systemd-nsresourced.service systemd-nsresourced.socket")
time.sleep(2)
status("stopped")
out("starting systemd-nsresourced again: its startup sweep")
sh("systemctl start systemd-nsresourced.socket systemd-nsresourced.service")
time.sleep(3)
status("restarted")
for line in sh("journalctl -u systemd-nsresourced.service -o cat --no-pager -p info").splitlines()[-25:]:
    out("nsresourced: " + line)
