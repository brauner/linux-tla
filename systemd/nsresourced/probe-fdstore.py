#!/usr/bin/env python3
"""Allocate a 64K range for an empty user namespace as an unprivileged user,
drop the fd, and watch whether the registry entry and PID 1's fd store entry go
away (needs systemd-nsresourced.socket active and a kernel with the BPF LSM)."""
import os, socket, json, array, time, subprocess, sys

def sh(cmd):
    return subprocess.run(cmd, shell=True, capture_output=True, text=True).stdout.strip()

a, b = socket.socketpair(socket.AF_UNIX, socket.SOCK_DGRAM)
pid = os.fork()
if pid == 0:
    a.close()
    os.unshare(os.CLONE_NEWUSER)
    fd = os.open("/proc/self/ns/user", os.O_RDONLY | os.O_CLOEXEC)
    b.sendmsg([b"x"], [(socket.SOL_SOCKET, socket.SCM_RIGHTS, array.array("i", [fd]))])
    os._exit(0)
b.close()
msg, anc, flags, addr = a.recvmsg(1, socket.CMSG_LEN(4))
os.waitpid(pid, 0)
userns_fd = [array.array("i", d)[0] for l, t, d in anc if t == socket.SCM_RIGHTS][0]
ino = os.stat(userns_fd).st_ino
print("empty userns fd", userns_fd, "inode", ino)

s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
s.connect("/run/systemd/io.systemd.NamespaceResource")
req = json.dumps({"method": "io.systemd.NamespaceResource.AllocateUserRange",
                  "parameters": {"name": "tlaprobe", "mangleName": True, "size": 65536,
                                 "userNamespaceFileDescriptor": 0}}).encode() + b"\0"
s.sendmsg([req], [(socket.SOL_SOCKET, socket.SCM_RIGHTS, array.array("i", [userns_fd]))])
reply = b""
while not reply.endswith(b"\0"):
    chunk = s.recv(65536)
    if not chunk:
        break
    reply += chunk
print("reply:", reply.decode(errors="replace"))

def status(tag):
    print(f"[{tag}] registry:", sh("ls /run/systemd/nsresource/ 2>&1 | tr '\\n' ' '"))
    print(f"[{tag}] fdstore:", sh("systemctl show -p NFileDescriptorStore systemd-nsresourced.service"))
status("registered")
s.close()
os.close(userns_fd)
print("closed our userns fd and the connection")
for i in range(4):
    time.sleep(1.5)
    status(f"after {1.5*(i+1):.1f}s")
