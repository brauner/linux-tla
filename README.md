# TLA+ models of Linux kernel and systemd protocols

Formal models of concurrent protocols, one directory per protocol,
written to check specific series against the interleavings a reproducer
cannot enumerate.  Each directory carries its own README with the mapping
from model actions to functions, the abstractions, the configurations
and the results, and pins the tree it was written against.

## Kernel

| Directory | Protocol | Kernel base |
|-----------|----------|-------------|
| `kernel/coredump/` | the coredump rendezvous and the signal, exit, fork, exec and io-wq code around it; "coredump & signals: an impossible affair" | 938c2dd45269 on c7b1fa3db4a1 (vfs-7.4.coredump) |
| `kernel/close_range/` | close_range() with CLOSE_RANGE_EXCEPT and CLOSE_RANGE_CLOEXEC_ONLY and the clone dup_fd() makes for CLOSE_RANGE_UNSHARE; "files,close_range: add CLOSE_RANGE_{CLOEXEC_ONLY,EXCEPT}" | 93957f154604 on 5dd1818b15d9 (work.file.close_range_except) |
| `kernel/close-files/` | the order in which a dying descriptor table closes its files and the exit, exec and fork code around it; "files: make closing files synchronous for close_range(), exec, exit" and its fixes | c7b1fa3db4a1 plus the fixes in 938c2dd45269 |

## systemd

| Directory | Protocol | systemd base |
|-----------|----------|--------------|
| `systemd/executor/` | systemd-executor and the service manager: the exec_fd protocol of Type=exec, the (sd-pam) helper, the PrivatePIDs= pidref handoff, the priorities of the manager's event loop against SIGCHLD, and the kill logic | v262-rc2-60-ge96ff3b5b9 |
| `systemd/nsresourced/` | the user namespace registry of systemd-nsresourced: clients (nspawn, the executor), the worker, the BPF-LSM map and death ring buffer, PID 1's fd store, the kernel's inode reuse, the manager's release and startup sweep | v262-rc2-60-ge96ff3b5b9 |
| `systemd/mountfsd/` | dm-verity device sharing between systemd-mountfsd workers: the verity_partition() retry loop against the device-mapper's deferred removal and udev's symlinks | v262-rc2-60-ge96ff3b5b9 |
| `systemd/fiber/` | the fiber runtime of sd-future: fibers driven by their defer and exit event sources, futures resolving and resuming fibers, cancellation and cleanup unwinding, SD_FIBER_TIMEOUT() deadlines, against sd-event's dispatch order; six findings, every fix a switch | v262-rc3 (e96ff3b5b9) |

## Running

Every directory expects `tla2tools.jar` from
https://github.com/tlaplus/tlaplus/releases (2.19 was used) and a Java 17
or newer runtime.

    export TLA2TOOLS=/path/to/tla2tools.jar
    cd kernel/coredump && ./check.sh sqpoll_deadlock

The configurations that switch a fix off stop at their counterexample in
seconds to minutes; the green kernel proofs explore tens of millions of
states and want a large machine (`run-parallel.sh`).  The systemd models
are small and finish in seconds.

## License

MPL-2.0, see `LICENSE`.
