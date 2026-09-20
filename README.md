# TLA+ models of Linux kernel protocols

Formal models of concurrent kernel protocols, one directory per protocol,
written to check specific series against the interleavings a reproducer
cannot enumerate.  Each directory carries its own README with the mapping
from model actions to kernel functions, the abstractions, the
configurations and the results, and pins the kernel tree it was written
against.

| Directory | Protocol | Kernel base |
|-----------|----------|-------------|
| `coredump/` | the coredump rendezvous and the signal, exit, fork, exec and io-wq code around it; "coredump & signals: an impossible affair" | 938c2dd45269 on c7b1fa3db4a1 (vfs-7.4.coredump) |

## Running

Every directory expects `tla2tools.jar` from
https://github.com/tlaplus/tlaplus/releases (2.19 was used) and a Java 17
or newer runtime.

    export TLA2TOOLS=/path/to/tla2tools.jar
    cd coredump && ./check.sh sqpoll_deadlock

The configurations that switch a fix off stop at their counterexample in
seconds to minutes; the green proofs explore tens of millions of states
and want a large machine (`run-parallel.sh`).

## License

MPL-2.0, see `LICENSE`.
