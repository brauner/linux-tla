# Synchronous file closing

The series "files: make closing files synchronous for close_range(), exec,
exit" (merge c7b1fa3db4a1 in vfs-7.4.coredump) runs the final `__fput()`
of a dying descriptor table inside the walk instead of from task work.
Nothing in it is a rendezvous; what changed is the order in which
`->flush()` and `->release()` run relative to each other and to the rest
of exit, exec and fork.  Four small models cover the four places where
that order was visible.  Each is a few dozen lines and TLC finishes every
configuration in a second (`./check-all.sh`).

| Module | Question | Kernel |
|--------|----------|--------|
| `CloseOrder.tla` | for every pattern of "the release (or flush) of fd i waits for the release of fd j" over three descriptors, which walk order hangs? | `close_files()`, `__range_close()`, `close_cloexec_files()` before the series (`filp_close()` + LIFO task work), as merged (ascending), and with "fs: close files from the highest descriptor down" (descending) |
| `VforkExec.tla` | a vfork child execs holding the last reference to a file the parent serves | `begin_new_exec()`: `close_cloexec_files()` before `exec_mmap()` -> `mm_exit_exec_release()` -> `complete_vfork_done()`; the deferred put of mainline before 64cdb497e727 versus the inline put; `exit(2)` via `exit_mm()` before `exit_files()` |
| `ForkCleanup.tla` | a failed `copy_process()` whose child table holds the last reference to a sched_ext link | `sched_fork()` -> `scx_pre_fork()` (read side of `scx_fork_rwsem`), `exit_files()` -> `bpf_scx_unreg()` -> `scx_flush_disable_work()`, `scx_disable_workfn()` (write side), `sched_cancel_fork()`; "fork: release the files of a failed fork after sched_cancel_fork()" |
| `TtyHangup.tla` | a session leader holding the last open of its tty exits while a foreground job without tty descriptors is still in the session | `do_exit()`: `exit_files()` -> `tty_release()` -> `session_clear_tty()` versus `disassociate_ctty(1)` -> `tty_vhangup_session()` -> `__tty_hangup()` -> `tty_signal_session_leader()`; "exit: hang up the tty before closing the files" |

## What the models establish

**Walk order (`CloseOrder`).** TLC enumerates every dependency pattern
over three descriptors and runs the three disciplines side by side.

- `DescendingMatchesDeferredOnReleases` holds: for release dependencies
  the descending walk hangs exactly where the deferred puts hung.  That is
  the claim of the reordering patch, proven for every layout.
- `DescendingNoWorseThanDeferred` holds: with flush dependencies included
  the descending walk never hangs where the old order did not.
- `DescendingMatchesDeferred` fails, in the good direction: a `->flush()`
  that waits for a higher descriptor's release (a self-served FUSE file
  whose `/dev/fuse` sits above it) hung forever before, because every
  flush ran before any release; it completes now.
- `AscendingNoWorseThanDeferred` fails with the pipe-before-socket
  layout: a lower descriptor whose release waits for a higher one hangs
  in the merged ascending walk and did not before.  `AscendingMatchesDeferred`
  fails in both directions.

**vfork and exec (`VforkExec`).** With the inline put a vfork child that
execs holding the last reference to a file whose `->release()` needs the
parent hangs until the parent is killed (`VforkExec_sync_release`); the
deferred put let it through.  A `->flush()` that needs the parent hung
in both variants, since `->flush()` always ran in that window
(`VforkExec_deferred_flush`).  The exit route is safe in every variant
because `exit_mm()` releases the parent first.  The exec route is known
and was left as is: the same program hangs on every kernel if it uses
`close(2)` instead of close-on-exec.

**Fork failure (`ForkCleanup`).** With `exit_files()` before
`sched_cancel_fork()` the fork waits for the disable work and the disable
work waits for the fork's read side of `scx_fork_rwsem`
(`ForkCleanup_files_first`).  Dropping the read side first completes.

**tty hangup (`TtyHangup`).** With `exit_files()` first the last release
clears `signal->tty` for the session without a signal and
`disassociate_ctty(1)` then finds nothing to hang up
(`TtyHangup_files_first_tty`).  Hanging up first delivers SIGHUP; a pty is
unaffected in either order because the master keeps the slave's count
above zero.

## Results

| Configuration | Expected | Result | States |
|---|---|---|---|
| `CloseOrder_AscendingMatchesDeferred` | violation | violation | 12729 |
| `CloseOrder_AscendingNoWorseThanDeferred` | violation | violation | 12948 |
| `CloseOrder_DescendingMatchesDeferred` | violation | violation | 12241 |
| `CloseOrder_DescendingMatchesDeferredOnReleases` | pass | pass | 13755 |
| `CloseOrder_DescendingNoWorseThanDeferred` | pass | pass | 13755 |
| `ForkCleanup_cancel_first` | pass | pass | 8 |
| `ForkCleanup_files_first` | violation | violation | 4 |
| `TtyHangup_files_first_pty` | pass | pass | 3 |
| `TtyHangup_files_first_tty` | violation | violation | 3 |
| `TtyHangup_hangup_first_pty` | pass | pass | 3 |
| `TtyHangup_hangup_first_tty` | pass | pass | 3 |
| `VforkExec_deferred_flush` | violation | violation | 4 |
| `VforkExec_deferred_release` | pass | pass | 7 |
| `VforkExec_exit_route` | pass | pass | 5 |
| `VforkExec_sync_flush` | violation | violation | 4 |
| `VforkExec_sync_none` | pass | pass | 7 |
| `VforkExec_sync_release` | violation | violation | 5 |

The counterexamples are in `traces/`.

## Abstractions

- A dependency is a set of descriptors whose release must have completed
  before the operation returns; the task that provides the event (the
  peer holding the pipe mutex, the daemon, the driver) is not modelled,
  only the fact that releasing the other descriptor is what lets it
  proceed.  Self dependencies are excluded.
- `->flush()` runs once per descriptor at the point the code runs it
  (`filp_close()` in every discipline); the deferred discipline runs all
  flushes ascending in the walk and all releases descending from task
  work, which is what `task_work_run()`'s LIFO list does.
- `VforkExec` has one file and one operation that needs the parent;
  killing the parent is not modelled, so a hang shows up as a violated
  liveness property rather than a killable wait.
- `ForkCleanup` reduces `percpu_rw_semaphore` to a reader count and a
  writer flag and the kthread worker to a queued/running/done state.
- `TtyHangup` keeps `tty->count`, whether the session's `signal->tty`
  still points at the tty, whether `tty->ctrl.pgrp` is set and whether
  the job received SIGHUP; `tty_old_pgrp` is never set in this scenario.
