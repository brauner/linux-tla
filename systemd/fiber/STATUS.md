# Status and how to resume

Working notes for whoever (or whichever session) picks this up.  README.md is
the write-up; this file is the progress log and the resume protocol.  Keep it
current: every step below is either done, running on jens, or next.

## Where things are

- Model, configurations, scripts: this directory, `~/src/git/linux-tla/systemd/fiber/`
  (laptop), mirrored to `jens:src/git/linux-tla/systemd/fiber/`.  Push with
  `rsync -a --exclude 'mount/' --exclude 'logs/' --exclude '*.jar' --exclude '.git/' ~/src/git/linux-tla/ jens:src/git/linux-tla/`,
  pull results with `rsync -a jens:src/git/linux-tla/systemd/fiber/logs/ ~/src/git/linux-tla/systemd/fiber/logs/`.
- TLC runs only on jens (512 cores, shared with other people's TLC jobs: never
  `pkill java`).  Jar: `jens:~/tmp/tla-coredump/tla2tools.jar`, copied to
  `tla2tools.jar` here (gitignored).  Java 25.
- Runs are detached (`setsid`) and checkpoint every 10 minutes into
  `/tmp/brauner-tlc-fiber/<cfg>/<timestamp>/` on jens (tmpfs: a reboot loses
  them, a disconnect does not).  `./status.sh` says pass / violation / running /
  dead (+ whether a checkpoint exists), `./resume.sh <cfg> [workers] [heap]`
  continues a dead run, `./run-parallel.sh [workers] [heap]` starts everything
  that has no verdict yet.
- The C side: worktree `~/src/git/systemd-worktrees/work.systemd.fiber`
  (branch `work.systemd.fiber`, base e96ff3b5b9 = upstream main).  Build and
  tests also on jens (see below).

## Progress log

- 2026-09-20 evening: code read (fiber.c, sd-future.c, event-future.c, fiber-io.c,
  bus-future.c, bus-objects.c, sd-varlink.c, main-func.c, io-util.c, sd-event.c
  dispatch rules, all tests).  Fiber.tla written; 36 configurations (`gen-cfgs.py`).
  Batch on jens: all 26 small configurations match their expectation (every
  `asis_*` finding reproduces, the ablations show which fix each property needs);
  the ten big `fixed_*`/`abl_no_awaitloop`/`abl_no_freepending` runs (10-100M
  states each) are still running detached (`./status.sh` on jens).  The model
  went through three artefact fixes (stale wakeSrc after a yield, budgets too
  small for the 4/5-operation scenarios, the spurious flag set on absorbed
  wakeups); nothing in the C code reading changed.
- Baseline `meson test` of the fiber/bus/varlink/qmp tests on jens
  (`~/src/git/systemd-fiber/build`, plain rsync of the worktree): 12/12 pass.
- 2026-09-20 ~21:00: all six fixes implemented on work.systemd.fiber as 12 commits
  (fix, test, fix, test, ...; tip 75855588dd on e96ff3b5b9, nothing pushed):
  89adec160d free of a pending future; 7f786c1199 fiber_await() wait loops;
  2b3246ed31 no completion trampoline on fiber futures; 5f8bd50488
  cancel_wait_unref waits + pending_result redelivery + stale value;
  38e2c9c03f exit source always armed; d49958e76a sticky error for a queued
  fiber + cancel of a running fiber. Order matters: the exit-source commit
  alone breaks test_fiber_nested_cancellation exactly as the model predicts
  (abl_no_cwuloop), so cancel_wait_unref comes first. Every new test was run
  against a pristine build of e96ff3b5b9 (`jens:src/git/systemd-fiber-orig`,
  `TESTFUNCS=<name> build/test-fiber`) and fails there the way the finding
  says. The 12 fiber/bus/varlink/qmp test binaries pass on the fixed tree
  (`jens:src/git/systemd-fiber/build`); a full `meson test` of the fixed
  tree runs detached, log in `build/test-all-fixed.log` there.
- ~21:10: README.md Findings + Beyond-the-code written; `traces/` holds the 21
  counterexamples of the finished violation configurations
  (`./extract-trace.sh`); one more commit 76d581a683 fixes the time base of
  the sleep test (ASan build `jens:src/git/systemd-fiber/build-asan` now
  passes all 12 fiber/bus/varlink/qmp tests; the user may want it folded into
  e77052d980). Still open: the results table (`./summarize.sh` on jens once
  the big runs are done, rsync logs/summary.txt back, `./fill-results.py
  --readme`, `cp logs/summary.txt RESULTS.txt`), the full `meson test` log.
- 20:53: every long TLC run on jens died with exit 143 (SIGTERM) at the moment
  another session restarted its mount-model batch; not OOM. Resumed from the
  20:45 checkpoints with `./resume.sh <cfg> 8 12g`. If it happens again, resume
  again; the verdicts are what count. A resume must use the same worker count
  as the run that wrote the checkpoint (TLC keeps one .chkpt per worker; with
  more workers it fails with FileNotFoundException on `MC_<cfg>-8.chkpt`); the
  heap may change. Worse: that failed attempt left the checkpoint's state queue
  unreadable ("Error: when reading the disk (StatePoolReader.run)"), so the six
  big runs were restarted from scratch at 21:12 with 32 workers/24g. Never kill
  a run to give it more workers; pick the worker count at start time.
- 21:29: those six runs filled jens's /tmp (tmpfs, 378G, shared with the other
  session's TLC jobs): 345G of state queues at ~140M distinct states each with
  tens of millions still queued, i.e. far from done. All eleven remaining runs
  died with "No space left on device" (StatePoolWriter). Whole-operation-set
  configurations with three or more operations per fiber are not feasible as a
  full BFS; they were replaced (gen-cfgs.py) by Budget=2 for the whole set plus
  scenario families (deadline, cancel, children, exit) with 3-4 operations and
  small liveness variants. Keep an eye on `du -sh /tmp/brauner-tlc-fiber`.
- 21:36: fixed_cancel_live found a livelock that is the model's unbounded
  MainCancel (main re-cancels the parent on every suspend, TLC always dispatches
  the parent's exit source before the child's): added `MainCancelMax` (0 =
  unbounded, 2 in the liveness configurations), clean rerun of all 39
  configurations with 16 workers/24g (`./run-parallel.sh 16 24g`).
- 21:56: fixed_deadline (3 fiber slots) and fixed_four_fibers (all operations)
  were heading past 150M distinct states with growing queues (74G/86G on /tmp):
  killed and shrunk (one child slot; five operations) and restarted. Rule of
  thumb from this batch: a configuration is feasible if "states left on queue"
  stops growing within the first few minutes; otherwise it will not finish.
- 22:45: the full `meson test` of the fixed tree (third attempt; the first two
  died in meson itself with "Unhandled python OSError", the default 512-way test
  parallelism against `ulimit -n 1024`; run with `ulimit -n 524288` and
  `--num-processes 96`): 1879 pass, 26 skipped, 5 fail. The five are the `dist`
  help/version checks (check-help-systemd, check-help-systemd-creds,
  check-help-systemctl, check-version-ukify, check-help-ukify) and fail the same
  way on the pristine tree in jens:src/git/systemd-fiber-orig: environmental.
  fixed_all_live was restarted without main's cancels (its graph was 3x
  fixed_all's 7.6M states) with a 48g heap; that is the last run.

## Findings so far (from reading; the model has to confirm each)

See README.md "Findings" once the runs are in.  Candidates:
1. `sd_future_free()` on a pending future calls `sd_future_resolve()`, which
   `sd_future_ref()`s an object with `n_ref == 0`: assertion.  Any error path
   that drops a pending future (sd_fiber_new() after sd_future_new(),
   future_new_io() when fcntl fails, bus_call_future() when
   sd_bus_call_async() fails, a wait future's set_ensure_put failing) aborts.
2. `sd_future_cancel_wait_unref()` returns after one resume, whatever resumed
   the fiber; if that was the fiber's own cancellation (exit, sibling, main)
   it unrefs the still-pending child: fiber_free() assertion (or 1.).
3. A fiber created on a fiber gets no exit source; once the loop is exiting
   nothing but a cancel via its parent drives it.  A child cancelled before
   the exit is stranded on its defer source; a floating child is never
   unwound at all.
4. The default fiber_resume_trampoline() on fiber futures created on a fiber:
   a child's completion resumes the parent out of whatever it waits on
   (sd_fiber_sleep() returns 0 early, sd_fiber_read() returns -EAGAIN, a
   child's error becomes the parent's sleep error); a floating child that
   outlives a floating parent resumes a freed fiber.
5. sd_fiber_resume() drops the result when the fiber is not SUSPENDED: an
   SD_FIBER_TIMEOUT deadline that fires while the fiber is queued (after a
   yield, or after another future resumed it) is lost, later waits in the
   scope are unbounded.
6. A cancellation delivered while the fiber waits in cancel_wait_unref() is
   swallowed (logged and ignored): the fiber carries on as if not cancelled.
7. A resume value stashed before a cancellation is not consumed by the
   -ECANCELED return and surfaces from a later sd_fiber_yield().

## Done (2026-09-20 23:06 UTC)

All 39 configurations match their expectation (`RESULTS.txt`, no MISMATCH), the
README results table is filled, `traces/` holds the 21 counterexamples, and the
full `meson test` of the fixed tree is in `FINISHED.txt` (1879 pass, 26 skipped,
5 environmental `dist` failures that fail identically on the pristine tree).
Nothing is running on jens any more. What is left is the user's: review the
series on work.systemd.fiber (tip b51ab4e6be, 19 commits, two `fixup!` commits
and one test time-base commit to fold), decide about the README review marker,
and whether the linux-tla work gets committed.

## If you are a fresh session picking this up

A detached `finish.sh` on jens waits for the last TLC run and the full
`meson test`, then writes `logs/summary.txt`, `RESULTS.txt`, `traces/`, fills
the README results table and writes `FINISHED.txt` with the test-suite
summary. So:

    ssh jens 'cat src/git/linux-tla/systemd/fiber/FINISHED.txt'     # exists = all done
    rsync -a --exclude '*.jar' jens:src/git/linux-tla/systemd/fiber/ ~/src/git/linux-tla/systemd/fiber/
    grep MISMATCH RESULTS.txt                                         # must be empty

If `FINISHED.txt` is missing, `ssh jens 'cd src/git/linux-tla/systemd/fiber && ./status.sh'`
tells what is still running or dead (`./resume.sh <cfg> 16 24g` for a dead one,
16 workers is what the batch was started with); `pgrep -f finish.sh` on jens
says whether the finisher is still waiting (restart it with
`setsid nohup ./finish.sh > logs/finish.out 2>&1 < /dev/null &`).
Then update the memory note (project_tla_fiber_model.md) and report.

## Next steps

1. Wait for the big runs (`./status.sh` on jens); if one died, `./resume.sh <cfg>`
   with the SAME worker count it was started with (32 for the six restarted at
   21:12, 8 for the five liveness runs).
2. `./summarize.sh` on jens, `rsync -a jens:src/git/linux-tla/systemd/fiber/logs/ logs/`,
   `./fill-results.py --readme`, `cp logs/summary.txt RESULTS.txt`. Findings,
   design assessment, beyond-the-code and `traces/` are done.
2b. Series on work.systemd.fiber, tip b51ab4e6be (19 commits): 8 fixes each followed
   by its test commit, 2 `fixup!` commits (overlong lines, for 7f786c1199 and
   5f8bd50488; not autosquashed on purpose), 76d581a683 (test time base, a fold
   candidate for e77052d980). The last two fixes (2a4d49719e a fiber owns itself
   while live, e00a9ff1ab waits refused once the loop exits) came from the user's
   question about remaining fundamental issues. README review marker uncommitted.
3. DONE (see the progress log). The plan was, in this order, each a commit,
   each followed by its test commit:
   1. sd_future_free() of a pending future: revive to n_ref 1, resolve, unref
      (FixFreePending).
   2. fiber_await()/fiber_await_any() in fiber.c: suspend until the given
      future resolves; a cancellation ends the wait with -ECANCELED, an
      interrupting future (SD_FIBER_TIMEOUT deadline, flag on sd_future set by
      sd_fiber_timeout()) or an external sd_fiber_resume() ends it with that
      value, any other wakeup is absorbed.  Used by sd_fiber_sleep(),
      sd_fiber_await(), fiber_io_operation(), sd_fiber_connect(),
      sd_fiber_ppoll(), event_run_suspend(), bus_call_suspend(),
      qmp_client (FixAwaitLoop).
   3. sd_fiber_new(): no fiber_resume_trampoline on the fiber's own future
      (FixNoChildTrampoline); cancel_wait_unref() always goes through a wait
      future.
   4. Exit source armed at creation for every fiber and re-armed whenever the
      defer source is (fiber_arm()), also by fiber_cancel() (FixExitArmed).
   5. sd_future_cancel_wait_unref(): wait until resolved; a cancellation or
      deadline consumed meanwhile lands in fiber->pending_result and is
      returned by the next sd_fiber_suspend()/yield()/fiber_await()
      (FixRecancel).  fiber_swap() on -ECANCELED also moves a stashed error
      there instead of leaving it for a later yield (asis_stale_yield).
   6. sd_fiber_resume() of a queued (READY, not running) fiber keeps an error
      over a stashed success (FixStickyError); a `running` flag on Fiber; a
      cancel of a running fiber is delivered at its next wait.
4. Build + `meson test -C build -v test-fiber test-fiber-io test-fiber-ops
   test-event-future test-bus-fiber test-main-func-fiber test-bus-chat
   test-bus-objects test-bus-server test-bus-watch-bind test-varlink
   test-qmp-client` on jens (rsync the worktree to jens:src/git/systemd-fiber).
5. Final full model batch, README tables, memory update.
