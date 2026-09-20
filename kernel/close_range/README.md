# TLA+ model of close_range() and the clone dup_fd() makes for it

Tree: `work.file.close_range_except` at e0bfe9dbba49 on top of
5dd1818b15d9, the series "files,close_range: add
CLOSE_RANGE_{CLOEXEC_ONLY,EXCEPT}".

The series makes `dup_fd()` leave the descriptors `close_range()` is
about to close behind instead of copying them and closing them again
from the clone, and adds CLOSE_RANGE_EXCEPT (act on everything outside
of the range) and CLOSE_RANGE_CLOEXEC_ONLY (act only on close-on-exec
descriptors).  What the series adds is bitmap arithmetic: which bits of
a word a range covers, the inversion and the close_on_exec mask on top
of it, the sizing of the clone, and a walk over the table that hops over
the window it keeps.  `FdTable.tla` writes that code down operator by
operator, next to what the flags are supposed to mean.  Three models use
it.

## Files

| File | What it is |
|------|------------|
| `FdTable.tla` | the descriptor table, one operator per helper of fs/file.c, the meaning of the flags, the properties of a clone |
| `CloseRange.tla` | every table of up to NWords words against every range and every flag combination, shared and private: the code refines the meaning |
| `RangeCloseRace.tla` | `__range_close()` walking a shared table while other threads open, install, close and re-flag descriptors and grow the table |
| `DupFdRace.tla` | `dup_fd()` copying a shared table against the lockless `fd_install()`, and against everything while it has the lock dropped to allocate |
| `*.cfg` | TLC configurations; the header says what to expect |
| `check.sh`, `check-all.sh`, `run-parallel.sh`, `summarize.sh` | run one, all, or all at once; results land in `logs/` |
| `extract-trace.sh`, `traces/` | the counterexamples of the configurations that are expected to fail |

## Running it

TLC ships in `tla2tools.jar` (https://github.com/tlaplus/tlaplus/releases,
version 2.19 was used).  Java 17 or newer.

    export TLA2TOOLS=/path/to/tla2tools.jar
    ./check.sh refine_new 16          # one configuration
    ./check-all.sh                    # every configuration, summary in logs/summary.txt

Everything but `race_fixed` and `refine_new_w4` finishes in minutes on a
laptop.  `race_fixed` explores the interleavings of the walk with liveness
over three-bit words and wants a big machine (`run-parallel.sh`,
`TLC_WORKERS`, `TLC_HEAP`); `race_fixed_w2` is the same walk over two-bit
words.

## What is in the model

A table is a function from descriptor numbers to slots.  A slot is the
open_fds bit, whether a struct file is installed, and the close_on_exec
bit.  `alloc_fd()` sets the open bit before `fd_install()` stores the
pointer, so a slot can be open without a file (claimed), and `close()`
leaves close_on_exec behind, so a closed slot can carry the bit.  The
refinement enumerates every such table of one or two words of W bits,
with W = 3 standing in for BITS_PER_LONG, and every range [fd, max_fd]
with fd <= max_fd over 0..2W and ~0U, for all twelve flag combinations
the syscall accepts, on a shared and on a private table.  The race
models start from every one-word table and let the table grow.

### Operators and the code they stand for

| Operator | Kernel |
|----------|--------|
| `FdRangeWord` | `fd_range_word()`: the GENMASK() of a range's bits in one word |
| `DupFdDroppedWord`, `DupFdDrops` | `dup_fd_dropped_word()`, `dup_fd_drops()`: the inversion for FD_RANGE_EXCEPT, the close_on_exec mask for FD_RANGE_CLOEXEC_ONLY |
| `SaneFdtableSizeNew`, `SaneFdtableSizeOld` | `sane_fdtable_size()` after and before the series |
| `DupFd` | `dup_fd()`: the size, `copy_fd_bitmaps()`, the copy loop with `get_file()` and `__clear_open_fd()`, full_fds_bits |
| `RangeCloexec` | `__range_cloexec()`: one or two `bitmap_set()` |
| `NextOpenFd`, `NextFdToClose` | `next_open_fd()`, `next_fd_to_close()` |
| `RangeClose` | `__range_close()` with nothing running next to it |
| `CloseRange` | `sys_close_range()`: the unshare, `drop = NULL` for CLOSE_RANGE_CLOEXEC, the close that is skipped after an unshare |
| `Selected`, `Meaning` | what the flags mean: the descriptors the call acts on, the table the caller ends up with |

### Actions of the race models

| Action | Kernel |
|--------|--------|
| `Start` | `__range_close()`: the bounds, computed once under file_lock |
| `Scan` | one iteration under file_lock: `next_fd_to_close()`, `file_close_fd_locked()` |
| `FilpClose` | `filp_close()` with the lock dropped |
| `Size` | `dup_fd()`: `sane_fdtable_size()` and `copy_fd_bitmaps()` under file_lock |
| `Alloc` | `alloc_fdtable()` with the lock dropped; the size is computed again afterwards |
| `Copy` | one slot of the copy loop: the pointer read, then `get_file()` or `__clear_open_fd()` |
| `Finish` | back in `sys_close_range()`: `__range_cloexec()` on the clone, or, before the series, `__range_close()` on it |
| `Open`, `Install`, `Close`, `SetFd`, `Grow` | the other threads: `alloc_fd()`, `fd_install()`, `close()`, `fcntl(F_SETFD)`, `expand_fdtable()` |

### Switches

| Constant | Meaning |
|----------|---------|
| `DROP_IN_DUP_FD` | TRUE is the series.  FALSE is the code before it: the punch_hole sizing, every descriptor the size covers copied and referenced, the range closed from the clone afterwards |
| `FIX_HOP` (`RangeCloseRace`) | FALSE takes the hop out of `next_fd_to_close()` |

### Properties

| Property | Meaning |
|----------|---------|
| `Refines` | the table the caller ends up with is what the flags mean, for every table, range and flag combination, shared or private |
| `CloneOK` | a clone has no file without an open bit and its full_fds_bits are exact |
| `NoRefOnDropped` | `dup_fd()` calls `get_file()` only on descriptors that make it into the clone |
| `Sized` | the clone reaches the last descriptor it carries over and nothing more |
| `ClosedOnlySelected` | every descriptor `__range_close()` closes is one the range and the flags select at that moment |
| `Bounded` | the bound computed at the start stays inside the table |
| `KeptCopied` | every descriptor that was installed and not dropped when the copy was sized is in the clone |
| `DroppedNotInClone` | nothing the range drops is in the clone |
| `CopiedAreFiles` | a copied slot points at a file that is in the table |
| `Terminates`, `Finishes` (liveness) | the walk and the copy end whatever the other threads do |

### Abstractions

- W = 3 bits per word in place of BITS_PER_LONG and tables of one or two
  words; `refine_new_w4` uses four-bit words, `refine_new_3w` three
  words of two bits.  ~0U is INF, which no table reaches.
- A slot beyond a table is free.  `alloc_fdtable()` hands out exactly the
  size the copy needs; what it rounds up to is free slots either way.
- No reference counts.  `refs` records the descriptors `get_file()` was
  called on.
- `->flush()`, dnotify and POSIX locks are not modelled.  The series only
  changes whether a clone ever holds the file at all.
- In `RangeCloseRace` the other threads may run between any two
  iterations of the walk, which is more than the kernel allows: it keeps
  the lock across an iteration that finds nothing to close and does not
  reschedule.
- In `DupFdRace` the other threads act only while the lock is dropped
  for `alloc_fdtable()`, except `fd_install()`, which is lockless and
  may act at any time until the clone is done.
- One `close_range()` at a time.  Two on the same table take the lock
  per iteration and do not interact in a new way.
- Memory is sequentially consistent.  Everything runs under file_lock
  except the `fd_install()` store, which the copy loop reads with
  `rcu_dereference_raw()`; the model reads whatever is there.

## Results

| Configuration | What it checks | Expected | Result | States | Time |
|---|---|---|---|---|---|
| `dupfd_new` | dup_fd() against the lockless fd_install() and the unlocked resize: CloneOK, NoRefOnDropped, KeptCopied, DroppedNotInClone, CopiedAreFiles, Finishes | pass | pass | 1071085 | 17s |
| `dupfd_old` | the code before the series: the same without NoRefOnDropped | pass | pass | 393408 | 09s |
| `dupfd_old_refs` | the code before the series: NoRefOnDropped | violation | violation | 238925 | 01s |
| `race_fixed_w2` | the same walk with two-bit words, the size that finishes in minutes | pass | pass | 1495584 | 27s |
| `race_no_hop` | the hop of next_fd_to_close() taken out: ClosedOnlySelected (the walk closes the kept window) | violation | violation | 95555 | 01s |
| `refine_new` | the series, all twelve flag combinations, every table of one or two words of three bits: Refines, CloneOK, NoRefOnDropped, Sized | pass | pass | 1734264 | 34s |
| `refine_new_3w` | the same over three words of two bits | pass | pass | 1775556 | 45s |
| `refine_new_w4` | the same over two words of four bits (1.7M tables, needs -maxSetSize) | pass | pass | 94131072 | 29min53s |
| `refine_old` | the code before the series with its two flags: Refines, CloneOK | pass | pass | 1734264 | 07s |
| `refine_old_refs` | the code before the series: NoRefOnDropped (the clone references what it then closes again) | violation | violation | 47796 | 01s |

## What the model says beyond the series

- The two "old" configurations show that the code before the series was
  correct for its flags (`refine_old`, `dupfd_old`) and that it took
  references it then dropped again (`refine_old_refs`,
  `dupfd_old_refs`): with descriptors 1 and 2 open and
  `close_range(0, 1, CLOSE_RANGE_UNSHARE)` the clone was sized to the
  word, descriptor 1 got a reference and was closed from the clone.
  That is what "file: let dup_fd() leave the punched hole behind" removes.
- Every table the refinement enumerates has stale close_on_exec bits on
  closed slots somewhere; no property depends on them, so the bits
  `close()` and the copy loop leave behind never matter.
- A claimed slot (open bit set, no file yet) is never copied and is
  cleared in the clone together with the full bit of its word.  The
  sizing counts it as carried over, so a clone can be a word larger than
  its files need.  `Sized` pins that down: the size is the last open
  descriptor that is not dropped, claimed or not.
- Without the hop (`race_no_hop`) the walk of CLOSE_RANGE_EXCEPT closes
  the first descriptor of the window it is supposed to keep.
