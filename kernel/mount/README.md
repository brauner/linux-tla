# TLA+ models of the mount code

Tree: master at 50d05c7c76c9 (v7.3-rc3) plus the staged revert of
put_mnt_ns() to `umount_tree(ns->root, 0)`; that revert is the
`FIX_PUT_MNT_NS_DISCONNECT` constant.  Files: fs/namespace.c, fs/pnode.c,
fs/mount.h, fs/pnode.h and the mount-crossing code of fs/namei.c.

Two families of models, as in `~/notes/work.tla.mount/PLAN.md`:

* **Family A, the propagation algebra** (this directory so far): one
  sequential state machine, one syscall per step, because every change to
  the tree runs under `namespace_sem`.  The algorithms of fs/pnode.c and
  the tree surgery of fs/namespace.c are transcribed as functions with
  the kernel's traversal orders, list insertion sides and marks; every
  step compares the result with a declarative specification and with the
  documentation, and the states the walks of an unprivileged process can
  reach are checked against what MNT_LOCKED mounts hid from it.
* **Family B, the lockless protocols**: `MntPut.tla` so far, the
  reference count of one mount under __legitimize_mnt(), do_umount() and
  the final mntput(), with per-CPU counters and TSO store buffers.  RCU
  path walk vs. tree changes, lock_mount, WRITE_HOLD and namespace
  lifetime are still to come.

## Files

| File | What it is |
|------|------------|
| `MountTree.tla` | the mount record (the struct mount fields the mount code reads), the constant dentry forest, `__lookup_mnt()`, `topmost_overmount()`, `next_mnt()` order, `next_peer()`/`next_slave()`/`propagation_next()`/`skip_propagation_subtree()`/`next_group()`, the declarative propagation set `RecvSet`, and the structural invariants |
| `Propagation.tla` | `clone_mnt()`, `copy_tree()`, `propagate_mnt()` with `need_secondary()`/`find_master()`, `attach_recursive_mnt()` with the tucking loop, `change_mnt_propagation()`/`transfer_propagation()`, `bulk_make_private()`, the 2025 `propagate_umount()` (`gather_candidates`, `trim_one`, `trim_ancestors`, `handle_locked`, `reparent`), `propagate_mount_unlock()`, `propagate_mount_busy()`, `umount_tree()`/`disconnect_mount()`; and the declarative side: `CopiesOK` (sharedsubtree.rst 5b/5d/5e), `ExpectedVictims` (propagate_umount.txt's maximal non-shifting, non-revealing subset), `UmountVictimsOK`, `DocUmountVictims` (sharedsubtree.rst 5f as written) |
| `MountOps.tla` | the syscalls as atomic actions, namespaces, processes with their references, the path walks a process can do, the lock covers, the epilogue of every action (final `mntput()`s, `put_mnt_ns()`), the invariants and the witnesses |
| `MC_algebra.tla`, `MC_small.tla` | layouts: superblocks, dentries, processes |
| `*.cfg` | TLC configurations from `gen-cfgs.py`; the header says what to expect |
| `check.sh`, `check-all.sh`, `run-parallel.sh`, `summarize.sh` | run one, all, or all at once |
| `show-trace.py` | print a counterexample from a log compactly |
| `MC_dbg.tla`, `dbg_trace.cfg` | a debugging template: script a scenario as a prelude with `MaxOps = 0`; the `PreludeDone` invariant fails after the last step and TLC prints every state |
| `MntPut.tla`, `MC_mntput.tla` | Family B: __legitimize_mnt(), mntput_no_expire() with its slow path, cleanup_mnt(), do_umount() (sync and MNT_DETACH), namespace_unlock(), mntget()/mntput() pairs of a task holding a reference, migration; per-CPU mnt_count summed CPU by CPU, TSO store buffers, RCU grace periods |
| `show-put-trace.py` | print a MntPut counterexample compactly |
| `LockMount.tla`, `MC_lockmount.tla` | Family B: do_lock_mount() (where_to_mount() under mount_lock, the temporary mntget(), inode_lock(), namespace_lock(), the second where_to_mount() and the -EAGAIN retry, cant_mount()/is_mounted()), get_mountpoint() with lookup_mountpoint()/d_set_mounted() and the -EBUSY retry, the pinned_mountpoint on m_list, do_add_mount()/attach_recursive_mnt(), unlock_mount(); against vfs_rmdir() (is_local_mountpoint() of its own namespace, dont_mount(), detach_mounts(), d_delete() after inode_unlock()), d_invalidate() (__d_drop() then detach_mounts() rounds), umount2(MNT_DETACH), namespace_unlock()'s puts and cleanup_mnt()'s put of stuck children; two namespaces sharing the dentries |
| `show-lock-trace.py` | print a LockMount counterexample compactly |
| `MountWalk.tla`, `MC_mountwalk.tla` | Family B: the RCU path walk (path_init(), __follow_mount_rcu() with __lookup_mnt()'s possible miss while a writer runs and the rechecks after a hop and a miss, follow_dotdot_rcu()/choose_mountpoint_rcu() with its recheck, step_into()'s -ENOENT on a negative dentry with no recheck, handle_dots()'s scoped -EAGAIN, complete_walk()'s legitimization, -ECHILD restarts in REF mode with lookup_mnt()/choose_mountpoint()) against a mounter (d_set_mounted(), then the write section), a lazy umount (unhash, DCACHE_MOUNTED cleared, synchronize_rcu(), the put that frees) and a move (unhash, new parent and mountpoint, rehash), each section one store per step |
| `show-walk-trace.py` | print a MountWalk counterexample compactly |
| `MntWriters.tla`, `MC_mntwriters.tla` | Family B: WRITE_HOLD, mnt_get_write_access() (per-CPU increment, smp_mb(), the spin on WRITE_HOLD, mnt_is_readonly() with s_readonly_remount) against mnt_make_readonly() and sb_prepare_remount_readonly() with the remount's SB_RDONLY and sb_end_ro_state_change(); TSO store buffers |
| `MntNs.tla`, `MC_mntns.tla` | Family B: the lifetime of one mount namespace under __ns_ref, __ns_ref_active (with the cascade to the owning user namespace) and the mount namespace's passive count; the task in it exiting (deactivate_nsproxy()), /proc/<pid>/ns/mnt files (mntns_get(), path_from_stashed(), nsfs_init_inode()'s resurrection, nsfs_evict()), listns() (ns_tree_lookup_rcu() + ns_get_unless_inactive()), NS_MNT_GET_NEXT (get_sequential_mnt_ns()), statmount() by id (lookup_mnt_ns(), namespace_sem shared, mnt_ns_release()), put_mnt_ns()'s teardown and free_mnt_ns() with the RCU-delayed passive drop |

## Actions and the kernel code they stand for

| Action | Kernel |
|--------|--------|
| `NewMount(p, pos, sb, auto)` | do_new_mount()/do_new_mount_fc()/do_add_mount()/graft_tree() -> attach_recursive_mnt(); `auto` is finish_automount()'s MNT_SHRINKABLE mount put on an expiry list |
| `Bind(p, src, dst, rec)` | do_loopback()/__do_loopback(): clone_mnt() or copy_tree(), __has_locked_children() for a non-recursive bind, may_copy_tree() |
| `Move(p, src, dst, beneath)` | do_move_mount(): attached source or root of an anonymous namespace, may_use_mount(), can_move_mount_beneath(), tree_contains_unbindable(), mount_is_ancestor(); do_lock_mount()'s choice of parent and mountpoint for MOVE_MOUNT_BENEATH |
| `Umount(p, m, mode)` | do_umount(): plain (shrink_submounts(), propagate_mount_busy(), umount_tree(UMOUNT_PROPAGATE\|UMOUNT_SYNC)), MNT_DETACH (umount_tree(UMOUNT_PROPAGATE)), MNT_EXPIRE (the count and expiry-mark handshake) |
| `ChangeType(p, m, type, rec)` | do_change_type(): may_change_propagation(), invent_group_ids(), change_mnt_propagation() |
| `SetGroup(p, from, to)` | do_set_group() (MOVE_MOUNT_SET_GROUP) |
| `CloneNs(p, empty)` | copy_mnt_ns(): CL_COPY_UNBINDABLE\|CL_EXPIRE, CL_SLAVE and lock_mnt_tree() across user namespaces, fs->root/pwd switched to the copies; CLONE_EMPTY_MNTNS |
| `OpenTree(p, pos, rec)` | open_tree(OPEN_TREE_CLONE)/get_detached_copy(): an anonymous namespace with seq_origin, referenced by a file |
| `Fsmount(p, sb)` | fsmount(): a new mount alone in an anonymous namespace |
| `OpenTreeNs(p, pos, rec, new, sb)` | open_tree(OPEN_TREE_NAMESPACE) and fsmount(FSMOUNT_NAMESPACE): create_new_namespace() with lock_mount_exact()'s copy of the nullfs root, MNT_LOCKED inherited from the old root's overmount stack, lock_mnt_tree() across user namespaces |
| `Setns(p, n)` | mntns_install(): root and pwd at the top of the namespace root's overmount stack |
| `CloseFd(p, f)` | __fput() -> dissolve_on_fput(): umount_tree(UMOUNT_CONNECTED) of an anonymous namespace root |
| `PivotRoot(p, new, putold)` | path_pivot_root(): every check, the MNT_LOCKED transfer to the new root, the two is_path_reachable() tests, chroot_fs_refs() |
| `Rmdir(p, pos)` | vfs_rmdir(): is_local_mountpoint() -> -EBUSY, else detach_mounts()/__detach_mounts() (UMOUNT_CONNECTED, already-unmounted mounts just unhashed) |
| `Expire` | mark_mounts_for_expiry(): mark, then unmount the marked ones that are not busy |
| `Touch(p, m)` | a path walk through m: mntput() clears mnt_expiry_mark |
| `Chdir`, `Chroot`, `OpenFd` | fs->pwd, fs->root, an open file: the references that make a mount busy and keep a detached tree alive |
| the epilogue of every action | namespace_unlock()'s mntput() of the disconnected mounts and the cascade of mntput_no_expire_slowpath()/cleanup_mnt() over stuck children (a detached mount nobody references goes), put_mnt_ns() when a namespace loses its last user |

Path walks (`Reachable`): a component step is `step_into()`/`handle_mounts()`
(cross into the mount on the dentry, then its overmount stack), `..` is
`follow_dotdot()` with `choose_mountpoint()` and `path_connected()`, the
process root stops the climb.  A process reaches everything from its
root, pwd and open files.

## Abstractions

* Dentries are a constant forest per superblock; every dentry is a
  directory; rmdir removes a leaf.  No renames.
* `struct mountpoint` is derived: it exists while a mount is attached at
  the dentry (d72c773237c0).
* Group ids and mount ids are allocated canonically (the smallest free
  one), so the state space carries no permutation copies.
* References: fs->root, fs->pwd and open files of the two processes.  A
  mount's count is one for itself while it is in a namespace or still
  connected to an unmounted parent, plus those references; that is what
  propagate_mount_busy() and the MNT_EXPIRE check see.  Children do not
  pin parents (493a4bebf515).
* No user namespaces beyond two: process `pi` lives in the initial one,
  process `pc` in a child; capability checks are `Capable(u, ns)`.
* No nsfs bind mounts, no automount transit, no MNT_LOCK_* attribute
  locks, no MNT_INTERNAL mounts, no allocation failures.
* The lock covers: when a mount becomes MNT_LOCKED, the (parent,
  mountpoint) it sits on is recorded for every process that could not
  already reach beneath it; the record outlives the mount's own lock so
  that a later reveal is caught.

## What is checked

| Invariant | Meaning |
|-----------|---------|
| `AlgebraOK` | every step's operational result equalled the declarative rule: `CopiesOK` after mount/bind/move (copies exactly at the receivers, the shape of the source, the receivers' propagation graph position by position), `UmountVictimsOK` after umount (the victims are the maximal non-revealing subset of the maximal non-shifting subset of tree plus cognates, survivors reparented to the first surviving ancestor, victims private, slaves of victims transferred to a surviving peer or up the master chain), the change-type table of sharedsubtree.rst 5e, where a recursive make-slave keeps a mount a slave only if a peer outside the tree survives or its master chain leaves the tree (`KeepsMaster`), the clone-namespace rules; with `CHECK_DOC` also sharedsubtree.rst 5f and 5g as written |
| `Structure` | one hashed mount per (parent, mountpoint); children lists and the overmount field; mountpoints under the parent's root; no cycles; T_SHARED iff a group id; peer rings; slave lists, one master per peer group, contiguous segments; unbindable is private; no marks left; MNT_UMOUNT means out of every namespace; a connected child of an unmounted mount is unmounted; MNT_LOCKED only with a parent |
| `IteratorsOK` | `propagation_next()` enumerates exactly `RecvSet` |
| `NsOK`, `RefsOK` | namespace roots attached, attached mounts in live namespaces, references to live mounts, detached mounts alive only while referenced |
| `CoverOK` | an unprivileged process never reaches a position a lock hid from it |
| `SyncUmountNotBusy` | a synchronous umount never takes a mount somebody references |

Witness configurations (`*_witness_*`, expected to fail) show that
tucking, lock transfer, reparenting, slave-of-slave copies, copies whose
nearest master received no copy, locked cognates kept, connected lazily
unmounted mounts, put_mnt_ns(), expiry, trimming and lock covers all
occur.

## Mutation toggles

| Constant | Off means |
|----------|-----------|
| `FIX_TRIM_ANCESTORS` | trim_ancestors() skipped: a candidate with a surviving descendant is taken (the non-shifting rule) |
| `FIX_HANDLE_LOCKED` | handle_locked() takes locked candidates whose parent stays (0c56fe31420c) |
| `FIX_REPARENT_LATE` | overmounts reparented before the victim set is final (570487d3faf2) |
| `FIX_FIND_MASTER_STOP` | find_master() does not stop at peers of the source (11933cf1d91d): a NULL dereference, recorded as a failed step |
| `FIX_TUCK_LOCK` | a mount slid under a locked one does not take over MNT_LOCKED (c62a4766937e) |
| `FIX_PUT_MNT_NS_DISCONNECT` | put_mnt_ns() keeps the tree connected (0342482a4d15) |
| `FIX_CLONE_UNBINDABLE` | clone_mnt() drops T_UNBINDABLE, as it does upstream since 406fea799925 (finding F1); the green configurations run with the fix, `small_clone_unbindable` shows the bug |
| `FIX_BUSY_VICTIMS` | propagate_mount_busy() only checks the references of copies without children and of copies covered by a single overmount, as upstream does (finding F5): since the 2025 propagate_umount() a copy whose children are victims themselves plus one overmount is pulled out too, so a synchronous umount succeeds with that copy still in use; the green configurations check every mount the umount would pull out, `locked_busy_victims` shows the bug |
| `FIX_SET_GROUP_UNBINDABLE` | do_set_group() accepts an unbindable target, as upstream does since 9ffb14ef61ba (finding F4): with a slave source the target ends up unbindable and a slave at once; the green configurations run with the fix, `locked_set_group_unbindable` shows the bug |

`MntPut.tla` (all constants are the pieces of the protocol, switched off one
by one):

| Constant | Off means |
|----------|-----------|
| `FIX_MB_LEGIT` | no smp_mb() between mnt_add_count() and the second read_seqretry() in __legitimize_mnt() |
| `FIX_MB_UMOUNT` | no smp_mb() before the refcount checks of a synchronous do_umount() (65781e19dcfc) |
| `FIX_MB_PUT` | no smp_mb() after lock_mount_hash() in mntput_no_expire_slowpath() |
| `FIX_RCU_DELAY` | namespace_unlock() drops the namespace's references without synchronize_rcu_expedited() |
| `FIX_PUT_RCU` | mntput_no_expire() tests mnt_ns outside rcu_read_lock() (9ea0a46ca2c3) |
| `FIX_SYNC_FLAG` | __legitimize_mnt() ignores MNT_SYNC_UMOUNT (48a066e72d97) |
| `FIX_DOOMED_FLAG` | __legitimize_mnt() ignores MNT_DOOMED (119e1ef80ecf, 250cf3693060) |
| `MIGRATE` | on: the holder migrates between CPUs, so its mntget()/mntput() pair can straddle mnt_get_count()'s loop |
| `LAZY` | umount2(MNT_DETACH) instead of a synchronous umount |

`LockMount.tla`:

| Constant | Off means |
|----------|-----------|
| `FIX_RECHECK` | do_lock_mount() does not repeat where_to_mount() after taking the locks (90006f21b78a) |
| `FIX_UNLINKED` | get_mountpoint() pins the mountpoint of an unlinked dentry instead of -ENOENT |
| `FIX_DONT_MOUNT` | do_lock_mount() ignores DCACHE_CANT_MOUNT |
| `FIX_LOOKUP_UNLINKED` | lookup_mountpoint() refuses an unlinked dentry, as before 1e9c75fb9c47 |
| `MaxLoops` | rounds of d_invalidate() and -EAGAIN retries of do_lock_mount() a task may take; `Bounded` stands in for liveness (TLC's fairness evaluation stalls on the d_invalidate() loop) |

What `LockMount.tla` checks: `HashUnique` (one hashed mount per parent
and mountpoint, ffdc52fbbd58), `MountpointOK` (DCACHE_MOUNTED exactly
while the struct mountpoint exists, but for the window between
d_set_mounted() and the insertion; the mountpoint exists exactly while
its m_list holds a mount or a pin), `PinsUnderNsem` (a pinned_mountpoint
exists only while its owner holds namespace_sem, which is what lets
__detach_mounts() treat everything after its own pin as a mount),
`NoUAF` (do_lock_mount()'s temporary reference, the chosen parent and
every parent pointer refer to live mounts), `AttachOK` (at attach time
the place is free, the parent mounted, the dentry a live mountpoint
pinned by this task and not dead), `NoOrphans` (once everything settled
no mount is hashed on an unlinked or removed dentry), `Bounded`, and
deadlock freedom (`TLC_DEADLOCK=check`).

`MntNs.tla`:

| Constant | Off means |
|----------|-----------|
| `FIX_ACTIVE_CHECK` | listns() takes a reference with ns_ref_get() instead of ns_get_unless_inactive() (56ea4e86832d) |
| `FIX_TREE_FIRST` | mnt_ns_tree_remove() queues the RCU callback before taking the namespace out of the tree |
| `FIX_CASCADE` | the active count does not cascade to the owning user namespace (3a18f809184b) |
| `FIX_ACTIVE_FIRST` | deactivate_nsproxy() drops the reference before the active count |
| `FIX_EVICT_FIRST` | nsfs_evict() drops the reference before the active count |
| `FIX_PASSIVE_RCU` | mnt_ns_release() runs at once instead of from the RCU callback |
| `FIX_PUT_OUTSIDE_RCU` | listns() drops its reference inside rcu_read_lock() (2ec2aff3c8e2) |

What `MntNs.tla` checks: `ActiveRef` (an active namespace is referenced,
the VFS_WARN_ON_ONCE in __ns_ref_put()), `OwnerOK` (the owner's active
count carries exactly one for N while N is active), `ProtocolOK` (no use
after free by a lookup, no passive increment on a namespace whose last
passive reference is gone, no teardown under rcu_read_lock(), no
listing of a namespace nobody uses), `Reaped` (once every task is done,
the RCU callback ran and no nsfs inode is left, the namespace is freed:
nothing leaks), and deadlock freedom.

`MntWriters.tla`:

| Constant | Off means |
|----------|-----------|
| `FIX_MB_GET` | no smp_mb() between this_cpu_inc(mnt_writers) and the WRITE_HOLD test |
| `FIX_MB_HOLD` | no smp_mb() between setting WRITE_HOLD and mnt_get_writers() |
| `FIX_SBRO` | mnt_is_readonly() does not test s_readonly_remount (d7439fb1f433) |
| `HMODE` | "mnt": mnt_make_readonly(); "sb": sb_prepare_remount_readonly() followed by the remount |

What `MntWriters.tla` checks: `ReadOnlyOK` (no writer holds write access
while MNT_READONLY, s_readonly_remount or SB_RDONLY is visible),
`DecisionOK` (the holder saw no writer only when there was none),
`Ledger`, `HoldUnderLock` (WRITE_HOLD is set only inside the holder's
mount_lock scope, 3371fa2f2713), and deadlock freedom (a writer spinning
forever would be one).  The smp_rmb()/smp_wmb() pairs are no-ops under
TSO and are left to the herd7 litmus tests.

`MountWalk.tla`:

| Constant | Off means |
|----------|-----------|
| `FIX_RECHECK_MISS` | no m_seq recheck after a miss of __lookup_mnt() (b37199e626b3) |
| `FIX_RECHECK_HOP` | no m_seq recheck after crossing into a mount (20aac6c60981) |
| `FIX_RECHECK_DOTDOT` | no m_seq recheck after choose_mountpoint_rcu() (aed434ada685) |
| `FIX_SCOPED_EAGAIN` | a scoped ".." does not recheck m_seq for -EAGAIN |
| `FIX_RCU_FREE` | the put after a lazy umount does not wait for the grace period |
| `CHANGE` | what happens to the first new mount: "none", "umount" or "move" |

What `MountWalk.tla` checks: `NoUAF` (a walker's current or final mount
is never freed), `RcuResultOK` (a walk that completed in RCU mode, and
the -ENOENT of a negative dentry that is returned without a recheck,
equal the sequential walk over the tree at that moment: 03fa86e9f79d's
contract), `ScopedOK` (a scoped walk never returns a path outside its
root), `Bounded` (restarts), `Ledger`, deadlock freedom; witnesses
`NoMiss`, `NoEscape` (the no-recheck arm taken while a writer runs) and
`NoClimb`.

What `MntPut.tla` checks: `Ledger` (the counters add up to the references),
`NoUAF` (nobody touches a freed mount), `DoomedIsLast` (MNT_DOOMED only
after the last reference), `NoNegative` (the WARN_ON in the slow path),
`SyncClean` (a synchronous umount that returned 0 left no reference but the
caller's, and the caller's own mntput() is the last one), `Freed` and
`AllDone` (liveness).

## Running

    export TLA2TOOLS=/path/to/tla2tools.jar
    ./check.sh small_witness_tuck      # one configuration
    ./check.sh mntput_torn_sum 4       # the MntPut configurations take seconds to minutes
    TLC_DEADLOCK=check ./check.sh lockmount_fixed 4   # LockMount, with deadlock detection
    TLC_DEADLOCK=check ./check.sh mntns_fixed 4       # MntNs, seconds
    TLC_DEADLOCK=check ./check.sh mntwriters_fixed 4  # MntWriters, seconds
    TLC_DEADLOCK=check ./check.sh mountwalk_fixed_move 6   # MountWalk, minutes
    ./start-batch.sh 8 32 16g          # everything, detached, 8 at a time

`check.sh` makes TLC checkpoint every ten minutes into the metadir and
resumes from the newest checkpoint when the same configuration is run
again (`TLC_RECOVER=no` to start over).  `start-batch.sh` runs the batch
under `setsid nohup`, so it survives the loss of the terminal; started
again after an interruption it skips the configurations that already have
a verdict in `logs/` and resumes the rest.  Progress is in `logs/*.log`
and `logs/batch.out`, the verdicts land in `logs/summary.txt`.

## Results

### MntPut (local runs, 2026-09-21)

| Configuration | Result | Meaning |
|---------------|--------|---------|
| `mntput_fixed`, `mntput_fixed_lazy`, `mntput_torn_sum_lazy` | pass | with every piece in place nothing is freed early, doomed early or leaked, and a synchronous umount that returns 0 leaves no reference behind |
| `mntput_torn_sum` | `SyncClean` violated | **F2**: the holder migrates between the two reads of mnt_get_count(): path_get() on the CPU already summed, path_put() (fast path, mnt_ns still set) on the CPU not yet summed; the sum comes out one short, the synchronous umount succeeds with an open file still referencing the mount and the filesystem is shut down later from that task's mntput().  The umount-side twin of 9ea0a46ca2c3, which moved only the mntput() side under mount_lock |
| `mntput_no_mb_legit`, `mntput_no_mb_umount` | `SyncClean` violated | the walker's increment or the umounter's seqcount bump stays in a store buffer: the walker legitimizes a mount that do_umount() found idle |
| `mntput_no_mb_put`, `mntput_no_mb_legit_lazy` | `DoomedIsLast` violated | the same store-buffer race against the final mntput(): MNT_DOOMED with a legitimized walker (119e1ef80ecf) |
| `mntput_no_sync_flag` | `SyncClean` violated | the walker's __legitimize_mnt() returns -1, its mntput() is the last one and cleanup_mnt() runs from the walker after umount(2) returned (48a066e72d97) |
| `mntput_no_doomed_flag` | `NoUAF` violated | the walker's mntput() touches the mount after the RCU callback freed it (250cf3693060) |
| `mntput_no_rcu_delay`, `mntput_no_put_rcu` | `Freed` violated | the holder's fast-path decrement lands after the namespace's slow-path put found the count non-zero: nobody frees the mount (9ea0a46ca2c3) |

### LockMount (local runs, 2026-09-21)

| Configuration | Result | Meaning |
|---------------|--------|---------|
| `lockmount_fixed`, `lockmount_no_unlinked` | pass | 29k states with deadlock detection; the -ENOENT for a mountpoint on an unlinked dentry in get_mountpoint() is redundant with d_set_mounted() and the detach rounds |
| `lockmount_no_recheck` | `NoUAF` violated | without the second where_to_mount() the mounter drops its temporary reference under namespace_sem on a stale answer, the lazily unmounted parent is freed, and attach_recursive_mnt() would use it |
| `lockmount_no_dont_mount` | `AttachOK` violated | a mount is attached on a directory vfs_rmdir() has already removed, between its inode_unlock() and d_delete() |
| `lockmount_no_lookup_unlinked` | `Bounded` violated | d_invalidate() never finds the mountpoint of the dentry it unhashed and loops forever (1e9c75fb9c47) |

### MntNs (local runs, 2026-09-21)

| Configuration | Result | Meaning |
|---------------|--------|---------|
| `mntns_fixed` | pass | 3.6k states with deadlock detection |
| `mntns_no_active_check` | `ProtocolOK` ("listed inactive") | listns() hands out a namespace no task or file uses, resurrecting it |
| `mntns_tree_after_rcu` | `ProtocolOK` ("use after free") | a lookup that started after call_rcu() still finds the namespace in the tree and increments a count in freed memory |
| `mntns_no_passive_rcu` | `ProtocolOK` ("use after free") | the same without the RCU delay of the initial passive reference |
| `mntns_put_in_rcu` | `ProtocolOK` ("sleep in rcu") | listns() drops the last reference under rcu_read_lock() and put_mnt_ns() takes namespace_sem there (2ec2aff3c8e2) |
| `mntns_no_cascade` | `OwnerOK` violated | the owner's active count no longer reflects an active child |
| `mntns_ref_before_active`, `mntns_evict_ref_first` | `ActiveRef` violated | the reference goes while the namespace still counts as active |

### MntWriters (local runs, 2026-09-21)

| Configuration | Result | Meaning |
|---------------|--------|---------|
| `mntwriters_fixed`, `mntwriters_fixed_sb` | pass | |
| `mntwriters_no_mb_get`, `mntwriters_no_mb_hold` | `ReadOnlyOK` violated | the store-buffer race between the writer's increment and the holder's WRITE_HOLD: the holder counts zero writers while one is about to write, and MNT_READONLY lands on a mount with an active writer |
| `mntwriters_no_sbro` | `ReadOnlyOK` violated | a writer that passes WRITE_HOLD after sb_prepare_remount_readonly() released it writes while the remount sets SB_RDONLY |

### MountWalk (local runs, 2026-09-21)

Two layouts: `MC_mountwalk` (W1 walks a, .., a from the root; W2 is scoped
at A and walks .., ..) and `MC_mountwalk2` (W1 walks a, a; W2 walks a, b);
the root filesystem has a negative "a" below A while the mounted one has a
positive "a" below its root, so a walk that ends up beneath a mount it
should have crossed gets -ENOENT where the right walk succeeds.

| Configuration | Result | Meaning |
|---------------|--------|---------|
| `mountwalk_fixed_mount`, `mountwalk_fixed_umount`, `mountwalk_fixed_move`, `mountwalk2_fixed_move` | pass | 0.2M, 1.5M, 2.4M and 2.8M states with deadlock detection; every RCU result equals the sequential walk over the tree it was validated against, every unvalidated -ENOENT equals the sequential walk at some instant of the walk, no scoped walk escapes, nothing is used after free |
| `mountwalk2_no_recheck_miss` | `RcuResultOK` violated | __lookup_mnt() misses while an unrelated mount's write section runs, the walk goes beneath the mount on A and returns -ENOENT for a path that succeeds at every instant (b37199e626b3) |
| `mountwalk_no_recheck_dotdot` | `RcuResultOK` violated | choose_mountpoint_rcu() reads the parent and mountpoint of a mount in the middle of a move, climbs to the wrong directory and returns -ENOENT where the walk succeeds before and after the move (aed434ada685) |
| `mountwalk_no_rcu_free` | `NoUAF` violated | the put after a lazy umount frees the mount a walker still holds in RCU mode |
| `mountwalk2_no_recheck_hop` | pass | 20aac6c60981's race needs a concurrent rename (RENAME_EXCHANGE), which the model does not have |
| `mountwalk_no_scoped_eagain` | pass | with mounts alone the final legitimization catches a scoped ".." that crossed a moved mount; the -EAGAIN is for rename races and for the unvalidated exits |
| `mountwalk_witness_miss`, `mountwalk2_witness_escape`, `mountwalk_witness_climb` | witnesses fire | the miss, the no-recheck arm during a write section and the climb through a mountpoint all occur |

### Documentation (the `*_doc` configurations)

Where Documentation/filesystems/sharedsubtree.rst and the code disagree,
in the order the model finds them:

1. **5g, unbindable mounts in a cloned namespace** -- the copy is not
   unbindable in the kernel (clone_mnt() drops T_UNBINDABLE since
   406fea799925, finding F1).  The green configurations run with the
   fix; `small_clone_unbindable` shows the bug.
2. **5f describes one mount without sub-mounts.**  For a tree, every
   mount of it propagates its unmount from its own parent; the model
   applies the rule per mount.
3. **5f's "does not have sub-mounts within them"** is the pre-2025 rule.
   Since the propagate_umount() rewrite a cognate goes when all of its
   sub-mounts go with it (the non-shifting rule of
   Documentation/filesystems/propagate_umount.txt); `peers_doc` stops
   there: a bind on top of a propagated mount, then a lazy umount of the
   tree in the other namespace, takes both copies.  sharedsubtree.rst
   needs an update.
4. **5e's footnote on make-slave** covers a shared mount alone in its
   peer group.  The code generalises it: a recursive make-slave over a
   tree that contains the whole peer group ends with every member
   private, because change_mnt_propagation() runs mount by mount and the
   last member has nobody left to be a slave of (the same result as the
   pre-2025 do_make_slave()).  The model's expected table follows the
   code (`KeepsMaster`); the first `chain_fixed`, `locked_fixed` and
   `peers_fixed` runs stopped on it.
5. **5d and a move onto the mount's own peer group.**  Moving a shared
   mount onto a mount of its own peer group is allowed (the parent it
   leaves is private, the destination is not below it) and the move
   propagates like any other mount at the destination: every peer and
   slave of the destination receives a copy at the same place, and the
   moved mount is one of those peers, so a copy of it lands on its own
   root.  Confirmed on a running kernel with `mount --move`; the
   declarative rule (`CopiesOK`) keeps that copy out of the shape of
   the moved tree.

### Propagation algebra (jens, 2026-09-21)

Every fix on, every safety invariant including `BusyMirrorOK`:

| Configuration | Result | States |
|---------------|--------|--------|
| `peers_fixed` (MaxOps 3) | pass | 59,631 |
| `locked_fixed` (MaxOps 3) | pass | 191,799 |
| `chain_fixed` (MaxOps 3) | pass | 359,356 |
| `small_smoke` (MaxOps 3, plus `ReachOK`) | pass | 98,492 |
| `algebra_smoke` (MaxOps 3) | running | |
| `small_fixed`, `algebra_fixed`, `algebra_*` mutations (MaxOps 4) | not feasible: the algebra layout sat at BFS depth 5 for 13 hours at ~6k states/min | |

Before the model's own expectations were corrected the green runs
stopped three times, each time on the kernel's behaviour: the recursive
make-slave whose peer group lies inside the tree (doc item 4), the move
onto the mount's own peer group (doc item 5), and the stale overmount
pointer of a mount that propagate_umount() pulled out (`ChildrenOK` now
skips unmounted mounts).  Two stops were kernel bugs, F4 and F5 below.

One fix off at a time:

| Configuration | Result | Meaning |
|---------------|--------|---------|
| `*_no_trim`, `*_no_handle_locked`, `*_reparent_early`, `*_find_master` (chain, locked, small) | `AlgebraOK` violated | the pre-2025 umount propagation bugs and the find_master() stop, each within seconds to an hour |
| `locked_tuck_no_lock` | `CoverOK` violated | a tuck under a locked mount without the lock transfer of c62a4766937e uncovers it; `chain_tuck_no_lock`, `small_tuck_no_lock` pass (no locked mount to uncover, 361k and 3.2M states) |
| `small_clone_unbindable` | `AlgebraOK` violated | **F1**: clone_mnt() drops T_UNBINDABLE, the copied namespace can bind what the original could not (fixed on `work.mount.unbindable_clone`) |
| `locked_set_group_unbindable` | `Structure` violated | **F4**: do_set_group() takes an unbindable target; with a slave source the target ends up unbindable and a slave at once, reproduced on 7.1.12 (fixed on `work.move_mount.set_group_unbindable`) |
| `locked_busy_victims` | `SyncUmountNotBusy` violated | **F5**: propagate_mount_busy() skips a copy with several children, propagate_umount() pulls it out when they are victims plus one overmount, so a synchronous umount succeeds with the copy still referenced, reproduced on 7.1.12 (fixed on `work.umount.busy_victims`; the green runs use the fix's rule and `BusyMirrorOK` checks it against the exact victim set) |
| `*_doc` | `AlgebraOK` violated | sharedsubtree.rst as written, see the documentation items below |
| `chain_witness_*`, `locked_witness_*`, `small_witness_*` | witnesses fire | tucks, lock transfers, reparenting, slaves of slaves, skipped masters, expiry, covers, connected and kept locked mounts all occur |

`small_witness_connected` and `small_witness_lockedkept` (MaxOps 4) ran
for 10 hours without firing; the locked layout shows both.
