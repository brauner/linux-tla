#!/usr/bin/env python3
"""Generate the TLC configurations for the mount models: one green config
per layout with every fix on, one config per mutation with its fix off,
and the documentation check."""
import pathlib

FIXES = ["FIX_TRIM_ANCESTORS", "FIX_HANDLE_LOCKED", "FIX_REPARENT_LATE",
         "FIX_FIND_MASTER_STOP", "FIX_TUCK_LOCK", "FIX_PUT_MNT_NS_DISCONNECT",
         "FIX_CLONE_UNBINDABLE", "FIX_SET_GROUP_UNBINDABLE", "FIX_BUSY_VICTIMS"]
SAFETY = ["TypeOK", "AlgebraOK", "Structure", "IteratorsOK", "NsOK", "RefsOK",
          "CoverOK", "SyncUmountNotBusy", "BusyMirrorOK"]
WITNESSES = ["NoTuck", "NoLockTransfer", "NoReparent", "NoSlaveOfSlave",
             "NoSkippedMaster", "NoLockedKept", "NoConnected", "NoPutNs",
             "NoExpiry", "NoTrim", "NoCovers"]

LAYOUTS = {
    # name: (mount ids, namespace ids, MaxOps, MaxFds)
    "algebra": (6, 3, 4, 1),
    "small":   (6, 3, 4, 1),
    "chain":   (10, 3, 3, 1),
    "peers":   (8, 3, 3, 1),
    "locked":  (9, 3, 3, 1),
    "parentcand": (6, 2, 1, 1),   # scripted: the victim's parent is a candidate
}

# name: (layout, fixes off, invariants, expectation, overrides)
CONFIGS = {
    "algebra_smoke":            ("algebra", [], SAFETY + ["ReachOK"], "pass", {"ops": 3}),
    "algebra_fixed":            ("algebra", [], SAFETY, "pass", {}),
    "algebra_doc":              ("algebra", [], ["AlgebraOK"], "violation", {"doc": True}),
    "algebra_no_trim":          ("algebra", ["FIX_TRIM_ANCESTORS"], ["AlgebraOK", "Structure"], "violation", {}),
    "algebra_no_handle_locked": ("algebra", ["FIX_HANDLE_LOCKED"], ["AlgebraOK", "CoverOK"], "violation", {}),
    "algebra_reparent_early":   ("algebra", ["FIX_REPARENT_LATE"], ["AlgebraOK", "Structure"], "violation", {}),
    "algebra_find_master":      ("algebra", ["FIX_FIND_MASTER_STOP"], ["AlgebraOK"], "violation", {}),
    "algebra_tuck_no_lock":     ("algebra", ["FIX_TUCK_LOCK"], ["CoverOK"], "violation", {}),
    "algebra_put_ns_connected": ("algebra", ["FIX_PUT_MNT_NS_DISCONNECT"], SAFETY, "pass", {}),
}
for w in WITNESSES:
    CONFIGS["small_witness_" + w[2:].lower()] = ("small", [], [w], "violation", {})
for name in ["no_trim", "no_handle_locked", "reparent_early", "find_master", "tuck_no_lock", "doc"]:
    layout, off, invs, expect, over = CONFIGS["algebra_" + name]
    CONFIGS["small_" + name] = ("small", off, invs, expect, over)
CONFIGS["small_fixed"] = ("small", [], SAFETY, "pass", {})
# F1: clone_mnt() drops T_UNBINDABLE, so a copied namespace can bind what
# the original could not (sharedsubtree.rst 5g says the copy is unbindable)
CONFIGS["small_clone_unbindable"] = ("small", ["FIX_CLONE_UNBINDABLE"], ["AlgebraOK"], "violation", {"doc": True})
CONFIGS["locked_set_group_unbindable"] = ("locked", ["FIX_SET_GROUP_UNBINDABLE"], ["Structure"], "violation", {})
# F5: propagate_mount_busy() skips a copy with several children, but
# propagate_umount() pulls it out when they are victims plus one overmount
CONFIGS["locked_busy_victims"] = ("locked", ["FIX_BUSY_VICTIMS"], ["SyncUmountNotBusy"], "violation", {})
# the review's case: the victim's parent sits at the victim's mountpoint under
# a receiver and is a candidate itself; the victim is still its child when
# propagate_mount_busy() runs
CONFIGS["parentcand_fixed"] = ("parentcand", [], SAFETY, "pass", {})
CONFIGS["parentcand_busy_victims"] = ("parentcand", ["FIX_BUSY_VICTIMS"], ["SyncUmountNotBusy"], "violation", {})
CONFIGS["small_smoke"] = ("small", [], SAFETY + ["ReachOK"], "pass", {"ops": 3})
for lay in ["chain", "peers", "locked"]:
    CONFIGS[lay + "_fixed"] = (lay, [], SAFETY, "pass", {})
    CONFIGS[lay + "_doc"] = (lay, [], ["AlgebraOK"], "violation", {"doc": True})
for w in ["NoSlaveOfSlave", "NoSkippedMaster", "NoTuck"]:
    CONFIGS["chain_witness_" + w[2:].lower()] = ("chain", [], [w], "violation", {})
for name in ["no_trim", "no_handle_locked", "reparent_early", "find_master", "tuck_no_lock"]:
    layout, off, invs, expect, over = CONFIGS["algebra_" + name]
    CONFIGS["chain_" + name] = ("chain", off, invs, expect, over)
    CONFIGS["locked_" + name] = ("locked", off, invs, expect, over)
for w in ["NoLockedKept", "NoConnected", "NoCovers", "NoLockTransfer"]:
    CONFIGS["locked_witness_" + w[2:].lower()] = ("locked", [], [w], "violation", {})
# the chain layout has no locked mounts and the small one cannot reach a
# tuck under a locked mount within its budget: the locked layout shows it
CONFIGS["chain_tuck_no_lock"] = ("chain", ["FIX_TUCK_LOCK"], ["CoverOK"], "pass", {})
CONFIGS["small_tuck_no_lock"] = ("small", ["FIX_TUCK_LOCK"], ["CoverOK"], "pass", {})


# ---- MntPut: the reference count under lockless use ----------------------
PUT_FIXES = ["FIX_MB_LEGIT", "FIX_MB_UMOUNT", "FIX_MB_PUT", "FIX_RCU_DELAY",
             "FIX_PUT_RCU", "FIX_SYNC_FLAG", "FIX_DOOMED_FLAG"]
PUT_SAFETY = ["TypeOK", "Ledger", "NoUAF", "DoomedIsLast", "NoNegative", "SyncClean"]
PUT_LIVE = ["Freed", "AllDone"]
# name: (lazy, migrate, fixes off, invariants, properties, expectation)
PUT_CONFIGS = {
    "mntput_fixed":            (False, False, [], PUT_SAFETY, PUT_LIVE, "pass"),
    "mntput_fixed_lazy":       (True,  False, [], PUT_SAFETY, PUT_LIVE, "pass"),
    "mntput_torn_sum":         (False, True,  [], PUT_SAFETY, [], "violation: SyncClean, mnt_get_count() torn by a migrating mntget()/mntput() pair"),
    "mntput_torn_sum_lazy":    (True,  True,  [], PUT_SAFETY, PUT_LIVE, "pass"),
    "mntput_no_mb_legit":      (False, False, ["FIX_MB_LEGIT"], PUT_SAFETY, [], "violation: SyncClean"),
    "mntput_no_mb_legit_lazy": (True,  False, ["FIX_MB_LEGIT"], PUT_SAFETY, [], "violation: DoomedIsLast"),
    "mntput_no_mb_umount":     (False, False, ["FIX_MB_UMOUNT"], PUT_SAFETY, [], "violation: SyncClean"),
    "mntput_no_mb_put":        (True,  False, ["FIX_MB_PUT"], PUT_SAFETY, [], "violation: DoomedIsLast"),
    "mntput_no_rcu_delay":     (True,  False, ["FIX_RCU_DELAY"], PUT_SAFETY, PUT_LIVE, "violation: Freed (the mount leaks)"),
    "mntput_no_put_rcu":       (True,  False, ["FIX_PUT_RCU"], PUT_SAFETY, PUT_LIVE, "violation: Freed (the mount leaks)"),
    "mntput_no_sync_flag":     (False, False, ["FIX_SYNC_FLAG"], PUT_SAFETY, [], "violation: SyncClean, cleanup_mnt() from the walker"),
    "mntput_no_doomed_flag":   (True,  False, ["FIX_DOOMED_FLAG"], PUT_SAFETY, [], "violation: NoUAF"),
}


# ---- LockMount: do_lock_mount()/get_mountpoint() vs rmdir/d_invalidate --
LOCK_FIXES = ["FIX_RECHECK", "FIX_UNLINKED", "FIX_DONT_MOUNT", "FIX_LOOKUP_UNLINKED"]
LOCK_SAFETY = ["TypeOK", "HashUnique", "MountpointOK", "PinsUnderNsem", "NoUAF", "AttachOK", "NoOrphans", "Bounded"]
# name: (fixes off, invariants, properties, expectation)
LOCK_CONFIGS = {
    "lockmount_fixed":              ([], LOCK_SAFETY, [], "pass"),
    "lockmount_no_recheck":         (["FIX_RECHECK"], LOCK_SAFETY, [], "violation: NoUAF, the temporary reference is dropped under namespace_sem on a stale answer and the parent is freed before the attach"),
    "lockmount_no_unlinked":        (["FIX_UNLINKED"], LOCK_SAFETY, [], "pass: d_set_mounted() and d_invalidate()'s rounds cover it; the mount on the unlinked directory is detached again"),
    "lockmount_no_dont_mount":      (["FIX_DONT_MOUNT"], LOCK_SAFETY, [], "violation: AttachOK, a mount is attached on a removed directory (DCACHE_CANT_MOUNT)"),
    "lockmount_no_lookup_unlinked": (["FIX_LOOKUP_UNLINKED"], LOCK_SAFETY, [], "violation: Bounded, d_invalidate() loops forever (1e9c75fb9c47)"),
}


# ---- MntNs: the lifetime of a mount namespace -----------------------------
NS_FIXES = ["FIX_ACTIVE_CHECK", "FIX_TREE_FIRST", "FIX_CASCADE", "FIX_ACTIVE_FIRST",
            "FIX_EVICT_FIRST", "FIX_PASSIVE_RCU", "FIX_PUT_OUTSIDE_RCU"]
NS_SAFETY = ["TypeOK", "ActiveRef", "OwnerOK", "ProtocolOK", "Reaped"]
NS_CONFIGS = {
    "mntns_fixed":               ([], "pass"),
    "mntns_no_active_check":     (["FIX_ACTIVE_CHECK"], "violation: ProtocolOK, listns() hands out an inactive namespace"),
    "mntns_tree_after_rcu":      (["FIX_TREE_FIRST"], "violation: ProtocolOK, a lookup increments passive after the RCU callback freed the namespace"),
    "mntns_no_cascade":          (["FIX_CASCADE"], "violation: OwnerOK"),
    "mntns_ref_before_active":   (["FIX_ACTIVE_FIRST"], "violation: ActiveRef or ProtocolOK, the reference goes while the namespace counts as active"),
    "mntns_evict_ref_first":     (["FIX_EVICT_FIRST"], "violation: ActiveRef or ProtocolOK"),
    "mntns_no_passive_rcu":      (["FIX_PASSIVE_RCU"], "violation: ProtocolOK, use after free"),
    "mntns_put_in_rcu":          (["FIX_PUT_OUTSIDE_RCU"], "violation: ProtocolOK, the teardown sleeps under rcu_read_lock() (2ec2aff3c8e2)"),
}


# ---- MntWriters: WRITE_HOLD -----------------------------------------------
WR_FIXES = ["FIX_MB_GET", "FIX_MB_HOLD", "FIX_SBRO"]
WR_SAFETY = ["ReadOnlyOK", "DecisionOK", "Ledger", "HoldUnderLock"]
# name: (mode, fixes off, expectation)
WR_CONFIGS = {
    "mntwriters_fixed":       ("mnt", [], "pass"),
    "mntwriters_fixed_sb":    ("sb", [], "pass"),
    "mntwriters_no_mb_get":   ("mnt", ["FIX_MB_GET"], "violation: DecisionOK or ReadOnlyOK, the writer's increment is still buffered when the holder sums"),
    "mntwriters_no_mb_hold":  ("mnt", ["FIX_MB_HOLD"], "violation: DecisionOK or ReadOnlyOK, WRITE_HOLD is still buffered when the holder sums"),
    "mntwriters_no_sbro":     ("sb", ["FIX_SBRO"], "violation: ReadOnlyOK, a writer gets in between sb_prepare_remount_readonly() and SB_RDONLY"),
}


# ---- MountWalk: the RCU walk against mount/umount/move --------------------
MW_FIXES = ["FIX_RECHECK_MISS", "FIX_RECHECK_HOP", "FIX_RECHECK_DOTDOT", "FIX_SCOPED_EAGAIN", "FIX_RCU_FREE"]
MW_SAFETY = ["NoUAF", "RcuResultOK", "ScopedOK", "Bounded", "Ledger"]
# name: (layout, change, victim, mounts, fixes off, invariants, expectation)
MW_CONFIGS = {
    "mountwalk_fixed_mount":     ("mountwalk", "none", 2, 2, [], MW_SAFETY, "pass"),
    "mountwalk_fixed_umount":    ("mountwalk", "umount", 2, 2, [], MW_SAFETY, "pass"),
    "mountwalk_fixed_move":      ("mountwalk", "move", 2, 2, [], MW_SAFETY, "pass"),
    "mountwalk_no_recheck_dotdot": ("mountwalk", "move", 2, 2, ["FIX_RECHECK_DOTDOT"], MW_SAFETY, "violation: RcuResultOK, the climb through a mount being moved ends on a negative dentry where the walk should have succeeded (aed434ada685)"),
    "mountwalk_no_scoped_eagain": ("mountwalk", "move", 2, 2, ["FIX_SCOPED_EAGAIN"], MW_SAFETY, "pass: the final legitimization catches the escape here; the -EAGAIN exists for rename races and for the sinks"),
    "mountwalk_no_rcu_free":     ("mountwalk", "umount", 2, 2, ["FIX_RCU_FREE"], MW_SAFETY, "violation: NoUAF, the walker's mount is freed under it"),
    "mountwalk_witness_climb":   ("mountwalk", "none", 2, 2, [], ["NoClimb"], "violation"),
    "mountwalk2_fixed_move":     ("mountwalk2", "move", 3, 2, [], MW_SAFETY, "pass"),
    "mountwalk2_no_recheck_miss": ("mountwalk2", "move", 3, 2, ["FIX_RECHECK_MISS"], MW_SAFETY, "violation: RcuResultOK, a miss of __lookup_mnt() while an unrelated mount moves lets the walk go beneath the mount on A (b37199e626b3)"),
    "mountwalk2_no_recheck_hop": ("mountwalk2", "move", 2, 2, ["FIX_RECHECK_HOP"], MW_SAFETY, "pass: 20aac6c60981 needs a rename race, which the model does not have"),
    "mountwalk2_witness_miss":   ("mountwalk2", "move", 3, 2, [], ["NoMiss"], "violation"),
    "mountwalk2_witness_escape": ("mountwalk2", "umount", 2, 2, [], ["NoEscape"], "violation"),
}

here = pathlib.Path(__file__).resolve().parent
for name, (layout, off, invs, expect, over) in CONFIGS.items():
    nmnt, nns, ops, fds = LAYOUTS[layout]
    ops = over.get("ops", ops)
    lines = [f"\\* generated by gen-cfgs.py: layout {layout}, expected: {expect}",
             "SPECIFICATION Spec", "CONSTANTS",
             f"  MntIds = {{{', '.join(str(i) for i in range(1, nmnt + 1))}}}",
             f"  NsIds = {{{', '.join(str(i) for i in range(1, nns + 1))}}}",
             "  Sbs <- SbsDef", "  Dentries <- DentriesDef", "  DSb <- DSbDef",
             "  DParent <- DParentDef", "  SbRoot <- SbRootDef",
             "  Procs <- ProcsDef", "  ProcUser <- ProcUserDef",
             '  InitSb = "N"', '  RootSb = "R"', "  MountSbs <- MountSbsDef",
             f"  MaxOps = {ops}", f"  MaxFds = {fds}", "  Prelude <- PreludeDef"]
    for f in FIXES:
        lines.append(f"  {f} = {'FALSE' if f in off else 'TRUE'}")
    lines.append(f"  CHECK_DOC = {'TRUE' if over.get('doc') else 'FALSE'}")
    lines.append("INVARIANTS")
    lines += [f"  {i}" for i in invs]
    (here / f"{name}.cfg").write_text("\n".join(lines) + "\n")
for name, (lazy, migrate, off, invs, props, expect) in PUT_CONFIGS.items():
    lines = [f"\\* generated by gen-cfgs.py: MntPut, expected: {expect}",
             "SPECIFICATION Spec", "CONSTANTS",
             "  TaskList <- TaskListDef", '  Walkers = {"W1"}', '  Holders = {"H1"}',
             "  NCPU = 2", "  GetBudget = 1",
             f"  MIGRATE = {'TRUE' if migrate else 'FALSE'}", "  MigBudget = 2", f"  LAZY = {'TRUE' if lazy else 'FALSE'}"]
    for f in PUT_FIXES:
        lines.append(f"  {f} = {'FALSE' if f in off else 'TRUE'}")
    lines.append("INVARIANTS")
    lines += [f"  {i}" for i in invs]
    if props:
        lines.append("PROPERTIES")
        lines += [f"  {p}" for p in props]
    (here / f"{name}.cfg").write_text("\n".join(lines) + "\n")
for name, (off, invs, props, expect) in LOCK_CONFIGS.items():
    lines = [f"\\* generated by gen-cfgs.py: LockMount, expected: {expect}",
             "SPECIFICATION Spec", "CONSTANTS",
             "  Dentries <- DentriesDef", "  DParent <- DParentDef", '  NewRoot = "F"',
             "  MntIds = {1, 2, 3, 4, 5}", "  Roots <- RootsDef", '  Mounters = {"M1", "M2"}',
             "  MInfo <- MInfoDef", '  RmdirTarget = "A"', '  InvalTarget = "A"', "  UmountTarget = 3", "  MaxLoops = 6"]
    for f in LOCK_FIXES:
        lines.append(f"  {f} = {'FALSE' if f in off else 'TRUE'}")
    lines.append("INVARIANTS")
    lines += [f"  {i}" for i in invs]
    if props:
        lines.append("PROPERTIES")
        lines += [f"  {p}" for p in props]
    (here / f"{name}.cfg").write_text("\n".join(lines) + "\n")
for name, (off, expect) in NS_CONFIGS.items():
    lines = [f"\\* generated by gen-cfgs.py: MntNs, expected: {expect}", "SPECIFICATION Spec", "CONSTANTS"]
    for f in NS_FIXES:
        lines.append(f"  {f} = {'FALSE' if f in off else 'TRUE'}")
    lines.append("INVARIANTS")
    lines += [f"  {i}" for i in NS_SAFETY]
    (here / f"{name}.cfg").write_text("\n".join(lines) + "\n")
for name, (mode, off, expect) in WR_CONFIGS.items():
    lines = [f"\\* generated by gen-cfgs.py: MntWriters, expected: {expect}", "SPECIFICATION Spec", "CONSTANTS",
             '  Writers = {"W1", "W2"}', "  WCpu <- WCpuDef", "  NCPU = 2", f'  HMODE = "{mode}"']
    for f in WR_FIXES:
        lines.append(f"  {f} = {'FALSE' if f in off else 'TRUE'}")
    lines.append("INVARIANTS")
    lines += [f"  {i}" for i in WR_SAFETY]
    (here / f"{name}.cfg").write_text("\n".join(lines) + "\n")
for name, (layout, change, victim, mounts, off, invs, expect) in MW_CONFIGS.items():
    lines = [f"\\* generated by gen-cfgs.py: MountWalk ({layout}), expected: {expect}", "SPECIFICATION Spec", "CONSTANTS",
             "  Dentries <- DentriesDef", "  DParent <- DParentDef", "  DName <- DNameDef", "  DSb <- DSbDef", "  SbRoot <- SbRootDef",
             "  Negative <- NegativeDef", '  RootSb = "S"', '  NewSb = "F"', "  MntIds = {1, 2, 3}",
             '  Walkers = {"W1", "W2"}', "  WProg <- WProgDef", "  WRoot <- WRootDef", "  WScoped <- WScopedDef",
             "  MaxRestarts = 3", f"  Mounts = {mounts}", f'  CHANGE = "{change}"', f"  Victim = {victim}"]
    for f in MW_FIXES:
        lines.append(f"  {f} = {'FALSE' if f in off else 'TRUE'}")
    lines.append("INVARIANTS")
    lines += [f"  {i}" for i in invs]
    (here / f"{name}.cfg").write_text("\n".join(lines) + "\n")
print(f"{len(CONFIGS) + len(PUT_CONFIGS) + len(LOCK_CONFIGS) + len(NS_CONFIGS) + len(WR_CONFIGS) + len(MW_CONFIGS)} configurations written")
