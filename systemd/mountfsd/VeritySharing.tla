--------------------------- MODULE VeritySharing ---------------------------
(***************************************************************************)
(* systemd-mountfsd workers mounting the same dm-verity image at the same  *)
(* time (veritySharing=true): the shared device-mapper device named after  *)
(* the root hash, the kernel's deferred removal of it, udev's creation and *)
(* removal of its /dev/mapper symlink, the mounts that keep it open, and   *)
(* the retry loop of verity_partition() that reuses, waits, re-arms and    *)
(* falls back to a private device.                                         *)
(*                                                                         *)
(* Tree: systemd v262-rc2-60-ge96ff3b5b9.                                  *)
(*                                                                         *)
(* Modelled code:                                                          *)
(*   src/shared/dissect-image.c  verity_partition (the attempt loop:       *)
(*                     open(), crypt_activate, dm_deferred_remove_cancel,  *)
(*                     verity_can_reuse, device_wait_for_devlink, the      *)
(*                     restore_deferred_remove cleanup, the fallback       *)
(*                     without DISSECT_IMAGE_VERITY_SHARE),                *)
(*                     decrypted_image_free (CRYPT_DEACTIVATE_DEFERRED once *)
(*                     the worker is done with its DissectedImage)         *)
(*   src/shared/dm-util.c  dm_deferred_remove_cancel (DM_TARGET_MSG        *)
(*                     "@cancel_deferred_remove")                          *)
(*   src/mountfsd/mountwork.c  vl_method_mount_image: the fsmount fd handed*)
(*                     to the client is what keeps the device open         *)
(*   kernel drivers/md/dm.c, dm-ioctl.c  dm_blk_open (ENXIO while          *)
(*                     DMF_DELETING), dm_blk_close (last close with        *)
(*                     DMF_DEFERRED_REMOVE queues the removal), dev_remove *)
(*                     with DM_DEFERRED_REMOVE (open: mark, else delete    *)
(*                     now), dm_cancel_deferred_remove (EBUSY while        *)
(*                     deleting), dm_deferred_remove()                     *)
(*   udev             the symlink appears after the add uevent and goes    *)
(*                     after the remove uevent, both asynchronously        *)
(*                                                                         *)
(* Switches:                                                               *)
(*   FIX_CANCEL_DEFERRED   dm_deferred_remove_cancel() before reusing      *)
(*   FIX_RESTORE_DEFERRED  the restore_deferred_remove cleanup re-arms     *)
(*                         removal when an attempt fails                   *)
(*   UDEV_SYNC             libdevmapper's udev cookie: the activation      *)
(*                         returns once udev created the symlink (deferred *)
(*                         removals carry no cookie, their symlink goes    *)
(*                         asynchronously)                                 *)
(*   WorkerMayDie          a worker is killed in the middle of an attempt  *)
(*                                                                         *)
(* Abstractions:                                                           *)
(*   - One image, one root hash, hence one shared device name; every       *)
(*     worker asks for the same hash, so verity_can_reuse() only fails on  *)
(*     a device that is going away.                                        *)
(*   - Activation either creates the device or fails with EEXIST/EBUSY;    *)
(*     the EINVAL and ENODEV quirks of libcryptsetup are not modelled.     *)
(*   - Removal is one step from DMF_DELETING to gone.  udev handles one    *)
(*     event per step and may take arbitrarily long, which is what the     *)
(*     devlink timeout is for.                                             *)
(*   - A successful worker hands one mount to its client, which the        *)
(*     client unmounts whenever it likes.  The private device of the       *)
(*     fallback path is not modelled.                                      *)
(*   - Attempts bounds the attempt loop (N_DEVICE_NODE_LIST_ATTEMPTS).     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Workers,
    Attempts,
    WorkerMayDie,
    UDEV_SYNC,            \* libdevmapper waits for udev before activation returns
    FIX_CANCEL_DEFERRED,
    FIX_RESTORE_DEFERRED

ASSUME Attempts \in Nat /\ Attempts >= 1

Done == {"done", "done_unique", "dead"}

VARIABLES
    dev,        \* the shared device: "absent", "active", "deleting"
    open,       \* its open count
    deferred,   \* DMF_DEFERRED_REMOVE
    udevq,      \* pending uevents: "add" / "remove"
    devlink,    \* /dev/mapper/<name> exists
    pc,         \* [Workers -> program counter]
    fd,         \* [Workers -> BOOLEAN]: holds an fd on the device
    restore,    \* [Workers -> BOOLEAN]: restore_deferred_remove is set
    attempt,    \* [Workers -> Nat]
    mount       \* [Workers -> BOOLEAN]: the client holds the mount

vars == <<dev, open, deferred, udevq, devlink, pc, fd, restore, attempt, mount>>
Dev  == <<dev, open, deferred, udevq, devlink>>

(***************************************************************************)
(* The kernel and udev                                                     *)
(***************************************************************************)
\* dev_remove with DM_DEFERRED_REMOVE: open devices are marked, others go now
Deactivate(d, o, df, q) ==
    IF d # "active" THEN [dev |-> d, deferred |-> df, udevq |-> q]
    ELSE IF o > 0 THEN [dev |-> d, deferred |-> TRUE, udevq |-> q]
    ELSE [dev |-> "deleting", deferred |-> df, udevq |-> q]

\* dm_blk_close: the last close of a marked device queues its removal
Close(d, o, df) ==
    IF o = 1 /\ df /\ d = "active" THEN [dev |-> "deleting", open |-> 0]
    ELSE [dev |-> d, open |-> o - 1]

\* dm_deferred_remove(): the device is gone, udev is told
RemoveWork ==
    /\ dev = "deleting"
    /\ dev' = "absent"
    /\ deferred' = FALSE
    /\ udevq' = Append(udevq, "remove")
    /\ UNCHANGED <<open, devlink, pc, fd, restore, attempt, mount>>

\* udev processes the next event
Udev ==
    /\ udevq # <<>>
    /\ devlink' = (Head(udevq) = "add")
    /\ udevq' = Tail(udevq)
    /\ UNCHANGED <<dev, open, deferred, pc, fd, restore, attempt, mount>>

\* the client unmounts: the mount's reference goes away
Umount(w) ==
    /\ mount[w]
    /\ LET c == Close(dev, open, deferred) IN
       /\ dev' = c.dev /\ open' = c.open
    /\ mount' = [mount EXCEPT ![w] = FALSE]
    /\ UNCHANGED <<deferred, udevq, devlink, pc, fd, restore, attempt>>

(***************************************************************************)
(* verity_partition(), one worker                                          *)
(***************************************************************************)
\* the cleanup at the end of a failed attempt: the fd is closed first (it
\* is declared last), then restore_deferred_remove re-arms removal
CleanupDev(w, d, o, df, q) ==
    LET c == IF fd[w] THEN Close(d, o, df) ELSE [dev |-> d, open |-> o]
        r == IF restore[w] /\ FIX_RESTORE_DEFERRED THEN Deactivate(c.dev, c.open, df, q)
             ELSE [dev |-> c.dev, deferred |-> df, udevq |-> q]
    IN [dev |-> r.dev, open |-> c.open, deferred |-> r.deferred, udevq |-> r.udevq]

Start(w) ==
    /\ pc[w] = "idle"
    /\ pc' = [pc EXCEPT ![w] = "loop"]
    /\ attempt' = [attempt EXCEPT ![w] = 0]
    /\ fd' = [fd EXCEPT ![w] = FALSE]
    /\ restore' = [restore EXCEPT ![w] = FALSE]
    /\ UNCHANGED <<Dev, mount>>

\* top of the loop: open the node; ENOENT/ENXIO means "activate it"
Loop(w) ==
    /\ pc[w] = "loop"
    /\ IF attempt[w] >= Attempts
       THEN pc' = [pc EXCEPT ![w] = "fallback"] /\ UNCHANGED <<open, fd>>
       ELSE IF devlink /\ dev = "active"
       THEN /\ open' = open + 1
            /\ fd' = [fd EXCEPT ![w] = TRUE]
            /\ pc' = [pc EXCEPT ![w] = "check"]
       ELSE pc' = [pc EXCEPT ![w] = "activate"] /\ UNCHANGED <<open, fd>>
    /\ UNCHANGED <<dev, deferred, udevq, devlink, restore, attempt, mount>>

\* do_crypt_activate_verity(): created, or EEXIST/EBUSY because it exists.
\* With the udev cookie the earlier events of the name and the add are
\* processed before the call returns.
Activate(w) ==
    /\ pc[w] = "activate"
    /\ IF dev = "absent"
       THEN /\ dev' = "active" /\ open' = 0 /\ deferred' = FALSE
            /\ udevq' = IF UDEV_SYNC THEN <<>> ELSE Append(udevq, "add")
            /\ devlink' = IF UDEV_SYNC THEN TRUE ELSE devlink
            /\ pc' = [pc EXCEPT ![w] = "try_open"]
       ELSE /\ pc' = [pc EXCEPT ![w] = "check"]
            /\ UNCHANGED <<dev, open, deferred, udevq, devlink>>
    /\ UNCHANGED <<fd, restore, attempt, mount>>

\* dm_deferred_remove_cancel(): EBUSY/ENXIO on a device going or gone
Check(w) ==
    /\ pc[w] = "check"
    /\ IF dev # "active"
       THEN pc' = [pc EXCEPT ![w] = "again"] /\ UNCHANGED <<deferred, restore>>
       ELSE /\ deferred' = IF FIX_CANCEL_DEFERRED THEN FALSE ELSE deferred
            /\ restore' = [restore EXCEPT ![w] = TRUE]
            /\ pc' = [pc EXCEPT ![w] = "reuse"]
    /\ UNCHANGED <<dev, open, udevq, devlink, fd, attempt, mount>>

\* verity_can_reuse(): crypt_init_by_name() and the root hash comparison
Reuse(w) ==
    /\ pc[w] = "reuse"
    /\ pc' = [pc EXCEPT ![w] = IF dev # "active" THEN "again"
                               ELSE IF fd[w] THEN "opened" ELSE "waitlink"]
    /\ UNCHANGED <<Dev, fd, restore, attempt, mount>>

\* device_wait_for_devlink(): the symlink appears, or the timeout falls back
WaitLink(w) ==
    /\ pc[w] = "waitlink"
    /\ \/ devlink /\ pc' = [pc EXCEPT ![w] = "try_open"]
       \/ pc' = [pc EXCEPT ![w] = "fallback"]
    /\ UNCHANGED <<Dev, fd, restore, attempt, mount>>

\* the open after activation or after the devlink appeared
TryOpen(w) ==
    /\ pc[w] = "try_open"
    /\ IF devlink /\ dev = "active"
       THEN /\ open' = open + 1
            /\ fd' = [fd EXCEPT ![w] = TRUE]
            /\ pc' = [pc EXCEPT ![w] = "opened"]
       ELSE pc' = [pc EXCEPT ![w] = "again"] /\ UNCHANGED <<open, fd>>
    /\ UNCHANGED <<dev, deferred, udevq, devlink, restore, attempt, mount>>

\* success: the mount is created and handed to the client, the worker's own
\* fd and DissectedImage go away, which marks the device for removal once
\* the mount is gone
Opened(w) ==
    /\ pc[w] = "opened"
    /\ LET o1 == open + 1                     \* the mount
           c  == Close(dev, o1, deferred)     \* the worker's fd
           r  == Deactivate(c.dev, c.open, deferred, udevq)  \* decrypted_image_free()
       IN /\ dev' = r.dev /\ open' = c.open /\ deferred' = r.deferred /\ udevq' = r.udevq
    /\ fd' = [fd EXCEPT ![w] = FALSE]
    /\ restore' = [restore EXCEPT ![w] = FALSE]
    /\ mount' = [mount EXCEPT ![w] = TRUE]
    /\ pc' = [pc EXCEPT ![w] = "done"]
    /\ UNCHANGED <<devlink, attempt>>

\* try_again: the attempt's cleanup, then the next one
Again(w) ==
    /\ pc[w] = "again"
    /\ LET c == CleanupDev(w, dev, open, deferred, udevq) IN
       /\ dev' = c.dev /\ open' = c.open /\ deferred' = c.deferred /\ udevq' = c.udevq
    /\ fd' = [fd EXCEPT ![w] = FALSE]
    /\ restore' = [restore EXCEPT ![w] = FALSE]
    /\ attempt' = [attempt EXCEPT ![w] = @ + 1]
    /\ pc' = [pc EXCEPT ![w] = "loop"]
    /\ UNCHANGED <<devlink, mount>>

\* the attempts are used up or the devlink took too long: activate with a
\* unique name instead (not modelled further)
Fallback(w) ==
    /\ pc[w] = "fallback"
    /\ LET c == CleanupDev(w, dev, open, deferred, udevq) IN
       /\ dev' = c.dev /\ open' = c.open /\ deferred' = c.deferred /\ udevq' = c.udevq
    /\ fd' = [fd EXCEPT ![w] = FALSE]
    /\ restore' = [restore EXCEPT ![w] = FALSE]
    /\ pc' = [pc EXCEPT ![w] = "done_unique"]
    /\ UNCHANGED <<devlink, attempt, mount>>

\* the worker is killed: its fd is closed by the kernel, nothing else runs
Die(w) ==
    /\ WorkerMayDie
    /\ pc[w] \notin Done \cup {"idle"}
    /\ LET c == IF fd[w] THEN Close(dev, open, deferred) ELSE [dev |-> dev, open |-> open] IN
       /\ dev' = c.dev /\ open' = c.open
    /\ fd' = [fd EXCEPT ![w] = FALSE]
    /\ pc' = [pc EXCEPT ![w] = "dead"]
    /\ UNCHANGED <<deferred, udevq, devlink, restore, attempt, mount>>

WorkerStep(w) ==
    Start(w) \/ Loop(w) \/ Activate(w) \/ Check(w) \/ Reuse(w) \/ WaitLink(w)
    \/ TryOpen(w) \/ Opened(w) \/ Again(w) \/ Fallback(w)

(***************************************************************************)
(* The specification                                                       *)
(***************************************************************************)
Init ==
    /\ dev = "absent" /\ open = 0 /\ deferred = FALSE /\ udevq = <<>> /\ devlink = FALSE
    /\ pc = [w \in Workers |-> "idle"]
    /\ fd = [w \in Workers |-> FALSE]
    /\ restore = [w \in Workers |-> FALSE]
    /\ attempt = [w \in Workers |-> 0]
    /\ mount = [w \in Workers |-> FALSE]

Next ==
    \/ \E w \in Workers : WorkerStep(w) \/ Die(w) \/ Umount(w)
    \/ RemoveWork \/ Udev

\* Workers, the kernel and udev make progress (the devlink wait returns
\* one way or the other); a client's unmount and a worker's death are the
\* environment's.
Fairness ==
    /\ \A w \in Workers : WF_vars(WorkerStep(w))
    /\ WF_vars(RemoveWork)
    /\ WF_vars(Udev)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ dev \in {"absent", "active", "deleting"}
    /\ open \in Nat
    /\ \A i \in DOMAIN udevq : udevq[i] \in {"add", "remove"}
    /\ \A w \in Workers : attempt[w] \in 0..Attempts

\* The open count is exactly the fds and mounts the model knows about.
OpenCountExact == open = Cardinality({w \in Workers : fd[w]}) + Cardinality({w \in Workers : mount[w]})

\* A device under a mount is never removed.
MountedIsActive == (\E w \in Workers : mount[w]) => dev = "active"

\* Nothing is ever opened on a device that is going away.
NoOpenWhileDeleting == dev = "deleting" => open = 0

\* Liveness: a worker that started finishes, with a shared or a private device.
EveryWorkerFinishes == \A w \in Workers : [](pc[w] = "loop" => <>(pc[w] \in Done))

\* Liveness: once nobody is in the protocol and nothing is mounted, the
\* shared device is gone: removal is armed whenever it is left behind.
NoOrphanDevice ==
    []((\A w \in Workers : pc[w] \in Done \cup {"idle"} /\ ~mount[w]) => <>(dev = "absent"))

=============================================================================
