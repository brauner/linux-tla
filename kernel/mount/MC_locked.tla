----------------------------- MODULE MC_locked -----------------------------
(* The unprivileged case: pi mounts F on /a, then pc clones the namespace   *)
(* into its own user namespace, so the copies of rootfs and of the F mount  *)
(* are locked and hide (copy of rootfs, "Ra").  Mount ids: 1,2,3 initial;   *)
(* 4,5,6 pc's copy.                                                         *)
EXTENDS MountOps

SbsDef      == {"N", "R", "F"}
DentriesDef == {"N", "R", "Ra", "Rb", "F"}
DSbDef      == ("N" :> "N") @@ ("R" :> "R") @@ ("Ra" :> "R") @@ ("Rb" :> "R") @@ ("F" :> "F")
DParentDef  == ("N" :> "N") @@ ("R" :> "R") @@ ("Ra" :> "R") @@ ("Rb" :> "R") @@ ("F" :> "F")
SbRootDef   == ("N" :> "N") @@ ("R" :> "R") @@ ("F" :> "F")
ProcsDef    == {"pi", "pc"}
ProcUserDef == ("pi" :> 1) @@ ("pc" :> 2)
MountSbsDef == {"F"}
PreludeDef  == << [kind |-> "chtype", p |-> "pi", m |-> 2, type |-> "shared", rec |-> TRUE],
                  [kind |-> "mount", p |-> "pi", pos |-> [mnt |-> 2, dentry |-> "Ra"], sb |-> "F", auto |-> FALSE],
                  [kind |-> "clonens", p |-> "pc", empty |-> FALSE] >>
=============================================================================
