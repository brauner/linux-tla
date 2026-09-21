--------------------------- MODULE MC_parentcand ---------------------------
(* The victim's parent is a candidate itself (found in review of the F5    *)
(* fix): P is a bind of the root at R@Ra, the victim V sits at P@Ra, the   *)
(* same dentry, and the root joins P's peer group, so P is the mount at    *)
(* the victim's mountpoint under a receiver.  A process holds a file on P. *)
(* MaxOps 1 leaves the synchronous umount of V as one of the next steps.  *)
EXTENDS MountOps
SbsDef      == {"N", "R", "F"}
DentriesDef == {"N", "R", "Ra", "Rb", "F"}
DSbDef      == ("N" :> "N") @@ ("R" :> "R") @@ ("Ra" :> "R") @@ ("Rb" :> "R") @@ ("F" :> "F")
DParentDef  == ("N" :> "N") @@ ("R" :> "R") @@ ("Ra" :> "R") @@ ("Rb" :> "R") @@ ("F" :> "F")
SbRootDef   == ("N" :> "N") @@ ("R" :> "R") @@ ("F" :> "F")
ProcsDef    == {"pi"}
ProcUserDef == ("pi" :> 1)
MountSbsDef == {"F"}
PreludeDef  == << [kind |-> "bind", p |-> "pi", src |-> [mnt |-> 2, dentry |-> "R"], dst |-> [mnt |-> 2, dentry |-> "Ra"], rec |-> FALSE],
                  [kind |-> "chtype", p |-> "pi", m |-> 3, type |-> "shared", rec |-> FALSE],
                  [kind |-> "mount", p |-> "pi", pos |-> [mnt |-> 3, dentry |-> "Ra"], sb |-> "F", auto |-> FALSE],
                  [kind |-> "setgroup", p |-> "pi", from |-> 3, to |-> 2],
                  [kind |-> "openfd", p |-> "pi", pos |-> [mnt |-> 3, dentry |-> "R"]] >>
=============================================================================
