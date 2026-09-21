----------------------------- MODULE MC_peers -----------------------------
(* Two namespaces whose mounts are peers (a clone within one user           *)
(* namespace, rootfs shared first); pi ends up in the copy, pc stays in the *)
(* initial namespace without privileges there.  Mount ids: 1,2 and 3,4.     *)
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
                  [kind |-> "clonens", p |-> "pi", empty |-> FALSE] >>
=============================================================================
