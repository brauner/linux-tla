----------------------------- MODULE MC_small -----------------------------
(* A smaller layout for the mutation and witness configurations: the       *)
(* nullfs root, a rootfs with two directories, one mountable filesystem,    *)
(* the two processes.                                                       *)
EXTENDS MountOps

SbsDef      == {"N", "R", "F"}
DentriesDef == {"N", "R", "Ra", "Rb", "F"}
DSbDef      == ("N" :> "N") @@ ("R" :> "R") @@ ("Ra" :> "R") @@ ("Rb" :> "R") @@ ("F" :> "F")
DParentDef  == ("N" :> "N") @@ ("R" :> "R") @@ ("Ra" :> "R") @@ ("Rb" :> "R") @@ ("F" :> "F")
SbRootDef   == ("N" :> "N") @@ ("R" :> "R") @@ ("F" :> "F")
ProcsDef    == {"pi", "pc"}
ProcUserDef == ("pi" :> 1) @@ ("pc" :> 2)
MountSbsDef == {"F"}
PreludeDef  == <<>>
=============================================================================
