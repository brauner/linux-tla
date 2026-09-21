---------------------------- MODULE MC_algebra ----------------------------
(* The layout for Family A: three superblocks (the nullfs namespace root,  *)
(* the rootfs with two directories and a subdirectory, one mountable       *)
(* filesystem with a subdirectory, one empty one), two processes, one in   *)
(* the initial user namespace and one in a child user namespace.           *)
EXTENDS MountOps

SbsDef      == {"N", "R", "F", "G"}
DentriesDef == {"N", "R", "Ra", "Rb", "Rax", "F", "Fc", "G"}
DSbDef      == ("N" :> "N") @@ ("R" :> "R") @@ ("Ra" :> "R") @@ ("Rb" :> "R") @@ ("Rax" :> "R")
               @@ ("F" :> "F") @@ ("Fc" :> "F") @@ ("G" :> "G")
DParentDef  == ("N" :> "N") @@ ("R" :> "R") @@ ("Ra" :> "R") @@ ("Rb" :> "R") @@ ("Rax" :> "Ra")
               @@ ("F" :> "F") @@ ("Fc" :> "F") @@ ("G" :> "G")
SbRootDef   == ("N" :> "N") @@ ("R" :> "R") @@ ("F" :> "F") @@ ("G" :> "G")
ProcsDef    == {"pi", "pc"}
ProcUserDef == ("pi" :> 1) @@ ("pc" :> 2)
MountSbsDef == {"F", "G"}
PreludeDef  == <<>>
=============================================================================
