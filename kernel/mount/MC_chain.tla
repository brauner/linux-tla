----------------------------- MODULE MC_chain -----------------------------
(* Three namespaces in a propagation chain: the initial one (rootfs made    *)
(* shared), pc's copy (slaves, locked, then made shared as well) and pd's   *)
(* copy of that (slaves of slaves): pd is spawned inside pc's namespace in  *)
(* a user namespace of its own.  Three processes in three user              *)
(* namespaces.  Mount ids: 1,2 initial; 3,4 pc's copy; 5,6 pd's copy.       *)
EXTENDS MountOps

SbsDef      == {"N", "R", "F"}
DentriesDef == {"N", "R", "Ra", "Rb", "F"}
DSbDef      == ("N" :> "N") @@ ("R" :> "R") @@ ("Ra" :> "R") @@ ("Rb" :> "R") @@ ("F" :> "F")
DParentDef  == ("N" :> "N") @@ ("R" :> "R") @@ ("Ra" :> "R") @@ ("Rb" :> "R") @@ ("F" :> "F")
SbRootDef   == ("N" :> "N") @@ ("R" :> "R") @@ ("F" :> "F")
ProcsDef    == {"pi", "pc", "pd"}
ProcUserDef == ("pi" :> 1) @@ ("pc" :> 2) @@ ("pd" :> 3)
MountSbsDef == {"F"}
PreludeDef  == << [kind |-> "chtype", p |-> "pi", m |-> 2, type |-> "shared", rec |-> TRUE],
                  [kind |-> "clonens", p |-> "pc", empty |-> FALSE],
                  [kind |-> "chtype", p |-> "pc", m |-> 4, type |-> "shared", rec |-> FALSE],
                  [kind |-> "spawn", p |-> "pd", n |-> 2],
                  [kind |-> "clonens", p |-> "pd", empty |-> FALSE] >>
=============================================================================
