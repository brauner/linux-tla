---------------------------- MODULE MC_mountwalk ----------------------------
(* Root filesystem S: R > a=A > b=B, and a negative "a" below A.  Mounted   *)
(* filesystem F: F > a=Fa, and a negative "b" below F.  W1 walks a, .., a   *)
(* from the root (the climb); W2 is scoped at A and walks .., ..            *)
EXTENDS MountWalk, TLC

DentriesDef == {"R", "A", "B", "An", "F", "Fa", "Fn"}
DParentDef  == ("R" :> "R") @@ ("A" :> "R") @@ ("B" :> "A") @@ ("An" :> "A")
               @@ ("F" :> "F") @@ ("Fa" :> "F") @@ ("Fn" :> "F")
DNameDef    == ("R" :> "/") @@ ("A" :> "a") @@ ("B" :> "b") @@ ("An" :> "a")
               @@ ("F" :> "/") @@ ("Fa" :> "a") @@ ("Fn" :> "b")
DSbDef      == ("R" :> "S") @@ ("A" :> "S") @@ ("B" :> "S") @@ ("An" :> "S")
               @@ ("F" :> "F") @@ ("Fa" :> "F") @@ ("Fn" :> "F")
SbRootDef   == ("S" :> "R") @@ ("F" :> "F")
NegativeDef == {"An", "Fn"}
WProgDef    == ("W1" :> <<"a", "..", "a">>) @@ ("W2" :> <<"..", "..">>)
WRootDef    == ("W1" :> [mnt |-> 1, d |-> "R"]) @@ ("W2" :> [mnt |-> 1, d |-> "A"])
WScopedDef  == ("W1" :> FALSE) @@ ("W2" :> TRUE)
=============================================================================
