---------------------------- MODULE MC_mountwalk2 ----------------------------
(* Same forest; W1 walks a, a (success inside a mount on A, -ENOENT on the *)
(* negative "a" beneath it) and W2 walks a, b (the other way round)         *)
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
WProgDef    == ("W1" :> <<"a", "a">>) @@ ("W2" :> <<"a", "b">>)
WRootDef    == ("W1" :> [mnt |-> 1, d |-> "R"]) @@ ("W2" :> [mnt |-> 1, d |-> "R"])
WScopedDef  == ("W1" :> FALSE) @@ ("W2" :> FALSE)
=============================================================================
