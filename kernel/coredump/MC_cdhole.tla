---------------------------- MODULE MC_cdhole ----------------------------
(* The cdhole shape: m crashes and dumps, x owns a ring and exits with     *)
(* exit(2) while its worker w has a creation queued on it, n is the        *)
(* worker that creation makes.                                             *)
EXTENDS Coredump
ThreadsDef    == {"m", "x", "w", "n"}
RoleDef       == ("m" :> "user") @@ ("x" :> "user") @@ ("w" :> "iowq") @@ ("n" :> "slot")
Owner0Def     == ("m" :> NoThread) @@ ("x" :> NoThread) @@ ("w" :> "x") @@ ("n" :> NoThread)
RingOwnersDef == {"x"}
=============================================================================
