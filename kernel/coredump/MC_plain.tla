---------------------------- MODULE MC_plain ----------------------------
(* A plain ring: m owns the io-wq, w is its worker, n a worker it may      *)
(* create, b a second ordinary thread.                                     *)
EXTENDS Coredump
ThreadsDef    == {"m", "b", "w", "n"}
RoleDef       == ("m" :> "user") @@ ("b" :> "user") @@ ("w" :> "iowq") @@ ("n" :> "slot")
Owner0Def     == ("m" :> NoThread) @@ ("b" :> NoThread) @@ ("w" :> "m") @@ ("n" :> NoThread)
RingOwnersDef == {"m"}
=============================================================================
