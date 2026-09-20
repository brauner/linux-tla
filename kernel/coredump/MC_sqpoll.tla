---------------------------- MODULE MC_sqpoll ----------------------------
(* The SQPOLL shape: m owns a ring with SQPOLL, s is the iou-sqp thread,   *)
(* w is an iou-wrk worker of s's io-wq, n is a worker s or m may create.   *)
EXTENDS Coredump
ThreadsDef    == {"m", "s", "w", "n"}
RoleDef       == ("m" :> "user") @@ ("s" :> "sqpoll") @@ ("w" :> "iowq") @@ ("n" :> "slot")
Owner0Def     == ("m" :> NoThread) @@ ("s" :> NoThread) @@ ("w" :> "s") @@ ("n" :> NoThread)
RingOwnersDef == {"m", "s"}
=============================================================================
