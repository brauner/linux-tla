---------------------------- MODULE MC_signals ----------------------------
(* Three ordinary threads, no io_uring: signals, masks, sigtimedwait,      *)
(* exit, exec and the coredump rendezvous between them.                    *)
EXTENDS Coredump
ThreadsDef    == {"m", "b", "c"}
RoleDef       == [t \in ThreadsDef |-> "user"]
Owner0Def     == [t \in ThreadsDef |-> NoThread]
RingOwnersDef == {}
=============================================================================
