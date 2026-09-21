----------------------------- MODULE MC_mntput -----------------------------
(* The layout for MntPut: the umounter, one RCU walker, one holder of an   *)
(* open file, two CPUs.                                                    *)
EXTENDS MntPut

TaskListDef == <<"U", "W1", "H1">>
=============================================================================
