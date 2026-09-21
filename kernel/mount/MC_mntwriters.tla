---------------------------- MODULE MC_mntwriters ----------------------------
(* Two writers on two CPUs against one holder.                             *)
EXTENDS MntWriters, TLC

WCpuDef == ("W1" :> 1) @@ ("W2" :> 2)
=============================================================================
