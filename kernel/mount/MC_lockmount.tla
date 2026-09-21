---------------------------- MODULE MC_lockmount ----------------------------
(* The layout for LockMount: dentries R > A > B of the filesystem mounted  *)
(* on, F the root of the filesystem being mounted; two namespaces with    *)
(* root mounts 1 and 2 sharing the dentries; M1 mounts twice at A in      *)
(* namespace 1, M2 once at A in namespace 2; R removes A in namespace 1,   *)
(* D invalidates A, U detaches the first new mount.                       *)
EXTENDS LockMount, TLC

DentriesDef == {"R", "A", "B", "F"}
DParentDef  == ("R" :> "R") @@ ("A" :> "R") @@ ("B" :> "A") @@ ("F" :> "F")
RootsDef    == (1 :> 1) @@ (2 :> 2)
MInfoDef    == ("M1" :> [ns |-> 1, pm |-> 1, pd |-> "A", budget |-> 2])
               @@ ("M2" :> [ns |-> 2, pm |-> 2, pd |-> "A", budget |-> 1])
=============================================================================
