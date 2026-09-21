------------------------------ MODULE MC_dbg ------------------------------
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
                  [kind |-> "clonens", p |-> "pi", empty |-> FALSE],
                  [kind |-> "bind", p |-> "pi", src |-> [mnt |-> 4, dentry |-> "Ra"], dst |-> [mnt |-> 4, dentry |-> "Ra"], rec |-> FALSE],
                  [kind |-> "setns", p |-> "pi", n |-> 1],
                  [kind |-> "mount", p |-> "pi", pos |-> [mnt |-> 6, dentry |-> "Ra"], sb |-> "F", auto |-> FALSE] >>
PreludeDone == step <= Len(Prelude)
=============================================================================
