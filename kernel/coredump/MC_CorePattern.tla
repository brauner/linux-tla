--------------------------- MODULE MC_CorePattern ---------------------------
EXTENDS CorePattern
OldDef == [mode |-> "pipe", path |-> "/usr/bin/helper"]
NewDef == [mode |-> "file", path |-> "/tmp/core.%p"]
=============================================================================
