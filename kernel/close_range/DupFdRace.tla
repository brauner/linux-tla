----------------------------- MODULE DupFdRace -----------------------------
(***************************************************************************)
(* dup_fd() for close_range(CLOSE_RANGE_UNSHARE) on a shared table.  The  *)
(* copy runs under file_lock, but fd_install() is lockless and can put a   *)
(* file into a claimed slot at any time, and the lock is dropped to        *)
(* allocate a bigger table, during which the other threads can do          *)
(* anything.  DROP_IN_DUP_FD = FALSE is the code before the series.        *)
(***************************************************************************)
EXTENDS FdTable

CONSTANTS NWords, FlagSet

VARIABLES table, range, flags, pc, cap, open_files, snap, i, clone, full, refs
vars == <<table, range, flags, pc, cap, open_files, snap, i, clone, full, refs>>

UnshareFlagsDef == {f \in ValidFlags : f.unshare}
OldUnshareFlagsDef == {f \in OldFlags : f.unshare}
Ranges == RangesUpTo(W * NWords)
Drop == IF flags.cloexec THEN NoRange ELSE range

Init ==
    /\ table \in Table(W)
    /\ range \in Ranges
    /\ flags \in FlagSet
    /\ pc = "size" /\ cap = NR_OPEN_DEFAULT /\ open_files = 0 /\ snap = table
    /\ i = 0 /\ clone = <<>> /\ full = <<>> /\ refs = {}

(* under the lock: size the copy; a table bigger than what we have means dropping the lock *)
Size ==
    /\ pc = "size"
    /\ LET n == SaneFdtableSize(table, Drop, flags) IN
       /\ open_files' = n
       /\ IF n > cap
          THEN pc' = "alloc" /\ UNCHANGED <<snap, clone, full, i, refs>>
          ELSE /\ pc' = "copy"
               /\ snap' = table
               /\ clone' = [d \in 0..(n - 1) |->             \* copy_fd_bitmaps()
                               [open |-> table[d].open, file |-> FALSE, cloexec |-> table[d].cloexec]]
               /\ full' = [w \in 0..(n \div W - 1) |-> OpenBits(table, w) = WordBits]
               /\ i' = 0 /\ refs' = {}
    /\ UNCHANGED <<table, range, flags, cap>>

(* alloc_fdtable() without the lock; then the sizing starts over *)
Alloc ==
    /\ pc = "alloc"
    /\ cap' = open_files /\ pc' = "size"
    /\ UNCHANGED <<table, range, flags, open_files, snap, i, clone, full, refs>>

(* one slot of the copy loop, under the lock: the file pointer is read now *)
Copy ==
    /\ pc = "copy"
    /\ IF i = open_files
       THEN pc' = "finish" /\ UNCHANGED <<clone, full, refs, i>>
       ELSE /\ i' = i + 1
            /\ pc' = "copy"
            /\ IF table[i].file /\ (DROP_IN_DUP_FD => ~DupFdDrops(table, i, Drop, flags))
               THEN /\ clone' = [clone EXCEPT ![i] = [open |-> TRUE, file |-> TRUE, cloexec |-> table[i].cloexec]]
                    /\ refs' = refs \cup {i}
                    /\ UNCHANGED full
               ELSE /\ clone' = [clone EXCEPT ![i] = [open |-> FALSE, file |-> FALSE, cloexec |-> clone[i].cloexec]]
                    /\ full' = [full EXCEPT ![i \div W] = FALSE]   \* __clear_open_fd()
                    /\ UNCHANGED refs
    /\ UNCHANGED <<table, range, flags, cap, open_files, snap>>

(* back in sys_close_range(): mark the clone, close from it (before the series), or nothing *)
Finish ==
    /\ pc = "finish"
    /\ pc' = "done"
    /\ IF flags.cloexec
       THEN clone' = RangeCloexec(clone, range, flags) /\ UNCHANGED full
       ELSE IF DROP_IN_DUP_FD
            THEN UNCHANGED <<clone, full>>
            ELSE LET c == RangeClose(clone, range, flags) IN
                 /\ clone' = c
                 /\ full' = [w \in DOMAIN full |-> full[w] /\ \A b \in WordBits : c[w * W + b].open]
    /\ UNCHANGED <<table, range, flags, cap, open_files, snap, i, refs>>

(* the rest of the process: fd_install() is lockless, everything else needs the lock *)
Unlocked == pc = "alloc"
Grow ==
    /\ Unlocked /\ MaxFds(table) < W * NWords
    /\ table' = [d \in 0..(MaxFds(table) + W - 1) |-> IF d \in DOMAIN table THEN table[d] ELSE Free]
    /\ UNCHANGED <<range, flags, pc, cap, open_files, snap, i, clone, full, refs>>
Open ==
    \E b \in BOOLEAN :
        LET free == {d \in DOMAIN table : ~table[d].open} IN
        /\ Unlocked /\ free # {}
        /\ table' = [table EXCEPT ![SetMin(free)] = [open |-> TRUE, file |-> FALSE, cloexec |-> b]]
        /\ UNCHANGED <<range, flags, pc, cap, open_files, snap, i, clone, full, refs>>
Install ==
    \E d \in DOMAIN table :
        /\ pc # "done" /\ table[d].open /\ ~table[d].file
        /\ table' = [table EXCEPT ![d].file = TRUE]
        /\ UNCHANGED <<range, flags, pc, cap, open_files, snap, i, clone, full, refs>>
Close ==
    \E d \in DOMAIN table :
        /\ Unlocked /\ table[d].file
        /\ table' = CloseSlot(table, d)
        /\ UNCHANGED <<range, flags, pc, cap, open_files, snap, i, clone, full, refs>>
SetFd ==
    \E d \in DOMAIN table :
        /\ Unlocked /\ table[d].file
        /\ table' = [table EXCEPT ![d].cloexec = ~table[d].cloexec]
        /\ UNCHANGED <<range, flags, pc, cap, open_files, snap, i, clone, full, refs>>

Next == Size \/ Alloc \/ Copy \/ Finish \/ Grow \/ Open \/ Install \/ Close \/ SetFd
Spec == Init /\ [][Next]_vars /\ WF_vars(Size) /\ WF_vars(Alloc) /\ WF_vars(Copy) /\ WF_vars(Finish)

Done == pc = "done"
Clone == [slots |-> clone, full |-> full]
(* no file without an open bit, full_fds_bits exact *)
CloneOK == Done => SlotsOK(Clone) /\ FullBitsOK(Clone)
(* only descriptors that are carried over are referenced *)
NoRefOnDropped == Done => Drop.null \/ \A d \in refs : ~Selected(snap, Drop, flags, d)
(* every descriptor that was installed and not dropped when the copy was sized is in the clone *)
KeptCopied == Done => \A d \in DOMAIN snap :
                          (snap[d].file /\ ~DupFdDrops(snap, d, Drop, flags)) => d \in refs /\ clone[d].file
(* nothing dropped is in the clone *)
DroppedNotInClone == Done => Drop.null \/
                             \A d \in DOMAIN clone : DupFdDrops(snap, d, Drop, flags) => ~clone[d].open
(* a copied slot points at a file that is in the table *)
CopiedAreFiles == Done => \A d \in DOMAIN clone : clone[d].file => table[d].file
(* dup_fd() ends whatever the other threads do while it has the lock dropped *)
Finishes == <>(pc = "done")

=============================================================================
