--------------------------- MODULE RangeCloseRace ---------------------------
(***************************************************************************)
(* __range_close() in place while the other threads of the process open,  *)
(* install, close and re-flag descriptors in the shared table.  The loop   *)
(* drops file_lock around filp_close() and re-reads the table afterwards;  *)
(* the bound it computed at the start stays.  The model lets the others    *)
(* run between any two iterations, which is more than the kernel allows.   *)
(*                                                                         *)
(* FIX_HOP = FALSE takes the hop out of next_fd_to_close(): the walk then  *)
(* closes the window CLOSE_RANGE_EXCEPT is meant to keep.                  *)
(***************************************************************************)
EXTENDS FdTable

CONSTANTS NWords, FIX_HOP

VARIABLES table, range, flags, pc, cur, max_fd, ok
vars == <<table, range, flags, pc, cur, max_fd, ok>>

LoopFlags == {f \in ValidFlags : ~f.unshare /\ ~f.cloexec}  \* the combinations that walk
Ranges == RangesUpTo(W * NWords)

Init ==
    /\ table \in Table(W)      \* one word to start with, it can grow to NWords
    /\ range \in Ranges
    /\ flags \in LoopFlags
    /\ pc = "start" /\ cur = 0 /\ max_fd = 0 /\ ok = TRUE

NextToClose(t, fd0, m, r, f) ==
    IF FIX_HOP THEN NextFdToClose(t, fd0, m, r, f) ELSE NextOpenFd(t, fd0, m, f)

(* the bounds, computed once under the lock *)
Start ==
    /\ pc = "start"
    /\ cur' = IF flags.except THEN 0 ELSE range.from
    /\ max_fd' = IF flags.except THEN LastFd(table) ELSE Min(range.to, LastFd(table))
    /\ pc' = "scan"
    /\ UNCHANGED <<table, range, flags, ok>>

(* one iteration under the lock: find the next descriptor, take it out of the table *)
Scan ==
    /\ pc = "scan"
    /\ LET fd == NextToClose(table, cur, max_fd, range, flags) IN
       IF fd > max_fd
       THEN pc' = "done" /\ UNCHANGED <<table, cur, ok>>
       ELSE IF table[fd].file
            THEN /\ table' = CloseSlot(table, fd)
                 /\ ok' = (ok /\ Selected(table, range, flags, fd))
                 /\ cur' = fd + 1
                 /\ pc' = "closing"
            ELSE /\ cur' = fd + 1
                 /\ pc' = "scan"
                 /\ UNCHANGED <<table, ok>>
    /\ UNCHANGED <<range, flags, max_fd>>

(* filp_close() outside the lock *)
FilpClose == pc = "closing" /\ pc' = "scan" /\ UNCHANGED <<table, range, flags, cur, max_fd, ok>>

(* the rest of the process *)
Grow ==      \* expand_fdtable()
    /\ MaxFds(table) < W * NWords
    /\ table' = [d \in 0..(MaxFds(table) + W - 1) |-> IF d \in DOMAIN table THEN table[d] ELSE Free]
    /\ UNCHANGED <<range, flags, pc, cur, max_fd, ok>>
Open ==      \* alloc_fd(): the lowest free slot, close-on-exec or not
    \E b \in BOOLEAN :
        LET free == {d \in DOMAIN table : ~table[d].open} IN
        /\ free # {}
        /\ table' = [table EXCEPT ![SetMin(free)] = [open |-> TRUE, file |-> FALSE, cloexec |-> b]]
        /\ UNCHANGED <<range, flags, pc, cur, max_fd, ok>>
Install ==   \* fd_install()
    \E d \in DOMAIN table :
        /\ table[d].open /\ ~table[d].file
        /\ table' = [table EXCEPT ![d].file = TRUE]
        /\ UNCHANGED <<range, flags, pc, cur, max_fd, ok>>
Close ==     \* close()
    \E d \in DOMAIN table :
        /\ table[d].file
        /\ table' = CloseSlot(table, d)
        /\ UNCHANGED <<range, flags, pc, cur, max_fd, ok>>
SetFd ==     \* fcntl(F_SETFD)
    \E d \in DOMAIN table :
        /\ table[d].file
        /\ table' = [table EXCEPT ![d].cloexec = ~table[d].cloexec]
        /\ UNCHANGED <<range, flags, pc, cur, max_fd, ok>>

Next == Start \/ Scan \/ FilpClose \/ Grow \/ Open \/ Install \/ Close \/ SetFd
Spec == Init /\ [][Next]_vars /\ WF_vars(Start) /\ WF_vars(Scan) /\ WF_vars(FilpClose)

TypeOK ==
    /\ table \in UNION {Table(W * k) : k \in 1..NWords}
    /\ pc \in {"start", "scan", "closing", "done"}
(* every descriptor the loop closes is one the range and the flags select at that moment *)
ClosedOnlySelected == ok
(* the bound computed at the start stays inside the table, which never shrinks *)
Bounded == pc \in {"scan", "closing"} => max_fd < MaxFds(table)
(* the loop ends whatever the other threads do *)
Terminates == <>(pc = "done")

=============================================================================
