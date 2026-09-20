-------------------------- MODULE UsernsRegistry --------------------------
(***************************************************************************)
(* The life of a user namespace delegated by systemd-nsresourced: the      *)
(* clients that allocate it (systemd-nspawn --private-users=managed, the   *)
(* executor for PrivateUsers=managed), the worker that registers it, the   *)
(* BPF-LSM map that restricts it, PID 1's file descriptor store that pins  *)
(* it, the kernel that frees it and reuses its inode number, the kprobe    *)
(* and ring buffer that report the death, and the manager that releases    *)
(* the registration.                                                       *)
(*                                                                         *)
(* Tree: systemd v262-rc2-60-ge96ff3b5b9.                                  *)
(*                                                                         *)
(* Modelled code:                                                          *)
(*   src/nsresourced/nsresourcework.c   vl_method_allocate_user_range,     *)
(*                     allocate_now, inode_slot_is_available,              *)
(*                     registry_range_is_available, uid_is_available,      *)
(*                     write_userns, the FDSTORE=1 push after the lock is  *)
(*                     dropped, vl_method_add_cgroup_to_user_namespace,    *)
(*                     vl_method_add_netif_to_user_namespace               *)
(*   src/nsresourced/userns-registry.c  userns_registry_lock (LOCK_BSD on  *)
(*                     "lock"), _store, _remove, _load_by_userns_inode,    *)
(*                     userns_info_verify_fd (NS_GET_ID), _reap_if_dead    *)
(*                     (namespace_open_by_id), _release_by_info (BPF map,  *)
(*                     FDSTOREREMOVE=1, cgroup rmdir, RTM_DELLINK)         *)
(*   src/nsresourced/nsresourced-manager.c  ringbuf_event,                 *)
(*                     manager_release_userns_by_inode/_by_info (the       *)
(*                     liveness probe), manager_startup (the fdstore and   *)
(*                     registry sweeps, manager_restore_userns_policy)     *)
(*   src/nsresourced/userns-restrict.c  userns_restrict_register_by_fd,    *)
(*                     _reset_by_inode: BPF_MAP_TYPE_HASH keyed by inode   *)
(*   src/bpf/userns-restrict.bpf.c  kprobe/retire_userns_sysctls:          *)
(*                     bpf_ringbuf_output() of the inode if it is in a map *)
(*   src/shared/nsresource.c, src/nspawn/nspawn.c, nspawn-cgroup.c,        *)
(*                     src/core/exec-invoke.c  the clients                 *)
(*   src/core/service.c  service_add_fd_store, FDSTOREREMOVE=1 removes     *)
(*                     every fd of that name                               *)
(*   kernel            nsfs: an open fd references the namespace;          *)
(*                     free_user_ns()/retire_userns_sysctls() run when the *)
(*                     last reference is gone; the inode number is then    *)
(*                     free for the next namespace; NS_GET_ID is unique    *)
(*                                                                         *)
(* Switches:                                                               *)
(*   FDSTORE_PINS        PID 1 keeps the userns fd the worker pushes with   *)
(*                       FDSTORE=1 (FileDescriptorStoreMax=4096), so the   *)
(*                       namespace cannot die while it is registered.      *)
(*                       This is what the code does; FALSE is what the     *)
(*                       release logic assumes.                            *)
(*   FIX_NSID_VERIFY     01e6465b55: the registry entry carries NS_GET_ID, *)
(*                       inode_slot_is_available() releases a stale entry, *)
(*                       the manager refuses to release a live namespace    *)
(*   FIX_REAP_ON_ALLOC   a77838a950: a range held by a dead namespace is   *)
(*                       reclaimed during allocation                       *)
(*   FIX_STARTUP_SWEEP   23f2204718: manager_startup() reaps dead entries  *)
(*                       by id and restores the BPF policy of live ones    *)
(*   FIX_RINGBUF_LOCK    ringbuf_event() takes the registry lock           *)
(*                                                                         *)
(* Abstractions:                                                           *)
(*   - Namespace identity: a small pool of inode numbers the kernel        *)
(*     reuses, and an ever increasing id (NS_GET_ID).                      *)
(*   - A client holds one reference on its namespace (its fd and the       *)
(*     processes it runs in it) and drops it in one step.  The worker's    *)
(*     own dup of the fd is folded into the request: the namespace cannot  *)
(*     die while its request is in flight.                                 *)
(*   - Only 64K "managed" allocations: no self mappings, no delegated      *)
(*     ranges, no nested namespaces, no user database side, no polkit.    *)
(*   - One request per client at a time; the worker of a request is the   *)
(*     client's id.  Steps under the registry lock are atomic; the fd     *)
(*     store push after the lock is a step of its own, as in the code.    *)
(*   - The cgroup and the veth of an nspawn client are one "resource"      *)
(*     each, created under the lock in AddControlGroup/AddNetwork and      *)
(*     destroyed on release; cgroups are found by id, interfaces by name.  *)
(*   - The ring buffer holds RingCap events; a further death is dropped.  *)
(*   - A manager restart is atomic: in-flight requests fail, PID 1 keeps   *)
(*     the fd store across it (FileDescriptorStorePreserve=restart), the   *)
(*     ring buffer survives (the map is pinned), the sweep runs.           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Clients,          \* client ids, also the ids of the workers serving them
    Role,             \* [Clients -> {"nspawn", "executor"}]: nspawn also delegates a cgroup and a veth
    Inodes,           \* the inode numbers nsfs hands out
    Ranges,           \* the 64K transient UID ranges the registry can allocate
    IdMax,            \* the last namespace id the kernel hands out (bounds the run)
    RingCap,          \* ring buffer capacity in events
    RestartBudget,    \* manager restarts the environment may cause
    FDSTORE_PINS,
    FIX_NSID_VERIFY,
    FIX_REAP_ON_ALLOC,
    FIX_STARTUP_SWEEP,
    FIX_RINGBUF_LOCK

ASSUME Role \in [Clients -> {"nspawn", "executor"}]

\* the layout of the configurations: one container, one service
RoleDef == ("c1" :> "nspawn") @@ ("c2" :> "executor")
ASSUME IdMax \in Nat /\ RingCap \in Nat /\ RestartBudget \in Nat

Ids     == 1..IdMax
NoId    == 0
NoEntry == [id |-> NoId, range |-> "none", cg |-> FALSE, netif |-> FALSE]
NoLock  == "none"
Mgr     == "mgr"

VARIABLES
    \* the kernel
    nsAlive,      \* ids of the live user namespaces
    nsInode,      \* [Ids -> Inodes \cup {0}]: the inode number of a namespace
    nsRefs,       \* [Ids -> Nat]: references held by clients
    nsRange,      \* [Ids -> Ranges \cup {"none"}]: the range written into uid_map, never undone
    freeInodes,   \* inode numbers not in use
    nextId,       \* the next NS_GET_ID
    \* the BPF map and ring buffer
    managed,      \* inodes in the userns_managed map
    ringbuf,      \* inodes of dead namespaces waiting for the manager
    \* PID 1's fd store for systemd-nsresourced.service
    fdstore,      \* set of [inode, id]: an fd named "userns-<inode>" referencing namespace id
    \* the registry directory
    registry,     \* [Inodes -> entry]: i<inode>.userns and the links to it
    lock,         \* holder of the "lock" file: NoLock, a client id (its worker) or Mgr
    cgroups,      \* cgroup ids that exist (delegated ones are named after the namespace id)
    netifs,       \* host interface names that exist
    \* the clients and their workers
    cl,           \* [Clients -> [pc, ns]]
    wk,           \* [Clients -> pc of the worker serving the client's request]
    mgr,          \* [pc, inode]: the manager
    budget,       \* [restart]
    hist          \* dropped: a death event was lost

vars == <<nsAlive, nsInode, nsRefs, nsRange, freeInodes, nextId, managed, ringbuf,
          fdstore, registry, lock, cgroups, netifs, cl, wk, mgr, budget, hist>>

Kernel == <<nsAlive, nsInode, nsRefs, nsRange, freeInodes, nextId>>

(***************************************************************************)
(* Derived predicates                                                      *)
(***************************************************************************)
Pinned(n)   == \E f \in fdstore : f.id = n
Registered(n) == \E i \in Inodes : registry[i].id = n
\* namespace_open_by_id(): succeeds iff the namespace is alive
Alive(n)    == n \in nsAlive
RangeHeld(r) == \E i \in Inodes : registry[i].range = r
FreeRange   == {r \in Ranges : ~RangeHeld(r)}
\* the cgroup and the interface a registration owns
CgOf(n)     == <<"cg", n>>
NetifOf(n)  == <<"if", n>>

(***************************************************************************)
(* userns_registry_release_by_info(): the BPF map entry, the fd store      *)
(* entries of that name, the cgroup, the interface, the registry files.    *)
(* Written as a record of the new values so that a step can release more   *)
(* than nothing and still assign each variable once.                       *)
(***************************************************************************)
Released(i, m, f, c, nf, reg) ==
    LET e == reg[i] IN
    [managed  |-> m \ {i},
     fdstore  |-> {x \in f : x.inode # i},
     cgroups  |-> c \ {CgOf(e.id)},
     netifs   |-> nf \ {NetifOf(e.id)},
     registry |-> [reg EXCEPT ![i] = NoEntry]]

(***************************************************************************)
(* The clients                                                             *)
(***************************************************************************)
\* userns_acquire_empty() and the AllocateUserRange call: a fresh empty
\* namespace, one reference (the client's fd, later its processes)
Create(c) ==
    /\ cl[c].pc = "idle"
    /\ nextId <= IdMax
    /\ freeInodes # {}
    /\ \E i \in freeInodes :
        /\ nsAlive' = nsAlive \cup {nextId}
        /\ nsInode' = [nsInode EXCEPT ![nextId] = i]
        /\ nsRefs' = [nsRefs EXCEPT ![nextId] = 1]
        /\ freeInodes' = freeInodes \ {i}
        /\ nextId' = nextId + 1
        /\ cl' = [cl EXCEPT ![c] = [pc |-> "alloc", ns |-> nextId]]
        /\ wk' = [wk EXCEPT ![c] = "lock"]
    /\ UNCHANGED <<nsRange, managed, ringbuf, fdstore, registry, lock, cgroups, netifs, mgr, budget, hist>>

\* The client is done: nspawn's container exited, the service stopped; the
\* client's fd and processes are gone.  A failed request is given up the
\* same way.
Drop(c) ==
    /\ cl[c].pc \in {"registered", "failed"}
    /\ nsRefs' = [nsRefs EXCEPT ![cl[c].ns] = @ - 1]
    /\ cl' = [cl EXCEPT ![c] = [pc |-> "idle", ns |-> NoId]]
    /\ UNCHANGED <<nsAlive, nsInode, nsRange, freeInodes, nextId, managed, ringbuf, fdstore,
                   registry, lock, cgroups, netifs, wk, mgr, budget, hist>>

(***************************************************************************)
(* The worker serving AllocateUserRange                                    *)
(***************************************************************************)
\* userns_registry_lock()
WLock(c) ==
    /\ wk[c] = "lock"
    /\ lock = NoLock
    /\ lock' = c
    /\ wk' = [wk EXCEPT ![c] = "slot"]
    /\ UNCHANGED <<Kernel, managed, ringbuf, fdstore, registry, cgroups, netifs, cl, mgr, budget, hist>>

\* inode_slot_is_available(): an entry for the inode that describes another
\* namespace is stale and released; without the id check any entry means
\* UserNamespaceExists
WSlot(c) ==
    /\ wk[c] = "slot"
    /\ LET n == cl[c].ns
           i == nsInode[n]
           e == registry[i]
       IN IF e.id = NoId
          THEN /\ wk' = [wk EXCEPT ![c] = "range"]
               /\ UNCHANGED <<managed, fdstore, registry, cgroups, netifs, lock, cl>>
          ELSE IF FIX_NSID_VERIFY /\ e.id # n
          THEN LET R == Released(i, managed, fdstore, cgroups, netifs, registry) IN
               /\ managed' = R.managed /\ fdstore' = R.fdstore /\ cgroups' = R.cgroups
               /\ netifs' = R.netifs /\ registry' = R.registry
               /\ wk' = [wk EXCEPT ![c] = "range"]
               /\ UNCHANGED <<lock, cl>>
          ELSE /\ wk' = [wk EXCEPT ![c] = "done"]
               /\ cl' = [cl EXCEPT ![c].pc = "failed"]
               /\ lock' = NoLock
               /\ UNCHANGED <<managed, fdstore, registry, cgroups, netifs>>
    /\ UNCHANGED <<Kernel, ringbuf, mgr, budget, hist>>

\* allocate_one()/uid_is_available(): a free range, or one whose dead owner
\* registry_range_is_available() reaps; then userns_registry_store(),
\* userns_restrict_register_by_fd(), write_userns(), and the lock is dropped
WRange(c) ==
    /\ wk[c] = "range"
    /\ LET n == cl[c].ns
           i == nsInode[n]
           dead == {j \in Inodes : registry[j].id # NoId /\ ~Alive(registry[j].id)}
       IN \/ \E r \in FreeRange :
                /\ registry' = [registry EXCEPT ![i] = [id |-> n, range |-> r, cg |-> FALSE, netif |-> FALSE]]
                /\ managed' = managed \cup {i}
                /\ nsRange' = [nsRange EXCEPT ![n] = r]
                /\ UNCHANGED <<fdstore, cgroups, netifs, hist>>
                /\ wk' = [wk EXCEPT ![c] = "push"]
                /\ lock' = NoLock
                /\ UNCHANGED cl
          \/ /\ FreeRange = {}
             /\ FIX_REAP_ON_ALLOC
             /\ \E j \in dead :
                  LET R == Released(j, managed, fdstore, cgroups, netifs, registry) IN
                  /\ managed' = R.managed /\ fdstore' = R.fdstore /\ cgroups' = R.cgroups
                  /\ netifs' = R.netifs /\ registry' = R.registry
                  /\ UNCHANGED <<nsRange, wk, lock, cl, hist>>
          \/ /\ FreeRange = {}
             /\ ~FIX_REAP_ON_ALLOC \/ dead = {}
             /\ wk' = [wk EXCEPT ![c] = "done"]
             /\ cl' = [cl EXCEPT ![c].pc = "failed"]
             /\ lock' = NoLock
             /\ hist' = [hist EXCEPT !.starved = @ \/ dead # {}]
             /\ UNCHANGED <<registry, managed, nsRange, fdstore, cgroups, netifs>>
    /\ UNCHANGED <<nsAlive, nsInode, nsRefs, freeInodes, nextId, ringbuf, mgr, budget>>

\* sd_pid_notifyf_with_fds(FDSTORE=1 FDNAME=userns-<inode>) after the lock
\* was closed, then the reply
WPush(c) ==
    /\ wk[c] = "push"
    /\ LET n == cl[c].ns IN
       /\ fdstore' = IF FDSTORE_PINS THEN fdstore \cup {[inode |-> nsInode[n], id |-> n]} ELSE fdstore
       /\ wk' = [wk EXCEPT ![c] = "done"]
       /\ cl' = [cl EXCEPT ![c].pc = "registered"]
    /\ UNCHANGED <<Kernel, managed, ringbuf, registry, lock, cgroups, netifs, mgr, budget, hist>>

\* AddControlGroupToUserNamespace and AddNetworkToUserNamespace of an nspawn
\* client, under the lock: the entry is loaded by inode and verified by id,
\* the cgroup is chowned to the range, the veth created and recorded
WResources(c) ==
    /\ cl[c].pc = "registered"
    /\ Role[c] = "nspawn"
    /\ lock = NoLock
    /\ LET n == cl[c].ns
           i == nsInode[n]
           e == registry[i]
       IN IF e.id = n
          THEN /\ ~e.cg
               /\ registry' = [registry EXCEPT ![i].cg = TRUE, ![i].netif = TRUE]
               /\ cgroups' = cgroups \cup {CgOf(n)}
               /\ netifs' = netifs \cup {NetifOf(n)}
          ELSE /\ e.id # n   \* UserNamespaceNotRegistered
               /\ FALSE
    /\ UNCHANGED <<Kernel, managed, ringbuf, fdstore, lock, cl, wk, mgr, budget, hist>>

(***************************************************************************)
(* The kernel                                                              *)
(***************************************************************************)
\* The last reference is gone: free_user_ns(), retire_userns_sysctls(), the
\* kprobe reports the inode if a map knows it, the inode number is free again
NsDie(n) ==
    /\ n \in nsAlive
    /\ nsRefs[n] = 0
    /\ ~Pinned(n)
    /\ nsAlive' = nsAlive \ {n}
    /\ freeInodes' = freeInodes \cup {nsInode[n]}
    /\ IF nsInode[n] \in managed
       THEN IF Len(ringbuf) < RingCap
            THEN ringbuf' = Append(ringbuf, nsInode[n]) /\ UNCHANGED hist
            ELSE ringbuf' = ringbuf /\ hist' = [hist EXCEPT !.dropped = TRUE]
       ELSE UNCHANGED <<ringbuf, hist>>
    /\ UNCHANGED <<nsInode, nsRefs, nsRange, nextId, managed, fdstore, registry, lock,
                   cgroups, netifs, cl, wk, mgr, budget>>

(***************************************************************************)
(* The manager                                                             *)
(***************************************************************************)
\* ringbuf_event(): take the lock (or not), then release the inode
MgrTake ==
    /\ mgr.pc = "idle"
    /\ ringbuf # <<>>
    /\ ~FIX_RINGBUF_LOCK \/ lock = NoLock
    /\ lock' = IF FIX_RINGBUF_LOCK THEN Mgr ELSE lock
    /\ mgr' = [pc |-> "release", inode |-> Head(ringbuf)]
    /\ ringbuf' = Tail(ringbuf)
    /\ UNCHANGED <<Kernel, managed, fdstore, registry, cgroups, netifs, cl, wk, budget, hist>>

\* manager_release_userns_by_inode(): an entry whose namespace is alive is
\* left alone (with the id probe); an entry is released; no entry means
\* inode-only cleanup of the map and the fd store
MgrRelease ==
    /\ mgr.pc = "release"
    /\ LET i == mgr.inode
           e == registry[i]
       IN IF e.id # NoId /\ FIX_NSID_VERIFY /\ Alive(e.id)
          THEN UNCHANGED <<managed, fdstore, cgroups, netifs, registry>>
          ELSE IF e.id # NoId
          THEN LET R == Released(i, managed, fdstore, cgroups, netifs, registry) IN
               /\ managed' = R.managed /\ fdstore' = R.fdstore /\ cgroups' = R.cgroups
               /\ netifs' = R.netifs /\ registry' = R.registry
          ELSE /\ managed' = managed \ {i}
               /\ fdstore' = {x \in fdstore : x.inode # i}
               /\ UNCHANGED <<cgroups, netifs, registry>>
    /\ lock' = IF FIX_RINGBUF_LOCK THEN NoLock ELSE lock
    /\ mgr' = [pc |-> "idle", inode |-> 0]
    /\ UNCHANGED <<Kernel, ringbuf, cl, wk, budget, hist>>

\* systemd-nsresourced restarts: workers die and their requests fail, PID 1
\* keeps the fd store, the pinned maps and ring buffer survive;
\* manager_startup() drops fd store entries without a registry entry,
\* reaps dead entries by id and re-adds live ones to the map
Restart ==
    /\ budget.restart > 0
    /\ mgr.pc = "idle"
    /\ budget' = [budget EXCEPT !.restart = @ - 1]
    /\ LET stale  == {i \in Inodes : registry[i].id # NoId /\ FIX_STARTUP_SWEEP /\ ~Alive(registry[i].id)}
           live   == {i \in Inodes : registry[i].id # NoId /\ i \notin stale}
           orphan == {f.inode : f \in {x \in fdstore : registry[x.inode].id = NoId}}
       IN /\ registry' = [i \in Inodes |-> IF i \in stale THEN NoEntry ELSE registry[i]]
          /\ managed' = (managed \ (stale \cup orphan)) \cup live
          /\ fdstore' = {x \in fdstore : x.inode \notin stale \cup orphan}
          /\ cgroups' = cgroups \ {CgOf(registry[i].id) : i \in stale}
          /\ netifs' = netifs \ {NetifOf(registry[i].id) : i \in stale}
    /\ lock' = NoLock
    /\ wk' = [c \in Clients |-> "done"]
    /\ cl' = [c \in Clients |-> IF cl[c].pc = "alloc" THEN [cl[c] EXCEPT !.pc = "failed"] ELSE cl[c]]
    /\ UNCHANGED <<Kernel, ringbuf, mgr, hist>>

(***************************************************************************)
(* The specification                                                       *)
(***************************************************************************)
Init ==
    /\ nsAlive = {}
    /\ nsInode = [n \in Ids |-> 0]
    /\ nsRefs = [n \in Ids |-> 0]
    /\ nsRange = [n \in Ids |-> "none"]
    /\ freeInodes = Inodes
    /\ nextId = 1
    /\ managed = {}
    /\ ringbuf = <<>>
    /\ fdstore = {}
    /\ registry = [i \in Inodes |-> NoEntry]
    /\ lock = NoLock
    /\ cgroups = {}
    /\ netifs = {}
    /\ cl = [c \in Clients |-> [pc |-> "idle", ns |-> NoId]]
    /\ wk = [c \in Clients |-> "done"]
    /\ mgr = [pc |-> "idle", inode |-> 0]
    /\ budget = [restart |-> RestartBudget]
    /\ hist = [dropped |-> FALSE, starved |-> FALSE]

Next ==
    \/ \E c \in Clients : Create(c) \/ Drop(c) \/ WLock(c) \/ WSlot(c) \/ WRange(c) \/ WPush(c) \/ WResources(c)
    \/ \E n \in Ids : NsDie(n)
    \/ MgrTake \/ MgrRelease
    \/ Restart

\* Workers, the manager and the kernel are fair; clients may keep a
\* namespace forever, and restarts never have to happen.
Fairness ==
    /\ \A c \in Clients : WF_vars(WLock(c) \/ WSlot(c) \/ WRange(c) \/ WPush(c))
    /\ \A n \in Ids : WF_vars(NsDie(n))
    /\ WF_vars(MgrTake \/ MgrRelease)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ nsAlive \subseteq Ids
    /\ nextId \in 1..(IdMax + 1)
    /\ managed \subseteq Inodes
    /\ freeInodes \subseteq Inodes
    /\ lock \in Clients \cup {NoLock, Mgr}
    /\ \A f \in fdstore : f.inode \in Inodes /\ f.id \in Ids
    /\ Len(ringbuf) <= RingCap

\* Two live namespaces never map the same transient range.
LiveRangesDisjoint ==
    \A n, m \in nsAlive : n # m /\ nsRange[n] # "none" => nsRange[n] # nsRange[m]

\* A live namespace that holds a range is subject to the BPF policy.
ManagedCoversLive ==
    \A n \in nsAlive : nsRange[n] # "none" => nsInode[n] \in managed

\* The cgroup and the interface delegated to a live namespace are not
\* destroyed behind its back.
ResourcesOfLiveKept ==
    \A i \in Inodes : LET e == registry[i] IN
        e.id # NoId /\ Alive(e.id) => (e.cg => CgOf(e.id) \in cgroups) /\ (e.netif => NetifOf(e.id) \in netifs)

\* A request fails with NoDynamicRange only when every range is held by a
\* live namespace, never because of one a dead namespace still holds.
NoStarvationByDead == ~hist.starved

\* The registry never describes a live namespace under the wrong inode.
RegistryConsistent ==
    \A i \in Inodes : LET e == registry[i] IN
        e.id # NoId /\ Alive(e.id) => nsInode[e.id] = i

\* Liveness: a namespace nobody uses any more dies.
UnusedNamespaceDies ==
    \A n \in Ids : [](n \in nsAlive /\ nsRefs[n] = 0 => <>(n \notin nsAlive))

\* Liveness: the range of a dead namespace is returned to the pool.
RangeReclaimed ==
    \A i \in Inodes : [](registry[i].id # NoId /\ ~Alive(registry[i].id) => <>(registry[i].id = NoId \/ Alive(registry[i].id)))

=============================================================================
