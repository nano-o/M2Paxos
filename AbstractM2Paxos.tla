-------------------------- MODULE AbstractM2Paxos --------------------------

EXTENDS Correctness, Objects, Integers, Maps

CONSTANT Instances
ASSUME Instances = Nat \ {0} \/ \E i \in Nat : Instances = 1..i

CONSTANT LeaseId
ASSUME LeaseId \subseteq Nat

(***************************************************************************)
(* The algorithms maintains a sequence of instances per object.  Processes *)
(* called the proposers (not explicitely modeled here) can execute a       *)
(* command by inserting it in all of the sequences of the objects it       *)
(* accesses.  The algorithm guarantees that there is a total order among   *)
(* commands such that each object's sequence can be interpreted as a       *)
(* subset of the total order.  To implement this guarantee, proposers      *)
(* acquire exclusive leases on sets of objects before executing commands.  *)
(***************************************************************************)

(***************************************************************************)
(* For every object o and instance i, decision[o][i] is the decision made  *)
(* in instance i of object o.  For every object o, lease[o] describes the  *)
(* lease that o is currently participating in.  For example, lease[o1] = 2 *)
(* and objs[2] = {o1, o2} means that o1 accepted lease number 2 involving  *)
(* o1 and o2.  The lease owner can then submit commands accessing o1 and   *)
(* o2 to o1.  For each object o, minInstance[o] is the minimum available   *)
(* instance for commands accessing objects in the lease that o is          *)
(* currently in.  The domain of leases is the set of created leases, and   *)
(* leases[l] is the set of objects of l.  The variable executed tracks the *)
(* set of commands which have been executed.                               *)
(***************************************************************************)
VARIABLES decision, lease, minInstance, leases, executed

TypeInvariant ==
    /\ decision \in [Objects -> [Instances -> Commands \cup {None}]]
    /\ lease \in [Objects -> LeaseId \cup {-1}]
    /\ minInstance \in [Objects -> Instances]
    /\ \E L \in SUBSET LeaseId : leases \in [L -> SUBSET Objects]
    /\ executed \in SUBSET Commands
    
AvailableLeaseIds == LeaseId \ DOMAIN leases
    
Init ==
    /\ decision = [o \in Objects |-> [i \in Instances |-> None]]
    /\ lease = [o \in Objects |-> -1]
    /\ minInstance = [o \in Objects |-> 1]
    /\ leases = <<>>
    /\ executed = {}

(***************************************************************************)
(* To use the definitions from the Correctness module, we need to obtain   *)
(* per-object sequences of commands which do not contain any holes.        *)
(***************************************************************************)
IsBijection(f, X, Y) ==
    /\  DOMAIN f = X 
    /\  Image(f) = Y
    /\  \A x,y \in X : x # y => f[x] # f[y]
    /\  \A y \in Y : \E x \in X : f[x] = y

IsInjective(f) == \A x,y \in DOMAIN f : x # y => f[x] # f[y]

IsIncreasing(f) ==
    \A x,y \in DOMAIN f : x <= y => f[x] <= f[y]
    
IsSubSequence(s1, s2) == 
    \E f \in [DOMAIN s1 -> DOMAIN s2] :
        /\  IsInjective(f)
        /\  IsIncreasing(f)
        /\  \A i \in DOMAIN s1 : s1[i] = s2[f[i]]

Seqs(ds) == 
    LET RemoveHoles(s) == SelectSeq(s, LAMBDA x : x # None)
    IN [o \in Objects |-> RemoveHoles(ds[o])]

Max(xs) ==  CHOOSE x \in xs : \A y \in xs : y <= x

MaxDecision(o) == 
    IF \E i \in Instances : decision[o][i] # None 
    THEN Max({i \in Instances : decision[o][i] # None})
    ELSE 0

(***************************************************************************)
(* The owner of a lease maintains the protocol correctness property while  *)
(* the lease holds: if it decides c1 before c2 on object o1, then it       *)
(* cannot decide c2 before c1 on object o2.                                *)
(***************************************************************************)
LocalCorrectness(l) ==
    LET view == [o \in Objects |-> 
            IF o \in leases[l] /\ minInstance[o] # 0 /\ MaxDecision(o) # 0
            THEN SubSeq(decision[o], minInstance[o], MaxDecision(o))
            ELSE <<>>]
    IN  Correctness(Seqs(view))

InstancesAvailable(objs) ==
    \A o \in objs : \E i \in Instances : i >= minInstance[o] /\ decision[o][i] = None
    
Acquire(objs) == 
    /\ \A l \in DOMAIN leases : \neg objs \subseteq leases[l]
    /\  InstancesAvailable(objs)
    /\ \E l \in AvailableLeaseIds : 
        /\ lease' = [o \in Objects |->
            IF o \in objs THEN l ELSE lease[o]]
        /\ leases' = leases ++ <<l, objs>> 
    /\ minInstance' = [o \in Objects |-> 
        IF o \in objs THEN MaxDecision(o)+1 ELSE minInstance[o]]
    /\ UNCHANGED <<decision, executed>>

Invariant1 == \A o \in Objects : o \in leases[lease[o]]

(***************************************************************************)
(* A command c is executed if there is a lease on a superset of its        *)
(* accessed objects.                                                       *)
(***************************************************************************)
Exec(c) == \E l \in DOMAIN leases :
    /\ c \notin executed
    /\ \A o \in AccessedBy(c) : lease[o] = l
    /\ InstancesAvailable(AccessedBy(c))
    \* Choose one instance per accessed object where c will be decided:
    /\ \E is \in [AccessedBy(c) -> Instances] : 
        /\ \A o \in AccessedBy(c) :
            /\ is[o] >= minInstance[o]
            /\ decision[o][is[o]] = None
        /\ decision' = [o \in Objects |->
               IF o \notin AccessedBy(c) THEN decision[o]
               ELSE [decision[o] EXCEPT ![is[o]] = c]]  
    /\ executed' = executed \cup {c}
    /\ UNCHANGED <<lease, leases, minInstance>>
    \* Ensure that a lease owner does not create cycles on its own:
    /\ LocalCorrectness(l)'
    
\* An under-approximation of what leases are useful to acquire
ToAcquire == {AccessedBy(c) : c \in Commands} \cup {AccessedBy(c1) \cup AccessedBy(c2) : c1,c2 \in Commands}

Next == 
    \/  \E objs \in ToAcquire : Acquire(objs)
    \/  \E c \in Commands : Exec(c)    

Spec == Init /\ [][Next]_<<decision, lease, minInstance, leases, executed>>
    
THEOREM Spec => []Correctness2(Seqs(decision))

=============================================================================
\* Modification History
\* Last modified Tue Jun 07 12:55:43 EDT 2016 by nano
\* Created Tue Jun 07 09:31:03 EDT 2016 by nano
