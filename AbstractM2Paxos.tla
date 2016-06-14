-------------------------- MODULE AbstractM2Paxos --------------------------

(***************************************************************************)
(* This spec might be fine, but how to implement it in practice? It seems  *)
(* very tricky to acquire an new lease that is not a superset of existing  *)
(* leases: how are started but undecided instances going to be completed?  *)
(***************************************************************************)

EXTENDS Objects, Maps, SequenceUtils, Integers, FiniteSets

C == INSTANCE Correctness

(***************************************************************************)
(* In this module we specifies an algorithm describing how M2Paxos uses    *)
(* leases on objects to maintain the correctness property of the global    *)
(* object-sequence map (defined in the Correctness module) while           *)
(* repeatedly increasing the set of commands that can be executed by the   *)
(* replicas.  This specification describes at an abstract level how leases *)
(* and the global object-sequence map evolve, without any                  *)
(* distributed-system model.                                               *)
(***************************************************************************)

(***************************************************************************)
(* The algorithm maintains a sequence of instances per object, where an    *)
(* instance can hold a command, or the special values Free.  The global *)
(* object-sequence map is obtained from the object-instances map by        *)
(* truncating the sequence at the first Free value encountered, and     *)
(* then removing duplicate commands.                                       *)
(***************************************************************************)

CONSTANT Instances
ASSUME Instances = Nat \ {0} \/ \E i \in Nat : Instances = 1..i

Free == CHOOSE x : x \notin Commands
NoOp == CHOOSE x : x \notin Commands \cup {Free}

(***************************************************************************)
(* Truncate a sequence of instances right before the first Free value.  *)
(***************************************************************************)
RECURSIVE Truncate(_)
Truncate(vs) ==
    IF vs = <<>> \/ Head(vs) = Free
    THEN <<>>
    ELSE <<Head(vs)>> \o Truncate(Tail(vs))
    
FilterNoOps(vs) ==
    SelectSeq(vs, LAMBDA x : x # NoOp)

ObjectSequenceMap(is) ==
    [o \in Objects |-> RemDup(FilterNoOps(Truncate(is[o])))]

Correctness(is) == \neg C!HasCycle(C!DependencyGraph(ObjectSequenceMap(is)))

(***************************************************************************)
(* At any moment in time, an object is part of a unique lease, lease[o].   *)
(***************************************************************************)
CONSTANT LeaseId
ASSUME LeaseId \subseteq Nat

VARIABLE instances, lease

(***************************************************************************)
(* A invariant describing the type of the variables.                       *)
(***************************************************************************)
TypeInvariant ==
    /\ instances \in [Objects -> [Instances -> Commands \cup {Free, NoOp}]]
    /\ lease \in [Objects -> LeaseId]

ActiveLeases == {l \in LeaseId : \E o \in Objects : lease[o] = l}
LeaseObjects(l) == {o \in Objects : lease[o] = l}

(***************************************************************************)
(* A command c can be assigned to a set of instances {i[o] : o \in         *)
(* Objects}, one per object it accesses, when:                             *)
(*     1)  all the objects that c accesses are part of the same lease;     *)
(*     2)  instances[i[o]] holds value Free for all object accessed by     *)
(*         the command;                                                    *)
(*     3)  after the assignement, the object-sequence map obtained by      *)
(*         restricting the global object-sequence map to the objects accessed *)
(*         by c satisfies the correctness condition for object-sequences.  *)
(* This process models a lease owner executing commands on the objects     *)
(* that are part of its lease.                                             *)
(*                                                                         *)
(* The condition 3 is specified in the definition LocalCorrectness(_)      *)
(* below, while the full action is specified in Order(_).                  *)
(***************************************************************************)

LocalCorrectness(l) ==
    LET view == [o \in Objects |-> 
        IF o \in LeaseObjects(l)
        THEN instances[o]
        ELSE <<>>]
    IN  Correctness(view)
    
(***************************************************************************)
(* A lease is safe to break when:                                          *)
(*     1)  for every object o in the lease and instance i, if instances[o][i] *)
(*         holds a command, then for every other object o2 in the lease, then *)
(*         instances[o2][i] holds a command;                               *)
(*     2)  for every object o in the lease, instance i, and instance j < i, *)
(*         if instances[o][i] holds a command, then instances[o][j] holds  *)
(*         a command.                                                      *)
(***************************************************************************)

Safe(l) == 
    /\ \A o1,o2 \in LeaseObjects(l) : \A i \in Instances : 
        (instances[o1][i] \in Commands) = (instances[o2][i] \in Commands)
    /\ \A o \in  LeaseObjects(l) : \A i,j \in Instances :
        i < j /\ instances[o][j] \in Commands => instances[o][i] \in Commands

(***************************************************************************)
(* The initial state.                                                      *)
(***************************************************************************)
Init ==
    /\ instances = [o \in Objects |-> [i \in Instances |-> Free]]
    /\ lease \in [Objects -> LeaseId]
    
(***************************************************************************)
(* A new lease on the set of objects objs can be acquired only when the    *)
(* existing leases on those objects are safe.                              *)
(***************************************************************************)
Acquire(objs) == 
    /\ \A l \in ActiveLeases : LeaseObjects(l) \cap objs # {} => Safe(l)
    /\ \E l \in LeaseId \ ActiveLeases :
        /\ lease' = [o \in Objects |->
            IF o \in objs THEN l ELSE lease[o]]
    /\ UNCHANGED instances

(***************************************************************************)
(* A command c is executed if there is a lease on a superset of its        *)
(* accessed objects.                                                       *)
(***************************************************************************)
Exec(c) == \E l \in ActiveLeases :
    /\ AccessedBy(c) \subseteq LeaseObjects(l)
    \* Choose one instance per accessed object where c will be decided:
    /\ \E is \in [AccessedBy(c) -> Instances] :
        /\ \A o \in AccessedBy(c) : instances[o][is[o]] = Free
        /\ instances' = [o \in Objects |->
               IF o \notin AccessedBy(c) THEN instances[o]
               ELSE [instances[o] EXCEPT ![is[o]] = c]]
    /\ UNCHANGED lease
    \* Ensure that a lease owner does not create cycles on its own:
    /\ LocalCorrectness(l)'

Next == 
    \/  \E objs \in SUBSET Objects : Acquire(objs)
    \/  \E c \in Commands : Exec(c)

Spec == Init /\ [][Next]_<<lease, instances>>

THEOREM Spec => []Correctness(instances)

=============================================================================
\* Modification History
\* Last modified Tue Jun 14 12:17:12 EDT 2016 by nano
\* Created Tue Jun 07 09:31:03 EDT 2016 by nano