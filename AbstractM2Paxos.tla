-------------------------- MODULE AbstractM2Paxos --------------------------

EXTENDS Objects, Maps, SequenceUtils, Integers

C == INSTANCE Correctness

(***************************************************************************)
(* In this module we specifies an algorithm describing how M2Paxos uses    *)
(* leases on objects to maintain the correctness property of the global    *)
(* object-sequence map while repeatedly increasing the set of commands     *)
(* that can be executed by the replicas.  This specification describes at  *)
(* an abstract level how leases and the global object-sequence map evolve, *)
(* without any distributed-system model.                                   *)
(***************************************************************************)

(***************************************************************************)
(* The algorithm maintains a sequence of instances per object, were an     *)
(* instance can hold a command, or the special values Unknown and Aborted. *)
(* The global object-sequence map is obtained from the object-instances    *)
(* map by ignoring the instances that have value Aborted, truncating the   *)
(* sequence at the first Unknown value encountered, and removing duplicate *)
(* commands.                                                               *)
(***************************************************************************)

CONSTANT Instances
ASSUME Instances = Nat \ {0} \/ \E i \in Nat : Instances = 1..i
VARIABLE instances

Unknown == CHOOSE x : x \notin Commands
Aborted == CHOOSE x : x \notin Commands \cup {Unknown}

GlobalMap(is) ==
    [o \in Objects |->
        LET unknowns == {i \in DOMAIN is[o] : is[o][i] = Unknown}
            firstUnknown ==
                IF unknowns # {} 
                THEN Max(unknowns, LAMBDA i,j : j <= i) - 1
                ELSE Len(is[o])
            truncated == SubSeq(is[o], 1, firstUnknown)
            filtered == SelectSeq(truncated, LAMBDA x : x # Aborted)  
        IN RemDup(filtered)]


Correctness(is) ==
    \E m \in [Objects -> Seq(Commands)] :
        LET gm == GlobalMap(is)
        IN  /\ C!IsPrefix(gm,m)
            /\ C!IsComplete(m)
            /\ \neg C!HasCycle(C!DependencyGraph(m))

(***************************************************************************)
(* At any moment in time, an object is part of a unique lease, noted       *)
(* lease[o][1], and has a minimum instance for that lease, noted           *)
(* lease[o][2].                                                            *)
(***************************************************************************)
CONSTANT LeaseId
ASSUME LeaseId \subseteq Nat
VARIABLE lease

ActiveLeases == {l \in LeaseId : \E o \in Objects : lease[o][1] = l}
LeaseObjects(l) == {o \in Objects : lease[o][1] = l}

(***************************************************************************)
(* A command c can be assigned to a set of instances {i[o] : o \in         *)
(* Objects}, one per object it accesses, when:                             *)
(*                                                                         *)
(*     1)  all the objects that c accesses are part of the same lease;     *)
(*     2)  for each object that c accesses, i[o] is greater or equal to the *)
(*         minimum instance of o for its current lease;                    *)
(*     3)  after the assignement, the object-sequence map obtained by      *)
(*         restricting the global object-sequence map to the objects accessed *)
(*         by c and, for each such object o, to the positions greater or   *)
(*         equal than lease[o][2], satisfies the correctness condition     *)
(*         for object-sequences.                                           *)
(*                                                                         *)
(* This process models a lease owner executing commands on the objects     *)
(* that are part of its lease.                                             *)
(*                                                                         *)
(* The condition 3 is specified in the definition LocalCorrectness(_)      *)
(* below, while the full action is specified in Order(_).                  *)
(***************************************************************************)

LocalCorrectness(l) ==
    LET view == [o \in Objects |-> 
        LET min == lease[o][2] 
        IN  IF o \in LeaseObjects(l)
            THEN SubSeq(instances[o], min, Len(instances[o]))
            ELSE <<>>]
    IN  Correctness(view)

(***************************************************************************)
(* Leases can change at any time.  When the lease of object o changes, the *)
(* minimum instance associated with the lease and object is set to the     *)
(* sucessor of the largest instance that does not contain Unknown.         *)
(* Moreover, all instances lower that the new minimum instance and that    *)
(* contain unknown are updated to contain Aborted.                         *)
(*                                                                         *)
(* Lease change is specified in the definition Acquire(_) below.           *)
(***************************************************************************)


(***************************************************************************)
(* A invariant describing the type of the variables.                       *)
(***************************************************************************)
TypeInvariant ==
    /\ instances \in [Objects -> [Instances -> Commands \cup {Unknown, Aborted}]]
    /\ lease \in [Objects -> LeaseId \times Instances]

(***************************************************************************)
(* The initial state.                                                      *)
(***************************************************************************)
ALease == CHOOSE l \in LeaseId : TRUE
Init ==
    /\ instances = [o \in Objects |-> [i \in Instances |-> Unknown]]
    /\ lease = [o \in Objects |-> <<ALease, 1>>]
    
(***************************************************************************)
(* The Acquire action.                                                     *)
(***************************************************************************)
AbortUnknown(s, min) ==
    [i \in DOMAIN s |-> 
        IF i < min /\ s[i] = Unknown
        THEN Aborted
        ELSE s[i]]

Acquire(objs) == 
    \* /\ \A l \in ActiveLeases : \neg objs \subseteq LeaseObjects(l)
    /\ \E l \in LeaseId \ ActiveLeases : 
        /\ lease' = [o \in Objects |->
            IF o \in objs THEN
                LET is == {i \in Instances : instances[o][i] \in Commands}
                    min == 
                        IF is # {} 
                        THEN Max(is, LAMBDA i,j : i <= j)
                        ELSE 1 
                IN  <<l,min>> 
            ELSE lease[o]]
    /\ instances' = [o \in Objects |-> AbortUnknown(instances[o], lease'[o][2])]


(***************************************************************************)
(* A command c is executed if there is a lease on a superset of its        *)
(* accessed objects.                                                       *)
(***************************************************************************)
Exec(c) == \E l \in ActiveLeases :
    /\ AccessedBy(c) \subseteq LeaseObjects(l)
    \* Choose one instance per accessed object where c will be decided:
    /\ \E is \in [AccessedBy(c) -> Instances] :
        /\ \A o \in AccessedBy(c) :
            /\ is[o] >= lease[o][2]
            /\ instances[o][is[o]] = Unknown
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

WeakCorrectness == \neg C!HasCycle(C!DependencyGraph(GlobalMap(instances)))

THEOREM Spec => []WeakCorrectness

=============================================================================
\* Modification History
\* Last modified Fri Jun 10 16:34:03 EDT 2016 by nano
\* Created Tue Jun 07 09:31:03 EDT 2016 by nano
