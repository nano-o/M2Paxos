------------------------------ MODULE M2Paxos2 ------------------------------

(***************************************************************************)
(* An abstract specification of M2Paxos.  It consists in coordinating      *)
(* several MultiPaxos instances (one per object).                          *)
(***************************************************************************)

EXTENDS Sequences, Objects, FiniteSets, Integers

CONSTANT Acceptors, Quorums, MaxBallot, MaxInstance, LeaseId

ASSUME LeaseId \subseteq Nat

ASSUME \A Q \in Quorums : Q \subseteq Acceptors

ASSUME \A Q1,Q2 \in Quorums : Q1 \cap Q2 # {}

(***************************************************************************)
(* Majority quorums.                                                       *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET Acceptors :
    Cardinality(Q) > Cardinality(Acceptors) \div 2}

Instances == 1..MaxInstance

Ballots == 0..MaxBallot

(***************************************************************************)
(* For each object o and acceptor a, ballots[o][a] indicates the current   *)
(* ballot of a.  For each object o, acceptor a, instance i, and ballot b,  *)
(* vote[o][a][i][b] indicates what vote (if any) acceptor a cast in        *)
(* instance i of object o.                                                 *)
(***************************************************************************)
VARIABLES
    ballots, votes, lease

TypeInvariant ==
    /\  ballots \in [Acceptors -> [Objects -> Ballots]]
    /\  votes \in [Acceptors -> [Objects ->
            [Instances -> [Ballots -> Commands]]]]
    /\  lease \in [Objects -> [Acceptors -> LeaseId]]
    \* /\  leases \in [LeaseId ->  {[D -> Ballots] : D \in SUBSET Objects}]

(***************************************************************************)
(* The initial state.                                                      *)
(***************************************************************************)
Init ==
    /\  ballots = [a \in Acceptors |-> [o \in Objects |-> -1]]
    /\  votes = [a \in Acceptors |-> [o \in Objects |->
            [i \in Instances |-> [b \in Ballots |-> None(Commands)]]]]
    /\  lease \in [Acceptors -> [Objects -> LeaseId]]
    

LocalLeaseObjects(l, a) == {o \in Objects : lease[a][o] = l}
LeaseObjects(l) == UNION {LocalLeaseObjects(l, a) : a \in Acceptors}
 
LocalActiveLeases(a) == {lease[a][o] : o \in Objects}

(***************************************************************************)
(* We now define a refinement mapping between the state of this            *)
(* specification and the state of the AbstractM2Paxos specification.  For  *)
(* that we need a few definitions.                                         *)
(***************************************************************************)
    
(***************************************************************************)
(* A command c (or the value Aborted) is chosen in instance i at ballot b  *)
(* for object o if there is a quorum of acceptors that voted for c in      *)
(* instance i and at ballot b of object o.                                 *)
(***************************************************************************)
ChosenAt(o, i, b, c) ==
    \E Q \in Quorums : \A a \in Q : votes[a][o][i][b] = c

(***************************************************************************)
(* A command c (or the value Aborted) is chosen in instance i for object o *)
(* if there is a ballot b such that c is chosen at i and b for object o.   *)
(***************************************************************************)
Chosen(o,i,c) ==
    \E b \in Ballots : ChosenAt(o,i,b,c)
    
(***************************************************************************)
(* A lease is valid if a quorum of acceptors have it locally.              *)
(***************************************************************************)
Active(l) == \E Q \in Quorums : \A a \in Q :
    l \in LocalActiveLeases(a)

(***************************************************************************)
(* The refinement.                                                         *)
(***************************************************************************)
A == INSTANCE AbstractM2Paxos WITH
    instances <- [o \in Objects |-> [i \in Instances |-> 
        IF \E c \in Commands : Chosen(o, i, c)
        THEN CHOOSE c \in Commands : Chosen(o, i, c)
        ELSE None(Commands) ]],
    lease <- [o \in Objects |-> 
        IF \E l \in LeaseId : o \in LeaseObjects(l) /\ Active(l)
        THEN CHOOSE l \in LeaseId : o \in LeaseObjects(l) /\ Active(l)
        ELSE None(LeaseId)]

(***************************************************************************)
(* A lease is for a fixed set of objects.                                  *)
(***************************************************************************)
LeasesWellFormed == \A l \in LeaseId : \A a1,a2 \in Acceptors :
    LET os1 == LocalLeaseObjects(l, a1)
        os2 == LocalLeaseObjects(l, a2)
    IN
        os1 # {} /\ os2 # {} => os1 = os2      

(***************************************************************************)
(* Accept a new lease l on a set of objects os.                            *)
(***************************************************************************)
AcceptLease(a, l, os) ==
    /\ l \notin LocalActiveLeases(a)
    \* Choose one ballot per object
    /\ \E bs \in [os -> Ballots] :
        /\ \A o \in os : ballots[o][a] < bs[o]
        /\ ballots' = [ballots EXCEPT ![a] = [o \in Objects |->
            IF o \in os 
            THEN bs[o]
            ELSE ballots[a][o] ]]
    /\ lease' = [lease EXCEPT ![a] = [o \in Objects |-> 
        IF o \in os  THEN l ELSE lease[a][o] ]]
    /\  UNCHANGED votes
    \* A lease is for the same set of objects on all replicas:
    /\ LeasesWellFormed'
    \* TODO: what about breaking only safe leases?

(***************************************************************************)
(* A command is allocated one instance per object it accesses.  TODO: here *)
(* it seems we need to introduce the notion of proposal, giving an         *)
(* instance for each object.  Should a proposal be tied to a lease?        *)
(* Probably yes.  Should proposals be made "in order"? Probably yes.       *)
(***************************************************************************)
VotesWellFormed == TRUE
    
(***************************************************************************)
(* Vote for c in all of the instances of c's objects.                      *)
(***************************************************************************)
Vote(a, c) ==
    /\ \E is \in [AccessedBy(c) -> Instances] :
        /\  \A obj \in AccessedBy(c) : is[obj] <= NextInstance(obj)
        /\  \A o \in AccessedBy(c) :
                MultiPaxos(o)!Vote(a, c, is[o])
    /\  \A o \in Objects \ AccessedBy(c) : UNCHANGED <<ballots[o], votes[o]>>
    
Propose(v) ==
    /\  propCmds' = propCmds \cup {v}
    /\  UNCHANGED <<ballots, votes>>
    
Next ==
    \/  \E c \in V : Propose(c)
    \/  \E o \in Objects : \E a \in Acceptors : \E b \in Ballots : 
            JoinBallot(a, o, b)
    \/  \E c \in Commands : \E a \in Acceptors :
            Vote(a, c)

Spec == Init /\ [][Next]_<<ballots, votes, propCmds>>  

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)    

(***************************************************************************)
(* We start by defining the execution sequence of an object o.  This is    *)
(* the longest prefix of sequence describing the commands that are chosen  *)
(* in the MultiPaxos incarnation of object o.                              *)
(***************************************************************************)
\* We redefine chosen because of a problem with the toolbox (a bug?)
Chosen2(o, i, c) == \E b \in Ballots :
    \E Q \in Quorums : \A a \in Q : votes[o][a][i][b] = c

RECURSIVE ExecutionSequenceRec(_,_)
ExecutionSequenceRec(o, s) ==
    IF Len(s)+1 \in Instances /\ \E c \in Commands : Chosen2(o, Len(s)+1, c)
    THEN 
        LET chosen == CHOOSE c \in Commands : Chosen2(o, Len(s)+1, c)
        IN  ExecutionSequenceRec(o, Append(s, chosen))
    ELSE s

ExecutionSequence(o) == ExecutionSequenceRec(o,<<>>)

(***************************************************************************)
(* We now define the projection of a command sequence onto object o.  This *)
(* is the longest subsequence in which all commands access o.              *)
(***************************************************************************)
RECURSIVE ProjectOnObject(_,_)
ProjectOnObject(o, s) ==
     IF s = <<>>
     THEN <<>>
     ELSE IF o \in AccessedBy(Head(s))
        THEN IF Len(s) = 1 
            THEN <<Head(s)>> 
            ELSE <<Head(s)>> \o ProjectOnObject(o, Tail(s))
        ELSE ProjectOnObject(o, Tail(s))    

 (***************************************************************************)
 (* Prefix relation on sequences                                            *)
 (***************************************************************************)
 Prefix(s1,s2) ==
     /\  Len(s1) <= Len(s2)
     /\  \A i \in DOMAIN s1 : s1[i] = s2[i]

(***************************************************************************)
(* The Correctness property: given two objects o1 and o2, if s1 is the     *)
(* execution sequence of o1 projected on the commands accesing o2, and s2  *)
(* s1 is the execution sequence of o2 projected on the commands accessing  *)
(* o1, then s1 is a prefix of s2 or vice versa.                            *)
(*                                                                         *)
(* TODO: this is not sufficient! In a 3-objects scenario we might end up   *)
(* with a cylcle.                                                          *)
(***************************************************************************)
Correctness == \A o1,o2 \in Objects : o1 # o2 =>
    LET s1 == ProjectOnObject(o2, ExecutionSequence(o1))
        s2 == ProjectOnObject(o1, ExecutionSequence(o2))
    IN Prefix(s1,s2) \/ Prefix(s2,s1)
        
THEOREM Spec => []Correctness

(***************************************************************************)
(* The spec above cannot be used with TLC because TLC does not accept      *)
(* statements like fun[x]' = y (updating the value of a function on just a *)
(* subset of its domain), and that's what happens when we reuse the        *)
(* specification of MultiPaxos.  Below is a second version of the spec,    *)
(* which should be equivalent to the one above, and which can be           *)
(* model-checked with TLC.                                                 *)
(***************************************************************************)
    
JoinBallot2(a, o, b) ==
    /\  ballots' = [ballots EXCEPT ![o] = [ballots[o] EXCEPT ![a] = b]]
    /\  UNCHANGED votes
    /\  MultiPaxos(o)!JoinBallot(a, b)

Vote2(c, a) ==
    \* Vote for c in all of the instances of c's objects:
    /\ c \in propCmds
    /\ \E is \in [AccessedBy(c) -> Instances] : 
        /\  \A obj \in AccessedBy(c) : is[obj] <= NextInstance(obj) /\ is[obj] \in Instances   
        /\  votes' = [o \in Objects |->
                IF o \in AccessedBy(c)
                THEN 
                    [votes[o] EXCEPT ![a] = [@ EXCEPT ![is[o]] = 
                        IF ballots[o][a] # -1
                        THEN [@ EXCEPT ![ballots[o][a]] = c]
                        ELSE @]]
                ELSE votes[o]]
    /\  UNCHANGED ballots
    \* Only do the updates above if all of the instances can take the transition according to MultiPaxos: 
    /\  \A o \in AccessedBy(c) : \E i \in Instances :
            MultiPaxos(o)!Vote(a, c, i)


(***************************************************************************)
(* An equivalent version of Next which can be used with TLC                *)
(***************************************************************************)
Next2 ==
    \/  \E o \in Objects : \E a \in Acceptors : \E b \in Ballots :
            JoinBallot2(a, o, b)
    \/  \E c \in Commands : \E a \in Acceptors :
            Vote2(c, a)
    \/  \E c \in V : Propose(c)

Spec2 == Init /\ [][Next2]_<<ballots, votes, propCmds>> 

=============================================================================
\* Modification History
\* Last modified Thu Jun 23 12:28:46 EDT 2016 by nano
\* Created Mon Jun 06 13:48:20 EDT 2016 by nano
