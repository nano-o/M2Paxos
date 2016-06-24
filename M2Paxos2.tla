------------------------------ MODULE M2Paxos2 ------------------------------

(***************************************************************************)
(* An abstract specification of M2Paxos.  It consists in coordinating      *)
(* several MultiPaxos instances (one per object).                          *)
(***************************************************************************)

EXTENDS Sequences, Objects, FiniteSets, Integers, Maps

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
(* A proposal is tied to a lease and assigns one instance to each object   *)
(* accessed by the command.                                                *)
(***************************************************************************)
Lease(p) == p[3]
Command(p) == p[1]
Slots(p) == p[2]
IsProposal(p) == 
    /\ Command(p) \in Commands
    /\ Slots(p) \in [AccessedBy(p[1]) -> Instances]
    /\ Lease(p) \in LeaseId

VARIABLES
    ballots, votes, leases, proposals

TypeInvariant ==
    /\  ballots \in [Acceptors -> [Objects -> Ballots]]
    /\  votes \in [Acceptors -> [Objects ->
            [Instances -> [Ballots -> Commands]]]]
    /\  \E L \in SUBSET LeaseId : leases \in [L ->
            {[D -> Ballots] : D \in SUBSET Objects}]
    /\  \A p \in proposals : IsProposal(p) 

(***************************************************************************)
(* Another invariant                                                       *)
(***************************************************************************)
Inv1 == \A p \in proposals :
    /\  Lease(p) \in DOMAIN leases 
    /\  AccessedBy(Command(p)) \subseteq DOMAIN leases[Lease(p)]
    

(***************************************************************************)
(* The initial state.                                                      *)
(***************************************************************************)
Init ==
    /\  ballots = [a \in Acceptors |-> [o \in Objects |-> -1]]
    /\  votes = [a \in Acceptors |-> [o \in Objects |->
            [i \in Instances |-> [b \in Ballots |-> None(Commands)]]]]
    /\  leases = <<>>
    /\  proposals = {}

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
Chosen(o, i, c) ==
    \E b \in Ballots : ChosenAt(o, i, b, c)

Executed(c) == \A o \in AccessedBy(c) : \E i \in Instances : 
    Chosen(o, i, c)

ExecutedWithLease(c, l) == \E Q \in Quorums : \A a \in Q :
    \A o \in AccessedBy(c) : \E i \in Instances :
        votes[a][o][i][leases[l][o]] = c

(***************************************************************************)
(* A lease is valid if a quorum of acceptors have it locally.              *)
(***************************************************************************) 
IsLocalActiveLease(l, a) == 
    \A o \in DOMAIN leases[l] : ballots[a][o] = leases[l][o]

Active(l) == \E Q \in Quorums : \A a \in Q : IsLocalActiveLease(l, a)

(***************************************************************************)
(* The refinement.                                                         *)
(***************************************************************************)
Get(S, P(_)) == IF \E x \in S : P(x) THEN CHOOSE x \in S : P(x) ELSE None(S)
 
A == INSTANCE AbstractM2Paxos WITH
    instances <- [o \in Objects |-> [i \in Instances |-> 
        Get(Commands, LAMBDA c : Chosen(o, i, c))]],
    lease <- [o \in Objects |-> 
        Get(LeaseId, LAMBDA l : o \in DOMAIN leases[l] /\ Active(l))]

(***************************************************************************)
(* Create a lease on an arbitrary non-empty set of objects with arbitrary  *)
(* ballots.                                                                *)
(***************************************************************************)
NewLease(l) ==
    /\ l \notin DOMAIN leases
    /\ \E os \in SUBSET Objects \ {} : \E bs \in [os -> Ballots] :
        leases' = leases ++ <<l, bs>>
    /\ UNCHANGED <<ballots, votes, proposals>>
    
(***************************************************************************)
(* Accept a new lease l on a set of objects os.                            *)
(***************************************************************************)
AcceptLease(a, l) ==
    /\ l \in DOMAIN leases
    /\ \A o \in DOMAIN leases[l] : ballots[o][a] < leases[l][o]
    /\ ballots' = [ballots EXCEPT ![a] = [o \in Objects |->
        IF o \in DOMAIN leases[l]
        THEN leases[l][o]
        ELSE ballots[a][o]]]
    /\ UNCHANGED <<votes, proposals, leases>>
    \* TODO: what about breaking only safe leases? => not needed if we forbid running parallel instances on the same lease.
    
Propose(c, l) ==
    /\ l \in DOMAIN leases
    /\ \A p \in proposals : Lease(p) = l => Command(p) # c
    \* Wait for all other proposals in the same lease to be executed.
    /\ \A p \in proposals : Lease(p) = l => ExecutedWithLease(Command(p), l)
    \* Choose an instance for every object accessed by c, leaving no holes:
    /\ \E is \in [AccessedBy(c) -> Instances] :
        /\ \A o \in AccessedBy(c) : \A i \in Instances : i < is[o] =>
            \E c2 \in Commands : Chosen(o, i, c2)
        /\ proposals' = proposals \cup {<<c,is,l>>}
    /\  UNCHANGED <<ballots, votes, leases>>
    
Vote(a) ==
    /\ \E p \in proposals :
        /\ \A o \in DOMAIN Slots(p) : ballots[a][o] = leases[Lease(p)][o]
        /\ votes' = [votes EXCEPT ![a] = [o \in Objects |->
            IF o \in AccessedBy(Command(p))
            THEN [votes[a][o] EXCEPT ![Slots(p)[o]] = Command(p)]
            ELSE votes[a][o]]]
    /\ UNCHANGED <<ballots, leases, proposals>>
    
Next ==
    \/  \E l \in LeaseId : NewLease(l)
    \/  \E a \in Acceptors, l \in LeaseId : AcceptLease(a, l)
    \/  \E c \in Commands : \E l \in LeaseId : Propose(c, l)
    \/  \E a \in Acceptors : Vote(a)

Spec == Init /\ [][Next]_<<ballots, votes, proposals, leases>>

=============================================================================
\* Modification History
\* Last modified Fri Jun 24 13:13:05 EDT 2016 by nano
\* Created Mon Jun 06 13:48:20 EDT 2016 by nano