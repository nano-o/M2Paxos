------------------------------ MODULE M2Paxos ------------------------------

(***************************************************************************)
(* An abstract specification of M2Paxos.  It consists in coordinating      *)
(* several MultiPaxos instances (one per object).                          *)
(***************************************************************************)

EXTENDS MultiConsensus, Sequences, Objects

ASSUME Commands = V

(***************************************************************************)
(* ballot and vote are functions from object to "ballot" and "vote"        *)
(* structures of the MultiPaxos specification.                             *)
(***************************************************************************)
VARIABLES
    ballots, votes, propCmds

(***************************************************************************)
(* The MultiPaxos incarnation of object o.                                 *)
(***************************************************************************)
MultiPaxos(o) == 
    INSTANCE MultiPaxos WITH
        ballot <- ballots[o], 
        vote <- votes[o]
    
(***************************************************************************)
(* The initial state                                                       *)
(***************************************************************************)
InitBallot == [a \in Acceptors |-> -1]
InitVote == [a \in Acceptors |-> 
    [i \in Instances |-> [b \in Ballots |-> None]]]
Init ==
    /\  ballots = [o \in Objects |-> InitBallot]
    /\  votes = [o \in Objects |-> InitVote]
    /\  propCmds = {}

(***************************************************************************)
(* Is instance i of object o complete?                                     *)
(***************************************************************************)
Complete(o, i) ==
    \E v \in V : MultiPaxos(o)!Chosen(i, v)

(***************************************************************************)
(* The next undecided instance for object o:                               *)
(***************************************************************************)
NextInstance(o) ==
    LET completed == {i \in Instances : Complete(o, i)}
    IN  IF completed # {}
        THEN Max(completed, <=) + 1
        ELSE Max(Instances, \geq) \* the minimum instance

(***************************************************************************)
(* The next-state relation:                                                *)
(*                                                                         *)
(* Either an acceptor executes the JoinBallot action in the MultiPaxos     *)
(* incarnation of an object o, or, for a command c, an acceptor executes   *)
(* the Vote action in all MultiPaxos incarnations that correspond to an    *)
(* object that the command c accesses.                                     *)
(*                                                                         *)
(* Note that for each object o, an acceptor only votes in the instance     *)
(* whose predecessor is the largest instance in which a command was        *)
(* decided for o.                                                          *)
(***************************************************************************)

\* Join a higher ballot for an object:
JoinBallot(a, o, b) ==
    /\  MultiPaxos(o)!JoinBallot(a, b)
    /\  \A obj \in Objects \ {o} : UNCHANGED <<ballots[obj], votes[obj]>>

(***************************************************************************)
(* Vote for c in all of the instances of c's objects.  Note that we must   *)
(* not leave any gaps in the instance sequence, otherwise we leave open    *)
(* the possibility for interleaving.  What are the practical implications  *)
(* of this? It seems that one cannot propose a new command before the      *)
(* outcome of the previous command is known...  This can probably be fixed *)
(* by always increasing the instance in which one proposes and, upon       *)
(* ownership acquisition, completing all pending instances and starting    *)
(* proposing in bigger instances.  Maybe model this explicitely.           *)
(***************************************************************************)
Vote(a, c) ==
    /\ c \in propCmds
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
\* Last modified Tue Jun 07 09:13:00 EDT 2016 by nano
\* Created Mon Nov 02 14:55:16 EST 2015 by nano