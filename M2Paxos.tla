------------------------------ MODULE M2Paxos ------------------------------

(***************************************************************************)
(* An abstract specification of M2Paxos.  It consists in coordinating      *)
(* several MultiPaxos instances (one per object).                          *)
(***************************************************************************)

EXTENDS MultiConsensus

CONSTANTS Commands, AccessedBy(_), Objects

ASSUME Commands = V

(***************************************************************************)
(* AccessedBy(c) is the set of objects accessed by c.                      *)
(***************************************************************************)
ASSUME \A c \in Commands : AccessedBy(c) \in SUBSET Objects

(***************************************************************************)
(* ballot and vote are functions from object to "ballot" and "vote"        *)
(* structures of the MultiPaxos specification.                             *)
(***************************************************************************)
VARIABLES
    ballots, votes, propCmds

(***************************************************************************)
(* The MultiPaxos instance of object o.                                    *)
(***************************************************************************)
MultiPaxos(o) == 
    INSTANCE MultiPaxos WITH
        ballot <- ballots[o], 
        vote <- votes[o]


InitBallot == [a \in Acceptors |-> -1]
InitVote == [a \in Acceptors |-> [i \in Instances |-> [b \in Ballots |-> None]]]
(***************************************************************************)
(* The initial state                                                       *)
(***************************************************************************)
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
        ELSE 0

(***************************************************************************)
(* The next-state relation:                                                *)
(*                                                                         *)
(* Either an acceptor executes the JoinBallot action in the MultiPaxos     *)
(* instance of an object o, or, for a command c, an acceptor executes the  *)
(* Vote action in all instances that correspond to an object that the      *)
(* command c accesses.                                                     *)
(*                                                                         *)
(* Note that for each object o, an acceptor only votes for command in the  *)
(* instance whose predecessor is the largest instance in which a command   *)
(* was decided for o, using a non-distributed implementation.  How to do   *)
(* it in a distributed way is not clear to me (maybe by requiring FIFO     *)
(* links?).                                                                *)
(***************************************************************************)

\* Join a higher ballot for an object:
JoinBallot(a, o, b) ==
    /\  MultiPaxos(o)!JoinBallot(a, b)
    /\  \A obj \in Objects \ {o} : UNCHANGED <<ballots[obj], votes[obj]>>

\* Vote for c in all of the instances of c's objects:
Vote(a, c) ==
    /\  \A o \in AccessedBy(c) :
            MultiPaxos(o)!Vote(a, NextInstance(o), c)
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

JoinBallot2(a, o, b) ==
    /\  ballots' = [ballots EXCEPT ![o] = [ballots[o] EXCEPT ![a] = b]]
    /\  UNCHANGED votes
    /\  MultiPaxos(o)!JoinBallot(a, b)

Vote2(c, a) ==
    \* Vote for c in all of the instances of c's objects:
    /\  votes' = [o \in Objects |->
            IF o \in AccessedBy(c)
            THEN [votes[o] EXCEPT ![a] = [@ EXCEPT ![NextInstance(o)] = 
                IF ballots[o][a] # -1 
                THEN [@ EXCEPT ![ballots[o][a]] = c]
                ELSE @]]
            ELSE votes[o]]
    /\  UNCHANGED ballots
    \* Only do the updates above if all of the instances can take the transition according to MultiPaxos: 
    /\  \A o \in AccessedBy(c) : \E i \in Instances :
            MultiPaxos(o)!Vote(a, c, i)
    \* and c has not been chosen before (just because it is a simple way to avoid duplicated commands):
    /\  \A i \in Instances : \A o \in Objects : \neg MultiPaxos(o)!Chosen(i, c)


(***************************************************************************)
(* An equivalent version of Next which can be used with TLC                *)
(***************************************************************************)
Next2 ==
    \/  \E o \in Objects : \E a \in Acceptors : \E b \in Ballots :
            JoinBallot2(a, o, b)
    \/  \E c \in Commands : \E a \in Acceptors :
            Vote2(c, a)
    \/  \E c \in V : Propose(c)

(***************************************************************************)
(* True when c1 has been chosen before c2 in the MultiPaxos instance       *)
(* associated to object o.                                                 *)
(***************************************************************************)
ChosenInOrder(c1, c2, o) ==
    \A i,j \in Instances : 
        MultiPaxos(o)!Chosen(i, c1) /\ MultiPaxos(o)!Chosen(j, c2)
        => i <= j

(***************************************************************************)
(* The correctness property: any two commands are ordered in the same way  *)
(* by the MultiPaxos instances corresponding to objects that both commands *)
(* access.                                                                 *)
(***************************************************************************)
Correctness ==
    \A c1,c2 \in Commands : \A o1,o2 \in AccessedBy(c1) \cap AccessedBy(c2) :
        ChosenInOrder(c1, c2, o1) = ChosenInOrder(c1, c2, o2)

=============================================================================
\* Modification History
\* Last modified Sun Nov 15 18:48:48 EST 2015 by nano
\* Created Mon Nov 02 14:55:16 EST 2015 by nano