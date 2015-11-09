------------------------------ MODULE M2Paxos ------------------------------

EXTENDS MultiConsensus
    
CONSTANTS Commands, AccessedBy(_), Objects

ASSUME Commands = V

(***************************************************************************)
(* A set of assumption about the constants                                 *)
(***************************************************************************)

ASSUME \A c \in Commands : AccessedBy(c) \in SUBSET Objects

(***************************************************************************)
(* We reuse the MultiPaxos specification.                                  *)
(***************************************************************************)
MultiPaxos == 
    INSTANCE MultiPaxos2

(***************************************************************************)
(* ballot and vote are functions from object to "ballot" and "vote"        *)
(* structures of the MultiPaxos specification.                             *)
(***************************************************************************)
VARIABLES
    ballot, vote
    
(***************************************************************************)
(* The initial state                                                       *)
(***************************************************************************)
Init ==
    /\  ballot = [o \in Objects |-> MultiPaxos!InitBallot]
    /\  vote = [o \in Objects |-> MultiPaxos!InitVote]

(***************************************************************************)
(* The next undecided instance for object o:                               *)
(***************************************************************************)
NextInstance(o) ==
    LET completed == {i \in Instances : MultiPaxos!Complete(i, vote[o])}
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
    /\  MultiPaxos!JoinBallot(a, b, ballot[o], vote[o])
    /\  \A o2 \in Objects \ {o} : UNCHANGED <<ballot[o2], vote[o2]>>

\* Vote for c in all of the instances of c's objects:
Vote(a, c) ==
    /\  \A o \in AccessedBy(c) :
            MultiPaxos!Vote(a, NextInstance(o), c, ballot[o], vote[o])
    /\  \A o \in Objects \ AccessedBy(c) : UNCHANGED <<ballot[o], vote[o]>>
    
Next ==
    \/  \E o \in Objects : \E a \in Acceptors : \E b \in Ballots : 
            JoinBallot(a, o, b)
    \/  \E c \in Commands : \E a \in Acceptors :
            Vote(a, c)

Spec == Init /\ [][Next]_<<ballot, vote>>      


(***************************************************************************)
(* An equivalent version of Next which can be used with TLC                *)
(***************************************************************************)
Next2 ==
    \*  Join a higher ballot in one instance:
    \/  \E o \in Objects : \E a \in Acceptors : \E b \in Ballots :
            /\  ballot' = [ballot EXCEPT ![o] = [ballot[o] EXCEPT ![a] = b]]
            /\  UNCHANGED vote
            /\  MultiPaxos!JoinBallot(a, b, ballot[o], vote[o])
    \* Vote for a command in all the instances corresponding to its accessed objects:
    \/  \E c \in Commands : \E a \in Acceptors :
            \* Vote for c in all of the instances of c's objects:
            /\  vote' = [o \in Objects |->
                    IF o \in AccessedBy(c)
                    THEN [vote[o] EXCEPT ![a] = [@ EXCEPT ![NextInstance(o)] = 
                        IF ballot[o][a] # -1 
                        THEN [@ EXCEPT ![ballot[o][a]] = c]
                        ELSE @]]
                    ELSE vote[o]]
            /\  UNCHANGED ballot
            \* Only do the updates above if all of the instances can take the transition according to MultiPaxos: 
            /\  \A o \in AccessedBy(c) : \E i \in Instances :
                    MultiPaxos!Vote(a, i, c, ballot[o], vote[o])
            \* and c has not been chosen before (just because it is a simple way to avoid duplicated commands):
            /\  \A i \in Instances : \A o \in Objects : \neg MultiPaxos!Chosen(i, c, vote[o])
    

(***************************************************************************)
(* The correctness property: any two commands are ordered in the same way  *)
(* by the MultiPaxos instances corresponding to objects that both commands *)
(* access.                                                                 *)
(***************************************************************************)
ChosenInOrder(c1, c2, o) ==
    \A i,j \in Instances : 
        MultiPaxos!Chosen(i, c1, vote[o]) /\ MultiPaxos!Chosen(j, c2, vote[o])
        => i <= j

Correctness ==
    \A c1,c2 \in Commands : \A o1,o2 \in AccessedBy(c1) \cap AccessedBy(c2) :
        ChosenInOrder(c1, c2, o1) = ChosenInOrder(c1, c2, o2)

=============================================================================
\* Modification History
\* Last modified Thu Nov 05 14:56:51 EST 2015 by nano
\* Created Mon Nov 02 14:55:16 EST 2015 by nano
