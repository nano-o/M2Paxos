------------------------------ MODULE M2Paxos ------------------------------

(***************************************************************************)
(* An abstract specification of M2Paxos.  It consists in coordinating      *)
(* several MultiPaxos instances (one per object).                          *)
(***************************************************************************)

EXTENDS MultiConsensus, Sequences, TLC, Objects

ASSUME Instances \subseteq Nat \ {0}

ASSUME Commands = V

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
        ELSE Max(Instances, \geq) \* the minimum instance

(***************************************************************************)
(* The next-state relation:                                                *)
(*                                                                         *)
(* Either an acceptor executes the JoinBallot action in the MultiPaxos     *)
(* instance of an object o, or, for a command c, an acceptor executes the  *)
(* Vote action in all instances that correspond to an object that the      *)
(* command c accesses.                                                     *)
(*                                                                         *)
(* Note that for each object o, an acceptor only votes in the instance     *)
(* whose predecessor is the largest instance in which a command was        *)
(* decided for o, using a non-distributed implementation.                  *)
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

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)    

(***************************************************************************)
(* True when c1 has been chosen before c2 in the MultiPaxos instance       *)
(* associated to object o.  This definition works only when there are no   *)
(* duplicate chosen commands.                                              *)
(***************************************************************************)
ChosenInOrder2(c1, c2, o) ==
    /\  c1 # c2
    /\  \E i,j \in Instances : 
            /\  MultiPaxos(o)!Chosen(i, c1) 
            /\  MultiPaxos(o)!Chosen(j, c2)
            /\  i < j
(***************************************************************************)
(* Have the commands in cs been chosen in instances of object o?           *)
(***************************************************************************)
Chosen(cs, o) ==
    \A c \in cs : \E i \in Instances : MultiPaxos(o)!Chosen(i, c)

(***************************************************************************)
(* A simplified correctness property: any two commands are ordered in the  *)
(* same way by the MultiPaxos instances corresponding to objects that both *)
(* commands access.  This correctness property is satisfied only if no     *)
(* duplicate commands can be chosen.                                       *)
(***************************************************************************)
CorrectnessSimple ==
    \A c1,c2 \in Commands : \A o1,o2 \in AccessedBy(c1) \cap AccessedBy(c2) :
        /\ ChosenInOrder2(c1, c2, o1) 
        /\ Chosen({c1, c2}, o2)
        => ChosenInOrder2(c1, c2, o2)
        
(***************************************************************************)
(* A more complex correctness condition that is satisfied by the spec,     *)
(* even in the presence of duplicate commands                              *)
(***************************************************************************)
        
(***************************************************************************)
(* Removing duplicates from a seqence                                      *)
(***************************************************************************)   
RECURSIVE RemDupRec(_,_)
 RemDupRec(es, seen) ==
   IF es = <<>>
   THEN <<>>
   ELSE
     IF es[1] \in seen
     THEN RemDupRec(Tail(es), seen)
     ELSE <<es[1]>> \o RemDupRec(Tail(es), seen \cup {es[1]})
     
 RemDup(es) == RemDupRec(es, {})
 
(***************************************************************************)
(* For each object, the sequence of commands chosen with duplicates        *)
(* removed.                                                                *)
(***************************************************************************)
ChosenCmds == [o \in Objects |->
    LET s == [i \in Instances |-> 
                IF \E c \in propCmds : MultiPaxos(o)!Chosen(i, c)
                THEN CHOOSE c \in propCmds : MultiPaxos(o)!Chosen(i, c)
                ELSE None]
    IN RemDup(s)]
                     
(***************************************************************************)
(* The image of a function.                                                *)
(***************************************************************************)
Image(f) == {f[x] : x \in DOMAIN f}

(***************************************************************************)
(* Has c1 been chosen before c2 for object o?                              *)
(***************************************************************************)
ChosenInOrder(c1, c2, o) ==
    LET s == ChosenCmds[o]
    IN
        /\  {c1,c2} \subseteq Image(s)
        /\  \A i,j \in DOMAIN s :
                s[i] = c1 /\ s[j] = c2 => i \leq j
  
(***************************************************************************)
(* Correctness: if two commands have been ordered for two different        *)
(* objects, then their order is the same.                                  *)
(***************************************************************************)  
Correctness ==  \A c1,c2 \in Commands : 
    \A o1,o2 \in AccessedBy(c1) \cap AccessedBy(c2) :
        (\A o \in {o1,o2} : 
            c1 \in Image(ChosenCmds[o]) /\ c2 \in Image(ChosenCmds[o]))
        =>  (ChosenInOrder(c1, c2, o1) = ChosenInOrder(c1, c2, o2))

THEOREM Spec => []Correctness

(***************************************************************************)
(* The spec above cannot be used with TLC.  Below is a second version of   *)
(* the spec, which should be equivalent to the one above, and which can be *)
(* model-checked with TLC.                                                 *)
(***************************************************************************)

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
(* Model-checking results:                                                 *)
(*                                                                         *)
(* Model: 3 acceptors, 2 objects, 2 commands (1 accessing both, 1          *)
(* accessing only 1 object), majority quorums, 3 ballots, 3 instances.     *)
(*                                                                         *)
(* Checked CorrectnessSimple.                                              *)
(*                                                                         *)
(* State constraints:                                                      *)
(*     /\ \A o \in Objects : \E i \in Instances : \neg Complete(o, i)      *)
(*     /\ \A o \in Objects : \A a \in Acceptors : \A i \in Instances : \A c \in Commands : \neg MultiPaxos(o)!Chosen(i, votes[o][a][i]) *)
(*                                                                         *)
(* Running on 48 cores on whitewhale with 120GB of memory.                 *)
(*                                                                         *)
(* Exhaustive exploration completed: 674414109 states generated, 48486426  *)
(* distinct states found.  The depth of the complete state graph search is *)
(* 31.                                                                     *)
(*                                                                         *)
(***************************************************************************)

=============================================================================
\* Modification History
\* Last modified Tue Dec 01 11:40:04 EST 2015 by nano
\* Created Mon Nov 02 14:55:16 EST 2015 by nano