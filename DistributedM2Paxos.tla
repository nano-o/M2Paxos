------------------------- MODULE DistributedM2Paxos -------------------------

(***************************************************************************)
(* A spec of M2Paxos based on DistributedMultiPaxos.                       *)
(***************************************************************************)

EXTENDS MultiConsensus, Objects

VARIABLES
    ballots, votes, network, propCmds

ASSUME Instances \subseteq Nat \ {0}

ASSUME Commands = V

DistMultiPaxos(o) == INSTANCE DistributedMultiPaxos WITH
    ballot <- ballots[o],
    vote <- votes[o],
    network <- network[o]
    
(***************************************************************************)
(* Is instance i of object o complete?                                     *)
(***************************************************************************)
Complete(o, i) ==
    \E v \in V : DistMultiPaxos(o)!MultiPaxos!Chosen(i, v)

(***************************************************************************)
(* The next undecided instance for object o:                               *)
(***************************************************************************)
NextInstance(o) ==
    LET completed == {i \in Instances : Complete(o, i)}
    IN  IF completed # {}
        THEN Max(completed, <=) + 1
        ELSE Max(Instances, \geq) \* the minimum instance

Msgs == DistMultiPaxos(CHOOSE o \in Objects : TRUE)!Msgs

(***************************************************************************)
(* A type invariant.                                                       *)
(***************************************************************************)
TypeInv ==
    /\  ballots \in [Objects -> [Acceptors -> {-1} \cup Ballots]]
    /\  votes \in [Objects -> [Acceptors -> 
            [Instances -> 
                [Ballots -> {None} \cup V]]]]
    /\  network \in [Objects -> SUBSET Msgs]
    /\  propCmds \subseteq V

InitBallot == [a \in Acceptors |-> -1]
InitVote == [a \in Acceptors |-> [i \in Instances |-> [b \in Ballots |-> None]]]

(***************************************************************************)
(* The initial state.                                                      *)
(***************************************************************************)
Init ==
    /\  ballots = [o \in Objects |-> InitBallot]
    /\  votes = [o \in Objects |-> InitVote]
    /\  propCmds = {}
    /\  network = [o \in Objects |-> {}]


(***************************************************************************)
(* The actions.                                                            *)
(***************************************************************************)

Propose(c) ==
    /\  propCmds' = propCmds \cup {c}
    /\  UNCHANGED <<ballots, votes, network>>

Phase1a(c) ==
    /\  \E bs \in [Objects -> Ballots] :
            network' = [o \in Objects |-> 
                    IF o \in AccessedBy(c)
                    THEN network[o] \cup {<<"1a", bs[o]>>}
                    ELSE network[o]]
    /\  UNCHANGED <<ballots, votes, propCmds>>

Phase1b(a, c) == 
    /\  \E b \in Ballots : 
            \A o \in AccessedBy(c) : DistMultiPaxos(o)!Phase1b(a, b, c)
    /\  \A o \in Objects \ AccessedBy(c) : UNCHANGED <<ballots[o], votes[o], network[o]>>

(***************************************************************************)
(* The Phase2a(c) action.                                                  *)
(*                                                                         *)
(* NextInstance could be computed from the 1b messages.  For simplicity,   *)
(* we reuse the NextInstance(_) operator.                                  *)
(***************************************************************************)
Phase2a(c) ==
    /\  \A o \in AccessedBy(c) : \E b \in Ballots :
            DistMultiPaxos(o)!Phase2a(b, NextInstance(o), c)
    /\  \A o \in Objects \ AccessedBy(c) : UNCHANGED <<network[o]>>
    /\  UNCHANGED <<propCmds, ballots, votes>>

Vote(a, c) ==
    /\  \A o \in AccessedBy(c) : \E b \in Ballots, i \in Instances :
            DistMultiPaxos(o)!Vote(a, b, i)
    /\  \A o \in Objects \ AccessedBy(c) : UNCHANGED votes[o]
    /\  UNCHANGED <<ballots, network, propCmds>>
    
Next ==
    \E c \in Commands : Propose(c) \/ Phase1a(c) \/ Phase2a(c)
        \/  \E a \in Acceptors :  Phase1b(a, c) \/ Vote(a, c)

Spec == Init /\ [][Next]_<<ballots, votes, network, propCmds>>

M2Paxos == INSTANCE M2Paxos

THEOREM Spec => []M2Paxos!Correctness 

(***************************************************************************)
(* The spec above cannot be used with TLC.  Below is a second version of   *)
(* the spec, which should be equivalent to the one above, and which can be *)
(* model-checked with TLC.                                                 *)
(***************************************************************************)

Phase1b2(a, c) == 
    /\  \A o \in AccessedBy(c) : \E b \in Ballots :
            /\  ballots[o][a] < b
            /\  <<"1a",b>> \in network[o]
    /\  LET bals == [o \in AccessedBy(c) |-> CHOOSE b \in Ballots :
                /\  ballots[o][a] < b
                /\  <<"1a", b>> \in network[o]]
        IN  /\  ballots' = [o \in Objects |-> 
                    IF o \in AccessedBy(c)
                    THEN [ballots[o] EXCEPT ![a] = bals[o]]
                    ELSE ballots[o]]
            /\  network' = [o \in Objects |->
                    IF o \in AccessedBy(c)
                    THEN network[o] \cup 
                        {<<"1b", a, i, bals[o], DistMultiPaxos(o)!MaxAcceptorVote(a,i)>> : i \in Instances}
                    ELSE network[o]]
    /\  UNCHANGED <<votes, propCmds>>
    /\  \E b \in Ballots : 
            \A o \in AccessedBy(c) : DistMultiPaxos(o)!Phase1b(a, b, c) 

Phase2a2(c) ==
    LET OkForObj(o, b, Q) ==
        /\  \neg (\E m \in network[o] : m[1] = "2a" /\ m[2] = NextInstance(o) /\ m[3] = b)
        /\ \A a \in Q : \E m \in DistMultiPaxos(o)!1bMsgs(b, NextInstance(o), Q) : m[2] = a
    IN
        /\  propCmds # {}
        /\ \A o \in AccessedBy(c) : \E b \in Ballots, Q \in Quorums : OkForObj(o, b, Q)
        /\  LET qs == [o \in AccessedBy(c) |->  CHOOSE q \in Ballots \times Quorums :
                            OkForObj(o, q[1], q[2])] 
                safe == [o \in AccessedBy(c) |->
                    LET maxV == DistMultiPaxos(o)!MaxVote(qs[o][1], NextInstance(o) , qs[o][2])
                    IN  IF maxV # None THEN {maxV} ELSE propCmds]
            IN network' = [o \in Objects |->
                IF o \in AccessedBy(c)
                THEN
                    IF c \in safe[o]
                    THEN network[o] \cup {<<"2a", NextInstance(o), qs[o][1], c>>}
                    ELSE network[o] \cup {<<"2a", NextInstance(o), qs[o][1], CHOOSE v \in safe[o] : TRUE>>}
                ELSE network[o]]
    /\  UNCHANGED <<propCmds, ballots, votes>>
    /\ \A o \in AccessedBy(c) : \E b \in Ballots : 
            DistMultiPaxos(o)!Phase2a(b,NextInstance(o),c) 

Vote2(a, c) ==
    /\  \A o \in AccessedBy(c) : \E i \in Instances :
            \E m \in network[o] : m[1] = "2a" /\ m[2] = i /\ m[3] = ballots[o][a] /\ m[4] = c
    /\  LET is == [o \in AccessedBy(c) |->
                CHOOSE i \in Instances : 
                    \E m \in network[o] : m[1] = "2a" /\ m[2] = i /\ m[3] = ballots[o][a] /\ m[4] = c]
        IN
        /\  votes' = [o \in Objects |->
                IF o \in AccessedBy(c)
                THEN [votes[o] EXCEPT ![a] = [@ EXCEPT ![is[o]] = [@ EXCEPT ![ballots[o][a]] = c]]]
                ELSE votes[o]]
    /\  UNCHANGED <<ballots, network, propCmds>>
    
Next2 ==
    \E c \in Commands : Propose(c) \/ Phase1a(c) \/ Phase2a2(c)
        \/  \E a \in Acceptors :  Phase1b2(a, c) \/ Vote2(a, c)

Spec2 == Init /\ [][Next2]_<<ballots, votes, network, propCmds>>

(***************************************************************************)
(* Model-checking results:                                                 *)
(*                                                                         *)
(* Configuration: 2 objects, 2 commands (one accessing both objects, one   *)
(* accessing only one object), 3 acceptors, majority quorums, 2 ballots, 2 *)
(* instances per object.                                                   *)
(*                                                                         *)
(* Checked the property M2Paxos!Correctness                                *)
(*                                                                         *)
(* Exhaustive exploration completed: 243636 distinct states generated,     *)
(* diameter 23, ran for 10 minutes.                                        *)
(*                                                                         *)
(***************************************************************************)
   
=============================================================================
\* Modification History
\* Last modified Tue Dec 01 11:40:20 EST 2015 by nano
\* Created Wed Nov 18 18:34:22 EST 2015 by nano
