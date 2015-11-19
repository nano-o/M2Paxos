------------------------- MODULE DistributedM2Paxos -------------------------

(***************************************************************************)
(* A spec of M2Paxos based on DistributedMultiPaxos                        *)
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

TypeInv ==
    /\  ballots \in [Objects -> [Acceptors -> {-1} \cup Ballots]]
    /\  votes \in [Objects -> [Acceptors -> 
            [Instances -> 
                [Ballots -> {None} \cup V]]]]
    /\  network \in [Objects -> SUBSET Msgs]
    /\  propCmds \subseteq V

InitBallot == [a \in Acceptors |-> -1]
InitVote == [a \in Acceptors |-> [i \in Instances |-> [b \in Ballots |-> None]]]

Init ==
    /\  ballots = [o \in Objects |-> InitBallot]
    /\  votes = [o \in Objects |-> InitVote]
    /\  propCmds = {}
    /\  network = [o \in Objects |-> {}]


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
(* Here we must assume that there are no duplicate commands, otherwise it  *)
(* will break.                                                             *)
(***************************************************************************)
Phase2a(c) ==
    /\  \A o \in AccessedBy(c) : \E b \in Ballots, i \in Instances :
            DistMultiPaxos(o)!Phase2a(b, i, c)
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

(***************************************************************************)
(* We can't reuse DistMultiPaxos with TLC, so we need to reimplement       *)
(* everything...                                                           *)
(***************************************************************************)

(***************************************************************************)
(* This would be easier to write if all 1a messages were combined in the   *)
(* same message.                                                           *)
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
    LET OkForObj(o, i, b, Q) ==
        /\  \neg (\E m \in network[o] : m[1] = "2a" /\ m[2] = i /\ m[3] = b)
        /\ \A a \in Q : \E m \in DistMultiPaxos(o)!1bMsgs(b, i, Q) : m[2] = a
    IN
        /\  propCmds # {}
        /\ \A o \in AccessedBy(c) : \E i \in Instances, b \in Ballots, Q \in Quorums : OkForObj(o, i, b, Q)
        /\  LET qs == [o \in AccessedBy(c) |->  CHOOSE q \in Instances \times Ballots \times Quorums :
                            OkForObj(o, q[1], q[2], q[3])] 
                safe == [o \in AccessedBy(c) |->
                    LET maxV == DistMultiPaxos(o)!MaxVote(qs[o][2], qs[o][1] , qs[o][3])
                    IN  IF maxV # None THEN {maxV} ELSE propCmds]
            IN network' = [o \in Objects |->
                IF o \in AccessedBy(c)
                THEN
                    IF c \in safe[o]
                    THEN network[o] \cup {<<"2a", qs[o][1], qs[o][2], c>>}
                    ELSE network[o] \cup {<<"2a", qs[o][1], qs[o][2], CHOOSE v \in safe[o] : TRUE>>}
                ELSE network[o]]
    /\  UNCHANGED <<propCmds, ballots, votes>>
    /\ \A o \in AccessedBy(c) : \E b \in Ballots, i \in Instances : 
            DistMultiPaxos(o)!Phase2a(b,i,c) 

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
       
=============================================================================
\* Modification History
\* Last modified Thu Nov 19 10:43:44 EST 2015 by nano
\* Created Wed Nov 18 18:34:22 EST 2015 by nano
