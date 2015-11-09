---------------------------- MODULE MultiPaxos2 ----------------------------

(***************************************************************************)
(* A "reusable" version of the abstract specification of the MultiPaxos    *)
(* algorithm.  Instead of declaring two variables "ballot" and "vote", the *)
(* two actions JoinBallot and Vote take the parameters "ballot" and "vote" *)
(* because we would like to reuse the definition of the actions in a       *)
(* setting where we have an array of "ballot" and "vote" structures that   *)
(* should be modified using the two actions.                               *)
(*                                                                         *)
(* See MultiPaxos.tla for more comments.                                   *)
(***************************************************************************)

EXTENDS MultiConsensus

InitBallot == [a \in Acceptors |-> -1]
InitVote == [a \in Acceptors |-> [i \in Instances |-> [b \in Ballots |-> None]]]

Init(ballot, vote) ==
    /\  ballot = InitBallot
    /\  vote = InitVote
        
ChosenAt(i,b,v,vote) ==
    \E Q \in Quorums : \A a \in Q : vote[a][i][b] = v

Chosen(i,v,vote) ==
    \E b \in Ballots : ChosenAt(i,b,v,vote)
    
Complete(i, vote) ==
    \E v \in V : Chosen(i, v, vote)

MaxVotedBallot(i, a, max, vote) ==
    LET VotedIn == {b \in Ballots : b <= max /\ vote[a][i][b] # None}
    IN
        IF VotedIn # {}
        THEN Max(VotedIn, <=)
        ELSE -1

MaxVotedBallots(i, Q, max, vote) == {MaxVotedBallot(i, a, max, vote) : a \in Q}

HighestVote(i, Q, max, vote) == 
    IF \E a \in Q : MaxVotedBallot(i, a, max, vote) # -1
    THEN 
        LET MaxVoter == CHOOSE a \in Q : 
                MaxVotedBallot(i, a, max, vote) = Max(MaxVotedBallots(i, Q, max, vote), <=)
        IN vote[MaxVoter][i][MaxVotedBallot(i, MaxVoter, max, vote)]
    ELSE
        None

SafeAt(i, Q, b, ballot, vote) ==
    IF \A a \in Q : ballot[a] >= b
    THEN
        IF HighestVote(i, Q, b-1, vote) # None
        THEN {HighestVote(i, Q, b-1, vote)}
        ELSE V
    ELSE {}

Invariant1(ballot,vote) == \A a \in Acceptors : \A i \in Instances :
    MaxVotedBallot(i, a, ballot[1]+1, vote) <= ballot[a]
    
Conservative(i,b,vote) ==
    \A a1,a2 \in Acceptors :
        LET v1 == vote[a1][i][b]
            v2 == vote[a2][i][b]
        IN  (v1 # None /\ v2 # None) => v1 = v2
        
JoinBallot(a, b, ballot, vote) == 
    /\  ballot[a] < b
    /\  ballot' = [ballot EXCEPT ![a] = b]
    /\  UNCHANGED vote

Vote(a, i, v, ballot, vote) ==
    /\  ballot[a] # -1
    /\  vote[a][i][ballot[a]] = None
    /\  \E Q \in Quorums : 
            /\  v \in SafeAt(i, Q, ballot[a], ballot, vote)
            /\  vote' = [vote EXCEPT ![a] = [@ EXCEPT ![i] = [@ EXCEPT ![ballot[a]] = v]]]
    /\  UNCHANGED ballot
    /\  Conservative(i, ballot[a],vote)' \* Implemented by the leader in real algorithms.
    
Next(ballot, vote) == 
    \/  \E a \in Acceptors : \E b \in Ballots : JoinBallot(a, b, ballot, vote)
    \/  \E a \in Acceptors : \E i \in Instances : \E v\in V : Vote(a, i, v, ballot, vote)
    
Correctness(vote) ==  
    \A i \in Instances : \A b1,b2 \in Ballots : \A v1,v2 \in V :
        ChosenAt(i,b1,v1,vote) /\ ChosenAt(i,b2,v2,vote) => v1 = v2

=============================================================================
\* Modification History
\* Last modified Tue Nov 03 10:24:25 EST 2015 by nano
\* Created Mon Nov 02 15:08:08 EST 2015 by nano
