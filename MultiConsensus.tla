--------------------------- MODULE MultiConsensus ---------------------------
(***************************************************************************)
(* A set of constants and definitions for use in the specification of      *)
(* MultiPaxos-like algorithms.                                             *)
(***************************************************************************)

EXTENDS Integers, FiniteSets
    
CONSTANTS Acceptors, Quorums, MaxBallot, MaxInstance

ASSUME MaxBallot \in Nat

ASSUME MaxInstance \in Nat \ {0}

Instances == 1..MaxInstance 

Ballots == 0..MaxBallot

ASSUME \A Q \in Quorums : Q \subseteq Acceptors

ASSUME \A Q1,Q2 \in Quorums : Q1 \cap Q2 # {}

(***************************************************************************)
(* Majority quorums.                                                       *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET Acceptors : Cardinality(Q) > Cardinality(Acceptors) \div 2}

=============================================================================
\* Modification History
\* Last modified Fri Jun 10 16:42:50 EDT 2016 by nano
\* Created Mon Nov 02 19:28:17 EST 2015 by nano
