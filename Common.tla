------------------------------- MODULE Common -------------------------------

EXTENDS Naturals, TLC

(***************************************************************************)
(* All sequences of elements of X which have a length smaller or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
BSeq(X, b) == {<<>>} \cup UNION {[1..n -> X] : n \in 1..b}


=============================================================================
\* Modification History
\* Last modified Wed Jun 22 16:57:21 EDT 2016 by nano
\* Created Thu Feb 04 16:55:11 EST 2016 by nano
