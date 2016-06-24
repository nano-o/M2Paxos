------------------------------- MODULE Misc -------------------------------

EXTENDS Naturals

Some(S) == CHOOSE e \in S : TRUE

(***************************************************************************)
(* All sequences of elements of X which have a length smaller or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
BSeq(X, b) == {<<>>} \cup UNION {[1..n -> X] : n \in 1..b}

Min(i,j) == IF i < j THEN i ELSE j

Max(S, LessEq(_,_)) == CHOOSE e \in S : \A e1 \in S : LessEq(e1,e)

IfExistsElse(S, P(_), d) == IF \E x \in S : P(x) THEN CHOOSE x \in S : P(x) ELSE d

=============================================================================
\* Modification History
\* Last modified Fri Jun 24 14:27:44 EDT 2016 by nano
\* Created Thu Feb 04 16:55:11 EST 2016 by nano
