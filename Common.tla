------------------------------- MODULE Common -------------------------------

EXTENDS Naturals, TLC

CONSTANT V
None == CHOOSE x : x \notin V

(***************************************************************************)
(* All sequences of elements of X which have a length smaller or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
BSeq(X, b) == {<<>>} \cup UNION {[1..n -> X] : n \in 1..b}

Image(f) == {f[x] : x \in DOMAIN f}

=============================================================================
\* Modification History
\* Last modified Mon Jun 06 14:03:17 EDT 2016 by nano
\* Created Thu Feb 04 16:55:11 EST 2016 by nano
