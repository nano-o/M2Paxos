------------------------------ MODULE Objects ------------------------------

CONSTANTS Commands, AccessedBy(_), Objects

(***************************************************************************)
(* AccessedBy(c) is the set of objects accessed by c.                      *)
(***************************************************************************)
ASSUME \A c \in Commands : AccessedBy(c) \in SUBSET Objects

=============================================================================
\* Modification History
\* Last modified Wed Nov 18 23:03:37 EST 2015 by nano
\* Created Wed Nov 18 23:02:07 EST 2015 by nano
