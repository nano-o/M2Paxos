------------------------------ MODULE Objects ------------------------------

(***************************************************************************)
(* This module defines the constants Commands, the set of commands,        *)
(* Object, the set of objects that commands may access, and AccessedBy(_), *)
(* where AccessedBy(c) is the set of objects accessed by the command c.    *)
(***************************************************************************)

CONSTANTS Commands, AccessedBy(_), Objects, Quorums

None == CHOOSE c : c \notin Commands

ASSUME \A c \in Commands : AccessedBy(c) \in SUBSET Objects

=============================================================================
\* Modification History
\* Last modified Tue Jun 07 09:35:50 EDT 2016 by nano
\* Created Wed Nov 18 23:02:07 EST 2015 by nano
