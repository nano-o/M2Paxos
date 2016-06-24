------------------------------ MODULE Objects ------------------------------

(***************************************************************************)
(* This module defines the constants Commands, the set of commands,        *)
(* Object, the set of objects that commands may access, and AccessedBy(_), *)
(* where AccessedBy(c) is the set of objects accessed by the command c.    *)
(***************************************************************************)

EXTENDS Misc

CONSTANTS Commands, AccessedBy(_), Objects

ASSUME \A c \in Commands : AccessedBy(c) \in SUBSET Objects

NotACommand == CHOOSE x : x \notin Commands

=============================================================================
\* Modification History
\* Last modified Fri Jun 24 13:20:03 EDT 2016 by nano
\* Created Wed Nov 18 23:02:07 EST 2015 by nano
