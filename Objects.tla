------------------------------ MODULE Objects ------------------------------

(***************************************************************************)
(* This module defines the constants Commands, the set of commands,        *)
(* Object, the set of objects that commands may access, and AccessedBy(_), *)
(* where AccessedBy(c) is the set of objects accessed by the command c.    *)
(***************************************************************************)

EXTENDS Misc

CONSTANTS Commands, AccessedBy(_), Objects

ASSUME \A c \in Commands : AccessedBy(c) \in SUBSET Objects

=============================================================================
\* Modification History
\* Last modified Fri Jun 10 12:59:59 EDT 2016 by nano
\* Created Wed Nov 18 23:02:07 EST 2015 by nano
