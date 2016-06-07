---------------------------- MODULE Correctness ----------------------------

(***************************************************************************)
(* Correctness condition for M2Paxos.                                      *)
(***************************************************************************)

EXTENDS Objects, Sequences, Naturals, TLC, Maps

INSTANCE DiGraph WITH V <- Commands

(***************************************************************************)
(* For each object, the M2Paxos algorithm builds a sequence of operations  *)
(* that we model as a map from object to sequence of commands.  Such a map *)
(* is well-formed when there are no duplicate commands in any sequence,    *)
(* and if c is in object o's sequence, the o is in the set of objects      *)
(* accessed by c.                                                          *)
(***************************************************************************)
WellFormed(seqs) ==
    /\ seqs \in [Objects -> Seq(Commands)]
    /\ \A o \in Objects : NoDup(seqs[o])
    /\ \A o \in Objects : \A c \in Image(seqs[o]) :
        o \in AccessedBy(c)

(***************************************************************************)
(* A command c1 depends on a command c2 if there is an object for which c1 *)
(* appears before c2 in the object's sequence.  The dependency relation    *)
(* can be seen as a graph.                                                 *)
(***************************************************************************)
DependencyGraph(seqs) ==
    LET Vs == UNION {Image(seqs[o]) : o \in Objects}
        Es == {e \in Vs \X Vs : \E o \in Objects :
            LET s == seqs[o] IN \E i \in DOMAIN s :
                /\ i # Len(s)
                /\ s[i] = e[1]
                /\ s[i+1] = e[2]}
    IN <<Vs, Es>>
    
(***************************************************************************)
(* The correctness property: the dependency graph must be well-formed  and *)
(* acyclic.                                                                *)
(***************************************************************************)
Correctness(seqs) == LET G == DependencyGraph(seqs) IN
    /\ WellFormed(seqs)
    /\ \neg HasCycle(G)

(***************************************************************************)
(* Now we define a stronger correctness property which excludes sequence   *)
(* maps which satisfy the definition above but in which a command is       *)
(* blocked, e.g.  when we have two objects o1 and o2, two commands c1 and  *)
(* c2 accessing both, a such that:                                         *)
(*                                                                         *)
(*     /\  seqs[o1] = <<c1, c2>>                                           *)
(*     /\  seqs[o2] = <<c2>>                                               *)
(*                                                                         *)
(* Here it is no possible to extend seqs[o2] with c1, and we say c1 is     *)
(* blocked.                                                                *)
(***************************************************************************)
    
(***************************************************************************)
(* A well-formed sequence map is complete when if the command c is in an   *)
(* object's sequence, then for all objects o accessed by c, c is also in   *)
(* o's sequence.                                                           *)
(***************************************************************************)
IsComplete(seqs) == \A c \in Commands : \A o1,o2 \in Objects :
    /\ c \in Image(seqs[o1])
    /\ o2 \in AccessedBy(c)
    => c \in Image(seqs[o2])

(***************************************************************************)
(* Pointwise prefix on maps                                                *)
(***************************************************************************)
IsPrefix(seqs1, seqs2) ==
    \A o \in Objects : Prefix(seqs1[o], seqs2[o])

(***************************************************************************)
(* The stronger correctness property: a sequence map is correct if it can  *)
(* be extended to a correct and complete sequence map.                     *)
(***************************************************************************)
Correctness2(seqs) == \E seqs2 \in [Objects -> Seq(Commands)] :
    /\ IsPrefix(seqs, seqs2)
    /\ IsComplete(seqs2)
    /\ Correctness(seqs2)

=============================================================================
\* Modification History
\* Last modified Tue Jun 07 10:59:10 EDT 2016 by nano
\* Created Mon Jun 06 14:59:29 EDT 2016 by nano