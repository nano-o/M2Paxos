------------------------------ MODULE DiGraph ------------------------------

(***************************************************************************)
(* A few notions related to directed graphs.                               *)
(***************************************************************************)

EXTENDS FiniteSets, Sequences, Naturals, Misc, SequenceUtils
  
(***************************************************************************)
(* A digraph is a set of vertices and a set of edges, where an edge is a   *)
(* pair of vertices.                                                       *)
(***************************************************************************)
Vertices(G) == G[1]

Edges(G) == G[2]

IsDigraph(G) == Edges(G) \subseteq (Vertices(G) \times Vertices(G))

(***************************************************************************)
(* True when there exists a path from v1 to v2 in the graph G              *)
(***************************************************************************)
RECURSIVE DominatesRec(_,_,_,_) 
Dominates(v1, v2, G) ==
    DominatesRec(v1,v2,G,{})

(***************************************************************************)
(* Recursive implementation of Dominates(v1,v2,G).                         *)
(***************************************************************************)    
DominatesRec(v1, v2, G, acc) ==
    \/ <<v1,v2>> \in Edges(G)
    \/ \E v \in Vertices(G) : 
        /\ \neg v \in acc
        /\ <<v1,v>> \in Edges(G)
        /\ DominatesRec(v, v2, G, acc \cup {v1})
        
HasCycle(G) ==
    \E v1,v2 \in Vertices(G) : 
        /\  v1 # v2
        /\  Dominates(v1, v2, G)
        /\  Dominates(v2, v1, G)    

=============================================================================
\* Modification History
\* Last modified Wed Jun 22 16:56:37 EDT 2016 by nano
\* Created Tue Jul 28 03:10:02 CEST 2015 by nano
