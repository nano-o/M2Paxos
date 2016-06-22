---------------------------- MODULE Correctness ----------------------------

(***************************************************************************)
(* We are interested in implementing State-Machine Replication (SMR)       *)
(* accross multiple replicas communicating in an asynchronous network.     *)
(* Each replica has a copy of the same state machine, which accepts        *)
(* commands that modify the state of the state machine and return an       *)
(* output.  Roughly speaking, the goal of the M2Paxos algorithm is to meet *)
(* the following requirements despite the possible failure of strictly     *)
(* less than half of the replicas:                                         *)
(*                                                                         *)
(*     1)  ensure that if two replicas produce an output at position i in  *)
(*         their sequence of outputs, then the output is the same;         *)
(*     2)  if new commands to be accepted keep coming, the every replica   *)
(*         that does not fail keeps producing new outputs.                 *)
(*                                                                         *)
(* Here we are concerned with requirement 1.                               *)
(*                                                                         *)
(* One way to meet requirement 1 is to have each replica execute requests  *)
(* in a unique total order, e.g.  like in the Multi-Paxos algorithm.       *)
(* However, sometime the order in which two or more commands are executed  *)
(* does not influence their output or the output of any future commands;   *)
(* we ways that such commands commute.  By allowing different replicas to  *)
(* execute commuting commands in a different order, an SMR algorithm might *)
(* improve its performance compared to Multi-Paxos.  This is our goal with *)
(* M2Paxos.                                                                *)
(*                                                                         *)
(* To take advantage of commutativity, we assume that the state machine to *)
(* be replicated accepts commands which access a determined set of         *)
(* objects, modifying those object's state and computing command output    *)
(* based on those object's state.  Observe that in this model, two         *)
(* commands that access disjoint sets of objects commute, and therefore    *)
(* need not be executed in the same order on all replicas.                 *)
(*                                                                         *)
(* Instead of enforcing that all replicas execute commands in a unique     *)
(* total order, a replica running M2Paxos maintains one sequence of        *)
(* commands per object, where sequences contain no duplicate commands,     *)
(* called an object-sequence map.  M2Paxos enforces that, for each object, *)
(* the sequences of the replicas are all prefixes of the same total order. *)
(*                                                                         *)
(* Replicas execute commands based on their object-sequence map according  *)
(* to the following execution rule.  Once a command c appears in all the   *)
(* sequences of the objects it accesses, and all commands comming before c *)
(* in those sequences have been executed, then c can be executed.          *)
(*                                                                         *)
(* However, this alone is not sufficient to meet requirement 1 because     *)
(* commands that do not commute must be execute in the same total order by *)
(* all replicas.  For example, consider two objects o1 and o2 and two      *)
(* commands c1 and c2 that access both objects.  Also consider two         *)
(* replicas and a global system state in which replica 1 computed the      *)
(* following sequences for object o1 and o2:                               *)
(*                                                                         *)
(*     replica1[o1] = <<c1,c2>>                                            *)
(*     replica1[o2] = <<c2>>                                               *)
(*                                                                         *)
(* while replica 2 computed the following sequences for object o1 and o2:  *)
(*                                                                         *)
(*     replica2[o1] = <<c1>>                                               *)
(*     replica2[o2] = <<c2,c1>>                                            *)
(*                                                                         *)
(* In this situation, for each object, the sequence of the replicas are    *)
(* both prefix of the same total order (<<c1,c2>> for o1 and <<c2,c1>> for *)
(* o2).  However, according to the rule for execution, replica 1 may       *)
(* execute c1 then c2, while replica 2 may execute c2 then c1, potentially *)
(* violating requirement 1.                                                *)
(*                                                                         *)
(* M2Paxos therefore enforces an additional property of the per-object     *)
(* sequences that replicas build.  Define the global object-sequence map   *)
(* of the system as the mapping an object o to the longest sequence than   *)
(* any replica has in its local map for o.  Moreover, given two commands   *)
(* c1 and c2, we say that c1 depends on c2 if c2 appears before c1 in the  *)
(* sequence of one object in the global objec-sequence map.  M2Paxos       *)
(* ensures that the dependency relation given by the global                *)
(* object-sequence map is acyclic.  This guarantees that if replicas       *)
(* follow the execution rule, then every two commands that do not commute  *)
(* will be executed in the same order by all replicas.  Observe that in    *)
(* the example above, the global object-sequence map has a cycle.          *)
(*                                                                         *)
(* In this TLA module, we formally define the guarantee of M2Paxos that    *)
(* were informally described above.                                        *)
(***************************************************************************)

EXTENDS Objects, Sequences, Naturals, Maps, SequenceUtils, TLC

INSTANCE DiGraph

(***************************************************************************)
(* An object-sequence map is well-formed when there are no duplicate       *)
(* commands in any sequence, and if c is in object o's sequence, then o is *)
(* in the set of objects accessed by c.                                    *)
(***************************************************************************)
WellFormed(map) ==
    /\ map \in [Objects -> Seq(Commands)]
    /\ \A o \in Objects : NoDup(map[o])
    /\ \A o \in Objects : \A c \in Image(map[o]) :
        o \in AccessedBy(c)

(***************************************************************************)
(* A command c1 depends on a command c2 if there is an object accessed by  *)
(* both c1 and c2 for which c1 appears before c2 in the object's sequence, *)
(* or c1 appears in the object sequence but not c2 (which will therefore   *)
(* have to come after c1).  The dependency relation can be seen as a       *)
(* graph.                                                                  *)
(***************************************************************************)
DependencyGraph(map) ==
    LET Vs == UNION {Image(map[o]) : o \in Objects}
        Es == {e \in Vs \X Vs : \E o \in Objects :
            LET s == map[o] IN \E i \in DOMAIN s :
                \/  /\ i # Len(s)
                    /\ s[i] = e[1]
                    /\ s[i+1] = e[2]
                \/  /\ o \in AccessedBy(e[2])  
                    /\ s[i] = e[1]
                    /\ e[2] \notin Image(s) }
    IN <<Vs, Es>>
    
(***************************************************************************)
(* An object-sequence map is correct when its dependency graph has no      *)
(* cycles.                                                                 *)
(***************************************************************************)
MapCorrectness(gm) == \neg HasCycle(DependencyGraph(gm))

(***************************************************************************)
(* The global system state associates to each replica node a local         *)
(* object-sequence map.                                                    *)
(***************************************************************************)
IsGlobalState(gs) ==
    \A s \in DOMAIN gs : gs[s] \in [Objects -> Seq(Commands)]

(***************************************************************************)
(* The global object-sequence map.                                         *)
(***************************************************************************)
GlobalMap(gs) ==
    LET MaxSeq(ss) == CHOOSE s \in ss : \A t \in ss : Len(t) <= Len(s)
        ObjSeqs(o) == {s[o] : s \in {gs[x] : x \in DOMAIN gs}}
    IN [o \in Objects |-> MaxSeq(ObjSeqs(o))]

(***************************************************************************)
(* Correctness of the global state:                                        *)
(*     1)  Every replica has a well-formed local object-sequence map;      *)
(*     2)  For each object, all replicas agree on a total order of commands; *)
(*     3)  The global object-sequence map is acyclic.                      *)
(***************************************************************************)
Correctness(gs) == 
    LET replicas == DOMAIN gs 
    IN  /\ \A r \in replicas : WellFormed(gs[r])
        /\ \A o \in Objects : \A r1,r2 \in replicas :
            LET s1 == gs[r1][o]
                s2 == gs[r2][o]
            IN Prefix(s1,s2) \/ Prefix(s2,s1)
        /\  \neg HasCycle(DependencyGraph(GlobalMap(gs)))

=============================================================================
\* Modification History
\* Last modified Tue Jun 21 22:14:43 EDT 2016 by nano
\* Created Mon Jun 06 14:59:29 EDT 2016 by nano