---- MODULE MC ----
EXTENDS AbstractM2Paxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
o1, o2, o3
----

\* MV CONSTANT definitions Commands
const_1466631390188538000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Objects
const_1466631390198539000 == 
{o1, o2, o3}
----

\* CONSTANT definitions @modelParameterConstants:2AccessedBy(c)
const_1466631390208540000(c) == 
CASE c = c1 -> {o1, o2}
[] c = c2 -> {o2,o3}
[] c = c3 -> {o3,o1}
----

\* CONSTANT definitions @modelParameterConstants:3Instances
const_1466631390219541000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:4LeaseId
const_1466631390229542000 == 
0..3
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1466631390239543000(X) ==
BSeq(X,3)
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1466631390249544000 ==
0..10
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1466631390269546000 ==
TRUE \/ \A l \in ActiveLeases : LeaseObjects(l) # Objects
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1466631390279547000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1466631390289548000 ==
Correctness(instances)
----
=============================================================================
\* Modification History
\* Created Wed Jun 22 17:36:30 EDT 2016 by nano
