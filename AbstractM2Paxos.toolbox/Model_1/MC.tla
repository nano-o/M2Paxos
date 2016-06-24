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
const_1466792777693578000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Objects
const_1466792777703579000 == 
{o1, o2, o3}
----

\* CONSTANT definitions @modelParameterConstants:2AccessedBy(c)
const_1466792777713580000(c) == 
CASE c = c1 -> {o1, o2}
[] c = c2 -> {o2,o3}
[] c = c3 -> {o3,o1}
----

\* CONSTANT definitions @modelParameterConstants:3Instances
const_1466792777723581000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:4LeaseId
const_1466792777733582000 == 
0..3
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1466792777743583000(X) ==
BSeq(X,3)
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1466792777754584000 ==
0..10
----
\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1466792777764585000
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1466792777774586000 ==
TRUE \/ \A l \in ActiveLeases : LeaseObjects(l) # Objects
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1466792777784587000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1466792777794588000 ==
Correctness(instances)
----
=============================================================================
\* Modification History
\* Created Fri Jun 24 14:26:17 EDT 2016 by nano
