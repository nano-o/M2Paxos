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
const_1466623592626422000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Objects
const_1466623592636423000 == 
{o1, o2, o3}
----

\* CONSTANT definitions @modelParameterConstants:2AccessedBy(c)
const_1466623592646424000(c) == 
CASE c = c1 -> {o1, o2}
[] c = c2 -> {o2,o3}
[] c = c3 -> {o3,o1}
----

\* CONSTANT definitions @modelParameterConstants:3Instances
const_1466623592657425000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:4LeaseId
const_1466623592667426000 == 
0..3
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1466623592677427000(X) ==
BSeq(X,3)
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1466623592687428000 ==
0..10
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1466623592707430000 ==
TRUE \/ \A l \in ActiveLeases : LeaseObjects(l) # Objects
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1466623592718431000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1466623592728432000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1466623592738433000 ==
Correctness(instances)
----
=============================================================================
\* Modification History
\* Created Wed Jun 22 15:26:32 EDT 2016 by nano
