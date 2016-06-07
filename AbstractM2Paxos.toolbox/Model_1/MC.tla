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
const_1465314181816467000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Objects
const_1465314181826468000 == 
{o1, o2, o3}
----

\* CONSTANT definitions @modelParameterConstants:0Quorums
const_1465314181836469000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:3AccessedBy(c)
const_1465314181846470000(c) == 
CASE c = c1 -> {o1, o2}
[] c = c2 -> {o2,o3}
[] c = c3 -> {o3,o1}
----

\* CONSTANT definitions @modelParameterConstants:4Instances
const_1465314181856471000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:5LeaseId
const_1465314181866472000 == 
0..2
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1465314181887474000(X) ==
BSeq(X,3)
----
\* CONSTANT definition @modelParameterDefinitions:2
def_ov_1465314181897475000 ==
0..100
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1465314181907476000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1465314181917477000 ==
Cardinality(DependencyGraph(Seqs(decision))[1]) # 2
----
=============================================================================
\* Modification History
\* Created Tue Jun 07 11:43:01 EDT 2016 by nano
