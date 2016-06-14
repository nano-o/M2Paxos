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
const_1465921111428170000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Objects
const_1465921111438171000 == 
{o1, o2, o3}
----

\* CONSTANT definitions @modelParameterConstants:2AccessedBy(c)
const_1465921111448172000(c) == 
CASE c = c1 -> {o1, o2}
[] c = c2 -> {o2,o3}
[] c = c3 -> {o3,o1}
----

\* CONSTANT definitions @modelParameterConstants:3Instances
const_1465921111458173000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:4LeaseId
const_1465921111468174000 == 
0..1
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1465921111478175000(X) ==
BSeq(X,3)
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1465921111488176000 ==
0..10
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1465921111519179000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1465921111529180000 ==
Correctness(instances)
----
=============================================================================
\* Modification History
\* Created Tue Jun 14 12:18:31 EDT 2016 by nano
