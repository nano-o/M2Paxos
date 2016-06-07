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
const_14653198459371647000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Objects
const_14653198459471648000 == 
{o1, o2, o3}
----

\* CONSTANT definitions @modelParameterConstants:0Quorums
const_14653198459571649000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:3AccessedBy(c)
const_14653198459671650000(c) == 
CASE c = c1 -> {o1, o2}
[] c = c2 -> {o2,o3}
[] c = c3 -> {o3,o1}
----

\* CONSTANT definitions @modelParameterConstants:4Instances
const_14653198459771651000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:5LeaseId
const_14653198459871652000 == 
0..3
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_14653198460081654000(X) ==
BSeq(X,3)
----
\* CONSTANT definition @modelParameterDefinitions:2
def_ov_14653198460181655000 ==
0..100
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14653198460281656000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_14653198460381657000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_14653198460481658000 ==
Correctness(Seqs(decision))
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_14653198460591659000 ==
Invariant1
----
=============================================================================
\* Modification History
\* Created Tue Jun 07 13:17:26 EDT 2016 by nano
