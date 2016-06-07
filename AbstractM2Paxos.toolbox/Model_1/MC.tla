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
const_14653165532721051000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Objects
const_14653165532821052000 == 
{o1, o2, o3}
----

\* CONSTANT definitions @modelParameterConstants:0Quorums
const_14653165532921053000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:3AccessedBy(c)
const_14653165533021054000(c) == 
CASE c = c1 -> {o1, o2}
[] c = c2 -> {o2,o3}
[] c = c3 -> {o3,o1}
----

\* CONSTANT definitions @modelParameterConstants:4Instances
const_14653165533121055000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:5LeaseId
const_14653165533221056000 == 
0..2
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_14653165533431058000(X) ==
BSeq(X,3)
----
\* CONSTANT definition @modelParameterDefinitions:2
def_ov_14653165533531059000 ==
0..100
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14653165533631060000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_14653165533731061000 ==
\neg(decision[o1][1] = c1 /\ decision[o2][2] = c1 /\ decision[o2][1] = c2 /\ decision[o3][2] = c2 /\ decision[o3][1] = c3 /\ decision[o1][2] = c3)
----
=============================================================================
\* Modification History
\* Created Tue Jun 07 12:22:33 EDT 2016 by nano
