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
const_14653185199421480000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Objects
const_14653185199521481000 == 
{o1, o2, o3}
----

\* CONSTANT definitions @modelParameterConstants:0Quorums
const_14653185199621482000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:3AccessedBy(c)
const_14653185199721483000(c) == 
CASE c = c1 -> {o1, o2}
[] c = c2 -> {o2,o3}
[] c = c3 -> {o3,o1}
----

\* CONSTANT definitions @modelParameterConstants:4Instances
const_14653185199821484000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:5LeaseId
const_14653185199921485000 == 
0..4
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_14653185200131487000(X) ==
BSeq(X,3)
----
\* CONSTANT definition @modelParameterDefinitions:2
def_ov_14653185200231488000 ==
0..100
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14653185200331489000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_14653185200431490000 ==
Correctness(Seqs(decision))
----
=============================================================================
\* Modification History
\* Created Tue Jun 07 12:55:20 EDT 2016 by nano
