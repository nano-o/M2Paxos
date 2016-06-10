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
const_14655906134502235000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Objects
const_14655906134602236000 == 
{o1, o2, o3}
----

\* CONSTANT definitions @modelParameterConstants:2AccessedBy(c)
const_14655906134702237000(c) == 
CASE c = c1 -> {o1, o2}
[] c = c2 -> {o2,o3}
[] c = c3 -> {o3,o1}
----

\* CONSTANT definitions @modelParameterConstants:3Instances
const_14655906134802238000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:4LeaseId
const_14655906134902239000 == 
0..1
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_14655906135012240000(X) ==
BSeq(X,3)
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_14655906135112241000 ==
0..10
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14655906135412244000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_14655906135512245000 ==
WeakCorrectness
----
=============================================================================
\* Modification History
\* Created Fri Jun 10 16:30:13 EDT 2016 by nano
