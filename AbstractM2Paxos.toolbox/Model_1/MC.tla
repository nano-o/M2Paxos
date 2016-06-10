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
const_14655896531192104000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Objects
const_14655896531292105000 == 
{o1, o2, o3}
----

\* CONSTANT definitions @modelParameterConstants:2AccessedBy(c)
const_14655896531392106000(c) == 
CASE c = c1 -> {o1, o2}
[] c = c2 -> {o2,o3}
[] c = c3 -> {o3,o1}
----

\* CONSTANT definitions @modelParameterConstants:3Instances
const_14655896531492107000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:4LeaseId
const_14655896531592108000 == 
0..3
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_14655896531692109000(X) ==
BSeq(X,3)
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_14655896531802110000 ==
0..10
----
\* Constant expression definition @modelExpressionEval
const_expr_14655896532102113000 == 
C!Correctness(GlobalMap([o \in Objects |-> [i \in Instances |-> Unknown]]))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_14655896532102113000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14655896532202114000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_14655896532302115000 ==
Correctness(instances)
----
=============================================================================
\* Modification History
\* Created Fri Jun 10 16:14:13 EDT 2016 by nano
