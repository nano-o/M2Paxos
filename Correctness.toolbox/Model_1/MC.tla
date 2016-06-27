---- MODULE MC ----
EXTENDS Correctness, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
o1, o2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT definitions Objects
const_1467038690765103000 == 
{o1, o2}
----

\* MV CONSTANT definitions Commands
const_1467038690775104000 == 
{c1, c2}
----

\* MV CONSTANT definitions Replica
const_1467038690785105000 == 
{r1, r2}
----

\* CONSTANT definitions @modelParameterConstants:2AccessedBy(c)
const_1467038690795106000(c) == 
CASE c = c1 -> {o1,o2}
[] c = c2 -> {o1,o2}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1467038690805107000(X) ==
BSeq(X,Cardinality(Commands))
----
\* Constant expression definition @modelExpressionEval
const_expr_1467038690816108000 == 
LET 
seqs == (o1 :> <<c2>> @@ o2 :> <<c1>>)
G == DependencyGraph(seqs) IN
/\ PrintT(Correctness(seqs))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1467038690816108000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1467038690826109000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1467038690836110000 ==
Correctness(replicaState)
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1467038690846111000 ==
TypeInvariant
----
=============================================================================
\* Modification History
\* Created Mon Jun 27 10:44:50 EDT 2016 by nano
