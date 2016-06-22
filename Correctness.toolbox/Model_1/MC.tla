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

\* MV CONSTANT definitions Objects
const_1466628493033521000 == 
{o1, o2}
----

\* MV CONSTANT definitions Commands
const_1466628493043522000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:2AccessedBy(c)
const_1466628493053523000(c) == 
CASE c = c1 -> {o1,o2}
[] c = c2 -> {o1,o2}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1466628493063524000(X) ==
BSeq(X,Cardinality(Commands))
----
\* Constant expression definition @modelExpressionEval
const_expr_1466628493073525000 == 
LET 
seqs == (o1 :> <<c2>> @@ o2 :> <<c1>>)
G == DependencyGraph(seqs) IN
/\ PrintT(Correctness(seqs))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1466628493073525000>>)
----

=============================================================================
\* Modification History
\* Created Wed Jun 22 16:48:13 EDT 2016 by nano
