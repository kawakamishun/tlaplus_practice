---- MODULE MC ----
EXTENDS LinkedListTest, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Nodes
const_171671624362417000 == 
{a, b, c}
----

\* Constant expression definition @modelExpressionEval
const_expr_171671624362418000 == 
Valid
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_171671624362418000>>)
----

=============================================================================
\* Modification History
\* Created Sun May 26 18:37:23 JST 2024 by 81902
