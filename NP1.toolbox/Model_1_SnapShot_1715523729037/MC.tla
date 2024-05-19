---- MODULE MC ----
EXTENDS NP1, TLC

\* Constant expression definition @modelExpressionEval
const_expr_171552372698558000 == 
KnapsackValue([a |-> 1, b |-> 3, c|-> 0], HardcodedItemSet)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_171552372698558000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_171552372698559000 ==
FALSE/\pc = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_171552372698560000 ==
FALSE/\pc' = pc
----
=============================================================================
\* Modification History
\* Created Sun May 12 23:22:06 JST 2024 by 81902
