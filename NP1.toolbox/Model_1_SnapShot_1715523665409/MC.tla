---- MODULE MC ----
EXTENDS NP1, TLC

\* Constant expression definition @modelExpressionEval
const_expr_171552366334055000 == 
BestKnapsacks(HardcodedItemSet)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_171552366334055000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_171552366334056000 ==
FALSE/\pc = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_171552366334057000 ==
FALSE/\pc' = pc
----
=============================================================================
\* Modification History
\* Created Sun May 12 23:21:03 JST 2024 by 81902
