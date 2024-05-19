---- MODULE MC ----
EXTENDS NP1, TLC

\* Constant expression definition @modelExpressionEval
const_expr_17159257169312000 == 
{BestKnapsacks(itemset) : itemset \in ItemSets}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_17159257169312000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_17159257169313000 ==
FALSE/\pc = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_17159257169324000 ==
FALSE/\pc' = pc
----
=============================================================================
\* Modification History
\* Created Fri May 17 15:01:56 JST 2024 by 81902
