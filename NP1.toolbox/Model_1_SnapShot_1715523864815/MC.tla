---- MODULE MC ----
EXTENDS NP1, TLC

\* Constant expression definition @modelExpressionEval
const_expr_171552382773570000 == 
{BestKnapsacks(itemset) : itemset \in ItemSets}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_171552382773570000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_171552382773571000 ==
FALSE/\pc = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_171552382773572000 ==
FALSE/\pc' = pc
----
=============================================================================
\* Modification History
\* Created Sun May 12 23:23:47 JST 2024 by 81902
