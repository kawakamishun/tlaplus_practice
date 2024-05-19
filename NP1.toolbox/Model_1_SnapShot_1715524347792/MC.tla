---- MODULE MC ----
EXTENDS NP1, TLC

\* Constant expression definition @modelExpressionEval
const_expr_171552431263196000 == 
{BestKnapsacks(itemset) : itemset \in ItemSets}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_171552431263196000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_171552431263197000 ==
FALSE/\pc = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_171552431263198000 ==
FALSE/\pc' = pc
----
=============================================================================
\* Modification History
\* Created Sun May 12 23:31:52 JST 2024 by 81902
