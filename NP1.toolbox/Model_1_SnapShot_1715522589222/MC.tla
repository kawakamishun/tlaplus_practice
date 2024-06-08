---- MODULE MC ----
EXTENDS NP1, TLC

\* Constant expression definition @modelExpressionEval
const_expr_171552142411649000 == 
LET is == CHOOSE is \in ItemSets:
    BestKnapsacksTwo(is) /= BestKnapsacksOne(is)
IN <<is, BestKnapsacksOne(is), BestKnapsacksTwo(is)>>
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_171552142411649000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_171552142411650000 ==
FALSE/\pc = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_171552142411651000 ==
FALSE/\pc' = pc
----
=============================================================================
\* Modification History
\* Created Sun May 12 22:43:44 JST 2024 by 81902
