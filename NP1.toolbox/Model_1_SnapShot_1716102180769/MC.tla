---- MODULE MC ----
EXTENDS NP1, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
i1, i2, i3
----

\* MV CONSTANT definitions Items
const_171610214068814000 == 
{i1, i2, i3}
----

\* SYMMETRY definition
symm_171610214068815000 == 
Permutations(const_171610214068814000)
----

\* CONSTANT definitions @modelParameterConstants:0Capacity
const_171610214068816000 == 
7
----

\* CONSTANT definitions @modelParameterConstants:1ValueRange
const_171610214068817000 == 
0..5
----

\* CONSTANT definitions @modelParameterConstants:2SizeRange
const_171610214068818000 == 
2..4
----

\* Constant expression definition @modelExpressionEval
const_expr_171610214068819000 == 
{BestKnapsacks(itemset) : itemset \in ItemSets}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_171610214068819000>>)
----

=============================================================================
\* Modification History
\* Created Sun May 19 16:02:20 JST 2024 by 81902
