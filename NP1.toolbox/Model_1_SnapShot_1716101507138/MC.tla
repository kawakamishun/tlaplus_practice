---- MODULE MC ----
EXTENDS NP1, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
i1, i2, i3
----

\* MV CONSTANT definitions Items
const_17161014644428000 == 
{i1, i2, i3}
----

\* SYMMETRY definition
symm_17161014644429000 == 
Permutations(const_17161014644428000)
----

\* CONSTANT definitions @modelParameterConstants:0Capacity
const_171610146444210000 == 
7
----

\* CONSTANT definitions @modelParameterConstants:1ValueRange
const_171610146444211000 == 
0..5
----

\* CONSTANT definitions @modelParameterConstants:2SizeRange
const_171610146444212000 == 
2..4
----

\* Constant expression definition @modelExpressionEval
const_expr_171610146444213000 == 
{BestKnapsacks(itemset) : itemset \in ItemSets}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_171610146444213000>>)
----

=============================================================================
\* Modification History
\* Created Sun May 19 15:51:04 JST 2024 by 81902
