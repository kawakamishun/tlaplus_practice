---- MODULE MC ----
EXTENDS cache2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_1716111283088161000 == 
{a1, a2}
----

\* SYMMETRY definition
symm_1716111283088162000 == 
Permutations(const_1716111283088161000)
----

\* CONSTANT definitions @modelParameterConstants:1ResourceCap
const_1716111283088163000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:2MaxConsumerReq
const_1716111283088164000 == 
2
----

=============================================================================
\* Modification History
\* Created Sun May 19 18:34:43 JST 2024 by 81902
