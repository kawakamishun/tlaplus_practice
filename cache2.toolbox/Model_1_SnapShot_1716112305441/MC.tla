---- MODULE MC ----
EXTENDS cache2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_1716112303394190000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:1ResourceCap
const_1716112303394191000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:2MaxConsumerReq
const_1716112303394192000 == 
2
----

=============================================================================
\* Modification History
\* Created Sun May 19 18:51:43 JST 2024 by 81902
