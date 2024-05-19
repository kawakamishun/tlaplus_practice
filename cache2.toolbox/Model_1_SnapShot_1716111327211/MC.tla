---- MODULE MC ----
EXTENDS cache2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_1716111325174170000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:1ResourceCap
const_1716111325174171000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:2MaxConsumerReq
const_1716111325174172000 == 
2
----

=============================================================================
\* Modification History
\* Created Sun May 19 18:35:25 JST 2024 by 81902
