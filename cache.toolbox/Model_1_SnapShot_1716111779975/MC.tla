---- MODULE MC ----
EXTENDS cache, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_1716111777939174000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_1716111777940175000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_1716111777940176000 == 
2
----

=============================================================================
\* Modification History
\* Created Sun May 19 18:42:57 JST 2024 by 81902