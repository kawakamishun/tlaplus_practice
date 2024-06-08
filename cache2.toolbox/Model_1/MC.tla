---- MODULE MC ----
EXTENDS cache2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_17165387252532000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:1ResourceCap
const_17165387252533000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:2MaxConsumerReq
const_17165387252534000 == 
2
----

=============================================================================
\* Modification History
\* Created Fri May 24 17:18:45 JST 2024 by 81902
