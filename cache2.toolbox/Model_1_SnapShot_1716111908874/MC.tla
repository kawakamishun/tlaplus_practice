---- MODULE MC ----
EXTENDS cache2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT definitions Actors
const_1716111906834182000 == 
{a1, a2}
----

\* CONSTANT definitions @modelParameterConstants:1ResourceCap
const_1716111906834183000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:2MaxConsumerReq
const_1716111906834184000 == 
2
----

=============================================================================
\* Modification History
\* Created Sun May 19 18:45:06 JST 2024 by 81902
