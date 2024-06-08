---- MODULE MC ----
EXTENDS Database3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2
----

\* MV CONSTANT definitions Clients
const_171673237945071000 == 
{c1, c2}
----

\* MV CONSTANT definitions Data
const_171673237945072000 == 
{d1, d2}
----

=============================================================================
\* Modification History
\* Created Sun May 26 23:06:19 JST 2024 by 81902
