---- MODULE MC ----
EXTENDS Database, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2
----

\* MV CONSTANT definitions Clients
const_171672449821825000 == 
{c1, c2}
----

\* MV CONSTANT definitions Data
const_171672449821826000 == 
{d1, d2}
----

=============================================================================
\* Modification History
\* Created Sun May 26 20:54:58 JST 2024 by 81902
