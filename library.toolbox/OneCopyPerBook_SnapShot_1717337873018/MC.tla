---- MODULE MC ----
EXTENDS library, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT definitions Books
const_1717337869977166000 == 
{b1}
----

\* MV CONSTANT definitions People
const_1717337869977167000 == 
{p1, p2}
----

\* CONSTANT definitions @modelParameterConstants:0NumCopies
const_1717337869977168000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Sun Jun 02 23:17:49 JST 2024 by 81902
