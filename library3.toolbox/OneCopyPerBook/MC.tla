---- MODULE MC ----
EXTENDS library3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT definitions Books
const_1717340848980211000 == 
{b1}
----

\* MV CONSTANT definitions People
const_1717340848980212000 == 
{p1, p2}
----

\* CONSTANT definitions @modelParameterConstants:1NumCopies
const_1717340848980213000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Mon Jun 03 00:07:28 JST 2024 by 81902
