---- MODULE MC ----
EXTENDS library2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT definitions Books
const_1717339931388188000 == 
{b1}
----

\* MV CONSTANT definitions People
const_1717339931388189000 == 
{p1, p2}
----

\* CONSTANT definitions @modelParameterConstants:1NumCopies
const_1717339931388190000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Sun Jun 02 23:52:11 JST 2024 by 81902
