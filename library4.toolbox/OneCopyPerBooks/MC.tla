---- MODULE MC ----
EXTENDS library4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT definitions Books
const_171785649683577000 == 
{b1}
----

\* MV CONSTANT definitions People
const_171785649683578000 == 
{p1, p2}
----

\* CONSTANT definitions @modelParameterConstants:1NumCopies
const_171785649683579000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Sat Jun 08 23:21:36 JST 2024 by 81902
