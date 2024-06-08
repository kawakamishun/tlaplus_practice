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
const_171785597392550000 == 
{b1}
----

\* MV CONSTANT definitions People
const_171785597392651000 == 
{p1, p2}
----

\* CONSTANT definitions @modelParameterConstants:1NumCopies
const_171785597392652000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Sat Jun 08 23:12:53 JST 2024 by 81902
