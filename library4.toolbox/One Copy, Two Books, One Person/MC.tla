---- MODULE MC ----
EXTENDS library4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1, b2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1
----

\* MV CONSTANT definitions Books
const_171785654046580000 == 
{b1, b2}
----

\* MV CONSTANT definitions People
const_171785654046581000 == 
{p1}
----

\* CONSTANT definitions @modelParameterConstants:1NumCopies
const_171785654046582000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Sat Jun 08 23:22:20 JST 2024 by 81902
