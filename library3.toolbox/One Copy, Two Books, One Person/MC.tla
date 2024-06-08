---- MODULE MC ----
EXTENDS library3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1, b2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1
----

\* MV CONSTANT definitions Books
const_17178549980148000 == 
{b1, b2}
----

\* MV CONSTANT definitions People
const_17178549980149000 == 
{p1}
----

\* CONSTANT definitions @modelParameterConstants:1NumCopies
const_171785499801410000 == 
1..1
----

=============================================================================
\* Modification History
\* Created Sat Jun 08 22:56:38 JST 2024 by 81902
