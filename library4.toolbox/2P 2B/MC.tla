---- MODULE MC ----
EXTENDS library4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
b1, b2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT definitions Books
const_1717858873312155000 == 
{b1, b2}
----

\* MV CONSTANT definitions People
const_1717858873312156000 == 
{p1, p2}
----

\* CONSTANT definitions @modelParameterConstants:1NumCopies
const_1717858873312157000 == 
1..1
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1717858873312158000 ==
\A p \in People: Cardinality(wants[p]) <= 1
----
=============================================================================
\* Modification History
\* Created Sun Jun 09 00:01:13 JST 2024 by 81902
