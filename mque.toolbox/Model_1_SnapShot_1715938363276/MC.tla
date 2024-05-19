---- MODULE MC ----
EXTENDS mque, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxQueueSize
const_171593836122514000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:1defaultInitValue
const_171593836122515000 == 
1
----

\* INIT definition @modelBehaviorNoSpec:0
init_171593836122516000 ==
FALSE/\val = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_171593836122517000 ==
FALSE/\val' = val
----
=============================================================================
\* Modification History
\* Created Fri May 17 18:32:41 JST 2024 by 81902
