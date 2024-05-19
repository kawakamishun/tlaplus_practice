---- MODULE MC ----
EXTENDS mque, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxQueueSize
const_171593837081818000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:1defaultInitValue
const_171593837081919000 == 
1
----

\* INIT definition @modelBehaviorNoSpec:0
init_171593837081920000 ==
FALSE/\val = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_171593837081921000 ==
FALSE/\val' = val
----
=============================================================================
\* Modification History
\* Created Fri May 17 18:32:50 JST 2024 by 81902
