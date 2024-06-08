---- MODULE MC ----
EXTENDS LinkedLists, TLC

\* Constant expression definition @modelExpressionEval
const_expr_171671584753810000 == 
CHOOSE ll \in LinkedLists({"a", "b"}): Cyclic(ll) /\ ~Ring(ll)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_171671584753810000>>)
----

=============================================================================
\* Modification History
\* Created Sun May 26 18:30:47 JST 2024 by 81902
