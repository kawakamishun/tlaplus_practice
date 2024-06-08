--------------------------- MODULE LinkedListTest ---------------------------
EXTENDS TLC, Integers, FiniteSets, Sequences

CONSTANTS Nodes, NULL
INSTANCE LinkedLists WITH NULL <- NULL
AllLinkedLists == LinkedLists(Nodes) 

CycleImpliesTwoParents(ll) ==
    Cyclic(ll) <=>
        \E n \in DOMAIN ll:
            Cardinality({p \in DOMAIN ll: ll[p] = n}) = 2

CycleImpliesRingOrTwoParents(ll) ==
    Cyclic(ll) <=>
        \/ Ring(ll)
        \/ \E n \in DOMAIN ll:
            Cardinality({p \in DOMAIN ll: ll[p] = n}) = 2

Valid ==
    /\ \A ll \in AllLinkedLists:
        /\ Assert(CycleImpliesRingOrTwoParents(ll), <<"Counterexamples:", ll>>)

=============================================================================
\* Modification History
\* Last modified Sun May 26 18:37:18 JST 2024 by 81902
\* Created Sun May 26 17:45:26 JST 2024 by 81902
