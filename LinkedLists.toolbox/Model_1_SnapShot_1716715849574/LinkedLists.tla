----------------------------- MODULE LinkedLists -----------------------------
CONSTANT NULL
LOCAL INSTANCE TLC \* for Assert
LOCAL INSTANCE FiniteSets \* for Cardinality
LOCAL INSTANCE Sequences \* for Len
LOCAL INSTANCE Integers \* for a..b

\* NULL is termination.
LOCAL PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]

\* Range is defined in PT, but I don't want a general-purpose module to depend on PT, so I define it here.
LOCAL Range(f) == {f[x]: x \in DOMAIN f}

LOCAL isLinkedList(PointerMap) ==
    LET
        nodes == DOMAIN PointerMap
        all_seqs == [1..Cardinality(nodes) -> nodes] 
    IN \E ordering \in all_seqs:
        \* Each node points to the next node in ordering
        /\ \A i \in 1..Len(ordering)-1:
            PointerMap[ordering[i]] = ordering[i+1]
        \* All nodes in the mapping appear in ordering
        /\ nodes \subseteq Range(ordering)
\*        /\ \A n \in nodes:
\*            \E i \in 1..Len(ordering):
\*                ordering[i] = n

LinkedLists(Nodes) == 
    IF NULL \in Nodes THEN
        Assert(FALSE, "NULL cannot be in Nodes")
    ELSE
        LET
            node_subsets == (SUBSET Nodes \ {{}})
            pointer_maps_sets == {PointerMaps(subn): subn \in node_subsets}
            \* Since pointer_maps_sets is a set of functions, it is necessary to find the union of them.
            all_pointer_maps == UNION pointer_maps_sets
        IN {pm \in all_pointer_maps : isLinkedList(pm)}

Cyclic(LL) == NULL \notin Range(LL)
Ring(LL) == (DOMAIN LL = Range(LL))

First(LL) ==
    IF Ring(LL)
    THEN CHOOSE node \in DOMAIN LL:
        TRUE
    ELSE CHOOSE node \in DOMAIN LL:
        node \notin Range(LL) 


\* Ring..
\* >> CHOOSE ll \in LinkedLists({"a", "b"}): {"a", "b"} \subseteq Range(ll)
\* [a |-> "b", b |-> "a"]

\* self reference
\* >> CHOOSE ll \in LinkedLists({"a", "b"}): Cyclic(ll) /\ ~Ring(ll)
\* [a |-> "a", b |-> "a"]



=============================================================================
\* Modification History
\* Last modified Sun May 26 18:28:57 JST 2024 by 81902
\* Created Sun May 26 17:46:20 JST 2024 by 81902
