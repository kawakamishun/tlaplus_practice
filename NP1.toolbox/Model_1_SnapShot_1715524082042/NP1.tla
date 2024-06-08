-------------------------------- MODULE NP1 --------------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets
PT == INSTANCE PT

\* knapsack problem
\*
\* There is a knapsack with a capacity of N and a set of items.
\* Each item has a value and size. 
\* A knapsack may contain any number of these items, but their combined size must not exceed the knapsack's capacity.
\* How to maximize the value of your knapsack ?

Capacity == 7
Items == {"a", "b", "c"}

\*HardcodedItemSet == {
\*    [item |-> "a", size |-> 1, value |-> 1],
\*    [item |-> "b", size |-> 2, value |-> 3],
\*    [item |-> "c", size |-> 3, value |-> 1]
\*}
\*ValueOf(item) == (CHOOSE struct \in HardcodedItemSet: struct.item = item).value

HardcodedItemSet == [
    a |-> [size |-> 1, value |-> 1],
    b |-> [size |-> 2, value |-> 3],
    c |-> [size |-> 3, value |-> 1]
]
ValueOf(item) == HardcodedItemSet[item].value

ItemParams == [size: 2..4, value: 0..5]
\*ItemSets == [a: ItemParams, b: ItemParams, c: ItemParams]
ItemSets == [Items -> ItemParams]

KnapsackSize(sack, itemset) == 
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) == 
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

KnapsackValue(sack, itemset) == 
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

\* first version
\*BestKnapsack(itemset) ==
\*    LET all == ValidKnapsacks(itemset)
\*    IN CHOOSE best \in all:
\*        \A worse \in all \ {best}: KnapsackValue(best, itemset) > KnapsackValue(worse, itemset)

\* TEST
\* >>> BestKnapsack(HardcodedItemSet)
\* [a |-> 1, b |-> 3, c|-> 0]
\* >>> KnapsackValue([a |-> 1, b |-> 3, c|-> 0], HardcodedItemSet)
\* 10

\* >>> {BestKnapsack(itemset) : itemset \in ItemSets}
\* Attempted to compute the value of an expression of form
\* CHOOSE x \in S: P, but no element of S satisfied P.

\*--------------------------------------------------

\* Pluscal debug
\* TLC threw an unexpected exception.
\* This was probably caused by an error in the spec or model.
\* See the User Output or TLC Console for clues to what happened.
\* The exception was a java.lang.RuntimeException
\* : Attempted to compute the value of an expression of form
\* CHOOSE x \in S: P, but no element of S satisfied P.
\*
\* [ a |-> [size |-> 2, value |-> 0], b |-> [size |-> 2, value |-> 0], c |-> [size |-> 2, value |-> 0] ]
\* value of all items are 0...

BestKnapsacksOne(itemset) ==
    LET all == ValidKnapsacks(itemset)
    IN CHOOSE all_the_best \in SUBSET all:
\*        \A good \in all_the_best:
        \E good \in all_the_best:
            /\ \A other \in all_the_best:
                KnapsackValue(good, itemset) = KnapsackValue(other, itemset)
            /\ \A worse \in all \ all_the_best:
                KnapsackValue(good, itemset) > KnapsackValue(worse, itemset)

BestKnapsacksTwo(itemset) ==
    LET 
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}: KnapsackValue(best, itemset) >= KnapsackValue(worse, itemset)
        value_of_best == KnapsackValue(best, itemset)
    IN
        {k \in all: value_of_best = KnapsackValue(k, itemset)}

\* TEST
\* >>> \A is \in ItemSets: BestKnapsacksTwo(is) = BestKnapsacksOne(is)
\* FALSE
\* WHY !?
\* >>> LET is == CHOOSE is \in ItemSets:
\* >>>     BestKnapsacksTwo(is) /= BestKnapsacksOne(is)
\* >>> IN <<is, BestKnapsacksOne(is), BestKnapsacksTwo(is)>>
\*  << [ a |-> [size |-> 2, value |-> 0],
\*        b |-> [size |-> 2, value |-> 0],
\*        c |-> [size |-> 2, value |-> 0] ],
\*      {},
\*      { [a |-> 0, b |-> 0, c |-> 0],
\*        [a |-> 0, b |-> 0, c |-> 1],
\*        [a |-> 0, b |-> 0, c |-> 2],
\*        [a |-> 0, b |-> 0, c |-> 3],
\*        [a |-> 0, b |-> 1, c |-> 0],
\*        [a |-> 0, b |-> 1, c |-> 1],
\*        [a |-> 0, b |-> 1, c |-> 2],
\*        [a |-> 0, b |-> 2, c |-> 0],
\*        [a |-> 0, b |-> 2, c |-> 1],
\*        [a |-> 0, b |-> 3, c |-> 0],
\*        [a |-> 1, b |-> 0, c |-> 0],
\*        [a |-> 1, b |-> 0, c |-> 1],
\*        [a |-> 1, b |-> 0, c |-> 2],
\*        [a |-> 1, b |-> 1, c |-> 0],
\*        [a |-> 1, b |-> 1, c |-> 1],
\*        [a |-> 1, b |-> 2, c |-> 0],
\*        [a |-> 2, b |-> 0, c |-> 0],
\*        [a |-> 2, b |-> 0, c |-> 1],
\*        [a |-> 2, b |-> 1, c |-> 0],
\*        [a |-> 3, b |-> 0, c |-> 0] } >>
\* WHY is BestKnapsacksOne(is) phi set?

\*--------------------------------------------------

\* FIX 
\*     IN CHOOSE all_the_best \in SUBSET all: \A good \in all_the_best:
\*     IN CHOOSE all_the_best \in SUBSET all: \E good \in all_the_best:
\* >>>
\* >>> LET is == CHOOSE is \in ItemSets:
\* >>>     BestKnapsacksTwo(is) /= BestKnapsacksOne(is)
\* >>> IN <<is, BestKnapsacksOne(is), BestKnapsacksTwo(is)>>
\* NO RESULT

\*--------------------------------------------------

\* last version
BestKnapsacks(itemset) ==
    LET
        value(sack) ==KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                value(best) >= value(worse)
    IN
        {k \in all: value(best) = value(k)}

\* >>>BestKnapsacks(HardcodedItemSet)
\* {[a |-> 1, b |-> 3, c |-> 0]}

\*--------------------------------------------------


(*--algorithm NP1
variables
    itemset \in ItemSets;

begin
    skip;
    assert BestKnapsacks(itemset) \in ValidKnapsacks(itemset);
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "5e8cc485" /\ chksum(tla) = "d4175233")
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ Assert(BestKnapsacks(itemset) \in ValidKnapsacks(itemset), 
                   "Failure of assertion at line 161, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED itemset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun May 12 23:27:31 JST 2024 by 81902
\* Created Sun May 12 20:37:32 JST 2024 by 81902
