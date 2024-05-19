----------------------------- MODULE recycler2 -----------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets

(*--algorithm recicler
variables
    capacity \in [trash: 1..10, recycle: 1..10],
    bins = [trash |-> <<>>, recycle |-> <<>>],
    count = [trash |-> 0, recycle |-> 0],
    item = [type: {"trash", "recycle"}, size: 1..6],
    items \in SetOfFour(Items),
\*    items \in item \X item \X item \X item,
    curr = ""; \* helper variable, means current item

define
    \* TLA+ `Operator` definitions
    BinTypes == {"trash", "recycle"}
    SetOfFour(set) == set \X set \X set \X set
    Items == [type: BinTypes, size: 1..6]

    NoBinOverflow == capacity.trash >= 0 /\ capacity.recycle >= 0
    CountsMatchUp == Len(bins.trash) = count.trash /\ Len(bins.recycle) = count.recycle

    \* Or define them all together as one Invariant.
    Invariant == 
        /\ capacity.trash >= 0 
        /\ capacity.recycle >= 0
        /\ CountsMatchUp == Len(bins.trash) = count.trash 
        /\ Len(bins.recycle) = count.recycle

end define;

macro add_item(type) begin
    bins[type] := Append(bins[type], curr);
    capacity[type] := capacity[type] - curr.size;
    count[type] := count[type] + 1;
end macro;

begin
    while items /= <<>> do
        curr := Head(items);
        items := Tail(items);
        if curr.type = "recycle"
            /\ curr.size < capacity.recycle then
            add_item("recycle");
        elsif curr.size < capacity.trash then
            add_item("trash");
        end if;
    end while;

    \* Rewrit Invariants using operators.
    assert NoBinOverflow /\ CountsMatchUp;    
\*    assert capacity.trash >= 0 /\ capacity.recycle >= 0;
\*    assert Len(bins.trash) = count.trash;
\*    assert Len(bins.recycle) = count.recycle;
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "de47812a" /\ chksum(tla) = "fa35863")
VARIABLES capacity, bins, count, item, items, curr, pc

(* define statement *)
BinTypes == {"trash", "recycle"}
SetOfFour(set) == set \X set \X set \X set
Items == [type: BinTypes, size: 1..6]
NoBinOverflow == capacity.trash >= 0 /\ capacity.recycle >= 0
CountsMatchUp == Len(bins.trash) = count.trash /\ Len(bins.recycle) = count.recycle


vars == << capacity, bins, count, item, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity \in [trash: 1..10, recycle: 1..10]
        /\ bins = [trash |-> <<>>, recycle |-> <<>>]
        /\ count = [trash |-> 0, recycle |-> 0]
        /\ item = [type: {"trash", "recycle"}, size: 1..6]
        /\ items \in SetOfFour(Items)
        /\ curr = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycle"
                           /\ curr'.size < capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = Append(bins["recycle"], curr')]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - curr'.size]
                               /\ count' = [count EXCEPT !["recycle"] = count["recycle"] + 1]
                          ELSE /\ IF curr'.size < capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = Append(bins["trash"], curr')]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(NoBinOverflow /\ CountsMatchUp, 
                              "Failure of assertion at line 41, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>
         /\ item' = item

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun May 12 00:04:43 JST 2024 by 81902
\* Created Sat May 11 23:52:09 JST 2024 by 81902
