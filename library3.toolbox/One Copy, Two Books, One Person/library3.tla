------------------------------ MODULE library3 ------------------------------
EXTENDS TLC, Integers, Sequences
CONSTANTS Books, People, NumCopies
ASSUME NumCopies \subseteq Nat
PT == INSTANCE PT

set ++ x == set \union {x}
set -- x == set \ {x}

(*--algorithm library3
variables
    library \in [Books -> NumCopies],
    \* reserve, no priority
    reserves = [b \in Books |-> <<>>];
    \* reserves = [b \in Books |-> {}];

define
    AvailableBooks == {b \in Books: library[b] > 0}

    BorrowableBooks(p) == {b \in AvailableBooks: reserves[b] = <<>> \/ p = Head(reserves[b])}
    \* BorrowableBooks(p) == {b \in AvailableBooks: reserves[b] = {} \/ p \in reserves[b]}
end define;
    
fair process person \in People
variables
    \* person can borrow only one book at a time.
    books = {},
    wants \in SUBSET Books;
begin
    Person:
        either
            \* Checkout
            with b \in BorrowableBooks(self) \ books do
                library[b] := library[b] - 1;
                books := books ++ b;
                wants := wants -- b;

                if reserves[b] /= <<>> /\ self = Head(reserves[b]) then
                    reserves[b] := Tail(reserves[b]);
                end if;

            end with;
        or
            \* Return
            with b \in books do
                library[b] := library[b] + 1;
                books := books -- b;
            end with;
        or
            \* Reserve
            with b \in {b \in Books: self \notin PT!Range(reserves[b])} do
                reserves[b] := Append(reserves[b], self);
            end with;
\*            with b \in Books do
\*                 reserves[b] := reserves[b] ++ self;
\*            end with;
        end either;
    goto Person;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6eb7e3bb" /\ chksum(tla) = "fce4a300")
VARIABLES library, reserves, pc

(* define statement *)
AvailableBooks == {b \in Books: library[b] > 0}

BorrowableBooks(p) == {b \in AvailableBooks: reserves[b] = <<>> \/ p = Head(reserves[b])}

VARIABLES books, wants

vars == << library, reserves, pc, books, wants >>

ProcSet == (People)

Init == (* Global variables *)
        /\ library \in [Books -> NumCopies]
        /\ reserves = [b \in Books |-> <<>>]
        (* Process person *)
        /\ books = [self \in People |-> {}]
        /\ wants \in [People -> SUBSET Books]
        /\ pc = [self \in ProcSet |-> "Person"]

Person(self) == /\ pc[self] = "Person"
                /\ \/ /\ \E b \in BorrowableBooks(self) \ books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] - 1]
                           /\ books' = [books EXCEPT ![self] = books[self] ++ b]
                           /\ wants' = [wants EXCEPT ![self] = wants[self] -- b]
                           /\ IF reserves[b] /= <<>> /\ self = Head(reserves[b])
                                 THEN /\ reserves' = [reserves EXCEPT ![b] = Tail(reserves[b])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED reserves
                   \/ /\ \E b \in books[self]:
                           /\ library' = [library EXCEPT ![b] = library[b] + 1]
                           /\ books' = [books EXCEPT ![self] = books[self] -- b]
                      /\ UNCHANGED <<reserves, wants>>
                   \/ /\ \E b \in {b \in Books: self \notin PT!Range(reserves[b])}:
                           reserves' = [reserves EXCEPT ![b] = Append(reserves[b], self)]
                      /\ UNCHANGED <<library, books, wants>>
                /\ pc' = [pc EXCEPT ![self] = "Person"]

person(self) == Person(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in People: person(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in People : WF_vars(person(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

NoDuplicateReservations ==
    \A b \in Books:
        \A i, j \in 1..Len(reserves[b]):
            i /= j => reserves[b][i] /= reserves[b][j]

TypeInvariant == 
    /\ library \in [Books -> NumCopies ++ 0]
    /\ books \in [People -> SUBSET Books]
    /\ wants \in [People -> SUBSET Books]

Liveness ==
    /\ <>(\A p \in People: wants[p] = {})

=============================================================================
\* Modification History
\* Last modified Mon Jun 03 00:07:25 JST 2024 by 81902
\* Created Sun Jun 02 23:54:48 JST 2024 by 81902
