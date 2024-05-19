----------------------------- MODULE telephone -----------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets

(*--algorithm recicler
variables
    to_send = <<1, 2, 3>>,
    received = <<>>,
    in_transit = {};

begin
    while Len(received) /= 3 do
        \* send
        if to_send /= <<>> then
            in_transit := in_transit \union {Head(to_send)};
            to_send := Tail(to_send);
        end if;
        
        \* receive
        either
            with msg \in in_transit do
                received := Append(received, msg);
                in_transit := in_transit \ {msg};
            end with;
        or
            \* failed to receive...
            skip
        end either;   
    end while;

    assert received = <<1,2,3>>;

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "98eedace" /\ chksum(tla) = "dbb7107c")
VARIABLES to_send, received, in_transit, pc

vars == << to_send, received, in_transit, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) /= 3
               THEN /\ IF to_send /= <<>>
                          THEN /\ in_transit' = (in_transit \union {Head(to_send)})
                               /\ to_send' = Tail(to_send)
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ Assert(received = <<1,2,3>>, 
                              "Failure of assertion at line 30, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = in_transit \ {msg}
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sat May 11 23:34:56 JST 2024 by 81902
\* Created Sat May 11 23:29:15 JST 2024 by 81902
