------------------------------ MODULE Database ------------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS Data, NULL, Clients

(*---algorithm Database
variables
    db_value \in Data;

process clients \in Clients
variables result = NULL;
begin
    Client:
        either \* read
            result := db_value;
            assert result = db_value;
        or \* write
            with d \in Data do
                db_value := d;
            end with;
        end either;
    goto Client;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "cd667dc9" /\ chksum(tla) = "b9d2234e")
VARIABLES db_value, pc, result

vars == << db_value, pc, result >>

ProcSet == (Clients)

Init == (* Global variables *)
        /\ db_value \in Data
        (* Process clients *)
        /\ result = [self \in Clients |-> NULL]
        /\ pc = [self \in ProcSet |-> "Client"]

Client(self) == /\ pc[self] = "Client"
                /\ \/ /\ result' = [result EXCEPT ![self] = db_value]
                      /\ Assert(result'[self] = db_value, 
                                "Failure of assertion at line 15, column 13.")
                      /\ UNCHANGED db_value
                   \/ /\ \E d \in Data:
                           db_value' = d
                      /\ UNCHANGED result
                /\ pc' = [pc EXCEPT ![self] = "Client"]

clients(self) == Client(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Clients: clients(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun May 26 21:57:28 JST 2024 by 81902
\* Created Sun May 26 20:22:44 JST 2024 by 81902
