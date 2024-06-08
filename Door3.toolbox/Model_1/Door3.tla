------------------------------- MODULE Door3 -------------------------------
(*---algorithm Door3

variables
    open = FALSE,
    locked = FALSE,
    key \in BOOLEAN;

process open_door = "open"
begin
    OpenDoor:
        await open;
        either \* lock/unlock
            locked := ~locked;
        or  \* close
            await ~locked;
            open := FALSE;
        end either;
    goto OpenDoor;
end process;

process closed_door = "closed"
begin
    CloseDoor:
        await ~open;
        either \* lock/unlock
            await key;
            locked := ~locked;
        or  \* open
            await ~locked;
            open := TRUE;
        end either;
    goto CloseDoor;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "d2e74d61" /\ chksum(tla) = "3d16879f")
VARIABLES open, locked, key, pc

vars == << open, locked, key, pc >>

ProcSet == {"open"} \cup {"closed"}

Init == (* Global variables *)
        /\ open = FALSE
        /\ locked = FALSE
        /\ key \in BOOLEAN
        /\ pc = [self \in ProcSet |-> CASE self = "open" -> "OpenDoor"
                                        [] self = "closed" -> "CloseDoor"]

OpenDoor == /\ pc["open"] = "OpenDoor"
            /\ open
            /\ \/ /\ locked' = ~locked
                  /\ open' = open
               \/ /\ ~locked
                  /\ open' = FALSE
                  /\ UNCHANGED locked
            /\ pc' = [pc EXCEPT !["open"] = "OpenDoor"]
            /\ key' = key

open_door == OpenDoor

CloseDoor == /\ pc["closed"] = "CloseDoor"
             /\ ~open
             /\ \/ /\ key
                   /\ locked' = ~locked
                   /\ open' = open
                \/ /\ ~locked
                   /\ open' = TRUE
                   /\ UNCHANGED locked
             /\ pc' = [pc EXCEPT !["closed"] = "CloseDoor"]
             /\ key' = key

closed_door == CloseDoor

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == open_door \/ closed_door
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun May 26 20:45:27 JST 2024 by 81902
\* Created Sun May 26 20:41:33 JST 2024 by 81902
