------------------------------- MODULE Door2 -------------------------------
(*---algorithm Door2

variables
    open = FALSE,
    locked = FALSE,
    key \in BOOLEAN;
begin
    Event:
        either  \* unlock
            await locked /\ (~open \/ key);
            locked := FALSE;
        or  \* lock
            await ~locked /\ (~open \/ key);
            locked := TRUE;
        or  \* open
            await ~locked /\ ~open;
            open := TRUE;
        or  \* close
            await open /\ ~locked;
\*            await open;
            open := FALSE;
        end either;
    goto Event;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "6a5e3698" /\ chksum(tla) = "374dd7a5")
VARIABLES open, locked, key, pc

vars == << open, locked, key, pc >>

Init == (* Global variables *)
        /\ open = FALSE
        /\ locked = FALSE
        /\ key \in BOOLEAN
        /\ pc = "Event"

Event == /\ pc = "Event"
         /\ \/ /\ locked /\ (~open \/ key)
               /\ locked' = FALSE
               /\ open' = open
            \/ /\ ~locked /\ (~open \/ key)
               /\ locked' = TRUE
               /\ open' = open
            \/ /\ ~locked /\ ~open
               /\ open' = TRUE
               /\ UNCHANGED locked
            \/ /\ open /\ ~locked
               /\ open' = FALSE
               /\ UNCHANGED locked
         /\ pc' = "Event"
         /\ key' = key

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Event
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun May 26 20:40:32 JST 2024 by 81902
\* Created Sun May 26 20:30:57 JST 2024 by 81902
