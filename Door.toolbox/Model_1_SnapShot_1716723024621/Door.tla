-------------------------------- MODULE Door --------------------------------
(*---algorithm Door

variables
    open = FALSE,
    locked = FALSE;

begin
    Event:
        either  \* unlock
            await locked;
            locked := FALSE;
        or  \* ~unlock
            await ~locked;
            locked := TRUE;
        or  \* open
            await ~locked;
            await ~open;
            open := TRUE;
        or  \* close
            await open;
            open := FALSE;
        end either;
    goto Event;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "32ad3c0b" /\ chksum(tla) = "4888dead")
VARIABLES open, locked, pc

vars == << open, locked, pc >>

Init == (* Global variables *)
        /\ open = FALSE
        /\ locked = FALSE
        /\ pc = "Event"

Event == /\ pc = "Event"
         /\ \/ /\ locked
               /\ locked' = FALSE
               /\ open' = open
            \/ /\ ~locked
               /\ locked' = TRUE
               /\ open' = open
            \/ /\ ~locked
               /\ ~open
               /\ open' = TRUE
               /\ UNCHANGED locked
            \/ /\ open
               /\ open' = FALSE
               /\ UNCHANGED locked
         /\ pc' = "Event"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Event
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun May 26 20:30:21 JST 2024 by 81902
\* Created Sun May 26 20:23:59 JST 2024 by 81902
