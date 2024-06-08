------------------------------- MODULE cache -------------------------------
EXTENDS TLC, Integers, Sequences
CONSTANTS ResourceCap, MaxConsumerReq, Actors

ASSUME ResourceCap > 0
ASSUME MaxConsumerReq \in 1..ResourceCap
ASSUME Actors /= {}

(*---algorithm cache
variables 
    resource_cap = ResourceCap, \*\in 1..ResourceCap,
    resources_left = ResourceCap,
    ran = [a \in Actors |-> FALSE]; \* context switch.

define
    ResourceInvariant == resources_left >= 0
end define;

\*process actor = "acotor"
process actor \in Actors
variables
    resources_needed \in 1..MaxConsumerReq
begin
\*    with multi process, invariant violation...
    WaitForResorces:
        while TRUE do
            await ~ran[self];
            when resources_left >= resources_needed;
            \* await resources_left >= resources_needed;
            UseResources:
                while resources_needed > 0 do
                    resources_left := resources_left - 1;
                    resources_needed := resources_needed - 1;
                end while;
                \* restore needed                
                with x \in 1..MaxConsumerReq do
                   resources_needed := x; 
                end with;
                ran[self] := TRUE;
        end while;

\*    UserResources:
\*        while TRUE do
\*            await resources_left >= resources_needed;
\*            resources_left := resources_left - resources_needed;
\*        end while;
end process;

process time = "time"
begin
    Tick:
        resources_left := resource_cap;
        ran := [a \in Actors |-> FALSE];
        \* reserved := 0;
        goto Tick;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6b2ea7be" /\ chksum(tla) = "2b5fe54c")
VARIABLES resource_cap, resources_left, ran, pc

(* define statement *)
ResourceInvariant == resources_left >= 0

VARIABLE resources_needed

vars == << resource_cap, resources_left, ran, pc, resources_needed >>

ProcSet == (Actors) \cup {"time"}

Init == (* Global variables *)
        /\ resource_cap = ResourceCap
        /\ resources_left = ResourceCap
        /\ ran = [a \in Actors |-> FALSE]
        (* Process actor *)
        /\ resources_needed \in [Actors -> 1..MaxConsumerReq]
        /\ pc = [self \in ProcSet |-> CASE self \in Actors -> "WaitForResorces"
                                        [] self = "time" -> "Tick"]

WaitForResorces(self) == /\ pc[self] = "WaitForResorces"
                         /\ ~ran[self]
                         /\ resources_left >= resources_needed[self]
                         /\ pc' = [pc EXCEPT ![self] = "UseResources"]
                         /\ UNCHANGED << resource_cap, resources_left, ran, 
                                         resources_needed >>

UseResources(self) == /\ pc[self] = "UseResources"
                      /\ IF resources_needed[self] > 0
                            THEN /\ resources_left' = resources_left - 1
                                 /\ resources_needed' = [resources_needed EXCEPT ![self] = resources_needed[self] - 1]
                                 /\ pc' = [pc EXCEPT ![self] = "UseResources"]
                                 /\ ran' = ran
                            ELSE /\ \E x \in 1..MaxConsumerReq:
                                      resources_needed' = [resources_needed EXCEPT ![self] = x]
                                 /\ ran' = [ran EXCEPT ![self] = TRUE]
                                 /\ pc' = [pc EXCEPT ![self] = "WaitForResorces"]
                                 /\ UNCHANGED resources_left
                      /\ UNCHANGED resource_cap

actor(self) == WaitForResorces(self) \/ UseResources(self)

Tick == /\ pc["time"] = "Tick"
        /\ resources_left' = resource_cap
        /\ ran' = [a \in Actors |-> FALSE]
        /\ pc' = [pc EXCEPT !["time"] = "Tick"]
        /\ UNCHANGED << resource_cap, resources_needed >>

time == Tick

Next == time
           \/ (\E self \in Actors: actor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun May 19 18:42:47 JST 2024 by 81902
\* Created Fri May 17 18:36:44 JST 2024 by 81902
