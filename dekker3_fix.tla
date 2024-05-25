------------------------------ MODULE dekker3_fix ------------------------------
EXTENDS TLC, Integers, Sequences
Threads == 1..2

(*---algorithm dekker3_fix

variables 
    flag = [t \in Threads |-> FALSE],
    timeout = [t \in Threads |-> 3]
    next_thread \in Threads;

define
    AtMostOneCritical ==
        \A t1, t2 \in Threads:
            t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")
    Liveness ==
        \A t \in {1}: <>(pc[t] = "CS")
end define;

procedure thread()
begin
    P1: flag[self] := TRUE;
    \* All threads other than self are FALSE
    P2:
        while \E t \in Threads \ {self}: flag[t] do
            P2_1:
                if next_thread /= self then
                    P2_1_1: 
                        flag[self] := FALSE;
                        timeout := 3;
                    P2_1_2: 
                        while timeout = 0 do
                            P2_1_2_1: timeout := timeout - 1;                        
                        end while;
                    P2_1_3: next_thread := self;
                    P2_1_4: flag[self] := TRUE;
                end if;
            P2_2: flag[self] := TRUE;
        end while;
    \* Critical Section
    CS: 
        skip;
    P3: next_thread := 3 - self;
    P4: flag[self] := FALSE;
    P5: goto P1;
end procedure;

fair process fair_thread \in {1}
begin
    Fair:
        call thread();
end process;

\* Since crashable_thread is a normal process, it is not evaluated, 
\* i.e. crashable_thread simulates the behavior of not moving forward.
process crashable_thread \in {2}
begin
    Crashable:
        call thread();
end process;

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "a63109b4" /\ chksum(tla) = "f74a1b8b")
VARIABLES flag, Sem, next_thread, pc, stack

(* define statement *)
AtMostOneCritical ==
    \A t1, t2 \in Threads:
        t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")
Liveness ==
    \A t \in {1}: <>(pc[t] = "CS")


vars == << flag, Sem, next_thread, pc, stack >>

ProcSet == ({1}) \cup ({2})

Init == (* Global variables *)
        /\ flag = [t \in Threads |-> FALSE]
        /\ Sem = 2
        /\ next_thread \in Threads
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {1} -> "Fair"
                                        [] self \in {2} -> "Crashable"]

P1(self) == /\ pc[self] = "P1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << Sem, next_thread, stack >>

P2(self) == /\ pc[self] = "P2"
            /\ IF next_thread /= self
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << flag, Sem, next_thread, stack >>

P2_1(self) == /\ pc[self] = "P2_1"
              /\ (Sem - self) >= 0
              /\ pc' = [pc EXCEPT ![self] = "P2_2"]
              /\ UNCHANGED << flag, Sem, next_thread, stack >>

P2_2(self) == /\ pc[self] = "P2_2"
              /\ Sem' = Sem - self
              /\ pc' = [pc EXCEPT ![self] = "P2"]
              /\ UNCHANGED << flag, next_thread, stack >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ Sem' = Sem + self
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ UNCHANGED << flag, next_thread, stack >>

P3(self) == /\ pc[self] = "P3"
            /\ next_thread' = 3 - self
            /\ pc' = [pc EXCEPT ![self] = "P4"]
            /\ UNCHANGED << flag, Sem, stack >>

P4(self) == /\ pc[self] = "P4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ UNCHANGED << Sem, next_thread, stack >>

P5(self) == /\ pc[self] = "P5"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ UNCHANGED << flag, Sem, next_thread, stack >>

thread(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_2(self)
                   \/ CS(self) \/ P3(self) \/ P4(self) \/ P5(self)

Fair(self) == /\ pc[self] = "Fair"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "thread",
                                                       pc        |->  "Done" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "P1"]
              /\ UNCHANGED << flag, Sem, next_thread >>

fair_thread(self) == Fair(self)

Crashable(self) == /\ pc[self] = "Crashable"
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "thread",
                                                            pc        |->  "Done" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "P1"]
                   /\ UNCHANGED << flag, Sem, next_thread >>

crashable_thread(self) == Crashable(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: thread(self))
           \/ (\E self \in {1}: fair_thread(self))
           \/ (\E self \in {2}: crashable_thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1} : WF_vars(fair_thread(self)) /\ WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun May 26 00:33:23 JST 2024 by 81902
\* Created Sat May 25 22:32:57 JST 2024 by 81902
