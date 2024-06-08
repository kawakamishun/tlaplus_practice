------------------------------ MODULE dekker_fix ------------------------------
EXTENDS Integers
CONSTANT Threads

(*---algorithm dekker_fix

variables 
    flag = [t \in Threads |-> FALSE],
    done = [t \in Threads |-> FALSE], \* added
    next_thread \in Threads;

define
    AtMostOneCritical ==
        \A t1, t2 \in Threads:
            t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")
    Liveness ==
        \A t \in Threads: <>(pc[t] = "CS")
end define;

fair process thread \in Threads
begin
    P1: 
        flag[self] := TRUE;
    \* All threads other than self are FALSE
    P2:
        while \E t \in Threads \ {self}: flag[t] 
            \/ next_thread /= self do           \* added
            P2_1:
                if next_thread /= self then
                    P2_1_1: flag[self] := FALSE;
                    P2_1_2: await next_thread = self;
                    P2_1_3: flag[self] := TRUE;
                end if;
            P2_2: flag[self] := TRUE;
        end while;
    \* Critical Section
    CS: 
        skip;
        done[self] := TRUE;
    P3:
        \* added
        if \A t \in Threads: done[t] then
            done := [t \in Threads |-> FALSE]
        end if;
        with t \in {t \in Threads: ~done[t]} do
            next_thread := t;
        end with;
    P4: flag[self] := FALSE;
    P5: goto P1;
end process;

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "d1969848" /\ chksum(tla) = "16f63014")
VARIABLES flag, done, next_thread, pc

(* define statement *)
AtMostOneCritical ==
    \A t1, t2 \in Threads:
        t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")
Liveness ==
    \A t \in Threads: <>(pc[t] = "CS")


vars == << flag, done, next_thread, pc >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ flag = [t \in Threads |-> FALSE]
        /\ done = [t \in Threads |-> FALSE]
        /\ next_thread \in Threads
        /\ pc = [self \in ProcSet |-> "P1"]

P1(self) == /\ pc[self] = "P1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << done, next_thread >>

P2(self) == /\ pc[self] = "P2"
            /\ IF   \E t \in Threads \ {self}: flag[t]
                  \/ next_thread /= self
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << flag, done, next_thread >>

P2_1(self) == /\ pc[self] = "P2_1"
              /\ IF next_thread /= self
                    THEN /\ pc' = [pc EXCEPT ![self] = "P2_1_1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "P2_2"]
              /\ UNCHANGED << flag, done, next_thread >>

P2_1_1(self) == /\ pc[self] = "P2_1_1"
                /\ flag' = [flag EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "P2_1_2"]
                /\ UNCHANGED << done, next_thread >>

P2_1_2(self) == /\ pc[self] = "P2_1_2"
                /\ next_thread = self
                /\ pc' = [pc EXCEPT ![self] = "P2_1_3"]
                /\ UNCHANGED << flag, done, next_thread >>

P2_1_3(self) == /\ pc[self] = "P2_1_3"
                /\ flag' = [flag EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "P2_2"]
                /\ UNCHANGED << done, next_thread >>

P2_2(self) == /\ pc[self] = "P2_2"
              /\ flag' = [flag EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "P2"]
              /\ UNCHANGED << done, next_thread >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ done' = [done EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ UNCHANGED << flag, next_thread >>

P3(self) == /\ pc[self] = "P3"
            /\ IF \A t \in Threads: done[t]
                  THEN /\ done' = [t \in Threads |-> FALSE]
                  ELSE /\ TRUE
                       /\ done' = done
            /\ \E t \in {t \in Threads: ~done'[t]}:
                 next_thread' = t
            /\ pc' = [pc EXCEPT ![self] = "P4"]
            /\ flag' = flag

P4(self) == /\ pc[self] = "P4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ UNCHANGED << done, next_thread >>

P5(self) == /\ pc[self] = "P5"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ UNCHANGED << flag, done, next_thread >>

thread(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_1_1(self)
                   \/ P2_1_2(self) \/ P2_1_3(self) \/ P2_2(self)
                   \/ CS(self) \/ P3(self) \/ P4(self) \/ P5(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun May 26 00:34:37 JST 2024 by 81902
\* Created Sat May 25 22:05:45 JST 2024 by 81902
