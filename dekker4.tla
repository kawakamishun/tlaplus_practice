------------------------------ MODULE dekker4 ------------------------------
EXTENDS Naturals
Procs == 1..2

\* (3) copilot generated using TLA+/pluscal, ver 0.02 ==> fix to deadlock

(*--algorithm Decker
variables flag = [i \in Procs |-> FALSE], turn = 1;

define
    AtMostOneCritical ==
        \A p1, p2 \in Procs:
            p1 /= p2 => ~(pc[p1] = "CS" /\ pc[p2] = "CS")
    Liveness ==
        \A p \in Procs: <>(pc[p] = "CS")
end define;

fair process proc \in Procs
variables other = 3 - self;
begin
  P1:
    while TRUE do
      P2: flag[self] := TRUE;
      P3:
          while flag[other] do
            if turn = other then
              P3_1: flag[self] := FALSE;
              P3_2: await turn = self;
              P3_3: flag[self] := TRUE;
            end if;
          end while;
      \* critical section
      CS: skip;
      P5: turn := other;
      P6: flag[self] := FALSE;
    end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "d4e399f5" /\ chksum(tla) = "9ad759f7")
VARIABLES flag, turn, pc

(* define statement *)
AtMostOneCritical ==
    \A p1, p2 \in Procs:
        p1 /= p2 => ~(pc[p1] = "CS" /\ pc[p2] = "CS")
Liveness ==
    \A p \in Procs: <>(pc[p] = "CS")

VARIABLE other

vars == << flag, turn, pc, other >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ flag = [i \in Procs |-> FALSE]
        /\ turn = 1
        (* Process proc *)
        /\ other = [self \in Procs |-> 3 - self]
        /\ pc = [self \in ProcSet |-> "P1"]

P1(self) == /\ pc[self] = "P1"
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << flag, turn, other >>

P2(self) == /\ pc[self] = "P2"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ UNCHANGED << turn, other >>

P3(self) == /\ pc[self] = "P3"
            /\ IF flag[other[self]]
                  THEN /\ IF turn = other[self]
                             THEN /\ pc' = [pc EXCEPT ![self] = "P3_1"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "P3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << flag, turn, other >>

P3_1(self) == /\ pc[self] = "P3_1"
              /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "P3_2"]
              /\ UNCHANGED << turn, other >>

P3_2(self) == /\ pc[self] = "P3_2"
              /\ turn = self
              /\ pc' = [pc EXCEPT ![self] = "P3_3"]
              /\ UNCHANGED << flag, turn, other >>

P3_3(self) == /\ pc[self] = "P3_3"
              /\ flag' = [flag EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "P3"]
              /\ UNCHANGED << turn, other >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ UNCHANGED << flag, turn, other >>

P5(self) == /\ pc[self] = "P5"
            /\ turn' = other[self]
            /\ pc' = [pc EXCEPT ![self] = "P6"]
            /\ UNCHANGED << flag, other >>

P6(self) == /\ pc[self] = "P6"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ UNCHANGED << turn, other >>

proc(self) == P1(self) \/ P2(self) \/ P3(self) \/ P3_1(self) \/ P3_2(self)
                 \/ P3_3(self) \/ CS(self) \/ P5(self) \/ P6(self)

Next == (\E self \in Procs: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

\* END TRANSLATION 

\* (1) copilot only TLA+

\*CONSTANT Procs
\*VARIABLE flag, turn
\*
\*TypeOK == /\ flag \in [Procs -> BOOLEAN]
\*          /\ turn \in Procs
\*
\*Init == /\ flag = [p \in Procs |-> FALSE]
\*        /\ turn \in Procs
\*
\*enter(p) == /\ flag[p] = FALSE
\*            /\ flag' = [flag EXCEPT ![p] = TRUE]
\*            /\ turn' = p
\*            /\ UNCHANGED << turn >>
\*
\*exit(p) == /\ flag' = [flag EXCEPT ![p] = FALSE]
\*           /\ UNCHANGED << turn >>
\*
\*Next == \E p \in Procs: enter(p) \/ exit(p)
\*
\*Spec == Init /\ [][Next]_<<flag, turn>>


\* (2) copilot generated using TLA+/pluscal, ver 0.01 ==> deadlock occurs!!

\*Procs == 1..2
\*
\*(*--algorithm Decker
\*variables flag = [i \in Procs |-> FALSE], turn = 1;
\*
\*define
\*    AtMostOneCritical ==
\*        \A p1, p2 \in Procs:
\*            p1 /= p2 => ~(pc[p1] = "CS" /\ pc[p2] = "CS")
\*    Liveness ==
\*        \A p \in Procs: <>(pc[p] = "CS")
\*end define;
\*
\*fair process proc \in Procs
\*variables other = 3 - self;
\*begin
\*  P1:
\*    while TRUE do
\*      P2: await ~flag[other];
\*      P3: flag[self] := TRUE;
\*      P4:
\*          if turn = other then
\*            flag[self] := FALSE;
\*            await turn = self;
\*          end if;
\*      \* critical section
\*      CS: skip;
\*      P5: turn := other;
\*      P6: flag[self] := FALSE;
\*    end while;
\*end process;
\*end algorithm;*)

=============================================================================
