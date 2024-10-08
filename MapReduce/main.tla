-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Sequences, Integers
PT == INSTANCE PT
CONSTANTS Workers, Reducer, NULL

PossibleInputs == PT!TupleOf(0..2, 4)
SumSeq(seq) == PT!ReduceSeq(LAMBDA x, y: x + y, seq, 0)

(*--algorithm mapreduce

variables 
    input \in PossibleInputs,
    result = [w \in Workers |-> NULL],
    queue = [w \in Workers |-> <<>>];
\*    queue = [w \in Workers |-> <<1, 2>>];

process reducer = Reducer
variables
    final = 0,
    consumed = [w \in Workers |-> FALSE];
begin
    Schedule:
        with worker_order = PT!OrderSet(Workers) do
            queue := [ w \in Workers |-> 
                LET offset == PT!Index(worker_order, w) - 1
                IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
            ];
        end with;

    ReduceResult:
        while \E w \in Workers: ~consumed[w] do
            with w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL} do
                final := final + result[w];
                consumed[w] := TRUE;
            end with;
        end while;
    Finish:
        assert final = SumSeq(input);
end process;

process worker \in Workers
variables total = 0;
begin
    WaitForQueue:
        await queue[self] /= <<>>;
    Process:
        while queue[self] /= <<>> do
            total := total + Head(queue[self]);
            queue[self] := Tail(queue[self]);
        end while;
    Worker:
        result[self] := total;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "7651e4df" /\ chksum(tla) = "bfcda556")
VARIABLES input, result, queue, pc, final, consumed, total

vars == << input, result, queue, pc, final, consumed, total >>

ProcSet == {Reducer} \cup (Workers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ result = [w \in Workers |-> NULL]
        /\ queue = [w \in Workers |-> <<>>]
        (* Process reducer *)
        /\ final = 0
        /\ consumed = [w \in Workers |-> FALSE]
        (* Process worker *)
        /\ total = [self \in Workers |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = Reducer -> "Schedule"
                                        [] self \in Workers -> "WaitForQueue"]

Schedule == /\ pc[Reducer] = "Schedule"
            /\ LET worker_order == PT!OrderSet(Workers) IN
                 queue' =          [ w \in Workers |->
                              LET offset == PT!Index(worker_order, w) - 1
                              IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = offset)
                          ]
            /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
            /\ UNCHANGED << input, result, final, consumed, total >>

ReduceResult == /\ pc[Reducer] = "ReduceResult"
                /\ IF \E w \in Workers: ~consumed[w]
                      THEN /\ \E w \in {w \in Workers: ~consumed[w] /\ result[w] /= NULL}:
                                /\ final' = final + result[w]
                                /\ consumed' = [consumed EXCEPT ![w] = TRUE]
                           /\ pc' = [pc EXCEPT ![Reducer] = "ReduceResult"]
                      ELSE /\ pc' = [pc EXCEPT ![Reducer] = "Finish"]
                           /\ UNCHANGED << final, consumed >>
                /\ UNCHANGED << input, result, queue, total >>

Finish == /\ pc[Reducer] = "Finish"
          /\ Assert(final = SumSeq(input), 
                    "Failure of assertion at line 39, column 9.")
          /\ pc' = [pc EXCEPT ![Reducer] = "Done"]
          /\ UNCHANGED << input, result, queue, final, consumed, total >>

reducer == Schedule \/ ReduceResult \/ Finish

WaitForQueue(self) == /\ pc[self] = "WaitForQueue"
                      /\ queue[self] /= <<>>
                      /\ pc' = [pc EXCEPT ![self] = "Process"]
                      /\ UNCHANGED << input, result, queue, final, consumed, 
                                      total >>

Process(self) == /\ pc[self] = "Process"
                 /\ IF queue[self] /= <<>>
                       THEN /\ total' = [total EXCEPT ![self] = total[self] + Head(queue[self])]
                            /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                            /\ pc' = [pc EXCEPT ![self] = "Process"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Worker"]
                            /\ UNCHANGED << queue, total >>
                 /\ UNCHANGED << input, result, final, consumed >>

Worker(self) == /\ pc[self] = "Worker"
                /\ result' = [result EXCEPT ![self] = total[self]]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << input, queue, final, consumed, total >>

worker(self) == WaitForQueue(self) \/ Process(self) \/ Worker(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reducer
           \/ (\E self \in Workers: worker(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Jun 09 23:16:38 JST 2024 by 81902
\* Created Sun Jun 09 22:22:55 JST 2024 by 81902
