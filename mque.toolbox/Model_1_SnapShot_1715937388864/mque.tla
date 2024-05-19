-------------------------------- MODULE mque --------------------------------
EXTENDS TLC, Integers, Sequences
CONSTANTS MaxQueueSize

(*--algorithm message_queue
variable queue = <<>>;

define
    BoundedQueue == Len(queue) <= MaxQueueSize
end define;


process writer = "writer"
begin Write:
    while TRUE do
        queue := Append(queue, "msg");
    end while;
end process;

process reader = "reader"
variables current_message = "none";
begin Read:
    while TRUE do
        await queue /= <<>>;
        current_message := Head(queue);
        queue := Tail(queue);
    end while;
end process;

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "97f3b76d" /\ chksum(tla) = "1c35dd73")
VARIABLE queue

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLE current_message

vars == << queue, current_message >>

ProcSet == {"writer"} \cup {"reader"}

Init == (* Global variables *)
        /\ queue = <<>>
        (* Process reader *)
        /\ current_message = "none"

writer == /\ queue' = Append(queue, "msg")
          /\ UNCHANGED current_message

reader == /\ queue /= <<>>
          /\ current_message' = Head(queue)
          /\ queue' = Tail(queue)

Next == writer \/ reader

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri May 17 18:15:38 JST 2024 by 81902
\* Created Fri May 17 17:11:15 JST 2024 by 81902