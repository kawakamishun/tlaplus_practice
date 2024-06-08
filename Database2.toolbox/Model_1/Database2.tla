----------------------------- MODULE Database2 -----------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS Data, NULL, Clients

(*---algorithm Database2
variables
    query = [c \in Clients |-> NULL],
    db_value \in Data;

define
    Exists(val) == val /= NULL
    RequestingClients ==
        {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}
end define;

macro request(data) begin
    \* query[self] := [type |-> "request", data |-> data];
    query[self] := [type |-> "request"] @@ data;
end macro;

macro wait_for_response() begin
    await query[self].type = "response";
end macro;

process database = "Database"
begin
    DB:
        with client \in RequestingClients, q = query[client] do
            if q.request = "write" then
                db_value := q.data;
            elsif q.request = "read" then
                skip;
            else
                assert FALSE;
            end if;
            query[client] := [type |-> "response", result |-> db_value];
            \* db_value := q.data;
            \* query[client] := [type |-> "response"];
        end with;
    goto DB;
end process;

process clients \in Clients
variables result = NULL;
begin
    Request:
        while TRUE do
            either \* read
                request([request |-> "read"]);
                Confirm:
                    wait_for_response();
                    result := query[self].result;
                    \* If we verify using the db_value, the db_value may have already been rewritten by another client at the time of verification...
                    assert result = db_value;                   
                \* result := db_value;
                \* assert result = db_value;
            or \* write
                with d \in Data do
                    request([request |-> "write", data |-> d]);
                    \* request(d);
                end with;
                Wait:
                    wait_for_response();
            end either;
        end while;  
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "f6c60be" /\ chksum(tla) = "49802d96")
VARIABLES query, db_value, pc

(* define statement *)
Exists(val) == val /= NULL
RequestingClients ==
    {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}

VARIABLE result

vars == << query, db_value, pc, result >>

ProcSet == {"Database"} \cup (Clients)

Init == (* Global variables *)
        /\ query = [c \in Clients |-> NULL]
        /\ db_value \in Data
        (* Process clients *)
        /\ result = [self \in Clients |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self = "Database" -> "DB"
                                        [] self \in Clients -> "Request"]

DB == /\ pc["Database"] = "DB"
      /\ \E client \in RequestingClients:
           LET q == query[client] IN
             /\ IF q.request = "write"
                   THEN /\ db_value' = q.data
                   ELSE /\ IF q.request = "read"
                              THEN /\ TRUE
                              ELSE /\ Assert(FALSE, 
                                             "Failure of assertion at line 34, column 17.")
                        /\ UNCHANGED db_value
             /\ query' = [query EXCEPT ![client] = [type |-> "response", result |-> db_value']]
      /\ pc' = [pc EXCEPT !["Database"] = "DB"]
      /\ UNCHANGED result

database == DB

Request(self) == /\ pc[self] = "Request"
                 /\ \/ /\ query' = [query EXCEPT ![self] = [type |-> "request"] @@ ([request |-> "read"])]
                       /\ pc' = [pc EXCEPT ![self] = "Confirm"]
                    \/ /\ \E d \in Data:
                            query' = [query EXCEPT ![self] = [type |-> "request"] @@ ([request |-> "write", data |-> d])]
                       /\ pc' = [pc EXCEPT ![self] = "Wait"]
                 /\ UNCHANGED << db_value, result >>

Confirm(self) == /\ pc[self] = "Confirm"
                 /\ query[self].type = "response"
                 /\ result' = [result EXCEPT ![self] = query[self].result]
                 /\ Assert(result'[self] = db_value, 
                           "Failure of assertion at line 53, column 21.")
                 /\ pc' = [pc EXCEPT ![self] = "Request"]
                 /\ UNCHANGED << query, db_value >>

Wait(self) == /\ pc[self] = "Wait"
              /\ query[self].type = "response"
              /\ pc' = [pc EXCEPT ![self] = "Request"]
              /\ UNCHANGED << query, db_value, result >>

clients(self) == Request(self) \/ Confirm(self) \/ Wait(self)

Next == database
           \/ (\E self \in Clients: clients(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun May 26 23:02:13 JST 2024 by 81902
\* Created Sun May 26 21:57:45 JST 2024 by 81902
