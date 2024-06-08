------------------------------ MODULE led ------------------------------
EXTENDS TLC
CONSTANT NULL, Leds

LOCAL ErrorMessage == Leds \union {NULL}

\* LED control logic
SwitchError(object, specified, stat) == CASE object = specified /\ (stat = "off" \/ stat = "alert") -> "error"
                                          [] object = specified /\ stat = "error" -> "off"
                                          [] stat = "alert" -> "off"
                                          [] OTHER -> stat
SwitchAlert(object, specified, stat) == CASE object = specified /\ stat = "off" -> "alert"
                                          [] object = specified /\ stat = "alert" -> "off"
                                          [] OTHER -> stat
                                                

(*---algorithm led
variables
    \* stat = {"off", "error", "alert"}
    stats = [n \in Leds |-> "off"],
    errorNotice = NULL,
    alertNotice = NULL;

define
    IsActive(led) == (stats[led]) 
    InError == (\E n \in Leds: stats[n] = "error")
    InAlert == (\E n \in Leds: stats[n] = "alert")
\*    Invariant ==
\*        (InError /\ ~InAlert)
\*        \/ (\A n \in Leds: stats[n] = "off")
\*        \/ (~InError /\ InAlert)
    Invariant ==
        (\E n \in Leds: stats[n] = "error" /\ ~((\E n2 \in Leds: stats[n2] = "alert")))
        \/ (\A n \in Leds: stats[n] = "off")
        \/ (~(\E n \in Leds: stats[n] = "error") /\ (\E n2 \in Leds: stats[n2] = "alert"))
    MayErrorOn == <>(errorNotice /= NULL => \E n \in Leds: stats[n]="error")
    MayAlertOn == <>(alertNotice /= NULL => \E n \in Leds: stats[n]="alert")
    \* for debug    
    VerifyWillErrorOn == [](errorNotice /= NULL => ~(\E n \in Leds: stats[n]="error"))
    VerifyWillASlertOn == [](alertNotice /= NULL => ~(\E n \in Leds: stats[n]="alert"))
end define;

\* LightService
fair process ALS = "als"
begin
    Service:
        while TRUE do        
            if errorNotice /= NULL then
                ErrorSwitch:
                    stats := [n \in Leds |-> SwitchError(n, errorNotice, stats[n])];
            elsif alertNotice /= NULL then
                AlertSwitch:
                    if ~InError /\ alertNotice /= NULL then
                        stats := [n \in Leds |-> SwitchAlert(n, errorNotice, stats[n])];
                    end if;
            end if;
            Debug: print(<<stats, errorNotice>>);
        end while;
end process;

\* ErrorManager
fair process EWM = "EWM"
begin
    ErrorHandling:
        while TRUE do
            either  \* ON/OFF
                with n \in Leds do
                    errorNotice := n;
                end with;
            or  \* NOP
                errorNotice := NULL;
            end either;
        end while;
end process;

\* AlertInfo
fair process alertInfo = "alertInfo"
begin
    AlertHandling:
        while TRUE do
            either  \* ON/OFF
                with n \in Leds do
                    alertNotice := n;
                end with;
            or  \* NOP
                alertNotice := NULL;
            end either;
        end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "afd48e3b" /\ chksum(tla) = "e3be6e77")
VARIABLES stats, errorNotice, alertNotice, pc

(* define statement *)
IsActive(led) == (stats[led])
InError == (\E n \in Leds: stats[n] = "error")
InAlert == (\E n \in Leds: stats[n] = "alert")




Invariant ==
    (\E n \in Leds: stats[n] = "error" /\ ~((\E n2 \in Leds: stats[n2] = "alert")))
    \/ (\A n \in Leds: stats[n] = "off")
    \/ (~(\E n \in Leds: stats[n] = "error") /\ (\E n2 \in Leds: stats[n2] = "alert"))
MayErrorOn == <>(errorNotice /= NULL => \E n \in Leds: stats[n]="error")
MayAlertOn == <>(alertNotice /= NULL => \E n \in Leds: stats[n]="alert")

VerifyWillErrorOn == [](errorNotice /= NULL => ~(\E n \in Leds: stats[n]="error"))
VerifyWillASlertOn == [](alertNotice /= NULL => ~(\E n \in Leds: stats[n]="alert"))


vars == << stats, errorNotice, alertNotice, pc >>

ProcSet == {"als"} \cup {"EWM"} \cup {"alertInfo"}

Init == (* Global variables *)
        /\ stats = [n \in Leds |-> "off"]
        /\ errorNotice = NULL
        /\ alertNotice = NULL
        /\ pc = [self \in ProcSet |-> CASE self = "als" -> "Service"
                                        [] self = "EWM" -> "ErrorHandling"
                                        [] self = "alertInfo" -> "AlertHandling"]

Service == /\ pc["als"] = "Service"
           /\ IF errorNotice /= NULL
                 THEN /\ pc' = [pc EXCEPT !["als"] = "ErrorSwitch"]
                 ELSE /\ IF alertNotice /= NULL
                            THEN /\ pc' = [pc EXCEPT !["als"] = "AlertSwitch"]
                            ELSE /\ pc' = [pc EXCEPT !["als"] = "Debug"]
           /\ UNCHANGED << stats, errorNotice, alertNotice >>

Debug == /\ pc["als"] = "Debug"
         /\ PrintT((<<stats, errorNotice>>))
         /\ pc' = [pc EXCEPT !["als"] = "Service"]
         /\ UNCHANGED << stats, errorNotice, alertNotice >>

ErrorSwitch == /\ pc["als"] = "ErrorSwitch"
               /\ stats' = [n \in Leds |-> SwitchError(n, errorNotice, stats[n])]
               /\ pc' = [pc EXCEPT !["als"] = "Debug"]
               /\ UNCHANGED << errorNotice, alertNotice >>

AlertSwitch == /\ pc["als"] = "AlertSwitch"
               /\ IF ~InError /\ alertNotice /= NULL
                     THEN /\ stats' = [n \in Leds |-> SwitchAlert(n, errorNotice, stats[n])]
                     ELSE /\ TRUE
                          /\ stats' = stats
               /\ pc' = [pc EXCEPT !["als"] = "Debug"]
               /\ UNCHANGED << errorNotice, alertNotice >>

ALS == Service \/ Debug \/ ErrorSwitch \/ AlertSwitch

ErrorHandling == /\ pc["EWM"] = "ErrorHandling"
                 /\ \/ /\ \E n \in Leds:
                            errorNotice' = n
                    \/ /\ errorNotice' = NULL
                 /\ pc' = [pc EXCEPT !["EWM"] = "ErrorHandling"]
                 /\ UNCHANGED << stats, alertNotice >>

EWM == ErrorHandling

AlertHandling == /\ pc["alertInfo"] = "AlertHandling"
                 /\ \/ /\ \E n \in Leds:
                            alertNotice' = n
                    \/ /\ alertNotice' = NULL
                 /\ pc' = [pc EXCEPT !["alertInfo"] = "AlertHandling"]
                 /\ UNCHANGED << stats, errorNotice >>

alertInfo == AlertHandling

Next == ALS \/ EWM \/ alertInfo

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ALS)
        /\ WF_vars(EWM)
        /\ WF_vars(alertInfo)

\* END TRANSLATION 
=============================================================================
