------------------------------ MODULE naviled ------------------------------
EXTENDS TLC
CONSTANT NULL, NaviLeds

LOCAL ErrorMessage == NaviLeds \union {NULL}

SwitchErrorLed(stat) == CASE stat = "off" -> "error"
                          [] stat = "error" -> "off"
                          [] stat = "alert" -> "error"
                          [] OTHER -> stat

SwitchAlertLed(stat) == CASE stat = "off" -> "alert"
                          [] stat = "error" -> "error"
                          [] stat = "alert" -> "off"
                          [] OTHER -> stat

(*---algorithm naviled

variables
    \* "off", "error", "alert"    
    stats = [n \in NaviLeds |-> "off"],
    errorNotify = NULL,
    alertNotify = NULL,
    alert = [n \in NaviLeds |-> FALSE];

define
    IsActive(led) == (stats[led]) 
    ErrorNaviLeds ==
        {n \in NaviLeds: stats[n] = "error"}
    AlertNaviLeds ==
        {n \in NaviLeds: alert[n]}
    Invariants ==
        ((\E n \in NaviLeds: stats[n] = "error") 
            /\ ~(\E n \in NaviLeds: stats[n]="alert"))
        \/ (\A n \in NaviLeds: stats[n] = "off")
        \/ (~(\E n \in NaviLeds: stats[n] = "error") 
            /\ (\E n \in NaviLeds: stats[n]="alert"))
end define;

\* AlertLightService
process ALS = "als"
begin
    Service:
        while TRUE do        
            ErrorSwitch:
                if errorNotify /= NULL then
                        print(<<stats, errorNotify>>);
                        \* TODO: turn off alert led
                        stats[errorNotify] := SwitchErrorLed(stats[errorNotify]);
                elsif AlertNaviLeds /= {} then
                    AlertSwitch:
    \*                    TODO multi ON...
                        with n \in AlertNaviLeds do
                            stats[n] := SwitchAlertLed(stats[n]);
                        end with;                
                end if;
        end while;
end process;

\* ErrorWaitManager
process EWM = "EWM"
begin
    ErrorNotify:
        while TRUE do
            either
                with n \in ErrorMessage do
                    errorNotify := n;
                end with;
            or
                skip;
            end either;
        end while;
end process;

\* IOperatorAlertInfo
process alertInfo = "alertInfo"
begin
    AlertNotify:
        while TRUE do
            either  \* ON/OFF
                with n \in NaviLeds do
                    alertNotify := n;
                    alert[n] := ~alert[n];
                end with;
            or
                skip;
            end either;
        end while;
end process;

\*<>(\E n \in NaviLeds: stats[n]="error");
\*<>(\E n \in NaviLeds: stats[n]="alert");

end algorithm;*)
=============================================================================
