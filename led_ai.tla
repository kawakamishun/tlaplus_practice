---- MODULE led_ai ----
EXTENDS TLC, Sequences
CONSTANT Leds, NULL

VARIABLES stats, errorNotify, alertNotify

(* Function to change LED state *)
Switch(stat, newStat) == 
  CASE stat = newStat -> "off"
    [] OTHER -> newStat

(* Update the LED state *)
UpdateLed(led, newStat) ==
  /\ led \in Leds
  /\ stats' = [stats EXCEPT ![led] = Switch(stats[led], newStat)]
  /\ UNCHANGED <<errorNotify, alertNotify>>

(* Receive messages and change LED state *)
ALS ==
  /\ errorNotify \in Leds
  /\ UpdateLed(errorNotify, "error")
  /\ alertNotify = NULL
  /\ \A led \in Leds \ {errorNotify} : UpdateLed(led, "off")
      \/ alertNotify \in Leds
  /\ UpdateLed(alertNotify, "alert")
  /\ errorNotify = NULL
  /\ \A led \in Leds \ {alertNotify} : UpdateLed(led, "off")

(* Send errorNotify message to ALS *)
EWM ==
  /\ errorNotify' \in Leds
  /\ alertNotify' = NULL
  /\ UNCHANGED stats

(* Send alertNotify message to ALS *)
AlertInfo ==
  /\ alertNotify' \in Leds
  /\ errorNotify' = NULL
  /\ UNCHANGED stats

(* Initialize *)
Init ==
  /\ stats = [led \in Leds |-> "off"]
  /\ errorNotify = NULL
  /\ alertNotify = NULL

(* Next step *)
Next ==
  \/ ALS
  \/ EWM
  \/ AlertInfo

(* Invariant *)
Invariant ==
  \/ \A led \in Leds : stats[led] = "off"
  \/ \E led \in Leds : stats[led] = "error"
     /\ \A other \in Leds \ {led} : stats[other] \in {"off", "error"}
  \/ \E led \in Leds : stats[led] = "alert"
     /\ \A other \in Leds \ {led} : stats[other] \in {"off", "alert"}

(* Model *)
Spec ==
  Init /\ [][Next]_<<stats, errorNotify, alertNotify>>
  /\ WF_<<stats, errorNotify, alertNotify>>(Next)
  /\ Invariant
=============================================================================
\* Modification History
\* Last modified Sun Jun 02 15:04:09 JST 2024 by 81902
\* Created Sun Jun 02 15:00:44 JST 2024 by 81902
