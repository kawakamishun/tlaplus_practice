# PROMPT: TLA＋、Pluscalでプログラムを作成してください。

## プログラムの仕様

* 言語: TLA＋、Pluscal
* 複数のLEDを点灯させるシステムです
* LEDは複数の種類があり、LedsをCONSTANTSで定義しています
  * ここではLedsの種類が３つある前提で考えます
  * LEDの点灯状態 {"off", "error", ”alert"}
* このシステムを構成要素
  * ALS: メッセージを受信して、LEDの点灯状態を変更する
    * errorNotify受信したら、LEDの状態を"off" -> "error" または、"error" -> "off"に変更します。さらに、状態が"alert"のLEDを"off"に変更します。
    * alertNotigy受信したら、LEDの状態を"off" -> "alert" または、"alert" -> "off"に変更します
  * EWM: errorNotifyメッセージをALSに対して送信します。errorNotifyメッセージは、点灯状態を変更するLEDを指定します
  * alertInfo: alertNotifyメッセージをALSに対して送信します。errorNotifyメッセージは、点灯状態を変更するLEDを指定します
* 不変条件: すべてのLEDの点灯状態は次のいずれかの条件を満たします
  * すべてのLEDが"off"であること
  * 状態が"error"のLEDが1つ以上ある場合は、他のLEDを"alert"にしてはならない。ほかのLEDは、"off"または"error"でなければならない
  * 状態が"alert"のLEDが1つ以上ある場合は、他のLEDを"error"にしてはならない。ほかのLEDは、"off"または"alert"でなければならない

## 結果

* 変数宣言(NULL)とか、抜けたりしていた
  * 不足を補って、実行すると、パスする。詳細は未検証
* pluscalだけで作成してもらうと、TLA+のロジックとpluscalのモデル間で変数宣言の矛盾や不整合があった。自分で書いたほうがましかもしれない

```tlaplus
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
===
```