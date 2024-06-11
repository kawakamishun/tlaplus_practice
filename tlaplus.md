# TLA+ toolbox

## What is

* TLA+
  * Temporal Logic of Actions
  * 並行システムと分散システムの設計、モデル化、検証
  * TODO
  * Amazon DynamoDBの非同期更新故のデータ整合性に問題が生じないことの検証
* 安全性検査
  * すべてのモデルが無効な状態に遷移しないこと
    * 不変条件
* 活性検査
  * 最終的に沿うて鄭通の振る舞いをすること

## Environment

### TLA+ toolbox

* <https://github.com/tlaplus/tlaplus/releases>
  * TLAToolbox-1.7.1-win32.win32.x86_64.zip
  * tla2tools.jar [latest version]
* Unzip and extract to any folder
* execute `toolbox.exe`

### PT

* Practical TLA +
  * <https://github.com/Apress/practical-tla-plus>
* usage
  * deploy module to any folder
  * toolbox > File > Preferences > TLA+ Preferences > TLA+ library path locations: > Add Directory
  * usage...

    ```txt
    PT == INSTANCE PT
    SumUpTo(n) == PT!ResuceSet(LAMBDA x, y: x + y, 0..n, 0)
    ```

## 検査方法

* モデルを作成する
  * toolbox > [File] > [Open Spec] > [Add New Spec]
* モデルを変換する
  * toolbox > [File] > [Translate PlusCal Algorithm]
  * `Ctrl+T`
* モデルを検査する
  * モデルを追加する
    * toolbox > [TLC Model Checker] > [New Model]
  * モデルを実行する
    * toolbox > [TLC Model Checker] > [Run Model]
    * `F11`

## 2. TLA+, PlusCal

### What is ?

* refer to: <https://zenn.dev/riita10069/articles/bc689cae1c7bc0>

### 値

* `文字列`
  * "abcde"
* `整数`
  * [-]*[0-9]+
* `ブール値`
  * {TRUE, FALSE}
* `モデル値`(model value)
  *

### 演算子

* 演算子

| 演算子 | 意味 | 例 |
| -- | -- | -- |
| a `=` b | 等しい | >> 1 = 2<br>FALSE |
| a `/=` b | 等しくない | >> 1 = 2<br>TRUE |
| x `/\` y | 論理積(AND) | >> TRUE /\ TRUE<br>TRUE |
| x `\/` y | 論理和(OR) | >> TRUE \/ FALSE<br>TRUE |
| x `:=` y | 代入 | (PlusCal) |
| `~`x | 否定 | >> ~TRUE<br>FALSE |

* 算術演算子
  * `+`, `-`, `%`, `*`, `\div`
  * 範囲演算子 `a..b` == `{a, a+1, a+2, ..., b}`

### データ型

#### 集合

* リテラル: set = `{"a", "b", "c"}`

| 演算子 | 意味 | 例 |
| -- | -- | -- |
| x `\in` set | 集合の要素である | >> 1 = 1..2<br>TRUE |
| x `\notin` set | 集合の要素でない | >> 1 = 1..2<br>FALSE |
| `~`(x `\notn` set) | 集合の要素でない | |
| set1 `\subseteq` set2 | 集合の部分集合である | >> {1,2} \subseteq {1,2,3}<br>TRUE |
| set1 `\union` set2 | 和集合 | >> {1..2} \union {2..3}<br>{1,2,3} |
| set1 `\intersect` set2 | 積集合 | >> {1..2} \intersect {2..3}<br>{2} |
| set1 `\` set2 | 差集合 | >> {1..2} \ {2..3}<br>{1} |
| `Cardinality(`set`)` | 集合の要素数 | >> Cardinality({"a","b","c"})<br>3 |

* 集合の変換
  * フィルタリング
    * `{x \in set: <条件式>>}`
  * マッピング
    * `{<式>: x \in set}`

  ```tlaplus
  >> {x \in 1..3: x<2}
  {1}
  >> {x*2: x \in 1..2}
  {2, 4}
  ```

#### タプル, シーケンス

* リテラル: tup = `<<a, b, c>>`

```tlaplus
tup = `<<"a", {1,2}>>`
tup[1] = "a"
tup[2] = {1,2}
```

| 演算子 | 意味 | 例 |
| -- | -- | -- |
| `Head(`seq`)` | 先頭 | >> Head(<<1,2,3>>)<br>1 |
| `Tail(`seq`)` | 末尾 | >> Tail(<<1,2,3>>)<br>{2,3} |
| `Append(`seq, x`)` | 末尾追加 | >> Append(<<1,2>>,3)<br><<1,2,3>>|
| seq1 `\o` seq2 | 結合 | >> <<1>> \o <<2,3>><br><<1,2,3>> |
| `Len(`set`)` | 長さ | >> Len(<<1,1,1,1>><br>4 |

#### 構造体

* リテラル: struct = `[key1 |-> val1, key2 |-> val2, ...]`
* 値を参照: `struct.key`

```tlaplus
>> [a |-> 1, b |-> <<1,{}>>].b
<<1,{}>>
```

### PlusCal アルゴリズム

* 代入
* assert <式>
  * 不変条件

  ```tlaplus
  EXTENDS TLC
  assert a = 1
  ```

* skip
  * 何もしない no-op

* if

```tlaplus
if condition1 then
  body;
elsif condition2 then
  body;
else
  body;
end if;
```

* while

```tlaplus
while condition do
  body;
end while;
```

* マクロ

```tlaplus
macro name(arg1, arg2) begin
  \* do something
  \* 代入、アサーション、if文
end macro;

begin
  name(x,y);
end algorithm
```

#### 開始状態

* 変数`x \in set`で初期化した場合、TLCはxの定義域のすべての値に対して、アルゴリズムを実行する

```tlaplus
(*--algorithm in
variables x \in 1..3;
begin
  assert x <=2;
end algorithm; *)
```

* べき(冪)集合: すべての部分集合からなる集合
  * `SUBSET set`
* 部分集合の結合
  * `UNION set`

```tlaplus
>> SUBSET {"a", "b"}
{{}, {"a"}, {"b"}, {"a","b"}}
>> UNION {{"a"}, {"b"}, {"b", "c"}}
{"a", "b", "c"}
```

* 2つの集合からペアのタプル集合を作る
  * `set1 \X set2`
  * 1つ目の要素をset1の要素として、2つ目の要素としてset2の要素を持つすべてのタプル からなる集合

```tlaplus
>> {"a", "b", "c"} \X {1..2}
{<<"a", 1>>, <<"a", 2>>, <<"b", 1>>, <<"b", 2>>, <<"c", 1>>, <<"c", 2>>}
```

* 構造体の集合を生成する
  * `[key: set]`

```tlaplus
>> [a: {"a", "b"}]
{[a |-> "a"], [a |-> "b"]}
>> [a: {"a", "b"}, b: (1..2)]
{[a |-> "a", b |-> 1], [a |-> "a", b |-> 2]
 [a |-> "b", b |-> 1], [a |-> "b", b |-> 2]
}
```

#### 非決定論的ふるまい

* `either`
  * 複数の選択肢の中からランダムに選択して実行する

```tlaplus
either
  \* 分岐1
or
  \* 分岐2
  \* ...
or
  \* 分岐n
end either;
```

* `with`
  * 一時変数の生成

```tlaplus
with var = value do
  body;
end with;
```

  * 非決定論的にすべての要素を使って検査する

```tlaplus
with var \in set do
  body;
end with;
```

---

### 複雑なデータ型

#### 演算子

* プログラミングのプロシージャのようなもの
* リテラル: `Op(arg1, arg2) == Expr`
* 例(TLA+)

  ```tlaplus
  BinTypes == {"trash", "recycle"}
  SetsOfFour(set) == set \X set \X set \X set
  Items == [type: BinTypes, size: 1..6]

  (*--algorithm recycler
  variables
    capacity \in ...
    ...
    items \in SetsOfFour(Itemes);
    curr = "";
  ```

* 例(PlusCal)

  ```tlaplus
  define
    NoBinOverflow ==
      capacity.trash >= 0 /\ capacity.recycle >= 0
    CountsMatchUp ==
      Len(bins.trash) = count.trash
      /\ Len(bins.recycle) = count.recycle
  end deine;
  ...
  assert NoBinOverflow /\ CountsMatchUp;
  ```

  ```tlaplus
  define
    Invariant ==
      /\ capacity.trash >= 0
      /\ capacity.recycle >= 0
      /\ Len(bins.trash) = count.trash
      /\ Len(bins.recycle) = count.recycle
  end deine;
  ```

* 高階演算子 `Op(_, _)`
  * 他の演算子をパラメータとして受け取る演算子

    ```tlaplus
    Add(a, b) == a + b
    Apply(op(_, _), x, y) == op(x, y)

    >> Apply(Add, 1, 2)
    3
    ```

* 無名演算子 `LAMBDA`
  * `LAMBDA param1, param2 ,.., paramN: body`
  * 例

  ```tlaplus
  >> Apply(LAMBDA x, y: x + y, 1, 2)
  ```

#### 不変条件

* 演算子を不変条件として利用できる
* 不変条件: モデルの各捨てプの最後に検査される論理式
  * 常に満たさなければならない性質
* 使い方
  * toolbox > [Model] tab > [Model Overview] > [What to check?] > [Invariants]
  * 不変条件の演算子を追加して、検査する

##### 論理演算子

* 量化子 `\A`
  * 集合に含まれているすべての要素
  * `\A x \in set: P(x)`
  * 集合内のすべての要素に対してP(x)がTRUEである

  ```tlaplus
  AllLessThan(set, max) == \A num set: num < max
  ```

* 量化子 `\E`
  * ある要素が集合内に存在する
  * `\E x \in set: P(x)`
  * P(x)がTRUEである要素が集合内に少なくとも一つ存在する

  ```tlaplus
  SeqOverlapsSet(set, set) == \E x \in 1..Len(seq): seq[x] \in set
  ```

* `P => Q`: PならばQ
  * `^P /\ Q`
* `P <=> Q`: PとQは同等
  * `(P /\ Q) \/ (^P /\ ^Q)`

##### 式

* LET-IN
  * ローカル演算子やローカル定義を追加できる

  ```tlaplus
  RotateRight(seq) ==
    LET
      last == seq[Len(seq)]
      first == SubSeq(seq, 1, Len(seq) - 1)
    IN <<last>> \o first
  ```

* IF-THEN-ELSE
  * `IF condition THEN Expr1 ELSE Expr2`

  ```tlaplus
  Max(x, y) == IF x > y THEN x ELSE y
  ```

* CASE
  * switch-case

  ```tlaplus
  CASE x = 1 -> TRUE
    [] x = 2 -> TRUE
    [] x = 3 -> 7
    [] OTHER -> FALSE
  ```

* CHOOSE
  * `CHOOSE x \in S : P(x)`
  * P(x)=TRUEになるxを選択する

  ```tlaplus
  IndexOf(seq, elem) == CHOOSE i \in 1..Len(seq): seq[i] = elem

  Max(set) == CHOOSE x \in set: \A y \in set: x >= y
  ```

---

#### 関数

* 一連の入力（定義域）を一連の出力にマッピングする
* `[x \in set |-> P(x)]`

```tlaplus
>> [x \in 1..2 |-> x * 2]
<<2, 4>>
>> Head([x \in 1..2 |-> x * 2])
2
```

* 関数で演算子を作る
  * `Op == [x \in set \-> P(x)]`
  * メモ:
    * 演算子は、任意の入力に対応できる
    * 関数は、定義域が指定されないといけない

* `PT!ReduceSet`
  * 演算子を集合に対して再帰的に適用する

  ```tlaplus
  PT == INSTANCE PT
  SumUpTo(n) == PT!ReduceSet(LAMBDA x, y: x + y, 0..n, 0)

  >> SumUpTo(10)
  55
  ```

* `DOMAIN`: 関数がとりうる入力を指定する前置演算子
* `@@`: 関数をマージする
* `:>`: `a :> b`は、`[x \in {a} |-> b]` と同じ

##### 関数の集合

* `set1 -> set2`
  * set1 の要素をせt2の要素にマッピングするすべての関数からなる集合

```tlaplus
>> [s \in {"a", "b"} |-> {1, 2}]
[a |-> {1, 2}, b |-> {1, 2}]

>> [{"a", "b"} -> {1, 2}]
{[a |-> 1, b |-> 1], [a |-> 1, b |-> 2],
 [a |-> 2, b |-> 1], [a |-> 2, b |-> 2],
}
```

* シーケンスの集合の作成
  * `SeqOf(set, count) == [1..count -> set]`

  ```tlaplus
  >> SeqOf({"a", "b", "c"}, 2)
  {<<"a", "a">>, <<"a", "b">>, <<"a", "c">>, 
   <<"b", "a">>, ...
  }
  ```

### モジュール化

モデルの単純化、一般化

#### 定数

* `CONSTANTS {定数名}`

  ```tlaplus
  CONSTANTS Capacity, ValueRange, SizeRange, Items
  ```

* 定数の値の指定
  * toolbox > [Model] tab > [Model Overview] > [What is the model?]
    * Ordinary assignment
      * TLA＋で使用できる値: 数値、集合、シーケンス、関数
    * Model value
      * モデル値、（enum定義みたい）
    * Set of model values
      * モデル値の集合
      * Symmetry set
        * 対象集合、{a,b,c} のモデル値の時に、aをbに置換、bをcに置換、cをaに置換しても同じ結果が得られるケース
        * 検査時の状態数の削減効果がある

#### ASSUME

* 前提条件
  * 条件を満たさない場合、仕様を実行できない

  ```tlaplus
  ASSUME SizeRange \subseteq 1..Capacity
  ASSUME Capacity > 0
  ASSUME \A v \in ValueRange: v >= 0
  ```

#### TLCランタイム

* What is the behavior spec?
  * [Temporal formula] にしとけばいい
* What to check?
  * Deadlock: デッドロックを検出するか
  * Invariants: 不変条件
  * Properties: 活性検査
* How to run?
  * TLCの高速化
  * TLC Options
    * Additional Definition
      * 演算子の追加定義
    * State Constraint
      * 状態制約
        * モデルのすべての状態でTRUEになる式
        * 違反してもモデルは失敗しないので、不変条件違反を見逃す可能性がある
        * 探索空間を狭くしてモデルの検査を素早く終えることができる
    * Definition Override
      * カスタム定義による演算子の上書き
* TLC Options
  * Checking Mode
    * Model Checking mode
      * 検査モード
        * 幅優先探索（デフォルト）
        * 深さ優先探索
    * Simulation mode
      * ランダムトレース
      * 大規模な状態空間でのストレステストなど。

#### エラートレース

* [Error-Trace Exploration]
  * デバッグ

#### TLCモジュール

* `Print(val out)`
  * User Outputへvalとoutを出力、outを評価する
* `PrintT(val)`
  * `Print(val, TRUE)`
* `Assert(val, out)`
  * valがFALSEの場合、outを出力する
* `Permutaions(set)`
  * 集合setについて考えられるすべての順序集合
* `SetSeq(seq, Op(_, _))`
  * Opに基づいてシーケンスを並べ替える

#### インポート

* EXTENDS
  * モジュールを同じ名前空間にダンプする
* INSTANCE
  * 複数のモジュールをインポートできない
  * `LOCAL INSTANCE`
    * プライべーとスコープ
  * モジュールの名前空間化
    * `PT == INSTANCE PT`
  * パラメータ化されたモジュールのインポート

    ```tlaplus
    ----------- module Point ----------
    LOCAL INSTANCE Integers
    CONSTANTS X, Y
    ASSUME X \in Int
    ASSUME Y \in Int

    Point == <<X, Y>> 
    Add(x,y) == <<X + x, Y + y>>
    ===================================

    INSTANCE Point WITH X <- 1, Y <- 2

    >> Point
    <<1, 2>>
    >> Add(3, 4)
    <<4, 6>>
    ```

---

### 5. 並行処理

#### ラベル

* 仕様の原子性の粒度を決定する
  * ラベル内のすべてのものを1つのステップで実行する
  * 記述ルール
    * 各プロセスの始め、各while分の前にラベルを配置しなければならない
    * マクロやwith文の中にラベルを配置してはならない
    * goto文の後に必ずラベルを配置しなければならない
    * either、ifを使っていて、その中にラベルを含む分岐がある場合は、制御構造が終わった後にラベルを配置しなければならない
    * ラベル内で同じ変数に2回代入してはならない

#### プロセス

* 文字通りプロセスの記述
  * プロセスに値を割り当てること 名前とか
  * ラベルで始まっていること

```tlaplus
process writer = "writer"
begin Write:
  \* do
end process;
```

##### await

* `await <式>`
  * <式>がTRUEになるまえステップの実行を阻止する

##### デッドロック

* 複数のawaitがお見合いすると、デッドロックになる
* エラーシミュレーションのパターン possibly

  ```tlaplus
  either
    skip;
  or
    NotifyFailure:
      current_message = := "none";
      add_to_queue("fail");
  ```

* プロセスセット
  * マルチプロセスの記述

  ```tlaplus
  process reader \in {"r1", "r2"}
    ...
  end process;
  ```

#### プロシージャ

* ラベル使用したふるまいの記述

  ```tlaplus
  procedure add_to_queue(val="") begin
    Add:
      await Len(queue) < MaxQueueSize;
      queue := Append(queue, val);
      return;
  end procedure;

  ...
  call add_to_queue("msg");
  ```

---

### 6. 時相論理

* アルゴリズムは終了するか
* キューのメッセージはすべて処理されるか
* 障害が発生した場合、そのシステムは安定した状態に戻るか
* データベースは最終的に整合性のとれた状態になるか

#### 停止性

##### スタッタリング (Stuttering)

* 何のアクションも起こさない ステップが生じること
  * 停止性を満たさなくなる、システム全体が変化しなくなるので停止性の検査ができない
* 現実の事象を表現するのであれば
  * サーバークラッシュ、プロセスタイムアウト、目的のシグナルが到達しない など
  * TLA+のデフォルトの振る舞い 「すべてのものはクラッシュする可能性がある」

##### 公平性

* 弱公平性
  * 有効であり続けるならば、最終的に発生する

  ```tlaplus
  fair process process_name = "aaa"
  begin
  ...
  end process;
  ```

* 強公平性
  * 繰り返し有効になるならば、最終的には発生する

  ```tlaplus
  fair+ process process_name = "aaa"
  begin
  ...
  end process;
  ```

#### 時相演算子

* `[]P`
  * "常に"
* `<>P`
  * "最終的に"
    * 意訳: いつかそうなる
* `P ~> Q`
  * PならばQ
  * PがTrueになる状態があるとすれば、Qがその時点または将来の時点においてTureにならなければならない
* ‘[]<>P'
  * 常に最終的にはTrueになる
    * 途中でFalseになるかもしれないが、最後はTrueになることを、繰り返す
* `<>[]P`
  * 最終的に常にTrueになる
    * Trueになって以降ずっとTrueのままであり続ける、いつかそんな状態になる

* 時相特性の制約
  * 時相特性が必要になる機会はそれほど多くなくて、ほとんどの場合は不変条件で表すことができる
    * あるいは、`[]`、`<>`、`~>`の単純な式で十分な場合が多い
  * 活性検査に時間がかかる
    * 不変条件は個々の状態ごとに検査される、時相特性は一連の状態遷移パスにわたって検査するため
  * 時相特性と対称集合を組み合わせてはならない
    * 活性エラーを見逃す可能性（重複する状態をスキップするから）

#### サンプル

* `dekker.tla`
* `dekker_fix.tla`  fix startavation problem
* `dekker3.tla`  Crashable (un-fair) process
* `dekker4.tla`  fix Crashable process, Copilot version !

---

### 7. アルゴリズム

#### シングルプロセス

#### マルチプロセス

---

### 8. データ構造

#### リンクリスト

* データ構造　ロジックの作成方法
* 再利用可能なモジュールの作成方法とその利用方法

`LinkedLists.tla`

---

### StateMachine

* TLA+は 有限状態モデルで動作する

* PlusCalのStateMachineの作り方
  * 分岐とプロセスは、await文とeither文によって制御できる

`Door.tla`
`Door2.tla` key有, シングルプロセス
`Door3.tla` key有, マルチプロセス、より簡潔で明確になる

#### リファインメント

* DBへの読み書きシステムのモデル化する例
* 最初はデータの読み書きに抽象化してモデルを作成する
  * `Database.tla`
    * DBは存在せず、クライアントが直接データを読み書きするモデル
* 次にデータベースを追加して、クエリによるリクエストに対して、DBがデータを読み書きしてクライアントへ応答する
  * `Database2.tla`
    * クライアント数1の場合は、動作する
    * クライアント数2の場合は、クライアントが読み取ったデータとDBのデータが一致するべき不変条件を満たさなくなる
      * `assert result = db_value;`
      * データを読み取ったクライアントがデータを参照する前に、もう一つのクライアントがデータを変更してしまうから
        * 解決の考え方として
          * 「クライアントは常にデータベースの現在の値を読み取る」 ← 実システムに沿ってるか疑問？
            * クライアントがDBのデータを知っていること
          * 「レスポンスはデータベースがリクエストを処理した時点の値」 ← 考えるべきはこっち
            * DBがクライアントに対して正直であること
            * リクエストした時点でリードしたデータが正しいことを検証する方法を考える

#### ゴースト変数

* 不変条件を検証するために追跡するコンテキストデータ＝ゴーストデータ
  * DBの例だと、リクエスト時点の履歴のデータ
* `Database3.tla`
  * ゴースト変数 `ghost_db_history` をreadリクエストに対するレスポンスとして、履歴データとして保存
  * クライアントのプロセスでは、responseの`query[self].result`と、`ghost_db_history`を比較して不変条件を検証する
    * 不変条件の検証用にゴースト変数を参照しているだけなので、クライアントがゴースト変数を参照してはいない

---

### 9. 状態機械

#### Example

* Door.tla
  * ドアのopen/close
* Door2.tla
  * ドアのopen/close + lock
* Door3.tla
  * open/closeとlock/unlockを別のprocessで表現する
  * State mchineが複雑になった場合に、別々のプロセスに分割することで単純化できる
    * Doorの例だと現実世界との乖離がある気がするが・・・

* 段階的詳細化 リファインメント
  * Database.tla
    * クライアントとDB、データのRWのシンプルな概念のモデル
  * Database2.tla
    * DBMS クラサバの構成、DBサーバーへのR/W request、レスポンス受信待機を追加
      * R requestに対する検証が正しくできない
        * queryに対する応答結果の検証で、DBのデータを直接参照して検証する場合、データ応答結果と検証時点のDBの状態が変わってる可能性があり、検証不一致になりうる
  * Database3.tla
    * 不変条件を検証するために、補助データ（"ゴーストデータ"）を導入して、クライアントのレスポンスの不変条件assertionの検証を行う
      * ごーすとでーたは、不変条件の検査にのみ使用すること。仕様の振る舞いが変化しないこと

---

### 10. ビジネスロジック

* モデル作成の手順
* 例: 図書館 書籍の貸出管理システム

#### 要件を定義する

* 標準的セットアップ

  ```tlaplus
  EXTENDS Integers, TLC, Sequence
  PT == INSTANCE PT
  ```

* 定数
  * 定義域の定数宣言

    ```tlaplus
    CONSTANTS Peopel, Books, NumCopies
    ASUUME NumCopies \subseteq Nat
    ```

  * 本の所蔵数は1冊のみか、複数冊の可能性があるか？
    * 1冊のみ: `{b \in Books}`
    * 1冊のみ: `[Books -> NumCopies]`

    ```tlaplus
    variables
      library \in [Books -> NumCopies];
    ```

* 仕様を決める
  * 本を借りる、本を返却する
    * 利用者が借りている本
    * 本を借りるアクション
    * 本を返却するアクション

* 便利な演算子の追加
  * 集合への要素の追加、削除

  ```tlaplus
  set ++ b == set \union {b}
  set -- b == set \ {b}
  ```

* processのデザイン
  * 常に最終的に実行されると想定する -> `fair process`

#### 不変条件を追加する

* 安全性の検査
  * TLA＋パターン
    * TypeInvariant
      * 変数の型を定義する
        * プロセスのプライベート変数に関する制約を検査する場合は、PlusCal変換結果の下に不変条件を配置する

      ```tlaplus
      TypeInvariant == 
        /\ library \in [Books -> NumCopies ++ 0]
        /\ books \in [People -> SUBSET Books]
      ```

#### Livenessを追加する

* 時相特性を追加する
  * 最終的にシステムの目的が達成できること
  * 例: 利用者が特定の本を読みたいのなら、それらの本は最終的に利用者に貸し出されること
    * 制約違反: 片方のユーザーのみが同じ本を借り続けることができる

#### 機能仕様の追加

* 例: 予約機能の追加
  * 予約変数に関するいくつかの疑問
    * `[Books -> People]` どの本についても一人の利用者しか予約できない、
      * 未予約の本の表現のためにNULLを導入する？ -> モデルが複雑になる
      * 他の人が予約しようとしたら、予約できない？あるいは、先行する予約を上書きする？ -> ありえない
    * `[Books -> SUBSET People]` 複数の利用者が予約できる、順序不問
      * 未予約の状態 `{} \in SUBSET People` も含む
      * 最初に予約した人は優先されるべきでしょ
    * `[Books -> Seq(People)]` 複数の予約者が予約できて、優先順位付き
  * 例では、最初は2番目で考えてみる
    * 一人の利用者が予約、借りるを 繰り返すことができてしまう。やはり、予約順の管理は必要だ
      * 予約表に順序性を持たせよう

* 予約順番管理
  * 予約リストへの登録を1人1回に制限する
    * 予約リストへの同一利用者の重複登録は許可しない
      * 予約表シーケンスの2つのインデックスの値が一致しないことを条件に、Booksをフィルタする

    ```tlaplus
    NoDuplicateReservations ==
    \A b \in Books:
        \A i, j \in 1..Len(reserves[b]):
            i /= j => reserves[b][i] /= reserves[b][j]
    ```

* 利用者2人、本2冊の仮定では、デッドロックする
  * 興味のない本を予約したせいで、他の利用者がその本を読めなくなる

* 予約の有効期限の管理
  * 利用者全員が最終的に読みたい本を読むのではなく、
  * 本を借りることができる状態になる（利用者に本を借りるチャンスが与えられる）

  * (問題) 予約する > 期限切れ > wantsから本が削除されない（本を借りたら削除されるから） > 予約する > 期限切れ ...以下同文
    * ユーザーが本を借りないかもしれない。その場合wantsが空になることもない
    * Livenessを満たすためには、ユーザーがシステムの都合の良いようにふるまうことを期待することになる
      * 現実的にそんなことはない。人間の行動に非現実的な仮定をおかないと、Livenessを保証できない
  * いくつかの特別なケースでうまくいくかどいうかの検証は可能です。

* 「利用者がwantsに追加できる本は最大1冊まで」の制約を付けてみる => OK!

  ```tlaplus
  EXTENDS FiniteSets

  \A p \in People: Cardinality(wants[p]) <= 1
  ```

* 仕様のあいまいさを解消し、仕様が意味するところを深く理解し、要求を満たせないことを証明した。

---

### 11. MapReduce

大規模な仕様の開発を理解する

* 大規模な仕様を作成するプロセス
* アイディア出し
* つまずき

* map: 同じ計算を複数のノードに分散させる
* reduce: 1台のノードで計算結果を統合する

#### 仕様概要

構成

* 1台目のノードをReducer、残りの3台をWorker
* Reducerは、本1,4,7,...、本2,5,8,...、本3,6,9,...をそれぞれ割り当てる
* 各Workerは割り当てられた本の単語の数を計算し、結果をReducerに報告する
* Reducerは数を合計し、最終的な単語の数を割り出す

仕様

* すべてのWorkerが常に正常に動作するものと仮定する
* Workerの障害を考慮に入れたフォールトトレランス
* リカバリメカニズムが部分的に失敗するとしてもうまくいくこと

#### 第1ステージ: 基本的な仕様

* 構成要素を定義する `CONSTANTS Workers, Reducer, NULL`
* 可能性のあるInputを定義する `PossibleInputs == PT!TupleOf(0..2, 4)`
  * とりあえず最初は、Worker2つ、4冊の本を2つのWorkerに均等分配する、各本の単語の数を0..2と仮定する
* 仕様が正しいことを検証するための、不変条件を先に考えておく `assert final = SumSeq(input);`
* 各processの振る舞いを実装する
  * 段階的にモデルを実行して、期待通りの結果になるか、結果は妥当なのかを確認しながら詳細化すること
  * Workerの結果をReducerが取得するとして、その方法は？ Wokerに対するpingの応答として結果を取得する
    * 考え方: Workerの処理官僚の判断としてNULLを使うのが妥当か？
      * 処理済み？処理済み？処理途中？区別がつかない
    * 考え方: Workerの処理の開始は？処理対象のアイテムのキューが空になったら終了する
      * キューが空でなくなるまで待機する（キューにアイテムが追加されたら動き出す）
  * Workerに対して、処理対象のアイテムを分配する
    * 各Workerに番号を割り当て、アイテムを各Workerに循環的に割り当てる・・・
      * PT使ってて難しい
        * PT!TupleOf()
        * PT!OrderSet()
        * PT!Index()
        * PT!SelectSeqByIndex()
        * PT!SeqMod()

#### 第2ステージ: Liveness

* 活性を証明するためLivenessを追加する
  * `Liveness == <>(final = SumSeq(input))`
  * => Stuttering !
    * Workerの処理が完了しなければ、集計も永遠に終われない
  * 公平なプロセスにすれば、解決できる可能性はあるが、、、
    * Workerはいつクラッシュするか分からない、クラッシュの可能性を想定する
    * ハッピーパスで動作するだけではない、フォールトトレラントにしたい
  * **Workerの一部で問題が発生したとしても動作し続ける**ことを目指す

* 仮定
  * Reducerは公平であること
  * 公平なWorkerが少なくとも一つは存在する
  * 公平なWorkerがどれかは重要ではない
    * **CHOOSEにより任意のWorkerを選択できるので、状態空間を縮小できる**
  * Reducerは、公平で花いWorkerのクラッシュを検知できるとは限らないが、公平なWorkerがクラッシュしている判断を誤ることはない
    * システムの設計が容易になる

* 公平なプロセスの振る舞い ∈ 公平でないプロセスの振る舞い
  * 公平でないプロセスが安全なら、サブセットである公平なプロセスも安全である、と言える

* Workerの一つは処理を完了するが、残りのWorkerは処理を完了せず、Reducerを待たせるかもしれない
  * Reducerの振る舞いを変更する
* Reducerがやるべきこと
  * 「Workerを消費済みとして宣言し、totalに足す」 標準的なふるまい
  * 「クラッシュしたWorkerのキューを正常に動作しているWorkerに移動する」
    * クラッシュしたWorkerの検出方法？
      * Workerの結果が消費されているなら、そのWorkerはクラッシュしなかった
      * 消費されてないWorkerはクラッシュしているかもしれない
    * (問題点2) 再割当をどう考えるか？
      * クラッシュしたWorkerを永遠に待ち続けるか、あるいは、クラッシュしてない場合は時間が経ってから結果が得られる結果を間違える
        * クラッシュしたWorkerを「消費済み」と宣言すれば、結果を間違うことはない
      * キューの再割当先が消費済みWorkerの可能性がある（並行性のため、再割当て先Workerが再割当処理中に、消費済みになってしまうかもしれない）
        * 再割り当てしたキューのアイテムの値が合計されない
      * さもなければ、再割当先を未消費のWorkerに限定するか？最後のWorkerがクラッシュしたらどうするかの問題が残る
      * 妥結点: 公平なWorkerはどれも再割当先にできるが、消費済みだった場合は未消費の状態にする
    * reassignとは？
      * 割当元のキューのアイテムを、割当先のキューにダンプすること
        * キューをReducerと公平なWorker間で直接送信したデータを表していて、抽象化したのだから、キューを直接操作することはできない
        * **キューを破壊的に更新することになるので、データの正しさも保証できない**
      * from_workerに送信したものをReducerは知っているはず
        * Reducerが同じアイテムをto_workerに送信できる
        * 割当をローカルで追跡すればよい
          * ReducerのローカルでWorkerごとの割当済みアイテムを管理する `assignments = [w \in Workers |-> <<>>]`
    * (問題点2) reassign組込み後の問題点
      * 処理1巡目修了後に公平なWorkerに対する再割り当て、公平なWorkerは消費済みになっているので、再割当て後のアイテムを処理しない。再割当て後の結果が合計に反映されない
      * 問題: Reducerから見て、Workerに割り当てたすべてのアイテムがresultに含まれているのかが分からない
        * resultに情報を追加する
          * ReducerはWorkerに割り当てたアイテムの数を知っている
          * Workerは処理したアイテムの数を知っている
          * [割当アイテム数=処理済みアイテム数]の時にのみ、結果を消費すればいい！
            * finalで最初の割当を二重にカウントする問題がある
              * 再割当て時に、割当先のWorkerの最終結果を無効にする

#### 第3ステージ: ステータス

* ダウンしているノードを調べたい
* ハートビートプロトコルを仕様に追加する
  * 仕様: Reducerは公平ではないWorkerの割当を公平なWorkerへ再割当てできる
    * どのWorkerが公平なのかはわからない
  * 前提: 2つの公平ではないWorkerに異なるふるまいをさせる、1つのWorkerは常に公平でなければならない
  * Workers <- {w1, w2, w3}
    * 実行すると、モデルが止まらなくなる エラー
    * プラクティス: 変数の値を制限するために、TypeInvariantを定義する
      * 「アイテムの総数は決まっている、Workerのキューに含まれているアイテムの数がその数を超えることはない」
* 問題1: Workerのキューサイズ不変条件を満足しない
  * Workerに再割当て、Workerを消費済み、「元」のWorkerに再割当てして消費しない。。。
    * 古い割当てを内部キューから削除する案？
      * Workerの処理完了の追跡のために処理した割当て数を使っているので削除できない
    * 別案: ノードにステータスを定義する
      * active, inactive, broken
      * "active"ノードがなくなったら処理完了

#### 練習問題

* エッジケース
  * アイテムの数がWorkerの数よりも少ない場合、うまくいかない
    * 一部のWorkerがWaitForQueueから離れなくなるから
* 次の条件でも検査をパスするように修正すること
  * 条件
    * Workers <- {w1, w2, w3}
    * ItemCount <- 2
    * PROPERTY ReducerLiveness
    * INVARIANTS TypeInvariant

* 解は
  * Reducerが `RducerResult`ラベルに留まってしまって、Finishをいつまでも実行しないこと

---

### PT モジュール


---

### template

* example.tla

```tlaplus
-------------------------------- MODULE example --------------------------------
EXTENDS TLC, Sequences, Integers, FiniteSets
CONSTANTS NULL, NumCopies
ASSUME NumCopies \subseteq Nat
PT == INSTANCE PT

(*--algorithm example

variable dummy \in Int,
  dummy2 \in {"a", "b", "c"};

macro xxxx() begin
    \* do something
    skip;
end macro;

procedure pppp() begin
    \* do something
    skip;
    return;
end procedure;

process proc = "process_name"
begin MyLabel:
    \* do something
    skip;
end process;

end algorithm*)
```
