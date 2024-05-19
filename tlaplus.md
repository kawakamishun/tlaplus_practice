# TLA+ toolbox

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

## TLA+, PlusCal

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

### 並行処理

#### ラベル

* 仕様の原子性の粒度を決定する
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

### template

* example.tla

```tlaplus
-------------------------------- MODULE EXSAMPLE --------------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets
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
