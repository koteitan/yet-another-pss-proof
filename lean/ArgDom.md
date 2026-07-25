[← README](README.md)

<a id="t-seqlex_of_sle_not_prefix"></a>
## 定理: 前部分列でないときの狭義比較 (T.seqlex_of_sle_not_prefix)

### 定理

[$`W, X, Y \in \mathrm{PairSeq}`$](Pss.md#d-PairSeq) とする。
[$`X \preceq_{\mathrm{lex}} W \mathbin{+\!\!+} Y`$](Cofinality.md#d-sle) であり、かつ任意の
$`X' \in \mathrm{PairSeq}`$ について $`X \ne W \mathbin{+\!\!+} X'`$ であるならば、任意の
$`Y' \in \mathrm{PairSeq}`$ について
[$`X \prec_{\mathrm{lex}} W \mathbin{+\!\!+} Y'`$](Seqlex.md#d-seqlex)。

### 証明

$`W`$ の長さに関する帰納法（$`X`$, $`Y`$, $`Y'`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(W) :\equiv \forall X, Y \in \mathrm{PairSeq},\
  X \preceq_{\mathrm{lex}} W \mathbin{+\!\!+} Y
  \ \to\ \bigl(\forall X',\ X \ne W \mathbin{+\!\!+} X'\bigr)
  \ \to\ \forall Y',\ X \prec_{\mathrm{lex}} W \mathbin{+\!\!+} Y' .
```

- **基底段** $`W = ()`$：第 2 の仮定を $`X' := X`$ に適用すると
  $`X \ne () \mathbin{+\!\!+} X`$、すなわち $`X \ne X`$ が得られ、$`=`$ の反射性に矛盾する。
  よって前件が偽であり $`\Phi(())`$ が成り立つ。

- **帰納段** $`W = w :: W'`$：帰納法の仮定は $`\Phi(W')`$ である。
  $`X`$, $`Y`$ を取り、$`X \preceq_{\mathrm{lex}} (w :: W') \mathbin{+\!\!+} Y`$ と
  $`\forall X',\ X \ne (w :: W') \mathbin{+\!\!+} X'`$ を仮定し、$`Y'`$ を取る。
  $`X`$ の形で場合分けする。

  **(a) $`X = ()`$ のとき。**
  $`(w :: W') \mathbin{+\!\!+} Y' = w :: (W' \mathbin{+\!\!+} Y')`$ は空列でない。
  $`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式により
  $`() \prec_{\mathrm{lex}} L`$ は $`L \ne ()`$ と同一の命題であるから、結論が成り立つ。

  **(b) $`X = x :: X''`$ のとき。**
  仮定は $`x :: X'' \preceq_{\mathrm{lex}} w :: (W' \mathbin{+\!\!+} Y)`$ である。
  $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）より、これは等号の場合と
  $`\prec_{\mathrm{lex}}`$ の場合に分かれる。

  等号の場合、$`X = w :: (W' \mathbin{+\!\!+} Y) = (w :: W') \mathbin{+\!\!+} Y`$ となり、
  第 2 の仮定を $`X' := Y`$ に適用したものに矛盾する。

  $`x :: X'' \prec_{\mathrm{lex}} w :: (W' \mathbin{+\!\!+} Y)`$ の場合、
  $`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式により次のいずれかが成り立つ。

  - [$`x \prec_{\mathrm{p}} w`$](Seqlex.md#d-pairlt) のとき。
    示すべきは $`x :: X'' \prec_{\mathrm{lex}} w :: (W' \mathbin{+\!\!+} Y')`$ であり、
    D.seqlex の第 3 式の右辺の第 1 選言がいまの仮定そのものである。
  - $`x = w`$ かつ $`X'' \prec_{\mathrm{lex}} W' \mathbin{+\!\!+} Y`$ のとき。
    まず $`X'' \preceq_{\mathrm{lex}} W' \mathbin{+\!\!+} Y`$ である（D.sle の第 2 選言）。
    次に、任意の $`Z`$ について $`X'' \ne W' \mathbin{+\!\!+} Z`$ である。実際
    $`X'' = W' \mathbin{+\!\!+} Z`$ とすると、$`x = w`$ より
    $`X = x :: X'' = w :: (W' \mathbin{+\!\!+} Z) = (w :: W') \mathbin{+\!\!+} Z`$ となり、
    第 2 の仮定を $`X' := Z`$ に適用したものに矛盾する。
    よって帰納法の仮定 $`\Phi(W')`$ を $`X := X''`$, $`Y := Y`$, $`Y' := Y'`$ に適用でき、
    $`X'' \prec_{\mathrm{lex}} W' \mathbin{+\!\!+} Y'`$ を得る。
    $`x = w`$ と合わせて D.seqlex の第 3 式の右辺の第 2 選言が成り立つ。∎

<a id="t-peel_aux"></a>
## 定理: 自己言及的な上界の剥がし (T.peel_aux)

### 定理

$`d, w, n, a \in \mathbb{N}`$、$`X, Q, A_2 \in \mathrm{PairSeq}`$ とする。
$`\lvert X\rvert \le n`$ かつ
[$`X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} (a,w) :: \mathrm{shr}_d (X \mathbin{+\!\!+} A_2)`$](Cnf.md#d-shiftr0)
ならば、ある $`m \in \mathbb{N}`$ が存在して
[$`X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} \mathrm{copies}_d\bigl((a,w) :: \mathrm{shr}_d Q,\ m\bigr)`$](Cnf.md#d-copies)。

### 証明

$`n`$ に関する自然数の帰納法（$`X`$, $`Q`$, $`A_2`$, $`a`$ は全称量化したまま動かす）。
帰納法の述語は

```math
\Psi(n) :\equiv \forall X, Q, A_2 \in \mathrm{PairSeq},\ \forall a \in \mathbb{N},\
  \lvert X\rvert \le n
  \ \to\ X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} (a,w) :: \mathrm{shr}_d (X \mathbin{+\!\!+} A_2)
  \ \to\ \exists m,\ X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} \mathrm{copies}_d\bigl((a,w) :: \mathrm{shr}_d Q,\ m\bigr) .
```

- **基底段** $`n = 0`$：$`\lvert X\rvert \le 0`$ より $`X = ()`$ である。
  $`m := 0`$ とすると、$`\mathrm{copies}`$ の定義（D.copies）より
  $`\mathrm{copies}_d(B, 0) = ()`$ であるから、示すべきは
  $`() \preceq_{\mathrm{lex}} Q`$ である。$`Q = ()`$ のときは
  $`() = Q`$ であり、D.sle の第 1 選言が成り立つ。$`Q = q :: Q'`$ のときは
  $`Q \ne ()`$ であり、D.seqlex の第 1 式より $`() \prec_{\mathrm{lex}} Q`$、
  すなわち D.sle の第 2 選言が成り立つ。

- **帰納段** $`n \to n+1`$：帰納法の仮定は $`\Psi(n)`$ である。
  $`X`$, $`Q`$, $`A_2`$, $`a`$ を取り、$`\lvert X\rvert \le n+1`$ と
  $`X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} (a,w) :: \mathrm{shr}_d (X \mathbin{+\!\!+} A_2)`$ を仮定する。
  $`X`$ が $`Q \mathbin{+\!\!+} [(a,w)]`$ を前部分列として持つかどうかで場合分けする。

**(a) ある $`X'`$ について $`X = Q \mathbin{+\!\!+} (a,w) :: X'`$ であるとき。**
仮定の $`X`$ をこの形に書き換えると

```math
Q \mathbin{+\!\!+} (a,w) :: X'
  \ \preceq_{\mathrm{lex}}\
Q \mathbin{+\!\!+} (a,w) :: \mathrm{shr}_d \bigl((Q \mathbin{+\!\!+} (a,w) :: X') \mathbin{+\!\!+} A_2\bigr)
```

である。[T.sle_append_cancel](Cofinality.md#t-sle_append_cancel) を $`Q`$ について、
続いて $`[(a,w)]`$ について適用すると

```math
X' \preceq_{\mathrm{lex}} \mathrm{shr}_d \bigl((Q \mathbin{+\!\!+} (a,w) :: X') \mathbin{+\!\!+} A_2\bigr)
```

を得る。ここで結合則により
$`(Q \mathbin{+\!\!+} (a,w) :: X') \mathbin{+\!\!+} A_2 = Q \mathbin{+\!\!+} (a,w) :: (X' \mathbin{+\!\!+} A_2)`$
であるから、[T.shiftr0_append](Cofinality.md#t-shiftr0_append) と
[T.shiftr0_cons](Cnf.md#t-shiftr0_cons) により

```math
\mathrm{shr}_d \bigl((Q \mathbin{+\!\!+} (a,w) :: X') \mathbin{+\!\!+} A_2\bigr)
  = \mathrm{shr}_d Q \mathbin{+\!\!+} (a+d,\ w) :: \mathrm{shr}_d (X' \mathbin{+\!\!+} A_2)
```

であり、したがって

```math
X' \preceq_{\mathrm{lex}} \mathrm{shr}_d Q \mathbin{+\!\!+} (a+d,\ w) :: \mathrm{shr}_d (X' \mathbin{+\!\!+} A_2) .
```

また $`\lvert X\rvert = \lvert Q\rvert + 1 + \lvert X'\rvert \le n+1`$ から
$`\lvert X'\rvert \le n`$ である。よって帰納法の仮定 $`\Psi(n)`$ を
$`X := X'`$, $`Q := \mathrm{shr}_d Q`$, $`A_2 := A_2`$, $`a := a+d`$ に適用でき、ある $`m`$ について

```math
X' \preceq_{\mathrm{lex}} \mathrm{shr}_d Q \mathbin{+\!\!+}
  \mathrm{copies}_d\bigl((a+d,\ w) :: \mathrm{shr}_d (\mathrm{shr}_d Q),\ m\bigr)
```

が成り立つ。求める $`m`$ として $`m+1`$ を取る。
[T.copies_succ_front](Cnf.md#t-copies_succ_front) により

```math
\mathrm{copies}_d\bigl((a,w) :: \mathrm{shr}_d Q,\ m+1\bigr)
  = \bigl((a,w) :: \mathrm{shr}_d Q\bigr) \mathbin{+\!\!+}
    \mathrm{shr}_d \Bigl(\mathrm{copies}_d\bigl((a,w) :: \mathrm{shr}_d Q,\ m\bigr)\Bigr)
```

であり、[T.shiftr0_copies](Cofinality.md#t-shiftr0_copies) と [T.shiftr0_cons](Cnf.md#t-shiftr0_cons) により

```math
\mathrm{shr}_d \Bigl(\mathrm{copies}_d\bigl((a,w) :: \mathrm{shr}_d Q,\ m\bigr)\Bigr)
  = \mathrm{copies}_d\bigl((a+d,\ w) :: \mathrm{shr}_d(\mathrm{shr}_d Q),\ m\bigr)
```

である。したがって結合則により

```math
Q \mathbin{+\!\!+} \mathrm{copies}_d\bigl((a,w) :: \mathrm{shr}_d Q,\ m+1\bigr)
  = \bigl(Q \mathbin{+\!\!+} [(a,w)]\bigr) \mathbin{+\!\!+}
    \Bigl(\mathrm{shr}_d Q \mathbin{+\!\!+}
      \mathrm{copies}_d\bigl((a+d,\ w) :: \mathrm{shr}_d(\mathrm{shr}_d Q),\ m\bigr)\Bigr)
```

であり、また $`X = Q \mathbin{+\!\!+} (a,w) :: X' = (Q \mathbin{+\!\!+} [(a,w)]) \mathbin{+\!\!+} X'`$ である。
両辺が共通の前部分列 $`Q \mathbin{+\!\!+} [(a,w)]`$ を持つから、
[T.sle_append_cancel](Cofinality.md#t-sle_append_cancel) を逆向きに用いて、上で得た $`X'`$ についての比較から
求める比較が従う。

**(b) どの $`X'`$ についても $`X \ne Q \mathbin{+\!\!+} (a,w) :: X'`$ であるとき。**
$`m := 1`$ を取る。[T.copies_one](Cnf.md#t-copies_one) より
$`\mathrm{copies}_d(B, 1) = B`$ であるから、示すべきは

```math
X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} \bigl((a,w) :: \mathrm{shr}_d Q\bigr)
  = \bigl(Q \mathbin{+\!\!+} [(a,w)]\bigr) \mathbin{+\!\!+} \mathrm{shr}_d Q
```

である。仮定を同じく括り直すと

```math
X \preceq_{\mathrm{lex}} \bigl(Q \mathbin{+\!\!+} [(a,w)]\bigr) \mathbin{+\!\!+} \mathrm{shr}_d (X \mathbin{+\!\!+} A_2)
```

であり、場合の仮定は「任意の $`X'`$ について
$`X \ne (Q \mathbin{+\!\!+} [(a,w)]) \mathbin{+\!\!+} X'`$」と同値である
（$`(Q \mathbin{+\!\!+} [(a,w)]) \mathbin{+\!\!+} X' = Q \mathbin{+\!\!+} (a,w) :: X'`$ だからである）。
よって [T.seqlex_of_sle_not_prefix](#t-seqlex_of_sle_not_prefix) を
$`W := Q \mathbin{+\!\!+} [(a,w)]`$、$`Y := \mathrm{shr}_d (X \mathbin{+\!\!+} A_2)`$、
$`Y' := \mathrm{shr}_d Q`$ に適用して
$`X \prec_{\mathrm{lex}} (Q \mathbin{+\!\!+} [(a,w)]) \mathbin{+\!\!+} \mathrm{shr}_d Q`$ を得る。
D.sle の第 2 選言によりこれが求める比較である。∎

<a id="t-sle_take_of_short"></a>
## 定理: 短い側の比較は前半で決まる (T.sle_take_of_short)

### 定理

$`P, X, Y \in \mathrm{PairSeq}`$ とする。$`X \preceq_{\mathrm{lex}} P \mathbin{+\!\!+} Y`$ かつ
$`\lvert X\rvert \le \lvert P\rvert`$ ならば $`X \preceq_{\mathrm{lex}} P`$。

### 証明

$`P`$ の長さに関する帰納法（$`X`$, $`Y`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Xi(P) :\equiv \forall X, Y \in \mathrm{PairSeq},\
  X \preceq_{\mathrm{lex}} P \mathbin{+\!\!+} Y \to \lvert X\rvert \le \lvert P\rvert
  \to X \preceq_{\mathrm{lex}} P .
```

- **基底段** $`P = ()`$：$`\lvert X\rvert \le 0`$ より $`X = ()`$ であり、
  $`X = P`$ であるから D.sle の第 1 選言が成り立つ。

- **帰納段** $`P = p :: P'`$：帰納法の仮定は $`\Xi(P')`$ である。
  $`X`$, $`Y`$ を取り、$`X \preceq_{\mathrm{lex}} p :: (P' \mathbin{+\!\!+} Y)`$ と
  $`\lvert X\rvert \le \lvert P'\rvert + 1`$ を仮定する。$`X`$ の形で場合分けする。

  **(a) $`X = ()`$ のとき。** $`p :: P'`$ は空列でないから、D.seqlex の第 1 式より
  $`() \prec_{\mathrm{lex}} p :: P'`$ であり、D.sle の第 2 選言が成り立つ。

  **(b) $`X = x :: X''`$ のとき。** 仮定の長さ条件は $`\lvert X''\rvert \le \lvert P'\rvert`$ である。
  $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）により、等号の場合と
  $`\prec_{\mathrm{lex}}`$ の場合に分かれる。

  等号 $`x :: X'' = p :: (P' \mathbin{+\!\!+} Y)`$ の場合、対の列の先頭と後続を比べて
  $`x = p`$ および $`X'' = P' \mathbin{+\!\!+} Y`$ を得る。
  長さを取ると $`\lvert X''\rvert = \lvert P'\rvert + \lvert Y\rvert`$ であり、
  $`\lvert X''\rvert \le \lvert P'\rvert`$ と合わせて $`\lvert Y\rvert = 0`$、すなわち $`Y = ()`$ である。
  よって $`X'' = P'`$ となり $`X = p :: P' = P`$、D.sle の第 1 選言が成り立つ。

  $`x :: X'' \prec_{\mathrm{lex}} p :: (P' \mathbin{+\!\!+} Y)`$ の場合、D.seqlex の第 3 式により
  次のいずれかである。

  - $`x \prec_{\mathrm{p}} p`$ のとき。D.seqlex の第 3 式の右辺の第 1 選言により
    $`x :: X'' \prec_{\mathrm{lex}} p :: P'`$ であり、D.sle の第 2 選言が成り立つ。
  - $`x = p`$ かつ $`X'' \prec_{\mathrm{lex}} P' \mathbin{+\!\!+} Y`$ のとき。
    D.sle の第 2 選言より $`X'' \preceq_{\mathrm{lex}} P' \mathbin{+\!\!+} Y`$ であり、
    $`\lvert X''\rvert \le \lvert P'\rvert`$ であるから帰納法の仮定 $`\Xi(P')`$ が適用でき、
    $`X'' \preceq_{\mathrm{lex}} P'`$ を得る。これがさらに 2 つに分かれる。
    $`X'' = P'`$ ならば $`X = p :: P' = P`$ で D.sle の第 1 選言。
    $`X'' \prec_{\mathrm{lex}} P'`$ ならば、$`x = p`$ と合わせて D.seqlex の第 3 式の
    右辺の第 2 選言により $`x :: X'' \prec_{\mathrm{lex}} p :: P'`$ であり、
    D.sle の第 2 選言が成り立つ。∎

<a id="t-sle_trans"></a>
## 定理: 広義比較の推移律 (T.sle_trans)

### 定理

$`A \preceq_{\mathrm{lex}} B`$ かつ $`B \preceq_{\mathrm{lex}} C`$ ならば $`A \preceq_{\mathrm{lex}} C`$。

### 証明

$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）により、$`A \preceq_{\mathrm{lex}} B`$ は
$`A = B`$ か $`A \prec_{\mathrm{lex}} B`$ である。

- $`A = B`$ のとき。$`B`$ を $`A`$ に書き換えれば第 2 の仮定そのものである。
- $`A \prec_{\mathrm{lex}} B`$ のとき。
  [T.seqlex_sle_trans](Cofinality.md#t-seqlex_sle_trans) を
  $`A \prec_{\mathrm{lex}} B`$ と $`B \preceq_{\mathrm{lex}} C`$ に適用して
  $`A \prec_{\mathrm{lex}} C`$ を得る。D.sle の第 2 選言によりこれが結論である。∎

<a id="t-sle_of_append_left"></a>
## 定理: 小さい側の右切り詰め (T.sle_of_append_left)

### 定理

$`X \mathbin{+\!\!+} Y \preceq_{\mathrm{lex}} W`$ ならば $`X \preceq_{\mathrm{lex}} W`$。

### 証明

まず $`X \preceq_{\mathrm{lex}} X \mathbin{+\!\!+} Y`$ を示す。$`Y`$ の形で場合分けする。

- $`Y = ()`$ のとき。$`X \mathbin{+\!\!+} () = X`$ であるから D.sle の第 1 選言が成り立つ。
- $`Y = y :: Y'`$ のとき。$`Y \ne ()`$ であるから
  [T.seqlex_prefix](Seqlex.md#t-seqlex_prefix) より
  $`X \prec_{\mathrm{lex}} X \mathbin{+\!\!+} Y`$ であり、D.sle の第 2 選言が成り立つ。

得られた $`X \preceq_{\mathrm{lex}} X \mathbin{+\!\!+} Y`$ と仮定
$`X \mathbin{+\!\!+} Y \preceq_{\mathrm{lex}} W`$ に [T.sle_trans](#t-sle_trans) を適用すればよい。∎

<a id="t-shiftr0_injective"></a>
## 定理: 行 0 の右シフトは単射 (T.shiftr0_injective)

### 定理

$`d \in \mathbb{N}`$ とする。$`\mathrm{shr}_d X = \mathrm{shr}_d Y`$ ならば $`X = Y`$。

### 証明

以下、対 $`p \in \mathbb{N} \times \mathbb{N}`$ の第 1 成分を $`p_1`$、第 2 成分を $`p_2`$ と書く。

写像 $`f : p \mapsto (p_1 + d,\ p_2)`$ が単射であることを示す。$`f(p) = f(q)`$ とすると、
対の成分を比べて $`p_1 + d = q_1 + d`$ かつ $`p_2 = q_2`$ である。
前者から $`p_1 = q_1`$ が従うので $`p = q`$ である。

$`\mathrm{shr}_d`$ の定義（D.shiftr0）は $`f`$ による各要素の写像であり、
単射な写像による列の各要素の写像は列について単射である。すなわち
$`\mathrm{shr}_d X = \mathrm{shr}_d Y`$ から $`X = Y`$ が従う。∎

<a id="t-seqlex_shiftr0"></a>
## 定理: 行 0 の右シフトは狭義比較を保つ (T.seqlex_shiftr0)

### 定理

$`d \in \mathbb{N}`$ とする。任意の $`X, Y \in \mathrm{PairSeq}`$ について

```math
\mathrm{shr}_d X \prec_{\mathrm{lex}} \mathrm{shr}_d Y \iff X \prec_{\mathrm{lex}} Y .
```

### 証明

$`X`$ の長さに関する帰納法（$`Y`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Theta(X) :\equiv \forall Y \in \mathrm{PairSeq},\
  \bigl(\mathrm{shr}_d X \prec_{\mathrm{lex}} \mathrm{shr}_d Y \iff X \prec_{\mathrm{lex}} Y\bigr).
```

- **基底段** $`X = ()`$：$`\mathrm{shr}_d () = ()`$ である。$`Y`$ の形で場合分けする。
  $`Y = ()`$ のときは $`\mathrm{shr}_d Y = ()`$ であり、D.seqlex の第 1 式により
  両辺とも $`() \ne ()`$、すなわちともに偽である。
  $`Y = y :: Y'`$ のときは $`\mathrm{shr}_d Y = (y_1+d,\ y_2) :: \mathrm{shr}_d Y'`$ であり、
  D.seqlex の第 1 式により両辺とも空列でない列についての条件であり、ともに真である。

- **帰納段** $`X = x :: X'`$：帰納法の仮定は $`\Theta(X')`$ である。$`Y`$ の形で場合分けする。

  **(a) $`Y = ()`$ のとき。** $`\mathrm{shr}_d Y = ()`$、
  $`\mathrm{shr}_d X = (x_1+d,\ x_2) :: \mathrm{shr}_d X'`$ であり、
  D.seqlex の第 2 式により両辺とも偽である。

  **(b) $`Y = y :: Y'`$ のとき。** [T.shiftr0_cons](Cnf.md#t-shiftr0_cons) により

```math
\mathrm{shr}_d X = (x_1+d,\ x_2) :: \mathrm{shr}_d X', \qquad
\mathrm{shr}_d Y = (y_1+d,\ y_2) :: \mathrm{shr}_d Y'
```

  である。D.seqlex の第 3 式を両辺に適用すると、示すべきことは

```math
\Bigl((x_1+d,\ x_2) \prec_{\mathrm{p}} (y_1+d,\ y_2)
  \ \vee\ \bigl((x_1+d,\ x_2) = (y_1+d,\ y_2) \wedge \mathrm{shr}_d X' \prec_{\mathrm{lex}} \mathrm{shr}_d Y'\bigr)\Bigr)
\iff
\Bigl(x \prec_{\mathrm{p}} y \ \vee\ (x = y \wedge X' \prec_{\mathrm{lex}} Y')\Bigr)
```

  である。帰納法の仮定 $`\Theta(X')`$ を $`Y := Y'`$ に適用すると
  $`\mathrm{shr}_d X' \prec_{\mathrm{lex}} \mathrm{shr}_d Y' \iff X' \prec_{\mathrm{lex}} Y'`$
  であるから、残るのは次の 2 点である。

  第 1 に、$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）より

```math
(x_1+d,\ x_2) \prec_{\mathrm{p}} (y_1+d,\ y_2)
  \iff x_1 + d \lt y_1 + d \ \vee\ (x_1 + d = y_1 + d \wedge x_2 \lt y_2)
```

  であり、$`x_1 + d \lt y_1 + d \iff x_1 \lt y_1`$ および
  $`x_1 + d = y_1 + d \iff x_1 = y_1`$ であるから、右辺は
  $`x_1 \lt y_1 \vee (x_1 = y_1 \wedge x_2 \lt y_2)`$、すなわち $`x \prec_{\mathrm{p}} y`$ と同値である。

  第 2 に、$`(x_1+d,\ x_2) = (y_1+d,\ y_2)`$ は
  $`x_1 + d = y_1 + d`$ かつ $`x_2 = y_2`$ と同値であり、
  $`x_1 + d = y_1 + d \iff x_1 = y_1`$ であるから $`x = y`$ と同値である。

  以上により両辺の 2 つの選言が対応し、同値が成り立つ。∎

<a id="t-sle_shiftr0"></a>
## 定理: 行 0 の右シフトは広義比較を保つ (T.sle_shiftr0)

### 定理

$`d \in \mathbb{N}`$ とする。任意の $`X, Y \in \mathrm{PairSeq}`$ について

```math
\mathrm{shr}_d X \preceq_{\mathrm{lex}} \mathrm{shr}_d Y \iff X \preceq_{\mathrm{lex}} Y .
```

### 証明

$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）により、示すべきことは

```math
\bigl(\mathrm{shr}_d X = \mathrm{shr}_d Y \vee \mathrm{shr}_d X \prec_{\mathrm{lex}} \mathrm{shr}_d Y\bigr)
\iff \bigl(X = Y \vee X \prec_{\mathrm{lex}} Y\bigr)
```

である。第 2 選言どうしは [T.seqlex_shiftr0](#t-seqlex_shiftr0) により同値であるから、
第 1 選言どうしが対応することを見ればよい。

- 左から右：$`\mathrm{shr}_d X = \mathrm{shr}_d Y`$ ならば
  [T.shiftr0_injective](#t-shiftr0_injective) より $`X = Y`$。
- 右から左：$`X = Y`$ ならば、両辺に $`\mathrm{shr}_d`$ を施して
  $`\mathrm{shr}_d X = \mathrm{shr}_d Y`$。∎

<a id="d-SpineOK"></a>
## 定義: 右可視列の行 1 の下界 (D.SpineOK)

$`A \in \mathrm{PairSeq}`$、$`L, w \in \mathbb{N}`$ に対し

```math
\mathrm{SpineOK}(A, L, w) :\iff
\forall U, V \in \mathrm{PairSeq},\ \forall x \in \mathbb{N} \times \mathbb{N},\
\Bigl(A = U \mathbin{+\!\!+} x :: V \ \wedge\ x_1 \lt L
  \ \wedge\ \bigl(\forall y \in V,\ x_1 \lt y_1\bigr)\Bigr)
\ \longrightarrow\ w \le x_2 .
```

すなわち、$`A`$ の列 $`x`$ であって行 0 の値が $`L`$ より小さく、かつ $`A`$ の中で $`x`$ より
後ろのどの列も行 0 の値が $`x_1`$ より大きいもの（これを $`x`$ が**右可視**であるという）は、
すべて行 1 の値が $`w`$ 以上である、という条件である。

<a id="d-ArgDomCore"></a>
## 定義: 引数支配の中核 (D.ArgDomCore)

以下、$`L \in \mathrm{PairSeq}`$ に対し $`\mathrm{hd}\,L`$ を $`L`$ の先頭要素とする
（$`L = ()`$ のときは $`\mathrm{hd}\,L := (0,0)`$ とする）。

命題 $`\mathrm{ArgDomCore}`$ を次で定める。すなわち、任意の
$`X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$ と $`u, w, e \in \mathbb{N}`$ について、
次の 8 条件がすべて成り立つならば結論 (9) が成り立つ、という命題である。

1. [$`\bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z \in \mathrm{ST\_PS}`$](Pss.md#d-ST_PS)
2. $`0 \lt e`$
3. $`\forall x \in A_1,\ u \lt x_1`$
4. $`\forall x \in B,\ u + e \lt x_1`$
5. $`\forall x \in A_2,\ u \lt x_1`$
6. $`A_2 = () \ \vee\ (\mathrm{hd}\,A_2)_1 \le u + e`$
7. $`Z = () \ \vee\ (\mathrm{hd}\,Z)_1 \le u`$
8. $`\mathrm{SpineOK}(A_1,\ u+e,\ w)`$
9. $`B \preceq_{\mathrm{lex}} \mathrm{shr}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)`$

<a id="t-spineOK_of_nextrel1"></a>
## 定理: 行 1 の親子関係から SpineOK を得る (T.spineOK_of_nextrel1)

### 定理

$`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$ とし、

```math
\ell := (v_0 + d_0,\ w_0 + 1), \qquad
M := \bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} (\ell), \qquad
j := \bigl\lvert G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr\rvert
```

とおく。[$`\lvert G\rvert \to^M_1 j`$](Pss.md#d-nextrel1) ならば
$`\mathrm{SpineOK}(R,\ v_0 + d_0,\ w_0)`$。

### 証明

$`\to^M_1`$ の定義（D.nextrel1）の 6 条件のうち、条件 (5)

```math
\lvert G\rvert \le^M_0 j
```

と条件 (6)

```math
\forall j'\ \bigl(\lvert G\rvert \lt j' \ \wedge\ j' \le^M_0 j \ \to\ M_{1,j} \le M_{1,j'}\bigr)
```

を用いる（[$`\le^M_0`$](Pss.md#d-le0)、[$`M_{i,j}`$](Pss.md#d-entry)）。

$`\mathrm{SpineOK}`$ の定義（D.SpineOK）にしたがい、$`U, V \in \mathrm{PairSeq}`$ と
$`x \in \mathbb{N}\times\mathbb{N}`$ を取り

```math
R = U \mathbin{+\!\!+} x :: V, \qquad x_1 \lt v_0 + d_0, \qquad \forall y \in V,\ x_1 \lt y_1
```

を仮定して $`w_0 \le x_2`$ を示す。$`A := G \mathbin{+\!\!+} ((v_0,w_0) :: U)`$ とおくと、
$`R`$ の分解を代入して

```math
M = A \mathbin{+\!\!+} \bigl(x :: (V \mathbin{+\!\!+} (\ell))\bigr), \qquad
\lvert A\rvert = \lvert G\rvert + 1 + \lvert U\rvert, \qquad
j = \lvert A\rvert + 1 + \lvert V\rvert
```

である。[T.getD_append_right'](Cofinality.md#t-getD_append_right') を
$`A`$ と $`x :: (V \mathbin{+\!\!+} (\ell))`$、添字 $`0`$ に適用すると

```math
M\langle \lvert A\rvert \rangle = x
```

であり、同じ補題を添字 $`t+1`$ に適用すると

```math
M\bigl\langle \lvert A\rvert + (t+1) \bigr\rangle = (V \mathbin{+\!\!+} (\ell))\langle t \rangle
```

である。また $`j = \lvert G \mathbin{+\!\!+} ((v_0,w_0) :: R)\rvert`$ は $`M`$ における $`\ell`$ の位置であり、
同じ補題を $`G \mathbin{+\!\!+} ((v_0,w_0) :: R)`$ と $`(\ell)`$、添字 $`0`$ に適用して
$`M\langle j\rangle = \ell`$ を得る。

**行 0 の値についての中間評価。** 任意の $`y`$ について
$`\lvert A\rvert \lt y`$ かつ $`y \le j`$ ならば $`M_{0,\lvert A\rvert} \lt M_{0,y}`$ であることを示す。
$`\lvert A\rvert \lt y`$ より $`y = \lvert A\rvert + (t+1)`$ と書ける。
$`y \le j = \lvert A\rvert + 1 + \lvert V\rvert`$ より $`t \le \lvert V\rvert`$ である。
[T.entry_zero](Cofinality.md#t-entry_zero) より
$`M_{0,\lvert A\rvert} = x_1`$、$`M_{0,y} = \bigl((V \mathbin{+\!\!+} (\ell))\langle t\rangle\bigr)_1`$ である。

- $`t \lt \lvert V\rvert`$ のとき。$`(V \mathbin{+\!\!+} (\ell))\langle t\rangle = V\langle t\rangle`$ であり、
  これは $`V`$ の要素である。仮定 $`\forall y \in V,\ x_1 \lt y_1`$ より
  $`x_1 \lt \bigl(V\langle t\rangle\bigr)_1`$。
- $`t = \lvert V\rvert`$ のとき。$`(V \mathbin{+\!\!+} (\ell))\langle \lvert V\rvert\rangle = \ell`$ であり、
  $`\ell_1 = v_0 + d_0`$ であるから、仮定 $`x_1 \lt v_0 + d_0`$ より $`x_1 \lt \ell_1`$。

**行 0 の祖先関係の持ち上げ。** $`\lvert G\rvert \lt \lvert A\rvert`$ かつ
$`\lvert A\rvert \le j`$ であり、いま示した中間評価が成り立つので、
条件 (5) に [T.le0_through_pivot](Column.md#t-le0_through_pivot) を適用して

```math
\lvert A\rvert \le^M_0 j
```

を得る。

**行 1 の最小性からの結論。** [T.entry_one](Cofinality.md#t-entry_one) と
$`M\langle j\rangle = \ell`$ より $`M_{1,j} = \ell_2 = w_0 + 1`$ であり、
$`M\langle \lvert A\rvert\rangle = x`$ より $`M_{1,\lvert A\rvert} = x_2`$ である。
条件 (6) を $`j' := \lvert A\rvert`$ に適用すると、
$`\lvert G\rvert \lt \lvert A\rvert`$ と $`\lvert A\rvert \le^M_0 j`$ から

```math
w_0 + 1 = M_{1,j} \le M_{1,\lvert A\rvert} = x_2
```

が従う。とくに $`w_0 \le x_2`$ である。∎

<a id="t-ascArgDom_of_core"></a>
## 定理: 中核から昇順引数支配へ (T.ascArgDom_of_core)

### 定理

$`\mathrm{ArgDomCore}`$ が成り立つならば
[$`\mathrm{AscArgDom}`$](Cofinality.md#d-AscArgDom) が成り立つ。

### 証明

以下、$`a \in \mathbb{N}`$ と $`L \in \mathrm{PairSeq}`$ に対し、$`\mathrm{tw}_a L`$ を
$`L`$ の先頭から第 1 成分が $`a`$ より大きい要素が続く極大な前部分列、
$`\mathrm{dw}_a L`$ をその残りの列とする。すなわち
$`\mathrm{tw}_a L \mathbin{+\!\!+} \mathrm{dw}_a L = L`$ であり、$`\mathrm{tw}_a L`$ の各要素 $`x`$ は
$`a \lt x_1`$ をみたし、$`\mathrm{dw}_a L \ne ()`$ ならば
$`\neg\bigl(a \lt (\mathrm{hd}(\mathrm{dw}_a L))_1\bigr)`$ である。

$`\mathrm{AscArgDom}`$ の定義（D.AscArgDom）にしたがい、
$`G, R, S \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$ を取り、次を仮定する。

```math
\bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr) \in \mathrm{ST\_PS},
```
```math
\bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS},
```
```math
\forall x \in R,\ v_0 \lt x_1, \qquad 0 \lt d_0, \qquad
\lvert G\rvert \to^{M}_1 \bigl\lvert G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr\rvert
```

ここで $`M := (G \mathbin{+\!\!+} ((v_0,w_0) :: R)) \mathbin{+\!\!+} ((v_0+d_0,\ w_0+1))`$ である。
示すべきは、ある $`m`$ について

```math
\mathrm{tw}_{v_0+d_0} S \ \preceq_{\mathrm{lex}}\
  \mathrm{shr}_{d_0}\Bigl(R \mathbin{+\!\!+} \mathrm{copies}_{d_0}\bigl(\mathrm{shr}_{d_0}((v_0,w_0) :: R),\ m\bigr)\Bigr)
```

が成り立つことである。

**列の分割。** $`S_{\mathrm{hi}} := \mathrm{tw}_{v_0+d_0} S`$、
$`D := \mathrm{dw}_{v_0+d_0} S`$、$`A_2 := \mathrm{tw}_{v_0} D`$、$`Z := \mathrm{dw}_{v_0} D`$ とおく。
$`\mathrm{tw}`$ と $`\mathrm{dw}`$ の定義より
$`S_{\mathrm{hi}} \mathbin{+\!\!+} D = S`$ および $`A_2 \mathbin{+\!\!+} Z = D`$ である。
さらに次の 5 つが成り立つ。

**(i) $`\forall x \in S_{\mathrm{hi}},\ v_0 + d_0 \lt x_1`$。**
$`\mathrm{tw}_{v_0+d_0} S`$ の要素は述語「第 1 成分が $`v_0+d_0`$ より大きい」をみたすからである。

**(ii) $`\forall x \in A_2,\ v_0 \lt x_1`$。** 同様に $`\mathrm{tw}_{v_0} D`$ の要素は
述語「第 1 成分が $`v_0`$ より大きい」をみたすからである。

**(iii) $`D = () \ \vee\ (\mathrm{hd}\,D)_1 \le v_0 + d_0`$。**
$`D = \mathrm{dw}_{v_0+d_0} S`$ が空でなければ、その先頭は述語をみたさない最初の要素であり、
$`\neg(v_0 + d_0 \lt (\mathrm{hd}\,D)_1)`$、すなわち $`(\mathrm{hd}\,D)_1 \le v_0 + d_0`$ である。

**(iv) $`A_2 = () \ \vee\ (\mathrm{hd}\,A_2)_1 \le v_0 + d_0`$。**
$`A_2 \ne ()`$ とする。$`A_2 = \mathrm{tw}_{v_0} D`$ が空でないので $`D \ne ()`$ であり、
$`\mathrm{tw}_{v_0} D`$ は $`D`$ の先頭から取った前部分列で空でないから
$`\mathrm{hd}\,A_2 = \mathrm{hd}\,D`$ である。(iii) の第 1 選言は $`D \ne ()`$ により偽であるから
第 2 選言が成り立ち、$`(\mathrm{hd}\,A_2)_1 = (\mathrm{hd}\,D)_1 \le v_0 + d_0`$。

**(v) $`Z = () \ \vee\ (\mathrm{hd}\,Z)_1 \le v_0`$。**
$`Z = \mathrm{dw}_{v_0} D`$ が空でなければ、その先頭は述語
「第 1 成分が $`v_0`$ より大きい」をみたさないから $`(\mathrm{hd}\,Z)_1 \le v_0`$ である。

**中核の適用。** $`S = S_{\mathrm{hi}} \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)`$ を代入し、結合則で括り直すと

```math
\bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S
 = \Bigl(G \mathbin{+\!\!+} (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: (S_{\mathrm{hi}} \mathbin{+\!\!+} A_2)\bigr)\Bigr) \mathbin{+\!\!+} Z
```

である。$`\mathrm{ArgDomCore}`$ を
$`X := G`$, $`A_1 := R`$, $`B := S_{\mathrm{hi}}`$, $`A_2 := A_2`$, $`Z := Z`$,
$`u := v_0`$, $`w := w_0`$, $`e := d_0`$ に適用する。
D.ArgDomCore の 8 条件は次のように与えられる。

- 条件 (1)：いま書き換えた第 2 の $`\mathrm{ST\_PS}`$ の仮定そのものである。
- 条件 (2)：仮定 $`0 \lt d_0`$。
- 条件 (3)：仮定 $`\forall x \in R,\ v_0 \lt x_1`$。
- 条件 (4)：(i)。
- 条件 (5)：(ii)。
- 条件 (6)：(iv)。
- 条件 (7)：(v)。
- 条件 (8)：$`\mathrm{SpineOK}(R,\ v_0+d_0,\ w_0)`$ であり、
  [T.spineOK_of_nextrel1](#t-spineOK_of_nextrel1) を第 5 の仮定に適用して得られる。

よって結論 (9)

```math
S_{\mathrm{hi}} \preceq_{\mathrm{lex}}
  \mathrm{shr}_{d_0}\bigl(R \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: (S_{\mathrm{hi}} \mathbin{+\!\!+} A_2)\bigr)
```

を得る。[T.shiftr0_append](Cofinality.md#t-shiftr0_append) と [T.shiftr0_cons](Cnf.md#t-shiftr0_cons) により右辺は

```math
\mathrm{shr}_{d_0} R \mathbin{+\!\!+} (v_0+d_0+d_0,\ w_0) :: \mathrm{shr}_{d_0}(S_{\mathrm{hi}} \mathbin{+\!\!+} A_2)
```

に等しい。

**コピー塔への展開。** [T.peel_aux](#t-peel_aux) を
$`d := d_0`$, $`w := w_0`$, $`n := \lvert S_{\mathrm{hi}}\rvert`$,
$`X := S_{\mathrm{hi}}`$, $`Q := \mathrm{shr}_{d_0} R`$, $`A_2 := A_2`$,
$`a := v_0+d_0+d_0`$ に適用する。長さの条件
$`\lvert S_{\mathrm{hi}}\rvert \le \lvert S_{\mathrm{hi}}\rvert`$ は $`\le`$ の反射性で成り立つ。
よってある $`m`$ について

```math
S_{\mathrm{hi}} \preceq_{\mathrm{lex}}
  \mathrm{shr}_{d_0} R \mathbin{+\!\!+}
  \mathrm{copies}_{d_0}\bigl((v_0+d_0+d_0,\ w_0) :: \mathrm{shr}_{d_0}(\mathrm{shr}_{d_0} R),\ m\bigr)
```

が成り立つ。この $`m`$ が求めるものである。実際、[T.shiftr0_append](Cofinality.md#t-shiftr0_append)、[T.shiftr0_copies](Cofinality.md#t-shiftr0_copies)、
[T.shiftr0_cons](Cnf.md#t-shiftr0_cons) により

```math
\begin{aligned}
\mathrm{shr}_{d_0}\Bigl(R \mathbin{+\!\!+} \mathrm{copies}_{d_0}\bigl(\mathrm{shr}_{d_0}((v_0,w_0) :: R),\ m\bigr)\Bigr)
&= \mathrm{shr}_{d_0} R \mathbin{+\!\!+}
   \mathrm{copies}_{d_0}\bigl(\mathrm{shr}_{d_0}(\mathrm{shr}_{d_0}((v_0,w_0) :: R)),\ m\bigr) \cr
&= \mathrm{shr}_{d_0} R \mathbin{+\!\!+}
   \mathrm{copies}_{d_0}\bigl((v_0+d_0+d_0,\ w_0) :: \mathrm{shr}_{d_0}(\mathrm{shr}_{d_0} R),\ m\bigr)
\end{aligned}
```

であり、いま得た比較の右辺と一致する。∎

<a id="t-pss_cofinality_of_core"></a>
## 定理: 中核から PSS の共終性へ (T.pss_cofinality_of_core)

### 定理

$`\mathrm{ArgDomCore}`$ が成り立つとする。$`M, N \in \mathrm{ST\_PS}`$ であり
[$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$](Term.md#d-translate) ならば、ある $`n`$ が存在して
$`1 \le n`$ かつ [$`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$](Pss.md#d-oper)。

### 証明

[T.ascArgDom_of_core](#t-ascArgDom_of_core) を仮定 $`\mathrm{ArgDomCore}`$ に適用して
$`\mathrm{AscArgDom}`$ を得る。これと、仮定 $`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ を
[T.pss_cofinality_of_argdom](Cofinality.md#t-pss_cofinality_of_argdom) に与えると、
$`1 \le n`$ かつ $`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$ をみたす $`n`$ が得られる。∎

<a id="d-ArgDomCoreOn"></a>
## 定義: 中核の列ごとの形 (D.ArgDomCoreOn)

$`N \in \mathrm{PairSeq}`$ に対し、命題 $`\mathrm{ArgDomCoreOn}(N)`$ を次で定める。
すなわち、任意の $`X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$ と $`u, w, e \in \mathbb{N}`$ について、
次の 8 条件がすべて成り立つならば結論 (9) が成り立つ、という命題である。

1. $`N = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z`$
2. $`0 \lt e`$
3. $`\forall x \in A_1,\ u \lt x_1`$
4. $`\forall x \in B,\ u + e \lt x_1`$
5. $`\forall x \in A_2,\ u \lt x_1`$
6. $`A_2 = () \ \vee\ (\mathrm{hd}\,A_2)_1 \le u + e`$
7. $`Z = () \ \vee\ (\mathrm{hd}\,Z)_1 \le u`$
8. $`\mathrm{SpineOK}(A_1,\ u+e,\ w)`$
9. $`B \preceq_{\mathrm{lex}} \mathrm{shr}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)`$

<a id="t-argDomCore_of_on"></a>
## 定理: 列ごとの形から中核へ (T.argDomCore_of_on)

### 定理

任意の $`N \in \mathrm{PairSeq}`$ について
$`N \in \mathrm{ST\_PS} \to \mathrm{ArgDomCoreOn}(N)`$ が成り立つならば、
$`\mathrm{ArgDomCore}`$ が成り立つ。

### 証明

D.ArgDomCore にしたがい $`X, A_1, B, A_2, Z`$ と $`u, w, e`$ を取り、条件 (1) から (8) を仮定する。

```math
N := \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z
```

とおくと、条件 (1) は $`N \in \mathrm{ST\_PS}`$ である。仮定をこの $`N`$ に適用して
$`\mathrm{ArgDomCoreOn}(N)`$ を得る。

$`\mathrm{ArgDomCoreOn}(N)`$ を同じ $`X, A_1, B, A_2, Z, u, w, e`$ に適用する。
D.ArgDomCoreOn の条件 (1) は $`N = N`$ であり、$`=`$ の反射性で成り立つ。
条件 (2) から (8) は D.ArgDomCore の条件 (2) から (8) と同一である。
よって結論 (9) が得られ、これは D.ArgDomCore の結論 (9) と同一である。∎

<a id="t-argdom_pos"></a>
## 定理: 印付き 2 列の位置 (T.argdom_pos)

### 定理

$`N = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z`$
ならば

```math
N\bigl\langle \lvert X\rvert \bigr\rangle = (u,w), \qquad
N\bigl\langle \lvert X\rvert + (\lvert A_1\rvert + 1) \bigr\rangle = (u+e,\ w), \qquad
\lvert X\rvert + (\lvert A_1\rvert + 1) \lt \lvert N\rvert .
```

### 証明

結合則により $`N`$ は

```math
N = X \mathbin{+\!\!+} \Bigl((u,w) :: \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: ((B \mathbin{+\!\!+} A_2) \mathbin{+\!\!+} Z)\bigr)\Bigr)
```

と書ける。$`T := A_1 \mathbin{+\!\!+} (u+e,w) :: ((B \mathbin{+\!\!+} A_2) \mathbin{+\!\!+} Z)`$ とおく。

**第 1 の主張。** [T.getD_append_right'](Cofinality.md#t-getD_append_right') を $`X`$ と $`(u,w) :: T`$、添字 $`0`$ に適用すると

```math
N\bigl\langle \lvert X\rvert + 0 \bigr\rangle = \bigl((u,w) :: T\bigr)\langle 0\rangle = (u,w) .
```

**第 2 の主張。** 同じ補題を $`X`$ と $`(u,w) :: T`$、添字 $`\lvert A_1\rvert + 1`$ に適用すると

```math
N\bigl\langle \lvert X\rvert + (\lvert A_1\rvert + 1) \bigr\rangle
  = \bigl((u,w) :: T\bigr)\bigl\langle \lvert A_1\rvert + 1 \bigr\rangle
  = T\bigl\langle \lvert A_1\rvert \bigr\rangle
```

であり、さらに同じ補題を $`A_1`$ と $`(u+e,w) :: ((B \mathbin{+\!\!+} A_2) \mathbin{+\!\!+} Z)`$、添字 $`0`$ に
適用して $`T\langle \lvert A_1\rvert \rangle = (u+e,\ w)`$ を得る。

**第 3 の主張。** 上の分解から

```math
\lvert N\rvert = \lvert X\rvert + 1 + \bigl(\lvert A_1\rvert + 1
  + (\lvert B\rvert + \lvert A_2\rvert + \lvert Z\rvert)\bigr)
```

であり、これは $`\lvert X\rvert + \lvert A_1\rvert + 2`$ 以上であるから
$`\lvert X\rvert + (\lvert A_1\rvert + 1) \lt \lvert N\rvert`$ である。∎

<a id="t-argDomCoreOn_diag"></a>
## 定理: 対角列における中核 (T.argDomCoreOn_diag)

### 定理

任意の $`v \in \mathbb{N}`$ について
[$`\mathrm{ArgDomCoreOn}(\Delta_0^v)`$](Pss.md#d-diagSeq)。

### 証明

D.ArgDomCoreOn にしたがい $`X, A_1, B, A_2, Z`$ と $`u, w, e`$ を取り、
条件 (1) から (8) を仮定する。条件 (1) を [T.argdom_pos](#t-argdom_pos) に適用すると

```math
\Delta_0^v\bigl\langle \lvert X\rvert \bigr\rangle = (u,w), \qquad
\Delta_0^v\bigl\langle \lvert X\rvert + (\lvert A_1\rvert + 1) \bigr\rangle = (u+e,\ w), \qquad
\lvert X\rvert + (\lvert A_1\rvert + 1) \lt \bigl\lvert \Delta_0^v \bigr\rvert
```

を得る。[T.diagSeq0_length](Column.md#t-diagSeq0_length) より
$`\lvert \Delta_0^v\rvert = v + 1`$ であるから

```math
\lvert X\rvert \le \lvert X\rvert + (\lvert A_1\rvert + 1) \lt v + 1
```

であり、[T.diagSeq0_getD](Column.md#t-diagSeq0_getD) を添字 $`\lvert X\rvert`$ と
$`\lvert X\rvert + (\lvert A_1\rvert + 1)`$ に適用できて

```math
\Delta_0^v\bigl\langle \lvert X\rvert \bigr\rangle = \bigl(\lvert X\rvert,\ \lvert X\rvert\bigr),
\qquad
\Delta_0^v\bigl\langle \lvert X\rvert + (\lvert A_1\rvert + 1) \bigr\rangle
  = \bigl(\lvert X\rvert + (\lvert A_1\rvert + 1),\ \lvert X\rvert + (\lvert A_1\rvert + 1)\bigr)
```

である。第 1 の等式の第 2 成分を比べて $`\lvert X\rvert = w`$、
第 2 の等式の第 2 成分を比べて $`\lvert X\rvert + (\lvert A_1\rvert + 1) = w`$ である。
両者から $`\lvert A_1\rvert + 1 = 0`$ となるが、$`\lvert A_1\rvert + 1 \ge 1`$ であるから矛盾する。

よって条件 (1) から (8) をみたす分解は存在せず、結論 (9) が空虚に成り立つ。∎

<a id="t-argDomCoreOn_snoc_zero"></a>
## 定理: 行 0 が 0 の末尾列の除去 (T.argDomCoreOn_snoc_zero)

### 定理

$`N \in \mathrm{PairSeq}`$、$`p \in \mathbb{N}\times\mathbb{N}`$ とし $`p_1 = 0`$ とする。
$`\mathrm{ArgDomCoreOn}(N \mathbin{+\!\!+} (p))`$ ならば $`\mathrm{ArgDomCoreOn}(N)`$。

### 証明

D.ArgDomCoreOn にしたがい $`X, A_1, B, A_2, Z`$ と $`u, w, e`$ を取り、
$`N`$ についての条件 (1) から (8) を仮定する。
仮定 $`\mathrm{ArgDomCoreOn}(N \mathbin{+\!\!+} (p))`$ を、同じ
$`X, A_1, B, A_2, u, w, e`$ と $`Z := Z \mathbin{+\!\!+} (p)`$ に適用する。

- 条件 (1)：$`N`$ についての条件 (1) の両辺に $`(p)`$ を右から連結し、結合則で括り直すと

```math
N \mathbin{+\!\!+} (p)
  = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr)
    \mathbin{+\!\!+} \bigl(Z \mathbin{+\!\!+} (p)\bigr)
```

  である。
- 条件 (2) から (6)、および条件 (8)：$`N`$ についてのものと同一である。
- 条件 (7)：$`Z \mathbin{+\!\!+} (p) = () \vee (\mathrm{hd}(Z \mathbin{+\!\!+} (p)))_1 \le u`$ を示す。
  $`Z = ()`$ のときは $`Z \mathbin{+\!\!+} (p) = (p)`$ であり、
  $`(\mathrm{hd}(p))_1 = p_1 = 0 \le u`$ であるから第 2 選言が成り立つ。
  $`Z = z :: Z'`$ のときは $`\mathrm{hd}(Z \mathbin{+\!\!+} (p)) = \mathrm{hd}\,Z`$ であり、
  $`N`$ についての条件 (7) の第 1 選言 $`Z = ()`$ は偽であるから第 2 選言
  $`(\mathrm{hd}\,Z)_1 \le u`$ が成り立ち、これが求めるものである。

よって結論 (9)

```math
B \preceq_{\mathrm{lex}} \mathrm{shr}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)
```

が得られる。これは $`N`$ についての結論 (9) と同一である。∎

<a id="t-argDomCoreOn_drop_left"></a>
## 定理: 左側の列は見えない (T.argDomCoreOn_drop_left)

### 定理

$`P, S \in \mathrm{PairSeq}`$ とする。$`\mathrm{ArgDomCoreOn}(P \mathbin{+\!\!+} S)`$ ならば
$`\mathrm{ArgDomCoreOn}(S)`$。

### 証明

D.ArgDomCoreOn にしたがい $`X, A_1, B, A_2, Z`$ と $`u, w, e`$ を取り、
$`S`$ についての条件 (1) から (8) を仮定する。
仮定 $`\mathrm{ArgDomCoreOn}(P \mathbin{+\!\!+} S)`$ を、$`X := P \mathbin{+\!\!+} X`$ と
同じ $`A_1, B, A_2, Z, u, w, e`$ に適用する。

条件 (1) は、$`S`$ についての条件 (1) の両辺に左から $`P`$ を連結し、結合則で括り直した

```math
P \mathbin{+\!\!+} S
  = \bigl((P \mathbin{+\!\!+} X) \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z
```

である。条件 (2) から (8) は $`X`$ を含まないから、$`S`$ についてのものと同一である。
よって結論 (9) が得られ、これも $`X`$ を含まないから $`S`$ についての結論 (9) と同一である。∎

<a id="d-shiftl0"></a>
## 定義: 行 0 の左シフト (D.shiftl0)

$`d \in \mathbb{N}`$ と $`L \in \mathrm{PairSeq}`$ に対し、$`\mathrm{shl}_d L`$ を
$`L`$ の各要素 $`p`$ を $`(p_1 - d,\ p_2)`$ に置き換えた列と定める。

```math
\mathrm{shl}_d\bigl(L_0, \dots, L_{\lvert L\rvert - 1}\bigr)
  := \Bigl((L_0)_1 - d,\ (L_0)_2\Bigr), \dots,
     \Bigl((L_{\lvert L\rvert - 1})_1 - d,\ (L_{\lvert L\rvert - 1})_2\Bigr)
```

ここで $`-`$ は自然数の切り捨て減法である。

<a id="t-shiftl0_cons"></a>
## 定理: 左シフトと先頭 (T.shiftl0_cons)

### 定理

$`d \in \mathbb{N}`$、$`p \in \mathbb{N}\times\mathbb{N}`$、$`A \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{shl}_d (p :: A) = (p_1 - d,\ p_2) :: \mathrm{shl}_d A .
```

### 証明

$`\mathrm{shl}_d`$ の定義（D.shiftl0）は各要素への写像であり、
先頭要素の像が $`(p_1-d,\ p_2)`$、残りの像が $`\mathrm{shl}_d A`$ であるから、
両辺は定義により同一の列である。∎

<a id="t-shiftl0_append"></a>
## 定理: 左シフトと連結 (T.shiftl0_append)

### 定理

$`d \in \mathbb{N}`$、$`A, B \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{shl}_d (A \mathbin{+\!\!+} B) = \mathrm{shl}_d A \mathbin{+\!\!+} \mathrm{shl}_d B .
```

### 証明

各要素への写像は連結と可換である。すなわち $`A \mathbin{+\!\!+} B`$ の各要素の像を並べた列は、
$`A`$ の各要素の像を並べた列と $`B`$ の各要素の像を並べた列の連結である。∎

<a id="t-mem_shiftl0"></a>
## 定理: 左シフトの要素 (T.mem_shiftl0)

### 定理

$`d \in \mathbb{N}`$、$`M \in \mathrm{PairSeq}`$、$`x \in \mathbb{N}\times\mathbb{N}`$ に対し

```math
x \in \mathrm{shl}_d M \iff \exists p \in M,\ (p_1 - d,\ p_2) = x .
```

### 証明

$`\mathrm{shl}_d M`$ は $`M`$ の各要素 $`p`$ を $`(p_1-d,\ p_2)`$ に置き換えた列であるから
（D.shiftl0）、その要素であることは、$`M`$ のある要素 $`p`$ の像であることと同値である。∎

<a id="t-shiftl0_shiftr0"></a>
## 定理: 左シフトは右シフトの左逆 (T.shiftl0_shiftr0)

### 定理

$`d \in \mathbb{N}`$、$`X \in \mathrm{PairSeq}`$ に対し
$`\mathrm{shl}_d (\mathrm{shr}_d X) = X`$。

### 証明

$`X`$ の長さに関する帰納法。帰納法の述語は

```math
\Lambda(X) :\equiv \mathrm{shl}_d (\mathrm{shr}_d X) = X .
```

- **基底段** $`X = ()`$：$`\mathrm{shr}_d () = ()`$、$`\mathrm{shl}_d () = ()`$ であるから
  両辺は $`()`$ である。

- **帰納段** $`X = p :: X'`$：帰納法の仮定は $`\Lambda(X')`$、すなわち
  $`\mathrm{shl}_d (\mathrm{shr}_d X') = X'`$ である。[T.shiftr0_cons](Cnf.md#t-shiftr0_cons) と
  [T.shiftl0_cons](#t-shiftl0_cons) により

```math
\mathrm{shl}_d \bigl(\mathrm{shr}_d (p :: X')\bigr)
  = \mathrm{shl}_d \bigl((p_1 + d,\ p_2) :: \mathrm{shr}_d X'\bigr)
  = \bigl((p_1 + d) - d,\ p_2\bigr) :: \mathrm{shl}_d (\mathrm{shr}_d X')
```

  である。$`(p_1 + d) - d = p_1`$ であり、帰納法の仮定より
  $`\mathrm{shl}_d (\mathrm{shr}_d X') = X'`$ であるから、右辺は
  $`(p_1,\ p_2) :: X' = p :: X'`$ に等しい。∎

<a id="t-shiftr0_shiftl0"></a>
## 定理: 行 0 が $`d`$ 以上なら右シフトは左シフトの逆 (T.shiftr0_shiftl0)

### 定理

$`d \in \mathbb{N}`$、$`L \in \mathrm{PairSeq}`$ とし、$`\forall x \in L,\ d \le x_1`$ とする。
このとき $`\mathrm{shr}_d (\mathrm{shl}_d L) = L`$。

### 証明

$`L`$ の長さに関する帰納法。帰納法の述語は

```math
\Upsilon(L) :\equiv
  \bigl(\forall x \in L,\ d \le x_1\bigr) \to \mathrm{shr}_d (\mathrm{shl}_d L) = L .
```

- **基底段** $`L = ()`$：$`\mathrm{shl}_d () = ()`$、$`\mathrm{shr}_d () = ()`$ であるから
  両辺は $`()`$ である。

- **帰納段** $`L = p :: L'`$：帰納法の仮定は $`\Upsilon(L')`$ である。
  仮定 $`\forall x \in p :: L',\ d \le x_1`$ から、$`p`$ を取って $`d \le p_1`$ が、
  $`L'`$ の各要素を取って $`\forall x \in L',\ d \le x_1`$ が従う。
  後者に帰納法の仮定 $`\Upsilon(L')`$ を適用して
  $`\mathrm{shr}_d (\mathrm{shl}_d L') = L'`$ を得る。
  [T.shiftl0_cons](#t-shiftl0_cons) と [T.shiftr0_cons](Cnf.md#t-shiftr0_cons) により

```math
\mathrm{shr}_d \bigl(\mathrm{shl}_d (p :: L')\bigr)
  = \mathrm{shr}_d \bigl((p_1 - d,\ p_2) :: \mathrm{shl}_d L'\bigr)
  = \bigl((p_1 - d) + d,\ p_2\bigr) :: \mathrm{shr}_d (\mathrm{shl}_d L')
```

  である。$`d \le p_1`$ であるから切り捨て減法について $`(p_1 - d) + d = p_1`$ であり、
  また $`\mathrm{shr}_d (\mathrm{shl}_d L') = L'`$ であるから、右辺は
  $`(p_1,\ p_2) :: L' = p :: L'`$ に等しい。∎

<a id="t-shiftr0_comm"></a>
## 定理: 右シフトどうしの可換性 (T.shiftr0_comm)

### 定理

$`d, e \in \mathbb{N}`$、$`L \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{shr}_e (\mathrm{shr}_d L) = \mathrm{shr}_d (\mathrm{shr}_e L) .
```

### 証明

$`\mathrm{shr}`$ の定義（D.shiftr0）より、左辺は $`L`$ の各要素 $`p`$ を
$`\bigl((p_1 + d) + e,\ p_2\bigr)`$ に置き換えた列であり、右辺は各要素 $`p`$ を
$`\bigl((p_1 + e) + d,\ p_2\bigr)`$ に置き換えた列である。
自然数の加法の結合律と交換律より $`(p_1 + d) + e = (p_1 + e) + d`$ であるから、
2 つの写像は各 $`p`$ について同じ値を取り、したがって両辺の列は等しい。∎

<a id="t-argDomCoreOn_shiftr0"></a>
## 定理: 中核は一様な右シフトと可換 (T.argDomCoreOn_shiftr0)

### 定理

$`W \in \mathrm{PairSeq}`$、$`d \in \mathbb{N}`$ とする。$`\mathrm{ArgDomCoreOn}(W)`$ ならば
$`\mathrm{ArgDomCoreOn}(\mathrm{shr}_d W)`$。

### 証明

D.ArgDomCoreOn にしたがい $`X, A_1, B, A_2, Z`$ と $`u, w, e`$ を取り、
$`\mathrm{shr}_d W`$ についての条件 (1) から (8) を仮定する。すなわち

```math
\mathrm{shr}_d W
  = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z
```

であり、$`0 \lt e`$、$`\forall x \in A_1,\ u \lt x_1`$、$`\forall x \in B,\ u+e \lt x_1`$、
$`\forall x \in A_2,\ u \lt x_1`$、$`A_2 = () \vee (\mathrm{hd}\,A_2)_1 \le u+e`$、
$`Z = () \vee (\mathrm{hd}\,Z)_1 \le u`$、$`\mathrm{SpineOK}(A_1,\ u+e,\ w)`$ が成り立つ。

**すべての列の行 0 は $`d`$ 以上である。** 条件 (1) の右辺の任意の要素 $`x`$ は
$`\mathrm{shr}_d W`$ の要素であるから、[T.mem_shiftr0](Cnf.md#t-mem_shiftr0) により
$`W`$ のある要素 $`q`$ について $`x = (q_1 + d,\ q_2)`$ であり、$`d \le x_1`$ である。
$`X`$, $`A_1`$, $`B`$, $`A_2`$, $`Z`$ の各要素と列 $`(u,w)`$ はいずれも右辺の要素であるから、

```math
\forall x \in X,\ d \le x_1, \quad
\forall x \in A_1,\ d \le x_1, \quad
\forall x \in B,\ d \le x_1, \quad
\forall x \in A_2,\ d \le x_1, \quad
\forall x \in Z,\ d \le x_1, \quad
d \le u
```

が成り立つ。

**分解をシフトの手前へ引き戻す。**

```math
X' := \mathrm{shl}_d X, \quad A_1' := \mathrm{shl}_d A_1, \quad B' := \mathrm{shl}_d B, \quad
A_2' := \mathrm{shl}_d A_2, \quad Z' := \mathrm{shl}_d Z
```

とおく。いま示した行 0 の下界と [T.shiftr0_shiftl0](#t-shiftr0_shiftl0) により

```math
\mathrm{shr}_d X' = X, \quad \mathrm{shr}_d A_1' = A_1, \quad \mathrm{shr}_d B' = B, \quad
\mathrm{shr}_d A_2' = A_2, \quad \mathrm{shr}_d Z' = Z
```

である。条件 (1) の両辺に $`\mathrm{shl}_d`$ を施すと、左辺は
[T.shiftl0_shiftr0](#t-shiftl0_shiftr0) により $`W`$ であり、右辺は
[T.shiftl0_append](#t-shiftl0_append) と [T.shiftl0_cons](#t-shiftl0_cons) により

```math
W = \bigl(X' \mathbin{+\!\!+} (u-d,\ w) :: (A_1' \mathbin{+\!\!+} (u+e-d,\ w) :: (B' \mathbin{+\!\!+} A_2'))\bigr) \mathbin{+\!\!+} Z'
```

となる。$`d \le u`$ であるから切り捨て減法について $`u + e - d = (u-d) + e`$ であり、

```math
W = \bigl(X' \mathbin{+\!\!+} (u-d,\ w) :: (A_1' \mathbin{+\!\!+} ((u-d)+e,\ w) :: (B' \mathbin{+\!\!+} A_2'))\bigr) \mathbin{+\!\!+} Z'
```

と書ける。これが $`W`$ についての条件 (1) である。

**残りの条件の引き戻し。** 以下、$`u' := u - d`$ と書く。$`d \le u`$ である。

**(2)** $`0 \lt e`$ は仮定そのものである。

**(3)** $`\forall x \in A_1',\ u' \lt x_1`$。$`x \in A_1'`$ とすると
[T.mem_shiftl0](#t-mem_shiftl0) により $`A_1`$ のある要素 $`q`$ について
$`x = (q_1 - d,\ q_2)`$ である。$`u \lt q_1`$ かつ $`d \le q_1`$ かつ $`d \le u`$ であるから、
切り捨て減法について $`u - d \lt q_1 - d`$、すなわち $`u' \lt x_1`$ である。

**(4)** $`\forall x \in B',\ u' + e \lt x_1`$。同様に $`B`$ のある要素 $`q`$ について
$`x = (q_1 - d,\ q_2)`$ であり、$`u + e \lt q_1`$、$`d \le q_1`$、$`d \le u`$ から
$`u' + e = u + e - d \lt q_1 - d = x_1`$ である。

**(5)** $`\forall x \in A_2',\ u' \lt x_1`$。同様に $`A_2`$ のある要素 $`q`$ について
$`x = (q_1 - d,\ q_2)`$ であり、$`u \lt q_1`$、$`d \le q_1`$、$`d \le u`$ から
$`u' \lt x_1`$ である。

**(6)** $`A_2' = () \vee (\mathrm{hd}\,A_2')_1 \le u' + e`$。
$`A_2 = ()`$ のときは $`A_2' = \mathrm{shl}_d () = ()`$ であり第 1 選言が成り立つ。
$`A_2 = a :: A_2''`$ のときは、条件 (6) の第 1 選言が偽であるから
$`(\mathrm{hd}\,A_2)_1 = a_1 \le u + e`$ である。また $`d \le a_1`$ である。
[T.shiftl0_cons](#t-shiftl0_cons) より $`\mathrm{hd}\,A_2' = (a_1 - d,\ a_2)`$ であり、
$`d \le u`$ と合わせて $`a_1 - d \le u + e - d = u' + e`$ である。

**(7)** $`Z' = () \vee (\mathrm{hd}\,Z')_1 \le u'`$。
$`Z = ()`$ のときは $`Z' = ()`$ であり第 1 選言が成り立つ。
$`Z = z :: Z''`$ のときは、条件 (7) の第 1 選言が偽であるから
$`(\mathrm{hd}\,Z)_1 = z_1 \le u`$ である。[T.shiftl0_cons](#t-shiftl0_cons) より
$`\mathrm{hd}\,Z' = (z_1 - d,\ z_2)`$ であり、$`z_1 - d \le u - d = u'`$ である。

**(8)** $`\mathrm{SpineOK}(A_1',\ u' + e,\ w)`$。D.SpineOK にしたがい
$`U', V' \in \mathrm{PairSeq}`$ と $`x' \in \mathbb{N}\times\mathbb{N}`$ を取り、

```math
A_1' = U' \mathbin{+\!\!+} x' :: V', \qquad x'_1 \lt u' + e, \qquad \forall y \in V',\ x'_1 \lt y_1
```

を仮定して $`w \le x'_2`$ を示す。この分解の両辺に $`\mathrm{shr}_d`$ を施すと、
左辺は $`\mathrm{shr}_d A_1' = A_1`$ であり、右辺は [T.shiftr0_append](Cofinality.md#t-shiftr0_append) と [T.shiftr0_cons](Cnf.md#t-shiftr0_cons) により

```math
A_1 = \mathrm{shr}_d U' \mathbin{+\!\!+} (x'_1 + d,\ x'_2) :: \mathrm{shr}_d V'
```

である。$`\mathrm{SpineOK}(A_1,\ u+e,\ w)`$ を
$`U := \mathrm{shr}_d U'`$、$`V := \mathrm{shr}_d V'`$、$`x := (x'_1 + d,\ x'_2)`$ に適用する。
その 3 条件は次のようにみたされる。

- 分解式は上で得たものである。
- $`x'_1 + d \lt u + e`$：$`x'_1 \lt u' + e = u + e - d`$ と $`d \le u \le u + e`$ から従う。
- $`\forall y \in \mathrm{shr}_d V',\ x'_1 + d \lt y_1`$：[T.mem_shiftr0](Cnf.md#t-mem_shiftr0) により
  $`V'`$ のある要素 $`q`$ について $`y = (q_1 + d,\ q_2)`$ であり、
  仮定より $`x'_1 \lt q_1`$ であるから $`x'_1 + d \lt q_1 + d = y_1`$ である。

よって $`w \le \bigl((x'_1 + d,\ x'_2)\bigr)_2 = x'_2`$ が得られる。

**中核の適用と結論の押し上げ。** 仮定 $`\mathrm{ArgDomCoreOn}(W)`$ を
$`X := X'`$, $`A_1 := A_1'`$, $`B := B'`$, $`A_2 := A_2'`$, $`Z := Z'`$,
$`u := u'`$、およびもとの $`w`$, $`e`$ に適用すると、結論 (9)

```math
B' \preceq_{\mathrm{lex}} \mathrm{shr}_e\bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)
```

を得る。ここで [T.shiftr0_comm](#t-shiftr0_comm) と
$`\mathrm{shr}_d A_1' = A_1`$、$`\mathrm{shr}_d B' = B`$、$`\mathrm{shr}_d A_2' = A_2`$、
および $`(u'+e)+d = u+e`$（$`d \le u`$ による）を用いると

```math
\begin{aligned}
\mathrm{shr}_d\Bigl(\mathrm{shr}_e\bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)\Bigr)
&= \mathrm{shr}_e\Bigl(\mathrm{shr}_d\bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)\Bigr) \cr
&= \mathrm{shr}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,\ w) :: (B \mathbin{+\!\!+} A_2)\bigr)
\end{aligned}
```

である。したがって示すべき結論 (9)

```math
B \preceq_{\mathrm{lex}} \mathrm{shr}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,\ w) :: (B \mathbin{+\!\!+} A_2)\bigr)
```

は、$`B = \mathrm{shr}_d B'`$ を代入すると

```math
\mathrm{shr}_d B' \preceq_{\mathrm{lex}}
  \mathrm{shr}_d\Bigl(\mathrm{shr}_e\bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)\Bigr)
```

と同じ主張である。[T.sle_shiftr0](#t-sle_shiftr0) の右から左により、
これは上で得た結論 (9) から従う。∎

<a id="t-split_prefix_left"></a>
## 定理: 短い左因子による分割 (T.split_prefix_left)

### 定理

$`C, D, E, F \in \mathrm{PairSeq}`$ が

```math
C \mathbin{+\!\!+} D = E \mathbin{+\!\!+} F, \qquad \lvert E\rvert \le \lvert C\rvert
```

をみたすならば

```math
C = E \mathbin{+\!\!+} \mathrm{drop}_{\lvert E\rvert} C
\qquad\text{かつ}\qquad
F = \mathrm{drop}_{\lvert E\rvert} C \mathbin{+\!\!+} D .
```

ここで $`\mathrm{drop}_k L`$ は $`L`$ の先頭 $`k`$ 要素を落とした列、$`\mathrm{take}_k L`$ は
$`L`$ の先頭 $`k`$ 要素からなる列である（$`k \ge \lvert L\rvert`$ のときはそれぞれ $`()`$ と $`L`$）。

### 証明

$`K := \mathrm{drop}_{\lvert E\rvert} C`$、$`P := \mathrm{take}_{\lvert E\rvert} C`$ とおく。

**第 1 段：仮定を $`P`$ を左因子とする形に書き直す。**
任意の列 $`L`$ と任意の $`k`$ について $`L = \mathrm{take}_k L \mathbin{+\!\!+} \mathrm{drop}_k L`$ が成り立つ。
これを $`L := C`$、$`k := \lvert E\rvert`$ に用いると $`C = P \mathbin{+\!\!+} K`$ である。よって仮定の左辺は
$`(P \mathbin{+\!\!+} K) \mathbin{+\!\!+} D`$ であり、連結の結合律より $`P \mathbin{+\!\!+} (K \mathbin{+\!\!+} D)`$ に等しい。すなわち

```math
P \mathbin{+\!\!+} (K \mathbin{+\!\!+} D) = E \mathbin{+\!\!+} F .
```

**第 2 段：左因子の長さを合わせる。**
$`\lvert \mathrm{take}_k L\rvert = \min(k, \lvert L\rvert)`$ であり、仮定 $`\lvert E\rvert \le \lvert C\rvert`$ より
$`\lvert P\rvert = \min(\lvert E\rvert, \lvert C\rvert) = \lvert E\rvert`$ である。

**第 3 段：連結の分解の一意性。**
2 つの連結 $`s_1 \mathbin{+\!\!+} t_1 = s_2 \mathbin{+\!\!+} t_2`$ が等しく $`\lvert s_1\rvert = \lvert s_2\rvert`$ ならば
$`s_1 = s_2`$ かつ $`t_1 = t_2`$ である。実際、$`i \lt \lvert s_1\rvert`$ なる各 $`i`$ について両辺の
第 $`i`$ 要素はそれぞれ $`s_1`$ の第 $`i`$ 要素と $`s_2`$ の第 $`i`$ 要素であるから
$`s_1 = s_2`$ が従い、次にその共通の左因子を両辺の先頭から取り除けば $`t_1 = t_2`$ が従う。

第 1 段の等式に第 2 段の長さの一致とともにこれを適用して

```math
P = E, \qquad K \mathbin{+\!\!+} D = F
```

を得る。第 1 の等式を第 1 段の $`C = P \mathbin{+\!\!+} K`$ に代入すれば $`C = E \mathbin{+\!\!+} K`$ であり、
第 2 の等式が結論の後半である。∎

<a id="t-split_prefix_right"></a>
## 定理: 長い左因子による分割 (T.split_prefix_right)

### 定理

$`C, D, E, F \in \mathrm{PairSeq}`$ が

```math
C \mathbin{+\!\!+} D = E \mathbin{+\!\!+} F, \qquad \lvert C\rvert \le \lvert E\rvert
```

をみたすならば

```math
E = C \mathbin{+\!\!+} \mathrm{drop}_{\lvert C\rvert} E
\qquad\text{かつ}\qquad
D = \mathrm{drop}_{\lvert C\rvert} E \mathbin{+\!\!+} F .
```

### 証明

仮定の等式の両辺を入れ替えると $`E \mathbin{+\!\!+} F = C \mathbin{+\!\!+} D`$ である。
[T.split_prefix_left](#t-split_prefix_left) をこの等式に、その 4 つの列を
$`(E, F, C, D)`$ の順に対応させて適用する。長さの仮定は $`\lvert C\rvert \le \lvert E\rvert`$ であり、
これは本定理の仮定そのものである。得られる結論は

```math
E = C \mathbin{+\!\!+} \mathrm{drop}_{\lvert C\rvert} E, \qquad
D = \mathrm{drop}_{\lvert C\rvert} E \mathbin{+\!\!+} F
```

であり、これが求めるものである。∎

<a id="t-copies_headI"></a>
## 定理: コピー塔の先頭 (T.copies_headI)

### 定理

$`d \in \mathbb{N}`$、$`\mathrm{blk} \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とする。
$`\mathrm{blk} \ne ()`$ かつ $`1 \le n`$ ならば

```math
\mathrm{head}\bigl(\mathrm{copies}_d(\mathrm{blk}, n)\bigr) = \mathrm{head}\,\mathrm{blk} .
```

ここで $`\mathrm{head}\,L`$ は $`L \ne ()`$ ならばその先頭要素、$`L = ()`$ ならば $`(0,0)`$ である。

### 証明

$`1 \le n`$ より $`n = m + 1`$ なる $`m`$ が取れる。
[T.copies_succ_front](Cnf.md#t-copies_succ_front) より

```math
\mathrm{copies}_d(\mathrm{blk}, m+1)
  = \mathrm{blk} \mathbin{+\!\!+} \bigl(\mathrm{copies}_d(\mathrm{blk}, m)\bigr)^{+d}
```

である。$`\mathrm{blk}`$ の構成子で場合分けする。

- $`\mathrm{blk} = ()`$ のとき。仮定 $`\mathrm{blk} \ne ()`$ に矛盾する。

- $`\mathrm{blk} = b :: \mathrm{blk}'`$ のとき。上の等式の右辺は
  $`b :: \bigl(\mathrm{blk}' \mathbin{+\!\!+} (\mathrm{copies}_d(\mathrm{blk},m))^{+d}\bigr)`$ であり、
  空でないからその先頭要素は $`b`$ である。一方 $`\mathrm{head}\,\mathrm{blk} = b`$ である。∎

<a id="t-argbound_split"></a>
## 定理: 上界の分割 (T.argbound_split)

### 定理

$`e, u, w \in \mathbb{N}`$、$`A_1, B, A_2 \in \mathrm{PairSeq}`$ に対し

```math
\bigl(A_1 \mathbin{+\!\!+} (u+e,\,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
  = \bigl(A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}\bigr) \mathbin{+\!\!+} A_2^{+e} .
```

### 証明

$`L^{+d}`$ は各要素 $`p`$ を $`(p_1 + d,\ p_2)`$ に置き換える写像であるから、
[T.shiftr0_append](Cofinality.md#t-shiftr0_append) より連結を保ち
$`(L \mathbin{+\!\!+} L')^{+d} = L^{+d} \mathbin{+\!\!+} L'^{+d}`$、
[T.shiftr0_cons](Cnf.md#t-shiftr0_cons) より
$`(p :: L)^{+d} = (p_1+d,\ p_2) :: L^{+d}`$ である。これを順に用いると

```math
\begin{aligned}
\bigl(A_1 \mathbin{+\!\!+} (u+e,\,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
&= A_1^{+e} \mathbin{+\!\!+} \bigl((u+e,\,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e} \cr
&= A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: (B \mathbin{+\!\!+} A_2)^{+e} \cr
&= A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: \bigl(B^{+e} \mathbin{+\!\!+} A_2^{+e}\bigr)
\end{aligned}
```

を得る（第 2 成分 $`w`$ は写像で変わらない）。最後に、任意の $`P, Q, S \in \mathrm{PairSeq}`$ と
$`c \in \mathbb{N}\times\mathbb{N}`$ について

```math
P \mathbin{+\!\!+} c :: (Q \mathbin{+\!\!+} S) = P \mathbin{+\!\!+} \bigl((c :: Q) \mathbin{+\!\!+} S\bigr)
  = \bigl(P \mathbin{+\!\!+} c :: Q\bigr) \mathbin{+\!\!+} S
```

が連結の結合律から従う。これを $`P := A_1^{+e}`$、$`c := (u+e+e,\,w)`$、$`Q := B^{+e}`$、
$`S := A_2^{+e}`$ に適用すればよい。∎

<a id="t-argbound_len"></a>
## 定理: 上界の長さ (T.argbound_len)

### 定理

$`e, u, w \in \mathbb{N}`$、$`A_1, B \in \mathrm{PairSeq}`$ に対し

```math
\lvert B\rvert \lt \bigl\lvert A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}\bigr\rvert .
```

### 証明

連結と cons の長さの計算により、右辺は $`\lvert A_1^{+e}\rvert + 1 + \lvert B^{+e}\rvert`$ である。
[T.shiftr0_length](Cofinality.md#t-shiftr0_length) より $`\lvert L^{+d}\rvert = \lvert L\rvert`$ であるから、
これは $`\lvert A_1\rvert + 1 + \lvert B\rvert`$ に等しい。
$`\mathbb{N}`$ において $`\lvert B\rvert \lt \lvert A_1\rvert + 1 + \lvert B\rvert`$ である。∎

<a id="t-argDomCoreOn_bad_A1"></a>
## 定理: 展開の第 4 分岐の場合 A1 (T.argDomCoreOn_bad_A1)

### 定理

$`M, G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0, n \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ とし、
$`\mathrm{blk} := (v_0,w_0) :: R`$ とおく。次を仮定する。

```math
\begin{aligned}
&\text{(hM)}\quad M \in \mathrm{ST\_PS}, \cr
&\text{(hMon)}\quad \mathrm{ArgDomCoreOn}(M), \cr
&\text{(hMeq)}\quad M = G \mathbin{+\!\!+} \mathrm{blk} \mathbin{+\!\!+} (\ell), \cr
&\text{(hRgt)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hlp)}\quad v_0 \lt \ell_1, \cr
&\text{(hdisj)}\quad \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr) \cr
&\qquad\qquad\quad\ \vee\ \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
    \wedge \lvert G\rvert \to^M_1 (\lvert M\rvert - 1)\bigr), \cr
&\text{(hSTn)}\quad \forall m,\ 1 \le m \to G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m) \in \mathrm{ST\_PS}, \cr
&\text{(hIH)}\quad \forall m,\ 1 \le m \to m \lt n \to
    \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr), \cr
&\text{(hn)}\quad 1 \le n .
\end{aligned}
```

さらに $`X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$、$`u, w, e \in \mathbb{N}`$ について次を仮定する。

```math
\begin{aligned}
&\text{(heq)}\quad G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n)
   = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z, \cr
&\text{(he)}\quad 0 \lt e, \cr
&\text{(h1)}\quad \forall x \in A_1,\ u \lt x_1, \cr
&\text{(h2)}\quad \forall x \in B,\ u + e \lt x_1, \cr
&\text{(h3)}\quad \forall x \in A_2,\ u \lt x_1, \cr
&\text{(h4)}\quad A_2 = () \ \vee\ (\mathrm{head}\,A_2)_1 \le u + e, \cr
&\text{(h5)}\quad Z = () \ \vee\ (\mathrm{head}\,Z)_1 \le u, \cr
&\text{(h6)}\quad \mathrm{SpineOK}(A_1,\ u+e,\ w), \cr
&\text{(hcase)}\quad \lvert G\rvert + (\lvert R\rvert + 1) \le \lvert X\rvert .
\end{aligned}
```

このとき

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e} .
```

### 証明

(hn) より $`n = m + 1`$ なる $`m`$ が取れる。以下 $`n`$ をこの形に書く。

**第 1 段：コピー 0 を剥がす。**
[T.copies_succ_front](Cnf.md#t-copies_succ_front) と連結の結合律より

```math
G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1)
 = G \mathbin{+\!\!+} \Bigl(\mathrm{blk} \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}\Bigr)
 = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}
```

である。また (heq) の右辺も結合律で並べ替えられるから

```math
(G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}
 = X \mathbin{+\!\!+} \Bigl(\bigl((u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z\Bigr)
```

が成り立つ。

**第 2 段：境界で切る。**
$`\lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert = \lvert G\rvert + (\lvert R\rvert + 1)`$ であり、(hcase) は
これが $`\lvert X\rvert`$ 以下であることを言う。よって
[T.split_prefix_right](#t-split_prefix_right) を第 1 段の等式に適用できて、
$`X' := \mathrm{drop}_{\lvert G\rvert + (\lvert R\rvert + 1)} X`$ とおくと

```math
X = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} X',
```
```math
\bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}
 = X' \mathbin{+\!\!+} \Bigl(\bigl((u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z\Bigr)
```

を得る。第 2 の等式は結合律により

```math
(\ast)\qquad
\bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}
 = \bigl(X' \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z
```

と書ける。これは $`\mathrm{ArgDomCoreOn}`$ の定義（D.ArgDomCoreOn）が要求する分解の形であり、
$`X`$ を $`X'`$ に置き換えたほかは (heq) と同一である。とくに $`A_1, B, A_2, Z, u, w, e`$ は
変わらないから、(he)、(h1)〜(h6) はそのまま使える。

**第 3 段：$`m`$ で場合分けする。**

**(a) $`m = 0`$ のとき。** [T.copies_zero](Cnf.md#t-copies_zero) より
$`\mathrm{copies}_{d_0}(\mathrm{blk}, 0) = ()`$ であり、
[T.shiftr0_nil](Cnf.md#t-shiftr0_nil) より $`()^{+d_0} = ()`$ である。
よって $`(\ast)`$ の左辺の長さは $`0`$ である。一方その右辺の長さは

```math
\lvert X'\rvert + 1 + \lvert A_1\rvert + 1 + \lvert B\rvert + \lvert A_2\rvert + \lvert Z\rvert
```

であり、$`2`$ 以上である。$`(\ast)`$ は両辺が同じ列であることを言うからその長さも等しく、
$`0 \ge 2`$ が得られる。これは $`\mathbb{N}`$ において偽であるから、この場合は起こらない。

**(b) $`1 \le m`$ のとき。** $`m \lt m + 1 = n`$ であるから (hIH) を $`m`$ に適用して

```math
\mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)
```

を得る。[T.argDomCoreOn_drop_left](#t-argDomCoreOn_drop_left) を $`P := G`$、
$`S := \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$ として適用すると
$`\mathrm{ArgDomCoreOn}(\mathrm{copies}_{d_0}(\mathrm{blk}, m))`$ が得られ、
[T.argDomCoreOn_shiftr0](#t-argDomCoreOn_shiftr0) を $`d := d_0`$ として適用すると

```math
\mathrm{ArgDomCoreOn}\Bigl(\bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}\Bigr)
```

が得られる。これを第 2 段の分解 $`(\ast)`$ と (he)、(h1)、(h2)、(h3)、(h4)、(h5)、(h6) に
適用すれば、D.ArgDomCoreOn の結論そのものとして

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

を得る。∎

<a id="t-arg_split"></a>
## 定理: 水準による列の分割 (T.arg_split)

### 定理

$`L \in \mathbb{N}`$ と $`E \in \mathrm{PairSeq}`$ に対し、$`B_p, R_p \in \mathrm{PairSeq}`$ が存在して

```math
E = B_p \mathbin{+\!\!+} R_p, \qquad
\forall x \in B_p,\ L \lt x_1, \qquad
R_p = () \ \vee\ (\mathrm{head}\,R_p)_1 \le L .
```

### 証明

$`E`$ の構成子に関する帰納法（$`L`$ は固定する）。帰納法の述語は

```math
\Phi(E) :\equiv \exists B_p, R_p \in \mathrm{PairSeq},\
  \Bigl(E = B_p \mathbin{+\!\!+} R_p \wedge (\forall x \in B_p,\ L \lt x_1)
   \wedge \bigl(R_p = () \vee (\mathrm{head}\,R_p)_1 \le L\bigr)\Bigr).
```

- **基底段** $`E = ()`$：$`B_p := ()`$、$`R_p := ()`$ と取る。
  $`() = () \mathbin{+\!\!+} ()`$ である。$`B_p = ()`$ は要素をもたないから第 2 の連言子の前件が偽で成り立つ。
  第 3 の連言子は第 1 選言 $`R_p = ()`$ が成り立つ。

- **帰納段** $`E = a :: E'`$：帰納法の仮定は $`\Phi(E')`$ である。$`L \lt a_1`$ かどうかで場合分けする。

  - $`L \lt a_1`$ のとき。$`\Phi(E')`$ から $`B_p', R_p'`$ を取り、
    $`B_p := a :: B_p'`$、$`R_p := R_p'`$ と置く。
    $`a :: E' = a :: (B_p' \mathbin{+\!\!+} R_p') = (a :: B_p') \mathbin{+\!\!+} R_p'`$ である。
    $`x \in a :: B_p'`$ ならば $`x = a`$ か $`x \in B_p'`$ であり、前者は本場合の仮定 $`L \lt a_1`$、
    後者は $`\Phi(E')`$ の第 2 の連言子により $`L \lt x_1`$。
    第 3 の連言子は $`\Phi(E')`$ のものをそのまま用いる。

  - $`\neg(L \lt a_1)`$ のとき。$`B_p := ()`$、$`R_p := a :: E'`$ と置く。
    $`a :: E' = () \mathbin{+\!\!+} (a :: E')`$ である。$`B_p = ()`$ は要素をもたない。
    $`\mathrm{head}\,R_p = a`$ であり、$`\neg(L \lt a_1)`$ は $`\mathbb{N}`$ において $`a_1 \le L`$ と
    同値であるから第 3 の連言子の第 2 選言が成り立つ。∎

<a id="t-seqlex_of_sle_snoc'"></a>
## 定理: 末尾列の差し替え、上界相対形 (T.seqlex_of_sle_snoc')

### 定理

$`X, V, E \in \mathrm{PairSeq}`$、$`\ell, q \in \mathbb{N}\times\mathbb{N}`$ が

```math
X \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} E,
\qquad q \prec_{\mathrm{pair}} \ell,
\qquad \lvert X\rvert \lt \lvert V\rvert
```

をみたすならば、任意の $`S', E' \in \mathrm{PairSeq}`$ に対し

```math
X \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V \mathbin{+\!\!+} E' .
```

### 証明

$`X`$ の構成子に関する帰納法（$`V, E, \ell, q, S', E'`$ は全称量化したまま動かす）。
帰納法の述語は

```math
\Phi(X) :\equiv \forall V, E, \ell, q,\
  \bigl(X \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} E
   \wedge q \prec_{\mathrm{pair}} \ell \wedge \lvert X\rvert \lt \lvert V\rvert\bigr)
  \to \forall S', E',\ X \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V \mathbin{+\!\!+} E' .
```

**基底段** $`X = ()`$。$`\lvert V\rvert \gt 0`$ であるから $`V = v :: V'`$ と書ける
（$`V = ()`$ なら $`\lvert V\rvert = 0`$ となり $`0 \lt \lvert V\rvert`$ に反する）。
示すべきことは $`q :: S' \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E')`$ であり、
$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式によりその第 1 選言 $`q \prec_{\mathrm{pair}} v`$ を
示せば十分である。仮定は $`(\ell) \preceq_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E)`$ であり、
$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）で場合分けする。

- $`(\ell) = v :: (V' \mathbin{+\!\!+} E)`$ のとき。両辺の先頭要素を比べて $`\ell = v`$ である。
  仮定 $`q \prec_{\mathrm{pair}} \ell`$ がそのまま $`q \prec_{\mathrm{pair}} v`$ を与える。

- $`(\ell) \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E)`$ のとき。$`(\ell) = \ell :: ()`$ であるから
  D.seqlex の第 3 式より、$`\ell \prec_{\mathrm{pair}} v`$ または
  $`\ell = v \wedge () \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$ である。
  前者のときは [T.pairlt_trans](Cofinality.md#t-pairlt_trans) を
  $`q \prec_{\mathrm{pair}} \ell`$ と $`\ell \prec_{\mathrm{pair}} v`$ に適用して $`q \prec_{\mathrm{pair}} v`$。
  後者のときは $`\ell = v`$ を $`q \prec_{\mathrm{pair}} \ell`$ に代入して $`q \prec_{\mathrm{pair}} v`$。

**帰納段** $`X = x :: X'`$。帰納法の仮定は $`\Phi(X')`$ である。
$`\lvert x :: X'\rvert \lt \lvert V\rvert`$ より $`V \ne ()`$ であるから $`V = v :: V'`$ と書け、
このとき $`\lvert X'\rvert + 1 \lt \lvert V'\rvert + 1`$、すなわち $`\lvert X'\rvert \lt \lvert V'\rvert`$ である。
仮定は

```math
x :: \bigl(X' \mathbin{+\!\!+} (\ell)\bigr) \preceq_{\mathrm{lex}} v :: \bigl(V' \mathbin{+\!\!+} E\bigr)
```

であり、示すべきことは
$`x :: (X' \mathbin{+\!\!+} q :: S') \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E')`$、
すなわち D.seqlex の第 3 式により

```math
x \prec_{\mathrm{pair}} v
\quad\text{または}\quad
\bigl(x = v \wedge X' \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E'\bigr)
```

である。仮定を D.sle で場合分けする。

- 等号 $`x :: (X' \mathbin{+\!\!+} (\ell)) = v :: (V' \mathbin{+\!\!+} E)`$ のとき。
  先頭要素を比べて $`x = v`$、残りを比べて $`X' \mathbin{+\!\!+} (\ell) = V' \mathbin{+\!\!+} E`$ である。
  後者は D.sle の第 1 選言により
  $`X' \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$ を与える。
  帰納法の仮定 $`\Phi(X')`$ を $`V', E, \ell, q`$ に適用する（残りの仮定は
  $`q \prec_{\mathrm{pair}} \ell`$ と $`\lvert X'\rvert \lt \lvert V'\rvert`$）と
  $`X' \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E'`$ が得られ、第 2 の選言が成り立つ。

- $`x :: (X' \mathbin{+\!\!+} (\ell)) \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E)`$ のとき。
  D.seqlex の第 3 式より 2 つに分かれる。

  - $`x \prec_{\mathrm{pair}} v`$ のとき。これが第 1 の選言そのものである。
  - $`x = v \wedge X' \mathbin{+\!\!+} (\ell) \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$ のとき。
    後半は D.sle の第 2 選言により
    $`X' \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$ を与えるから、
    前の場合と同じく帰納法の仮定 $`\Phi(X')`$ を適用して第 2 の選言を得る。∎

<a id="t-argDomCoreOn_bad_B"></a>
## 定理: 展開の第 4 分岐の場合 B (T.argDomCoreOn_bad_B)

### 定理

$`M, G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0, n \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、
$`\mathrm{blk} := (v_0,w_0) :: R`$ とし、
[T.argDomCoreOn_bad_A1](#t-argDomCoreOn_bad_A1) の仮定
(hM), (hMon), (hMeq), (hRgt), (hlp), (hdisj), (hSTn), (hIH), (hn) および
$`X, A_1, B, A_2, Z, u, w, e`$ についての (heq), (he), (h1), (h2), (h3), (h4), (h5), (h6) を
そのまま仮定する。さらに

```math
\text{(hcase)}\qquad
\lvert X\rvert + (\lvert A_1\rvert + 1) \lt \lvert G\rvert + (\lvert R\rvert + 1)
```

を仮定する。このとき

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e} .
```

### 証明

(hn) より $`n = m + 1`$ と書く。

```math
T := \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0},
\qquad
C_p := X \mathbin{+\!\!+} (u,w) :: \bigl(A_1 \mathbin{+\!\!+} ((u+e,w))\bigr)
```

とおく。ここで $`\bigl((u+e,w)\bigr)`$ は対 $`(u+e,w)`$ のみからなる長さ $`1`$ の列である。
$`C_p`$ は分解の先頭から深い方の印付き列 $`(u+e,w)`$ までを含む部分であり、
$`\lvert C_p\rvert = \lvert X\rvert + 1 + (\lvert A_1\rvert + 1)`$ である。

**第 1 段：共通部分で切る。**
[T.copies_succ_front](Cnf.md#t-copies_succ_front) と連結の結合律より

```math
G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1) = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} T
```

である。また (heq) の右辺を結合律で並べ替えると

```math
(G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} T
 = C_p \mathbin{+\!\!+} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

を得る。長さは

```math
\lvert C_p\rvert = \lvert X\rvert + \bigl(\lvert A_1\rvert + 1\bigr) + 1,
\qquad
\lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert = \lvert G\rvert + (\lvert R\rvert + 1)
```

である。$`\mathbb{N}`$ において $`a \lt b`$ は $`a + 1 \le b`$ と同値であるから、(hcase) は

```math
\lvert C_p\rvert = \bigl(\lvert X\rvert + (\lvert A_1\rvert + 1)\bigr) + 1
  \le \lvert G\rvert + (\lvert R\rvert + 1) = \lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert
```

を与える。
[T.split_prefix_left](#t-split_prefix_left) を適用して
$`D := \mathrm{drop}_{\lvert C_p\rvert}(G \mathbin{+\!\!+} \mathrm{blk})`$ とおくと

```math
G \mathbin{+\!\!+} \mathrm{blk} = C_p \mathbin{+\!\!+} D,
\qquad
B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} T
```

である。第 1 の等式と (hMeq) を合わせ、結合律により

```math
M = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} (\ell)
  = \bigl(C_p \mathbin{+\!\!+} D\bigr) \mathbin{+\!\!+} (\ell)
  = C_p \mathbin{+\!\!+} \bigl(D \mathbin{+\!\!+} (\ell)\bigr)
```

を得る。すなわちホスト $`M`$ は $`C_p`$ の右に $`D \mathbin{+\!\!+} (\ell)`$ を続けたものである。

**第 2 段（key）：ホストの判定。**
次を示す。$`B', A_2', Z' \in \mathrm{PairSeq}`$ が

```math
D \mathbin{+\!\!+} (\ell) = B' \mathbin{+\!\!+} (A_2' \mathbin{+\!\!+} Z'),
\qquad \forall x \in B',\ u + e \lt x_1,
\qquad \forall x \in A_2',\ u \lt x_1,
```
```math
A_2' = () \ \vee\ (\mathrm{head}\,A_2')_1 \le u+e,
\qquad
Z' = () \ \vee\ (\mathrm{head}\,Z')_1 \le u
```

をみたすならば

```math
B' \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B'^{+e} .
```

実際、第 1 段の $`M = C_p \mathbin{+\!\!+} (D \mathbin{+\!\!+} (\ell))`$ に分解の仮定を代入し、
$`C_p`$ の定義と結合律で並べ替えると

```math
M = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B' \mathbin{+\!\!+} A_2'))\bigr) \mathbin{+\!\!+} Z'
```

である。これは D.ArgDomCoreOn が要求する分解の形であるから、(hMon) をこの分解と
(he)、(h1)、上に挙げた $`B'`$、$`A_2'`$、$`Z'`$ についての 4 条件、(h6) に適用して

```math
B' \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+e}
```

を得る。[T.argbound_split](#t-argbound_split) により右辺は

```math
\bigl(A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B'^{+e}\bigr) \mathbin{+\!\!+} A_2'^{+e}
```

に等しく、[T.argbound_len](#t-argbound_len) により
$`\lvert B'\rvert \le \lvert A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B'^{+e}\rvert`$ である。
[T.sle_take_of_short](#t-sle_take_of_short) を適用して主張を得る。

**第 3 段（goal_of）：結論を同じ形に直す。**

```math
B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}
```

が示せれば結論が従う。実際、[T.argbound_split](#t-argbound_split) により結論の右辺は
$`(A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}) \mathbin{+\!\!+} A_2^{+e}`$ であり、
[T.sle_append_mono](Cofinality.md#t-sle_append_mono) を
$`C := A_2^{+e}`$ として適用すればよい。以下この形を示す。

**第 4 段：$`\lvert B\rvert`$ と $`\lvert D\rvert`$ で場合分けする。**

**(a) $`\lvert B\rvert \lt \lvert D\rvert`$ のとき。**
[T.split_prefix_right](#t-split_prefix_right) を第 1 段の
$`B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} T`$ と $`\lvert B\rvert \le \lvert D\rvert`$ に適用し、
$`D_r := \mathrm{drop}_{\lvert B\rvert} D`$ とおくと

```math
D = B \mathbin{+\!\!+} D_r,
\qquad
A_2 \mathbin{+\!\!+} Z = D_r \mathbin{+\!\!+} T
```

である。

まず $`D_r \ne ()`$ である。$`D_r = ()`$ とすると $`D = B`$ となり
$`\lvert B\rvert \lt \lvert D\rvert = \lvert B\rvert`$ となって矛盾する。
したがって $`A_2 \mathbin{+\!\!+} Z = D_r \mathbin{+\!\!+} T \ne ()`$ であり、
[T.headI_append_left](Seqlex.md#t-headI_append_left) より
$`\mathrm{head}(A_2 \mathbin{+\!\!+} Z) = \mathrm{head}\,D_r`$ である。

次に $`(\mathrm{head}\,D_r)_1 \le u + e`$ を示す。$`A_2`$ が空かどうかで分ける。

- $`A_2 = ()`$ のとき。$`A_2 \mathbin{+\!\!+} Z = Z`$ であり、これは空でないから
  (h5) の第 1 選言 $`Z = ()`$ は偽である。よって第 2 選言により
  $`(\mathrm{head}\,Z)_1 \le u \le u + e`$ であり、
  $`\mathrm{head}\,D_r = \mathrm{head}(A_2 \mathbin{+\!\!+} Z) = \mathrm{head}\,Z`$ である。

- $`A_2 \ne ()`$ のとき。[T.headI_append_left](Seqlex.md#t-headI_append_left) より
  $`\mathrm{head}(A_2 \mathbin{+\!\!+} Z) = \mathrm{head}\,A_2`$ であり、(h4) の第 1 選言は偽であるから
  第 2 選言により $`(\mathrm{head}\,A_2)_1 \le u + e`$ である。

[T.arg_split](#t-arg_split) を $`L := u`$、$`E := D_r \mathbin{+\!\!+} (\ell)`$ に適用して
$`A_2', Z'`$ を取る。すなわち

```math
D_r \mathbin{+\!\!+} (\ell) = A_2' \mathbin{+\!\!+} Z',
\qquad \forall x \in A_2',\ u \lt x_1,
\qquad Z' = () \vee (\mathrm{head}\,Z')_1 \le u .
```

$`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u+e`$ を示す。$`A_2' = ()`$ なら第 1 選言。
$`A_2' \ne ()`$ なら [T.headI_append_left](Seqlex.md#t-headI_append_left) より
$`\mathrm{head}(D_r \mathbin{+\!\!+} (\ell)) = \mathrm{head}\,A_2'`$ であり、
$`D_r \ne ()`$ であるからふたたび同じ定理により
$`\mathrm{head}(D_r \mathbin{+\!\!+} (\ell)) = \mathrm{head}\,D_r`$ である。
よって $`(\mathrm{head}\,A_2')_1 = (\mathrm{head}\,D_r)_1 \le u+e`$。

第 2 段の主張を $`B' := B`$、$`A_2'`$、$`Z'`$ に適用する。分解の条件は

```math
D \mathbin{+\!\!+} (\ell) = (B \mathbin{+\!\!+} D_r) \mathbin{+\!\!+} (\ell)
 = B \mathbin{+\!\!+} \bigl(D_r \mathbin{+\!\!+} (\ell)\bigr)
 = B \mathbin{+\!\!+} \bigl(A_2' \mathbin{+\!\!+} Z'\bigr)
```

であり、$`\forall x \in B,\ u+e \lt x_1`$ は (h2)、残りの 3 条件は上で確かめた。よって

```math
B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}
```

を得る。第 3 段により結論が従う。

**(b) $`\lvert D\rvert \le \lvert B\rvert`$ のとき。**
[T.split_prefix_left](#t-split_prefix_left) を
$`B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} T`$ に適用し、
$`B_2 := \mathrm{drop}_{\lvert D\rvert} B`$ とおくと

```math
B = D \mathbin{+\!\!+} B_2,
\qquad
T = B_2 \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)
```

である。$`D`$ の要素は $`B`$ の要素であるから (h2) より
$`\forall x \in D,\ u+e \lt x_1`$ である。

**第 4 段 (b) の補助 1：$`B_2`$ が空でないときの先頭。**
$`B_2 = q :: B_2'`$ と書けるとき $`q = (v_0+d_0,\ w_0)`$ である。
まず $`m \ne 0`$ である。$`m = 0`$ とすると
[T.copies_zero](Cnf.md#t-copies_zero) と [T.shiftr0_nil](Cnf.md#t-shiftr0_nil) より $`T = ()`$ となるが、
$`T = B_2 \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)`$ の右辺は $`B_2 = q :: B_2'`$ を含むので空でなく、矛盾する。
よって $`m = m' + 1`$ と書ける。
[T.copies_succ_cons](Cnf.md#t-copies_succ_cons) より

```math
\mathrm{copies}_{d_0}(\mathrm{blk}, m'+1)
 = (v_0, w_0) :: \Bigl(R \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m')\bigr)^{+d_0}\Bigr)
```

であり、[T.shiftr0_cons](Cnf.md#t-shiftr0_cons) より

```math
T = (v_0 + d_0,\ w_0) :: \Bigl(R \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m')\bigr)^{+d_0}\Bigr)^{+d_0}
```

である。一方 $`T = B_2 \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = q :: \bigl(B_2' \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)`$
であるから、cons の単射性により $`q = (v_0+d_0,\ w_0)`$ である。

**第 4 段 (b) の補助 2：$`q`$ と $`\ell`$ の比較。**
$`B_2 = q :: B_2'`$ のとき、次の 2 つが成り立つ。

- $`q_1 \le \ell_1`$。(hdisj) の第 1 選言のときは $`d_0 = 0`$ かつ $`\ell_1 = v_0 + 1`$ であり、
  $`q_1 = v_0 + d_0 = v_0 \le v_0 + 1 = \ell_1`$。
  第 2 選言のときは $`\ell_1 = v_0 + d_0 = q_1`$。

- $`q \prec_{\mathrm{pair}} \ell`$。(hdisj) の第 1 選言のときは
  $`q_1 = v_0 \lt v_0 + 1 = \ell_1`$ であり、$`\prec_{\mathrm{pair}}`$ の定義（D.pairlt）の第 1 選言が成り立つ。
  第 2 選言のときは $`q_1 = v_0 + d_0 = \ell_1`$ かつ $`q_2 = w_0 \lt w_0 + 1 = \ell_2`$ であり、
  D.pairlt の第 2 選言が成り立つ。

$`u+e`$ と $`\ell_1`$ で場合分けする。

**(b-1) $`u + e \lt \ell_1`$ のとき。**
$`\forall x \in D \mathbin{+\!\!+} (\ell),\ u+e \lt x_1`$ である
（$`x \in D`$ なら上で示したこと、$`x = \ell`$ なら本場合の仮定による）。
第 2 段の主張を $`B' := D \mathbin{+\!\!+} (\ell)`$、$`A_2' := ()`$、$`Z' := ()`$ に適用する。
分解の条件は $`D \mathbin{+\!\!+} (\ell) = (D \mathbin{+\!\!+} (\ell)) \mathbin{+\!\!+} (() \mathbin{+\!\!+} ())`$、
$`A_2' = ()`$ は要素をもたず頭の条件は第 1 選言、$`Z' = ()`$ も同様である。よって

```math
D \mathbin{+\!\!+} (\ell)
 \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: \bigl(D \mathbin{+\!\!+} (\ell)\bigr)^{+e} .
```

[T.shiftr0_append](Cofinality.md#t-shiftr0_append) と連結の結合律により、
$`V := A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: D^{+e}`$ とおくと右辺は
$`V \mathbin{+\!\!+} (\ell)^{+e}`$ に等しい。すなわち

```math
(\dagger)\qquad D \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} (\ell)^{+e} .
```

なお [T.shiftr0_length](Cofinality.md#t-shiftr0_length) より
$`\lvert V\rvert = \lvert A_1\rvert + 1 + \lvert D\rvert`$ である。$`B_2`$ で場合分けする。

**$`B_2 = ()`$ のとき。** $`B = D \mathbin{+\!\!+} () = D`$ である。
[T.sle_of_append_left](#t-sle_of_append_left) を $`(\dagger)`$ に適用して
$`D \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} (\ell)^{+e}`$ を得る。
$`\lvert D\rvert \le \lvert A_1\rvert + 1 + \lvert D\rvert = \lvert V\rvert`$ であるから、
[T.sle_take_of_short](#t-sle_take_of_short) を適用して $`D \preceq_{\mathrm{lex}} V`$。
$`B = D`$ より、これは
$`B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}`$ そのものである。
第 3 段により結論が従う。

**$`B_2 = q :: B_2'`$ のとき。** $`\lvert D\rvert \lt \lvert A_1\rvert + 1 + \lvert D\rvert = \lvert V\rvert`$ である。
[T.seqlex_of_sle_snoc'](#t-seqlex_of_sle_snoc') を、その主張に現れる列と対に
$`D`$、$`V`$、$`(\ell)^{+e}`$、$`\ell`$、$`q`$ をこの順に対応させて適用する。
3 つの仮定は $`(\dagger)`$、補助 2 の $`q \prec_{\mathrm{pair}} \ell`$、いま示した $`\lvert D\rvert \lt \lvert V\rvert`$ である。
結論の 2 つの全称量化された列を $`B_2'`$ と $`(q_1+e,\ q_2) :: B_2'^{+e}`$ に取ると

```math
D \mathbin{+\!\!+} q :: B_2'
 \prec_{\mathrm{lex}} V \mathbin{+\!\!+} \bigl((q_1+e,\ q_2) :: B_2'^{+e}\bigr)
```

を得る。左辺は $`B = D \mathbin{+\!\!+} B_2 = D \mathbin{+\!\!+} q :: B_2'`$ である。
右辺は [T.shiftr0_append](Cofinality.md#t-shiftr0_append)、
[T.shiftr0_cons](Cnf.md#t-shiftr0_cons) と結合律により

```math
V \mathbin{+\!\!+} \bigl((q_1+e,\ q_2) :: B_2'^{+e}\bigr)
 = A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: \bigl(D^{+e} \mathbin{+\!\!+} (q_1+e,\ q_2) :: B_2'^{+e}\bigr)
 = A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}
```

に等しい。よって $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言により
$`B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}`$ であり、
第 3 段により結論が従う。

**(b-2) $`\neg(u + e \lt \ell_1)`$ のとき。**
まず $`B_2 = ()`$ である。$`B_2 = q :: B_2'`$ とすると、$`q`$ は $`B = D \mathbin{+\!\!+} B_2`$ の要素であるから
(h2) より $`u + e \lt q_1`$ であり、補助 2 より $`q_1 \le \ell_1`$、本場合の仮定より
$`\ell_1 \le u+e`$ であるから $`u+e \lt q_1 \le \ell_1 \le u+e`$ となって矛盾する。
よって $`B = D`$ であり、$`D \mathbin{+\!\!+} (\ell) = B \mathbin{+\!\!+} (\ell)`$ である。
$`u`$ と $`\ell_1`$ でさらに場合分けする。

- $`u \lt \ell_1`$ のとき。第 2 段の主張を $`B' := B`$、$`A_2' := (\ell)`$、$`Z' := ()`$ に適用する。
  分解の条件は $`B \mathbin{+\!\!+} (\ell) = B \mathbin{+\!\!+} ((\ell) \mathbin{+\!\!+} ())`$、
  $`\forall x \in B,\ u+e \lt x_1`$ は (h2)、
  $`\forall x \in (\ell),\ u \lt x_1`$ は本場合の仮定 $`u \lt \ell_1`$、
  $`(\mathrm{head}(\ell))_1 = \ell_1 \le u+e`$ は (b-2) の仮定、
  $`Z' = ()`$ は第 1 選言である。

- $`\neg(u \lt \ell_1)`$、すなわち $`\ell_1 \le u`$ のとき。
  第 2 段の主張を $`B' := B`$、$`A_2' := ()`$、$`Z' := (\ell)`$ に適用する。
  分解の条件は $`B \mathbin{+\!\!+} (\ell) = B \mathbin{+\!\!+} (() \mathbin{+\!\!+} (\ell))`$、
  $`A_2' = ()`$ は要素をもたず頭の条件は第 1 選言、
  $`(\mathrm{head}(\ell))_1 = \ell_1 \le u`$ である。

いずれの場合も
$`B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}`$ が得られ、
第 3 段により結論が従う。∎

<a id="t-shiftr0_add"></a>
## 定理: 平行移動の合成 (T.shiftr0_add)

### 定理

$`a, b \in \mathbb{N}`$、$`X \in \mathrm{PairSeq}`$ に対し

```math
X^{+(a+b)} = \bigl(X^{+b}\bigr)^{+a} .
```

### 証明

$`L^{+d}`$ は各要素 $`p`$ を $`(p_1 + d,\ p_2)`$ に置き換えるものであるから、
左辺は $`X`$ の各要素 $`p`$ を $`(p_1 + (a+b),\ p_2)`$ に置き換えた列であり、
右辺は $`p`$ をまず $`(p_1 + b,\ p_2)`$ に、次に $`((p_1 + b) + a,\ p_2)`$ に置き換えた列である。
$`\mathbb{N}`$ の加法の結合律と交換律により

```math
p_1 + (a+b) = (p_1 + b) + a
```

であるから、2 つの置き換えは各要素で同じ値を与える。要素ごとの置き換えが一致すれば
列全体も一致する。∎

<a id="t-sle_of_prefix"></a>
## 定理: 前部分列は広義に小さい (T.sle_of_prefix)

### 定理

$`X, Y \in \mathrm{PairSeq}`$ とし、$`X \sqsubseteq Y`$ を

```math
X \sqsubseteq Y :\iff \exists t \in \mathrm{PairSeq},\ Y = X \mathbin{+\!\!+} t
```

で定める（$`X`$ は $`Y`$ の**前部分列**である）。$`X \sqsubseteq Y`$ ならば
$`X \preceq_{\mathrm{lex}} Y`$。

### 証明

$`Y = X \mathbin{+\!\!+} t`$ なる $`t`$ を取り、$`t`$ の構成子で場合分けする。

- $`t = ()`$ のとき。$`Y = X \mathbin{+\!\!+} () = X`$ であるから、
  $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 1 選言が成り立つ。

- $`t = a :: t'`$ のとき。$`t \ne ()`$ であるから
  [T.seqlex_prefix](Seqlex.md#t-seqlex_prefix) を $`v := t`$、$`u := X`$ として適用して
  $`X \prec_{\mathrm{lex}} X \mathbin{+\!\!+} t = Y`$ を得る。D.sle の第 2 選言が成り立つ。∎

<a id="t-shiftr0_prefix"></a>
## 定理: 平行移動は前部分列関係を保つ (T.shiftr0_prefix)

### 定理

$`d \in \mathbb{N}`$、$`X, Y \in \mathrm{PairSeq}`$ とする。$`X \sqsubseteq Y`$ ならば
$`X^{+d} \sqsubseteq Y^{+d}`$。

### 証明

$`Y = X \mathbin{+\!\!+} t`$ なる $`t`$ を取る。
[T.shiftr0_append](Cofinality.md#t-shiftr0_append) より

```math
Y^{+d} = \bigl(X \mathbin{+\!\!+} t\bigr)^{+d} = X^{+d} \mathbin{+\!\!+} t^{+d}
```

である。よって $`t^{+d}`$ が $`X^{+d} \sqsubseteq Y^{+d}`$ の証人である。∎

<a id="t-prefix_append_left"></a>
## 定理: 共通の左因子と前部分列 (T.prefix_append_left)

### 定理

$`P, X, Y \in \mathrm{PairSeq}`$ とする。$`X \sqsubseteq Y`$ ならば
$`P \mathbin{+\!\!+} X \sqsubseteq P \mathbin{+\!\!+} Y`$。

### 証明

$`Y = X \mathbin{+\!\!+} t`$ なる $`t`$ を取る。連結の結合律より

```math
P \mathbin{+\!\!+} Y = P \mathbin{+\!\!+} \bigl(X \mathbin{+\!\!+} t\bigr) = \bigl(P \mathbin{+\!\!+} X\bigr) \mathbin{+\!\!+} t
```

である。よって $`t`$ が $`P \mathbin{+\!\!+} X \sqsubseteq P \mathbin{+\!\!+} Y`$ の証人である。∎

<a id="t-copies_length"></a>
## 定理: コピー塔の長さ (T.copies_length)

### 定理

$`d \in \mathbb{N}`$、$`\mathrm{blk} \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ に対し

```math
\bigl\lvert \mathrm{copies}_d(\mathrm{blk}, n)\bigr\rvert = n \cdot \lvert \mathrm{blk}\rvert .
```

### 証明

$`n`$ に関する帰納法（$`d`$, $`\mathrm{blk}`$ は固定する）。帰納法の述語は

```math
\Phi(n) :\equiv \bigl\lvert \mathrm{copies}_d(\mathrm{blk}, n)\bigr\rvert = n \cdot \lvert \mathrm{blk}\rvert .
```

- **基底段** $`n = 0`$：[T.copies_zero](Cnf.md#t-copies_zero) より
  $`\mathrm{copies}_d(\mathrm{blk}, 0) = ()`$ であり、その長さは $`0`$ である。
  一方 $`0 \cdot \lvert \mathrm{blk}\rvert = 0`$ である。

**帰納段** $`n = k + 1`$。帰納法の仮定は $`\Phi(k)`$、すなわち
$`\lvert \mathrm{copies}_d(\mathrm{blk}, k)\rvert = k \cdot \lvert \mathrm{blk}\rvert`$ である。
[T.copies_succ_back](Cofinality.md#t-copies_succ_back) より

```math
\mathrm{copies}_d(\mathrm{blk}, k+1)
 = \mathrm{copies}_d(\mathrm{blk}, k) \mathbin{+\!\!+} \mathrm{blk}^{+k d}
```

であるから、連結の長さは各因子の長さの和であり

```math
\bigl\lvert \mathrm{copies}_d(\mathrm{blk}, k+1)\bigr\rvert
 = \bigl\lvert \mathrm{copies}_d(\mathrm{blk}, k)\bigr\rvert + \bigl\lvert \mathrm{blk}^{+k d}\bigr\rvert .
```

[T.shiftr0_length](Cofinality.md#t-shiftr0_length) より
$`\lvert \mathrm{blk}^{+k d}\rvert = \lvert \mathrm{blk}\rvert`$ であり、帰納法の仮定と合わせて

```math
\bigl\lvert \mathrm{copies}_d(\mathrm{blk}, k+1)\bigr\rvert
 = k \cdot \lvert \mathrm{blk}\rvert + \lvert \mathrm{blk}\rvert = (k+1) \cdot \lvert \mathrm{blk}\rvert
```

を得る。よって $`\Phi(k+1)`$。∎

<a id="t-split_append_left"></a>
## 定理: 分割の存在形 (T.split_append_left)

### 定理

$`C, D, E, F \in \mathrm{PairSeq}`$ が $`C \mathbin{+\!\!+} D = E \mathbin{+\!\!+} F`$ と
$`\lvert E\rvert \le \lvert C\rvert`$ をみたすならば、$`K \in \mathrm{PairSeq}`$ が存在して

```math
C = E \mathbin{+\!\!+} K \qquad\text{かつ}\qquad F = K \mathbin{+\!\!+} D .
```

### 証明

$`K := \mathrm{drop}_{\lvert E\rvert} C`$ と取る。
[T.split_prefix_left](#t-split_prefix_left) の 2 つの結論が求める 2 つの等式そのものである。∎

<a id="t-prefix_cons_append"></a>
## 定理: 共通の左因子と共通の列に続く前部分列 (T.prefix_cons_append)

### 定理

$`A, P, Q \in \mathrm{PairSeq}`$、$`c \in \mathbb{N}\times\mathbb{N}`$ とする。$`P \sqsubseteq Q`$ ならば

```math
A \mathbin{+\!\!+} c :: P \ \sqsubseteq\ A \mathbin{+\!\!+} c :: Q .
```

### 証明

$`Q = P \mathbin{+\!\!+} t`$ なる $`t`$ を取る。cons と連結の関係
$`c :: (P \mathbin{+\!\!+} t) = (c :: P) \mathbin{+\!\!+} t`$ および連結の結合律より

```math
A \mathbin{+\!\!+} c :: Q = A \mathbin{+\!\!+} \bigl((c :: P) \mathbin{+\!\!+} t\bigr)
 = \bigl(A \mathbin{+\!\!+} c :: P\bigr) \mathbin{+\!\!+} t
```

である。よって $`t`$ が求める証人である。∎

<a id="t-spineOK_of_nextrel1_strict"></a>
## 定理: 背骨条件の強形 (T.spineOK_of_nextrel1_strict)

### 定理

$`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$ とし

```math
\ell := (v_0 + d_0,\ w_0 + 1),
\qquad
M := \bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} (\ell),
\qquad
j_1 := \bigl\lvert G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr\rvert
```

とおく。$`\lvert G\rvert \to^M_1 j_1`$ ならば

```math
\mathrm{SpineOK}\bigl(R,\ v_0 + d_0,\ w_0 + 1\bigr).
```

### 証明

$`\mathrm{SpineOK}`$ の定義（D.SpineOK）により、$`U, V \in \mathrm{PairSeq}`$ と
$`x \in \mathbb{N}\times\mathbb{N}`$ が

```math
R = U \mathbin{+\!\!+} x :: V,
\qquad x_1 \lt v_0 + d_0,
\qquad \forall y \in V,\ x_1 \lt y_1
```

をみたすとき $`w_0 + 1 \le x_2`$ を示せばよい。

$`\to^M_1`$ の定義（D.nextrel1）により、仮定 $`\lvert G\rvert \to^M_1 j_1`$ からとくに
条件 (5)

```math
\lvert G\rvert \le^M_0 j_1
```

と条件 (6)

```math
\forall j,\ \bigl(\lvert G\rvert \lt j \wedge j \le^M_0 j_1\bigr) \to M_{1,j_1} \le M_{1,j}
```

が得られる。$`A := G \mathbin{+\!\!+} ((v_0,w_0) :: U)`$ とおく。

**第 1 段：位置の勘定。**
$`R = U \mathbin{+\!\!+} x :: V`$ を $`M`$ の定義に代入し、連結の結合律で並べ替えると

```math
M = A \mathbin{+\!\!+} \bigl(x :: (V \mathbin{+\!\!+} (\ell))\bigr)
```

である。長さは

```math
\lvert A\rvert = \lvert G\rvert + 1 + \lvert U\rvert,
\qquad
j_1 = \lvert G\rvert + 1 + \lvert R\rvert
    = \lvert G\rvert + 1 + \lvert U\rvert + 1 + \lvert V\rvert
    = \lvert A\rvert + 1 + \lvert V\rvert
```

である。とくに $`\lvert G\rvert \lt \lvert A\rvert`$ かつ $`\lvert A\rvert \le j_1`$ である。

[T.getD_append_right'](Cofinality.md#t-getD_append_right') を
$`A`$、$`x :: (V \mathbin{+\!\!+} (\ell))`$、$`i := 0`$ に適用すると
$`M\langle \lvert A\rvert\rangle = x`$ である。したがって
[T.entry_zero](Cofinality.md#t-entry_zero) と [T.entry_one](Cofinality.md#t-entry_one) より

```math
M_{0,\lvert A\rvert} = x_1, \qquad M_{1,\lvert A\rvert} = x_2 .
```

**第 2 段：位置 $`\lvert A\rvert`$ より右、$`j_1`$ までのすべての列は行 $`0`$ が上。**
すなわち

```math
\forall y,\ \bigl(\lvert A\rvert \lt y \wedge y \le j_1\bigr) \to M_{0,\lvert A\rvert} \lt M_{0,y}
```

を示す。$`\lvert A\rvert \lt y`$ より $`y = \lvert A\rvert + (t+1)`$ なる $`t`$ が取れる。
第 1 段の分解と [T.getD_append_right'](Cofinality.md#t-getD_append_right') により

```math
M\bigl\langle \lvert A\rvert + (t+1)\bigr\rangle
 = \bigl(x :: (V \mathbin{+\!\!+} (\ell))\bigr)\langle t+1\rangle
 = \bigl(V \mathbin{+\!\!+} (\ell)\bigr)\langle t\rangle
```

である。$`y \le j_1 = \lvert A\rvert + 1 + \lvert V\rvert`$ より $`t \le \lvert V\rvert`$ であり、
$`t`$ で場合分けする。

- $`t \lt \lvert V\rvert`$ のとき。$`(V \mathbin{+\!\!+} (\ell))\langle t\rangle = V\langle t\rangle`$ であり、
  $`t \lt \lvert V\rvert`$ よりこれは $`V`$ の要素である。仮定 $`\forall y \in V,\ x_1 \lt y_1`$ を
  これに適用して $`x_1 \lt (V\langle t\rangle)_1`$、すなわち
  $`M_{0,\lvert A\rvert} \lt M_{0,y}`$ を得る。

- $`t = \lvert V\rvert`$ のとき。ふたたび
  [T.getD_append_right'](Cofinality.md#t-getD_append_right') を $`V`$、$`(\ell)`$、$`i := 0`$ に適用して
  $`(V \mathbin{+\!\!+} (\ell))\langle \lvert V\rvert\rangle = \ell`$ である。
  仮定 $`x_1 \lt v_0 + d_0 = \ell_1`$ より $`M_{0,\lvert A\rvert} \lt M_{0,y}`$ を得る。

**第 3 段：$`x`$ は落とされる列の行 $`0`$ の祖先である。**
[T.le0_through_pivot](Column.md#t-le0_through_pivot) を
$`a := \lvert G\rvert`$、$`\rho := \lvert A\rvert`$、$`b := j_1`$ として適用する。
仮定は条件 (5) の $`\lvert G\rvert \le^M_0 j_1`$、第 1 段の $`\lvert G\rvert \lt \lvert A\rvert`$ と
$`\lvert A\rvert \le j_1`$、および第 2 段である。結論は

```math
\lvert A\rvert \le^M_0 j_1 .
```

**第 4 段：最小性の条件を使う。**
[T.getD_append_right'](Cofinality.md#t-getD_append_right') を
$`G \mathbin{+\!\!+} ((v_0,w_0) :: R)`$、$`(\ell)`$、$`i := 0`$ に適用して
$`M\langle j_1\rangle = \ell`$ である。よって
[T.entry_one](Cofinality.md#t-entry_one) より $`M_{1,j_1} = \ell_2 = w_0 + 1`$ である。

条件 (6) を $`j := \lvert A\rvert`$ に適用する。その前件は第 1 段の
$`\lvert G\rvert \lt \lvert A\rvert`$ と第 3 段の $`\lvert A\rvert \le^M_0 j_1`$ である。
したがって

```math
w_0 + 1 = M_{1,j_1} \le M_{1,\lvert A\rvert} = x_2 . \qquad \blacksquare
```

<a id="t-argDomCoreOn_bad_A2"></a>
## 定理: 第 4 分岐の場合 A2（交差の場合） (T.argDomCoreOn_bad_A2)

### 定理

$`M, G, R, X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0, n, u, w, e \in \mathbb{N}`$、
$`\ell \in \mathbb{N}\times\mathbb{N}`$ とし、$`\beta := (v_0,w_0) :: R`$ とおく。
次の (1)–(19) を仮定する。

```math
\begin{aligned}
&(1)\ M \in \mathrm{ST\_PS}, \cr
&(2)\ \mathrm{ArgDomCoreOn}(M), \cr
&(3)\ M = G \mathbin{+\!\!+} \beta \mathbin{+\!\!+} (\ell), \cr
&(4)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(5)\ v_0 \lt \ell_1, \cr
&(6)\ \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr)
   \ \vee\ \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 (\lvert M\rvert - 1)\bigr), \cr
&(7)\ \forall m,\ 1 \le m \to G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m) \in \mathrm{ST\_PS}, \cr
&(8)\ \forall m,\ 1 \le m \to m \lt n \to
   \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)\bigr), \cr
&(9)\ 1 \le n, \cr
&(10)\ G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, n)
   = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr)
     \mathbin{+\!\!+} Z, \cr
&(11)\ 0 \lt e, \cr
&(12)\ \forall x \in A_1,\ u \lt x_1, \cr
&(13)\ \forall x \in B,\ u + e \lt x_1, \cr
&(14)\ \forall x \in A_2,\ u \lt x_1, \cr
&(15)\ A_2 = () \ \vee\ (\mathrm{head}\,A_2)_1 \le u + e, \cr
&(16)\ Z = () \ \vee\ (\mathrm{head}\,Z)_1 \le u, \cr
&(17)\ \mathrm{SpineOK}(A_1,\ u+e,\ w), \cr
&(18)\ \lvert X\rvert \lt \lvert G\rvert + (\lvert R\rvert + 1), \cr
&(19)\ \lvert G\rvert + (\lvert R\rvert + 1) \le \lvert X\rvert + (\lvert A_1\rvert + 1).
\end{aligned}
```

このとき

```math
B \preceq_{\mathrm{lex}}
  \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e} .
```

### 証明

**記法.** 以下

```math
L := \lvert R\rvert + 1 = \lvert\beta\rvert, \quad
p := \lvert G\rvert + L, \quad
N := G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, n), \quad
i := \lvert X\rvert, \quad
j := \lvert X\rvert + (\lvert A_1\rvert + 1)
```

と書く。仮定 (18) は $`i \lt p`$、仮定 (19) は $`p \le j`$ である。
また $`((u,w))`$ は $`(u,w)`$ ただ 1 つからなる列を表す。

**第 0 段：$`2 \le n`$。**
[T.argdom_pos](#t-argdom_pos) を (10) に適用すると $`j \lt \lvert N\rvert`$ を得る。
一方 [T.copies_length](#t-copies_length) より
$`\lvert \mathrm{copies}_{d_0}(\beta, n)\rvert = n \cdot L`$ であるから

```math
\lvert N\rvert = \lvert G\rvert + n \cdot L .
```

もし $`n = 1`$ ならば $`\lvert N\rvert = \lvert G\rvert + L = p`$ であり、$`j \lt p`$ となって
(19) の $`p \le j`$ に反する。(9) より $`1 \le n`$ であったから $`2 \le n`$ である。
以下 $`n = m + 1`$、$`1 \le m`$ と書く。

**第 1 段：コピー $`0`$ を剥がし、境界 $`p`$ で切る。**
[T.copies_succ_front](Cnf.md#t-copies_succ_front) より

```math
N = G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m+1)
  = (G \mathbin{+\!\!+} \beta) \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)^{+d_0}
```

である。これと (10) を結合し、結合律で括り直すと

```math
(\ast)\qquad
(G \mathbin{+\!\!+} \beta) \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)^{+d_0}
 = \bigl(X \mathbin{+\!\!+} ((u,w))\bigr)
   \mathbin{+\!\!+} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))\bigr)
```

を得る。(18) より $`\lvert X \mathbin{+\!\!+} ((u,w))\rvert = i + 1 \le p = \lvert G \mathbin{+\!\!+} \beta\rvert`$
であるから、[T.split_append_left](#t-split_append_left) を $`(\ast)`$ に適用して
$`C \in \mathrm{PairSeq}`$ を得る。

```math
\text{(C1)}\ G \mathbin{+\!\!+} \beta = \bigl(X \mathbin{+\!\!+} ((u,w))\bigr) \mathbin{+\!\!+} C,
\qquad
\text{(C2)}\ A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))
  = C \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)^{+d_0} .
```

(C1) の両辺の長さを比べて $`\lvert C\rvert = p - (i+1)`$ である。
(19) は $`p \le i + \lvert A_1\rvert + 1`$、すなわち $`\lvert C\rvert \le \lvert A_1\rvert`$ を与えるから、
ふたたび [T.split_append_left](#t-split_append_left) を (C2) に適用して $`D \in \mathrm{PairSeq}`$ を得る。

```math
\text{(D1)}\ A_1 = C \mathbin{+\!\!+} D,
\qquad
\text{(D2)}\ \mathrm{copies}_{d_0}(\beta, m)^{+d_0}
  = D \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)) .
```

(D1) の長さから $`\lvert A_1\rvert = \lvert C\rvert + \lvert D\rvert`$ である。

$`d_0`$ シフトされた列の要素はすべて第 1 成分が $`d_0`$ 以上である。実際、
$`y \in \mathrm{copies}_{d_0}(\beta, m)^{+d_0}`$ ならば
[T.mem_shiftr0](Cnf.md#t-mem_shiftr0) より $`y = (z_1 + d_0,\ z_2)`$ の形であり
$`d_0 \le z_1 + d_0 = y_1`$ である。これを (D2) の右辺の要素 $`(u+e,w)`$ に適用して

```math
(\dagger)\qquad d_0 \le u + e
```

を得る。同じ理由で $`\forall y \in D,\ d_0 \le y_1`$ である。

**第 2 段：逆シフトして小さい塔を書く。**
$`L^{-d}`$ を $`L`$ の各対の第 1 成分から $`d`$ を（切り捨て減法で）引いた列とする。
(D2) の両辺に $`(\cdot)^{-d_0}`$ を施し、[T.shiftl0_shiftr0](#t-shiftl0_shiftr0) と
[T.shiftl0_append](#t-shiftl0_append)、[T.shiftl0_cons](#t-shiftl0_cons) を使うと

```math
\text{(S)}\qquad \mathrm{copies}_{d_0}(\beta, m)
  = D^{-d_0} \mathbin{+\!\!+} (u+e-d_0,\ w) ::
      \bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
```

を得る。

**第 3 段：$`\lvert X\rvert`$ と $`\lvert G\rvert + \lvert D\rvert`$ の三分法。**
自然数の三分律により、次の 3 つのいずれかがちょうど 1 つ成り立つ。

**(a) $`\lvert X\rvert \lt \lvert G\rvert + \lvert D\rvert`$ のとき。**
$`1 \le m`$ であるから $`m = m'' + 1`$ と書ける。
[T.copies_succ_front](Cnf.md#t-copies_succ_front) より
$`\mathrm{copies}_{d_0}(\beta, m) = \beta \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m'')^{+d_0}`$
であるから $`\beta \sqsubseteq \mathrm{copies}_{d_0}(\beta, m)`$ である
（ここで $`P \sqsubseteq Q`$ は $`\exists T,\ Q = P \mathbin{+\!\!+} T`$ を表す）。
また (S) より $`D^{-d_0} \sqsubseteq \mathrm{copies}_{d_0}(\beta, m)`$ であり、
$`\lvert D^{-d_0}\rvert = \lvert D\rvert`$ である。

(C1) より $`X \mathbin{+\!\!+} ((u,w)) \sqsubseteq G \mathbin{+\!\!+} \beta`$ であり、
[T.prefix_append_left](#t-prefix_append_left) より
$`G \mathbin{+\!\!+} \beta \sqsubseteq G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)`$ かつ
$`G \mathbin{+\!\!+} D^{-d_0} \sqsubseteq G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)`$ である。
同一の列の 2 つの前部分列は、長さの短い方が長い方の前部分列である。いまの場合の長さは
$`i + 1 \le \lvert G\rvert + \lvert D\rvert`$（場合 (a) の条件）であるから

```math
X \mathbin{+\!\!+} ((u,w)) \sqsubseteq G \mathbin{+\!\!+} D^{-d_0}
```

であり、$`A_1' \in \mathrm{PairSeq}`$ が存在して

```math
\text{(A1')}\qquad G \mathbin{+\!\!+} D^{-d_0} = \bigl(X \mathbin{+\!\!+} ((u,w))\bigr) \mathbin{+\!\!+} A_1',
\qquad \lvert A_1'\rvert = \lvert G\rvert + \lvert D\rvert - (i+1)
```

となる。(S) と (A1') を合わせると、小さい塔は

```math
\text{(Nm)}\qquad G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)
  = \bigl((X \mathbin{+\!\!+} ((u,w))) \mathbin{+\!\!+} A_1'\bigr) \mathbin{+\!\!+} (u+e-d_0,\ w) ::
      \bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
```

と書ける。

一方 [T.copies_succ_back](Cofinality.md#t-copies_succ_back) より

```math
G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m+1)
  = \bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)\bigr) \mathbin{+\!\!+} \beta^{+(m d_0)}
```

である。これと (Nm)、および $`(\ast)`$ を合わせると、左因子 $`X \mathbin{+\!\!+} ((u,w))`$ を共有する
2 つの表示が得られる。左因子を消去して

```math
\text{(K)}\qquad
A_1 \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
= A_1' \mathbin{+\!\!+} (u+e-d_0,\ w) ::
   \Bigl(\bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
     \mathbin{+\!\!+} \beta^{+(m d_0)}\Bigr)
```

を得る。$`\lvert A_1'\rvert \le \lvert A_1\rvert`$ であるから
（$`\lvert A_1\rvert = \lvert C\rvert + \lvert D\rvert`$、$`\lvert C\rvert = p - (i+1)`$、
$`\lvert A_1'\rvert = \lvert G\rvert + \lvert D\rvert - (i+1)`$ と $`\lvert G\rvert \le p`$ による）、
[T.split_append_left](#t-split_append_left) を (K) に適用して $`W`$ を得る。

```math
A_1 = A_1' \mathbin{+\!\!+} W,
\qquad
(u+e-d_0,\ w) :: \Bigl(\cdots\Bigr) = W \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr).
```

長さを比べると $`\lvert W\rvert = \lvert A_1\rvert - \lvert A_1'\rvert = L`$ であり、$`1 \le L`$ であるから
$`W \ne ()`$、すなわち $`W = W_0 :: W'`$ と書ける。第 2 式の先頭を比べて
$`W_0 = (u+e-d_0,\ w)`$、残りを比べて

```math
\text{(W)}\qquad
\bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr) \mathbin{+\!\!+} \beta^{+(m d_0)}
 = W' \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

を得る。したがって

```math
\text{(A1dec)}\qquad A_1 = A_1' \mathbin{+\!\!+} (u+e-d_0,\ w) :: W' .
```

$`(u+e-d_0,\ w) \in A_1`$ であるから (12) より $`u \lt u+e-d_0`$、すなわち

```math
(\ddagger)\qquad d_0 \lt e, \qquad u + e - d_0 = u + (e - d_0) .
```

**(a-1) 小さい塔における実例。**
$`\mathrm{tw}_u`$、$`\mathrm{dw}_u`$ をそれぞれ「第 1 成分が $`u`$ より大きい要素が先頭から続く極大な
前部分列」およびその残りとし

```math
A_2' := \mathrm{tw}_u\bigl(A_2^{-d_0}\bigr), \qquad
Z_2 := \mathrm{dw}_u\bigl(A_2^{-d_0}\bigr) \mathbin{+\!\!+} Z^{-d_0}
```

とおく。次の 5 つが成り立つ。

- $`A_2' \mathbin{+\!\!+} Z_2 = A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0}`$：
  $`\mathrm{tw}_u`$ と $`\mathrm{dw}_u`$ の連結が元の列であることによる。
- $`A_2' \sqsubseteq A_2^{-d_0}`$：$`\mathrm{tw}_u`$ は前部分列である。
- $`\forall x \in A_2',\ u \lt x_1`$：$`\mathrm{tw}_u`$ の要素は述語をみたす。
- $`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u + (e-d_0)`$：
  $`A_2 = ()`$ なら $`A_2^{-d_0} = ()`$ で $`A_2' = ()`$。
  $`A_2 = a :: A_2''`$ なら (15) の第 2 選言より $`a_1 \le u+e`$ であり、
  $`A_2^{-d_0} = (a_1 - d_0,\ a_2) :: (A_2'')^{-d_0}`$ である。
  $`u \lt a_1 - d_0`$ ならば $`A_2'`$ の先頭は $`(a_1-d_0,\ a_2)`$ であって
  $`a_1 - d_0 \le u + e - d_0 = u + (e-d_0)`$（$`(\ddagger)`$ による）。
  $`\neg(u \lt a_1 - d_0)`$ ならば $`A_2' = ()`$。
- $`Z_2 = () \vee (\mathrm{head}\,Z_2)_1 \le u`$：
  $`\mathrm{dw}_u(A_2^{-d_0}) = z :: Z''`$ ならば $`\mathrm{dw}_u`$ の先頭は述語を破るので $`z_1 \le u`$。
  $`\mathrm{dw}_u(A_2^{-d_0}) = ()`$ ならば $`Z_2 = Z^{-d_0}`$ であり、$`Z = ()`$ なら $`Z_2 = ()`$、
  $`Z = z :: Z''`$ なら (16) の第 2 選言より $`z_1 \le u`$ であるから $`z_1 - d_0 \le u`$。

これと (Nm) から

```math
\text{(eq')}\qquad G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)
 = \Bigl(X \mathbin{+\!\!+} (u,w) :: \bigl(A_1' \mathbin{+\!\!+} (u + (e-d_0),\ w) ::
     (B^{-d_0} \mathbin{+\!\!+} A_2')\bigr)\Bigr) \mathbin{+\!\!+} Z_2
```

が成り立つ。(8) を $`m`$ に適用する（$`1 \le m`$ かつ $`m \lt m+1 = n`$）ために、
$`\mathrm{ArgDomCoreOn}`$ の残りの仮定を確かめる。

- $`0 \lt e - d_0`$：$`(\ddagger)`$ による。
- $`\forall x \in A_1',\ u \lt x_1`$：(A1dec) より $`A_1'`$ の要素は $`A_1`$ の要素であり、(12) による。
- $`\forall x \in B^{-d_0},\ u + (e-d_0) \lt x_1`$：$`x = (y_1 - d_0,\ y_2)`$（$`y \in B`$）と書ける。
  (13) より $`u + e \lt y_1`$ であり、$`(\dagger)`$ の $`d_0 \le u+e`$ と合わせて
  $`y_1 - d_0 \gt u + e - d_0 = u + (e-d_0)`$。
- $`\forall x \in A_2',\ u \lt x_1`$、$`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u+(e-d_0)`$、
  $`Z_2 = () \vee (\mathrm{head}\,Z_2)_1 \le u`$：上に示した。

**(a-2) 降下した $`\mathrm{SpineOK}`$。**
残るのは $`\mathrm{SpineOK}(A_1',\ u+(e-d_0),\ w)`$ である。
$`U, V \in \mathrm{PairSeq}`$、$`x \in \mathbb{N}\times\mathbb{N}`$ が

```math
A_1' = U \mathbin{+\!\!+} x :: V, \qquad x_1 \lt u + (e-d_0), \qquad \forall y \in V,\ x_1 \lt y_1
```

をみたすとし、$`w \le x_2`$ を示す。$`Y := (X \mathbin{+\!\!+} ((u,w))) \mathbin{+\!\!+} U`$ とおくと、(A1') より

```math
\text{(GSD)}\qquad Y \mathbin{+\!\!+} x :: V = G \mathbin{+\!\!+} D^{-d_0}
```

である。$`\lvert Y\rvert`$ と $`\lvert G\rvert`$ の大小で場合分けする。

**$`\lvert Y\rvert \lt \lvert G\rvert`$ のとき。**
このとき $`\lvert Y \mathbin{+\!\!+} (x)\rvert \le \lvert G\rvert`$ であるから、
[T.split_append_left](#t-split_append_left) を (GSD) に適用して $`V_3`$ を得る。

```math
G = \bigl(Y \mathbin{+\!\!+} (x)\bigr) \mathbin{+\!\!+} V_3, \qquad V = V_3 \mathbin{+\!\!+} D^{-d_0} .
```

これを (C1) に代入し、共通の左因子 $`X \mathbin{+\!\!+} ((u,w))`$ を消去すると

```math
C = \bigl(U \mathbin{+\!\!+} (x)\bigr) \mathbin{+\!\!+} \bigl(V_3 \mathbin{+\!\!+} \beta\bigr)
```

であり、(D1) と合わせて

```math
A_1 = U \mathbin{+\!\!+} x :: \bigl((V_3 \mathbin{+\!\!+} \beta) \mathbin{+\!\!+} D\bigr)
```

を得る。次に $`x_1 \lt v_0`$ を示す。$`\beta \ne ()`$ かつ $`1 \le m`$ であるから
[T.copies_headI](#t-copies_headI) より
$`\mathrm{head}\,\mathrm{copies}_{d_0}(\beta, m) = \mathrm{head}\,\beta = (v_0,w_0)`$ である。
(S) の右辺の先頭で場合分けする。

- $`D^{-d_0} = ()`$ のとき。(S) の右辺の先頭は $`(u+e-d_0,\ w)`$ であるから
  $`u + e - d_0 = v_0`$ である。$`(\ddagger)`$ より $`u+(e-d_0) = v_0`$ であり、
  仮定 $`x_1 \lt u+(e-d_0)`$ から $`x_1 \lt v_0`$。
- $`D^{-d_0} = s :: S'`$ のとき。(S) の右辺の先頭は $`s`$ であるから $`s = (v_0,w_0)`$ である。
  $`V = V_3 \mathbin{+\!\!+} D^{-d_0}`$ より $`s \in V`$ であり、仮定 $`\forall y \in V,\ x_1 \lt y_1`$ から
  $`x_1 \lt s_1 = v_0`$。

そこで (17) を $`U`$、$`(V_3 \mathbin{+\!\!+} \beta) \mathbin{+\!\!+} D`$、$`x`$ に適用する。3 つの条件を確かめる。

- 分解 $`A_1 = U \mathbin{+\!\!+} x :: ((V_3 \mathbin{+\!\!+} \beta) \mathbin{+\!\!+} D)`$：上に示した。
- $`x_1 \lt u + e`$：$`x_1 \lt u + (e-d_0) \le u + e`$。
- $`\forall y \in (V_3 \mathbin{+\!\!+} \beta) \mathbin{+\!\!+} D,\ x_1 \lt y_1`$：$`y`$ の属する部分で分ける。
  $`y \in V_3`$ なら $`y \in V`$ であるから仮定による。
  $`y = (v_0,w_0)`$ なら $`x_1 \lt v_0 = y_1`$。
  $`y \in R`$ なら (4) より $`v_0 \lt y_1`$ であり、$`x_1 \lt v_0`$ と合わせて $`x_1 \lt y_1`$。
  $`y \in D`$ なら (D2) より $`y \in \mathrm{copies}_{d_0}(\beta, m)^{+d_0}`$ であるから
  [T.mem_shiftr0](Cnf.md#t-mem_shiftr0) より $`y = (z_1+d_0,\ z_2)`$、
  $`z \in \mathrm{copies}_{d_0}(\beta, m)`$ と書ける。(4) より $`\forall x \in R,\ v_0 \le x_1`$ であるから
  [T.copies_v0_le](Cnf.md#t-copies_v0_le) が使えて $`v_0 \le z_1 \le z_1 + d_0 = y_1`$、
  したがって $`x_1 \lt v_0 \le y_1`$。

よって $`w \le x_2`$ を得る。

**$`\lvert G\rvert \le \lvert Y\rvert`$ のとき。**
[T.split_append_left](#t-split_append_left) を (GSD) に適用して $`U_2`$ を得る。

```math
Y = G \mathbin{+\!\!+} U_2, \qquad D^{-d_0} = U_2 \mathbin{+\!\!+} x :: V .
```

$`\forall y \in D,\ d_0 \le y_1`$ は第 1 段で示したから、
[T.shiftr0_shiftl0](#t-shiftr0_shiftl0) より $`(D^{-d_0})^{+d_0} = D`$ である。
第 2 式の両辺に $`(\cdot)^{+d_0}`$ を施し、
[T.shiftr0_append](Cofinality.md#t-shiftr0_append) と
[T.shiftr0_cons](Cnf.md#t-shiftr0_cons) を使って

```math
D = U_2^{+d_0} \mathbin{+\!\!+} (x_1 + d_0,\ x_2) :: V^{+d_0}
```

を得る。(17) を $`C \mathbin{+\!\!+} U_2^{+d_0}`$、$`V^{+d_0}`$、$`(x_1+d_0,\ x_2)`$ に適用する。

- 分解：(D1) より
  $`A_1 = C \mathbin{+\!\!+} D = (C \mathbin{+\!\!+} U_2^{+d_0}) \mathbin{+\!\!+} (x_1+d_0,\ x_2) :: V^{+d_0}`$。
- $`x_1 + d_0 \lt u+e`$：$`x_1 \lt u+(e-d_0)`$ と $`(\ddagger)`$ の $`d_0 \lt e`$ から
  $`x_1 + d_0 \lt u + (e-d_0) + d_0 = u + e`$。
- $`\forall y \in V^{+d_0},\ x_1 + d_0 \lt y_1`$：$`y = (z_1+d_0,\ z_2)`$（$`z \in V`$）と書け、
  仮定 $`x_1 \lt z_1`$ から $`x_1 + d_0 \lt z_1 + d_0 = y_1`$。

よって $`w \le (x_1+d_0,\ x_2)_2 = x_2`$ を得る。以上で
$`\mathrm{SpineOK}(A_1',\ u+(e-d_0),\ w)`$ が示された。

**(a-3) 結論の持ち上げ。**
(8) を $`m`$ に適用し、(eq') と (a-1)(a-2) で確かめた仮定を与えると

```math
\text{(core)}\qquad B^{-d_0} \preceq_{\mathrm{lex}}
  \bigl(A_1' \mathbin{+\!\!+} (u+(e-d_0),\ w) :: (B^{-d_0} \mathbin{+\!\!+} A_2')\bigr)^{+(e-d_0)}
```

を得る。まず

```math
B^{-d_0} \mathbin{+\!\!+} A_2' \ \sqsubseteq\ W' \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)
```

を示す。(W) と $`A_2' \mathbin{+\!\!+} Z_2 = A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0}`$ より

```math
\bigl(B^{-d_0} \mathbin{+\!\!+} A_2'\bigr) \mathbin{+\!\!+}
  \bigl(Z_2 \mathbin{+\!\!+} \beta^{+(m d_0)}\bigr)
 = W' \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

であるから $`B^{-d_0} \mathbin{+\!\!+} A_2'`$ は右辺の前部分列である。また
$`W' \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)`$ も
$`W' \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))`$ の前部分列である。長さは
$`\lvert A_2'\rvert \le \lvert A_2^{-d_0}\rvert = \lvert A_2\rvert`$ より

```math
\lvert B^{-d_0} \mathbin{+\!\!+} A_2'\rvert = \lvert B\rvert + \lvert A_2'\rvert
 \le \lvert W'\rvert + 1 + \lvert B\rvert + \lvert A_2\rvert
 = \lvert W' \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\rvert
```

であり、同一の列の 2 つの前部分列のうち短い方が長い方の前部分列であることから主張を得る。
これに (A1dec) と $`(\ddagger)`$ を使い [T.prefix_cons_append](#t-prefix_cons_append) を適用すると

```math
A_1' \mathbin{+\!\!+} (u+(e-d_0),\ w) :: (B^{-d_0} \mathbin{+\!\!+} A_2')
 \ \sqsubseteq\ A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)
```

である。[T.shiftr0_prefix](#t-shiftr0_prefix) を $`e-d_0`$ について適用すると、この前部分列関係は
$`(\cdot)^{+(e-d_0)}`$ で保たれるから、ある $`T`$ について

```math
\bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+(e-d_0)}
 = \bigl(A_1' \mathbin{+\!\!+} (u+(e-d_0),\ w) :: (B^{-d_0} \mathbin{+\!\!+} A_2')\bigr)^{+(e-d_0)}
   \mathbin{+\!\!+} T
```

である。(core) に [T.sle_append_mono](Cofinality.md#t-sle_append_mono) を適用して

```math
B^{-d_0} \preceq_{\mathrm{lex}}
  \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+(e-d_0)}
```

を得る。(13) と $`(\dagger)`$ から $`\forall x \in B,\ d_0 \le u + e \lt x_1`$ であるから、
[T.shiftr0_shiftl0](#t-shiftr0_shiftl0) より $`(B^{-d_0})^{+d_0} = B`$ である。
[T.sle_shiftr0](#t-sle_shiftr0) を $`d_0`$ について適用し、
[T.shiftr0_add](#t-shiftr0_add) と $`d_0 + (e-d_0) = e`$（$`(\ddagger)`$ による）を使うと

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

を得る。これが求める結論である。

**(b) $`\lvert X\rvert = \lvert G\rvert + \lvert D\rvert`$ のとき。**
(S) より

```math
\text{(Nm)}\qquad G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)
  = \bigl(G \mathbin{+\!\!+} D^{-d_0}\bigr) \mathbin{+\!\!+} (u+e-d_0,\ w) ::
      \bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
```

であり、[T.copies_succ_back](Cofinality.md#t-copies_succ_back) より

```math
G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m+1)
  = \bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)\bigr) \mathbin{+\!\!+} \beta^{+(m d_0)}
```

である。これらと $`(\ast)`$ から

```math
\text{(key)}\qquad
\bigl(X \mathbin{+\!\!+} ((u,w))\bigr) \mathbin{+\!\!+}
  \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))\bigr)
= \bigl(G \mathbin{+\!\!+} D^{-d_0}\bigr) \mathbin{+\!\!+}
  \Bigl((u+e-d_0,\ w) :: \bigl(\Sigma \mathbin{+\!\!+} \beta^{+(m d_0)}\bigr)\Bigr)
```

を得る。ここで
$`\Sigma := B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})`$ と略記した。
場合 (b) の条件より

```math
\lvert G \mathbin{+\!\!+} D^{-d_0}\rvert = \lvert G\rvert + \lvert D\rvert = \lvert X\rvert
 \le \lvert X \mathbin{+\!\!+} ((u,w))\rvert
```

であるから、[T.split_append_left](#t-split_append_left) を (key) に適用して $`K`$ を得る。

```math
X \mathbin{+\!\!+} ((u,w)) = \bigl(G \mathbin{+\!\!+} D^{-d_0}\bigr) \mathbin{+\!\!+} K,
\qquad
(u+e-d_0,\ w) :: \bigl(\Sigma \mathbin{+\!\!+} \beta^{+(m d_0)}\bigr)
 = K \mathbin{+\!\!+} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))\bigr).
```

第 1 式の長さから $`\lvert K\rvert = (\lvert X\rvert + 1) - (\lvert G\rvert + \lvert D\rvert) = 1`$
であるから $`K = (k)`$ と書ける。第 1 式は左右の長さの一致
$`\lvert X\rvert = \lvert G \mathbin{+\!\!+} D^{-d_0}\rvert`$ をもつので、両辺を長さ $`\lvert X\rvert`$ の
部分とその後の 1 要素に分けて比べると

```math
X = G \mathbin{+\!\!+} D^{-d_0}, \qquad k = (u,w)
```

を得る。第 2 式の先頭を比べると $`k = (u+e-d_0,\ w)`$ である。第 1 成分を比べて
$`u = u + e - d_0`$ であり、$`(\dagger)`$ の $`d_0 \le u+e`$ と合わせて $`e = d_0`$ を得る。
第 2 式の残りを比べると

```math
\text{(RW)}\qquad \Sigma \mathbin{+\!\!+} \beta^{+(m d_0)}
 = A_1 \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

である。$`B^{-d_0}`$ は $`\Sigma`$ の前部分列であるから (RW) より

```math
B^{-d_0} \ \sqsubseteq\ A_1 \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

である。また

```math
A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)
 \ \sqsubseteq\ A_1 \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

であり、長さは
$`\lvert B^{-d_0}\rvert = \lvert B\rvert \le \lvert A_1\rvert + 1 + \lvert B\rvert + \lvert A_2\rvert`$
をみたす。同一の列の 2 つの前部分列のうち短い方が長い方の前部分列であるから

```math
B^{-d_0} \ \sqsubseteq\ A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)
```

を得る。(13) と $`(\dagger)`$ から $`\forall x \in B,\ d_0 \le x_1`$ であり、$`e = d_0`$ であるから
[T.shiftr0_shiftl0](#t-shiftr0_shiftl0) より $`(B^{-d_0})^{+e} = B`$ である。
[T.shiftr0_prefix](#t-shiftr0_prefix) を $`e`$ について適用すると

```math
B \ \sqsubseteq\ \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

となり、[T.sle_of_prefix](#t-sle_of_prefix) から結論を得る。

**(c) $`\lvert G\rvert + \lvert D\rvert \lt \lvert X\rvert`$ のとき。**
この場合は起こらないことを示す。$`1 \le m`$ より $`m = m' + 1`$ と書ける。

**(c-1) $`(u,w)`$ は $`R`$ の内部にある。**
(C1) を左右入れ替えた
$`(X \mathbin{+\!\!+} ((u,w))) \mathbin{+\!\!+} C = G \mathbin{+\!\!+} \beta`$ に、
$`\lvert G\rvert \le \lvert X\rvert \lt \lvert X \mathbin{+\!\!+} ((u,w))\rvert`$ のもとで
[T.split_append_left](#t-split_append_left) を適用して $`K`$ を得る。

```math
X \mathbin{+\!\!+} ((u,w)) = G \mathbin{+\!\!+} K, \qquad \beta = K \mathbin{+\!\!+} C .
```

$`\lvert K\rvert = \lvert X\rvert + 1 - \lvert G\rvert`$ であり、場合 (c) の条件から
$`\lvert G\rvert \lt \lvert X\rvert`$ なので $`\lvert K\rvert \ge 2 \gt 0`$、すなわち
$`K = k_0 :: K_1`$ と書ける。$`\beta = (v_0,w_0) :: R`$ の尾を比べて $`R = K_1 \mathbin{+\!\!+} C`$ を得る。
第 1 式は $`X \mathbin{+\!\!+} ((u,w)) = (G \mathbin{+\!\!+} (k_0)) \mathbin{+\!\!+} K_1`$ と書き直せ、
$`\lvert G \mathbin{+\!\!+} (k_0)\rvert = \lvert G\rvert + 1 \le \lvert X\rvert`$ であるから、
ふたたび [T.split_append_left](#t-split_append_left) を適用して $`T`$ を得る。

```math
X = \bigl(G \mathbin{+\!\!+} (k_0)\bigr) \mathbin{+\!\!+} T, \qquad K_1 = T \mathbin{+\!\!+} ((u,w)) .
```

したがって

```math
\text{(Rdec)}\qquad R = T \mathbin{+\!\!+} (u,w) :: C
```

である。$`(u,w) \in R`$ であるから (4) より $`v_0 \lt u`$ である。

**(c-2) コピー $`1`$ の根から $`u \lt v_0 + d_0`$ と $`w \le w_0`$ を得る。**
[T.copies_succ_cons](Cnf.md#t-copies_succ_cons) と
[T.shiftr0_cons](Cnf.md#t-shiftr0_cons) より

```math
\text{(SC)}\qquad \mathrm{copies}_{d_0}(\beta, m'+1)^{+d_0}
 = (v_0+d_0,\ w_0) :: \Bigl(R \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m')^{+d_0}\Bigr)^{+d_0}
```

である。(D2) の左辺はこれであるから、$`D`$ で場合分けする。

**$`D = ()`$ のとき。** (D2) と (SC) の先頭を比べて
$`(v_0+d_0,\ w_0) = (u+e,\ w)`$、すなわち $`v_0 + d_0 = u + e`$ かつ $`w_0 = w`$ である。
(11) の $`0 \lt e`$ より $`u \lt u + e = v_0 + d_0`$ であり、$`w \le w_0`$ も成り立つ。

**$`D = d_1 :: D'`$ のとき。** (D2) と (SC) の先頭を比べて $`d_1 = (v_0+d_0,\ w_0)`$、
残りを比べて

```math
\text{(rest)}\qquad
\Bigl(R \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m')^{+d_0}\Bigr)^{+d_0}
 = D' \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

を得る。(D1) より $`A_1 = C \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: D'`$ である。
$`(v_0+d_0,\ w_0) \in A_1`$ に (12) を適用して $`u \lt v_0 + d_0`$ を得る。
これと (c-1) の $`v_0 \lt u`$ から $`0 \lt d_0`$ である。
(4) と $`0 \lt d_0`$ と $`1 \le m'+1`$ に
[T.copies_tl_gt](Cnf.md#t-copies_tl_gt) を適用すると

```math
\forall y \in R \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m')^{+d_0},\ v_0 \lt y_1
```

であり、[T.mem_shiftr0](Cnf.md#t-mem_shiftr0) より、この列を $`d_0`$ だけシフトした列
（すなわち (rest) の左辺）の要素 $`y`$ はすべて $`v_0 + d_0 \lt y_1`$ をみたす。
(rest) の右辺には $`(u+e,w)`$ と $`D'`$ の全要素が現れるから

```math
v_0 + d_0 \lt u + e, \qquad \forall y \in D',\ v_0 + d_0 \lt y_1
```

である。よって (17) を $`C`$、$`D'`$、$`(v_0+d_0,\ w_0)`$ に適用でき
（分解は $`A_1 = C \mathbin{+\!\!+} (v_0+d_0,w_0) :: D'`$）、$`w \le w_0`$ を得る。

いずれの場合も $`u \lt v_0 + d_0`$ かつ $`w \le w_0`$ である。
(c-1) の $`v_0 \lt u`$ と合わせて $`0 \lt d_0`$ である。

**(c-3) 極小性条件との矛盾。**
(6) で場合分けする。第 1 選言は $`d_0 = 0`$ を含み、(c-2) の $`0 \lt d_0`$ に反する。
第 2 選言のとき、$`\ell_1 = v_0 + d_0`$ と $`\ell_2 = w_0 + 1`$ より
$`\ell = (v_0+d_0,\ w_0+1)`$ である。(3) より
$`\lvert M\rvert - 1 = \lvert G \mathbin{+\!\!+} \beta\rvert`$ であるから、第 2 選言の第 4 連言子は

```math
\lvert G\rvert \to^{(G \mathbin{+\!\!+} \beta) \mathbin{+\!\!+} ((v_0+d_0,\,w_0+1))}_1
  \lvert G \mathbin{+\!\!+} \beta\rvert
```

と書ける。これに [T.spineOK_of_nextrel1_strict](#t-spineOK_of_nextrel1_strict) を適用すると
$`\mathrm{SpineOK}(R,\ v_0+d_0,\ w_0+1)`$ を得る。これを (Rdec) の分解
$`R = T \mathbin{+\!\!+} (u,w) :: C`$、$`u \lt v_0+d_0`$（(c-2)）、および
$`\forall y \in C,\ u \lt y_1`$（(D1) より $`C`$ の要素は $`A_1`$ の要素であり (12) による）に
適用して $`w_0 + 1 \le w`$ を得る。これは (c-2) の $`w \le w_0`$ に反する。

したがって場合 (c) は起こらない。∎

<a id="t-argDomCoreOn_bad"></a>
## 定理: 第 4 分岐での ArgDomCoreOn の保存 (T.argDomCoreOn_bad)

### 定理

$`M, G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0, n \in \mathbb{N}`$、
$`\ell \in \mathbb{N}\times\mathbb{N}`$ とし、$`\beta := (v_0,w_0) :: R`$ とおく。
[T.argDomCoreOn_bad_A2](#t-argDomCoreOn_bad_A2) の仮定 (1)–(7) と (9)、すなわち

```math
\begin{aligned}
&(1)\ M \in \mathrm{ST\_PS}, \quad (2)\ \mathrm{ArgDomCoreOn}(M), \quad
 (3)\ M = G \mathbin{+\!\!+} \beta \mathbin{+\!\!+} (\ell), \cr
&(4)\ \forall x \in R,\ v_0 \lt x_1, \quad (5)\ v_0 \lt \ell_1, \cr
&(6)\ \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr)
   \ \vee\ \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 (\lvert M\rvert - 1)\bigr), \cr
&(7)\ \forall m,\ 1 \le m \to G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m) \in \mathrm{ST\_PS},
 \quad (9)\ 1 \le n
\end{aligned}
```

を仮定する。このとき
$`\mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, n)\bigr)`$。

### 証明

$`n`$ に関する完全帰納法による。帰納法の述語は

```math
\Phi(n) :\equiv \Bigl(1 \le n \to
  \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, n)\bigr)\Bigr)
```

である（結論の $`1 \le n`$ を前件に戻して量化する）。完全帰納法の帰納段は
「任意の $`n`$ について、$`\forall m \lt n,\ \Phi(m)`$ を仮定して $`\Phi(n)`$ を示す」であり、
基底段はこの帰納段の $`n = 0`$ の場合、すなわち前件 $`1 \le 0`$ が偽であることから
$`\Phi(0)`$ が成り立つ場合として含まれている。

**帰納段。** $`n`$ を固定し、帰納法の仮定

```math
\text{(IH)}\qquad \forall m,\ m \lt n \to
  \Bigl(1 \le m \to \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)\bigr)\Bigr)
```

をおく。$`1 \le n`$ とし、$`\mathrm{ArgDomCoreOn}`$ の定義に従って
$`X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$、$`u, w, e \in \mathbb{N}`$ と
[T.argDomCoreOn_bad_A2](#t-argDomCoreOn_bad_A2) の仮定 (10)–(17) を与えられたとして

```math
B \preceq_{\mathrm{lex}}
  \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

を示す。(IH) を書き直すと、これは
[T.argDomCoreOn_bad_A2](#t-argDomCoreOn_bad_A2) の仮定 (8)

```math
\forall m,\ 1 \le m \to m \lt n \to
  \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, m)\bigr)
```

そのものである。

$`i := \lvert X\rvert`$、$`j := \lvert X\rvert + (\lvert A_1\rvert + 1)`$、
$`p := \lvert G\rvert + (\lvert R\rvert + 1)`$ とおく。自然数の全順序性により
$`j \lt p`$ または $`p \le j`$ であり、後者の場合さらに $`i \lt p`$ または $`p \le i`$ である。
この 3 通りは互いに排反で、かつすべての場合を尽くす。

- $`j \lt p`$ のとき。[T.argDomCoreOn_bad_B](#t-argDomCoreOn_bad_B) を
  (1)–(7)、(8)、(9)、(10)–(17) と判別条件 $`j \lt p`$ に適用する。
- $`p \le j`$ かつ $`i \lt p`$ のとき。[T.argDomCoreOn_bad_A2](#t-argDomCoreOn_bad_A2) を
  (1)–(7)、(8)、(9)、(10)–(17) と判別条件 (18) $`i \lt p`$、(19) $`p \le j`$ に適用する。
- $`p \le j`$ かつ $`p \le i`$ のとき。[T.argDomCoreOn_bad_A1](#t-argDomCoreOn_bad_A1) を
  (1)–(7)、(8)、(9)、(10)–(17) と判別条件 $`p \le i`$ に適用する。

いずれの場合も結論が得られた。∎

<a id="t-argDomCoreOn_oper"></a>
## 定理: 展開による ArgDomCoreOn の保存 (T.argDomCoreOn_oper)

### 定理

$`M \in \mathrm{ST\_PS}`$、$`\mathrm{ArgDomCoreOn}(M)`$、$`1 \le n`$ ならば
$`\mathrm{ArgDomCoreOn}(M[n])`$。

### 証明

$`j_1 := \lvert M\rvert - 1`$ と書く。$`M[n]`$ の定義（D.oper）の分岐に沿って場合分けする。

**(a) $`j_1 = 0`$ のとき。**
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より $`M[n] = M`$ であるから、
仮定 $`\mathrm{ArgDomCoreOn}(M)`$ がそのまま結論である。

**(b) $`j_1 \ne 0`$ かつ $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。**
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) より
$`M[n] = \mathrm{Pred}\,M`$ である。$`j_1 = \lvert M\rvert - 1 \ne 0`$ より
$`2 \le \lvert M\rvert`$、すなわち $`\neg(\lvert M\rvert \le 1)`$ であるから、
$`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合が選ばれて
$`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。

$`M \ne ()`$ である（$`M = ()`$ なら $`\lvert M\rvert = 0`$ となり $`2 \le \lvert M\rvert`$ に反する）。
また $`M_{i,j}`$ の定義（D.entry）より仮定は
$`(M\langle j_1\rangle)_1 = 0`$ かつ $`(M\langle j_1\rangle)_2 = 0`$、すなわち
$`M\langle j_1\rangle = (0,0)`$ である。
[T.dropLast_snoc_getD](Cofinality.md#t-dropLast_snoc_getD) より

```math
\mathrm{dropLast}\,M \mathbin{+\!\!+} \bigl((0,0)\bigr) = M
```

であるから、仮定 $`\mathrm{ArgDomCoreOn}(M)`$ は
$`\mathrm{ArgDomCoreOn}\bigl(\mathrm{dropLast}\,M \mathbin{+\!\!+} ((0,0))\bigr)`$ に他ならない。
$`(0,0)`$ の第 1 成分は $`0`$ であるから
[T.argDomCoreOn_snoc_zero](#t-argDomCoreOn_snoc_zero) が適用でき、
$`\mathrm{ArgDomCoreOn}(\mathrm{dropLast}\,M) = \mathrm{ArgDomCoreOn}(M[n])`$ を得る。

**(c) $`j_1 \ne 0`$ かつ $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ のとき。**
$`2 \le \lvert M\rvert`$ より $`0 \lt \lvert M\rvert`$ であるから、
[T.hasParent_last_ST_PS](Cofinality.md#t-hasParent_last_ST_PS) より
$`\mathrm{hasParent}(M, \mathrm{idx}_1(M,j_1), j_1)`$ が成り立つ。

[T.blockok_ST_PS](Seqlex.md#t-blockok_ST_PS) より $`\mathrm{blockok}(0, M)`$ であり、その第 3 連言子が
$`\mathrm{steps1}\,M`$ である。また [T.r1ok_ST_PS](Column.md#t-r1ok_ST_PS) より
$`\mathrm{r1ok}\,M`$ である。$`1 \lt \lvert M\rvert`$ とこれらに
[T.oper_bad_blocks_all](Cofinality.md#t-oper_bad_blocks_all) を適用して、
$`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$
であって、$`\beta := (v_0,w_0) :: R`$ とおくと

```math
\begin{aligned}
&M = G \mathbin{+\!\!+} \beta \mathbin{+\!\!+} (\ell), \cr
&\forall k,\ 1 \le k \to M[k] = G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, k), \cr
&\forall x \in R,\ v_0 \lt x_1, \qquad v_0 \lt \ell_1, \cr
&\bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr)
   \ \vee\ \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 (\lvert M\rvert - 1)\bigr)
\end{aligned}
```

をみたすものを取る。

各 $`k \ge 1`$ について
$`G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, k) = M[k]`$ であり、
$`\mathrm{ST\_PS}`$ の定義（D.ST_PS）の構成子 $`\mathrm{oper}`$ を $`M \in \mathrm{ST\_PS}`$ と
$`1 \le k`$ に適用すると $`M[k] \in \mathrm{ST\_PS}`$ であるから

```math
\forall k,\ 1 \le k \to G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, k) \in \mathrm{ST\_PS}
```

が成り立つ。最後に $`M[n] = G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\beta, n)`$ と書き直し、
[T.argDomCoreOn_bad](#t-argDomCoreOn_bad) を適用すればよい。∎

<a id="t-argDomCoreOn_ST_PS"></a>
## 定理: 標準形上の ArgDomCoreOn (T.argDomCoreOn_ST_PS)

### 定理

$`N \in \mathrm{ST\_PS}`$ ならば $`\mathrm{ArgDomCoreOn}(N)`$。

### 証明

$`N \in \mathrm{ST\_PS}`$ の導出に関する帰納法による（$`\mathrm{ST\_PS}`$ の定義 D.ST_PS が
帰納的定義であり、その最小性が帰納法の原理を与える）。帰納法の述語は

```math
\Phi(N) :\equiv \mathrm{ArgDomCoreOn}(N)
```

である。構成子は 2 つであるから、次の 2 段を示せばよい。

**基底段（構成子 $`\mathrm{diag}`$）。** $`N = \mathrm{diagSeq}(0,v)`$ の場合である。
[T.argDomCoreOn_diag](#t-argDomCoreOn_diag) がそのまま
$`\Phi(\mathrm{diagSeq}(0,v))`$ である。

**帰納段（構成子 $`\mathrm{oper}`$）。** $`N = M[n]`$ であって、
$`M \in \mathrm{ST\_PS}`$ と $`1 \le n`$ からこの構成子で導出された場合である。
帰納法の仮定は $`\Phi(M) = \mathrm{ArgDomCoreOn}(M)`$ である。
[T.argDomCoreOn_oper](#t-argDomCoreOn_oper) を $`M \in \mathrm{ST\_PS}`$、
帰納法の仮定 $`\mathrm{ArgDomCoreOn}(M)`$、$`1 \le n`$ に適用して
$`\mathrm{ArgDomCoreOn}(M[n]) = \Phi(N)`$ を得る。∎

<a id="t-argDomCore_holds"></a>
## 定理: ArgDomCore の成立 (T.argDomCore_holds)

### 定理

$`\mathrm{ArgDomCore}`$。

### 証明

[T.argDomCore_of_on](#t-argDomCore_of_on) は
$`\forall N,\ N \in \mathrm{ST\_PS} \to \mathrm{ArgDomCoreOn}(N)`$ から
$`\mathrm{ArgDomCore}`$ を導く。その前提は
[T.argDomCoreOn_ST_PS](#t-argDomCoreOn_ST_PS) そのものである。∎
