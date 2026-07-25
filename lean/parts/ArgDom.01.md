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
