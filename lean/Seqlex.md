[← README](README.md) ｜ Seqlex **1** [2](Seqlex-2.md)

<a id="d-pairlt"></a>
## 定義: 対の辞書式順序 (D.pairlt)

$`p, q \in \mathbb{N}\times\mathbb{N}`$ に対し

```math
p \prec_{\mathrm{p}} q :\iff p_1 \lt q_1 \ \vee\ \bigl(p_1 = q_1 \wedge p_2 \lt q_2\bigr).
```

ここで $`p = (p_1, p_2)`$、$`q = (q_1, q_2)`$ である。すなわち $`\prec_{\mathrm{p}}`$ は、
対を第 1 成分、第 2 成分の順に比べる辞書式順序である。

<a id="d-seqlex"></a>
## 定義: 列の辞書式順序 (D.seqlex)

$`M, N \in \mathrm{PairSeq}`$（[D.PairSeq](Pss.md#d-PairSeq)）に対し、関係
$`M \prec_{\mathrm{lex}} N`$ を両引数の構成子による場合分けで定める。
以下 $`()`$ は空列、$`p :: M`$ は列 $`M`$ の先頭に対 $`p`$ を付けた列である。

```math
\begin{aligned}
() &\prec_{\mathrm{lex}} N &&:\iff N \ne (), \cr
(p :: M) &\prec_{\mathrm{lex}} () &&:\iff \bot, \cr
(p :: M) &\prec_{\mathrm{lex}} (q :: N) &&:\iff
  p \prec_{\mathrm{p}} q \ \vee\ \bigl(p = q \wedge M \prec_{\mathrm{lex}} N\bigr).
\end{aligned}
```

第 3 式の右辺の再帰呼び出しは $`M \prec_{\mathrm{lex}} N`$ であり、$`M`$, $`N`$ は
それぞれ $`p :: M`$, $`q :: N`$ より長さが $`1`$ 短いから、この定義は整合的である。

すなわち $`\prec_{\mathrm{lex}}`$ は、列を先頭から 1 列ずつ $`\prec_{\mathrm{p}}`$ で比べる
辞書式順序である。第 1 式は空列が空でないすべての列より小さいこと、第 2 式は
空列より小さい列が存在しないことを言う。

<a id="t-seqlex_nil_iff"></a>
## 定理: 空列を左辺とする比較 (T.seqlex_nil_iff)

### 定理

$`N \in \mathrm{PairSeq}`$ に対し $`() \prec_{\mathrm{lex}} N \iff N \ne ()`$。

### 証明

$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式により、左辺と右辺は定義により
同一の命題である。∎

<a id="t-not_seqlex_nil"></a>
## 定理: 空列を右辺とする比較 (T.not_seqlex_nil)

### 定理

$`p \in \mathbb{N}\times\mathbb{N}`$、$`M \in \mathrm{PairSeq}`$ に対し
$`\neg\bigl((p :: M) \prec_{\mathrm{lex}} ()\bigr)`$。

### 証明

$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 2 式により
$`(p :: M) \prec_{\mathrm{lex}} ()`$ は $`\bot`$ と定義により同一の命題である。
よってその仮定から $`\bot`$ が得られる。∎

<a id="t-seqlex_cons_cons"></a>
## 定理: 先頭を付けた列どうしの比較 (T.seqlex_cons_cons)

### 定理

$`p, q \in \mathbb{N}\times\mathbb{N}`$、$`M, N \in \mathrm{PairSeq}`$ に対し

```math
(p :: M) \prec_{\mathrm{lex}} (q :: N) \iff
  p \prec_{\mathrm{p}} q \ \vee\ \bigl(p = q \wedge M \prec_{\mathrm{lex}} N\bigr).
```

### 証明

$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式そのものであり、両辺は定義により
同一の命題である。∎

<a id="t-seqlex_append_cancel"></a>
## 定理: 共通の前置列の消去 (T.seqlex_append_cancel)

### 定理

$`A, u, v \in \mathrm{PairSeq}`$ に対し

```math
(A \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A \mathbin{+\!\!+} v) \iff u \prec_{\mathrm{lex}} v .
```

### 証明

$`A`$ のリスト構造に関する帰納法（$`u`$, $`v`$ は固定する）。帰納法の述語は

```math
\Phi(A) :\equiv \Bigl((A \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A \mathbin{+\!\!+} v)
  \iff u \prec_{\mathrm{lex}} v\Bigr).
```

- **基底段** $`A = ()`$：$`() \mathbin{+\!\!+} u = u`$、$`() \mathbin{+\!\!+} v = v`$ であるから、
  両辺は同一の命題である。

**帰納段** $`A = a :: A'`$：帰納法の仮定は $`\Phi(A')`$、すなわち

```math
(A' \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A' \mathbin{+\!\!+} v) \iff u \prec_{\mathrm{lex}} v
```

である。$`(a :: A') \mathbin{+\!\!+} u = a :: (A' \mathbin{+\!\!+} u)`$、
$`(a :: A') \mathbin{+\!\!+} v = a :: (A' \mathbin{+\!\!+} v)`$ であるから、
[T.seqlex_cons_cons](#t-seqlex_cons_cons) により示すべき左辺は

```math
a \prec_{\mathrm{p}} a \ \vee\ \bigl(a = a \wedge
  (A' \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A' \mathbin{+\!\!+} v)\bigr)
```

と同値である。ここで $`\prec_{\mathrm{p}}`$ の定義（D.pairlt）より
$`a \prec_{\mathrm{p}} a`$ は $`a_1 \lt a_1`$ または
$`a_1 = a_1 \wedge a_2 \lt a_2`$ であり、$`\mathbb{N}`$ の $`\lt`$ の非反射性により
どちらも偽であるから、$`\neg(a \prec_{\mathrm{p}} a)`$ である。よって両方向を示す。

- ($`\to`$) 左辺を仮定すると、第 1 選言は $`\neg(a \prec_{\mathrm{p}} a)`$ に反するから
  第 2 選言が成り立ち、
  $`(A' \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A' \mathbin{+\!\!+} v)`$ を得る。
  帰納法の仮定 $`\Phi(A')`$ の $`\to`$ 向きにより $`u \prec_{\mathrm{lex}} v`$。

- ($`\leftarrow`$) $`u \prec_{\mathrm{lex}} v`$ を仮定すると、帰納法の仮定 $`\Phi(A')`$ の
  $`\leftarrow`$ 向きにより
  $`(A' \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A' \mathbin{+\!\!+} v)`$ を得る。
  $`a = a`$ と合わせて第 2 選言が成り立つ。

よって $`\Phi(a :: A')`$。∎

<a id="t-seqlex_prefix"></a>
## 定理: 真の前部分列は小さい (T.seqlex_prefix)

### 定理

$`v \ne ()`$ ならば、任意の $`u \in \mathrm{PairSeq}`$ に対し
$`u \prec_{\mathrm{lex}} (u \mathbin{+\!\!+} v)`$。

### 証明

$`u`$ のリスト構造に関する帰納法（$`v`$ と仮定 $`v \ne ()`$ は固定する）。帰納法の述語は

```math
\Phi(u) :\equiv u \prec_{\mathrm{lex}} (u \mathbin{+\!\!+} v).
```

- **基底段** $`u = ()`$：$`() \mathbin{+\!\!+} v = v`$ であり、
  [T.seqlex_nil_iff](#t-seqlex_nil_iff) より $`() \prec_{\mathrm{lex}} v`$ は
  $`v \ne ()`$ と同値である。これは仮定である。

- **帰納段** $`u = a :: u'`$：帰納法の仮定は $`\Phi(u')`$、すなわち
  $`u' \prec_{\mathrm{lex}} (u' \mathbin{+\!\!+} v)`$ である。
  $`(a :: u') \mathbin{+\!\!+} v = a :: (u' \mathbin{+\!\!+} v)`$ であるから、
  [T.seqlex_cons_cons](#t-seqlex_cons_cons) の右辺の第 2 選言
  $`a = a \wedge u' \prec_{\mathrm{lex}} (u' \mathbin{+\!\!+} v)`$ が、$`=`$ の反射性と
  帰納法の仮定により成り立つ。よって $`\Phi(a :: u')`$。∎

<a id="d-steps1"></a>
## 定義: 行 0 の隣接段差 1 以下 (D.steps1)

$`B \in \mathrm{PairSeq}`$ に対し述語 $`\mathrm{steps}_1(B)`$ を、
先頭 2 要素の有無による場合分けで定める。

```math
\begin{aligned}
\mathrm{steps}_1(()) &:\iff \top, \cr
\mathrm{steps}_1((p)) &:\iff \top, \cr
\mathrm{steps}_1(p :: q :: r) &:\iff q_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(q :: r).
\end{aligned}
```

第 3 式の右辺の再帰呼び出しの引数 $`q :: r`$ は $`p :: q :: r`$ より長さが $`1`$ 短いから、
この定義は整合的である。

すなわち $`\mathrm{steps}_1(B)`$ は、隣り合う 2 列について、右の列の行 $`0`$ の値が
左の列の行 $`0`$ の値に $`1`$ を足した値以下であることを言う。

<a id="t-steps1_nil"></a>
## 定理: 空列の隣接段差 (T.steps1_nil)

### 定理

$`\mathrm{steps}_1(())`$。

### 証明

$`\mathrm{steps}_1`$ の定義（D.steps1）の第 1 式により $`\mathrm{steps}_1(())`$ は
$`\top`$ と定義により同一の命題であり、$`\top`$ は成り立つ。∎

<a id="t-steps1_single"></a>
## 定理: 1 列だけの列の隣接段差 (T.steps1_single)

### 定理

任意の $`p \in \mathbb{N}\times\mathbb{N}`$ に対し $`\mathrm{steps}_1((p))`$。

### 証明

$`\mathrm{steps}_1`$ の定義（D.steps1）の第 2 式により $`\mathrm{steps}_1((p))`$ は
$`\top`$ と定義により同一の命題であり、$`\top`$ は成り立つ。∎

<a id="t-steps1_cons_cons"></a>
## 定理: 先頭 2 要素での分解 (T.steps1_cons_cons)

### 定理

$`p, q \in \mathbb{N}\times\mathbb{N}`$、$`r \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{steps}_1(p :: q :: r) \iff q_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(q :: r).
```

### 証明

$`\mathrm{steps}_1`$ の定義（D.steps1）の第 3 式そのものであり、両辺は定義により
同一の命題である。∎

<a id="d-blockok"></a>
## 定義: 深さ $`d`$ のブロック (D.blockok)

型 $`\alpha`$ の有限列 $`L`$ の先頭要素を $`\mathrm{head}\,L`$ と書く。すなわち $`L \ne ()`$ のとき
$`\mathrm{head}\,L := L_0`$ であり、$`L = ()`$ のときは型 $`\alpha`$ ごとに定めた既定値をとる
（$`\alpha = \mathbb{N}\times\mathbb{N}`$ のとき既定値は $`(0,0)`$ である）。
$`B \in \mathrm{PairSeq}`$、$`d \in \mathbb{N}`$ に対し

```math
\mathrm{blockok}(d, B) :\iff
  \bigl(B \ne () \to (\mathrm{head}\,B)_1 = d\bigr)
  \ \wedge\ \bigl(\forall p \in B,\ d \le p_1\bigr)
  \ \wedge\ \mathrm{steps}_1(B).
```

$`\mathrm{blockok}(d, B)`$ が成り立つとき $`B`$ を**深さ $`d`$ のブロック**と呼ぶ。
第 1 の連言子は「$`B`$ が空でなければその先頭の行 $`0`$ の値はちょうど $`d`$」、
第 2 の連言子は「$`B`$ のすべての列の行 $`0`$ の値が $`d`$ 以上」、
第 3 の連言子は $`\mathrm{steps}_1`$ の定義（D.steps1）の内容である。

<a id="t-steps1_iff"></a>
## 定理: 隣接段差の添字による特徴づけ (T.steps1_iff)

### 定理

$`B \in \mathrm{PairSeq}`$、$`j \in \mathbb{N}`$ に対し
$`B\langle j\rangle`$（[D.entry](Pss.md#d-entry)）を $`B`$ の第 $`j`$ 要素
（$`j \ge \lvert B\rvert`$ のときは $`(0,0)`$）とする。このとき

```math
\mathrm{steps}_1(B) \iff
  \forall j,\ \Bigl(j + 1 \lt \lvert B\rvert \to
    (B\langle j+1\rangle)_1 \le (B\langle j\rangle)_1 + 1\Bigr).
```

### 証明

$`B`$ のリスト構造に関する帰納法。帰納法の述語は

```math
\Phi(B) :\equiv \Bigl(\mathrm{steps}_1(B) \iff
  \forall j,\ \bigl(j + 1 \lt \lvert B\rvert \to
    (B\langle j+1\rangle)_1 \le (B\langle j\rangle)_1 + 1\bigr)\Bigr).
```

- **基底段** $`B = ()`$：左辺は [T.steps1_nil](#t-steps1_nil) により成り立つ。
  右辺は $`\lvert B\rvert = 0`$ であるから前件 $`j + 1 \lt 0`$ をみたす $`j`$ が存在せず、
  成り立つ。両辺とも成り立つので同値である。

**帰納段** $`B = p :: B'`$：帰納法の仮定は $`\Phi(B')`$ である。$`B'`$ で場合分けする。

**(a) $`B' = ()`$ のとき。** 左辺 $`\mathrm{steps}_1((p))`$ は
[T.steps1_single](#t-steps1_single) により成り立つ。右辺は $`\lvert B\rvert = 1`$ であるから
前件 $`j + 1 \lt 1`$ をみたす $`j`$ が存在せず、成り立つ。両辺とも成り立つので同値である。

**(b) $`B' = q :: r`$ のとき。** このとき

```math
\lvert B\rvert = \lvert B'\rvert + 1,\qquad
B\langle 0\rangle = p,\qquad
B\langle j+1\rangle = B'\langle j\rangle \quad (\forall j),\qquad
B'\langle 0\rangle = q
```

である。第 1 の等式は $`B = p :: B'`$ による。第 2 と第 4 の等式は $`B`$, $`B'`$ の
第 $`0`$ 要素がそれぞれ $`p`$, $`q`$ であることによる。第 3 の等式は、
$`j \lt \lvert B'\rvert`$ のときは $`B`$ の第 $`j+1`$ 要素が $`B'`$ の第 $`j`$ 要素で
あること、$`j \ge \lvert B'\rvert`$ のときは $`j + 1 \ge \lvert B\rvert`$ であり両辺とも
$`(0,0)`$ であることによる。[T.steps1_cons_cons](#t-steps1_cons_cons) により左辺は

```math
q_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(B')
```

と同値であり、帰納法の仮定 $`\Phi(B')`$ によりこれはさらに

```math
q_1 \le p_1 + 1 \ \wedge\
  \forall j,\ \bigl(j + 1 \lt \lvert B'\rvert \to
    (B'\langle j+1\rangle)_1 \le (B'\langle j\rangle)_1 + 1\bigr)
```

と同値である。これが右辺と同値であることを両方向に示す。

- ($`\to`$) 上の連言を仮定し、$`j + 1 \lt \lvert B\rvert`$ なる $`j`$ を取る。
  $`j = 0`$ のとき、示すべきは $`(B\langle 1\rangle)_1 \le (B\langle 0\rangle)_1 + 1`$、
  すなわち $`q_1 \le p_1 + 1`$ であり、これは第 1 の連言子である。
  $`j = j' + 1`$ のとき、示すべきは
  $`(B'\langle j'+1\rangle)_1 \le (B'\langle j'\rangle)_1 + 1`$ である。
  $`j' + 2 \lt \lvert B\rvert = \lvert B'\rvert + 1`$ より $`j' + 1 \lt \lvert B'\rvert`$ で
  あるから、第 2 の連言子を $`j'`$ に適用すればよい。

- ($`\leftarrow`$) 右辺を仮定する。第 1 の連言子については、
  $`\lvert B\rvert = \lvert B'\rvert + 1 \ge 2`$ より $`0 + 1 \lt \lvert B\rvert`$ であるから、
  右辺を $`j := 0`$ に適用して
  $`(B\langle 1\rangle)_1 \le (B\langle 0\rangle)_1 + 1`$、すなわち $`q_1 \le p_1 + 1`$ を得る。
  第 2 の連言子については、$`j + 1 \lt \lvert B'\rvert`$ なる $`j`$ を取ると
  $`(j+1) + 1 \lt \lvert B'\rvert + 1 = \lvert B\rvert`$ であるから、右辺を $`j + 1`$ に
  適用して $`(B\langle j+2\rangle)_1 \le (B\langle j+1\rangle)_1 + 1`$、すなわち
  $`(B'\langle j+1\rangle)_1 \le (B'\langle j\rangle)_1 + 1`$ を得る。

よって $`\Phi(p :: B')`$。∎

<a id="t-steps1_tail"></a>
## 定理: 尾部の隣接段差 (T.steps1_tail)

### 定理

$`\mathrm{steps}_1(p :: r)`$ ならば $`\mathrm{steps}_1(r)`$。

### 証明

$`r`$ の構成子で場合分けする。

- $`r = ()`$ のとき。[T.steps1_nil](#t-steps1_nil) による。

- $`r = q :: r'`$ のとき。仮定は $`\mathrm{steps}_1(p :: q :: r')`$ であり、
  [T.steps1_cons_cons](#t-steps1_cons_cons) の右辺の第 2 の連言子が
  $`\mathrm{steps}_1(q :: r') = \mathrm{steps}_1(r)`$ である。∎

<a id="t-steps1_append"></a>
## 定理: 連結の隣接段差 (T.steps1_append)

### 定理

型 $`\alpha`$ の有限列 $`L`$ と $`d \in \alpha`$ に対し

```math
\mathrm{last}_d\,L := \begin{cases} d & (L = ()) \cr L_{\lvert L\rvert - 1} & (L \ne ()) \end{cases}
```

とおく（減法は自然数の切り捨て減法である）。$`A, B \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{steps}_1(A \mathbin{+\!\!+} B) \iff
  \mathrm{steps}_1(A) \ \wedge\ \mathrm{steps}_1(B) \ \wedge\
  \Bigl(A = () \ \vee\ B = () \ \vee\
    (\mathrm{head}\,B)_1 \le (\mathrm{last}_{(0,0)} A)_1 + 1\Bigr).
```

### 証明

$`A`$ のリスト構造に関する帰納法（$`B`$ は固定する）。帰納法の述語は

```math
\Phi(A) :\equiv \Bigl(\mathrm{steps}_1(A \mathbin{+\!\!+} B) \iff
  \mathrm{steps}_1(A) \wedge \mathrm{steps}_1(B) \wedge
  \bigl(A = () \vee B = () \vee
    (\mathrm{head}\,B)_1 \le (\mathrm{last}_{(0,0)} A)_1 + 1\bigr)\Bigr).
```

- **基底段** $`A = ()`$：$`() \mathbin{+\!\!+} B = B`$ であるから左辺は $`\mathrm{steps}_1(B)`$ で
  ある。右辺の第 1 の連言子は [T.steps1_nil](#t-steps1_nil) により成り立ち、第 3 の連言子は
  その第 1 選言 $`A = ()`$ により成り立つから、右辺も $`\mathrm{steps}_1(B)`$ と同値である。

**帰納段** $`A = p :: A'`$：帰納法の仮定は $`\Phi(A')`$ である。$`A'`$ で場合分けする。

**(a) $`A' = ()`$ のとき。** $`A = (p)`$、$`A \mathbin{+\!\!+} B = p :: B`$ であり、
$`\mathrm{last}_{(0,0)} A = p`$、$`A = ()`$ は偽である。さらに $`B`$ で場合分けする。

**(a-1) $`B = ()`$ のとき。** 左辺は $`\mathrm{steps}_1((p))`$ であり
[T.steps1_single](#t-steps1_single) により成り立つ。右辺は、第 1 の連言子が
[T.steps1_single](#t-steps1_single)、第 2 の連言子が [T.steps1_nil](#t-steps1_nil)、
第 3 の連言子がその第 2 選言 $`B = ()`$ によりそれぞれ成り立つ。
両辺とも成り立つので同値である。

**(a-2) $`B = q :: B'`$ のとき。** $`\mathrm{head}\,B = q`$ である。
[T.steps1_cons_cons](#t-steps1_cons_cons) により左辺は
$`q_1 \le p_1 + 1 \wedge \mathrm{steps}_1(B)`$ と同値である。
右辺は、第 1 の連言子が [T.steps1_single](#t-steps1_single) により成り立ち、
第 3 の連言子は第 1 選言 $`A = ()`$ も第 2 選言 $`B = ()`$ も偽であるから
第 3 選言 $`q_1 \le p_1 + 1`$ と同値である。よって右辺も
$`q_1 \le p_1 + 1 \wedge \mathrm{steps}_1(B)`$ と同値であり、両辺は同値である。

**(b) $`A' = p' :: A''`$ のとき。** このとき

```math
A \mathbin{+\!\!+} B = p :: (A' \mathbin{+\!\!+} B),\qquad
A' \mathbin{+\!\!+} B = p' :: (A'' \mathbin{+\!\!+} B),\qquad
\mathrm{last}_{(0,0)} A = \mathrm{last}_{(0,0)} A'
```

である（第 3 の等式は $`A' \ne ()`$ による。$`A = p :: A'`$ の最後の要素は $`A'`$ の
最後の要素である）。また $`A = ()`$ と $`A' = ()`$ はいずれも偽である。
[T.steps1_cons_cons](#t-steps1_cons_cons) を 2 回用いて

```math
\mathrm{steps}_1(A \mathbin{+\!\!+} B) \iff
  p'_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(A' \mathbin{+\!\!+} B),
```
```math
\mathrm{steps}_1(A) \iff p'_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(A')
```

を得る。したがって右辺は

```math
p'_1 \le p_1 + 1 \ \wedge\ \Bigl(\mathrm{steps}_1(A') \wedge \mathrm{steps}_1(B) \wedge
  \bigl(A' = () \vee B = () \vee
    (\mathrm{head}\,B)_1 \le (\mathrm{last}_{(0,0)} A')_1 + 1\bigr)\Bigr)
```

と同値である。実際、$`A = ()`$ と $`A' = ()`$ がともに偽であるから第 3 の連言子の
選言の並びは一致し、$`\mathrm{last}_{(0,0)} A = \mathrm{last}_{(0,0)} A'`$ から第 3 選言も一致する。
あとは連言の結合順序を組み替えただけである。大きい括弧の中は帰納法の仮定 $`\Phi(A')`$ により
$`\mathrm{steps}_1(A' \mathbin{+\!\!+} B)`$ と同値であるから、右辺は

```math
p'_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(A' \mathbin{+\!\!+} B)
```

と同値であり、これは上の第 1 の同値により左辺と同値である。よって $`\Phi(p :: A')`$。∎

<a id="t-steps1_dropLast"></a>
## 定理: 末尾を落としても隣接段差は保たれる (T.steps1_dropLast)

### 定理

$`\mathrm{steps}_1(B)`$ ならば $`\mathrm{steps}_1(\mathrm{dropLast}\,B)`$。
ここで $`\mathrm{dropLast}\,B`$ は $`B`$ の末尾 1 要素を落とした列である
（$`B = ()`$ のときは $`()`$）。

### 証明

$`B = ()`$ かどうかで場合分けする。

**(a) $`B = ()`$ のとき。** $`\mathrm{dropLast}\,() = ()`$ であり、
[T.steps1_nil](#t-steps1_nil) による。

**(b) $`B \ne ()`$ のとき。** $`B`$ の最後の要素を $`\ell`$ とすると

```math
B = \mathrm{dropLast}\,B \mathbin{+\!\!+} (\ell)
```

である。仮定 $`\mathrm{steps}_1(B)`$ にこの書き換えを行い、
[T.steps1_append](#t-steps1_append) の $`\to`$ 向きを
$`A := \mathrm{dropLast}\,B`$、$`B := (\ell)`$ として適用すると、その第 1 の連言子が
$`\mathrm{steps}_1(\mathrm{dropLast}\,B)`$ である。∎

<a id="t-blockok_dropLast"></a>
## 定理: 末尾を落としてもブロックである (T.blockok_dropLast)

### 定理

$`\mathrm{blockok}(d, B)`$ ならば $`\mathrm{blockok}(d, \mathrm{dropLast}\,B)`$。

### 証明

$`\mathrm{blockok}`$ の定義（D.blockok）の 3 つの連言子を順に示す。仮定から
$`B \ne () \to (\mathrm{head}\,B)_1 = d`$、$`\forall p \in B,\ d \le p_1`$、
$`\mathrm{steps}_1(B)`$ が得られている。

**第 3 の連言子。** [T.steps1_dropLast](#t-steps1_dropLast) を $`\mathrm{steps}_1(B)`$ に
適用する。

**第 2 の連言子。** $`p \in \mathrm{dropLast}\,B`$ とする。$`B = ()`$ なら
$`\mathrm{dropLast}\,B = ()`$ は要素をもたないから、$`B \ne ()`$ であり、その最後の要素を
$`\ell`$ とすると $`B = \mathrm{dropLast}\,B \mathbin{+\!\!+} (\ell)`$ である。よって
$`p \in B`$ であり、仮定より $`d \le p_1`$。

**第 1 の連言子。** $`\mathrm{dropLast}\,B \ne ()`$ とする。$`B = ()`$ なら
$`\mathrm{dropLast}\,B = ()`$ となり仮定に反するから $`B \ne ()`$ であり、
$`B = x :: xs`$ と書ける。ここで $`xs \ne ()`$ である。実際 $`xs = ()`$ とすると
$`B = (x)`$ であり $`\mathrm{dropLast}\,B = ()`$ となって仮定に反する。
$`xs \ne ()`$ のとき $`\mathrm{dropLast}(x :: xs) = x :: \mathrm{dropLast}\,xs`$ であるから

```math
\mathrm{head}\,(\mathrm{dropLast}\,B) = x = \mathrm{head}\,B
```

であり、$`B \ne ()`$ に仮定の第 1 の連言子を適用して
$`(\mathrm{head}\,B)_1 = d`$、すなわち $`x_1 = d`$ を得る。∎

<a id="t-blockok_arg"></a>
## 定理: 行 0 の値が $`d`$ より大きい極大な前部分列はブロック (T.blockok_arg)

### 定理

$`d, y \in \mathbb{N}`$、$`r \in \mathrm{PairSeq}`$ とする。
$`\mathrm{blockok}\bigl(d, (d,y) :: r\bigr)`$ ならば
$`\mathrm{blockok}\bigl(d+1,\ \mathrm{tw}_d r\bigr)`$（[D.translate](Term.md#d-translate)）。

### 証明

仮定から $`\forall p \in (d,y) :: r,\ d \le p_1`$ と
$`\mathrm{steps}_1\bigl((d,y) :: r\bigr)`$ が得られている。
$`\mathrm{blockok}`$ の定義（D.blockok）の 3 つの連言子を順に示す。

**第 1 の連言子。** $`\mathrm{tw}_d r \ne ()`$ とする。$`\mathrm{tw}`$ の定義（D.translate）より
$`\mathrm{tw}_d\,() = ()`$ であるから $`r \ne ()`$ であり、$`r = p' :: r'`$ と書ける。
$`\mathrm{tw}`$ の定義（D.translate）より、$`\neg(d \lt p'_1)`$ ならば
$`\mathrm{tw}_d(p' :: r') = ()`$ となって仮定に反する。よって $`d \lt p'_1`$ であり、
このとき $`\mathrm{tw}_d(p' :: r') = p' :: \mathrm{tw}_d r'`$ であるから

```math
\mathrm{head}\,(\mathrm{tw}_d r) = p' .
```

一方 $`\mathrm{steps}_1\bigl((d,y) :: p' :: r'\bigr)`$ に
[T.steps1_cons_cons](#t-steps1_cons_cons) を適用すると、その第 1 の連言子は
$`p'_1 \le d + 1`$ である。$`d \lt p'_1`$ は $`d + 1 \le p'_1`$ であるから、
$`\le`$ の反対称性により $`p'_1 = d + 1`$ を得る。

**第 2 の連言子。** $`q \in \mathrm{tw}_d r`$ とする。$`\mathrm{tw}`$ の定義（D.translate）より
$`\mathrm{tw}_d r`$ の要素はすべて述語 $`d \lt x_1`$ をみたすから $`d \lt q_1`$、
すなわち $`d + 1 \le q_1`$ である。

**第 3 の連言子。** $`\mathrm{tw}`$ と $`\mathrm{dw}`$ の定義（D.translate）より
$`\mathrm{tw}_d r \mathbin{+\!\!+} \mathrm{dw}_d r = r`$ である。
[T.steps1_tail](#t-steps1_tail) を $`\mathrm{steps}_1\bigl((d,y) :: r\bigr)`$ に適用して
$`\mathrm{steps}_1(r)`$ を得るから、
$`\mathrm{steps}_1\bigl(\mathrm{tw}_d r \mathbin{+\!\!+} \mathrm{dw}_d r\bigr)`$ が成り立つ。
[T.steps1_append](#t-steps1_append) の $`\to`$ 向きを適用すると、その第 1 の連言子が
$`\mathrm{steps}_1(\mathrm{tw}_d r)`$ である。∎

<a id="t-blockok_tail"></a>
## 定理: その前部分列を除いた残りもブロック (T.blockok_tail)

### 定理

$`d, y \in \mathbb{N}`$、$`r \in \mathrm{PairSeq}`$ とする。
$`\mathrm{blockok}\bigl(d, (d,y) :: r\bigr)`$ ならば
$`\mathrm{blockok}\bigl(d,\ \mathrm{dw}_d r\bigr)`$。

### 証明

仮定から $`\forall p \in (d,y) :: r,\ d \le p_1`$ と
$`\mathrm{steps}_1\bigl((d,y) :: r\bigr)`$ が得られている。
$`\mathrm{blockok}`$ の定義（D.blockok）の 3 つの連言子を順に示す。

**第 1 の連言子。** $`\mathrm{dw}_d r \ne ()`$ とし、その先頭要素を $`a`$ とする。
$`\mathrm{dw}`$ の定義（D.translate）より、$`\mathrm{dw}_d r`$ が空でなければその先頭要素は
述語 $`d \lt x_1`$ を破るから $`\neg(d \lt a_1)`$、すなわち $`a_1 \le d`$ である。
また $`\mathrm{dw}_d r`$ は $`r`$ の部分列であるから $`a \in r`$ であり、
$`a \in (d,y) :: r`$ である。仮定の第 2 の連言子より $`d \le a_1`$。
$`\le`$ の反対称性により $`a_1 = d`$、すなわち
$`(\mathrm{head}\,(\mathrm{dw}_d r))_1 = d`$ を得る。

**第 2 の連言子。** $`q \in \mathrm{dw}_d r`$ とする。$`\mathrm{dw}_d r`$ は $`r`$ の部分列で
あるから $`q \in r`$、したがって $`q \in (d,y) :: r`$ であり、仮定より $`d \le q_1`$。

**第 3 の連言子。** $`\mathrm{tw}`$ と $`\mathrm{dw}`$ の定義（D.translate）より
$`\mathrm{tw}_d r \mathbin{+\!\!+} \mathrm{dw}_d r = r`$ である。
[T.steps1_tail](#t-steps1_tail) を $`\mathrm{steps}_1\bigl((d,y) :: r\bigr)`$ に適用して
$`\mathrm{steps}_1(r)`$ を得るから、
$`\mathrm{steps}_1\bigl(\mathrm{tw}_d r \mathbin{+\!\!+} \mathrm{dw}_d r\bigr)`$ が成り立つ。
[T.steps1_append](#t-steps1_append) の $`\to`$ 向きを適用すると、その第 2 の連言子が
$`\mathrm{steps}_1(\mathrm{dw}_d r)`$ である。∎

<a id="t-seqlex_arg_or_tail"></a>
## 定理: 最初の差は前部分列側か残り側のどちらかに現れる (T.seqlex_arg_or_tail)

### 定理

$`d \in \mathbb{N}`$、$`r, r' \in \mathrm{PairSeq}`$ とする。
$`r \prec_{\mathrm{lex}} r'`$ ならば、次の 2 つのいずれかが成り立つ。

```math
\begin{aligned}
&\text{(T)}\quad \mathrm{tw}_d r = \mathrm{tw}_d r' \ \wedge\
  \mathrm{dw}_d r \prec_{\mathrm{lex}} \mathrm{dw}_d r', \cr
&\text{(A)}\quad \mathrm{tw}_d r \ne \mathrm{tw}_d r' \ \wedge\
  \mathrm{tw}_d r \prec_{\mathrm{lex}} \mathrm{tw}_d r' .
\end{aligned}
```

### 証明

$`r`$ のリスト構造に関する帰納法（$`r'`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(r) :\equiv \forall r' \in \mathrm{PairSeq},\
  r \prec_{\mathrm{lex}} r' \to \bigl(\text{(T)} \vee \text{(A)}\bigr).
```

以下、$`\mathrm{tw}`$ と $`\mathrm{dw}`$ の定義（D.translate）から従う次の 4 つの等式を用いる。
$`d \lt p_1`$ のとき

```math
\mathrm{tw}_d(p :: L) = p :: \mathrm{tw}_d L, \qquad
\mathrm{dw}_d(p :: L) = \mathrm{dw}_d L
```

であり、$`\neg(d \lt p_1)`$ のとき

```math
\mathrm{tw}_d(p :: L) = (), \qquad
\mathrm{dw}_d(p :: L) = p :: L
```

である。

**基底段** $`r = ()`$：$`r'`$ を取り $`() \prec_{\mathrm{lex}} r'`$ とする。
[T.seqlex_nil_iff](#t-seqlex_nil_iff) より $`r' \ne ()`$ である。
$`\mathrm{tw}`$ と $`\mathrm{dw}`$ の定義（D.translate）より
$`\mathrm{tw}_d\,() = ()`$、$`\mathrm{dw}_d\,() = ()`$ である。
$`\mathrm{tw}_d r'`$ が空かどうかで場合分けする。

**(i) $`\mathrm{tw}_d r' = ()`$ のとき。** (T) を示す。第 1 の連言子は
$`\mathrm{tw}_d\,() = () = \mathrm{tw}_d r'`$ である。第 2 の連言子については、
まず $`\mathrm{dw}_d r' = r'`$ を示す。$`r' \ne ()`$ より $`r' = q :: t`$ と書ける。
$`d \lt q_1`$ とすると $`\mathrm{tw}_d r' = q :: \mathrm{tw}_d t \ne ()`$ となり
仮定に反するから $`\neg(d \lt q_1)`$ であり、$`\mathrm{dw}_d(q :: t) = q :: t = r'`$ である。
したがって示すべきは $`() \prec_{\mathrm{lex}} r'`$ であり、
[T.seqlex_nil_iff](#t-seqlex_nil_iff) と $`r' \ne ()`$ による。

**(ii) $`\mathrm{tw}_d r' \ne ()`$ のとき。** (A) を示す。第 1 の連言子は
$`\mathrm{tw}_d\,() = ()`$ と仮定 $`\mathrm{tw}_d r' \ne ()`$ から得られる。
第 2 の連言子 $`() \prec_{\mathrm{lex}} \mathrm{tw}_d r'`$ は
[T.seqlex_nil_iff](#t-seqlex_nil_iff) と仮定 $`\mathrm{tw}_d r' \ne ()`$ による。

**帰納段** $`r = p :: rr`$：帰納法の仮定は $`\Phi(rr)`$、すなわち

```math
\forall r'',\ rr \prec_{\mathrm{lex}} r'' \to
  \Bigl(\bigl(\mathrm{tw}_d rr = \mathrm{tw}_d r'' \wedge
    \mathrm{dw}_d rr \prec_{\mathrm{lex}} \mathrm{dw}_d r''\bigr) \vee
  \bigl(\mathrm{tw}_d rr \ne \mathrm{tw}_d r'' \wedge
    \mathrm{tw}_d rr \prec_{\mathrm{lex}} \mathrm{tw}_d r''\bigr)\Bigr)
```

である。$`r'`$ を取り $`(p :: rr) \prec_{\mathrm{lex}} r'`$ とする。
$`r' = ()`$ とすると [T.not_seqlex_nil](#t-not_seqlex_nil) に反するから
$`r' = q :: rr'`$ と書ける。$`p = q`$ かどうかで場合分けする。

**(a) $`p = q`$ のとき。** 以下 $`q`$ を $`p`$ に書き換える。すなわち $`r' = p :: rr'`$ で
ある。[T.seqlex_cons_cons](#t-seqlex_cons_cons) より
$`p \prec_{\mathrm{p}} p`$ または $`p = p \wedge rr \prec_{\mathrm{lex}} rr'`$ である。
$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）より $`p \prec_{\mathrm{p}} p`$ は
$`p_1 \lt p_1`$ または $`p_1 = p_1 \wedge p_2 \lt p_2`$ であり、$`\mathbb{N}`$ の $`\lt`$ の
非反射性によりどちらも偽である。よって $`rr \prec_{\mathrm{lex}} rr'`$ を得る。
さらに $`d \lt p_1`$ かどうかで場合分けする。

**(a-1) $`d \lt p_1`$ のとき。** このとき

```math
\mathrm{tw}_d(p :: rr) = p :: \mathrm{tw}_d rr, \qquad
\mathrm{dw}_d(p :: rr) = \mathrm{dw}_d rr,
```
```math
\mathrm{tw}_d(p :: rr') = p :: \mathrm{tw}_d rr', \qquad
\mathrm{dw}_d(p :: rr') = \mathrm{dw}_d rr'
```

である。帰納法の仮定を $`r'' := rr'`$ と $`rr \prec_{\mathrm{lex}} rr'`$ に適用し、
その結論の選言で場合分けする。

- (T) が成り立つとき、すなわち $`\mathrm{tw}_d rr = \mathrm{tw}_d rr'`$ かつ
  $`\mathrm{dw}_d rr \prec_{\mathrm{lex}} \mathrm{dw}_d rr'`$ のとき。
  結論の (T) を示す。第 1 の連言子は
  $`p :: \mathrm{tw}_d rr = p :: \mathrm{tw}_d rr'`$ であり、
  $`\mathrm{tw}_d rr = \mathrm{tw}_d rr'`$ から従う。第 2 の連言子は
  $`\mathrm{dw}_d rr \prec_{\mathrm{lex}} \mathrm{dw}_d rr'`$ そのものである。

- (A) が成り立つとき、すなわち $`\mathrm{tw}_d rr \ne \mathrm{tw}_d rr'`$ かつ
  $`\mathrm{tw}_d rr \prec_{\mathrm{lex}} \mathrm{tw}_d rr'`$ のとき。
  結論の (A) を示す。第 1 の連言子は、
  $`p :: \mathrm{tw}_d rr = p :: \mathrm{tw}_d rr'`$ と仮定すると構成子 $`::`$ の単射性より
  $`\mathrm{tw}_d rr = \mathrm{tw}_d rr'`$ となって矛盾することによる。
  第 2 の連言子は、[T.seqlex_cons_cons](#t-seqlex_cons_cons) の右辺の第 2 選言
  $`p = p \wedge \mathrm{tw}_d rr \prec_{\mathrm{lex}} \mathrm{tw}_d rr'`$ による。

**(a-2) $`\neg(d \lt p_1)`$ のとき。** このとき

```math
\mathrm{tw}_d(p :: rr) = () = \mathrm{tw}_d(p :: rr'), \qquad
\mathrm{dw}_d(p :: rr) = p :: rr, \qquad
\mathrm{dw}_d(p :: rr') = p :: rr'
```

である。結論の (T) を示す。第 1 の連言子は上の等式である。第 2 の連言子
$`(p :: rr) \prec_{\mathrm{lex}} (p :: rr')`$ は仮定
$`(p :: rr) \prec_{\mathrm{lex}} r'`$ そのものである。

**(b) $`p \ne q`$ のとき。** [T.seqlex_cons_cons](#t-seqlex_cons_cons) より
$`p \prec_{\mathrm{p}} q`$ または $`p = q \wedge rr \prec_{\mathrm{lex}} rr'`$ であり、
第 2 選言は $`p \ne q`$ に反するから $`p \prec_{\mathrm{p}} q`$ である。
$`d \lt p_1`$ と $`d \lt q_1`$ の成否で場合分けする。

**(b-1) $`d \lt p_1`$ のとき。** $`\prec_{\mathrm{p}}`$ の定義（D.pairlt）より
$`p_1 \lt q_1`$ または $`p_1 = q_1`$ であり、いずれの場合も $`p_1 \le q_1`$ であるから
$`d \lt p_1 \le q_1`$、すなわち $`d \lt q_1`$ である。よって

```math
\mathrm{tw}_d(p :: rr) = p :: \mathrm{tw}_d rr, \qquad
\mathrm{tw}_d(q :: rr') = q :: \mathrm{tw}_d rr'
```

である。結論の (A) を示す。第 1 の連言子は、
$`p :: \mathrm{tw}_d rr = q :: \mathrm{tw}_d rr'`$ と仮定すると構成子 $`::`$ の単射性より
$`p = q`$ となって $`p \ne q`$ に矛盾することによる。第 2 の連言子は、
[T.seqlex_cons_cons](#t-seqlex_cons_cons) の右辺の第 1 選言 $`p \prec_{\mathrm{p}} q`$ による。

**(b-2) $`\neg(d \lt p_1)`$ かつ $`d \lt q_1`$ のとき。** このとき

```math
\mathrm{tw}_d(p :: rr) = (), \qquad
\mathrm{tw}_d(q :: rr') = q :: \mathrm{tw}_d rr'
```

である。結論の (A) を示す。第 1 の連言子は、$`q :: \mathrm{tw}_d rr'`$ が空でないことによる。
第 2 の連言子 $`() \prec_{\mathrm{lex}} (q :: \mathrm{tw}_d rr')`$ は
[T.seqlex_nil_iff](#t-seqlex_nil_iff) と $`q :: \mathrm{tw}_d rr' \ne ()`$ による。

**(b-3) $`\neg(d \lt p_1)`$ かつ $`\neg(d \lt q_1)`$ のとき。** このとき

```math
\mathrm{tw}_d(p :: rr) = () = \mathrm{tw}_d(q :: rr'), \qquad
\mathrm{dw}_d(p :: rr) = p :: rr, \qquad
\mathrm{dw}_d(q :: rr') = q :: rr'
```

である。結論の (T) を示す。第 1 の連言子は上の等式である。第 2 の連言子
$`(p :: rr) \prec_{\mathrm{lex}} (q :: rr')`$ は仮定
$`(p :: rr) \prec_{\mathrm{lex}} r'`$ そのものである。

以上で (a-1), (a-2), (b-1), (b-2), (b-3) のすべての場合に (T) か (A) が示されたので
$`\Phi(p :: rr)`$。∎
