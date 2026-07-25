[← README](README.md)

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

<a id="t-seqlex_imp_olt"></a>
## 定理: 列辞書式順序から項の順序へ (T.seqlex_imp_olt)

### 定理

$`d \in \mathbb{N}`$、$`M, N \in \mathrm{PairSeq}`$ とする。
$`\mathrm{blockok}(d, M)`$、$`\mathrm{blockok}(d, N)`$、$`M \prec_{\mathrm{lex}} N`$ ならば

```math
\mathrm{tr}\,M \prec \mathrm{tr}\,N .
```

### 証明

$`\lvert M\rvert + \lvert N\rvert`$ に関する強帰納法を行う。深さ $`d`$ は再帰の途中で
$`d`$ から $`d+1`$ へ動くので、帰納法の述語では $`d`$ を全称量化しておく。すなわち

```math
\Phi(M, N) :\equiv \forall d \in \mathbb{N},\
  \bigl(\mathrm{blockok}(d,M) \wedge \mathrm{blockok}(d,N) \wedge M \prec_{\mathrm{lex}} N\bigr)
  \to \mathrm{tr}\,M \prec \mathrm{tr}\,N
```

とおき、帰納法の仮定は
「$`\lvert M'\rvert + \lvert N'\rvert \lt \lvert M\rvert + \lvert N\rvert`$ なるすべての $`M', N'`$ について $`\Phi(M', N')`$」である。

$`M`$ と $`N`$ の構成子で 4 通りに場合分けする。

**(1) $`M = ()`$、$`N = ()`$ のとき。**
$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式により $`() \prec_{\mathrm{lex}} ()`$ は $`() \ne ()`$ と
同一の命題であり、$`=`$ の反射性に矛盾する。よって前件が偽である。

**(2) $`M = ()`$、$`N = q :: N'`$ のとき。**
$`\mathrm{tr}`$ の定義（D.translate）の第 1 式より $`\mathrm{tr}\,() = \mathsf{Z}`$（[D.Three](Term.md#d-Three)）であり、
第 2 式より $`\mathrm{tr}(q :: N') = \mathsf{P}\bigl(q_2, \mathrm{tr}(\mathrm{tw}_{q_1}N'), \mathrm{tr}(\mathrm{dw}_{q_1}N')\bigr)`$
である。[T.olt_Z_P](Term.md#t-olt_Z_P) より $`\mathsf{Z} \prec \mathsf{P}(\cdot,\cdot,\cdot)`$。

**(3) $`M = p :: r`$、$`N = ()`$ のとき。**
[T.not_seqlex_nil](#t-not_seqlex_nil) より $`(p :: r) \prec_{\mathrm{lex}} ()`$ は偽であり、前件が偽である。

**(4) $`M = p :: r`$、$`N = q :: r'`$ のとき。**
$`\mathrm{blockok}(d, p :: r)`$ の第 1 の連言子を $`p :: r \ne ()`$ に適用すると
$`\bigl(\mathrm{head}(p :: r)\bigr)_1 = d`$、すなわち $`p_1 = d`$ を得る。
$`\mathrm{blockok}(d, q :: r')`$ の第 1 の連言子を $`q :: r' \ne ()`$ に適用すると
$`\bigl(\mathrm{head}(q :: r')\bigr)_1 = d`$、すなわち $`q_1 = d`$ を得る。
そこで $`y := p_2`$、$`y' := q_2`$ とおけば $`p = (d, y)`$、$`q = (d, y')`$ と書ける。
$`\mathrm{tr}`$ の定義（D.translate）の第 2 式より

```math
\mathrm{tr}\bigl((d,y) :: r\bigr)
  = \mathsf{P}\bigl(y,\ \mathrm{tr}(\mathrm{tw}_{d}\,r),\ \mathrm{tr}(\mathrm{dw}_{d}\,r)\bigr),
```
```math
\mathrm{tr}\bigl((d,y') :: r'\bigr)
  = \mathsf{P}\bigl(y',\ \mathrm{tr}(\mathrm{tw}_{d}\,r'),\ \mathrm{tr}(\mathrm{dw}_{d}\,r')\bigr)
```

である。$`y`$ と $`y'`$ が等しいかどうかで場合分けする。

**(4a) $`y = y'`$ のとき。**
[T.seqlex_cons_cons](#t-seqlex_cons_cons) より、仮定 $`(d,y) :: r \prec_{\mathrm{lex}} (d,y) :: r'`$ は
$`(d,y) \prec_{\mathrm{p}} (d,y)`$ または $`\bigl((d,y) = (d,y) \wedge r \prec_{\mathrm{lex}} r'\bigr)`$ である。
第 1 の選言は $`\prec_{\mathrm{p}}`$ の定義（D.pairlt）より $`d \lt d`$ または
$`(d = d \wedge y \lt y)`$ であり、$`\lt`$ の非反射性によりいずれも偽である。
よって $`r \prec_{\mathrm{lex}} r'`$ が成り立つ。

[T.seqlex_arg_or_tail](#t-seqlex_arg_or_tail) を $`d`$ と $`r \prec_{\mathrm{lex}} r'`$ に適用すると、
次のいずれかが成り立つ。

- (i) $`\mathrm{tw}_d\,r = \mathrm{tw}_d\,r'`$ かつ $`\mathrm{dw}_d\,r \prec_{\mathrm{lex}} \mathrm{dw}_d\,r'`$
- (ii) $`\mathrm{tw}_d\,r \ne \mathrm{tw}_d\,r'`$ かつ $`\mathrm{tw}_d\,r \prec_{\mathrm{lex}} \mathrm{tw}_d\,r'`$

**(i) のとき。**[T.blockok_tail](#t-blockok_tail) を $`\mathrm{blockok}(d, (d,y) :: r)`$ と
$`\mathrm{blockok}(d, (d,y) :: r')`$ に適用すると $`\mathrm{blockok}(d, \mathrm{dw}_d\,r)`$ と
$`\mathrm{blockok}(d, \mathrm{dw}_d\,r')`$ を得る。$`\mathrm{tw}`$ と $`\mathrm{dw}`$ の定義（D.translate）より
$`\mathrm{tw}_d\,r \mathbin{+\!\!+} \mathrm{dw}_d\,r = r`$ であるから
$`\lvert \mathrm{dw}_d\,r\rvert \le \lvert \mathrm{tw}_d\,r\rvert + \lvert \mathrm{dw}_d\,r\rvert = \lvert r\rvert`$ であり、
同じ等式を $`r'`$ について用いて
$`\lvert \mathrm{dw}_d\,r'\rvert \le \lvert \mathrm{tw}_d\,r'\rvert + \lvert \mathrm{dw}_d\,r'\rvert = \lvert r'\rvert`$ である。よって

```math
\lvert \mathrm{dw}_d\,r\rvert + \lvert \mathrm{dw}_d\,r'\rvert
  \le \lvert r\rvert + \lvert r'\rvert
  \lt \lvert (d,y) :: r\rvert + \lvert (d,y) :: r'\rvert
```

である。よって帰納法の仮定を $`(\mathrm{dw}_d\,r, \mathrm{dw}_d\,r')`$ に、深さ $`d`$ で適用でき、

```math
\mathrm{tr}(\mathrm{dw}_d\,r) \prec \mathrm{tr}(\mathrm{dw}_d\,r')
```

を得る。(i) の第 1 の連言子より $`\mathrm{tr}(\mathrm{tw}_d\,r) = \mathrm{tr}(\mathrm{tw}_d\,r')`$ であるから、
[T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 3 選言
$`y = y \wedge \mathrm{tr}(\mathrm{tw}_d r) = \mathrm{tr}(\mathrm{tw}_d r') \wedge \mathrm{tr}(\mathrm{dw}_d r) \prec \mathrm{tr}(\mathrm{dw}_d r')`$
が成り立ち、結論が従う。

**(ii) のとき。**[T.blockok_arg](#t-blockok_arg) を同じ 2 つの仮定に適用すると
$`\mathrm{blockok}(d+1, \mathrm{tw}_d\,r)`$ と $`\mathrm{blockok}(d+1, \mathrm{tw}_d\,r')`$ を得る。
$`\mathrm{tw}`$ と $`\mathrm{dw}`$ の定義（D.translate）より
$`\mathrm{tw}_d\,r \mathbin{+\!\!+} \mathrm{dw}_d\,r = r`$ であるから
$`\lvert \mathrm{tw}_d\,r\rvert \le \lvert \mathrm{tw}_d\,r\rvert + \lvert \mathrm{dw}_d\,r\rvert = \lvert r\rvert`$ であり、
同じ等式を $`r'`$ について用いて
$`\lvert \mathrm{tw}_d\,r'\rvert \le \lvert \mathrm{tw}_d\,r'\rvert + \lvert \mathrm{dw}_d\,r'\rvert = \lvert r'\rvert`$ である。よって

```math
\lvert \mathrm{tw}_d\,r\rvert + \lvert \mathrm{tw}_d\,r'\rvert
  \le \lvert r\rvert + \lvert r'\rvert
  \lt \lvert (d,y) :: r\rvert + \lvert (d,y) :: r'\rvert
```

である。よって帰納法の仮定を $`(\mathrm{tw}_d\,r, \mathrm{tw}_d\,r')`$ に、深さ $`d+1`$ で適用でき、

```math
\mathrm{tr}(\mathrm{tw}_d\,r) \prec \mathrm{tr}(\mathrm{tw}_d\,r')
```

を得る。[T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 2 選言
$`y = y \wedge \mathrm{tr}(\mathrm{tw}_d r) \prec \mathrm{tr}(\mathrm{tw}_d r')`$ が成り立ち、結論が従う。

**(4b) $`y \ne y'`$ のとき。**
[T.seqlex_cons_cons](#t-seqlex_cons_cons) より、仮定は
$`(d,y) \prec_{\mathrm{p}} (d,y')`$ または $`\bigl((d,y) = (d,y') \wedge r \prec_{\mathrm{lex}} r'\bigr)`$ である。
第 2 の選言が成り立つとすると、対の構成子の単射性より $`y = y'`$ となり仮定に矛盾する。
よって $`(d,y) \prec_{\mathrm{p}} (d,y')`$ であり、$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）より
$`d \lt d`$ または $`(d = d \wedge y \lt y')`$ である。前者は $`\lt`$ の非反射性に反するから
$`y \lt y'`$ である。[T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 1 選言がこれであるから、
上に書いた 2 つの翻訳の式と合わせて結論が従う。∎

<a id="t-seqlex_total"></a>
## 定理: 列辞書式順序の三分律 (T.seqlex_total)

### 定理

任意の $`M, N \in \mathrm{PairSeq}`$ に対し

```math
M = N \ \vee\ M \prec_{\mathrm{lex}} N \ \vee\ N \prec_{\mathrm{lex}} M .
```

### 証明

$`M`$ のリスト構造に関する帰納法を行う（$`N`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(M) :\equiv \forall N \in \mathrm{PairSeq},\
  \bigl(M = N \vee M \prec_{\mathrm{lex}} N \vee N \prec_{\mathrm{lex}} M\bigr).
```

**基底段 $`M = ()`$。** $`N`$ の構成子で場合分けする。

- $`N = ()`$ のとき。$`M = N`$ が成り立つ（第 1 選言）。
- $`N = q :: N'`$ のとき。[T.seqlex_nil_iff](#t-seqlex_nil_iff) より
  $`() \prec_{\mathrm{lex}} (q :: N')`$ は $`q :: N' \ne ()`$ と同値であり、列の構成子の像が交わらない
  ことからこれは成り立つ（第 2 選言）。

**帰納段 $`M = p :: M'`$。** 帰納法の仮定は $`\Phi(M')`$、すなわち
$`\forall N,\ (M' = N \vee M' \prec_{\mathrm{lex}} N \vee N \prec_{\mathrm{lex}} M')`$ である。
$`N`$ の構成子で場合分けする。

- $`N = ()`$ のとき。[T.seqlex_nil_iff](#t-seqlex_nil_iff) より
  $`() \prec_{\mathrm{lex}} (p :: M')`$ は $`p :: M' \ne ()`$ と同値であり、これは成り立つ（第 3 選言）。

- $`N = q :: N'`$ のとき。さらに $`p = q`$ かどうかで分ける。

**$`p = q`$ のとき。** 帰納法の仮定 $`\Phi(M')`$ を $`N'`$ に適用して 3 通りに分ける。

- $`M' = N'`$ のとき。$`p = q`$ と合わせて $`p :: M' = q :: N'`$（第 1 選言）。
- $`M' \prec_{\mathrm{lex}} N'`$ のとき。[T.seqlex_cons_cons](#t-seqlex_cons_cons) の右辺の第 2 選言
  $`p = q \wedge M' \prec_{\mathrm{lex}} N'`$ が成り立つから $`p :: M' \prec_{\mathrm{lex}} q :: N'`$（第 2 選言）。
- $`N' \prec_{\mathrm{lex}} M'`$ のとき。[T.seqlex_cons_cons](#t-seqlex_cons_cons) の右辺の第 2 選言
  $`q = p \wedge N' \prec_{\mathrm{lex}} M'`$ が成り立つから
  $`q :: N' \prec_{\mathrm{lex}} p :: M'`$（第 3 選言）。

**$`p \ne q`$ のとき。** まず
$`p \prec_{\mathrm{p}} q \vee q \prec_{\mathrm{p}} p`$ を示す。
$`\mathbb{N}`$ の $`\lt`$ の三分律を $`p_1`$ と $`q_1`$ に適用して 3 通りに分ける。

- $`p_1 \lt q_1`$ のとき。$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 1 選言により
  $`p \prec_{\mathrm{p}} q`$。
- $`p_1 = q_1`$ のとき。さらに $`\mathbb{N}`$ の $`\lt`$ の三分律を $`p_2`$ と $`q_2`$ に適用する。
  - $`p_2 \lt q_2`$ のとき。$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 2 選言
    $`p_1 = q_1 \wedge p_2 \lt q_2`$ により $`p \prec_{\mathrm{p}} q`$。
  - $`p_2 = q_2`$ のとき。$`p_1 = q_1`$ と $`p_2 = q_2`$ から対の外延性により $`p = q`$ となり、
    仮定 $`p \ne q`$ に矛盾する。
  - $`q_2 \lt p_2`$ のとき。$`q_1 = p_1`$ と合わせて $`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の
    第 2 選言により $`q \prec_{\mathrm{p}} p`$。
- $`q_1 \lt p_1`$ のとき。$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 1 選言により
  $`q \prec_{\mathrm{p}} p`$。

いずれの場合も $`p \prec_{\mathrm{p}} q`$ か $`q \prec_{\mathrm{p}} p`$ が得られた。
前者のときは [T.seqlex_cons_cons](#t-seqlex_cons_cons) の右辺の第 1 選言 $`p \prec_{\mathrm{p}} q`$ により
$`p :: M' \prec_{\mathrm{lex}} q :: N'`$（第 2 選言）であり、後者のときは
[T.seqlex_cons_cons](#t-seqlex_cons_cons) の右辺の第 1 選言 $`q \prec_{\mathrm{p}} p`$ により
$`q :: N' \prec_{\mathrm{lex}} p :: M'`$（第 3 選言）である。∎

<a id="t-olt_iff_seqlex"></a>
## 定理: ブロック上の順序同型 (T.olt_iff_seqlex)

### 定理

$`d \in \mathbb{N}`$、$`M, N \in \mathrm{PairSeq}`$ とする。
$`\mathrm{blockok}(d, M)`$、$`\mathrm{blockok}(d, N)`$、$`M \ne N`$ ならば

```math
\mathrm{tr}\,M \prec \mathrm{tr}\,N \iff M \prec_{\mathrm{lex}} N .
```

### 証明

両方向を示す。

**（$`\Rightarrow`$）** $`\mathrm{tr}\,M \prec \mathrm{tr}\,N`$ とする。
$`M \prec_{\mathrm{lex}} N`$ が成り立たないと仮定して矛盾を導く。
[T.seqlex_total](#t-seqlex_total) を $`M`$, $`N`$ に適用すると次の 3 通りである。

- $`M = N`$ のとき。仮定 $`M \ne N`$ に矛盾する。
- $`M \prec_{\mathrm{lex}} N`$ のとき。いま仮定した「$`M \prec_{\mathrm{lex}} N`$ が成り立たない」に矛盾する。
- $`N \prec_{\mathrm{lex}} M`$ のとき。[T.seqlex_imp_olt](#t-seqlex_imp_olt) を
  $`d`$, $`N`$, $`M`$, $`\mathrm{blockok}(d,N)`$, $`\mathrm{blockok}(d,M)`$ に適用して
  $`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ を得る。これと $`\mathrm{tr}\,M \prec \mathrm{tr}\,N`$ に
  [T.olt_trans](Term.md#t-olt_trans) を適用すると $`\mathrm{tr}\,M \prec \mathrm{tr}\,M`$ となり、
  [T.olt_irrefl](Term.md#t-olt_irrefl) に矛盾する。

いずれの場合も矛盾するから $`M \prec_{\mathrm{lex}} N`$ である。

**（$`\Leftarrow`$）** [T.seqlex_imp_olt](#t-seqlex_imp_olt) を $`d`$, $`M`$, $`N`$ に適用すればよい。∎

<a id="t-getLastD_eq_getD"></a>
## 定理: 末尾要素の添字表示 (T.getLastD_eq_getD)

### 定理

型 $`\alpha`$ の有限列 $`l`$ と $`d \in \alpha`$ に対し

```math
\mathrm{last}_d\,l = l\langle \lvert l\rvert - 1\rangle_d .
```

ここで

```math
l\langle i\rangle_d := \begin{cases} l_i & (i \lt \lvert l\rvert) \cr d & (i \ge \lvert l\rvert) \end{cases}
```

であり、減法は自然数の切り捨て減法である。$`\alpha = \mathbb{N}\times\mathbb{N}`$ かつ $`d = (0,0)`$ のときの
$`l\langle i\rangle_{(0,0)}`$ が、$`M_{i,j}`$ の定義（D.entry）の $`l\langle i\rangle`$ である。

### 証明

$`l`$ が空かどうかで場合分けする。

- $`l = ()`$ のとき。左辺は $`\mathrm{last}_d`$ の定義の第 1 式より $`d`$ である。
  右辺は $`\lvert l\rvert - 1 = 0 - 1 = 0`$ であり、$`0 \lt \lvert l\rvert = 0`$ は偽だから
  $`\langle\cdot\rangle_d`$ の定義の第 2 式より $`d`$ である。

- $`l \ne ()`$ のとき。$`1 \le \lvert l\rvert`$ であるから $`\lvert l\rvert - 1 \lt \lvert l\rvert`$ であり、
  右辺は $`\langle\cdot\rangle_d`$ の定義の第 1 式より $`l_{\lvert l\rvert - 1}`$ である。
  左辺も $`\mathrm{last}_d`$ の定義の第 2 式より $`l_{\lvert l\rvert - 1}`$ である。∎

<a id="t-getLastD_ne_nil_indep"></a>
## 定理: 空でない列の末尾要素は既定値に依らない (T.getLastD_ne_nil_indep)

### 定理

型 $`\alpha`$ の有限列 $`B`$ が $`B \ne ()`$ をみたすならば、任意の $`d, d' \in \alpha`$ に対し

```math
\mathrm{last}_d\,B = \mathrm{last}_{d'}\,B .
```

### 証明

$`B`$ の構成子で場合分けする。

- $`B = ()`$ のとき。仮定 $`B \ne ()`$ に矛盾する。

- $`B = b :: bs`$ のとき。$`\mathrm{last}_d`$ の定義の第 2 式より、両辺とも
  $`(b :: bs)_{\lvert b :: bs\rvert - 1}`$ に等しい。この値は $`d`$ にも $`d'`$ にも依らない。∎

<a id="t-headI_append_left"></a>
## 定理: 左が空でない連結の先頭 (T.headI_append_left)

### 定理

型 $`\alpha`$ の有限列 $`A, B`$ について、$`A \ne ()`$ ならば

```math
\mathrm{head}(A \mathbin{+\!\!+} B) = \mathrm{head}\,A .
```

### 証明

$`A`$ の構成子で場合分けする。

- $`A = ()`$ のとき。仮定 $`A \ne ()`$ に矛盾する。

- $`A = a :: as`$ のとき。$`(a :: as) \mathbin{+\!\!+} B = a :: (as \mathbin{+\!\!+} B)`$ であるから、
  $`\mathrm{head}`$ の定義より左辺は $`a`$ である。右辺も $`\mathrm{head}(a :: as) = a`$ である。∎

<a id="t-getLastD_append_right"></a>
## 定理: 右が空でない連結の末尾 (T.getLastD_append_right)

### 定理

型 $`\alpha`$ の有限列 $`A, B`$ について、$`B \ne ()`$ ならば、任意の $`d \in \alpha`$ に対し

```math
\mathrm{last}_d(A \mathbin{+\!\!+} B) = \mathrm{last}_d\,B .
```

### 証明

$`A`$ のリスト構造に関する帰納法を行う（$`d`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(A) :\equiv \forall d \in \alpha,\ \mathrm{last}_d(A \mathbin{+\!\!+} B) = \mathrm{last}_d\,B .
```

- **基底段** $`A = ()`$：$`() \mathbin{+\!\!+} B = B`$ であるから両辺は同一である。

**帰納段 $`A = a :: A'`$。** 帰納法の仮定は $`\Phi(A')`$、すなわち
$`\forall d,\ \mathrm{last}_d(A' \mathbin{+\!\!+} B) = \mathrm{last}_d\,B`$ である。
まず、任意の $`b \in \alpha`$ と型 $`\alpha`$ の有限列 $`bs`$ に対し

```math
\mathrm{last}_d(b :: bs) = \mathrm{last}_b\,bs
```

が成り立つことを示す。$`bs = ()`$ のとき、$`b :: bs = (b) \ne ()`$ であるから
$`\mathrm{last}_d`$ の定義の第 2 式より左辺は $`(b)_{\lvert (b)\rvert - 1} = (b)_0 = b`$ であり、
右辺は $`\mathrm{last}_b\,()`$ であって同じ定義の第 1 式より $`b`$ である。
$`bs \ne ()`$ のとき、$`b :: bs \ne ()`$ でもあるから
$`\mathrm{last}_d`$ の定義の第 2 式を両辺に用いて、左辺は
$`(b :: bs)_{\lvert b :: bs\rvert - 1} = (b :: bs)_{\lvert bs\rvert}`$、右辺は
$`bs_{\lvert bs\rvert - 1}`$ である。$`\lvert bs\rvert \ge 1`$ であるから
$`b :: bs`$ の第 $`\lvert bs\rvert`$ 要素は $`bs`$ の第 $`\lvert bs\rvert - 1`$ 要素であり、
両辺は等しい。

$`(a :: A') \mathbin{+\!\!+} B = a :: (A' \mathbin{+\!\!+} B)`$ であるから、この式を
$`b := a`$、$`bs := A' \mathbin{+\!\!+} B`$ に適用して

```math
\mathrm{last}_d\bigl(a :: (A' \mathbin{+\!\!+} B)\bigr) = \mathrm{last}_a(A' \mathbin{+\!\!+} B)
```

である。ここに帰納法の仮定 $`\Phi(A')`$ を $`d := a`$ に適用して
$`\mathrm{last}_a(A' \mathbin{+\!\!+} B) = \mathrm{last}_a\,B`$ を得る。
最後に $`B \ne ()`$ と [T.getLastD_ne_nil_indep](#t-getLastD_ne_nil_indep) より
$`\mathrm{last}_a\,B = \mathrm{last}_d\,B`$ である。よって $`\Phi(a :: A')`$。∎

<a id="t-steps1_flatMap"></a>
## 定理: ブロックの連結の段差 1 (T.steps1_flatMap)

### 定理

$`F : \mathbb{N} \to \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とし、

```math
\mathrm{cat}_n F := F(0) \mathbin{+\!\!+} F(1) \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} F(n-1)
```

とおく（$`n = 0`$ のときは空列）。次の 3 つを仮定する。

```math
\begin{aligned}
&\text{(F1)}\quad \forall k \lt n,\ \mathrm{steps}_1\bigl(F(k)\bigr), \cr
&\text{(Fne)}\quad \forall k \lt n,\ F(k) \ne (), \cr
&\text{(Fj)}\quad \forall k,\ k + 1 \lt n \to
   \bigl(\mathrm{head}\,F(k+1)\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)} F(k)\bigr)_1 + 1 .
\end{aligned}
```

このとき $`\mathrm{steps}_1(\mathrm{cat}_n F)`$ が成り立ち、さらに $`0 \lt n`$ ならば

```math
\mathrm{cat}_n F \ne (),
\qquad
\mathrm{head}(\mathrm{cat}_n F) = \mathrm{head}\,F(0),
\qquad
\mathrm{last}_{(0,0)}(\mathrm{cat}_n F) = \mathrm{last}_{(0,0)} F(n-1)
```

が成り立つ。

### 証明

$`n`$ に関する自然数の帰納法。$`F`$ は固定する。帰納法の述語は

```math
\begin{aligned}
\Phi(n) :\equiv\ &\Bigl(\forall k \lt n,\ \mathrm{steps}_1(F(k))\Bigr)
  \wedge \Bigl(\forall k \lt n,\ F(k) \ne ()\Bigr) \cr
&\wedge \Bigl(\forall k,\ k+1 \lt n \to
   (\mathrm{head}\,F(k+1))_1 \le (\mathrm{last}_{(0,0)} F(k))_1 + 1\Bigr) \cr
&\to\ \mathrm{steps}_1(\mathrm{cat}_n F) \wedge \Bigl(0 \lt n \to
   \bigl(\mathrm{cat}_n F \ne ()
   \wedge \mathrm{head}(\mathrm{cat}_n F) = \mathrm{head}\,F(0) \cr
&\hphantom{\to\ \mathrm{steps}_1(\mathrm{cat}_n F) \wedge \Bigl(0 \lt n \to \bigl(}
   \wedge \mathrm{last}_{(0,0)}(\mathrm{cat}_n F) = \mathrm{last}_{(0,0)} F(n-1)\bigr)\Bigr) .
\end{aligned}
```

**基底段 $`n = 0`$。** $`\mathrm{cat}_0 F = ()`$ である。
[T.steps1_nil](#t-steps1_nil) より $`\mathrm{steps}_1(())`$ が成り立つ。
第 2 の連言子の前件 $`0 \lt 0`$ は偽であるから、その含意は成り立つ。

**帰納段 $`n = m + 1`$。** 帰納法の仮定は $`\Phi(m)`$ である。
$`\mathrm{cat}`$ の定義と連結の結合性より

```math
\mathrm{cat}_{m+1} F = \mathrm{cat}_m F \mathbin{+\!\!+} F(m)
```

である。$`m`$ が $`0`$ かどうかで場合分けする。

**(a) $`m = 0`$ のとき。** $`\mathrm{cat}_1 F = F(0)`$ である。
(F1) を $`k := 0 \lt 1`$ に適用して $`\mathrm{steps}_1(F(0))`$ を得る。
また $`0 \lt 1`$ のとき、(Fne) を $`k := 0`$ に適用して $`F(0) \ne ()`$、
$`\mathrm{head}(\mathrm{cat}_1 F) = \mathrm{head}\,F(0)`$ は両辺が同一、
$`\mathrm{last}_{(0,0)}(\mathrm{cat}_1 F) = \mathrm{last}_{(0,0)} F(0) = \mathrm{last}_{(0,0)} F(1-1)`$
も両辺が同一である。

**(b) $`m \ne 0`$ のとき。** $`k \lt m`$ ならば $`k \lt m + 1`$、
$`k + 1 \lt m`$ ならば $`k + 1 \lt m + 1`$ であるから、(F1), (Fne), (Fj) は $`n := m`$ でも
成り立つ。よって帰納法の仮定 $`\Phi(m)`$ が使えて、

```math
\mathrm{steps}_1(\mathrm{cat}_m F)
```

を得る。さらに $`m \ne 0`$ より $`0 \lt m`$ であるから

```math
\mathrm{cat}_m F \ne (),
\qquad
\mathrm{head}(\mathrm{cat}_m F) = \mathrm{head}\,F(0),
\qquad
\mathrm{last}_{(0,0)}(\mathrm{cat}_m F) = \mathrm{last}_{(0,0)} F(m-1)
```

も得られる。

つぎに接合部の評価

```math
\bigl(\mathrm{head}\,F(m)\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)}(\mathrm{cat}_m F)\bigr)_1 + 1
```

を示す。上の第 3 式により右辺は $`\bigl(\mathrm{last}_{(0,0)} F(m-1)\bigr)_1 + 1`$ に等しい。
$`m \ne 0`$ より $`(m-1) + 1 = m \lt m + 1`$ であるから、(Fj) を $`k := m - 1`$ に適用して

```math
\bigl(\mathrm{head}\,F(m)\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)} F(m-1)\bigr)_1 + 1
```

を得る。また (Fne) を $`k := m \lt m + 1`$ に適用して $`F(m) \ne ()`$ である。

以上のもとで 4 つの結論を示す。

**段差 1。**上の分解と [T.steps1_append](#t-steps1_append) により、
$`\mathrm{steps}_1(\mathrm{cat}_m F \mathbin{+\!\!+} F(m))`$ を示すには
$`\mathrm{steps}_1(\mathrm{cat}_m F)`$、$`\mathrm{steps}_1(F(m))`$、および
「$`\mathrm{cat}_m F = ()`$ または $`F(m) = ()`$ または
$`(\mathrm{head}\,F(m))_1 \le (\mathrm{last}_{(0,0)}(\mathrm{cat}_m F))_1 + 1`$」
の 3 つを言えばよい。第 1 は上で得た。第 2 は (F1) を $`k := m \lt m+1`$ に適用して得る。
第 3 は上で示した接合部の評価が第 3 選言である。

**空でないこと。**$`\mathrm{cat}_m F \mathbin{+\!\!+} F(m) = ()`$ とすると、連結が空になるのは
両方が空のときに限るから $`\mathrm{cat}_m F = ()`$ となり、上で得た $`\mathrm{cat}_m F \ne ()`$ に
矛盾する。

**先頭。**[T.headI_append_left](#t-headI_append_left) を $`A := \mathrm{cat}_m F \ne ()`$ に適用して

```math
\mathrm{head}(\mathrm{cat}_{m+1} F) = \mathrm{head}(\mathrm{cat}_m F) = \mathrm{head}\,F(0)
```

を得る（第 2 の等号は帰納法の仮定から得た式である）。

**末尾。**[T.getLastD_append_right](#t-getLastD_append_right) を $`B := F(m) \ne ()`$ に適用して

```math
\mathrm{last}_{(0,0)}(\mathrm{cat}_{m+1} F) = \mathrm{last}_{(0,0)} F(m)
```

を得る。$`(m+1) - 1 = m`$ であるからこれが求める式である。∎

<a id="t-steps1_diag_range"></a>
## 定理: 対角区間の段差 1 (T.steps1_diag_range)

### 定理

任意の $`m, s \in \mathbb{N}`$ に対し

```math
\mathrm{steps}_1\bigl(\,\bigl((s,s),\ (s+1,s+1),\ \dots,\ (s+m-1,s+m-1)\bigr)\,\bigr).
```

すなわち $`s`$ から始まる長さ $`m`$ の連続整数の列の各要素 $`j`$ を $`(j,j)`$ に写した列は
段差 1 の条件をみたす。

### 証明

$`m`$ に関する自然数の帰納法（$`s`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(m) :\equiv \forall s \in \mathbb{N},\
  \mathrm{steps}_1\bigl(\,\bigl((s+i,\,s+i)\bigr)_{i=0}^{m-1}\,\bigr).
```

- **基底段** $`m = 0`$：列は空列であり、[T.steps1_nil](#t-steps1_nil) による。

**帰納段 $`m + 1`$。** 帰納法の仮定は $`\Phi(m)`$、すなわち
$`\forall s,\ \mathrm{steps}_1\bigl((\,(s+i,s+i)\,)_{i=0}^{m-1}\bigr)`$ である。
$`s`$ を取る。長さ $`m+1`$ の列は先頭を分離して

```math
\bigl((s+i,\,s+i)\bigr)_{i=0}^{m} = (s,s) :: \bigl((s+1+i,\,s+1+i)\bigr)_{i=0}^{m-1}
```

と書ける。$`m`$ が $`0`$ かどうかでさらに分ける。

**$`m = 0`$ のとき。** 右辺は $`\bigl((s,s)\bigr)`$、すなわち長さ 1 の列であり、
[T.steps1_single](#t-steps1_single) による。

**$`m = m' + 1`$ のとき。** もう一度先頭を分離して

```math
\bigl((s+1+i,\,s+1+i)\bigr)_{i=0}^{m-1}
  = (s+1,s+1) :: \bigl((s+2+i,\,s+2+i)\bigr)_{i=0}^{m'-1}
```

である。よって示すべき列は $`(s,s) :: (s+1,s+1) :: \cdots`$ の形であり、
[T.steps1_cons_cons](#t-steps1_cons_cons) により次の 2 つを示せばよい。

第 1 は $`(s+1,s+1)_1 \le (s,s)_1 + 1`$、すなわち $`s + 1 \le s + 1`$ であり、
$`\le`$ の反射性による。

第 2 は $`\mathrm{steps}_1\bigl((s+1,s+1) :: ((s+2+i,s+2+i))_{i=0}^{m'-1}\bigr)`$ であり、
これは帰納法の仮定 $`\Phi(m)`$ を $`s := s + 1`$ に適用して得られる
$`\mathrm{steps}_1\bigl(((s+1+i,s+1+i))_{i=0}^{m-1}\bigr)`$ を、上の先頭分離の式で
書き換えたものにほかならない。∎

<a id="t-blockok_diagSeq"></a>
## 定理: 対角列はブロック (T.blockok_diagSeq)

### 定理

任意の $`v \in \mathbb{N}`$ に対し $`\mathrm{blockok}(0, \Delta_0^v)`$（[D.diagSeq](Pss.md#d-diagSeq)）。

### 証明

$`\mathrm{blockok}`$ の定義（D.blockok）の 3 つの連言子を順に示す。

**第 1（先頭は深さ $`0`$）。** $`\Delta_0^v \ne ()`$ とする。
$`0 \le v`$ であるから [T.diagSeq_cons](Cnf.md#t-diagSeq_cons) より
$`\Delta_0^v = (0,0) :: \Delta_1^v`$ である。よって
$`\mathrm{head}\,\Delta_0^v = (0,0)`$ であり、その第 1 成分は $`0`$ である。

**第 2（行 $`0`$ の値は $`0`$ 以上）。** 任意の $`p \in \Delta_0^v`$ に対し
$`0 \le p_1`$ は、$`0`$ が自然数の最小元であることによる。

**第 3（段差 1）。** $`\Delta_0^v`$ の定義（D.diagSeq）より、$`\Delta_0^v`$ は
$`0`$ から始まる長さ $`v + 1 - 0`$ の連続整数の列の各要素 $`j`$ を $`(j,j)`$ に写した列である。
[T.steps1_diag_range](#t-steps1_diag_range) を $`m := v + 1`$, $`s := 0`$ に適用すればよい。∎

<a id="t-blockok_oper"></a>
## 定理: 展開はブロックを保つ (T.blockok_oper)

### 定理

$`M \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とする。
$`\mathrm{blockok}(0, M)`$ かつ $`1 \le n`$ ならば $`\mathrm{blockok}(0, M[n])`$（[D.oper](Pss.md#d-oper)）。

### 証明

以下 $`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$（[D.idx1](Pss.md#d-idx1)）と書く。
$`j_1 = 0`$ かどうかで場合分けする。

**(A) $`j_1 = 0`$ のとき。**
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より $`M[n] = M`$ であり、
結論は仮定 $`\mathrm{blockok}(0, M)`$ そのものである。

**(B) $`j_1 \ne 0`$ のとき。**
$`j_1 = \lvert M\rvert - 1 \ne 0`$ より $`1 \lt \lvert M\rvert`$ であり、とくに $`M \ne ()`$ である。
また $`\mathrm{Pred}\,M`$（[D.Pred](Pss.md#d-Pred)）の定義（D.Pred）の場合分けで $`\lvert M\rvert \le 1`$ が偽であるから

```math
\mathrm{Pred}\,M = \mathrm{dropLast}\,M
```

である。$`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ が成り立つかどうかで分ける。

**(B-1) $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。**
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) より
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。
[T.blockok_dropLast](#t-blockok_dropLast) を $`\mathrm{blockok}(0,M)`$ に適用すればよい。

**(B-2) $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ かつ
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$（[D.hasParent](Pss.md#d-hasParent)）のとき。**
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) より
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。
[T.blockok_dropLast](#t-blockok_dropLast) を適用すればよい。

**(B-3) $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ かつ $`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
[T.parent_nextR](Decrease.md#t-parent_nextR) より、$`j_0 := \mathrm{par}^M_{i_1}(j_1)`$（[D.parent](Pss.md#d-parent)）とおくと
$`j_0 \to^M_{i_1} j_1`$（[D.nextR](Pss.md#d-nextR)）である。[T.nextR_index_lt](Decrease.md#t-nextR_index_lt) より
$`j_0 \lt j_1`$ である。さらに

```math
d_0 := \begin{cases} M_{0,j_1} - M_{0,j_0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
```

とおく。

**行 $`0`$ の段差（式 E1）。** $`\mathrm{blockok}(0,M)`$ の第 3 の連言子は
$`\mathrm{steps}_1(M)`$ である。[T.steps1_iff](#t-steps1_iff) により

```math
\forall j,\ j + 1 \lt \lvert M\rvert \ \to\ M_{0,j+1} \le M_{0,j} + 1 .
```

（$`M\langle j\rangle`$ の第 1 成分が $`M_{0,j}`$ であることは $`M_{i,j}`$ の定義（D.entry）による。）

**接合部の評価（式 E2）。**

```math
M_{0,j_0} + d_0 \le M_{0,j_1 - 1} + 1 .
```

これを示す。まず $`j_1 \ne 0`$ より $`(j_1 - 1) + 1 = j_1 \lt \lvert M\rvert`$ であるから、
式 E1 を $`j := j_1 - 1`$ に適用して

```math
M_{0,j_1} \le M_{0,j_1 - 1} + 1
```

を得る。$`i_1`$ が $`0`$ かどうかで分ける。

**$`0 \lt i_1`$ のとき。** $`\to^M_{i}`$ の定義（D.nextR）の第 2 式より
$`j_0 \to^M_{i_1} j_1`$ は $`j_0 \to^M_1 j_1`$（[D.nextrel1](Pss.md#d-nextrel1)）である。
$`\to^M_1`$ の定義（D.nextrel1）の第 5 条件は $`j_0 \le^M_0 j_1`$ であり、
[T.le0_entry0_mono](Term.md#t-le0_entry0_mono) より $`M_{0,j_0} \le M_{0,j_1}`$ である。
$`d_0`$ の定義の第 1 式より $`d_0 = M_{0,j_1} - M_{0,j_0}`$ であり、切り捨て減法は
$`M_{0,j_0} \le M_{0,j_1}`$ のとき

```math
M_{0,j_0} + d_0 = M_{0,j_0} + (M_{0,j_1} - M_{0,j_0}) = M_{0,j_1}
```

をみたす。これと上の式を合わせて $`M_{0,j_0} + d_0 \le M_{0,j_1-1} + 1`$ を得る。

**$`i_1 = 0`$ のとき。** $`\to^M_{i}`$ の定義（D.nextR）の第 1 式より
$`j_0 \to^M_0 j_1`$（[D.nextrel0](Pss.md#d-nextrel0)）である。[T.nextrel0_entry0_less](Term.md#t-nextrel0_entry0_less) より
$`M_{0,j_0} \lt M_{0,j_1}`$ である。$`d_0`$ の定義の第 2 式より $`d_0 = 0`$ であるから

```math
M_{0,j_0} + d_0 = M_{0,j_0} \lt M_{0,j_1} \le M_{0,j_1-1} + 1
```

であり、とくに $`M_{0,j_0} + d_0 \le M_{0,j_1-1} + 1`$ を得る。

**展開の形。**[T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) より

```math
M[n] = \mathrm{take}_{j_0} M \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
```

である。ここで $`\mathrm{take}_{j_0} M := (M_0, \dots, M_{j_0-1})`$ である。
$`F(k) := B_k`$ とおけば右辺は $`\mathrm{take}_{j_0} M \mathbin{+\!\!+} \mathrm{cat}_n F`$ である。

**各ブロックの性質。** $`j_0 \lt j_1`$ より $`1 \le j_1 - j_0`$ であるから、
$`B_k`$ の添字の走る列は

```math
(j_0,\ j_0+1,\ \dots,\ j_1-1) = j_0 :: (j_0+1,\ \dots,\ j_1-1)
```

と先頭を分離できる。これより次の 5 つが従う。

**(F-ne)** $`B_k \ne ()`$。上の分離により $`B_k`$ は少なくとも 1 要素をもつ。

**(F-hd)** $`\mathrm{head}\,B_k = (M_{0,j_0} + k\,d_0,\ M_{1,j_0})`$。上の分離の先頭 $`j_0`$ の像である。

**(F-len)** $`\lvert B_k\rvert = j_1 - j_0`$。添字の列の長さがそれだけだからである。

**(F-get)** $`j \lt j_1 - j_0`$ ならば
$`B_k\langle j\rangle = (M_{0,j_0+j} + k\,d_0,\ M_{1,j_0+j})`$。
添字の列の第 $`j`$ 要素は $`j_0 + j`$ であり、その像がこれである。

**(F-last)** $`\mathrm{last}_{(0,0)} B_k = (M_{0,j_1-1} + k\,d_0,\ M_{1,j_1-1})`$。
[T.getLastD_eq_getD](#t-getLastD_eq_getD) と (F-len) より
$`\mathrm{last}_{(0,0)} B_k = B_k\langle j_1 - j_0 - 1\rangle`$ であり、
(F-get) を $`j := j_1 - j_0 - 1`$（これは $`j_1 - j_0`$ 未満）に適用すると、
$`j_0 + (j_1 - j_0 - 1) = j_1 - 1`$ よりこの値になる。

**(F-steps) 各ブロックの段差 1。** $`\mathrm{steps}_1(B_k)`$ を示す。
[T.steps1_iff](#t-steps1_iff) により、$`j + 1 \lt \lvert B_k\rvert = j_1 - j_0`$ なる $`j`$ について
$`\bigl(B_k\langle j+1\rangle\bigr)_1 \le \bigl(B_k\langle j\rangle\bigr)_1 + 1`$ を示せばよい。
(F-get) を $`j`$ と $`j+1`$ に適用すると、示すべき式は

```math
M_{0,j_0+j+1} + k\,d_0 \le M_{0,j_0+j} + k\,d_0 + 1
```

である。$`j + 1 \lt j_1 - j_0`$ より $`j_0 + j + 1 \lt j_1 \lt \lvert M\rvert`$ であるから、
式 E1 を $`j := j_0 + j`$ に適用して $`M_{0,j_0+j+1} \le M_{0,j_0+j} + 1`$ を得る。
両辺に $`k\,d_0`$ を加えれば上の式になる。

**(F-junc) ブロック間の接合。** $`k + 1 \lt n`$ なる $`k`$ について

```math
\bigl(\mathrm{head}\,B_{k+1}\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)} B_k\bigr)_1 + 1
```

を示す。(F-hd) と (F-last) により、示すべき式は

```math
M_{0,j_0} + (k+1)\,d_0 \le M_{0,j_1-1} + k\,d_0 + 1
```

である。$`(k+1)\,d_0 = k\,d_0 + d_0`$ であるから、これは
$`M_{0,j_0} + d_0 \le M_{0,j_1-1} + 1`$ の両辺に $`k\,d_0`$ を加えたものであり、式 E2 による。

**連結したブロック列。**[T.steps1_flatMap](#t-steps1_flatMap) を
$`F(k) = B_k`$、この $`n`$ に適用する。仮定 (F1) は (F-steps)、(Fne) は (F-ne)、
(Fj) は (F-junc) である。結論として $`\mathrm{steps}_1(\mathrm{cat}_n F)`$ を得る。
また $`1 \le n`$ より $`0 \lt n`$ であるから

```math
\mathrm{cat}_n F \ne (),
\qquad
\mathrm{head}(\mathrm{cat}_n F) = \mathrm{head}\,B_0
```

も得られる。(F-hd) を $`k := 0`$ に適用すると $`\mathrm{head}\,B_0 = (M_{0,j_0} + 0\cdot d_0, M_{1,j_0})`$
であり、$`0 \cdot d_0 = 0`$ であるから

```math
\mathrm{head}(\mathrm{cat}_n F) = (M_{0,j_0},\ M_{1,j_0}) .
```

**前置部分の段差 1。** $`\mathrm{steps}_1(\mathrm{take}_{j_0} M)`$ を示す。
[T.steps1_iff](#t-steps1_iff) により、$`j + 1 \lt \lvert \mathrm{take}_{j_0} M\rvert`$ なる $`j`$ について
$`\bigl((\mathrm{take}_{j_0} M)\langle j+1\rangle\bigr)_1 \le \bigl((\mathrm{take}_{j_0} M)\langle j\rangle\bigr)_1 + 1`$
を示せばよい。$`\lvert \mathrm{take}_{j_0} M\rvert = \min(j_0, \lvert M\rvert)`$ であり、
これは $`\lvert M\rvert`$ 以下であるから $`j + 1 \lt \lvert M\rvert`$ である。
また $`j`$ も $`j+1`$ も $`\lvert \mathrm{take}_{j_0} M\rvert`$ 未満であるから、
前置部分の第 $`j`$ 要素と第 $`j+1`$ 要素はそれぞれ $`M`$ の第 $`j`$ 要素と第 $`j+1`$ 要素に等しく、

```math
(\mathrm{take}_{j_0} M)\langle j\rangle = M\langle j\rangle,
\qquad
(\mathrm{take}_{j_0} M)\langle j+1\rangle = M\langle j+1\rangle
```

である。したがって示すべき式は $`M_{0,j+1} \le M_{0,j} + 1`$ であり、式 E1 による。

**前置部分と連結ブロックの接合。** 次の 3 選言のいずれかが成り立つことを示す。

```math
\mathrm{take}_{j_0} M = ()
\ \vee\ \mathrm{cat}_n F = ()
\ \vee\ \bigl(\mathrm{head}(\mathrm{cat}_n F)\bigr)_1
        \le \bigl(\mathrm{last}_{(0,0)}(\mathrm{take}_{j_0} M)\bigr)_1 + 1 .
```

$`j_0`$ が $`0`$ かどうかで分ける。

**$`j_0 = 0`$ のとき。** $`\mathrm{take}_0 M = ()`$ であり、第 1 選言が成り立つ。

**$`j_0 \ne 0`$ のとき。** $`j_0 \lt j_1 \lt \lvert M\rvert`$ より $`j_0 \le \lvert M\rvert`$ であるから
$`\lvert \mathrm{take}_{j_0} M\rvert = \min(j_0, \lvert M\rvert) = j_0`$ である。
[T.getLastD_eq_getD](#t-getLastD_eq_getD) より
$`\mathrm{last}_{(0,0)}(\mathrm{take}_{j_0} M) = (\mathrm{take}_{j_0} M)\langle j_0 - 1\rangle`$ であり、
$`j_0 - 1 \lt j_0 \le \lvert M\rvert`$ であるからこれは $`M\langle j_0 - 1\rangle`$ に等しい。
また $`j_0 \ne 0`$ より $`(j_0 - 1) + 1 = j_0 \lt \lvert M\rvert`$ であるから、式 E1 を
$`j := j_0 - 1`$ に適用して

```math
M_{0,j_0} \le M_{0,j_0-1} + 1
```

を得る。上で求めた $`\mathrm{head}(\mathrm{cat}_n F) = (M_{0,j_0}, M_{1,j_0})`$ と合わせると
これが第 3 選言である。

**結論。** $`\mathrm{blockok}`$ の定義（D.blockok）の 3 つの連言子を
$`M[n] = \mathrm{take}_{j_0} M \mathbin{+\!\!+} \mathrm{cat}_n F`$ について順に示す。

**第 1（先頭は深さ $`0`$）。** $`M[n] \ne ()`$ とする。$`j_0`$ が $`0`$ かどうかで分ける。

- $`j_0 = 0`$ のとき。$`\mathrm{take}_0 M = ()`$ であるから
  $`M[n] = \mathrm{cat}_n F`$ であり、上で求めたとおり
  $`\mathrm{head}(M[n]) = (M_{0,j_0}, M_{1,j_0}) = (M_{0,0}, M_{1,0})`$ である。
  その第 1 成分は $`M_{0,0}`$ である。$`M \ne ()`$ であるから $`M = x :: xs`$ と書け、
  $`\mathrm{head}\,M = x`$ かつ $`M\langle 0\rangle = x`$ であるから $`M_{0,0} = x_1`$ である。
  $`\mathrm{blockok}(0,M)`$ の第 1 の連言子を $`M \ne ()`$ に適用すると $`x_1 = 0`$ を得る。

- $`j_0 \ne 0`$ のとき。$`\lvert \mathrm{take}_{j_0} M\rvert = \min(j_0, \lvert M\rvert)`$ であり、
  $`0 \lt j_0`$ かつ $`0 \lt \lvert M\rvert`$ であるからこの値は $`0`$ より大きく、
  $`\mathrm{take}_{j_0} M \ne ()`$ である。
  [T.headI_append_left](#t-headI_append_left) より
  $`\mathrm{head}(M[n]) = \mathrm{head}(\mathrm{take}_{j_0} M)`$ である。
  $`M = x :: xs`$ と書き、$`j_0 = m + 1`$ とおくと
  $`\mathrm{take}_{m+1}(x :: xs) = x :: \mathrm{take}_m\,xs`$ であるから
  $`\mathrm{head}(\mathrm{take}_{j_0} M) = x = \mathrm{head}\,M`$ である。
  $`\mathrm{blockok}(0,M)`$ の第 1 の連言子を $`M \ne ()`$ に適用すると
  $`(\mathrm{head}\,M)_1 = 0`$ を得る。

**第 2（行 $`0`$ の値は $`0`$ 以上）。** 任意の $`p \in M[n]`$ に対し $`0 \le p_1`$ は、
$`0`$ が自然数の最小元であることによる。

**第 3（段差 1）。**[T.steps1_append](#t-steps1_append) により、
$`\mathrm{steps}_1(\mathrm{take}_{j_0} M)`$、$`\mathrm{steps}_1(\mathrm{cat}_n F)`$、および
上で示した 3 選言の 3 つを言えばよく、いずれもすでに示した。∎

<a id="t-blockok_ST_PS"></a>
## 定理: 標準形はブロック (T.blockok_ST_PS)

### 定理

$`M \in \mathrm{ST\_PS}`$（[D.ST_PS](Pss.md#d-ST_PS)）ならば $`\mathrm{blockok}(0, M)`$。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M) :\equiv \mathrm{blockok}(0, M).
```

- **基底段**（規則 (diag)、$`M = \Delta_0^v`$）：[T.blockok_diagSeq](#t-blockok_diagSeq) が
  $`\Phi(\Delta_0^v)`$ そのものである。

- **帰納段**（規則 (oper)、$`M \in \mathrm{ST\_PS}`$ と $`1 \le n`$ から $`M[n]`$）：
  帰納法の仮定は $`\Phi(M)`$、すなわち $`\mathrm{blockok}(0, M)`$ である。
  [T.blockok_oper](#t-blockok_oper) をこれと $`1 \le n`$ に適用して
  $`\mathrm{blockok}(0, M[n])`$、すなわち $`\Phi(M[n])`$ を得る。∎

<a id="t-olt_ST_iff_seqlex"></a>
## 定理: 標準形上の順序同型 (T.olt_ST_iff_seqlex)

### 定理

$`M, N \in \mathrm{ST\_PS}`$ かつ $`M \ne N`$ ならば

```math
\mathrm{tr}\,M \prec \mathrm{tr}\,N \iff M \prec_{\mathrm{lex}} N .
```

### 証明

[T.blockok_ST_PS](#t-blockok_ST_PS) を $`M`$ と $`N`$ に適用して
$`\mathrm{blockok}(0, M)`$ と $`\mathrm{blockok}(0, N)`$ を得る。
これらと $`M \ne N`$ に [T.olt_iff_seqlex](#t-olt_iff_seqlex) を $`d := 0`$ で適用すればよい。∎
