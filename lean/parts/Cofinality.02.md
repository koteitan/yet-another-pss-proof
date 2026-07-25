<a id="t-crux_zero"></a>
## 定理: 完全コピー分岐の核心 (T.crux_zero)

### 定理

$`G, R, S \in \mathrm{PairSeq}`$、$`v_0, w_0 \in \mathbb{N}`$、$`\ell, q \in \mathbb{N}\times\mathbb{N}`$ とし、
$`B := (v_0, w_0) :: R`$ とおく。次の 4 つを仮定する。

```math
\begin{aligned}
&(1)\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S \in \mathrm{ST\_PS}, \cr
&(2)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(3)\ \ell_2 = 0 \ \wedge\ \ell_1 = v_0 + 1, \cr
&(4)\ \mathrm{pairlt}(q, \ell) .
\end{aligned}
```

このとき $`1 \le m`$ なる $`m \in \mathbb{N}`$ が存在して

```math
q :: S \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m) .
```

### 証明

以下、$`\mathrm{tw}_p`$、$`\mathrm{dw}_p`$ を一般の述語 $`p`$ について書く（$`\mathrm{tw}_p L`$ は
$`L`$ の先頭から $`p`$ をみたす要素が続く極大な前部分列、$`\mathrm{dw}_p L`$ はその残りである）。

**第 1 段：$`q_1 \le v_0`$。**
$`\mathrm{pairlt}`$ の定義（D.pairlt）より、仮定 (4) は
$`q_1 \lt \ell_1`$ または（$`q_1 = \ell_1`$ かつ $`q_2 \lt \ell_2`$）である。
後者のとき、仮定 (3) の $`\ell_2 = 0`$ より $`q_2 \lt 0`$ となるが、自然数に $`0`$ より小さいものは
ないから矛盾であり、この場合は起こらない。前者のとき、仮定 (3) の $`\ell_1 = v_0 + 1`$ より
$`q_1 \lt v_0 + 1`$、すなわち $`q_1 \le v_0`$ である。

**第 2 段：$`q_1 \lt v_0`$ の場合。**
$`m := 1`$ と取る。[T.copies_one](Cnf.md#t-copies_one) より $`\mathrm{cp}_0(B, 1) = B = (v_0,w_0) :: R`$ である。
$`q_1 \lt v_0`$ であるから $`\mathrm{pairlt}`$ の定義（D.pairlt）の第 1 選言により
$`\mathrm{pairlt}\bigl(q, (v_0,w_0)\bigr)`$ が成り立ち、$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の
第 3 式の第 1 選言により $`q :: S \prec_{\mathrm{lex}} B`$ を得る。
$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言により結論を得る。

**第 3 段：以下 $`q_1 = v_0`$ とする。**
第 1 段と $`\neg(q_1 \lt v_0)`$ から $`q_1 = v_0`$ である。述語 $`p`$ を
$`p(x) :\equiv v_0 \le x_1`$ で定め、

```math
Y := \mathrm{tw}_p(q :: S), \qquad V := \mathrm{dw}_p(q :: S)
```

とおく。次の 4 つが成り立つ。

**(i)** $`Y \mathbin{+\!\!+} V = q :: S`$。$`\mathrm{tw}_p`$ と $`\mathrm{dw}_p`$ の定義そのものである。

**(ii)** $`Y = q :: \mathrm{tw}_p S`$。$`q_1 = v_0`$ より $`p(q)`$ が成り立つので、
$`\mathrm{tw}_p`$ は先頭の $`q`$ を取り込む。とくに $`Y \ne ()`$ であり
$`(\mathrm{head}\,Y)_1 = q_1 = v_0`$ である。

**(iii)** $`\forall x \in Y,\ v_0 \le x_1`$。$`\mathrm{tw}_p`$ の要素はすべて $`p`$ をみたすからである。

**(iv)** $`V = ()`$、または $`V = z :: Z`$ かつ $`z_1 \lt v_0`$ なる $`z, Z`$ が存在する。
実際 $`V \ne ()`$ ならばその先頭要素 $`z`$ は $`\neg p(z)`$、すなわち $`\neg(v_0 \le z_1)`$ を
みたすから $`z_1 \lt v_0`$ である。

**第 4 段：窓 $`B \mathbin{+\!\!+} Y`$ の分解。**
(i) と結合律により

```math
(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S = \bigl(G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)\bigr) \mathbin{+\!\!+} V
```

である。この列を $`N`$ と書く。

**第 5 段：$`\mathrm{steps}_1(B \mathbin{+\!\!+} Y)`$。**
仮定 (1) と [T.blockok_ST_PS](Seqlex.md#t-blockok_ST_PS) より $`\mathrm{blockok}(0, N)`$ が成り立ち、
$`\mathrm{blockok}`$ の定義（D.blockok）の第 3 連言子より $`\mathrm{steps}_1(N)`$ である。
第 4 段の分解に [T.steps1_append](Seqlex.md#t-steps1_append) を適用すると、その第 1 連言子として
$`\mathrm{steps}_1\bigl(G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)\bigr)`$ を得る。これにふたたび
[T.steps1_append](Seqlex.md#t-steps1_append) を適用すると、その第 2 連言子として
$`\mathrm{steps}_1(B \mathbin{+\!\!+} Y)`$ を得る。

**第 6 段：$`\mathrm{blockok}(v_0,\ B \mathbin{+\!\!+} Y)`$。**
$`\mathrm{blockok}`$ の定義（D.blockok）の 3 つの連言子を確かめる。
第 1 連言子は「空でなければ先頭の第 1 成分が $`v_0`$」であり、先頭は $`(v_0,w_0)`$ だから成り立つ。
第 2 連言子は $`\forall x \in B \mathbin{+\!\!+} Y,\ v_0 \le x_1`$ である。
$`x = (v_0,w_0)`$ なら $`x_1 = v_0`$、$`x \in R`$ なら仮定 (2) より $`v_0 \lt x_1`$、
$`x \in Y`$ なら (iii) より $`v_0 \le x_1`$ である。第 3 連言子は第 5 段である。

**第 7 段：窓の $`\mathrm{cnf}`$。**
仮定 (1) と [T.cnf_ST_PS](Cnf.md#t-cnf_ST_PS) より $`\mathrm{cnf}(\mathrm{tr}\,N)`$ である。
第 4 段の分解によりこれは
$`\mathrm{cnf}\bigl(\mathrm{tr}\bigl((G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)) \mathbin{+\!\!+} V\bigr)\bigr)`$ である。
[T.cnf_take](Cnf.md#t-cnf_take) を $`k := \lvert G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)\rvert`$ に適用する。
連結の左側の長さで切り取ると左側そのものが得られるから

```math
\mathrm{cnf}\bigl(\mathrm{tr}\,(G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y))\bigr)
```

を得る。$`B \mathbin{+\!\!+} Y = (v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$ であるから、これは
$`\mathrm{cnf}\bigl(\mathrm{tr}\,(G \mathbin{+\!\!+} ((v_0,w_0) :: (R \mathbin{+\!\!+} Y)))\bigr)`$ と同じ命題である。
[T.cnf_tail](Cnf.md#t-cnf_tail) を $`t := (v_0,w_0)`$、$`T' := R \mathbin{+\!\!+} Y`$、$`G := G`$ として
適用する。その仮定 $`\forall x \in R \mathbin{+\!\!+} Y,\ v_0 \le x_1`$ は第 6 段の第 2 連言子から
（$`R \mathbin{+\!\!+} Y`$ の要素は $`B \mathbin{+\!\!+} Y`$ の要素でもあるから）従う。よって

```math
\mathrm{cnf}\bigl(\mathrm{tr}\,((v_0,w_0) :: (R \mathbin{+\!\!+} Y))\bigr) .
```

**第 8 段：完全コピーによる支配。**
[T.copy_dom_zero](#t-copy_dom_zero) を $`d := \lvert Y\rvert`$、$`Y := Y`$、$`v_0`$、$`w_0`$、$`R`$ として
適用する。5 つの仮定は次のように満たされる。

- $`\lvert Y\rvert \le \lvert Y\rvert`$：等号による。
- $`\mathrm{blockok}\bigl(v_0,\ (v_0,w_0) :: (R \mathbin{+\!\!+} Y)\bigr)`$：第 6 段を
  $`B \mathbin{+\!\!+} Y = (v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$ と書き換えたものである。
- $`\forall x \in R,\ v_0 \lt x_1`$：仮定 (2) である。
- $`Y = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,Y)_1\bigr)`$：(ii) より
  $`(\mathrm{head}\,Y)_1 = v_0`$ であるから第 2 選言が成り立つ。
- $`\mathrm{cnf}\bigl(\mathrm{tr}\,((v_0,w_0) :: (R \mathbin{+\!\!+} Y))\bigr)`$：第 7 段である。

こうして $`1 \le m`$ なる $`m`$ と $`Y \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$ を得る。

**第 9 段：結論。**
求める witness として $`m + 1`$ を取る（$`1 \le m + 1`$）。
[T.copies_zero_succ](#t-copies_zero_succ) より
$`\mathrm{cp}_0(B, m+1) = \mathrm{cp}_0(B, m) \mathbin{+\!\!+} B`$ であり、(i) より $`q :: S = Y \mathbin{+\!\!+} V`$
であるから、示すべきは

```math
Y \mathbin{+\!\!+} V \prec_{\mathrm{lex}} \mathrm{cp}_0(B, m) \mathbin{+\!\!+} B
```

である（これが言えれば $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言により結論を得る）。
第 8 段の $`\preceq_{\mathrm{lex}}`$ を、$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）に従って 2 つの場合に分ける。

**(a) $`Y = \mathrm{cp}_0(B, m)`$ のとき。**
示すべきは $`Y \mathbin{+\!\!+} V \prec_{\mathrm{lex}} Y \mathbin{+\!\!+} B`$ である。
[T.seqlex_append_cancel](Seqlex.md#t-seqlex_append_cancel) により
$`V \prec_{\mathrm{lex}} B`$ を示せばよい。(iv) で場合分けする。

- $`V = ()`$ のとき。$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式により
  $`B \ne ()`$ を示せばよく、$`B = (v_0,w_0) :: R`$ は空でない。
- $`V = z :: Z`$ かつ $`z_1 \lt v_0`$ のとき。$`\mathrm{pairlt}`$ の定義（D.pairlt）の第 1 選言により
  $`\mathrm{pairlt}\bigl(z, (v_0,w_0)\bigr)`$ であり、$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の
  第 3 式の第 1 選言により $`z :: Z \prec_{\mathrm{lex}} (v_0,w_0) :: R`$ を得る。

**(b) $`Y \prec_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$ のとき。**
[T.seqlex_splice](#t-seqlex_splice) を、小さい側の列を $`Y`$、大きい側の列を $`\mathrm{cp}_0(B, m)`$、
小さい側に付ける列を $`V`$、大きい側に付ける列を $`B`$ として適用する。
残る仮定は「$`V = ()`$、または $`\forall x \in \mathrm{cp}_0(B,m),\ \mathrm{pairlt}(\mathrm{head}\,V,\ x)`$」
である。(iv) で場合分けする。

- $`V = ()`$ のとき。第 1 選言である。
- $`V = z :: Z`$ かつ $`z_1 \lt v_0`$ のとき。仮定 (2) より $`R`$ の各要素 $`y`$ は
  $`v_0 \le y_1`$ をみたすから、[T.copies_v0_le](Cnf.md#t-copies_v0_le) を $`d := 0`$、$`n := m`$ として
  適用して $`\forall x \in \mathrm{cp}_0(B, m),\ v_0 \le x_1`$ を得る。
  $`\mathrm{head}\,V = z`$ であり $`z_1 \lt v_0 \le x_1`$ であるから、$`\mathrm{pairlt}`$ の定義（D.pairlt）の
  第 1 選言により $`\mathrm{pairlt}(z, x)`$ が成り立つ。

いずれの場合も $`Y \mathbin{+\!\!+} V \prec_{\mathrm{lex}} \mathrm{cp}_0(B,m) \mathbin{+\!\!+} B`$ が得られた。∎

<a id="d-AscCrux"></a>
## 定義: 上昇コピーの核心 (D.AscCrux)

命題 $`\mathrm{AscCrux}`$ を次で定める。ここで $`B := (v_0,w_0) :: R`$、
$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$ と略記する（$`(\ell)`$ は $`\ell`$ のみからなる長さ $`1`$ の列）。

```math
\begin{aligned}
\mathrm{AscCrux} :\equiv\ &\forall G, R, S \in \mathrm{PairSeq},\ \forall v_0, w_0, d_0 \in \mathbb{N},\
   \forall \ell, q \in \mathbb{N}\times\mathbb{N}, \cr
&\quad H \in \mathrm{ST\_PS}
  \ \to\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S \in \mathrm{ST\_PS} \cr
&\quad \to\ \bigl(\forall x \in R,\ v_0 \lt x_1\bigr)
  \ \to\ 0 \lt d_0 \ \to\ \ell_2 = w_0 + 1 \ \to\ \ell_1 = v_0 + d_0 \cr
&\quad \to\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert
  \ \to\ \mathrm{pairlt}(q, \ell) \cr
&\quad \to\ \exists m,\ 1 \le m \ \wedge\
   q :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B, m)\bigr)^{+d_0} .
\end{aligned}
```

<a id="d-AscCrux1"></a>
## 定義: 頭を取った上昇コピーの核心 (D.AscCrux1)

命題 $`\mathrm{AscCrux1}`$ を次で定める。ここで $`B := (v_0,w_0) :: R`$、
$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr)`$ と略記する。

```math
\begin{aligned}
\mathrm{AscCrux1} :\equiv\ &\forall G, R, S \in \mathrm{PairSeq},\ \forall v_0, w_0, d_0 \in \mathbb{N}, \cr
&\quad H \in \mathrm{ST\_PS}
  \ \to\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS} \cr
&\quad \to\ \bigl(\forall x \in R,\ v_0 \lt x_1\bigr) \ \to\ 0 \lt d_0 \cr
&\quad \to\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert \cr
&\quad \to\ \exists m,\ 1 \le m \ \wedge\
   (v_0+d_0,\ w_0) :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B, m)\bigr)^{+d_0} .
\end{aligned}
```

<a id="t-shiftr0_length"></a>
## 定理: 平行移動は長さを変えない (T.shiftr0_length)

### 定理

$`d \in \mathbb{N}`$、$`X \in \mathrm{PairSeq}`$ に対し $`\lvert X^{+d}\rvert = \lvert X\rvert`$。

### 証明

$`X^{+d}`$ の定義（D.shiftr0）より $`X^{+d}`$ は $`X`$ の各要素 $`x`$ を $`(x_1+d,\ x_2)`$ に写した列で
あり、写像の適用は列の長さを変えない。∎

<a id="t-mem_shiftr0_le"></a>
## 定理: 平行移動後の行 0 の下界 (T.mem_shiftr0_le)

### 定理

$`d, e \in \mathbb{N}`$、$`X \in \mathrm{PairSeq}`$ とする。
$`\forall x \in X,\ d \le x_1`$ ならば $`\forall x \in X^{+e},\ d + e \le x_1`$。

### 証明

$`x \in X^{+e}`$ とする。[T.mem_shiftr0](Cnf.md#t-mem_shiftr0) より、ある $`y \in X`$ が存在して
$`x = (y_1 + e,\ y_2)`$ である。仮定より $`d \le y_1`$ であるから
$`d + e \le y_1 + e = x_1`$ である。∎

<a id="t-shiftr0_copies"></a>
## 定理: 平行移動とコピー塔の交換 (T.shiftr0_copies)

### 定理

$`d, n \in \mathbb{N}`$、$`B \in \mathrm{PairSeq}`$ に対し

```math
\bigl(\mathrm{cp}_d(B, n)\bigr)^{+d} = \mathrm{cp}_d\bigl(B^{+d},\ n\bigr) .
```

### 証明

$`\mathrm{cp}_d`$ の定義（D.copies）より

```math
\mathrm{cp}_d(B, n) = B^{+0\cdot d} \mathbin{+\!\!+} B^{+1\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d}
```

である。$`\cdot^{+d}`$ は各要素への写像の適用であるから連結を保ち、
$`(X \mathbin{+\!\!+} Y)^{+d} = X^{+d} \mathbin{+\!\!+} Y^{+d}`$ が成り立つ。これを繰り返して

```math
\bigl(\mathrm{cp}_d(B, n)\bigr)^{+d}
  = \bigl(B^{+0\cdot d}\bigr)^{+d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl(B^{+(n-1)d}\bigr)^{+d}
```

を得る。他方

```math
\mathrm{cp}_d\bigl(B^{+d},\ n\bigr)
  = \bigl(B^{+d}\bigr)^{+0\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl(B^{+d}\bigr)^{+(n-1)d}
```

である。両者の第 $`k`$ 項（$`k = 0, \dots, n-1`$）を比べる。$`x \in B`$ に対し
$`\bigl(B^{+kd}\bigr)^{+d}`$ の対応する要素は $`(x_1 + kd + d,\ x_2)`$、
$`\bigl(B^{+d}\bigr)^{+kd}`$ の対応する要素は $`(x_1 + d + kd,\ x_2)`$ であり、
自然数の加法の結合律と交換律により $`x_1 + kd + d = x_1 + d + kd`$ である。
第 2 成分はどちらも $`x_2`$ で変わらない。よって第 $`k`$ 項どうしは等しく、
連結も等しい。∎

<a id="d-AscArgDom"></a>
## 定義: 上昇コピーの引数支配 (D.AscArgDom)

命題 $`\mathrm{AscArgDom}`$ を次で定める。ここで $`B := (v_0,w_0) :: R`$、
$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr)`$ と略記し、
$`\mathrm{tw}_a S`$ は $`S`$ の先頭から第 1 成分が $`a`$ より大きい要素が続く極大な前部分列である。

```math
\begin{aligned}
\mathrm{AscArgDom} :\equiv\ &\forall G, R, S \in \mathrm{PairSeq},\ \forall v_0, w_0, d_0 \in \mathbb{N}, \cr
&\quad H \in \mathrm{ST\_PS}
  \ \to\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS} \cr
&\quad \to\ \bigl(\forall x \in R,\ v_0 \lt x_1\bigr) \ \to\ 0 \lt d_0 \cr
&\quad \to\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert \cr
&\quad \to\ \exists m,\
   \mathrm{tw}_{v_0+d_0} S \preceq_{\mathrm{lex}}
     \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B^{+d_0},\ m)\bigr)^{+d_0} .
\end{aligned}
```

<a id="t-shiftr0_append"></a>
## 定理: 平行移動は連結を保つ (T.shiftr0_append)

### 定理

$`d \in \mathbb{N}`$、$`A, B \in \mathrm{PairSeq}`$ に対し
$`(A \mathbin{+\!\!+} B)^{+d} = A^{+d} \mathbin{+\!\!+} B^{+d}`$。

### 証明

$`X^{+d}`$ の定義（D.shiftr0）より $`X^{+d}`$ は $`X`$ の各要素への写像 $`x \mapsto (x_1+d,\ x_2)`$ の
適用であり、連結した列の各要素への写像の適用は、それぞれに適用してから連結したものに等しい。∎

<a id="t-copies_succ_back"></a>
## 定理: コピー塔の末尾の 1 個 (T.copies_succ_back)

### 定理

$`d, n \in \mathbb{N}`$、$`B \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{cp}_d(B, n+1) = \mathrm{cp}_d(B, n) \mathbin{+\!\!+} B^{+nd} .
```

### 証明

$`\mathrm{cp}_d`$ の定義（D.copies）は、添字 $`k`$ を $`0`$ から $`n`$ まで（すなわち長さ $`n+1`$ の
添字列にわたって）走らせた $`B^{+kd}`$ の連結である。添字列を先頭 $`n`$ 個と最後の 1 個 $`k = n`$ に
分ければ

```math
\mathrm{cp}_d(B, n+1)
 = \bigl(B^{+0\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d}\bigr) \mathbin{+\!\!+} B^{+nd}
```

であり、括弧の中は $`\mathrm{cp}_d(B, n)`$ そのものである。∎

<a id="t-asc_crux1_of_argdom"></a>
## 定理: 引数支配から頭を取った核心 (T.asc_crux1_of_argdom)

### 定理

$`\mathrm{AscArgDom}`$ ならば $`\mathrm{AscCrux1}`$。

### 証明

$`G, R, S \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$ を取り、$`\mathrm{AscCrux1}`$ の
5 つの仮定

```math
\begin{aligned}
&(1)\ H \in \mathrm{ST\_PS}
  \quad\bigl(H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} ((v_0+d_0,\ w_0+1)),\ B := (v_0,w_0) :: R\bigr), \cr
&(2)\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS}, \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ 0 \lt d_0, \cr
&(5)\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert
\end{aligned}
```

を仮定する。$`\mathrm{AscArgDom}`$ をこの (1)〜(5) に適用して、$`m`$ と

```math
(\ast)\qquad S_{\mathrm{hi}} \preceq_{\mathrm{lex}}
  \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0},
\qquad
S_{\mathrm{hi}} := \mathrm{tw}_{v_0+d_0} S,\quad B' := B^{+d_0}
```

を得る。さらに $`S_{\mathrm{lo}} := \mathrm{dw}_{v_0+d_0} S`$ とおくと
$`S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}} = S`$ である。
また $`X^{+d}`$ の定義（D.shiftr0）より

```math
B' = B^{+d_0} = (v_0 + d_0,\ w_0) :: R^{+d_0}
```

である。

**第 1 段：$`\forall x \in R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m),\ v_0 \lt x_1`$。**
$`x \in R`$ のときは (3) による。$`x \in \mathrm{cp}_{d_0}(B', m)`$ のときは次のようにする。
(3) より $`\forall y \in R,\ v_0 \le y_1`$ であるから、
[T.mem_shiftr0_le](#t-mem_shiftr0_le) を $`d := v_0`$、$`e := d_0`$ として適用して
$`\forall y \in R^{+d_0},\ v_0 + d_0 \le y_1`$ を得る。
[T.copies_v0_le](Cnf.md#t-copies_v0_le) を、基点 $`v_0 + d_0`$、行 $`1`$ の値 $`w_0`$、
尾部 $`R^{+d_0}`$（すなわち $`B' = (v_0+d_0,\ w_0) :: R^{+d_0}`$）、$`d := d_0`$、$`n := m`$ として
適用すると $`v_0 + d_0 \le x_1`$ を得る。(4) より $`v_0 \lt v_0 + d_0 \le x_1`$ である。

**第 2 段：$`S_{\mathrm{lo}} = ()`$ または $`(\mathrm{head}\,S_{\mathrm{lo}})_1 \le v_0 + d_0`$。**
$`S_{\mathrm{lo}} = \mathrm{dw}_{v_0+d_0} S`$ が空でなければ、その先頭要素 $`z`$ は述語を破る、
すなわち $`\neg(v_0 + d_0 \lt z_1)`$ をみたすから $`z_1 \le v_0 + d_0`$ である。

**第 3 段：目標の展開。**
求める witness として $`m + 2`$ を取る（$`1 \le m+2`$）。
$`E := \bigl((B')^{+m d_0}\bigr)^{+d_0}`$ とおく。

```math
\begin{aligned}
\bigl(\mathrm{cp}_{d_0}(B,\ m+2)\bigr)^{+d_0}
 &= \mathrm{cp}_{d_0}(B',\ m+2) \cr
 &= B' \mathbin{+\!\!+} \bigl(\mathrm{cp}_{d_0}(B',\ m+1)\bigr)^{+d_0} \cr
 &= B' \mathbin{+\!\!+} \Bigl(\bigl(\mathrm{cp}_{d_0}(B',\ m)\bigr)^{+d_0} \mathbin{+\!\!+} E\Bigr) \cr
 &= (v_0+d_0,\ w_0) :: \Bigl(R^{+d_0} \mathbin{+\!\!+}
      \bigl(\mathrm{cp}_{d_0}(B',\ m)\bigr)^{+d_0} \mathbin{+\!\!+} E\Bigr) \cr
 &= (v_0+d_0,\ w_0) :: \Bigl(\bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',\ m)\bigr)^{+d_0}
      \mathbin{+\!\!+} E\Bigr).
\end{aligned}
```

第 1 の等号は [T.shiftr0_copies](#t-shiftr0_copies)（$`B' = B^{+d_0}`$）、
第 2 の等号は [T.copies_succ_front](Cnf.md#t-copies_succ_front)、
第 3 の等号は [T.copies_succ_back](#t-copies_succ_back) と [T.shiftr0_append](#t-shiftr0_append)、
第 4 の等号は $`B' = (v_0+d_0,\ w_0) :: R^{+d_0}`$ と結合律、
第 5 の等号は [T.shiftr0_append](#t-shiftr0_append) による。

**第 4 段：$`E`$ の形。**
$`B' = (v_0+d_0,\ w_0) :: R^{+d_0} \ne ()`$ であり、
[T.shiftr0_length](#t-shiftr0_length) を 2 回使うと $`\lvert E\rvert = \lvert B'\rvert \gt 0`$、
すなわち $`E \ne ()`$ である。また $`X^{+d}`$ の定義（D.shiftr0）は先頭要素を先頭要素に写すから、
$`B'`$ の先頭 $`(v_0+d_0,\ w_0)`$ に対応する $`E`$ の先頭は
$`\bigl(v_0 + d_0 + m d_0 + d_0,\ w_0\bigr)`$ であり、

```math
(\mathrm{head}\,E)_1 = v_0 + d_0 + m d_0 + d_0 .
```

**第 5 段：頭の消去。**
示すべきは第 3 段より

```math
(v_0+d_0,\ w_0) :: S \ \preceq_{\mathrm{lex}}\
 (v_0+d_0,\ w_0) :: \Bigl(\bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0} \mathbin{+\!\!+} E\Bigr)
```

である。両辺は長さ $`1`$ の列 $`\bigl((v_0+d_0,\ w_0)\bigr)`$ を共通の左側にもつ連結であるから、
[T.sle_append_cancel](#t-sle_append_cancel) によりこれは

```math
S \ \preceq_{\mathrm{lex}}\
 \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0} \mathbin{+\!\!+} E
```

と同値である。$`(\ast)`$ を $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）に従って 2 つの場合に分ける。

**(a) $`S_{\mathrm{hi}} = \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0}`$ のとき。**
$`S = S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}}`$ であるから、示すべきは

```math
S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}} \ \preceq_{\mathrm{lex}}\ S_{\mathrm{hi}} \mathbin{+\!\!+} E
```

であり、[T.sle_append_cancel](#t-sle_append_cancel) により
$`S_{\mathrm{lo}} \preceq_{\mathrm{lex}} E`$ を示せばよい。第 2 段で場合分けする。

- $`S_{\mathrm{lo}} = ()`$ のとき。第 4 段より $`E \ne ()`$ であるから、
  $`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式により $`() \prec_{\mathrm{lex}} E`$ であり、
  $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言が成り立つ。
- $`S_{\mathrm{lo}} = z :: Z`$ かつ $`z_1 \le v_0 + d_0`$ のとき。第 4 段より $`E \ne ()`$ だから
  $`E = e :: E'`$ と書け、$`e_1 = v_0 + d_0 + m d_0 + d_0`$ である。
  (4) の $`0 \lt d_0`$ より $`v_0 + d_0 \lt v_0 + d_0 + m d_0 + d_0`$ であるから
  $`z_1 \le v_0 + d_0 \lt e_1`$ であり、$`\mathrm{pairlt}`$ の定義（D.pairlt）の第 1 選言により
  $`\mathrm{pairlt}(z, e)`$、$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式の第 1 選言により
  $`z :: Z \prec_{\mathrm{lex}} e :: E'`$ を得る。

**(b) $`S_{\mathrm{hi}} \prec_{\mathrm{lex}} \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0}`$ のとき。**
[T.seqlex_splice](#t-seqlex_splice) を、小さい側の列を $`S_{\mathrm{hi}}`$、
大きい側の列を $`\bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0}`$、
小さい側に付ける列を $`S_{\mathrm{lo}}`$、大きい側に付ける列を $`E`$ として適用する。
残る仮定は次の選言である。

```math
S_{\mathrm{lo}} = ()
 \quad\vee\quad
\forall x \in \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',m)\bigr)^{+d_0},\
 \mathrm{pairlt}(\mathrm{head}\,S_{\mathrm{lo}},\ x)
```

第 2 段で場合分けする。

- $`S_{\mathrm{lo}} = ()`$ のとき。第 1 選言である。
- $`(\mathrm{head}\,S_{\mathrm{lo}})_1 \le v_0 + d_0`$ のとき。
  $`x \in \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',m)\bigr)^{+d_0}`$ とすると、
  [T.mem_shiftr0](Cnf.md#t-mem_shiftr0) よりある $`y \in R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',m)`$ が
  存在して $`x = (y_1 + d_0,\ y_2)`$ である。第 1 段より $`v_0 \lt y_1`$ であるから
  $`(\mathrm{head}\,S_{\mathrm{lo}})_1 \le v_0 + d_0 \lt y_1 + d_0 = x_1`$ であり、
  $`\mathrm{pairlt}`$ の定義（D.pairlt）の第 1 選言により
  $`\mathrm{pairlt}(\mathrm{head}\,S_{\mathrm{lo}},\ x)`$ が成り立つ。

こうして

```math
S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}} \prec_{\mathrm{lex}}
 \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0} \mathbin{+\!\!+} E
```

が得られ、$`S = S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}}`$ であるから、
第 5 段の目標が $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言として得られた。∎

<a id="t-asc_head_step"></a>
## 定理: 上昇コピーの核心の頭段 (T.asc_head_step)

### 定理

$`\mathrm{AscCrux1}`$ ならば $`\mathrm{AscCrux}`$。

### 証明

$`G, R, S \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell, q \in \mathbb{N}\times\mathbb{N}`$ を
取り、$`B := (v_0,w_0) :: R`$、$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$ とおいて
$`\mathrm{AscCrux}`$ の 8 つの仮定

```math
\begin{aligned}
&(1)\ H \in \mathrm{ST\_PS}, \qquad
 (2)\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S \in \mathrm{ST\_PS}, \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \qquad
 (4)\ 0 \lt d_0, \cr
&(5)\ \ell_2 = w_0 + 1, \qquad
 (6)\ \ell_1 = v_0 + d_0, \cr
&(7)\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert, \qquad
 (8)\ \mathrm{pairlt}(q, \ell)
\end{aligned}
```

を仮定する。(5)(6) より対 $`\ell`$ は両成分が定まり
$`\ell = (v_0 + d_0,\ w_0 + 1)`$ である。$`q`$ で場合分けする。

**(a) $`q = (v_0 + d_0,\ w_0)`$ のとき。**
$`\ell = (v_0+d_0,\ w_0+1)`$ により (1) と (7) を書き換えると、それぞれ
$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr) \in \mathrm{ST\_PS}`$ と
$`\lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert`$（$`H`$ も同じく書き換わる）になる。
また (2) は $`q = (v_0+d_0,\ w_0)`$ により
$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS}`$ である。
これらと (3)(4) に $`\mathrm{AscCrux1}`$ を適用すれば、求める $`m`$ と
$`q :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B,m)\bigr)^{+d_0}`$ が得られる。

**(b) $`q \ne (v_0 + d_0,\ w_0)`$ のとき。**
$`m := 1`$ と取る。[T.copies_one](Cnf.md#t-copies_one) より $`\mathrm{cp}_{d_0}(B, 1) = B`$ であり、
$`X^{+d}`$ の定義（D.shiftr0）より

```math
B^{+d_0} = (v_0 + d_0,\ w_0) :: R^{+d_0}
```

である。よって $`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式の第 1 選言により
$`\mathrm{pairlt}\bigl(q,\ (v_0+d_0,\ w_0)\bigr)`$ を示せばよい。
$`\ell = (v_0+d_0,\ w_0+1)`$ を (8) に代入すると、$`\mathrm{pairlt}`$ の定義（D.pairlt）より

```math
q_1 \lt v_0 + d_0 \quad\text{または}\quad \bigl(q_1 = v_0 + d_0 \ \wedge\ q_2 \lt w_0 + 1\bigr)
```

である。また $`q \ne (v_0+d_0,\ w_0)`$ は、対の相等が成分ごとの相等であることから
$`\neg\bigl(q_1 = v_0 + d_0 \ \wedge\ q_2 = w_0\bigr)`$ と同値である。場合分けする。

- $`q_1 \lt v_0 + d_0`$ のとき。$`\mathrm{pairlt}`$ の定義（D.pairlt）の第 1 選言が成り立つ。
- $`q_1 = v_0 + d_0`$ かつ $`q_2 \lt w_0 + 1`$ のとき。$`q_2 \le w_0`$ である。
  もし $`q_2 = w_0`$ なら $`q_1 = v_0 + d_0`$ と合わせて上の否定に反するから $`q_2 \ne w_0`$、
  よって $`q_2 \lt w_0`$ である。$`\mathrm{pairlt}`$ の定義（D.pairlt）の第 2 選言が成り立つ。

いずれの場合も $`q :: S \prec_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B,1)\bigr)^{+d_0}`$ であり、
$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言により結論を得る。∎

<a id="t-seqlex_cof_bad"></a>
## 定理: 第 4 分岐の共終性 (T.seqlex_cof_bad)

### 定理

$`\mathrm{AscCrux}`$ を仮定する。$`M, N \in \mathrm{PairSeq}`$ とし
$`j_1 := \lvert M\rvert - 1`$ とおく。

```math
M \in \mathrm{ST\_PS},\quad
N \in \mathrm{ST\_PS},\quad
1 \lt \lvert M\rvert,\quad
\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr),\quad
N \prec_{\mathrm{lex}} M
```

ならば、$`1 \le n`$ なる $`n`$ が存在して $`N \preceq_{\mathrm{lex}} M[n]`$。

### 証明

**第 1 段：ブロック分解。**
$`1 \lt \lvert M\rvert`$ より $`0 \lt \lvert M\rvert`$ であるから、
[T.hasParent_last_ST_PS](#t-hasParent_last_ST_PS) により
$`\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M, j_1),\ j_1\bigr)`$ が成り立つ。
また [T.blockok_ST_PS](Seqlex.md#t-blockok_ST_PS) と $`\mathrm{blockok}`$ の定義（D.blockok）の
第 3 連言子より $`\mathrm{steps}_1(M)`$、[T.r1ok_ST_PS](Column.md#t-r1ok_ST_PS) より
$`\mathrm{r1ok}(M)`$ である。これらに [T.oper_bad_blocks_all](#t-oper_bad_blocks_all) を適用して
$`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ を取り、
$`B := (v_0,w_0) :: R`$ とおくと

```math
\begin{aligned}
&(1)\ M = (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell), \cr
&(2)\ \forall n \ge 1,\ M[n] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n), \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ v_0 \lt \ell_1, \cr
&(5)\ \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr) \ \vee\
      \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
            \wedge \lvert G\rvert \to^M_1 j_1\bigr)
\end{aligned}
```

が成り立つ。

**第 2 段：$`N`$ の場合分け。**
(1) により仮定 $`N \prec_{\mathrm{lex}} M`$ は
$`N \prec_{\mathrm{lex}} (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$ である。
[T.seqlex_snoc_cases](#t-seqlex_snoc_cases) を $`D := G \mathbin{+\!\!+} B`$ として適用すると、
次の 2 つの場合に分かれる。

**(a) $`N \preceq_{\mathrm{lex}} G \mathbin{+\!\!+} B`$ のとき。**
$`n := 1`$ と取る。(2) と [T.copies_one](Cnf.md#t-copies_one) より
$`M[1] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B,1) = G \mathbin{+\!\!+} B`$ であるから、
仮定がそのまま結論である。

**(b) $`N = (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S`$ かつ $`\mathrm{pairlt}(q, \ell)`$ なる
$`q, S`$ が存在するとき。**
まず、$`1 \le m`$ なる $`m`$ で

```math
(\dagger)\qquad q :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B, m)\bigr)^{+d_0}
```

をみたすものを構成する。(5) の選言で場合分けする。

**(b-1) $`d_0 = 0`$、$`\ell_2 = 0`$、$`\ell_1 = v_0 + 1`$ のとき。**
$`X^{+0} = X`$（$`X^{+d}`$ の定義 D.shiftr0 で $`d = 0`$ とすると各要素が変わらない）であるから、
$`(\dagger)`$ は $`q :: S \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$ と同じ主張である。
[T.crux_zero](#t-crux_zero) を、その仮定 (1) として
$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S = N \in \mathrm{ST\_PS}`$、
仮定 (2) として本証明の (3)、仮定 (3) として $`\ell_2 = 0 \wedge \ell_1 = v_0+1`$、
仮定 (4) として $`\mathrm{pairlt}(q,\ell)`$ を与えて適用すればよい。

**(b-2) $`0 \lt d_0`$、$`\ell_2 = w_0 + 1`$、$`\ell_1 = v_0 + d_0`$、
$`\lvert G\rvert \to^M_1 j_1`$ のとき。**
(1) より $`\lvert M\rvert = \lvert G \mathbin{+\!\!+} B\rvert + 1`$ であるから
$`j_1 = \lvert M\rvert - 1 = \lvert G \mathbin{+\!\!+} B\rvert`$ であり、(1) と合わせて
$`\lvert G\rvert \to^M_1 j_1`$ は

```math
\lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert,
\qquad H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)
```

と同じ主張である。$`\mathrm{AscCrux}`$ を、その 8 つの仮定として
$`H = M \in \mathrm{ST\_PS}`$、$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S = N \in \mathrm{ST\_PS}`$、
本証明の (3)、$`0 \lt d_0`$、$`\ell_2 = w_0+1`$、$`\ell_1 = v_0+d_0`$、
いま書き換えた $`\lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert`$、$`\mathrm{pairlt}(q,\ell)`$ を
与えて適用すると $`(\dagger)`$ を得る。

**第 3 段：結論。**
$`n := m + 1`$ と取る（$`1 \le m + 1`$）。(2) と
[T.copies_succ_front](Cnf.md#t-copies_succ_front) より

```math
M[m+1] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, m+1)
 = G \mathbin{+\!\!+} \Bigl(B \mathbin{+\!\!+} \bigl(\mathrm{cp}_{d_0}(B,m)\bigr)^{+d_0}\Bigr)
```

であり、他方 (b) の $`N`$ は結合律により
$`N = G \mathbin{+\!\!+} \bigl(B \mathbin{+\!\!+} q :: S\bigr)`$ である。
[T.sle_append_cancel](#t-sle_append_cancel) を左側 $`G`$ について適用し、ついで左側 $`B`$ について
適用すると、示すべき $`N \preceq_{\mathrm{lex}} M[m+1]`$ は $`(\dagger)`$ と同値になる。∎

<a id="t-seqlex_cofinality_of_crux"></a>
## 定理: 核心からの列辞書式共終性 (T.seqlex_cofinality_of_crux)

### 定理

$`\mathrm{AscCrux}`$ ならば $`\mathrm{SeqlexCofinality}`$。

### 証明

$`M, N \in \mathrm{PairSeq}`$ を取り、$`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、
$`N \prec_{\mathrm{lex}} M`$ を仮定する。$`j_1 := \lvert M\rvert - 1`$ とおく。
求めるのは $`1 \le n`$ なる $`n`$ で $`N \preceq_{\mathrm{lex}} M[n]`$ をみたすものである。

**(a) $`j_1 = 0`$ のとき。**
[T.seqlex_cof_short](#t-seqlex_cof_short) を適用する。

**(b) $`j_1 \ne 0`$ かつ $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。**
自然数の減法は切り捨て減法であるから、$`\lvert M\rvert - 1 \ne 0`$ は $`1 \lt \lvert M\rvert`$ と
同値である。[T.seqlex_cof_zero](#t-seqlex_cof_zero) を適用する。

**(c) $`j_1 \ne 0`$ かつ $`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$ のとき。**
(b) と同じく $`1 \lt \lvert M\rvert`$ である。
[T.seqlex_cof_bad](#t-seqlex_cof_bad) を $`\mathrm{AscCrux}`$ の仮定のもとで適用する。

3 つの場合は $`j_1 = 0`$ か否か、および $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ か否かで
尽くされている。∎

<a id="t-pss_cofinality_of_crux"></a>
## 定理: 核心からの PSS 共終性 (T.pss_cofinality_of_crux)

### 定理

$`\mathrm{AscCrux1}`$ を仮定する。$`M, N \in \mathrm{PairSeq}`$ が
$`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ を
みたすならば、$`1 \le n`$ なる $`n`$ が存在して
$`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$。

### 証明

[T.asc_head_step](#t-asc_head_step) を仮定 $`\mathrm{AscCrux1}`$ に適用して $`\mathrm{AscCrux}`$ を得る。
これに [T.seqlex_cofinality_of_crux](#t-seqlex_cofinality_of_crux) を適用して
$`\mathrm{SeqlexCofinality}`$ を得る。
これに [T.pss_cofinality_of_seqlex](#t-pss_cofinality_of_seqlex) を
$`M`$、$`N`$、および 3 つの仮定 $`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ とともに適用すれば結論を得る。∎

<a id="t-pss_cofinality_of_argdom"></a>
## 定理: 引数支配からの PSS 共終性 (T.pss_cofinality_of_argdom)

### 定理

$`\mathrm{AscArgDom}`$ を仮定する。$`M, N \in \mathrm{PairSeq}`$ が
$`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ を
みたすならば、$`1 \le n`$ なる $`n`$ が存在して
$`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$。

### 証明

[T.asc_crux1_of_argdom](#t-asc_crux1_of_argdom) を仮定 $`\mathrm{AscArgDom}`$ に適用して
$`\mathrm{AscCrux1}`$ を得る。これに [T.pss_cofinality_of_crux](#t-pss_cofinality_of_crux) を
$`M`$、$`N`$、および 3 つの仮定 $`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ とともに適用すれば結論を得る。∎
