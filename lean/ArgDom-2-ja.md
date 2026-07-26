[← README](README-ja.md) | [English](ArgDom-2.md) | [Japanese](ArgDom-2-ja.md) | ArgDom [1](ArgDom-ja.md) **2** [3](ArgDom-3-ja.md) [4](ArgDom-4-ja.md) [5](ArgDom-5-ja.md)

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

（$`N\langle j\rangle`$ [D.entry](Pss-ja.md#d-entry)）

### 証明

結合則により $`N`$ は

```math
N = X \mathbin{+\!\!+} \Bigl((u,w) :: \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: ((B \mathbin{+\!\!+} A_2) \mathbin{+\!\!+} Z)\bigr)\Bigr)
```

と書ける。$`T := A_1 \mathbin{+\!\!+} (u+e,w) :: ((B \mathbin{+\!\!+} A_2) \mathbin{+\!\!+} Z)`$ とおく。

**第 1 の主張。** [T.getD_append_right'](Cofinality-ja.md#t-getD_append_right') を $`X`$ と $`(u,w) :: T`$、添字 $`0`$ に適用すると

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
$`\mathrm{ArgDomCoreOn}(\Delta_0^v)`$（$`\mathrm{ArgDomCoreOn}`$ [D.ArgDomCoreOn](ArgDom-ja.md#d-ArgDomCoreOn)、$`\Delta_0^v`$ [D.diagSeq](Pss-ja.md#d-diagSeq)）。

### 証明

D.ArgDomCoreOn にしたがい $`X, A_1, B, A_2, Z`$ と $`u, w, e`$ を取り、
条件 (1) から (8) を仮定する。条件 (1) を [T.argdom_pos](#t-argdom_pos) に適用すると

```math
\Delta_0^v\bigl\langle \lvert X\rvert \bigr\rangle = (u,w), \qquad
\Delta_0^v\bigl\langle \lvert X\rvert + (\lvert A_1\rvert + 1) \bigr\rangle = (u+e,\ w), \qquad
\lvert X\rvert + (\lvert A_1\rvert + 1) \lt \bigl\lvert \Delta_0^v \bigr\rvert
```

を得る。[T.diagSeq0_length](Column-2-ja.md#t-diagSeq0_length) より
$`\lvert \Delta_0^v\rvert = v + 1`$ であるから

```math
\lvert X\rvert \le \lvert X\rvert + (\lvert A_1\rvert + 1) \lt v + 1
```

であり、[T.diagSeq0_getD](Column-2-ja.md#t-diagSeq0_getD) を添字 $`\lvert X\rvert`$ と
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

$`N \in \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）、$`p \in \mathbb{N}\times\mathbb{N}`$ とし
$`p_1 = 0`$ とする。
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
- 条件 (7)：$`Z \mathbin{+\!\!+} (p) = () \vee (\mathrm{head}(Z \mathbin{+\!\!+} (p)))_1 \le u`$ を示す。
  $`Z = ()`$ のときは $`Z \mathbin{+\!\!+} (p) = (p)`$ であり、
  $`(\mathrm{head}(p))_1 = p_1 = 0 \le u`$ であるから第 2 選言が成り立つ。
  $`Z = z :: Z'`$ のときは $`\mathrm{head}(Z \mathbin{+\!\!+} (p)) = \mathrm{head}\,Z`$ であり、
  $`N`$ についての条件 (7) の第 1 選言 $`Z = ()`$ は偽であるから第 2 選言
  $`(\mathrm{head}\,Z)_1 \le u`$ が成り立ち、これが求めるものである。

よって結論 (9)

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

が得られる（$`\preceq_{\mathrm{lex}}`$ [D.sle](Cofinality-ja.md#d-sle)、
$`L^{+d}`$ [D.shiftr0](Cnf-2-ja.md#d-shiftr0)）。これは $`N`$ についての結論 (9) と同一である。∎

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

$`d \in \mathbb{N}`$、$`L \in \mathrm{PairSeq}`$ に対し、$`L`$ の各対の第 1 成分から一様に $`d`$ を
引いた列を $`L^{-d}`$ と書く。すなわち $`L = (L_0, \dots, L_{\lvert L\rvert - 1})`$ のとき

```math
L^{-d} := \Bigl(\,\bigl((L_0)_1 - d,\ (L_0)_2\bigr),\ \dots,\
  \bigl((L_{\lvert L\rvert - 1})_1 - d,\ (L_{\lvert L\rvert - 1})_2\bigr)\,\Bigr).
```

ここで $`-`$ は自然数の切り捨て減法である。

<a id="t-shiftl0_cons"></a>
## 定理: 左シフトと先頭 (T.shiftl0_cons)

### 定理

$`d \in \mathbb{N}`$、$`p \in \mathbb{N}\times\mathbb{N}`$、$`A \in \mathrm{PairSeq}`$ に対し

```math
(p :: A)^{-d} = (p_1 - d,\ p_2) :: A^{-d} .
```

### 証明

$`(\cdot)^{-d}`$ の定義（D.shiftl0）は各要素への写像であり、
先頭要素の像が $`(p_1-d,\ p_2)`$、残りの像が $`A^{-d}`$ であるから、
両辺は定義により同一の列である。∎

<a id="t-shiftl0_append"></a>
## 定理: 左シフトと連結 (T.shiftl0_append)

### 定理

$`d \in \mathbb{N}`$、$`A, B \in \mathrm{PairSeq}`$ に対し

```math
(A \mathbin{+\!\!+} B)^{-d} = A^{-d} \mathbin{+\!\!+} B^{-d} .
```

### 証明

各要素への写像は連結と可換である。すなわち $`A \mathbin{+\!\!+} B`$ の各要素の像を並べた列は、
$`A`$ の各要素の像を並べた列と $`B`$ の各要素の像を並べた列の連結である。∎

<a id="t-mem_shiftl0"></a>
## 定理: 左シフトの要素 (T.mem_shiftl0)

### 定理

$`d \in \mathbb{N}`$、$`M \in \mathrm{PairSeq}`$、$`x \in \mathbb{N}\times\mathbb{N}`$ に対し

```math
x \in M^{-d} \iff \exists p \in M,\ (p_1 - d,\ p_2) = x .
```

### 証明

$`M^{-d}`$ は $`M`$ の各要素 $`p`$ を $`(p_1-d,\ p_2)`$ に置き換えた列であるから
（D.shiftl0）、その要素であることは、$`M`$ のある要素 $`p`$ の像であることと同値である。∎

<a id="t-shiftl0_shiftr0"></a>
## 定理: 左シフトは右シフトの左逆 (T.shiftl0_shiftr0)

### 定理

$`d \in \mathbb{N}`$、$`X \in \mathrm{PairSeq}`$ に対し
$`(X^{+d})^{-d} = X`$。

### 証明

$`X`$ の長さに関する帰納法。帰納法の述語は

```math
\Lambda(X) :\equiv (X^{+d})^{-d} = X .
```

- **基底段** $`X = ()`$：$`()^{+d} = ()`$、$`()^{-d} = ()`$ であるから
  両辺は $`()`$ である。

- **帰納段** $`X = p :: X'`$：$`\Lambda(X')`$、すなわち
  $`(X'^{+d})^{-d} = X'`$ を仮定する。[T.shiftr0_cons](Cnf-2-ja.md#t-shiftr0_cons) と
  [T.shiftl0_cons](#t-shiftl0_cons) により

```math
\bigl((p :: X')^{+d}\bigr)^{-d}
  = \bigl((p_1 + d,\ p_2) :: X'^{+d}\bigr)^{-d}
  = \bigl((p_1 + d) - d,\ p_2\bigr) :: (X'^{+d})^{-d}
```

  である。$`(p_1 + d) - d = p_1`$ であり、帰納法の仮定より
  $`(X'^{+d})^{-d} = X'`$ であるから、右辺は
  $`(p_1,\ p_2) :: X' = p :: X'`$ に等しい。∎

<a id="t-shiftr0_shiftl0"></a>
## 定理: 行 0 が $`d`$ 以上なら右シフトは左シフトの逆 (T.shiftr0_shiftl0)

### 定理

$`d \in \mathbb{N}`$、$`L \in \mathrm{PairSeq}`$ とし、$`\forall x \in L,\ d \le x_1`$ とする。
このとき $`(L^{-d})^{+d} = L`$。

### 証明

$`L`$ の長さに関する帰納法。帰納法の述語は

```math
\Upsilon(L) :\equiv
  \bigl(\forall x \in L,\ d \le x_1\bigr) \to (L^{-d})^{+d} = L .
```

- **基底段** $`L = ()`$：$`()^{-d} = ()`$、$`()^{+d} = ()`$ であるから
  両辺は $`()`$ である。

- **帰納段** $`L = p :: L'`$：$`\Upsilon(L')`$ を仮定する。
  仮定 $`\forall x \in p :: L',\ d \le x_1`$ から、$`p`$ を取って $`d \le p_1`$ が、
  $`L'`$ の各要素を取って $`\forall x \in L',\ d \le x_1`$ が従う。
  後者に帰納法の仮定 $`\Upsilon(L')`$ を適用して
  $`(L'^{-d})^{+d} = L'`$ を得る。
  [T.shiftl0_cons](#t-shiftl0_cons) と [T.shiftr0_cons](Cnf-2-ja.md#t-shiftr0_cons) により

```math
\bigl((p :: L')^{-d}\bigr)^{+d}
  = \bigl((p_1 - d,\ p_2) :: L'^{-d}\bigr)^{+d}
  = \bigl((p_1 - d) + d,\ p_2\bigr) :: (L'^{-d})^{+d}
```

  である。$`d \le p_1`$ であるから切り捨て減法について $`(p_1 - d) + d = p_1`$ であり、
  また $`(L'^{-d})^{+d} = L'`$ であるから、右辺は
  $`(p_1,\ p_2) :: L' = p :: L'`$ に等しい。∎

<a id="t-shiftr0_comm"></a>
## 定理: 右シフトどうしの可換性 (T.shiftr0_comm)

### 定理

$`d, e \in \mathbb{N}`$、$`L \in \mathrm{PairSeq}`$ に対し

```math
(L^{+d})^{+e} = (L^{+e})^{+d} .
```

### 証明

$`(\cdot)^{+d}`$ の定義（D.shiftr0）より、左辺は $`L`$ の各要素 $`p`$ を
$`\bigl((p_1 + d) + e,\ p_2\bigr)`$ に置き換えた列であり、右辺は各要素 $`p`$ を
$`\bigl((p_1 + e) + d,\ p_2\bigr)`$ に置き換えた列である。
自然数の加法の結合律と交換律より $`(p_1 + d) + e = (p_1 + e) + d`$ であるから、
2 つの写像は各 $`p`$ について同じ値を取り、したがって両辺の列は等しい。∎

<a id="t-argDomCoreOn_shiftr0"></a>
## 定理: 中核は一様な右シフトと可換 (T.argDomCoreOn_shiftr0)

### 定理

$`W \in \mathrm{PairSeq}`$、$`d \in \mathbb{N}`$ とする。$`\mathrm{ArgDomCoreOn}(W)`$ ならば
$`\mathrm{ArgDomCoreOn}(W^{+d})`$。

### 証明

D.ArgDomCoreOn にしたがい $`X, A_1, B, A_2, Z`$ と $`u, w, e`$ を取り、
$`W^{+d}`$ についての条件 (1) から (8) を仮定する。すなわち

```math
W^{+d}
  = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z
```

であり、$`0 \lt e`$、$`\forall x \in A_1,\ u \lt x_1`$、$`\forall x \in B,\ u+e \lt x_1`$、
$`\forall x \in A_2,\ u \lt x_1`$、$`A_2 = () \vee (\mathrm{head}\,A_2)_1 \le u+e`$、
$`Z = () \vee (\mathrm{head}\,Z)_1 \le u`$、$`\mathrm{SpineOK}(A_1,\ u+e,\ w)`$（[D.SpineOK](ArgDom-ja.md#d-SpineOK)）が
成り立つ。

**すべての列の行 0 は $`d`$ 以上である。** 条件 (1) の右辺の任意の要素 $`x`$ は
$`W^{+d}`$ の要素であるから、[T.mem_shiftr0](Cnf-2-ja.md#t-mem_shiftr0) により
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
X' := X^{-d}, \quad A_1' := A_1^{-d}, \quad B' := B^{-d}, \quad
A_2' := A_2^{-d}, \quad Z' := Z^{-d}
```

とおく。いま示した行 0 の下界と [T.shiftr0_shiftl0](#t-shiftr0_shiftl0) により

```math
X'^{+d} = X, \quad A_1'^{+d} = A_1, \quad B'^{+d} = B, \quad
A_2'^{+d} = A_2, \quad Z'^{+d} = Z
```

である。条件 (1) の両辺に $`(\cdot)^{-d}`$ を施すと、左辺は
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

**(4)** $`\forall x \in B',\ u' + e \lt x_1`$。$`x \in B'`$ とすると
[T.mem_shiftl0](#t-mem_shiftl0) により $`B`$ のある要素 $`q`$ について
$`x = (q_1 - d,\ q_2)`$ であり、$`u + e \lt q_1`$、$`d \le q_1`$、$`d \le u`$ から
$`u' + e = u + e - d \lt q_1 - d = x_1`$ である。

**(5)** $`\forall x \in A_2',\ u' \lt x_1`$。$`x \in A_2'`$ とすると
[T.mem_shiftl0](#t-mem_shiftl0) により $`A_2`$ のある要素 $`q`$ について
$`x = (q_1 - d,\ q_2)`$ であり、$`u \lt q_1`$、$`d \le q_1`$、$`d \le u`$ から
$`u' \lt x_1`$ である。

**(6)** $`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u' + e`$。
$`A_2 = ()`$ のときは $`A_2' = ()^{-d} = ()`$ であり第 1 選言が成り立つ。
$`A_2 = a :: A_2''`$ のときは、条件 (6) の第 1 選言が偽であるから
$`(\mathrm{head}\,A_2)_1 = a_1 \le u + e`$ である。また $`d \le a_1`$ である。
[T.shiftl0_cons](#t-shiftl0_cons) より $`\mathrm{head}\,A_2' = (a_1 - d,\ a_2)`$ であり、
$`d \le u`$ と合わせて $`a_1 - d \le u + e - d = u' + e`$ である。

**(7)** $`Z' = () \vee (\mathrm{head}\,Z')_1 \le u'`$。
$`Z = ()`$ のときは $`Z' = ()`$ であり第 1 選言が成り立つ。
$`Z = z :: Z''`$ のときは、条件 (7) の第 1 選言が偽であるから
$`(\mathrm{head}\,Z)_1 = z_1 \le u`$ である。[T.shiftl0_cons](#t-shiftl0_cons) より
$`\mathrm{head}\,Z' = (z_1 - d,\ z_2)`$ であり、$`z_1 - d \le u - d = u'`$ である。

**(8)** $`\mathrm{SpineOK}(A_1',\ u' + e,\ w)`$。D.SpineOK にしたがい
$`U', V' \in \mathrm{PairSeq}`$ と $`x' \in \mathbb{N}\times\mathbb{N}`$ を取り、

```math
A_1' = U' \mathbin{+\!\!+} x' :: V', \qquad x'_1 \lt u' + e, \qquad \forall y \in V',\ x'_1 \lt y_1
```

を仮定して $`w \le x'_2`$ を示す。この分解の両辺に $`(\cdot)^{+d}`$ を施すと、
左辺は $`A_1'^{+d} = A_1`$ であり、右辺は [T.shiftr0_append](Cofinality-3-ja.md#t-shiftr0_append) と [T.shiftr0_cons](Cnf-2-ja.md#t-shiftr0_cons) により

```math
A_1 = U'^{+d} \mathbin{+\!\!+} (x'_1 + d,\ x'_2) :: V'^{+d}
```

である。$`\mathrm{SpineOK}(A_1,\ u+e,\ w)`$ を
$`U := U'^{+d}`$、$`V := V'^{+d}`$、$`x := (x'_1 + d,\ x'_2)`$ に適用する。
その 3 条件は次のようにみたされる。

- 分解式は上で得たものである。
- $`x'_1 + d \lt u + e`$：$`x'_1 \lt u' + e = u + e - d`$ と $`d \le u \le u + e`$ から従う。
- $`\forall y \in V'^{+d},\ x'_1 + d \lt y_1`$：[T.mem_shiftr0](Cnf-2-ja.md#t-mem_shiftr0) により
  $`V'`$ のある要素 $`q`$ について $`y = (q_1 + d,\ q_2)`$ であり、
  仮定より $`x'_1 \lt q_1`$ であるから $`x'_1 + d \lt q_1 + d = y_1`$ である。

よって $`w \le \bigl((x'_1 + d,\ x'_2)\bigr)_2 = x'_2`$ が得られる。

**中核の適用と結論の押し上げ。** 仮定 $`\mathrm{ArgDomCoreOn}(W)`$ を
$`X := X'`$, $`A_1 := A_1'`$, $`B := B'`$, $`A_2 := A_2'`$, $`Z := Z'`$,
$`u := u'`$、およびもとの $`w`$, $`e`$ に適用すると、結論 (9)

```math
B' \preceq_{\mathrm{lex}} \bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+e}
```

を得る。ここで [T.shiftr0_comm](#t-shiftr0_comm) と
$`A_1'^{+d} = A_1`$、$`B'^{+d} = B`$、$`A_2'^{+d} = A_2`$、
および $`(u'+e)+d = u+e`$（$`d \le u`$ による）を用いると

```math
\begin{aligned}
&\Bigl(\bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+e}\Bigr)^{+d} \cr
&\qquad = \Bigl(\bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+d}\Bigr)^{+e} \cr
&\qquad = \bigl(A_1 \mathbin{+\!\!+} (u+e,\ w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
\end{aligned}
```

である。したがって示すべき結論 (9)

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,\ w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

は、$`B = B'^{+d}`$ を代入すると

```math
B'^{+d} \preceq_{\mathrm{lex}}
  \Bigl(\bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+e}\Bigr)^{+d}
```

と同じ主張である。[T.sle_shiftr0](ArgDom-ja.md#t-sle_shiftr0) の右から左により、
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

（$`\mathrm{copies}_d`$ [D.copies](Cnf-2-ja.md#d-copies)）

### 証明

$`1 \le n`$ より $`n = m + 1`$ なる $`m`$ が取れる。
[T.copies_succ_front](Cnf-3-ja.md#t-copies_succ_front) より

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
[T.shiftr0_append](Cofinality-3-ja.md#t-shiftr0_append) より連結を保ち
$`(L \mathbin{+\!\!+} L')^{+d} = L^{+d} \mathbin{+\!\!+} L'^{+d}`$、
[T.shiftr0_cons](Cnf-2-ja.md#t-shiftr0_cons) より
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
[T.shiftr0_length](Cofinality-2-ja.md#t-shiftr0_length) より $`\lvert L^{+d}\rvert = \lvert L\rvert`$ であるから、
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

（$`\mathrm{ST\_PS}`$ [D.ST_PS](Pss-ja.md#d-ST_PS)、$`\to^M_1`$ [D.nextrel1](Pss-ja.md#d-nextrel1)）

さらに $`X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$、$`u, w, e \in \mathbb{N}`$ について次を仮定する。

```math
\begin{aligned}
&\text{(heq)}\quad   &&G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n) \cr
& &&\qquad = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z, \cr
&\text{(he)}\quad    &&0 \lt e, \cr
&\text{(h1)}\quad    &&\forall x \in A_1,\ u \lt x_1, \cr
&\text{(h2)}\quad    &&\forall x \in B,\ u + e \lt x_1, \cr
&\text{(h3)}\quad    &&\forall x \in A_2,\ u \lt x_1, \cr
&\text{(h4)}\quad    &&A_2 = () \ \vee\ (\mathrm{head}\,A_2)_1 \le u + e, \cr
&\text{(h5)}\quad    &&Z = () \ \vee\ (\mathrm{head}\,Z)_1 \le u, \cr
&\text{(h6)}\quad    &&\mathrm{SpineOK}(A_1,\ u+e,\ w), \cr
&\text{(hcase)}\quad &&\lvert G\rvert + (\lvert R\rvert + 1) \le \lvert X\rvert .
\end{aligned}
```

このとき

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e} .
```

### 証明

(hn) より $`n = m + 1`$ なる $`m`$ が取れる。以下 $`n`$ をこの形に書く。

**第 1 段：コピー 0 を剥がす。**
[T.copies_succ_front](Cnf-3-ja.md#t-copies_succ_front) と連結の結合律より

```math
\begin{aligned}
&G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1) \cr
&\qquad = G \mathbin{+\!\!+} \Bigl(\mathrm{blk} \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}\Bigr) \cr
&\qquad = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}
\end{aligned}
```

である。また (heq) の右辺も結合律で並べ替えられるから

```math
\begin{aligned}
&(G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0} \cr
&\qquad = X \mathbin{+\!\!+} \Bigl(\bigl((u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z\Bigr)
\end{aligned}
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

**(a) $`m = 0`$ のとき。** [T.copies_zero](Cnf-2-ja.md#t-copies_zero) より
$`\mathrm{copies}_{d_0}(\mathrm{blk}, 0) = ()`$ であり、
[T.shiftr0_nil](Cnf-2-ja.md#t-shiftr0_nil) より $`()^{+d_0} = ()`$ である。
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
  $`() = () \mathbin{+\!\!+} ()`$ である。$`B_p = ()`$ は要素をもたないから第 2 連言子の前件が偽で成り立つ。
  第 3 連言子は第 1 選言 $`R_p = ()`$ が成り立つ。

- **帰納段** $`E = a :: E'`$：$`\Phi(E')`$ を仮定する。$`L \lt a_1`$ かどうかで場合分けする。

  - $`L \lt a_1`$ のとき。$`\Phi(E')`$ から $`B_p', R_p'`$ を取り、
    $`B_p := a :: B_p'`$、$`R_p := R_p'`$ と置く。
    $`a :: E' = a :: (B_p' \mathbin{+\!\!+} R_p') = (a :: B_p') \mathbin{+\!\!+} R_p'`$ である。
    $`x \in a :: B_p'`$ ならば $`x = a`$ か $`x \in B_p'`$ であり、前者は本場合の仮定 $`L \lt a_1`$、
    後者は $`\Phi(E')`$ の第 2 連言子により $`L \lt x_1`$。
    第 3 連言子は $`\Phi(E')`$ のものをそのまま用いる。

  - $`\neg(L \lt a_1)`$ のとき。$`B_p := ()`$、$`R_p := a :: E'`$ と置く。
    $`a :: E' = () \mathbin{+\!\!+} (a :: E')`$ である。$`B_p = ()`$ は要素をもたない。
    $`\mathrm{head}\,R_p = a`$ であり、$`\neg(L \lt a_1)`$ は $`\mathbb{N}`$ において $`a_1 \le L`$ と
    同値であるから第 3 連言子の第 2 選言が成り立つ。∎
