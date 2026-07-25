[← README](README.md) ｜ ArgDom [1](ArgDom.md) [2](ArgDom-2.md) [3](ArgDom-3.md) **4** [5](ArgDom-5.md)

<a id="t-argDomCoreOn_bad_A2"></a>
## 定理: 第 4 分岐の場合 A2（交差の場合） (T.argDomCoreOn_bad_A2)

### 定理

$`M, G, R, X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0, n, u, w, e \in \mathbb{N}`$、
$`\ell \in \mathbb{N}\times\mathbb{N}`$ とし、$`\mathrm{blk} := (v_0,w_0) :: R`$ とおく。
次を仮定する。

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
&\text{(hn)}\quad 1 \le n, \cr
&\text{(heq)}\quad G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n)
   = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr)
     \mathbin{+\!\!+} Z, \cr
&\text{(he)}\quad 0 \lt e, \cr
&\text{(h1)}\quad \forall x \in A_1,\ u \lt x_1, \cr
&\text{(h2)}\quad \forall x \in B,\ u + e \lt x_1, \cr
&\text{(h3)}\quad \forall x \in A_2,\ u \lt x_1, \cr
&\text{(h4)}\quad A_2 = () \ \vee\ (\mathrm{head}\,A_2)_1 \le u + e, \cr
&\text{(h5)}\quad Z = () \ \vee\ (\mathrm{head}\,Z)_1 \le u, \cr
&\text{(h6)}\quad \mathrm{SpineOK}(A_1,\ u+e,\ w), \cr
&\text{(hcaseL)}\quad \lvert X\rvert \lt \lvert G\rvert + (\lvert R\rvert + 1), \cr
&\text{(hcaseR)}\quad \lvert G\rvert + (\lvert R\rvert + 1) \le \lvert X\rvert + (\lvert A_1\rvert + 1).
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
L := \lvert R\rvert + 1 = \lvert\mathrm{blk}\rvert, \quad
p := \lvert G\rvert + L, \quad
N := G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n), \quad
i := \lvert X\rvert, \quad
j := \lvert X\rvert + (\lvert A_1\rvert + 1)
```

と書く。仮定 (hcaseL) は $`i \lt p`$、仮定 (hcaseR) は $`p \le j`$ である。

**第 0 段：$`2 \le n`$。**
[T.argdom_pos](ArgDom-2.md#t-argdom_pos) を (heq) に適用すると $`j \lt \lvert N\rvert`$ を得る。
一方 [T.copies_length](ArgDom-3.md#t-copies_length) より
$`\lvert \mathrm{copies}_{d_0}(\mathrm{blk}, n)\rvert = n \cdot L`$ であるから

```math
\lvert N\rvert = \lvert G\rvert + n \cdot L .
```

もし $`n = 1`$ ならば $`\lvert N\rvert = \lvert G\rvert + L = p`$ であり、$`j \lt p`$ となって
(hcaseR) の $`p \le j`$ に反する。(hn) より $`1 \le n`$ であったから $`2 \le n`$ である。
以下 $`n = m + 1`$、$`1 \le m`$ と書く。

**第 1 段：コピー $`0`$ を剥がし、境界 $`p`$ で切る。**
[T.copies_succ_front](Cnf-3.md#t-copies_succ_front) より

```math
N = G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1)
  = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0}
```

である。これと (heq) を結合し、結合律で括り直すと

```math
(\ast)\qquad
(G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0}
 = \bigl(X \mathbin{+\!\!+} ((u,w))\bigr)
   \mathbin{+\!\!+} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))\bigr)
```

を得る。(hcaseL) より $`\lvert X \mathbin{+\!\!+} ((u,w))\rvert = i + 1 \le p = \lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert`$
であるから、[T.split_append_left](ArgDom-3.md#t-split_append_left) を $`(\ast)`$ に適用して
$`C \in \mathrm{PairSeq}`$ を得る。

```math
\text{(C1)}\ G \mathbin{+\!\!+} \mathrm{blk} = \bigl(X \mathbin{+\!\!+} ((u,w))\bigr) \mathbin{+\!\!+} C,
\qquad
\text{(C2)}\ A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))
  = C \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0} .
```

(C1) の両辺の長さを比べて $`\lvert C\rvert = p - (i+1)`$ である。
(hcaseR) は $`p \le i + \lvert A_1\rvert + 1`$、すなわち $`\lvert C\rvert \le \lvert A_1\rvert`$ を与えるから、
ふたたび [T.split_append_left](ArgDom-3.md#t-split_append_left) を (C2) に適用して $`D \in \mathrm{PairSeq}`$ を得る。

```math
\text{(D1)}\ A_1 = C \mathbin{+\!\!+} D,
\qquad
\text{(D2)}\ \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0}
  = D \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)) .
```

(D1) の長さから $`\lvert A_1\rvert = \lvert C\rvert + \lvert D\rvert`$ である。

$`d_0`$ シフトされた列の要素はすべて第 1 成分が $`d_0`$ 以上である。実際、
$`y \in \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0}`$ ならば
[T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) より $`y = (z_1 + d_0,\ z_2)`$ の形であり
$`d_0 \le z_1 + d_0 = y_1`$ である。これを (D2) の右辺の要素 $`(u+e,w)`$ に適用して

```math
(\dagger)\qquad d_0 \le u + e
```

を得る。同じ理由で $`\forall y \in D,\ d_0 \le y_1`$ である。

**第 2 段：逆シフトして小さい塔を書く。**
(D2) の両辺に $`(\cdot)^{-d_0}`$ を施し、[T.shiftl0_shiftr0](ArgDom-2.md#t-shiftl0_shiftr0) と
[T.shiftl0_append](ArgDom-2.md#t-shiftl0_append)、[T.shiftl0_cons](ArgDom-2.md#t-shiftl0_cons) を使うと

```math
\text{(S)}\qquad \mathrm{copies}_{d_0}(\mathrm{blk}, m)
  = D^{-d_0} \mathbin{+\!\!+} (u+e-d_0,\ w) ::
      \bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
```

を得る。

**第 3 段：$`\lvert X\rvert`$ と $`\lvert G\rvert + \lvert D\rvert`$ の三分律。**
自然数の三分律により、次の 3 つのいずれかがちょうど 1 つ成り立つ。

**(a) $`\lvert X\rvert \lt \lvert G\rvert + \lvert D\rvert`$ のとき。**
$`1 \le m`$ であるから $`m = m'' + 1`$ と書ける。
[T.copies_succ_front](Cnf-3.md#t-copies_succ_front) より
$`\mathrm{copies}_{d_0}(\mathrm{blk}, m) = \mathrm{blk} \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m'')^{+d_0}`$
であるから $`\mathrm{blk} \sqsubseteq \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$ である。
また (S) より $`D^{-d_0} \sqsubseteq \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$ であり、
$`\lvert D^{-d_0}\rvert = \lvert D\rvert`$ である。

(C1) より $`X \mathbin{+\!\!+} ((u,w)) \sqsubseteq G \mathbin{+\!\!+} \mathrm{blk}`$ であり、
[T.prefix_append_left](ArgDom-3.md#t-prefix_append_left) より
$`G \mathbin{+\!\!+} \mathrm{blk} \sqsubseteq G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$ かつ
$`G \mathbin{+\!\!+} D^{-d_0} \sqsubseteq G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$ である。
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
\text{(Nm)}\qquad G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)
  = \bigl((X \mathbin{+\!\!+} ((u,w))) \mathbin{+\!\!+} A_1'\bigr) \mathbin{+\!\!+} (u+e-d_0,\ w) ::
      \bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
```

と書ける。

一方 [T.copies_succ_back](Cofinality-3.md#t-copies_succ_back) より

```math
G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1)
  = \bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr) \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}
```

である。これと (Nm)、および $`(\ast)`$ を合わせると、左因子 $`X \mathbin{+\!\!+} ((u,w))`$ を共有する
2 つの表示が得られる。左因子を消去して

```math
\text{(K)}\qquad
A_1 \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
= A_1' \mathbin{+\!\!+} (u+e-d_0,\ w) ::
   \Bigl(\bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
     \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}\Bigr)
```

を得る。$`\lvert A_1'\rvert \le \lvert A_1\rvert`$ であるから
（$`\lvert A_1\rvert = \lvert C\rvert + \lvert D\rvert`$、$`\lvert C\rvert = p - (i+1)`$、
$`\lvert A_1'\rvert = \lvert G\rvert + \lvert D\rvert - (i+1)`$ と $`\lvert G\rvert \le p`$ による）、
[T.split_append_left](ArgDom-3.md#t-split_append_left) を (K) に適用して $`W`$ を得る。

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
\bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr) \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}
 = W' \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

を得る。したがって

```math
\text{(A1dec)}\qquad A_1 = A_1' \mathbin{+\!\!+} (u+e-d_0,\ w) :: W' .
```

$`(u+e-d_0,\ w) \in A_1`$ であるから (h1) より $`u \lt u+e-d_0`$、すなわち

```math
(\ddagger)\qquad d_0 \lt e, \qquad u + e - d_0 = u + (e - d_0) .
```

**(a-1) 小さい塔についての分解。**

```math
A_2' := \mathrm{tw}_u\bigl(A_2^{-d_0}\bigr), \qquad
Z_2 := \mathrm{dw}_u\bigl(A_2^{-d_0}\bigr) \mathbin{+\!\!+} Z^{-d_0}
```

とおく。次の 5 つが成り立つ。

- $`A_2' \mathbin{+\!\!+} Z_2 = A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0}`$：
  $`\mathrm{tw}_u`$ と $`\mathrm{dw}_u`$ の連結が元の列であることによる。
- $`A_2' \sqsubseteq A_2^{-d_0}`$：$`\mathrm{tw}_u L`$ は $`L`$ の前部分列であることによる。
- $`\forall x \in A_2',\ u \lt x_1`$：$`\mathrm{tw}_u L`$ の各要素 $`x`$ が $`u \lt x_1`$ をみたすことによる。
- $`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u + (e-d_0)`$：
  $`A_2 = ()`$ なら $`A_2^{-d_0} = ()`$ で $`A_2' = ()`$。
  $`A_2 = a :: A_2''`$ なら (h4) の第 2 選言より $`a_1 \le u+e`$ であり、
  $`A_2^{-d_0} = (a_1 - d_0,\ a_2) :: (A_2'')^{-d_0}`$ である。
  $`u \lt a_1 - d_0`$ ならば $`A_2'`$ の先頭は $`(a_1-d_0,\ a_2)`$ であって
  $`a_1 - d_0 \le u + e - d_0 = u + (e-d_0)`$（$`(\ddagger)`$ による）。
  $`\neg(u \lt a_1 - d_0)`$ ならば $`A_2' = ()`$。
- $`Z_2 = () \vee (\mathrm{head}\,Z_2)_1 \le u`$：
  $`\mathrm{dw}_u(A_2^{-d_0}) = z :: Z''`$ ならば $`\mathrm{dw}`$ の定義より $`\neg(u \lt z_1)`$、すなわち $`z_1 \le u`$。
  $`\mathrm{dw}_u(A_2^{-d_0}) = ()`$ ならば $`Z_2 = Z^{-d_0}`$ であり、$`Z = ()`$ なら $`Z_2 = ()`$、
  $`Z = z :: Z''`$ なら (h5) の第 2 選言より $`z_1 \le u`$ であるから $`z_1 - d_0 \le u`$。

これと (Nm) から

```math
\text{(eq')}\qquad G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)
 = \Bigl(X \mathbin{+\!\!+} (u,w) :: \bigl(A_1' \mathbin{+\!\!+} (u + (e-d_0),\ w) ::
     (B^{-d_0} \mathbin{+\!\!+} A_2')\bigr)\Bigr) \mathbin{+\!\!+} Z_2
```

が成り立つ。(hIH) を $`m`$ に適用する（$`1 \le m`$ かつ $`m \lt m+1 = n`$）ために、
$`\mathrm{ArgDomCoreOn}`$ の残りの仮定を確かめる。

- $`0 \lt e - d_0`$：$`(\ddagger)`$ による。
- $`\forall x \in A_1',\ u \lt x_1`$：(A1dec) より $`A_1'`$ の要素は $`A_1`$ の要素であり、(h1) による。
- $`\forall x \in B^{-d_0},\ u + (e-d_0) \lt x_1`$：$`x = (y_1 - d_0,\ y_2)`$（$`y \in B`$）と書ける。
  (h2) より $`u + e \lt y_1`$ であり、$`(\dagger)`$ の $`d_0 \le u+e`$ と合わせて
  $`y_1 - d_0 \gt u + e - d_0 = u + (e-d_0)`$。
- $`\forall x \in A_2',\ u \lt x_1`$、$`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u+(e-d_0)`$、
  $`Z_2 = () \vee (\mathrm{head}\,Z_2)_1 \le u`$：上に示した。

**(a-2) 小さい塔についての $`\mathrm{SpineOK}`$。**
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
[T.split_append_left](ArgDom-3.md#t-split_append_left) を (GSD) に適用して $`V_3`$ を得る。

```math
G = \bigl(Y \mathbin{+\!\!+} (x)\bigr) \mathbin{+\!\!+} V_3, \qquad V = V_3 \mathbin{+\!\!+} D^{-d_0} .
```

これを (C1) に代入し、共通の左因子 $`X \mathbin{+\!\!+} ((u,w))`$ を消去すると

```math
C = \bigl(U \mathbin{+\!\!+} (x)\bigr) \mathbin{+\!\!+} \bigl(V_3 \mathbin{+\!\!+} \mathrm{blk}\bigr)
```

であり、(D1) と合わせて

```math
A_1 = U \mathbin{+\!\!+} x :: \bigl((V_3 \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} D\bigr)
```

を得る。次に $`x_1 \lt v_0`$ を示す。$`\mathrm{blk} \ne ()`$ かつ $`1 \le m`$ であるから
[T.copies_headI](ArgDom-2.md#t-copies_headI) より
$`\mathrm{head}\,\mathrm{copies}_{d_0}(\mathrm{blk}, m) = \mathrm{head}\,\mathrm{blk} = (v_0,w_0)`$ である。
(S) の右辺の先頭で場合分けする。

- $`D^{-d_0} = ()`$ のとき。(S) の右辺の先頭は $`(u+e-d_0,\ w)`$ であるから
  $`u + e - d_0 = v_0`$ である。$`(\ddagger)`$ より $`u+(e-d_0) = v_0`$ であり、
  仮定 $`x_1 \lt u+(e-d_0)`$ から $`x_1 \lt v_0`$。
- $`D^{-d_0} = s :: S'`$ のとき。(S) の右辺の先頭は $`s`$ であるから $`s = (v_0,w_0)`$ である。
  $`V = V_3 \mathbin{+\!\!+} D^{-d_0}`$ より $`s \in V`$ であり、仮定 $`\forall y \in V,\ x_1 \lt y_1`$ から
  $`x_1 \lt s_1 = v_0`$。

そこで (h6) を $`U`$、$`(V_3 \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} D`$、$`x`$ に適用する。3 つの条件を確かめる。

- 分解 $`A_1 = U \mathbin{+\!\!+} x :: ((V_3 \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} D)`$：上に示した。
- $`x_1 \lt u + e`$：$`x_1 \lt u + (e-d_0) \le u + e`$。
- $`\forall y \in (V_3 \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} D,\ x_1 \lt y_1`$：$`y`$ の属する部分で分ける。
  $`y \in V_3`$ なら $`y \in V`$ であるから仮定による。
  $`y = (v_0,w_0)`$ なら $`x_1 \lt v_0 = y_1`$。
  $`y \in R`$ なら (hRgt) より $`v_0 \lt y_1`$ であり、$`x_1 \lt v_0`$ と合わせて $`x_1 \lt y_1`$。
  $`y \in D`$ なら (D2) より $`y \in \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0}`$ であるから
  [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) より $`y = (z_1+d_0,\ z_2)`$、
  $`z \in \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$ と書ける。(hRgt) より $`\forall x \in R,\ v_0 \le x_1`$ であるから
  [T.copies_v0_le](Cnf-3.md#t-copies_v0_le) が使えて $`v_0 \le z_1 \le z_1 + d_0 = y_1`$、
  したがって $`x_1 \lt v_0 \le y_1`$。

よって $`w \le x_2`$ を得る。

**$`\lvert G\rvert \le \lvert Y\rvert`$ のとき。**
[T.split_append_left](ArgDom-3.md#t-split_append_left) を (GSD) に適用して $`U_2`$ を得る。

```math
Y = G \mathbin{+\!\!+} U_2, \qquad D^{-d_0} = U_2 \mathbin{+\!\!+} x :: V .
```

$`\forall y \in D,\ d_0 \le y_1`$ は第 1 段で示したから、
[T.shiftr0_shiftl0](ArgDom-2.md#t-shiftr0_shiftl0) より $`(D^{-d_0})^{+d_0} = D`$ である。
第 2 式の両辺に $`(\cdot)^{+d_0}`$ を施し、
[T.shiftr0_append](Cofinality-3.md#t-shiftr0_append) と
[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons) を使って

```math
D = U_2^{+d_0} \mathbin{+\!\!+} (x_1 + d_0,\ x_2) :: V^{+d_0}
```

を得る。(h6) を $`C \mathbin{+\!\!+} U_2^{+d_0}`$、$`V^{+d_0}`$、$`(x_1+d_0,\ x_2)`$ に適用する。

- 分解：(D1) より
  $`A_1 = C \mathbin{+\!\!+} D = (C \mathbin{+\!\!+} U_2^{+d_0}) \mathbin{+\!\!+} (x_1+d_0,\ x_2) :: V^{+d_0}`$。
- $`x_1 + d_0 \lt u+e`$：$`x_1 \lt u+(e-d_0)`$ と $`(\ddagger)`$ の $`d_0 \lt e`$ から
  $`x_1 + d_0 \lt u + (e-d_0) + d_0 = u + e`$。
- $`\forall y \in V^{+d_0},\ x_1 + d_0 \lt y_1`$：$`y = (z_1+d_0,\ z_2)`$（$`z \in V`$）と書け、
  仮定 $`x_1 \lt z_1`$ から $`x_1 + d_0 \lt z_1 + d_0 = y_1`$。

よって $`w \le (x_1+d_0,\ x_2)_2 = x_2`$ を得る。以上で
$`\mathrm{SpineOK}(A_1',\ u+(e-d_0),\ w)`$ が示された。

**(a-3) 結論の持ち上げ。**
(hIH) を $`m`$ に適用し、(eq') と (a-1)(a-2) で確かめた仮定を与えると

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
  \bigl(Z_2 \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}\bigr)
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
これに (A1dec) と $`(\ddagger)`$ を使い [T.prefix_cons_append](ArgDom-3.md#t-prefix_cons_append) を適用すると

```math
A_1' \mathbin{+\!\!+} (u+(e-d_0),\ w) :: (B^{-d_0} \mathbin{+\!\!+} A_2')
 \ \sqsubseteq\ A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)
```

である。[T.shiftr0_prefix](ArgDom-3.md#t-shiftr0_prefix) を $`e-d_0`$ について適用すると、この前部分列関係は
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

を得る。(h2) と $`(\dagger)`$ から $`\forall x \in B,\ d_0 \le u + e \lt x_1`$ であるから、
[T.shiftr0_shiftl0](ArgDom-2.md#t-shiftr0_shiftl0) より $`(B^{-d_0})^{+d_0} = B`$ である。
[T.sle_shiftr0](ArgDom.md#t-sle_shiftr0) を $`d_0`$ について適用し、
[T.shiftr0_add](ArgDom-3.md#t-shiftr0_add) と $`d_0 + (e-d_0) = e`$（$`(\ddagger)`$ による）を使うと

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

を得る。これが求める結論である。

**(b) $`\lvert X\rvert = \lvert G\rvert + \lvert D\rvert`$ のとき。**
(S) より

```math
\text{(Nm)}\qquad G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)
  = \bigl(G \mathbin{+\!\!+} D^{-d_0}\bigr) \mathbin{+\!\!+} (u+e-d_0,\ w) ::
      \bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
```

であり、[T.copies_succ_back](Cofinality-3.md#t-copies_succ_back) より

```math
G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1)
  = \bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr) \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}
```

である。これらと $`(\ast)`$ から

```math
\text{(key)}\qquad
\bigl(X \mathbin{+\!\!+} ((u,w))\bigr) \mathbin{+\!\!+}
  \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))\bigr)
= \bigl(G \mathbin{+\!\!+} D^{-d_0}\bigr) \mathbin{+\!\!+}
  \Bigl((u+e-d_0,\ w) :: \bigl(\Sigma \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}\bigr)\Bigr)
```

を得る。ここで
$`\Sigma := B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})`$ と略記した。
場合 (b) の条件より

```math
\lvert G \mathbin{+\!\!+} D^{-d_0}\rvert = \lvert G\rvert + \lvert D\rvert = \lvert X\rvert
 \le \lvert X \mathbin{+\!\!+} ((u,w))\rvert
```

であるから、[T.split_append_left](ArgDom-3.md#t-split_append_left) を (key) に適用して $`K`$ を得る。

```math
X \mathbin{+\!\!+} ((u,w)) = \bigl(G \mathbin{+\!\!+} D^{-d_0}\bigr) \mathbin{+\!\!+} K,
\qquad
(u+e-d_0,\ w) :: \bigl(\Sigma \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}\bigr)
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
\text{(RW)}\qquad \Sigma \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}
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

を得る。(h2) と $`(\dagger)`$ から $`\forall x \in B,\ d_0 \le x_1`$ であり、$`e = d_0`$ であるから
[T.shiftr0_shiftl0](ArgDom-2.md#t-shiftr0_shiftl0) より $`(B^{-d_0})^{+e} = B`$ である。
[T.shiftr0_prefix](ArgDom-3.md#t-shiftr0_prefix) を $`e`$ について適用すると

```math
B \ \sqsubseteq\ \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

となり、[T.sle_of_prefix](ArgDom-3.md#t-sle_of_prefix) から結論を得る。

**(c) $`\lvert G\rvert + \lvert D\rvert \lt \lvert X\rvert`$ のとき。**
この場合は起こらないことを示す。$`1 \le m`$ より $`m = m' + 1`$ と書ける。

**(c-1) $`(u,w)`$ は $`R`$ の内部にある。**
(C1) を左右入れ替えた
$`(X \mathbin{+\!\!+} ((u,w))) \mathbin{+\!\!+} C = G \mathbin{+\!\!+} \mathrm{blk}`$ に、
$`\lvert G\rvert \le \lvert X\rvert \lt \lvert X \mathbin{+\!\!+} ((u,w))\rvert`$ のもとで
[T.split_append_left](ArgDom-3.md#t-split_append_left) を適用して $`K`$ を得る。

```math
X \mathbin{+\!\!+} ((u,w)) = G \mathbin{+\!\!+} K, \qquad \mathrm{blk} = K \mathbin{+\!\!+} C .
```

$`\lvert K\rvert = \lvert X\rvert + 1 - \lvert G\rvert`$ であり、場合 (c) の条件から
$`\lvert G\rvert \lt \lvert X\rvert`$ なので $`\lvert K\rvert \ge 2 \gt 0`$、すなわち
$`K = k_0 :: K_1`$ と書ける。$`\mathrm{blk} = (v_0,w_0) :: R`$ の尾を比べて $`R = K_1 \mathbin{+\!\!+} C`$ を得る。
第 1 式は $`X \mathbin{+\!\!+} ((u,w)) = (G \mathbin{+\!\!+} (k_0)) \mathbin{+\!\!+} K_1`$ と書き直せ、
$`\lvert G \mathbin{+\!\!+} (k_0)\rvert = \lvert G\rvert + 1 \le \lvert X\rvert`$ であるから、
ふたたび [T.split_append_left](ArgDom-3.md#t-split_append_left) を適用して $`T`$ を得る。

```math
X = \bigl(G \mathbin{+\!\!+} (k_0)\bigr) \mathbin{+\!\!+} T, \qquad K_1 = T \mathbin{+\!\!+} ((u,w)) .
```

したがって

```math
\text{(Rdec)}\qquad R = T \mathbin{+\!\!+} (u,w) :: C
```

である。$`(u,w) \in R`$ であるから (hRgt) より $`v_0 \lt u`$ である。

**(c-2) コピー $`1`$ の先頭から $`u \lt v_0 + d_0`$ と $`w \le w_0`$ を得る。**
[T.copies_succ_cons](Cnf-3.md#t-copies_succ_cons) と
[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons) より

```math
\text{(SC)}\qquad \mathrm{copies}_{d_0}(\mathrm{blk}, m'+1)^{+d_0}
 = (v_0+d_0,\ w_0) :: \Bigl(R \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m')^{+d_0}\Bigr)^{+d_0}
```

である。(D2) の左辺はこれであるから、$`D`$ で場合分けする。

**$`D = ()`$ のとき。** (D2) と (SC) の先頭を比べて
$`(v_0+d_0,\ w_0) = (u+e,\ w)`$、すなわち $`v_0 + d_0 = u + e`$ かつ $`w_0 = w`$ である。
(he) の $`0 \lt e`$ より $`u \lt u + e = v_0 + d_0`$ であり、$`w \le w_0`$ も成り立つ。

**$`D = d_1 :: D'`$ のとき。** (D2) と (SC) の先頭を比べて $`d_1 = (v_0+d_0,\ w_0)`$、
残りを比べて

```math
\text{(rest)}\qquad
\Bigl(R \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m')^{+d_0}\Bigr)^{+d_0}
 = D' \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

を得る。(D1) より $`A_1 = C \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: D'`$ である。
$`(v_0+d_0,\ w_0) \in A_1`$ に (h1) を適用して $`u \lt v_0 + d_0`$ を得る。
これと (c-1) の $`v_0 \lt u`$ から $`0 \lt d_0`$ である。
(hRgt) と $`0 \lt d_0`$ と $`1 \le m'+1`$ に
[T.copies_tl_gt](Cnf-3.md#t-copies_tl_gt) を適用すると

```math
\forall y \in R \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m')^{+d_0},\ v_0 \lt y_1
```

であり、[T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) より、この列を $`d_0`$ だけシフトした列
（すなわち (rest) の左辺）の要素 $`y`$ はすべて $`v_0 + d_0 \lt y_1`$ をみたす。
(rest) の右辺には $`(u+e,w)`$ と $`D'`$ の全要素が現れるから

```math
v_0 + d_0 \lt u + e, \qquad \forall y \in D',\ v_0 + d_0 \lt y_1
```

である。よって (h6) を $`C`$、$`D'`$、$`(v_0+d_0,\ w_0)`$ に適用でき
（分解は $`A_1 = C \mathbin{+\!\!+} (v_0+d_0,w_0) :: D'`$）、$`w \le w_0`$ を得る。

いずれの場合も $`u \lt v_0 + d_0`$ かつ $`w \le w_0`$ である。
(c-1) の $`v_0 \lt u`$ と合わせて $`0 \lt d_0`$ である。

**(c-3) 極小性条件との矛盾。**
(hdisj) で場合分けする。第 1 選言は $`d_0 = 0`$ を含み、(c-2) の $`0 \lt d_0`$ に反する。
第 2 選言のとき、$`\ell_1 = v_0 + d_0`$ と $`\ell_2 = w_0 + 1`$ より
$`\ell = (v_0+d_0,\ w_0+1)`$ である。(hMeq) より
$`\lvert M\rvert - 1 = \lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert`$ であるから、第 2 選言の第 4 連言子は

```math
\lvert G\rvert \to^{(G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} ((v_0+d_0,\,w_0+1))}_1
  \lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert
```

と書ける。これに [T.spineOK_of_nextrel1_strict](ArgDom-3.md#t-spineOK_of_nextrel1_strict) を適用すると
$`\mathrm{SpineOK}(R,\ v_0+d_0,\ w_0+1)`$ を得る。これを (Rdec) の分解
$`R = T \mathbin{+\!\!+} (u,w) :: C`$、$`u \lt v_0+d_0`$（(c-2)）、および
$`\forall y \in C,\ u \lt y_1`$（(D1) より $`C`$ の要素は $`A_1`$ の要素であり (h1) による）に
適用して $`w_0 + 1 \le w`$ を得る。これは (c-2) の $`w \le w_0`$ に反する。

したがって場合 (c) は起こらない。∎
