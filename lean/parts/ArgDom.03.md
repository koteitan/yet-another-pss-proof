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
