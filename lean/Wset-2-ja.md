[← README](README-ja.md) | [English](Wset-2.md) | [Japanese](Wset-2-ja.md) | Wset [1](Wset-ja.md) **2** [3](Wset-3-ja.md) [4](Wset-4-ja.md)

<a id="t-hasParent_shift"></a>
## 定理: 親の存在は行 0 の平行移動で不変 (T.hasParent_shift)

### 定理

$`b \lt \lvert S\rvert`$ ならば
$`\mathrm{hasParent}(S^{+d}, i, b) \iff \mathrm{hasParent}(S, i, b)`$
（$`\mathrm{hasParent}`$ [D.hasParent](Pss-ja.md#d-hasParent)、$`S^{+d}`$ [D.shiftr0](Cnf-2-ja.md#d-shiftr0)）。

### 証明

$`\mathrm{hasParent}`$ の定義（D.hasParent）より、両辺はそれぞれ
「$`j_0 \to^{S^{+d}}_i b`$（[D.nextR](Pss-ja.md#d-nextR)）をみたす $`j_0`$ が存在し一意である」
「$`j_0 \to^{S}_i b`$ をみたす $`j_0`$ が存在し一意である」である。

**（左から右）** $`j_0`$ を取り、$`j_0 \to^{S^{+d}}_i b`$ かつ
「$`y \to^{S^{+d}}_i b`$ なる任意の $`y`$ について $`y = j_0`$」とする。
[T.nextR_shift_iff](Wset-ja.md#t-nextR_shift_iff) より $`j_0 \to^{S}_i b`$ である。
また $`y \to^{S}_i b`$ なる $`y`$ を取ると、ふたたび
[T.nextR_shift_iff](Wset-ja.md#t-nextR_shift_iff) より $`y \to^{S^{+d}}_i b`$ であるから
$`y = j_0`$ である。よって $`S`$ の側でも存在と一意性が成り立つ。

**（右から左）** $`j_0`$ を取り、$`j_0 \to^{S}_i b`$ かつ
「$`y \to^{S}_i b`$ なる任意の $`y`$ について $`y = j_0`$」とする。
[T.nextR_shift_iff](Wset-ja.md#t-nextR_shift_iff) より $`j_0 \to^{S^{+d}}_i b`$ である。
また $`y \to^{S^{+d}}_i b`$ なる $`y`$ を取ると、ふたたび
[T.nextR_shift_iff](Wset-ja.md#t-nextR_shift_iff) より $`y \to^{S}_i b`$ であるから
$`y = j_0`$ である。よって $`S^{+d}`$ の側でも存在と一意性が成り立つ。∎

<a id="t-parent_shift"></a>
## 定理: 親は行 0 の平行移動で変わらない (T.parent_shift)

### 定理

$`b \lt \lvert S\rvert`$ ならば
$`\mathrm{par}^{S^{+d}}_i(b) = \mathrm{par}^{S}_i(b)`$（[D.parent](Pss-ja.md#d-parent)）。

### 証明

$`\mathrm{par}`$ の定義（D.parent）より、両辺はそれぞれ述語

```math
\varphi(j_0) :\equiv \bigl(j_0 \to^{S^{+d}}_i b\bigr),
\qquad
\psi(j_0) :\equiv \bigl(j_0 \to^{S}_i b\bigr)
```

に $`\varepsilon`$ を適用した値である。$`b \lt \lvert S\rvert`$ のもとで
[T.nextR_shift_iff](Wset-ja.md#t-nextR_shift_iff) はすべての $`j_0`$ について
$`\varphi(j_0) \iff \psi(j_0)`$ を与えるから、命題の外延性により各 $`j_0`$ で
$`\varphi(j_0)`$ と $`\psi(j_0)`$ は同一の命題であり、したがって $`\varphi = \psi`$ である。
$`\varepsilon`$ の値は述語のみで決まるから両辺は等しい。∎

<a id="t-oper_shift"></a>
## 定理: 展開は行 0 の平行移動と可換 (T.oper_shift)

### 定理

任意の $`M \in \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）、$`d, n \in \mathbb{N}`$ に対し

```math
\bigl(M^{+d}\bigr)[n] = \bigl(M[n]\bigr)^{+d} .
```

（$`M[n]`$ [D.oper](Pss-ja.md#d-oper)）

### 証明

$`\lvert M^{+d}\rvert = \lvert M\rvert`$ である（平行移動は各要素を 1 つずつ写すだけである）。
以下 $`j_1 := \lvert M\rvert - 1`$ とおく。$`j_1 = 0`$ か否かで場合分けする。

**(I) $`j_1 = 0`$ のとき。** $`\lvert M^{+d}\rvert - 1 = j_1 = 0`$ でもあるから、
[T.oper_eq_self_of_short](Decrease-ja.md#t-oper_eq_self_of_short) を $`M^{+d}`$ と $`M`$ の
双方に適用して $`(M^{+d})[n] = M^{+d}`$ と $`M[n] = M`$ を得る。よって両辺とも $`M^{+d}`$ である。

**(II) $`j_1 \ne 0`$ のとき。** このとき $`j_1 \lt \lvert M\rvert`$ である。
$`i_1 := \mathrm{idx}_1(M, j_1)`$（[D.idx1](Pss-ja.md#d-idx1)）とおくと
[T.idx1_shift](Column-4-ja.md#t-idx1_shift) より $`\mathrm{idx}_1(M^{+d}, j_1) = i_1`$ である。
$`\mathrm{hasParent}(M, i_1, j_1)`$ が成り立つか否かでさらに分ける。

**(II-a) $`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
まず $`0 \lt M_{0,j_1}`$（[D.entry](Pss-ja.md#d-entry)）である。実際 $`M_{0,j_1} = 0`$ とすると
[T.no_hasParent_of_row0_zero](Column-ja.md#t-no_hasParent_of_row0_zero) により
$`\mathrm{hasParent}(M, i_1, j_1)`$ から矛盾が出る。したがって
$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ である。
[T.entry_shift](Column-4-ja.md#t-entry_shift) より
$`(M^{+d})_{0,j_1} = M_{0,j_1} + d`$、$`(M^{+d})_{1,j_1} = M_{1,j_1}`$ であるから、
$`(M^{+d})_{0,j_1} \gt 0`$ で $`\neg\bigl((M^{+d})_{0,j_1} = 0 \wedge (M^{+d})_{1,j_1} = 0\bigr)`$ である。
また [T.hasParent_shift](#t-hasParent_shift) より $`\mathrm{hasParent}(M^{+d}, i_1, j_1)`$ である。
よって $`M`$ と $`M^{+d}`$ の双方で $`M[n]`$ の定義（D.oper）の分岐 (d) が選ばれ、
[T.oper_bad_unfold](Decrease-ja.md#t-oper_bad_unfold) が適用できる。

[T.parent_shift](#t-parent_shift) より
$`j_0 := \mathrm{par}^{M}_{i_1}(j_1) = \mathrm{par}^{M^{+d}}_{i_1}(j_1)`$ であり、
[T.parent_nextR](Decrease-ja.md#t-parent_nextR) と
[T.nextR_index_lt](Decrease-ja.md#t-nextR_index_lt) より $`j_0 \lt j_1`$、とくに
$`j_0 \lt \lvert M\rvert`$ である。したがってふたたび
[T.entry_shift](Column-4-ja.md#t-entry_shift) より $`(M^{+d})_{0,j_0} = M_{0,j_0} + d`$ であり、
$`d_0`$ の値は両者で一致する。すなわち $`0 \lt i_1`$ のとき

```math
(M^{+d})_{0,j_1} - (M^{+d})_{0,j_0} = (M_{0,j_1} + d) - (M_{0,j_0} + d) = M_{0,j_1} - M_{0,j_0}
```

であり（切り捨て減法でも右辺の $`d`$ は相殺する）、$`i_1 = 0`$ のときは両者とも $`0`$ である。
この共通の値を $`d_0`$ と書く。

[T.oper_bad_unfold](Decrease-ja.md#t-oper_bad_unfold) の与える両辺は

```math
M[n] = (M_0,\dots,M_{j_0-1}) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1},
```
```math
\begin{aligned}
\bigl(M^{+d}\bigr)[n]
  &= \bigl((M^{+d})_0,\dots,(M^{+d})_{j_0-1}\bigr) \mathbin{+\!\!+} B'_0
     \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B'_{n-1}, \qquad \cr
B'_k
  &= \bigl(\,((M^{+d})_{0,j} + k\,d_0,\ (M^{+d})_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
\end{aligned}
```

である。前部分については $`\bigl((M^{+d})_0,\dots,(M^{+d})_{j_0-1}\bigr) = (M_0,\dots,M_{j_0-1})^{+d}`$
である（平行移動は各要素ごとの写像であり、先頭 $`j_0`$ 個を取る操作と交換する）。
各ブロックについては、$`j_0 \le j \lt j_1 \lt \lvert M\rvert`$ の範囲で
[T.entry_shift](Column-4-ja.md#t-entry_shift) が使えて

```math
\bigl((M^{+d})_{0,j} + k\,d_0,\ (M^{+d})_{1,j}\bigr)
  = \bigl(M_{0,j} + d + k\,d_0,\ M_{1,j}\bigr)
  = \bigl((M_{0,j} + k\,d_0) + d,\ M_{1,j}\bigr)
```

であるから $`B'_k = (B_k)^{+d}`$ である。連結と平行移動は交換するから、両辺は等しい。

**(II-b) $`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
[T.hasParent_shift](#t-hasParent_shift) より
$`\neg\,\mathrm{hasParent}(M^{+d}, i_1, j_1)`$ である。
$`M`$ について、$`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ が成り立つなら
[T.oper_eq_pred_of_zero](Decrease-ja.md#t-oper_eq_pred_of_zero) により、成り立たないなら
[T.oper_eq_pred_of_noParent](Decrease-ja.md#t-oper_eq_pred_of_noParent) により、いずれにせよ
$`M[n] = \mathrm{Pred}\,M`$（[D.Pred](Pss-ja.md#d-Pred)）である。同じ 2 つの定理を $`M^{+d}`$ に適用して
$`(M^{+d})[n] = \mathrm{Pred}(M^{+d})`$ を得る。

$`j_1 = \lvert M\rvert - 1 \ne 0`$ より $`2 \le \lvert M\rvert = \lvert M^{+d}\rvert`$ であるから、
$`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合が両者で選ばれ

```math
\mathrm{Pred}\,M = \mathrm{dropLast}\,M,
\qquad
\mathrm{Pred}(M^{+d}) = \mathrm{dropLast}(M^{+d})
```

である。平行移動は各要素ごとの写像であるから末尾 1 要素を落とす操作と交換し、
$`\mathrm{dropLast}(M^{+d}) = (\mathrm{dropLast}\,M)^{+d}`$ である。よって両辺は等しい。∎

<a id="t-domT_shift"></a>
## 定理: $`\mathrm{domT}`$ は行 0 の平行移動で不変 (T.domT_shift)

### 定理

$`\mathrm{domT}(M^{+d}, m) \iff \mathrm{domT}(M, m)`$（[D.domT](Wset-ja.md#d-domT)）。

### 証明

$`M`$ の構成子で場合分けする。

**(a) $`M = ()`$ のとき。** $`()^{+d} = ()`$ である。$`\lvert ()\rvert - 1 = 0`$ であり、
$`M_{i,j}`$ の定義（D.entry）より $`()_{1,0} = 0`$ であるから、
$`\mathrm{domT}`$ の定義（D.domT）の第 1 連言子 $`()_{1,0} = m+1`$ は偽である。
よって両辺とも偽であり、同値である。

**(b) $`M = p :: L`$ のとき。** $`\lvert M^{+d}\rvert = \lvert M\rvert`$ であるから、
両辺で読む添字は同じ $`j_1 := \lvert M\rvert - 1`$ であり、$`j_1 \lt \lvert M\rvert`$ である。
$`\mathrm{domT}`$ の定義（D.domT）の 2 つの連言子をそれぞれ比べる。
第 1 連言子は [T.entry_shift](Column-4-ja.md#t-entry_shift) より
$`(M^{+d})_{1,j_1} = M_{1,j_1}`$ であるから同値であり、
第 2 連言子は [T.hasParent_shift](#t-hasParent_shift) より
$`\mathrm{hasParent}(M^{+d}, 1, j_1) \iff \mathrm{hasParent}(M, 1, j_1)`$ であるから同値である。∎

<a id="t-natDom_shift"></a>
## 定理: $`\mathrm{natDom}`$ は行 0 の平行移動で不変 (T.natDom_shift)

### 定理

$`\mathrm{natDom}(M^{+d}) \iff \mathrm{natDom}(M)`$（[D.natDom](Wset-ja.md#d-natDom)）。

### 証明

$`\mathrm{natDom}`$ の定義（D.natDom）より、左辺は
$`\forall m,\ \neg\,\mathrm{domT}(M^{+d}, m)`$、右辺は $`\forall m,\ \neg\,\mathrm{domT}(M, m)`$ である。

左辺を仮定し $`m`$ を取る。$`\mathrm{domT}(M,m)`$ とすると
[T.domT_shift](#t-domT_shift) より $`\mathrm{domT}(M^{+d}, m)`$ となり左辺に矛盾する。
よって $`\neg\,\mathrm{domT}(M,m)`$ である。

右辺を仮定し $`m`$ を取る。$`\mathrm{domT}(M^{+d},m)`$ とすると
[T.domT_shift](#t-domT_shift) より $`\mathrm{domT}(M, m)`$ となり右辺に矛盾する。
よって $`\neg\,\mathrm{domT}(M^{+d},m)`$ である。∎

<a id="t-graft_shift"></a>
## 定理: 接ぎ木は行 0 の平行移動と可換 (T.graft_shift)

### 定理

$`M \ne ()`$ ならば、任意の $`z \in \mathrm{PairSeq}`$、$`d \in \mathbb{N}`$ に対し

```math
\mathrm{graft}\bigl(M^{+d},\ z\bigr) = \bigl(\mathrm{graft}(M, z)\bigr)^{+d} .
```

（$`\mathrm{graft}`$ [D.graft](Wset-ja.md#d-graft)）

### 証明

$`M \ne ()`$ より $`0 \lt \lvert M\rvert`$、したがって $`j_1 := \lvert M\rvert - 1 \lt \lvert M\rvert`$ である。
$`\lvert M^{+d}\rvert = \lvert M\rvert`$ であるから、$`M^{+d}`$ の末尾の添字も $`j_1`$ である。
$`\mathrm{graft}`$ の定義（D.graft）より

```math
\mathrm{graft}\bigl(M^{+d}, z\bigr)
  = \mathrm{dropLast}\bigl(M^{+d}\bigr) \mathbin{+\!\!+} z^{+(M^{+d})_{0,j_1}} .
```

[T.entry_shift](Column-4-ja.md#t-entry_shift) より $`(M^{+d})_{0,j_1} = M_{0,j_1} + d`$ であり、
平行移動は末尾 1 要素を落とす操作と交換するから
$`\mathrm{dropLast}(M^{+d}) = (\mathrm{dropLast}\,M)^{+d}`$ である。よって

```math
\mathrm{graft}\bigl(M^{+d}, z\bigr)
  = (\mathrm{dropLast}\,M)^{+d} \mathbin{+\!\!+} z^{+(M_{0,j_1} + d)} .
```

一方

```math
\bigl(\mathrm{graft}(M,z)\bigr)^{+d}
  = \bigl(\mathrm{dropLast}\,M \mathbin{+\!\!+} z^{+M_{0,j_1}}\bigr)^{+d}
  = (\mathrm{dropLast}\,M)^{+d} \mathbin{+\!\!+} \bigl(z^{+M_{0,j_1}}\bigr)^{+d}
```

である（平行移動は連結と交換する）。$`z`$ の要素 $`q`$ は右辺の第 2 項では
$`\bigl((q_1 + M_{0,j_1}) + d,\ q_2\bigr)`$ に写り、左辺の第 2 項では
$`\bigl(q_1 + (M_{0,j_1} + d),\ q_2\bigr)`$ に写る。$`\mathbb{N}`$ の加法の結合律により
この 2 つは等しい。よって両辺は等しい。∎

<a id="t-W_shift"></a>
## 定理: 行 0 の平行移動による $`W_u`$ の不変性 (T.W_shift)

### 定理

$`M \in W_u`$（[D.W](Wset-ja.md#d-W)）ならば、任意の $`d \in \mathbb{N}`$ に対し $`M^{+d} \in W_u`$。

### 証明

$`d`$ を固定し

```math
Y := \{\, N \in \mathrm{PairSeq} \mid N^{+d} \in W_u \,\}
```

とおく。[T.A2'](Wset-ja.md#t-A2') により $`W_u \subseteq Y`$ を示すには、
任意の $`N`$ について $`N \in A_u(Y)`$（[D.Aop](Wset-ja.md#d-Aop)）ならば $`N \in Y`$、すなわち
$`N^{+d} \in W_u`$ を示せばよい。
[T.A1_intro](Wset-ja.md#t-A1_intro) によりこれは $`N^{+d} \in A_u(W_u)`$ に帰着する。
$`A_u`$ の定義（D.Aop）の 3 分岐で場合分けする。

**分岐 (1)：$`\lvert N\rvert \le 1 \wedge N_{1,0} = 0`$ のとき。**
$`\lvert N^{+d}\rvert = \lvert N\rvert \le 1`$ である。また $`(N^{+d})_{1,0} = N_{1,0} = 0`$ である。
実際 $`N = ()`$ なら $`N^{+d} = ()`$ で両辺とも $`0`$（D.entry の範囲外の読み）、
$`N = p :: L`$ なら $`N^{+d}`$ の先頭は $`(p_1 + d,\ p_2)`$ でその第 2 成分は $`p_2 = N_{1,0}`$ である。
よって $`N^{+d}`$ は分岐 (1) をみたす。

**分岐 (2)：$`\mathrm{natDom}(N) \wedge \forall n \ge 1,\ N[n] \in Y`$ のとき。**
[T.natDom_shift](#t-natDom_shift) より $`\mathrm{natDom}(N^{+d})`$ である。
$`n \ge 1`$ を取ると [T.oper_shift](#t-oper_shift) より
$`(N^{+d})[n] = (N[n])^{+d}`$ であり、$`N[n] \in Y`$ すなわち $`(N[n])^{+d} \in W_u`$ である。
よって $`N^{+d}`$ は分岐 (2) をみたす。

**分岐 (3)、すなわち $`m \lt u`$、$`\mathrm{domT}(N,m)`$、
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(N,z) \in Y`$
（$`\mathrm{based}`$ [D.based](Wset-ja.md#d-based)）をみたす $`m`$ があるとき。**
[T.domT_shift](#t-domT_shift) より $`\mathrm{domT}(N^{+d}, m)`$ である。
また $`N \ne ()`$ である（$`N = ()`$ なら [T.not_domT_nil](Wset-ja.md#t-not_domT_nil) が
$`\mathrm{domT}(N,m)`$ に矛盾する）。$`z \in W_m`$ が $`\mathrm{based}(z)`$ をみたすとき、
[T.graft_shift](#t-graft_shift) より

```math
\mathrm{graft}\bigl(N^{+d}, z\bigr) = \bigl(\mathrm{graft}(N,z)\bigr)^{+d}
```

であり、$`\mathrm{graft}(N,z) \in Y`$ よりこれは $`W_u`$ の元である。
よって $`N^{+d}`$ は同じ $`m`$ で分岐 (3) をみたす。

以上により $`W_u \subseteq Y`$ であり、$`M \in W_u`$ から $`M^{+d} \in W_u`$ を得る。∎

<a id="t-split_lastMin"></a>
## 定理: 最後の最上位木による分解 (T.split_lastMin)

### 定理

$`M \ne ()`$ ならば、$`A, P \in \mathrm{PairSeq}`$ が存在して

```math
M = A \mathbin{+\!\!+} P,
\qquad P \ne (),
\qquad \mathrm{rsum}(A, P),
\qquad \forall p \in \mathrm{tail}\,P,\ P_{0,0} \lt p_1 .
```

（$`\mathrm{rsum}`$ [D.rsum](Wset-ja.md#d-rsum)）

ここで $`\mathrm{tail}\,P`$ は $`P`$ の先頭 1 要素を落とした列である。

### 証明

列の末尾からの構成に関する帰納法を行う。すなわち、$`\mathrm{PairSeq}`$ の各元は
$`()`$ であるか、ある $`M'`$ と対 $`q`$ によって $`M' \mathbin{+\!\!+} (q)`$ と書けるかのいずれかであり、
後者では $`\lvert M'\rvert \lt \lvert M' \mathbin{+\!\!+} (q)\rvert`$ である。帰納法の述語は

```math
\Phi(M) :\equiv M \ne () \to \exists A, P,\
  \bigl(M = A \mathbin{+\!\!+} P \wedge P \ne () \wedge \mathrm{rsum}(A,P)
    \wedge \forall p \in \mathrm{tail}\,P,\ P_{0,0} \lt p_1\bigr).
```

- **基底段** $`M = ()`$：前件 $`M \ne ()`$ が偽であるから $`\Phi(())`$ が成り立つ。

**帰納段** $`M = M' \mathbin{+\!\!+} (q)`$：帰納法の仮定は $`\Phi(M')`$ である。
$`M'`$ が空か否かで場合分けする。

**(a) $`M' = ()`$ のとき。** $`A := ()`$、$`P := (q)`$ と取る。
$`M = () \mathbin{+\!\!+} (q)`$ であり $`P \ne ()`$ である。
$`P_{0,0} = q_1`$ であり、$`() \mathbin{+\!\!+} (q)`$ の要素は $`q`$ のみで $`q_1 \le q_1`$ が成り立つから
$`\mathrm{rsum}(A,P)`$ である。$`\mathrm{tail}\,(q) = ()`$ であるから最後の条件は要素をもたず成り立つ。

**(b) $`M' \ne ()`$ のとき。** 帰納法の仮定 $`\Phi(M')`$ より
$`M' = A' \mathbin{+\!\!+} P'`$、$`P' \ne ()`$、$`\mathrm{rsum}(A',P')`$、
$`\forall p \in \mathrm{tail}\,P',\ P'_{0,0} \lt p_1`$ をみたす $`A', P'`$ を取る。
$`q_1`$ と $`P'_{0,0}`$ の大小で分ける。

**(b-1) $`q_1 \le P'_{0,0}`$ のとき。** $`A := M'`$、$`P := (q)`$ と取る。
$`M = M' \mathbin{+\!\!+} (q)`$ であり $`P \ne ()`$ である。$`P_{0,0} = q_1`$ である。
$`p \in M' \mathbin{+\!\!+} (q)`$ を取る。$`p \in M' = A' \mathbin{+\!\!+} P'`$ のときは
$`\mathrm{rsum}(A',P')`$ より $`P'_{0,0} \le p_1`$ であり、仮定 $`q_1 \le P'_{0,0}`$ と合わせて
$`q_1 \le p_1`$ である。$`p = q`$ のときは $`q_1 \le q_1`$ である。よって $`\mathrm{rsum}(A,P)`$。
$`\mathrm{tail}\,(q) = ()`$ であるから最後の条件は成り立つ。

**(b-2) $`P'_{0,0} \lt q_1`$ のとき。** $`A := A'`$、$`P := P' \mathbin{+\!\!+} (q)`$ と取る。
連結の結合律より
$`M = (A' \mathbin{+\!\!+} P') \mathbin{+\!\!+} (q) = A' \mathbin{+\!\!+} (P' \mathbin{+\!\!+} (q))`$ であり、
$`P \ne ()`$ である。$`P' \ne ()`$ であるから $`P' = p_0 :: P''`$ と書け、
$`P' \mathbin{+\!\!+} (q) = p_0 :: (P'' \mathbin{+\!\!+} (q))`$ の先頭も $`p_0`$ である。よって

```math
P_{0,0} = (p_0)_1 = P'_{0,0} .
```

$`\mathrm{rsum}(A,P)`$ を示す。$`p \in A' \mathbin{+\!\!+} (P' \mathbin{+\!\!+} (q))`$ を取る。
$`p \in A'`$ のときは $`\mathrm{rsum}(A',P')`$ より $`P'_{0,0} \le p_1`$。
$`p \in P'`$ のときも $`\mathrm{rsum}(A',P')`$ より $`P'_{0,0} \le p_1`$。
$`p = q`$ のときは仮定 $`P'_{0,0} \lt q_1`$ より $`P'_{0,0} \le q_1`$。
いずれの場合も $`P_{0,0} = P'_{0,0} \le p_1`$ である。

最後の条件を示す。$`\mathrm{tail}\,P = P'' \mathbin{+\!\!+} (q)`$ である。
$`p \in P''`$ のときは $`P'' = \mathrm{tail}\,P'`$ であるから帰納法の仮定で得た条件より
$`P'_{0,0} \lt p_1`$ である。$`p = q`$ のときは仮定そのもの $`P'_{0,0} \lt q_1`$ である。
$`P_{0,0} = P'_{0,0}`$ であるから、いずれの場合も $`P_{0,0} \lt p_1`$ である。∎

<a id="t-map_sub_add"></a>
## 定理: 下方向と上方向の平行移動の合成 (T.map_sub_add)

### 定理

$`c \in \mathbb{N}`$、$`X \in \mathrm{PairSeq}`$ とし、$`\forall p \in X,\ c \le p_1`$ とする。このとき

```math
\bigl(X^{-c}\bigr)^{+c} = X .
```

ここで $`X^{-c}`$（[D.shiftl0](ArgDom-2-ja.md#d-shiftl0)）は $`X`$ の各対の第 1 成分から一様に
$`c`$ を切り捨て減法で引いた列である。

### 証明

$`X^{-c}`$ も $`(X^{-c})^{+c}`$ も $`X`$ の各要素を 1 つずつ写して得られる列であるから、
3 つの列の長さは等しい。$`X`$ の要素 $`q`$ が $`(X^{-c})^{+c}`$ の対応する位置で
何になるかを見ると、

```math
q \longmapsto (q_1 - c,\ q_2) \longmapsto \bigl((q_1 - c) + c,\ q_2\bigr)
```

である。仮定より $`c \le q_1`$ であるから、切り捨て減法について $`(q_1 - c) + c = q_1`$ であり、
この対は $`(q_1, q_2) = q`$ に等しい。よって対応する位置の要素がすべて一致し、両辺は等しい。∎

<a id="t-rsum_decomp"></a>
## 定理: 最上位分解の平行移動表示 (T.rsum_decomp)

### 定理

$`\mathrm{rsum}(A,P)`$ ならば、$`c := P_{0,0}`$ として

```math
\bigl(A^{-c} \mathbin{+\!\!+} P^{-c}\bigr)^{+c} = A \mathbin{+\!\!+} P .
```

### 証明

平行移動は各要素ごとの写像であるから連結と交換し、

```math
\bigl(A^{-c} \mathbin{+\!\!+} P^{-c}\bigr)^{+c} = \bigl(A^{-c}\bigr)^{+c} \mathbin{+\!\!+} \bigl(P^{-c}\bigr)^{+c}
```

である。$`\mathrm{rsum}(A,P)`$ の定義（D.rsum）は
$`\forall p \in A \mathbin{+\!\!+} P,\ c \le p_1`$ であるから、とくに
$`\forall p \in A,\ c \le p_1`$ と $`\forall p \in P,\ c \le p_1`$ が成り立つ。
[T.map_sub_add](#t-map_sub_add) を $`X := A`$ と $`X := P`$ に適用して
$`(A^{-c})^{+c} = A`$、$`(P^{-c})^{+c} = P`$ を得る。∎

<a id="t-entry_sub_zero"></a>
## 定理: 下げた列の先頭の行 0 の値は 0 (T.entry_sub_zero)

### 定理

$`P \ne ()`$ ならば、$`c := P_{0,0}`$ として $`\bigl(P^{-c}\bigr)_{0,0} = 0`$。

### 証明

$`P \ne ()`$ より $`P = p_0 :: P'`$ と書ける。$`M_{i,j}`$ の定義（D.entry）より
$`c = P_{0,0} = (p_0)_1`$ である。$`P^{-c}`$ の先頭は
$`\bigl((p_0)_1 - c,\ (p_0)_2\bigr) = \bigl((p_0)_1 - (p_0)_1,\ (p_0)_2\bigr) = \bigl(0,\ (p_0)_2\bigr)`$
であるから、ふたたび D.entry より $`(P^{-c})_{0,0} = 0`$ である。∎

<a id="t-oper_append_gen"></a>
## 定理: 最上位分解に沿う展開の前置可換性 (T.oper_append_gen)

### 定理

$`2 \le \lvert P\rvert`$ かつ $`\mathrm{rsum}(A,P)`$ ならば、任意の $`n`$ に対し

```math
(A \mathbin{+\!\!+} P)[n] = A \mathbin{+\!\!+} P[n] .
```

### 証明

$`c := P_{0,0}`$、$`\hat A := A^{-c}`$、$`\hat P := P^{-c}`$ とおく。
$`2 \le \lvert P\rvert`$ より $`P \ne ()`$ であり、次の 5 つが成り立つ。

1. $`(\hat P)_{0,0} = 0`$。[T.entry_sub_zero](#t-entry_sub_zero) による。
2. $`2 \le \lvert \hat P\rvert`$。平行移動は長さを変えないから $`\lvert \hat P\rvert = \lvert P\rvert`$ である。
3. $`(\hat A \mathbin{+\!\!+} \hat P)^{+c} = A \mathbin{+\!\!+} P`$。[T.rsum_decomp](#t-rsum_decomp) による。
4. $`(\hat P)^{+c} = P`$。$`\mathrm{rsum}(A,P)`$ より $`\forall p \in P,\ c \le p_1`$ であるから
   [T.map_sub_add](#t-map_sub_add) による。
5. $`(\hat A)^{+c} = A`$。$`\mathrm{rsum}(A,P)`$ より $`\forall p \in A,\ c \le p_1`$ であるから
   [T.map_sub_add](#t-map_sub_add) による。

これらを用いて計算する。

```math
\begin{aligned}
(A \mathbin{+\!\!+} P)[n]
  &= \Bigl(\bigl(\hat A \mathbin{+\!\!+} \hat P\bigr)^{+c}\Bigr)[n] && (3) \cr
  &= \Bigl(\bigl(\hat A \mathbin{+\!\!+} \hat P\bigr)[n]\Bigr)^{+c} && (6) \cr
  &= \bigl(\hat A \mathbin{+\!\!+} \hat P[n]\bigr)^{+c} && (7) \cr
  &= (\hat A)^{+c} \mathbin{+\!\!+} \bigl(\hat P[n]\bigr)^{+c} && (8) \cr
  &= A \mathbin{+\!\!+} \bigl(\hat P[n]\bigr)^{+c} && (5) \cr
  &= A \mathbin{+\!\!+} \bigl((\hat P)^{+c}\bigr)[n] && (6) \cr
  &= A \mathbin{+\!\!+} P[n] . && (4)
\end{aligned}
```

ここで (6) は [T.oper_shift](#t-oper_shift)（第 2 行では左から右へ、第 6 行では右から左へ）、
(7) は [T.oper_append_right](Column-2-ja.md#t-oper_append_right) であり、その 2 つの仮定
$`2 \le \lvert \hat P\rvert`$ と $`(\hat P)_{0,0} = 0`$ は (2) と (1) である。
(8) は平行移動が連結と交換することによる。∎

<a id="t-graft_append"></a>
## 定理: 接ぎ木の前置可換性 (T.graft_append)

### 定理

$`P \ne ()`$ ならば、任意の $`A, z \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{graft}(A \mathbin{+\!\!+} P,\ z) = A \mathbin{+\!\!+} \mathrm{graft}(P, z) .
```

### 証明

$`P \ne ()`$ より $`0 \lt \lvert P\rvert`$ であるから

```math
\lvert A \mathbin{+\!\!+} P\rvert - 1 = \lvert A\rvert + \lvert P\rvert - 1 = \lvert A\rvert + (\lvert P\rvert - 1)
```

である。[T.entry_append_right](Column-ja.md#t-entry_append_right) を
$`i := 0`$、$`j := \lvert P\rvert - 1`$ に適用して

```math
(A \mathbin{+\!\!+} P)_{0,\ \lvert A \mathbin{+\!\!+} P\rvert - 1} = P_{0,\ \lvert P\rvert - 1}
```

を得る。また $`P \ne ()`$ より
$`\mathrm{dropLast}(A \mathbin{+\!\!+} P) = A \mathbin{+\!\!+} \mathrm{dropLast}\,P`$ である。
よって $`\mathrm{graft}`$ の定義（D.graft）より

```math
\begin{aligned}
\mathrm{graft}(A \mathbin{+\!\!+} P, z)
  &= \bigl(A \mathbin{+\!\!+} \mathrm{dropLast}\,P\bigr) \mathbin{+\!\!+} z^{+P_{0,\lvert P\rvert-1}} \cr
  &= A \mathbin{+\!\!+} \bigl(\mathrm{dropLast}\,P \mathbin{+\!\!+} z^{+P_{0,\lvert P\rvert-1}}\bigr) \cr
  &= A \mathbin{+\!\!+} \mathrm{graft}(P,z)
\end{aligned}
```

である（中央の等号は連結の結合律による）。∎

<a id="t-hasParent_append_gen"></a>
## 定理: 最上位分解に沿う親の存在の前置不変性 (T.hasParent_append_gen)

### 定理

$`j \lt \lvert P\rvert`$ かつ $`\mathrm{rsum}(A,P)`$ ならば

```math
\mathrm{hasParent}\bigl(A \mathbin{+\!\!+} P,\ i,\ \lvert A\rvert + j\bigr) \iff \mathrm{hasParent}(P, i, j).
```

### 証明

$`j \lt \lvert P\rvert`$ より $`P \ne ()`$ である。
$`c := P_{0,0}`$、$`\hat A := A^{-c}`$、$`\hat P := P^{-c}`$ とおく。
平行移動は長さを変えないから $`\lvert \hat A\rvert = \lvert A\rvert`$、$`\lvert \hat P\rvert = \lvert P\rvert`$ である。
[T.entry_sub_zero](#t-entry_sub_zero) より $`(\hat P)_{0,0} = 0`$、
[T.rsum_decomp](#t-rsum_decomp) より $`(\hat A \mathbin{+\!\!+} \hat P)^{+c} = A \mathbin{+\!\!+} P`$、
[T.map_sub_add](#t-map_sub_add) より $`(\hat P)^{+c} = P`$ である。3 段に分ける。

**第 1 段。** 次を示す。

```math
\mathrm{hasParent}(A \mathbin{+\!\!+} P,\ i,\ \lvert A\rvert + j)
\iff \mathrm{hasParent}(\hat A \mathbin{+\!\!+} \hat P,\ i,\ \lvert \hat A\rvert + j).
```

$`\lvert \hat A \mathbin{+\!\!+} \hat P\rvert = \lvert A\rvert + \lvert P\rvert`$ であり
$`j \lt \lvert P\rvert`$ であるから $`\lvert A\rvert + j \lt \lvert \hat A \mathbin{+\!\!+} \hat P\rvert`$ である。
$`(\hat A \mathbin{+\!\!+} \hat P)^{+c} = A \mathbin{+\!\!+} P`$ であるから、
[T.hasParent_shift](#t-hasParent_shift) を $`S := \hat A \mathbin{+\!\!+} \hat P`$、$`d := c`$、
$`b := \lvert A\rvert + j`$ に適用すればよい（$`\lvert \hat A\rvert = \lvert A\rvert`$）。

**第 2 段。** 次を示す。

```math
\mathrm{hasParent}(\hat A \mathbin{+\!\!+} \hat P,\ i,\ \lvert \hat A\rvert + j)
\iff \mathrm{hasParent}(\hat P,\ i,\ j).
```

$`(\hat P)_{0,j}`$ が $`0`$ か否かで場合分けする。

**$`(\hat P)_{0,j} = 0`$ のとき。** [T.entry_append_right](Column-ja.md#t-entry_append_right) より
$`(\hat A \mathbin{+\!\!+} \hat P)_{0,\lvert \hat A\rvert + j} = (\hat P)_{0,j} = 0`$ である。
[T.no_hasParent_of_row0_zero](Column-ja.md#t-no_hasParent_of_row0_zero) を
$`\hat A \mathbin{+\!\!+} \hat P`$ に適用すると左辺は偽であり、同じ定理を $`\hat P`$ に適用すると
右辺も偽である。よって同値である。

**$`(\hat P)_{0,j} \ne 0`$ のとき。** 上と同じ等式より
$`0 \lt (\hat A \mathbin{+\!\!+} \hat P)_{0,\lvert \hat A\rvert + j}`$ である。
$`(\hat P)_{0,0} = 0`$ と合わせて
[T.hasParent_append_right](Column-ja.md#t-hasParent_append_right) が適用でき、同値を得る。

**第 3 段：$`\mathrm{hasParent}(\hat P, i, j) \iff \mathrm{hasParent}(P, i, j)`$。**
$`j \lt \lvert P\rvert = \lvert \hat P\rvert`$ であり $`(\hat P)^{+c} = P`$ であるから、
[T.hasParent_shift](#t-hasParent_shift) を $`S := \hat P`$、$`d := c`$、$`b := j`$ に適用すればよい。

3 段をつなげば結論を得る。∎

<a id="t-domT_append"></a>
## 定理: $`\mathrm{domT}`$ の前置不変性 (T.domT_append)

### 定理

$`P \ne ()`$ かつ $`\mathrm{rsum}(A,P)`$ ならば

```math
\mathrm{domT}(A \mathbin{+\!\!+} P,\ m) \iff \mathrm{domT}(P, m).
```

### 証明

$`P \ne ()`$ より $`0 \lt \lvert P\rvert`$ であるから

```math
\lvert A \mathbin{+\!\!+} P\rvert - 1 = \lvert A\rvert + (\lvert P\rvert - 1)
```

である。$`\mathrm{domT}`$ の定義（D.domT）の 2 つの連言子をそれぞれ比べる。

第 1 連言子について、[T.entry_append_right](Column-ja.md#t-entry_append_right) を
$`i := 1`$、$`j := \lvert P\rvert - 1`$ に適用して

```math
(A \mathbin{+\!\!+} P)_{1,\ \lvert A \mathbin{+\!\!+} P\rvert - 1} = P_{1,\ \lvert P\rvert - 1}
```

を得るから、$`(A \mathbin{+\!\!+} P)_{1,\lvert A \mathbin{+\!\!+} P\rvert-1} = m+1`$ と
$`P_{1,\lvert P\rvert-1} = m+1`$ は同値である。

第 2 連言子について、$`\lvert P\rvert - 1 \lt \lvert P\rvert`$ であるから
[T.hasParent_append_gen](#t-hasParent_append_gen) を $`i := 1`$、$`j := \lvert P\rvert - 1`$ に
適用して

```math
\mathrm{hasParent}\bigl(A \mathbin{+\!\!+} P,\ 1,\ \lvert A \mathbin{+\!\!+} P\rvert - 1\bigr)
  \iff \mathrm{hasParent}\bigl(P,\ 1,\ \lvert P\rvert - 1\bigr)
```

を得るから、その否定どうしも同値である。∎

<a id="t-natDom_append"></a>
## 定理: $`\mathrm{natDom}`$ の前置不変性 (T.natDom_append)

### 定理

$`P \ne ()`$ かつ $`\mathrm{rsum}(A,P)`$ ならば
$`\mathrm{natDom}(A \mathbin{+\!\!+} P) \iff \mathrm{natDom}(P)`$。

### 証明

$`\mathrm{natDom}`$ の定義（D.natDom）より、左辺は
$`\forall m,\ \neg\,\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$、右辺は $`\forall m,\ \neg\,\mathrm{domT}(P,m)`$ である。

左辺を仮定し $`m`$ を取る。$`\mathrm{domT}(P,m)`$ とすると
[T.domT_append](#t-domT_append) より $`\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$ となり左辺に矛盾する。
よって $`\neg\,\mathrm{domT}(P,m)`$ である。

右辺を仮定し $`m`$ を取る。$`\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$ とすると
[T.domT_append](#t-domT_append) より $`\mathrm{domT}(P, m)`$ となり右辺に矛盾する。
よって $`\neg\,\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$ である。∎

<a id="d-XA"></a>
## 定義: 前置による剰余集合 (D.XA)

$`A \in \mathrm{PairSeq}`$、$`X \subseteq \mathrm{PairSeq}`$ に対し

```math
X^{(A)} := \{\, B \in \mathrm{PairSeq} \mid \mathrm{rsum}(A,B) \to A \mathbin{+\!\!+} B \in X \,\} .
```

<a id="t-entry_zero_headD"></a>
## 定理: 先頭の行 0 の値 (T.entry_zero_headD)

### 定理

任意の $`X \in \mathrm{PairSeq}`$ に対し $`X_{0,0} = (\mathrm{hd}\,X)_1`$。
ここで $`\mathrm{hd}\,X`$ は $`X`$ の先頭要素であり、$`X = ()`$ のときは $`(0,0)`$ とする。

### 証明

$`X`$ の構成子で場合分けする。

- $`X = ()`$ のとき。$`M_{i,j}`$ の定義（D.entry）より $`()_{0,0} = 0`$ である
  （添字 $`0`$ は範囲外なので $`(0,0)`$ を読む）。また $`\mathrm{hd}\,() = (0,0)`$ でその第 1 成分は $`0`$ である。

- $`X = p :: X'`$ のとき。D.entry より $`X_{0,0} = p_1`$ である。また $`\mathrm{hd}\,X = p`$ で
  その第 1 成分は $`p_1`$ である。∎

<a id="t-oper_head_eq"></a>
## 定理: 展開は先頭の行 0 の値を変えない (T.oper_head_eq)

### 定理

$`1 \le n`$ ならば $`\bigl(N[n]\bigr)_{0,0} = N_{0,0}`$。

### 証明

$`1 \lt \lvert N\rvert`$ か否かで場合分けする。

- $`1 \lt \lvert N\rvert`$ のとき。[T.entry_zero_headD](#t-entry_zero_headD) を
  $`X := N[n]`$ と $`X := N`$ に適用すると、示すべきことは
  $`\bigl(\mathrm{hd}(N[n])\bigr)_1 = (\mathrm{hd}\,N)_1`$ である。
  [T.oper_headD](Column-2-ja.md#t-oper_headD) が $`1 \lt \lvert N\rvert`$ と $`1 \le n`$ のもとで
  $`\mathrm{hd}(N[n]) = \mathrm{hd}\,N`$ を与えるから、第 1 成分どうしも等しい。

- $`\neg(1 \lt \lvert N\rvert)`$ のとき。$`\lvert N\rvert \le 1`$ すなわち $`\lvert N\rvert - 1 = 0`$
  であるから、[T.oper_eq_self_of_short](Decrease-ja.md#t-oper_eq_self_of_short) より $`N[n] = N`$ であり、
  両辺は同一である。∎

<a id="t-entry_pair_mem"></a>
## 定理: 列の第 $`j`$ 成分は列の要素 (T.entry_pair_mem)

### 定理

$`j \lt \lvert N\rvert`$ ならば $`(N_{0,j},\ N_{1,j}) \in N`$。

### 証明

$`M_{i,j}`$ の定義（D.entry）より $`N_{0,j} = \pi_1\bigl(N\langle j\rangle\bigr)`$、
$`N_{1,j} = \pi_2\bigl(N\langle j\rangle\bigr)`$ であるから

```math
(N_{0,j},\ N_{1,j}) = N\langle j\rangle
```

である。仮定 $`j \lt \lvert N\rvert`$ より D.entry の $`N\langle j\rangle`$ は第 1 の場合になり
$`N\langle j\rangle = N_j`$、すなわち $`N`$ の第 $`j`$ 要素である。列の第 $`j`$ 要素は
$`j \lt \lvert N\rvert`$ のとき列の要素である。∎

<a id="t-oper_mem_ge"></a>
## 定理: 展開は行 0 の値の下界を保つ (T.oper_mem_ge)

### 定理

$`\forall p \in N,\ c \le p_1`$ ならば、任意の $`n`$ に対し $`\forall p \in N[n],\ c \le p_1`$。

### 証明

$`j_1 := \lvert N\rvert - 1`$ とおく。$`j_1 = 0`$ か否かで場合分けする。

**(I) $`j_1 = 0`$ のとき。** [T.oper_eq_self_of_short](Decrease-ja.md#t-oper_eq_self_of_short) より
$`N[n] = N`$ であるから、仮定そのものである。

**(II) $`j_1 \ne 0`$ のとき。** $`i_1 := \mathrm{idx}_1(N, j_1)`$ とおき、
$`\mathrm{hasParent}(N, i_1, j_1)`$ が成り立つか否かで分ける。

**(II-a) $`\mathrm{hasParent}(N, i_1, j_1)`$ のとき。**
$`N_{0,j_1} = 0`$ とすると
[T.no_hasParent_of_row0_zero](Column-ja.md#t-no_hasParent_of_row0_zero) により矛盾するから
$`0 \lt N_{0,j_1}`$ であり、とくに $`\neg(N_{0,j_1} = 0 \wedge N_{1,j_1} = 0)`$ である。
よって [T.oper_bad_unfold](Decrease-ja.md#t-oper_bad_unfold) が適用でき、
$`j_0 := \mathrm{par}^N_{i_1}(j_1)`$ として

```math
N[n] = (N_0,\dots,N_{j_0-1}) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(N_{0,j} + k\,d_0,\ N_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
```

である。$`p \in N[n]`$ を取り、$`p`$ がどの部分の要素かで分ける。

- $`p \in (N_0,\dots,N_{j_0-1})`$ のとき。これは $`N`$ の先頭部分列であるから $`p \in N`$ であり、
  仮定より $`c \le p_1`$ である。

- $`p \in B_k`$ のとき。ある $`j`$（$`j_0 \le j \lt j_1`$）について
  $`p = (N_{0,j} + k\,d_0,\ N_{1,j})`$ である。$`j \lt j_1 \lt \lvert N\rvert`$ であるから
  [T.entry_pair_mem](#t-entry_pair_mem) より $`(N_{0,j}, N_{1,j}) \in N`$ であり、
  仮定より $`c \le N_{0,j}`$ である。したがって
  $`c \le N_{0,j} \le N_{0,j} + k\,d_0 = p_1`$ である。

**(II-b) $`\neg\,\mathrm{hasParent}(N, i_1, j_1)`$ のとき。**
$`N_{0,j_1} = 0 \wedge N_{1,j_1} = 0`$ が成り立つなら
[T.oper_eq_pred_of_zero](Decrease-ja.md#t-oper_eq_pred_of_zero) により、成り立たないなら
[T.oper_eq_pred_of_noParent](Decrease-ja.md#t-oper_eq_pred_of_noParent) により、
いずれにせよ $`N[n] = \mathrm{Pred}\,N`$ である。
$`\mathrm{Pred}`$ の定義（D.Pred）の場合分けにより $`\mathrm{Pred}\,N`$ は $`N`$ 自身か
$`\mathrm{dropLast}\,N`$ である。前者なら仮定そのものであり、後者なら
$`\mathrm{dropLast}\,N`$ の要素は $`N`$ の要素であるから仮定が適用できる。∎

<a id="t-graft_mem_ge"></a>
## 定理: 接ぎ木は行 0 の値の下界を保つ (T.graft_mem_ge)

### 定理

$`N \ne ()`$ かつ $`\forall p \in N,\ c \le p_1`$ ならば、任意の $`z`$ に対し
$`\forall p \in \mathrm{graft}(N,z),\ c \le p_1`$。

### 証明

$`N \ne ()`$ より $`0 \lt \lvert N\rvert`$ であるから $`j_1 := \lvert N\rvert - 1 \lt \lvert N\rvert`$ である。
[T.entry_pair_mem](#t-entry_pair_mem) より $`(N_{0,j_1}, N_{1,j_1}) \in N`$ であり、
仮定より

```math
c \le N_{0,j_1} .
```

$`\mathrm{graft}`$ の定義（D.graft）より
$`\mathrm{graft}(N,z) = \mathrm{dropLast}\,N \mathbin{+\!\!+} z^{+N_{0,j_1}}`$ である。
$`p \in \mathrm{graft}(N,z)`$ を取り、どちらの部分の要素かで分ける。

- $`p \in \mathrm{dropLast}\,N`$ のとき。$`\mathrm{dropLast}\,N`$ の要素は $`N`$ の要素であるから、
  仮定より $`c \le p_1`$ である。

- $`p \in z^{+N_{0,j_1}}`$ のとき。ある $`q \in z`$ について
  $`p = (q_1 + N_{0,j_1},\ q_2)`$ である。上で示した $`c \le N_{0,j_1}`$ と
  $`N_{0,j_1} \le q_1 + N_{0,j_1}`$ から $`c \le p_1`$ である。∎

<a id="t-graft_head_eq"></a>
## 定理: 接ぎ木は先頭の行 0 の値を変えない (T.graft_head_eq)

### 定理

$`N \ne ()`$、$`\mathrm{based}(z)`$、$`\mathrm{graft}(N,z) \ne ()`$ ならば

```math
\bigl(\mathrm{graft}(N,z)\bigr)_{0,0} = N_{0,0} .
```

### 証明

$`N \ne ()`$ より $`N = b_0 :: N'`$ と書ける。$`N'`$ が空か否かで場合分けする。

**(a) $`N = (b_0)`$ のとき。** $`\lvert N\rvert - 1 = 0`$ であり、
$`M_{i,j}`$ の定義（D.entry）より $`N_{0,0} = (b_0)_1`$ である。
$`\mathrm{dropLast}\,(b_0) = ()`$ であるから $`\mathrm{graft}`$ の定義（D.graft）より

```math
\mathrm{graft}(N, z) = z^{+(b_0)_1} .
```

仮定 $`\mathrm{graft}(N,z) \ne ()`$ よりこれは空でなく、したがって $`z \ne ()`$ である。
$`z = z_0 :: z'`$ と書くと、$`\mathrm{based}`$ の定義（D.based）と D.entry より
$`z_{0,0} = (z_0)_1 = 0`$ である。$`z^{+(b_0)_1}`$ の先頭は
$`\bigl((z_0)_1 + (b_0)_1,\ (z_0)_2\bigr) = \bigl((b_0)_1,\ (z_0)_2\bigr)`$ であるから、
D.entry より

```math
\bigl(\mathrm{graft}(N,z)\bigr)_{0,0} = (b_0)_1 = N_{0,0} .
```

**(b) $`N = b_0 :: b_1 :: N''`$ のとき。**
$`\mathrm{dropLast}\,N = b_0 :: \mathrm{dropLast}(b_1 :: N'')`$ であり、これは空でなく先頭は $`b_0`$ である。
したがって $`\mathrm{graft}(N,z) = \mathrm{dropLast}\,N \mathbin{+\!\!+} z^{+N_{0,\lvert N\rvert-1}}`$ の
先頭も $`b_0`$ である。D.entry より

```math
\bigl(\mathrm{graft}(N,z)\bigr)_{0,0} = (b_0)_1 = N_{0,0} . \qquad \blacksquare
```
