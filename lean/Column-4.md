[← README](README.md) ｜ Column [1](Column.md) [2](Column-2.md) [3](Column-3.md) **4**

<a id="t-nextrel0_unique"></a>
## 定理: 行 0 の親の一意性 (T.nextrel0_unique)

### 定理

$`k_1 \to^M_0 j`$（[D.nextrel0](Pss.md#d-nextrel0)）かつ $`k_2 \to^M_0 j`$ ならば $`k_1 = k_2`$。

### 証明

$`k_1`$ と $`k_2`$ の三分律で場合分けする。

**(a) $`k_1 \lt k_2`$ のとき。**
$`k_2 \to^M_0 j`$ の第 3 条件（D.nextrel0）より $`k_2 \lt j`$ である。
$`k_1 \to^M_0 j`$ の第 5 条件の全称変数に $`k_2`$ を代入すると、その前件
$`k_1 \lt k_2 \wedge k_2 \lt j`$ が成り立つから

```math
M_{0,j} \le M_{0,k_2}
```

を得る（$`M_{i,j}`$ [D.entry](Pss.md#d-entry)）。一方 $`k_2 \to^M_0 j`$ の第 4 条件は
$`M_{0,k_2} \lt M_{0,j}`$ である。
両者から $`M_{0,j} \lt M_{0,j}`$ となり、$`\lt`$ の非反射性に矛盾する。

**(b) $`k_1 = k_2`$ のとき。** 結論そのものである。

**(c) $`k_2 \lt k_1`$ のとき。**
$`k_1 \to^M_0 j`$ の第 3 条件より $`k_1 \lt j`$ である。
$`k_2 \to^M_0 j`$ の第 5 条件の全称変数に $`k_1`$ を代入すると、その前件
$`k_2 \lt k_1 \wedge k_1 \lt j`$ が成り立つから
$`M_{0,j} \le M_{0,k_1}`$ を得る。一方 $`k_1 \to^M_0 j`$ の第 4 条件は
$`M_{0,k_1} \lt M_{0,j}`$ である。両者から $`M_{0,j} \lt M_{0,j}`$ となり矛盾する。∎

<a id="t-nextrel1_unique"></a>
## 定理: 行 1 の親の一意性 (T.nextrel1_unique)

### 定理

$`k_1 \to^M_1 j`$（[D.nextrel1](Pss.md#d-nextrel1)）かつ $`k_2 \to^M_1 j`$ ならば $`k_1 = k_2`$。

### 証明

$`k_1`$ と $`k_2`$ の三分律で場合分けする。

**(a) $`k_1 \lt k_2`$ のとき。**
$`k_2 \to^M_1 j`$ の第 5 条件（D.nextrel1）より $`k_2 \le^M_0 j`$（[D.le0](Pss.md#d-le0)）である。
$`k_1 \to^M_1 j`$ の第 6 条件の全称変数に $`k_2`$ を代入すると、その前件
$`k_1 \lt k_2 \wedge k_2 \le^M_0 j`$ が成り立つから

```math
M_{1,j} \le M_{1,k_2}
```

を得る。一方 $`k_2 \to^M_1 j`$ の第 4 条件は $`M_{1,k_2} \lt M_{1,j}`$ である。
両者から $`M_{1,j} \lt M_{1,j}`$ となり、$`\lt`$ の非反射性に矛盾する。

**(b) $`k_1 = k_2`$ のとき。** 結論そのものである。

**(c) $`k_2 \lt k_1`$ のとき。**
$`k_1 \to^M_1 j`$ の第 5 条件より $`k_1 \le^M_0 j`$ である。
$`k_2 \to^M_1 j`$ の第 6 条件の全称変数に $`k_1`$ を代入すると、その前件
$`k_2 \lt k_1 \wedge k_1 \le^M_0 j`$ が成り立つから
$`M_{1,j} \le M_{1,k_1}`$ を得る。一方 $`k_1 \to^M_1 j`$ の第 4 条件は
$`M_{1,k_1} \lt M_{1,j}`$ である。両者から $`M_{1,j} \lt M_{1,j}`$ となり矛盾する。∎

<a id="t-blockok_head_zero"></a>
## 定理: ブロックの先頭は行 0 が 0 (T.blockok_head_zero)

### 定理

$`\mathrm{blockok}(0, M)`$（[D.blockok](Seqlex.md#d-blockok)）かつ $`0 \lt \lvert M\rvert`$ ならば
$`M_{0,0} = 0`$。

### 証明

$`0 \lt \lvert M\rvert`$ より $`M`$ は空でないから、$`M = m_0 :: M'`$ と書ける。
このとき $`M\langle 0\rangle = m_0`$ であり、$`M`$ の先頭要素も $`m_0`$ である。

$`\mathrm{blockok}`$ の定義（D.blockok）の第 1 連言子は
「$`M \ne ()`$ ならば $`M`$ の先頭要素の第 1 成分が $`0`$ に等しい」である。
$`M = m_0 :: M' \ne ()`$ であるから、$`\pi_1(m_0) = 0`$ を得る。
$`M_{i,j}`$ の定義（D.entry）より $`M_{0,0} = \pi_1(M\langle 0\rangle) = \pi_1(m_0) = 0`$。∎

<a id="t-parent0_exists"></a>
## 定理: 行 0 の親の存在 (T.parent0_exists)

### 定理

$`\mathrm{blockok}(0, M)`$、$`j \lt \lvert M\rvert`$、$`0 \lt M_{0,j}`$ ならば、
ある $`k`$ が存在して $`k \to^M_0 j`$。

### 証明

**第 1 段：$`0 \lt j`$。**
$`j = 0`$ とすると、[T.blockok_head_zero](#t-blockok_head_zero) より $`M_{0,0} = 0`$ であり、
これは仮定 $`0 \lt M_{0,j} = M_{0,0}`$ に矛盾する。

**第 2 段：候補の最大元を取る。** 述語 $`P`$ を

```math
P(k) :\equiv M_{0,k} \lt M_{0,j}
```

で定める。[T.blockok_head_zero](#t-blockok_head_zero) より $`M_{0,0} = 0`$ であり、
仮定より $`0 \lt M_{0,j}`$ であるから $`P(0)`$ が成り立つ。
集合

```math
S := \{\, k \mid k \le j - 1 \ \wedge\ P(k) \,\}
```

は $`0`$ を要素にもち（第 1 段より $`0 \le j - 1`$）、$`\{0, 1, \dots, j-1\}`$ に含まれる
有限集合であるから最大元をもつ。それを $`k`$ とおく。$`k`$ について次の 3 つが成り立つ。

```math
\begin{aligned}
&(\mathrm{i})\ k \le j - 1, \cr
&(\mathrm{ii})\ M_{0,k} \lt M_{0,j}, \cr
&(\mathrm{iii})\ \forall l,\ \bigl(k \lt l \wedge l \le j - 1\bigr) \to \neg\,\bigl(M_{0,l} \lt M_{0,j}\bigr).
\end{aligned}
```

$`(\mathrm{i})`$ と $`(\mathrm{ii})`$ は $`k \in S`$ から、$`(\mathrm{iii})`$ は $`k`$ が
$`S`$ の最大元であることから従う。

**第 3 段：$`k \to^M_0 j`$ の 5 条件を確かめる。**

- 第 1 条件 $`k \lt \lvert M\rvert`$：$`(\mathrm{i})`$ と第 1 段より $`k \le j - 1 \lt j`$ であり、
  仮定 $`j \lt \lvert M\rvert`$ と合わせて $`k \lt \lvert M\rvert`$。
- 第 2 条件 $`j \lt \lvert M\rvert`$：仮定である。
- 第 3 条件 $`k \lt j`$：$`(\mathrm{i})`$ と第 1 段より $`k \le j - 1 \lt j`$。
- 第 4 条件 $`M_{0,k} \lt M_{0,j}`$：$`(\mathrm{ii})`$ である。
- 第 5 条件 $`\forall l,\ (k \lt l \wedge l \lt j) \to M_{0,j} \le M_{0,l}`$：
  $`l`$ を取り $`k \lt l`$、$`l \lt j`$ とする。$`l \lt j`$ より $`l \le j - 1`$ であるから
  $`(\mathrm{iii})`$ が使えて $`\neg(M_{0,l} \lt M_{0,j})`$、すなわち
  $`M_{0,j} \le M_{0,l}`$。∎

<a id="t-chain_to_zero"></a>
## 定理: 行 0 が 0 の列への鎖 (T.chain_to_zero)

### 定理

$`\mathrm{blockok}(0, M)`$ とする。任意の $`\mathrm{lev}, j \in \mathbb{N}`$ について、
$`M_{0,j} = \mathrm{lev}`$ かつ $`j \lt \lvert M\rvert`$ ならば、ある $`r`$ が存在して

```math
r \le j, \qquad M_{0,r} = 0, \qquad r \mathbin{(\to^M_0)^{*}} j .
```

### 証明

$`\mathrm{lev}`$ に関する強帰納法。帰納法の述語は

```math
\Phi(\mathrm{lev}) :\equiv \forall j,\ \bigl(M_{0,j} = \mathrm{lev} \wedge j \lt \lvert M\rvert\bigr)
  \to \exists r,\ \bigl(r \le j \wedge M_{0,r} = 0 \wedge r \mathbin{(\to^M_0)^{*}} j\bigr),
```

帰納法の仮定は「$`\mathrm{lev}' \lt \mathrm{lev}`$ なるすべての $`\mathrm{lev}'`$ について
$`\Phi(\mathrm{lev}')`$」である。$`j`$ を取り $`M_{0,j} = \mathrm{lev}`$、$`j \lt \lvert M\rvert`$ とし、
$`M_{0,j}`$ が $`0`$ かどうかで場合分けする。

**(a) $`M_{0,j} = 0`$ のとき。** $`r := j`$ と取る。$`j \le j`$、$`M_{0,j} = 0`$ であり、
$`j \mathbin{(\to^M_0)^{*}} j`$ は長さ $`0`$ の鎖である。

**(b) $`M_{0,j} \ne 0`$、すなわち $`0 \lt M_{0,j}`$ のとき。**
[T.parent0_exists](#t-parent0_exists) を $`\mathrm{blockok}(0,M)`$、$`j \lt \lvert M\rvert`$、
$`0 \lt M_{0,j}`$ に適用して、$`k \to^M_0 j`$ なる $`k`$ を取る。
$`\to^M_0`$ の定義（D.nextrel0）の第 1 条件より $`k \lt \lvert M\rvert`$、
第 3 条件より $`k \lt j`$、第 4 条件より

```math
M_{0,k} \lt M_{0,j} = \mathrm{lev}
```

である。よって帰納法の仮定を $`\mathrm{lev}' := M_{0,k}`$ に適用でき、それを
$`j := k`$（$`M_{0,k} = M_{0,k}`$ と $`k \lt \lvert M\rvert`$ による）に用いると、

```math
r \le k, \qquad M_{0,r} = 0, \qquad r \mathbin{(\to^M_0)^{*}} k
```

なる $`r`$ が得られる。この鎖の末尾に $`k \to^M_0 j`$ を継ぎ足せば
$`r \mathbin{(\to^M_0)^{*}} j`$ であり、$`r \le k \lt j`$ より $`r \le j`$ である。∎

<a id="t-parent1_exists"></a>
## 定理: 行 1 の親の存在 (T.parent1_exists)

### 定理

$`\mathrm{blockok}(0, M)`$、$`\mathrm{z0ok}(M)`$（[D.z0ok](Column-3.md#d-z0ok)）、
$`j \lt \lvert M\rvert`$、$`0 \lt M_{1,j}`$ ならば、ある $`k`$ が存在して $`k \to^M_1 j`$。

### 証明

**第 1 段：行 0 の根までの鎖を取る。**
[T.chain_to_zero](#t-chain_to_zero) を $`\mathrm{lev} := M_{0,j}`$ に適用して、

```math
r \le j, \qquad M_{0,r} = 0, \qquad r \mathbin{(\to^M_0)^{*}} j
```

なる $`r`$ を取る。$`r \le j \lt \lvert M\rvert`$ である。
$`M_{0,r} = 0`$ に $`\mathrm{z0ok}(M)`$ の定義（D.z0ok）を適用して $`M_{1,r} = 0`$ を得る。

**第 2 段：$`r \lt j`$。**
$`r \le j`$ である。$`r = j`$ とすると $`M_{1,j} = M_{1,r} = 0`$ となり、
仮定 $`0 \lt M_{1,j}`$ に矛盾する。よって $`r \lt j`$。

**第 3 段：候補の最大元を取る。** 述語 $`P`$ を

```math
P(k) :\equiv k \le^M_0 j \ \wedge\ M_{1,k} \lt M_{1,j}
```

で定める。$`P(r)`$ が成り立つ。実際、$`\le^M_0`$ の定義（D.le0）の 3 条件は
$`r \lt \lvert M\rvert`$、$`j \lt \lvert M\rvert`$、$`r \mathbin{(\to^M_0)^{*}} j`$ で
いずれも第 1 段で得ており、また $`M_{1,r} = 0 \lt M_{1,j}`$ である。

集合

```math
S := \{\, k \mid k \le j - 1 \ \wedge\ P(k) \,\}
```

は $`r`$ を要素にもち（第 2 段より $`r \le j - 1`$）、$`\{0,1,\dots,j-1\}`$ に含まれる
有限集合であるから最大元をもつ。それを $`k`$ とおく。$`k`$ について

```math
\begin{aligned}
&(\mathrm{i})\ k \le j - 1, \cr
&(\mathrm{ii})\ k \le^M_0 j \ \wedge\ M_{1,k} \lt M_{1,j}, \cr
&(\mathrm{iii})\ \forall l,\ \bigl(k \lt l \wedge l \le j - 1\bigr) \to \neg\,P(l)
\end{aligned}
```

が成り立つ。

**第 4 段：$`k \to^M_1 j`$ の 6 条件を確かめる。**

- 第 1 条件 $`k \lt \lvert M\rvert`$：$`(\mathrm{i})`$ と第 2 段より $`k \le j - 1 \lt j`$ であり、
  $`j \lt \lvert M\rvert`$ と合わせてよい。
- 第 2 条件 $`j \lt \lvert M\rvert`$：仮定である。
- 第 3 条件 $`k \lt j`$：$`(\mathrm{i})`$ と第 2 段による。
- 第 4 条件 $`M_{1,k} \lt M_{1,j}`$：$`(\mathrm{ii})`$ の第 2 連言子である。
- 第 5 条件 $`k \le^M_0 j`$：$`(\mathrm{ii})`$ の第 1 連言子である。
- 第 6 条件 $`\forall j',\ (k \lt j' \wedge j' \le^M_0 j) \to M_{1,j} \le M_{1,j'}`$：
  $`j'`$ を取り $`k \lt j'`$、$`j' \le^M_0 j`$ とする。
  [T.le0_le](Column-3.md#t-le0_le) より $`j' \le j`$ である。
  - $`j' = j`$ のとき。示すべきは $`M_{1,j} \le M_{1,j}`$ であり、$`\le`$ の反射性による。
  - $`j' \lt j`$ のとき。$`M_{1,j} \le M_{1,j'}`$ を否定して $`M_{1,j'} \lt M_{1,j}`$ と
    仮定する。すると $`j' \le^M_0 j`$ と合わせて $`P(j')`$ が成り立つ。
    一方 $`k \lt j'`$ かつ $`j' \lt j`$ より $`j' \le j - 1`$ であるから、
    $`(\mathrm{iii})`$ が $`\neg P(j')`$ を与え、矛盾する。∎

<a id="t-nextR_one_iff"></a>
## 定理: 行 1 の親子関係の言い換え (T.nextR_one_iff)

### 定理

行つき親子関係 $`\to^M_i`$（[D.nextR](Pss.md#d-nextR)）に $`i := 1`$ を代入したものは、行 $`1`$ の親子関係
$`\to^M_1`$ に一致する。すなわち $`i = 1`$ のとき $`k \to^M_i j`$ と $`k \to^M_1 j`$ は
同値である。

### 証明

$`\to^M_i`$ の定義（D.nextR）は $`i = 0`$ かどうかによる場合分けである。
$`1 \ne 0`$ であるから第 2 の場合が選ばれ、両辺は定義により同一の命題である。∎

<a id="t-nextR_zero_iff"></a>
## 定理: 行 0 の親子関係の言い換え (T.nextR_zero_iff)

### 定理

行つき親子関係 $`\to^M_i`$ に $`i := 0`$ を代入したものは行 $`0`$ の親子関係
$`\to^M_0`$ に一致する。

### 証明

$`\to^M_i`$ の定義（D.nextR）の場合分けにおいて $`i = 0`$ の条件が成り立つから
第 1 の場合が選ばれ、両辺は定義により同一の命題である。∎

<a id="t-hp_last"></a>
## 定理: 末尾の列は親をもつ (T.hp_last)

### 定理

$`j_1 := \lvert M\rvert - 1`$ とおく。$`\mathrm{blockok}(0, M)`$、$`\mathrm{z0ok}(M)`$、
$`0 \lt \lvert M\rvert`$、$`M\langle j_1\rangle \ne (0,0)`$ ならば

```math
\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M, j_1),\ j_1\bigr).
```

（$`\mathrm{hasParent}`$ [D.hasParent](Pss.md#d-hasParent)、$`\mathrm{idx}_1`$ [D.idx1](Pss.md#d-idx1)）

### 証明

$`0 \lt \lvert M\rvert`$ より $`j_1 = \lvert M\rvert - 1 \lt \lvert M\rvert`$ である。
$`M_{1,j_1}`$ の正負で場合分けする。

**(a) $`0 \lt M_{1,j_1}`$ のとき。**
$`\mathrm{idx}_1`$ の定義（D.idx1）の第 1 の場合が選ばれ $`\mathrm{idx}_1(M,j_1) = 1`$ である。
[T.parent1_exists](#t-parent1_exists) を $`\mathrm{blockok}(0,M)`$、$`\mathrm{z0ok}(M)`$、
$`j_1 \lt \lvert M\rvert`$、$`0 \lt M_{1,j_1}`$ に適用して、$`k \to^M_1 j_1`$ なる $`k`$ を取る。

$`\mathrm{hasParent}`$ の定義（D.hasParent）は存在と一意性の連言である。

- 存在：$`\mathrm{idx}_1(M,j_1) = 1`$ であるから、示すべきは $`i = 1`$ の場合の
  $`k \to^M_i j_1`$ である。[T.nextR_one_iff](#t-nextR_one_iff) よりこれは
  $`k \to^M_1 j_1`$ と同値であり、後者は上で得た。
- 一意性：$`y`$ が $`i = 1`$ の場合の $`y \to^M_i j_1`$ をみたすとすると、ふたたび
  [T.nextR_one_iff](#t-nextR_one_iff) より $`y \to^M_1 j_1`$ である。
  [T.nextrel1_unique](#t-nextrel1_unique) を $`y \to^M_1 j_1`$ と $`k \to^M_1 j_1`$ に
  適用して $`y = k`$。

**(b) $`M_{1,j_1} = 0`$ のとき。**
まず $`0 \lt M_{0,j_1}`$ を示す。$`M_{0,j_1} = 0`$ とすると、
$`M_{i,j}`$ の定義（D.entry）より $`\pi_1(M\langle j_1\rangle) = M_{0,j_1} = 0`$、
$`\pi_2(M\langle j_1\rangle) = M_{1,j_1} = 0`$ であるから
$`M\langle j_1\rangle = (0,0)`$ となり、仮定 $`M\langle j_1\rangle \ne (0,0)`$ に矛盾する。

$`\mathrm{idx}_1`$ の定義（D.idx1）の条件 $`0 \lt M_{1,j_1}`$ は偽であるから
$`\mathrm{idx}_1(M,j_1) = 0`$ である。
[T.parent0_exists](#t-parent0_exists) を $`\mathrm{blockok}(0,M)`$、
$`j_1 \lt \lvert M\rvert`$、$`0 \lt M_{0,j_1}`$ に適用して、$`k \to^M_0 j_1`$ なる $`k`$ を取る。

$`\mathrm{hasParent}`$ の定義（D.hasParent）の 2 つを確かめる。

- 存在：$`\mathrm{idx}_1(M,j_1) = 0`$ であるから、示すべきは $`i = 0`$ の場合の
  $`k \to^M_i j_1`$ である。[T.nextR_zero_iff](#t-nextR_zero_iff) よりこれは
  $`k \to^M_0 j_1`$ と同値であり、後者は上で得た。
- 一意性：$`y`$ が $`i = 0`$ の場合の $`y \to^M_i j_1`$ をみたすとすると、ふたたび
  [T.nextR_zero_iff](#t-nextR_zero_iff) より $`y \to^M_0 j_1`$ である。
  [T.nextrel0_unique](#t-nextrel0_unique) を $`y \to^M_0 j_1`$ と $`k \to^M_0 j_1`$ に
  適用して $`y = k`$。∎

<a id="t-z0ok_oper"></a>
## 定理: 展開は $`\mathrm{z0ok}`$ を保つ (T.z0ok_oper)

### 定理

$`1 \le n`$ かつ $`\mathrm{z0ok}(M)`$ ならば $`\mathrm{z0ok}(M[n])`$（$`M[n]`$ [D.oper](Pss.md#d-oper)）。

### 証明

$`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$ とおき、
$`M[n]`$ の定義（D.oper）の分岐に沿って場合分けする。

**(a) $`j_1 = 0`$ のとき。**
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より $`M[n] = M`$ であり、
結論は仮定 $`\mathrm{z0ok}(M)`$ そのものである。

**(b) $`j_1 \ne 0`$ かつ $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。**
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) より
$`M[n] = \mathrm{Pred}\,M`$（[D.Pred](Pss.md#d-Pred)）であり、[T.z0ok_Pred](Column-3.md#t-z0ok_Pred) を適用する。

**(c) $`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) より
$`M[n] = \mathrm{Pred}\,M`$ であり、[T.z0ok_Pred](Column-3.md#t-z0ok_Pred) を適用する。

**(d) $`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
$`1 \lt \lvert M\rvert`$ である。実際 $`\lvert M\rvert \le 1`$ とすると、自然数の減法は
$`0`$ で切り捨てるから $`j_1 = \lvert M\rvert - 1 = 0`$ となり、この場合の仮定
$`j_1 \ne 0`$ に反する。
[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) を
$`1 \lt \lvert M\rvert`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、
$`\mathrm{hasParent}(M, i_1, j_1)`$、$`1 \le n`$ に適用して
$`G, v_0, w_0, R, d_0, \ell`$ を取る。その (1) と (2) は

```math
M = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} (\ell),
```
```math
M[n] = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+0\cdot d_0}
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+(n-1)d_0}
```

である（$`L^{+e}`$ [D.copyExp](Column-2.md#d-copyExp)）。
後者の右辺は $`\mathrm{copyExp}`$ の定義（D.copyExp）により

```math
M[n] = \mathrm{copyExp}\bigl(G,\ (v_0,w_0) :: R,\ d_0,\ n\bigr)
```

と書ける。仮定 $`\mathrm{z0ok}(M)`$ を (1) で書き換えると
$`\mathrm{z0ok}\bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr)`$ であるから、
[T.z0ok_copyExp](Column-3.md#t-z0ok_copyExp) を $`B := (v_0,w_0) :: R`$ に適用して結論を得る。∎

<a id="t-z0ok_ST_PS"></a>
## 定理: 標準形は $`\mathrm{z0ok}`$ をみたす (T.z0ok_ST_PS)

### 定理

$`M \in \mathrm{ST\_PS}`$（[D.ST_PS](Pss.md#d-ST_PS)）ならば $`\mathrm{z0ok}(M)`$。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M) :\equiv \mathrm{z0ok}(M).
```

- **基底段**（規則 (diag)）：$`M = \Delta_0^v`$（[D.diagSeq](Pss.md#d-diagSeq)）である。
  [T.z0ok_diagSeq](Column-3.md#t-z0ok_diagSeq) が $`\Phi(\Delta_0^v)`$ そのものである。

- **帰納段**（規則 (oper)）：$`N \in \mathrm{ST\_PS}`$、$`1 \le n`$ とし、帰納法の仮定は
  $`\Phi(N)`$、すなわち $`\mathrm{z0ok}(N)`$ である。
  [T.z0ok_oper](#t-z0ok_oper) を $`1 \le n`$ と $`\mathrm{z0ok}(N)`$ に適用して
  $`\mathrm{z0ok}(N[n])`$、すなわち $`\Phi(N[n])`$ を得る。∎

<a id="t-rtg_through_pivot"></a>
## 定理: 行 0 の鎖は枢軸を通る (T.rtg_through_pivot)

### 定理

$`M \in \mathrm{PairSeq}`$（[D.PairSeq](Pss.md#d-PairSeq)）、$`\rho \in \mathbb{N}`$ とする。
任意の $`a, b \in \mathbb{N}`$ について、

```math
a \mathbin{(\to^M_0)^{*}} b, \qquad a \lt \rho, \qquad \rho \le b, \qquad
\forall y,\ \bigl(\rho \lt y \wedge y \le b\bigr) \to M_{0,\rho} \lt M_{0,y}
```

ならば $`\rho \mathbin{(\to^M_0)^{*}} b`$。

### 証明

$`a`$ を固定し、鎖 $`a \mathbin{(\to^M_0)^{*}} b`$ の構成に関する帰納法。
帰納法の述語は

```math
\Phi(b) :\equiv \Bigl(a \lt \rho \wedge \rho \le b \wedge
  \forall y,\ (\rho \lt y \wedge y \le b) \to M_{0,\rho} \lt M_{0,y}\Bigr)
  \to \rho \mathbin{(\to^M_0)^{*}} b .
```

- **基底段**（$`b = a`$、鎖の長さ $`0`$）：前件の第 1 連言子は $`a \lt \rho`$、
  第 2 連言子は $`\rho \le a`$ であり、両者から $`a \lt a`$ となって $`\lt`$ の
  非反射性に反する。よって前件が偽であり $`\Phi(a)`$ が成り立つ。

**帰納段**（$`a \mathbin{(\to^M_0)^{*}} y`$ と $`y \to^M_0 z`$ から
$`a \mathbin{(\to^M_0)^{*}} z`$）：帰納法の仮定は $`\Phi(y)`$ である。
$`a \lt \rho`$、$`\rho \le z`$、および

```math
(\ast)\qquad \forall y',\ \bigl(\rho \lt y' \wedge y' \le z\bigr) \to M_{0,\rho} \lt M_{0,y'}
```

を仮定して $`\rho \mathbin{(\to^M_0)^{*}} z`$ を示す。$`\rho`$ と $`y`$ の大小で場合分けする。

**(a) $`\rho \le y`$ のとき。**
[T.nextrel0_lt](Column.md#t-nextrel0_lt) より $`y \lt z`$ である。したがって
$`\rho \lt y' \wedge y' \le y`$ なる $`y'`$ は $`y' \le y \le z`$ をみたすから、
$`(\ast)`$ より $`M_{0,\rho} \lt M_{0,y'}`$ である。すなわち帰納法の仮定 $`\Phi(y)`$ の
前件 3 つがすべて成り立つ。よって $`\rho \mathbin{(\to^M_0)^{*}} y`$ を得る。
この鎖の末尾に $`y \to^M_0 z`$ を継ぎ足せば $`\rho \mathbin{(\to^M_0)^{*}} z`$ である。

**(b) $`y \lt \rho`$ のとき。** さらに $`\rho`$ と $`z`$ で場合分けする（$`\rho \le z`$ である）。

**(b-1) $`\rho = z`$ のとき。** $`\rho \mathbin{(\to^M_0)^{*}} z`$ は長さ $`0`$ の鎖である。

**(b-2) $`\rho \lt z`$ のとき。** $`y \to^M_0 z`$ すなわち $`\to^M_0`$ の定義（D.nextrel0）の
第 5 条件の全称変数に $`\rho`$ を代入すると、その前件 $`y \lt \rho \wedge \rho \lt z`$ が
成り立つから

```math
M_{0,z} \le M_{0,\rho}
```

を得る。一方 $`(\ast)`$ を $`y' := z`$ に適用すると（$`\rho \lt z`$ かつ $`z \le z`$）
$`M_{0,\rho} \lt M_{0,z}`$ である。両者から $`M_{0,z} \lt M_{0,z}`$ となり
$`\lt`$ の非反射性に矛盾する。よってこの場合は起こらない。∎

<a id="t-le0_through_pivot"></a>
## 定理: 行 0 の祖先関係は枢軸を通る (T.le0_through_pivot)

### 定理

$`a \le^M_0 b`$、$`a \lt \rho`$、$`\rho \le b`$、かつ

```math
\forall y,\ \bigl(\rho \lt y \wedge y \le b\bigr) \to M_{0,\rho} \lt M_{0,y}
```

ならば $`\rho \le^M_0 b`$。

### 証明

$`\le^M_0`$ の定義（D.le0）の 3 条件を確かめる。仮定 $`a \le^M_0 b`$ からは
$`a \lt \lvert M\rvert`$、$`b \lt \lvert M\rvert`$、$`a \mathbin{(\to^M_0)^{*}} b`$ が得られる。

- 第 1 条件 $`\rho \lt \lvert M\rvert`$：$`\rho \le b`$ と $`b \lt \lvert M\rvert`$ による。
- 第 2 条件 $`b \lt \lvert M\rvert`$：上のとおりである。
- 第 3 条件 $`\rho \mathbin{(\to^M_0)^{*}} b`$：
  [T.rtg_through_pivot](#t-rtg_through_pivot) を $`a \mathbin{(\to^M_0)^{*}} b`$、
  $`a \lt \rho`$、$`\rho \le b`$、および最後の仮定に適用する。∎

<a id="t-entry_shift"></a>
## 定理: 平行移動列の成分 (T.entry_shift)

### 定理

$`S \in \mathrm{PairSeq}`$、$`d, j \in \mathbb{N}`$ とする。$`j \lt \lvert S\rvert`$ ならば

```math
(S^{+d})_{0,j} = S_{0,j} + d
\qquad\text{かつ}\qquad
(S^{+d})_{1,j} = S_{1,j} .
```

### 証明

$`L^{+e}`$ の定義（D.copyExp）より $`S^{+d}`$ は $`S`$ の各要素を写したものであるから
$`\lvert S^{+d}\rvert = \lvert S\rvert`$ であり、仮定 $`j \lt \lvert S\rvert`$ より
どちらの列でも第 $`j`$ 要素が存在する。
[T.getD_eq_getElem'](Cnf.md#t-getD_eq_getElem') より

```math
S\langle j\rangle = S_j, \qquad S^{+d}\langle j\rangle = (S^{+d})_j = \bigl(\pi_1(S_j) + d,\ \pi_2(S_j)\bigr)
```

である。$`M_{i,j}`$ の定義（D.entry）は $`i = 0`$ のとき第 1 成分、$`i \ne 0`$ のとき
第 2 成分を読むから、

```math
(S^{+d})_{0,j} = \pi_1(S_j) + d = S_{0,j} + d,
\qquad
(S^{+d})_{1,j} = \pi_2(S_j) = S_{1,j} . \qquad \blacksquare
```

<a id="t-nextrel0_shift_iff"></a>
## 定理: 行 0 の親子関係の平行移動不変性 (T.nextrel0_shift_iff)

### 定理

$`b \lt \lvert S\rvert`$ ならば

```math
a \to^{S^{+d}}_0 b \iff a \to^{S}_0 b .
```

### 証明

$`\lvert S^{+d}\rvert = \lvert S\rvert`$ であるから、$`\to^M_0`$ の定義（D.nextrel0）の
第 1・第 2・第 3 条件は両辺で同一の命題である。第 4・第 5 条件を両方向で移す。

**（左から右）** $`a \to^{S^{+d}}_0 b`$ を仮定する。第 1 条件より $`a \lt \lvert S\rvert`$ で
ある。示すべき第 4・第 5 条件は次のとおり。

- 第 4 条件：仮定の第 4 条件は $`(S^{+d})_{0,a} \lt (S^{+d})_{0,b}`$ である。
  [T.entry_shift](#t-entry_shift) を $`j := a`$ と $`j := b`$ に適用すると
  $`S_{0,a} + d \lt S_{0,b} + d`$ となり、$`\mathbb{N}`$ の加法の狭義単調性から
  $`S_{0,a} \lt S_{0,b}`$ を得る。

- 第 5 条件：$`l`$ を取り $`a \lt l`$、$`l \lt b`$ とする。$`l \lt b \lt \lvert S\rvert`$ で
  あるから [T.entry_shift](#t-entry_shift) が $`j := l`$ と $`j := b`$ で使えて、
  仮定の第 5 条件 $`(S^{+d})_{0,b} \le (S^{+d})_{0,l}`$ は
  $`S_{0,b} + d \le S_{0,l} + d`$、すなわち $`S_{0,b} \le S_{0,l}`$ に等しい。

**（右から左）** $`a \to^{S}_0 b`$ を仮定する。第 1 条件より $`a \lt \lvert S\rvert`$ である。

- 第 4 条件：仮定の第 4 条件 $`S_{0,a} \lt S_{0,b}`$ の両辺に $`d`$ を足して
  $`S_{0,a} + d \lt S_{0,b} + d`$ であり、[T.entry_shift](#t-entry_shift) により
  これは $`(S^{+d})_{0,a} \lt (S^{+d})_{0,b}`$ である。

- 第 5 条件：$`l`$ を取り $`a \lt l`$、$`l \lt b`$ とする。$`l \lt \lvert S\rvert`$ であるから
  [T.entry_shift](#t-entry_shift) が使え、仮定の第 5 条件
  $`S_{0,b} \le S_{0,l}`$ の両辺に $`d`$ を足して
  $`(S^{+d})_{0,b} \le (S^{+d})_{0,l}`$ を得る。∎

<a id="t-rtg_shift_of"></a>
## 定理: 平行移動列の鎖はもとの列の鎖 (T.rtg_shift_of)

### 定理

$`a \mathbin{(\to^{S^{+d}}_0)^{*}} b`$ ならば $`a \mathbin{(\to^{S}_0)^{*}} b`$。

### 証明

鎖 $`a \mathbin{(\to^{S^{+d}}_0)^{*}} b`$ の構成に関する帰納法。帰納法の述語は

```math
\Phi(b) :\equiv a \mathbin{(\to^{S}_0)^{*}} b .
```

- **基底段**（$`b = a`$、鎖の長さ $`0`$）：$`a \mathbin{(\to^{S}_0)^{*}} a`$ は
  長さ $`0`$ の鎖である。

- **帰納段**（$`a \mathbin{(\to^{S^{+d}}_0)^{*}} c`$ と $`c \to^{S^{+d}}_0 e`$）：
  帰納法の仮定は $`\Phi(c)`$、すなわち $`a \mathbin{(\to^{S}_0)^{*}} c`$ である。
  [T.nextrel0_bound](Column-3.md#t-nextrel0_bound) を $`c \to^{S^{+d}}_0 e`$ に適用して
  $`e \lt \lvert S^{+d}\rvert = \lvert S\rvert`$ を得る。
  よって [T.nextrel0_shift_iff](#t-nextrel0_shift_iff) が使えて $`c \to^{S}_0 e`$ である。
  帰納法の仮定の鎖の末尾にこの 1 歩を継ぎ足せば $`a \mathbin{(\to^{S}_0)^{*}} e`$、
  すなわち $`\Phi(e)`$。∎

<a id="t-rtg_shift_to"></a>
## 定理: もとの列の鎖は平行移動列の鎖 (T.rtg_shift_to)

### 定理

$`a \mathbin{(\to^{S}_0)^{*}} b`$ ならば $`a \mathbin{(\to^{S^{+d}}_0)^{*}} b`$。

### 証明

鎖 $`a \mathbin{(\to^{S}_0)^{*}} b`$ の構成に関する帰納法。帰納法の述語は

```math
\Phi(b) :\equiv a \mathbin{(\to^{S^{+d}}_0)^{*}} b .
```

- **基底段**（$`b = a`$、鎖の長さ $`0`$）：$`a \mathbin{(\to^{S^{+d}}_0)^{*}} a`$ は
  長さ $`0`$ の鎖である。

- **帰納段**（$`a \mathbin{(\to^{S}_0)^{*}} c`$ と $`c \to^{S}_0 e`$）：
  帰納法の仮定は $`\Phi(c)`$、すなわち $`a \mathbin{(\to^{S^{+d}}_0)^{*}} c`$ である。
  [T.nextrel0_bound](Column-3.md#t-nextrel0_bound) を $`c \to^{S}_0 e`$ に適用して
  $`e \lt \lvert S\rvert`$ を得る。よって
  [T.nextrel0_shift_iff](#t-nextrel0_shift_iff) が使えて $`c \to^{S^{+d}}_0 e`$ である。
  帰納法の仮定の鎖の末尾にこの 1 歩を継ぎ足せば
  $`a \mathbin{(\to^{S^{+d}}_0)^{*}} e`$、すなわち $`\Phi(e)`$。∎

<a id="t-le0_shift_iff"></a>
## 定理: 行 0 の祖先関係の平行移動不変性 (T.le0_shift_iff)

### 定理

```math
a \le^{S^{+d}}_0 b \iff a \le^{S}_0 b .
```

### 証明

$`\lvert S^{+d}\rvert = \lvert S\rvert`$ であるから、$`\le^M_0`$ の定義（D.le0）の
第 1・第 2 条件は両辺で同一の命題である。第 3 条件は、
左から右が [T.rtg_shift_of](#t-rtg_shift_of)、
右から左が [T.rtg_shift_to](#t-rtg_shift_to) である。∎

<a id="t-idx1_shift"></a>
## 定理: 探索行の平行移動不変性 (T.idx1_shift)

### 定理

```math
\mathrm{idx}_1(S^{+d}, j) = \mathrm{idx}_1(S, j) .
```

### 証明

$`\mathrm{idx}_1`$ の定義（D.idx1）は $`0 \lt M_{1,j}`$ の真偽だけで値が決まるから、
$`(S^{+d})_{1,j} = S_{1,j}`$ を示せばよい。$`j`$ と $`\lvert S\rvert`$ の大小で場合分けする。

**(a) $`j \lt \lvert S\rvert`$ のとき。**
[T.entry_shift](#t-entry_shift) の第 2 の等式そのものである。

**(b) $`\lvert S\rvert \le j`$ のとき。**
$`\lvert S^{+d}\rvert = \lvert S\rvert \le j`$ であるから、
$`M\langle j\rangle`$ の定義（D.entry）より
$`S\langle j\rangle = (0,0)`$ かつ $`S^{+d}\langle j\rangle = (0,0)`$ である。
よって $`(S^{+d})_{1,j} = \pi_2\bigl((0,0)\bigr) = 0 = S_{1,j}`$。∎

<a id="t-nextrel1_shift_iff"></a>
## 定理: 行 1 の親子関係の平行移動不変性 (T.nextrel1_shift_iff)

### 定理

$`b \lt \lvert S\rvert`$ ならば

```math
a \to^{S^{+d}}_1 b \iff a \to^{S}_1 b .
```

### 証明

$`\lvert S^{+d}\rvert = \lvert S\rvert`$ であるから、$`\to^M_1`$ の定義（D.nextrel1）の
第 1・第 2・第 3 条件は両辺で同一の命題である。第 5 条件は
[T.le0_shift_iff](#t-le0_shift_iff) により両辺で同値である。残る第 4・第 6 条件を
両方向で移す。

**（左から右）** $`a \to^{S^{+d}}_1 b`$ を仮定する。第 1 条件より $`a \lt \lvert S\rvert`$ で
ある。

- 第 4 条件：仮定の第 4 条件は $`(S^{+d})_{1,a} \lt (S^{+d})_{1,b}`$ である。
  [T.entry_shift](#t-entry_shift) を $`j := a`$ と $`j := b`$ に適用すると
  第 2 の等式により $`S_{1,a} \lt S_{1,b}`$ となる。

- 第 6 条件：$`l`$ を取り $`a \lt l`$、$`l \le^{S}_0 b`$ とする。
  [T.le0_shift_iff](#t-le0_shift_iff) より $`l \le^{S^{+d}}_0 b`$ であるから、
  仮定の第 6 条件の全称変数に $`l`$ を代入して
  $`(S^{+d})_{1,b} \le (S^{+d})_{1,l}`$ を得る。
  [T.le0_le](Column-3.md#t-le0_le) より $`l \le b \lt \lvert S\rvert`$ であるから、
  [T.entry_shift](#t-entry_shift) が $`j := l`$ と $`j := b`$ で使えて、
  この不等式は $`S_{1,b} \le S_{1,l}`$ に等しい。

**（右から左）** $`a \to^{S}_1 b`$ を仮定する。第 1 条件より $`a \lt \lvert S\rvert`$ である。

- 第 4 条件：仮定の第 4 条件 $`S_{1,a} \lt S_{1,b}`$ に
  [T.entry_shift](#t-entry_shift) の第 2 の等式を $`j := a`$ と $`j := b`$ で適用すれば
  $`(S^{+d})_{1,a} \lt (S^{+d})_{1,b}`$ である。

- 第 6 条件：$`l`$ を取り $`a \lt l`$、$`l \le^{S^{+d}}_0 b`$ とする。
  [T.le0_shift_iff](#t-le0_shift_iff) より $`l \le^{S}_0 b`$ であり、
  [T.le0_le](Column-3.md#t-le0_le) より $`l \le b \lt \lvert S\rvert`$ である。
  仮定の第 6 条件の全称変数に $`l`$ を代入して $`S_{1,b} \le S_{1,l}`$ を得る。
  [T.entry_shift](#t-entry_shift) が $`j := l`$ と $`j := b`$ で使えて、
  この不等式は $`(S^{+d})_{1,b} \le (S^{+d})_{1,l}`$ に等しい。∎
