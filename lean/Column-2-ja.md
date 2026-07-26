[← README](README-ja.md) | [English](Column-2.md) | [Japanese](Column-2-ja.md) | Column [1](Column-ja.md) **2** [3](Column-3-ja.md) [4](Column-4-ja.md)

<a id="t-oper_append_right"></a>
## 定理: 展開は前置と可換 (T.oper_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）、$`n \in \mathbb{N}`$ とし、
$`2 \le \lvert T\rvert`$ かつ $`T_{0,0} = 0`$（[D.entry](Pss-ja.md#d-entry)）とする。
このとき

```math
(A \mathbin{+\!\!+} T)[n] = A \mathbin{+\!\!+} T[n] .
```

（$`M[n]`$ [D.oper](Pss-ja.md#d-oper)）

### 証明

$`j_1 := \lvert T\rvert - 1`$ とおく。$`2 \le \lvert T\rvert`$ より $`1 \le j_1`$、とくに $`j_1 \ne 0`$ である。
また

```math
\lvert A \mathbin{+\!\!+} T\rvert - 1 = (\lvert A\rvert + \lvert T\rvert) - 1 = \lvert A\rvert + j_1
```

であるから、$`A \mathbin{+\!\!+} T`$ に対する $`M[n]`$ の定義（D.oper）の末尾添字は $`\lvert A\rvert + j_1`$ である。
以下、D.oper の 4 分岐を左右で対応させる。

**分岐 (a)。** 条件は左辺では $`\lvert A\rvert + j_1 = 0`$、右辺では $`j_1 = 0`$ であり、
$`1 \le j_1`$ よりいずれも偽である。よって両辺とも分岐 (a) を選ばない。

**分岐 (b)。** 条件は左辺では
$`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = 0 \wedge (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} = 0`$、
右辺では $`T_{0,j_1} = 0 \wedge T_{1,j_1} = 0`$ である。
[T.entry_append_right](Column-ja.md#t-entry_append_right) より

```math
(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = T_{0,j_1},
\qquad
(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} = T_{1,j_1}
```

であるから、2 つの条件は同一の命題である。これが成り立つ場合、両辺はそれぞれ
$`\mathrm{Pred}\,(A \mathbin{+\!\!+} T)`$（[D.Pred](Pss-ja.md#d-Pred)）と $`\mathrm{Pred}\,T`$ であり、
[T.Pred_append_right](Column-ja.md#t-Pred_append_right) により
$`\mathrm{Pred}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{Pred}\,T`$ である。
以下、この条件は成り立たないとする。

**探索行。** [T.idx1_append_right](Column-ja.md#t-idx1_append_right) より
$`\mathrm{idx}_1(A \mathbin{+\!\!+} T, \lvert A\rvert + j_1) = \mathrm{idx}_1(T, j_1)`$（[D.idx1](Pss-ja.md#d-idx1)）
であるから、両辺の $`i_1`$ は共通の値である。これを $`i_1 := \mathrm{idx}_1(T, j_1)`$ と書く。
$`\mathrm{hasParent}(T, i_1, j_1)`$（[D.hasParent](Pss-ja.md#d-hasParent)）が成り立つかどうかで場合分けする。

**(A) $`\mathrm{hasParent}(T, i_1, j_1)`$ が成り立つとき。**
まず $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ を示す。
上の書き換えによりこれは $`0 \lt T_{0,j_1}`$ と同値である。
$`T_{0,j_1} = 0`$ とすると [T.no_hasParent_of_row0_zero](Column-ja.md#t-no_hasParent_of_row0_zero) を
$`M := T`$、$`i := i_1`$、$`j_1 := j_1`$ に適用して矛盾する。
よって [T.hasParent_append_right](Column-ja.md#t-hasParent_append_right) の（$`\Leftarrow`$）が適用でき、
$`\mathrm{hasParent}(A \mathbin{+\!\!+} T, i_1, \lvert A\rvert + j_1)`$ が成り立つ。
したがって分岐 (c) の条件は両辺で偽であり、両辺とも分岐 (d) を選ぶ。

分岐 (d) の各構成要素を比べる。$`j_0 := \mathrm{par}^{T}_{i_1}(j_1)`$（[D.parent](Pss-ja.md#d-parent)）とおく。

**親。** [T.parent_append_right](Column-ja.md#t-parent_append_right) より
$`\mathrm{par}^{A \mathbin{+\!\!+} T}_{i_1}(\lvert A\rvert + j_1) = \lvert A\rvert + j_0`$ である。

**増分。** 左辺の $`d_0`$ と $`d_1`$ は D.oper の式により

```math
d_0 = \begin{cases}
(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} - (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_0} & (0 \lt i_1) \cr
0 & (i_1 = 0)
\end{cases}
\qquad
d_1 = \begin{cases}
(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} - (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_0} & (1 \lt i_1) \cr
0 & (i_1 \le 1)
\end{cases}
```

である。[T.entry_append_right](Column-ja.md#t-entry_append_right) を 4 つの成分に適用すると、
これらはそれぞれ $`0 \lt i_1`$ のとき $`T_{0,j_1} - T_{0,j_0}`$、$`1 \lt i_1`$ のとき
$`T_{1,j_1} - T_{1,j_0}`$ に等しく、条件の部分も共通であるから、右辺の $`d_0`$、$`d_1`$ と一致する。

**前部分列。** [T.take_append_right](Column-ja.md#t-take_append_right) より
$`\mathrm{take}_{\lvert A\rvert + j_0}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{take}_{j_0}\,T`$ である。

**コピーブロック。** 左辺の第 $`k`$ ブロックは、添字 $`j`$ を $`\lvert A\rvert + j_0`$ から
$`(\lvert A\rvert + j_1) - 1`$ まで走らせた長さ
$`(\lvert A\rvert + j_1) - (\lvert A\rvert + j_0) = j_1 - j_0`$ の列

```math
\Bigl(\bigl((A \mathbin{+\!\!+} T)_{0,j} + k\,d_0,\ (A \mathbin{+\!\!+} T)_{1,j} + k\,d_1\bigr)\Bigr)_{j = \lvert A\rvert + j_0}^{\lvert A\rvert + j_1 - 1}
```

である。[T.copyblock_append](Column-ja.md#t-copyblock_append) を $`a := j_0`$、$`m := j_1 - j_0`$ に適用すると、
これは右辺の第 $`k`$ ブロック

```math
\Bigl(\bigl(T_{0,j} + k\,d_0,\ T_{1,j} + k\,d_1\bigr)\Bigr)_{j = j_0}^{j_1 - 1}
```

に等しい。これが $`k = 0, 1, \dots, n-1`$ のすべてについて成り立つ。

以上より、共通のブロックを $`B_0, \dots, B_{n-1}`$ と書くと

```math
\begin{aligned}
(A \mathbin{+\!\!+} T)[n]
 &= \bigl(A \mathbin{+\!\!+} \mathrm{take}_{j_0}\,T\bigr)
    \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1} \cr
 &= A \mathbin{+\!\!+} \bigl(\mathrm{take}_{j_0}\,T
    \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1}\bigr) \cr
 &= A \mathbin{+\!\!+} T[n]
\end{aligned}
```

である（中央の等号は連結の結合律）。

**(B) $`\neg\,\mathrm{hasParent}(T, i_1, j_1)`$ のとき。**
$`\neg\,\mathrm{hasParent}(A \mathbin{+\!\!+} T, i_1, \lvert A\rvert + j_1)`$ を示す。
$`\mathrm{hasParent}(A \mathbin{+\!\!+} T, i_1, \lvert A\rvert + j_1)`$ が成り立つと仮定して
$`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ で場合分けする。

- $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ のとき。
  [T.hasParent_append_right](Column-ja.md#t-hasParent_append_right) の（$`\Rightarrow`$）より
  $`\mathrm{hasParent}(T, i_1, j_1)`$ となり、この場合の仮定に矛盾する。
- $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = 0`$ のとき。
  [T.no_hasParent_of_row0_zero](Column-ja.md#t-no_hasParent_of_row0_zero) を
  $`M := A \mathbin{+\!\!+} T`$、$`j_1 := \lvert A\rvert + j_1`$ に適用して矛盾する。

よって両辺とも分岐 (c) を選び、それぞれ $`\mathrm{Pred}\,(A \mathbin{+\!\!+} T)`$ と $`\mathrm{Pred}\,T`$ である。
[T.Pred_append_right](Column-ja.md#t-Pred_append_right) により両者は $`A`$ の連結で結ばれる。∎

<a id="t-map_range_entry_eq_take"></a>
## 定理: 成分の列挙は前部分列 (T.map_range_entry_eq_take)

### 定理

$`N \in \mathrm{PairSeq}`$、$`j_1 \in \mathbb{N}`$ とし $`j_1 \le \lvert N\rvert`$ とする。このとき

```math
\bigl((N_{0,j},\ N_{1,j})\bigr)_{j = 0}^{j_1 - 1} = \mathrm{take}_{j_1}\,N .
```

### 証明

両辺の長さと各要素を比べる。

**長さ。** 左辺は長さ $`j_1`$ の列である。右辺の長さは
$`\min(j_1, \lvert N\rvert)`$ であり、仮定 $`j_1 \le \lvert N\rvert`$ より $`j_1`$ である。

**第 $`i`$ 要素（$`i \lt j_1`$）。**
$`i \lt j_1 \le \lvert N\rvert`$ であるから、$`M\langle j\rangle`$ の定義（D.entry）の第 1 の場合により
$`N\langle i\rangle = N_i`$ である。よって左辺の第 $`i`$ 要素は

```math
(N_{0,i},\ N_{1,i}) = \bigl(\pi_1(N_i),\ \pi_2(N_i)\bigr) = N_i
```

である。右辺の第 $`i`$ 要素は、$`i \lt j_1`$ より $`N`$ の第 $`i`$ 要素 $`N_i`$ である。
よって両辺の第 $`i`$ 要素は一致する。∎

<a id="t-oper_headD"></a>
## 定理: 展開は先頭を変えない (T.oper_headD)

### 定理

$`N \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とし、$`1 \lt \lvert N\rvert`$ かつ $`1 \le n`$ とする。
このとき $`\mathrm{head}\,(N[n]) = \mathrm{head}\,N`$。

### 証明

[T.oper_eq_dropLast_append](Cnf-ja.md#t-oper_eq_dropLast_append) より、ある $`R \in \mathrm{PairSeq}`$ について
$`N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R`$ である。
$`1 \lt \lvert N\rvert`$ より $`N`$ は少なくとも 2 要素をもち $`N = a :: b :: u`$ と書ける。
このとき

```math
\mathrm{dropLast}\,(a :: b :: u) = a :: \mathrm{dropLast}\,(b :: u)
```

であるから

```math
N[n] = a :: \bigl(\mathrm{dropLast}\,(b :: u) \mathbin{+\!\!+} R\bigr)
```

であり、$`\mathrm{head}\,(N[n]) = a = \mathrm{head}\,N`$ である。∎

<a id="t-translate_nil"></a>
## 定理: 空列の翻訳 (T.translate_nil)

### 定理

$`\mathrm{tr}\,()`$（[D.translate](Term-ja.md#d-translate)）は $`\mathsf{Z}`$（[D.Three](Term-ja.md#d-Three)）に等しい。

### 証明

$`\mathrm{tr}`$ の定義（D.translate）の第 1 式そのものである。∎

<a id="d-maxr1"></a>
## 定義: 行 1 の最大値 (D.maxr1)

$`S \in \mathrm{PairSeq}`$ に対し $`\mathrm{maxr}_1(S) \in \mathbb{N}`$ を、列の構成子に関する再帰で定める。

```math
\mathrm{maxr}_1(()) := 0,
\qquad
\mathrm{maxr}_1(c :: S) := \max\bigl(c_2,\ \mathrm{maxr}_1(S)\bigr) .
```

ここで $`c = (c_1, c_2)`$ である。再帰呼び出しの引数 $`S`$ は $`c :: S`$ の真の後部分列であり、
長さが真に小さいから、この定義は整合的である。

<a id="t-maxr1_cons"></a>
## 定理: 行 1 の最大値の再帰式 (T.maxr1_cons)

### 定理

$`c \in \mathbb{N} \times \mathbb{N}`$、$`S \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{maxr}_1(c :: S) = \max\bigl(c_2,\ \mathrm{maxr}_1(S)\bigr) .
```

### 証明

$`\mathrm{maxr}_1`$ の定義（D.maxr1）の第 2 式そのものであり、両辺は定義により同一の値である。∎

<a id="d-r1ok"></a>
## 定義: 行 1 の規律 (D.r1ok)

$`M \in \mathrm{PairSeq}`$ に対し、命題 $`\mathrm{r1ok}(M)`$ を次のものとして定める。

> 任意の $`j`$ について、$`j \lt \lvert M\rvert`$ かつ $`0 \lt M_{0,j}`$ ならば、
> 次の 4 条件をみたす $`k`$ が存在する。

```math
\begin{aligned}
&(1)\ k \lt j, \cr
&(2)\ M_{0,k} + 1 = M_{0,j}, \cr
&(3)\ \forall l\ \bigl(k \lt l \wedge l \lt j \to M_{0,j} \le M_{0,l}\bigr), \cr
&(4)\ M_{1,j} \le M_{1,k} + 1 .
\end{aligned}
```

条件 (1)〜(4) をみたす $`k`$ を、列 $`M`$ における第 $`j`$ 列の**証人**と呼ぶ。

<a id="t-diagSeq0_length"></a>
## 定理: 対角列の長さ (T.diagSeq0_length)

### 定理

任意の $`v \in \mathbb{N}`$ に対し $`\lvert \Delta_0^v\rvert = v + 1`$（[D.diagSeq](Pss-ja.md#d-diagSeq)）。

### 証明

$`\Delta_a^b`$ の定義（D.diagSeq）より
$`\Delta_0^v = ((0,0),(1,1),\dots,(v,v))`$ であり、その長さは $`v + 1 - 0`$、
すなわち $`v + 1`$ である。∎

<a id="t-diagSeq0_getD"></a>
## 定理: 対角列の成分 (T.diagSeq0_getD)

### 定理

任意の $`v, i \in \mathbb{N}`$ に対し、$`i \lt v + 1`$ ならば
$`\Delta_0^v\langle i\rangle = (i,i)`$。

### 証明

[T.diagSeq0_length](#t-diagSeq0_length) より $`\lvert \Delta_0^v\rvert = v+1`$ であり、
仮定 $`i \lt v+1`$ から添字 $`i`$ は範囲内である。よって $`M\langle i\rangle`$ の定義（D.entry）の
第 1 の場合が選ばれ、$`\Delta_0^v\langle i\rangle`$ は $`\Delta_0^v`$ の第 $`i`$ 要素である。
$`\Delta_a^b`$ の定義（D.diagSeq）より $`\Delta_0^v = ((0,0),(1,1),\dots,(v,v))`$ であるから、
その第 $`i`$ 要素は $`(i,i)`$ である。∎

<a id="t-r1ok_diagSeq"></a>
## 定理: 対角列は行 1 の規律をみたす (T.r1ok_diagSeq)

### 定理

任意の $`v \in \mathbb{N}`$ に対し $`\mathrm{r1ok}(\Delta_0^v)`$。

### 証明

$`j \lt \lvert \Delta_0^v\rvert`$ かつ $`0 \lt (\Delta_0^v)_{0,j}`$ とする。
[T.diagSeq0_length](#t-diagSeq0_length) より $`j \lt v+1`$ であり、
[T.diagSeq0_getD](#t-diagSeq0_getD) より $`\Delta_0^v\langle j\rangle = (j,j)`$、
したがって $`(\Delta_0^v)_{0,j} = j`$ である。仮定より $`0 \lt j`$。

証人として $`k := j - 1`$ を取る。$`0 \lt j`$ より $`j - 1 + 1 = j`$ であり、
$`j - 1 \lt j \lt v+1`$ であるから [T.diagSeq0_getD](#t-diagSeq0_getD) が $`j-1`$ にも使えて
$`\Delta_0^v\langle j-1\rangle = (j-1, j-1)`$ である。
$`\mathrm{r1ok}`$ の定義（D.r1ok）の 4 条件を確かめる。

**(1)** $`0 \lt j`$ より $`j - 1 \lt j`$。

**(2)** $`(\Delta_0^v)_{0,j-1} + 1 = (j-1) + 1 = j = (\Delta_0^v)_{0,j}`$。

**(3)** $`j - 1 \lt l`$ かつ $`l \lt j`$ をみたす $`l`$ を取ると、$`0 \lt j`$ より
$`j - 1 \lt l \lt j = (j-1) + 1`$ となり、そのような自然数 $`l`$ は存在しない。
よって前件が偽であり、条件は成り立つ。

**(4)** $`(\Delta_0^v)_{1,j} = j`$、$`(\Delta_0^v)_{1,j-1} + 1 = (j-1) + 1 = j`$ であるから
$`(\Delta_0^v)_{1,j} \le (\Delta_0^v)_{1,j-1} + 1`$。∎

<a id="t-getD_take"></a>
## 定理: 前部分列の成分 (T.getD_take)

### 定理

$`M \in \mathrm{PairSeq}`$、$`m, j \in \mathbb{N}`$ とする。$`j \lt m`$ ならば

```math
(\mathrm{take}_m M)\langle j\rangle = M\langle j\rangle .
```

### 証明

$`\mathrm{take}_m M`$ の第 $`j`$ 要素は、$`j \lt m`$ のとき $`M`$ の第 $`j`$ 要素であり、
$`M`$ の第 $`j`$ 要素が存在しないとき（$`j \ge \lvert M\rvert`$ のとき）は
$`\mathrm{take}_m M`$ の第 $`j`$ 要素も存在しない。すなわち $`j \lt m`$ のとき

```math
j \lt \lvert \mathrm{take}_m M\rvert \iff j \lt \lvert M\rvert
```

であり、そのとき両者の第 $`j`$ 要素は一致する。
$`M\langle j\rangle`$ の定義（D.entry）は、添字が範囲内なら第 $`j`$ 要素、範囲外なら
$`(0,0)`$ を返すものであったから、両辺は一致する。∎

<a id="t-r1ok_take"></a>
## 定理: 行 1 の規律は前部分列に遺伝する (T.r1ok_take)

### 定理

$`\mathrm{r1ok}(M)`$ ならば、任意の $`m \in \mathbb{N}`$ に対し
$`\mathrm{r1ok}(\mathrm{take}_m M)`$。

### 証明

$`j \lt \lvert \mathrm{take}_m M\rvert`$ かつ $`0 \lt (\mathrm{take}_m M)_{0,j}`$ とする。
$`\lvert \mathrm{take}_m M\rvert = \min(m, \lvert M\rvert)`$ であるから
$`j \lt m`$ かつ $`j \lt \lvert M\rvert`$ である。
[T.getD_take](#t-getD_take) より $`(\mathrm{take}_m M)\langle j\rangle = M\langle j\rangle`$ であり、
したがって $`0 \lt M_{0,j}`$ である。

仮定 $`\mathrm{r1ok}(M)`$ を $`j`$ に適用して、$`\mathrm{r1ok}`$ の定義（D.r1ok）の条件
(1)〜(4) をみたす $`k`$ を得る。この $`k`$ が $`\mathrm{take}_m M`$ における
第 $`j`$ 列の証人でもあることを示す。条件 (1) $`k \lt j`$ は共通である。
$`k \lt j \lt m`$ であるから [T.getD_take](#t-getD_take) が $`k`$ にも使えて
$`(\mathrm{take}_m M)\langle k\rangle = M\langle k\rangle`$ である。よって条件 (2) と (4) は
$`M`$ についての条件 (2), (4) そのものになる。
条件 (3) については、$`k \lt l`$ かつ $`l \lt j`$ をみたす $`l`$ に対し $`l \lt j \lt m`$
であるから [T.getD_take](#t-getD_take) より
$`(\mathrm{take}_m M)\langle l\rangle = M\langle l\rangle`$ であり、
$`M`$ についての条件 (3) がそのまま条件になる。∎

<a id="t-r1ok_dropLast"></a>
## 定理: 行 1 の規律は末尾除去に遺伝する (T.r1ok_dropLast)

### 定理

$`\mathrm{r1ok}(M)`$ ならば $`\mathrm{r1ok}(\mathrm{dropLast}\,M)`$。

### 証明

$`\mathrm{dropLast}\,M = \mathrm{take}_{\lvert M\rvert - 1} M`$ である
（どちらも $`M`$ の先頭 $`\lvert M\rvert - 1`$ 要素からなる列である）。
よって [T.r1ok_take](#t-r1ok_take) を $`m := \lvert M\rvert - 1`$ に適用すればよい。∎

<a id="t-getD_append_left"></a>
## 定理: 連結列の左側の成分 (T.getD_append_left)

### 定理

$`G, X \in \mathrm{PairSeq}`$、$`i \lt \lvert G\rvert`$ ならば
$`(G \mathbin{+\!\!+} X)\langle i\rangle = G\langle i\rangle`$。

### 証明

$`i \lt \lvert G\rvert`$ のとき、連結列 $`G \mathbin{+\!\!+} X`$ の第 $`i`$ 要素は
$`G`$ の第 $`i`$ 要素である。どちらの添字も範囲内であるから、
$`M\langle i\rangle`$ の定義（D.entry）の第 1 の場合が両辺で選ばれ、値は一致する。∎

<a id="t-getD_append_right"></a>
## 定理: 連結列の右側の成分 (T.getD_append_right)

### 定理

$`G, X \in \mathrm{PairSeq}`$、$`\lvert G\rvert \le i`$ ならば
$`(G \mathbin{+\!\!+} X)\langle i\rangle = X\langle i - \lvert G\rvert\rangle`$。

### 証明

$`\lvert G\rvert \le i`$ のとき、$`G \mathbin{+\!\!+} X`$ の第 $`i`$ 要素が存在することと
$`X`$ の第 $`i - \lvert G\rvert`$ 要素が存在することは同値であり
（$`i \lt \lvert G\rvert + \lvert X\rvert \iff i - \lvert G\rvert \lt \lvert X\rvert`$）、
存在するときは両者は同じ要素である。
よって $`M\langle i\rangle`$ の定義（D.entry）の場合分けが両辺で一致し、値も一致する。∎

<a id="t-index_decomp"></a>
## 定理: 添字の商剰余分解 (T.index_decomp)

### 定理

$`0 \lt L`$ かつ $`i \lt n L`$ ならば、$`k \lt n`$、$`q \lt L`$、$`i = k L + q`$ をみたす
$`k, q \in \mathbb{N}`$ が存在する。

### 証明

$`k := \lfloor i / L\rfloor`$、$`q := i \bmod L`$ と取る。

$`q \lt L`$：$`0 \lt L`$ であるから剰余は $`L`$ 未満である。

$`k \lt n`$：除法の等式 $`i = L\lfloor i/L\rfloor + (i \bmod L)`$ より
$`L\lfloor i/L\rfloor \le i`$ である。もし $`n \le \lfloor i/L\rfloor`$ ならば
$`nL \le L\lfloor i/L\rfloor \le i`$ となり、仮定 $`i \lt nL`$ に矛盾する。
よって $`\lfloor i/L\rfloor \lt n`$。

$`i = kL + q`$：除法の等式と乗法の可換性より

```math
i = L\lfloor i/L\rfloor + (i \bmod L) = \lfloor i/L\rfloor \cdot L + (i \bmod L) = kL + q . \qquad \blacksquare
```

<a id="t-copies_map_length"></a>
## 定理: 複製列の長さ (T.copies_map_length)

### 定理

以下、$`f : \mathbb{N} \to (\mathbb{N}\times\mathbb{N}) \to (\mathbb{N}\times\mathbb{N})`$、
$`B \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ に対し

```math
\mathrm{cp}(B, f, n) := \mathrm{map}(f_0, B) \mathbin{+\!\!+} \mathrm{map}(f_1, B)
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \mathrm{map}(f_{n-1}, B)
```

と書く。ここで $`f_k := f(k)`$ であり、$`\mathrm{map}(g, B)`$ は $`B`$ の各要素 $`x`$ を
$`g(x)`$ に置き換えた列である。$`n = 0`$ のとき $`\mathrm{cp}(B,f,0) = ()`$ である。
$`\mathrm{cp}(B,f,n+1)`$ は $`k = 0, 1, \dots, n`$ の各 $`k`$ に対する $`\mathrm{map}(f_k, B)`$ を
左から順に連結した列であり、その最後の 1 個を分離すると

```math
\mathrm{cp}(B,f,n+1) = \mathrm{cp}(B,f,n) \mathbin{+\!\!+} \mathrm{map}(f_n, B)
```

が成り立つ。このとき

```math
\lvert \mathrm{cp}(B,f,n)\rvert = n\,\lvert B\rvert .
```

### 証明

$`n`$ に関する帰納法。帰納法の述語は

```math
\Phi(n) :\equiv \lvert \mathrm{cp}(B,f,n)\rvert = n\,\lvert B\rvert .
```

- **基底段** $`n = 0`$：$`\mathrm{cp}(B,f,0) = ()`$ であり
  $`\lvert ()\rvert = 0 = 0 \cdot \lvert B\rvert`$。

**帰納段** $`n \to n+1`$。$`\Phi(n)`$、すなわち $`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert`$ を仮定する。
上に述べた分解と、連結列の長さが長さの和であること、および
$`\lvert \mathrm{map}(f_n, B)\rvert = \lvert B\rvert`$ より

```math
\lvert \mathrm{cp}(B,f,n+1)\rvert = n\lvert B\rvert + \lvert B\rvert = (n+1)\lvert B\rvert
```

である。よって $`\Phi(n+1)`$。∎

<a id="t-copies_map_getD"></a>
## 定理: 複製列の成分 (T.copies_map_getD)

### 定理

$`k \lt n`$ かつ $`q \lt \lvert B\rvert`$ ならば

```math
\mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle = f_k\bigl(B\langle q\rangle\bigr).
```

### 証明

$`n`$ に関する帰納法。帰納法の述語は

```math
\Phi(n) :\equiv \forall k, q,\ \bigl(k \lt n \wedge q \lt \lvert B\rvert\bigr)
  \to \mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle = f_k\bigl(B\langle q\rangle\bigr).
```

- **基底段** $`n = 0`$：$`k \lt 0`$ をみたす自然数 $`k`$ は存在しないから前件が偽であり、
  $`\Phi(0)`$ が成り立つ。

**帰納段** $`n \to n+1`$。$`\Phi(n)`$ を仮定する。
$`k \lt n+1`$、$`q \lt \lvert B\rvert`$ とし、[T.copies_map_length](#t-copies_map_length) の
分解 $`\mathrm{cp}(B,f,n+1) = \mathrm{cp}(B,f,n) \mathbin{+\!\!+} \mathrm{map}(f_n, B)`$ を使う。
[T.copies_map_length](#t-copies_map_length) より
$`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert`$ である。$`k`$ と $`n`$ の大小で場合分けする。

**(a) $`k \lt n`$ のとき。** $`q \lt \lvert B\rvert`$ より

```math
k\lvert B\rvert + q \lt k\lvert B\rvert + \lvert B\rvert = (k+1)\lvert B\rvert \le n\lvert B\rvert
```

である（最後の不等号は $`k + 1 \le n`$ による）。よって添字 $`k\lvert B\rvert + q`$ は
左側の $`\mathrm{cp}(B,f,n)`$ の範囲内にあり、[T.getD_append_left](#t-getD_append_left) より

```math
\mathrm{cp}(B,f,n+1)\bigl\langle k\lvert B\rvert + q\bigr\rangle
  = \mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle
```

である。これに帰納法の仮定 $`\Phi(n)`$ を適用して $`f_k(B\langle q\rangle)`$ を得る。

**(b) $`k = n`$ のとき。** 添字は $`n\lvert B\rvert + q`$ であり、
$`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert \le n\lvert B\rvert + q`$ であるから、
[T.getD_append_right](#t-getD_append_right) より

```math
\mathrm{cp}(B,f,n+1)\bigl\langle n\lvert B\rvert + q\bigr\rangle
  = \mathrm{map}(f_n, B)\bigl\langle (n\lvert B\rvert + q) - n\lvert B\rvert\bigr\rangle
  = \mathrm{map}(f_n, B)\langle q\rangle
```

である。$`q \lt \lvert B\rvert = \lvert \mathrm{map}(f_n,B)\rvert`$ であるから添字は範囲内であり、
$`\mathrm{map}(f_n,B)`$ の第 $`q`$ 要素は $`B`$ の第 $`q`$ 要素に $`f_n`$ を適用したもの、
すなわち $`f_n(B\langle q\rangle)`$ である。∎

<a id="d-copyExp"></a>
## 定義: 複製展開 (D.copyExp)

$`L \in \mathrm{PairSeq}`$、$`e \in \mathbb{N}`$ に対し、$`L`$ の各対の第 1 成分に
$`e`$ を足した列を $`L^{+e}`$（[D.shiftr0](Cnf-2-ja.md#d-shiftr0)）と書く。
$`G, B \in \mathrm{PairSeq}`$、$`d_0, n \in \mathbb{N}`$ に対し

```math
\mathrm{copyExp}(G,B,d_0,n) := G \mathbin{+\!\!+} \mathrm{cp}(B, f, n),
\qquad f_k(p) := (p_1 + k\,d_0,\ p_2)
```

と定める。すなわち

```math
\mathrm{copyExp}(G,B,d_0,n)
  = G \mathbin{+\!\!+} B^{+0\cdot d_0} \mathbin{+\!\!+} B^{+1\cdot d_0}
    \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}
```

である。$`G`$ を**前置部**、
$`B^{+0\cdot d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}`$ を**複製部**と呼ぶ。

<a id="t-copyExp_length"></a>
## 定理: 複製展開の長さ (T.copyExp_length)

### 定理

```math
\lvert \mathrm{copyExp}(G,B,d_0,n)\rvert = \lvert G\rvert + n\,\lvert B\rvert .
```

### 証明

$`\mathrm{copyExp}`$ の定義（D.copyExp）より
$`\mathrm{copyExp}(G,B,d_0,n) = G \mathbin{+\!\!+} \mathrm{cp}(B,f,n)`$ であり、
連結列の長さは長さの和であるから、その長さは
$`\lvert G\rvert + \lvert \mathrm{cp}(B,f,n)\rvert`$ である。
[T.copies_map_length](#t-copies_map_length) より
$`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert`$。∎

<a id="t-copyExp_getD_pre"></a>
## 定理: 複製展開の前置部の成分 (T.copyExp_getD_pre)

### 定理

$`i \lt \lvert G\rvert`$ ならば
$`\mathrm{copyExp}(G,B,d_0,n)\langle i\rangle = G\langle i\rangle`$。

### 証明

$`\mathrm{copyExp}`$ の定義（D.copyExp）より左辺は
$`(G \mathbin{+\!\!+} \mathrm{cp}(B,f,n))\langle i\rangle`$ であり、
[T.getD_append_left](#t-getD_append_left) を適用すればよい。∎

<a id="t-copyExp_getD_copy"></a>
## 定理: 複製展開の複製部の成分 (T.copyExp_getD_copy)

### 定理

$`k \lt n`$ かつ $`q \lt \lvert B\rvert`$ ならば

```math
\mathrm{copyExp}(G,B,d_0,n)\bigl\langle \lvert G\rvert + (k\lvert B\rvert + q)\bigr\rangle
  = \bigl(B_{0,q} + k\,d_0,\ B_{1,q}\bigr).
```

### 証明

$`\mathrm{copyExp}`$ の定義（D.copyExp）より左辺は
$`(G \mathbin{+\!\!+} \mathrm{cp}(B,f,n))\langle \lvert G\rvert + (k\lvert B\rvert + q)\rangle`$ である。
$`\lvert G\rvert \le \lvert G\rvert + (k\lvert B\rvert + q)`$ であるから
[T.getD_append_right](#t-getD_append_right) が使えて、これは

```math
\mathrm{cp}(B,f,n)\bigl\langle \bigl(\lvert G\rvert + (k\lvert B\rvert + q)\bigr) - \lvert G\rvert\bigr\rangle
  = \mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle
```

に等しい。[T.copies_map_getD](#t-copies_map_getD) より、これは
$`f_k(B\langle q\rangle)`$、すなわち $`\mathrm{copyExp}`$ の定義（D.copyExp）の
$`f_k(p) = (p_1 + k d_0, p_2)`$ を $`p := B\langle q\rangle`$ に適用した
$`(B_{0,q} + k d_0,\ B_{1,q})`$ に等しい。∎

<a id="t-hostM_getD_pre"></a>
## 定理: 連結列 $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ の前置部の成分 (T.hostM_getD_pre)

### 定理

$`G, B \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ とする。
$`i \lt \lvert G\rvert`$ ならば

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)\langle i\rangle = G\langle i\rangle .
```

### 証明

$`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell) = (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$ であり、
$`i \lt \lvert G\rvert \le \lvert G\rvert + \lvert B\rvert = \lvert G \mathbin{+\!\!+} B\rvert`$ であるから、
[T.getD_append_left](#t-getD_append_left) より左辺は
$`(G \mathbin{+\!\!+} B)\langle i\rangle`$ に等しい。
ふたたび $`i \lt \lvert G\rvert`$ に [T.getD_append_left](#t-getD_append_left) を適用して
$`G\langle i\rangle`$ を得る。∎

<a id="t-hostM_getD_blk"></a>
## 定理: 連結列 $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ のブロック部の成分 (T.hostM_getD_blk)

### 定理

$`q \lt \lvert B\rvert`$ ならば

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)\langle \lvert G\rvert + q\rangle = B\langle q\rangle .
```

### 証明

$`q \lt \lvert B\rvert`$ より
$`\lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert = \lvert G \mathbin{+\!\!+} B\rvert`$ であるから、
[T.getD_append_left](#t-getD_append_left) より左辺は
$`(G \mathbin{+\!\!+} B)\langle \lvert G\rvert + q\rangle`$ に等しい。
$`\lvert G\rvert \le \lvert G\rvert + q`$ であるから
[T.getD_append_right](#t-getD_append_right) が使えて、これは
$`B\langle (\lvert G\rvert + q) - \lvert G\rvert\rangle = B\langle q\rangle`$ に等しい。∎

<a id="t-hostM_length"></a>
## 定理: 連結列 $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ の長さ (T.hostM_length)

### 定理

```math
\bigl\lvert G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr\rvert = \lvert G\rvert + \lvert B\rvert + 1 .
```

### 証明

連結列の長さは長さの和であり、$`\lvert (\ell)\rvert = 1`$ であるから

```math
\bigl\lvert (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)\bigr\rvert
  = \bigl(\lvert G\rvert + \lvert B\rvert\bigr) + 1 . \qquad \blacksquare
```

<a id="t-r1ok_copyExp"></a>
## 定理: 複製展開における行 1 の規律 (T.r1ok_copyExp)

### 定理

$`G, B \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、$`n, d_0 \in \mathbb{N}`$ とし、
$`E := \mathrm{copyExp}(G,B,d_0,n)`$ とおく。次の 2 つを仮定する。

```math
\text{(hr)}\quad \mathrm{r1ok}\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr),
```

```math
\begin{aligned}
\text{(hmin)}\quad &\forall k, q,\
  \Bigl(0 \lt k \wedge k \lt n \wedge q \lt \lvert B\rvert
  \wedge \bigl(\forall r \lt q,\ B_{0,q} \le B_{0,r}\bigr)
  \wedge 0 \lt B_{0,q} + k d_0\Bigr) \to \cr
  &\quad \exists p,\
  \Bigl(p \lt \lvert G\rvert + (k\lvert B\rvert + q)
  \ \wedge\ E_{0,p} + 1 = B_{0,q} + k d_0 \cr
  &\qquad \wedge\ \bigl(\forall l,\ p \lt l \wedge l \lt \lvert G\rvert + (k\lvert B\rvert + q)
     \to B_{0,q} + k d_0 \le E_{0,l}\bigr) \cr
  &\qquad \wedge\ B_{1,q} \le E_{1,p} + 1\Bigr).
\end{aligned}
```

このとき $`\mathrm{r1ok}(E)`$ が成り立つ。

### 証明

$`H := G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ とおく。
$`j \lt \lvert E\rvert`$ かつ $`0 \lt E_{0,j}`$ とする。
[T.copyExp_length](#t-copyExp_length) より
$`j \lt \lvert G\rvert + n\lvert B\rvert`$ である。$`j`$ の位置で場合分けする。

**(A) $`j \lt \lvert G\rvert + \lvert B\rvert`$ のとき。**
まず次を示す。

```math
(\ast)\qquad \forall i \le j,\ E\langle i\rangle = H\langle i\rangle .
```

$`i \le j`$ を取る。

**(A-1) $`i \lt \lvert G\rvert`$ のとき。**
[T.copyExp_getD_pre](#t-copyExp_getD_pre) より $`E\langle i\rangle = G\langle i\rangle`$、
[T.hostM_getD_pre](#t-hostM_getD_pre) より $`H\langle i\rangle = G\langle i\rangle`$ であり、
両辺は一致する。

**(A-2) $`\lvert G\rvert \le i`$ のとき。**
$`i \le j \lt \lvert G\rvert + \lvert B\rvert`$ より $`i - \lvert G\rvert \lt \lvert B\rvert`$ である。
また $`0 \lt n`$ である。実際、$`n = 0`$ とすると
$`j \lt \lvert G\rvert + 0 \cdot \lvert B\rvert = \lvert G\rvert`$ となるが、
$`\lvert G\rvert \le i \le j`$ に反する。
$`i = \lvert G\rvert + (0 \cdot \lvert B\rvert + (i - \lvert G\rvert))`$ であるから、
[T.copyExp_getD_copy](#t-copyExp_getD_copy) を $`k := 0`$、$`q := i - \lvert G\rvert`$ に適用して

```math
E\langle i\rangle
  = \bigl(B_{0,\,i - \lvert G\rvert} + 0 \cdot d_0,\ B_{1,\,i - \lvert G\rvert}\bigr)
  = B\langle i - \lvert G\rvert\rangle
```

を得る。他方 $`i = \lvert G\rvert + (i - \lvert G\rvert)`$ であるから
[T.hostM_getD_blk](#t-hostM_getD_blk) より
$`H\langle i\rangle = B\langle i - \lvert G\rvert\rangle`$ である。よって両辺は一致する。

これで $`(\ast)`$ が示された。[T.hostM_length](#t-hostM_length) より
$`\lvert H\rvert = \lvert G\rvert + \lvert B\rvert + 1`$ であり、
$`j \lt \lvert G\rvert + \lvert B\rvert \lt \lvert H\rvert`$ である。
$`(\ast)`$ を $`i := j`$ に用いると $`0 \lt H_{0,j}`$ である。
仮定 (hr) を $`j`$ に適用して、$`H`$ における第 $`j`$ 列の証人 $`p`$ を得る。
すなわち $`p \lt j`$、$`H_{0,p} + 1 = H_{0,j}`$、
$`\forall l\ (p \lt l \wedge l \lt j \to H_{0,j} \le H_{0,l})`$、
$`H_{1,j} \le H_{1,p} + 1`$ である。
この $`p`$ が $`E`$ における第 $`j`$ 列の証人でもあることを示す。

条件 (1) $`p \lt j`$ はそのままである。
$`p \lt j`$ より $`p \le j`$ であるから $`(\ast)`$ が $`p`$ に使え、
$`E\langle p\rangle = H\langle p\rangle`$、$`E\langle j\rangle = H\langle j\rangle`$ である。
よって条件 (2) $`E_{0,p} + 1 = E_{0,j}`$ と条件 (4) $`E_{1,j} \le E_{1,p} + 1`$ は
$`H`$ についての等式・不等式そのものになる。
条件 (3) については、$`p \lt l`$ かつ $`l \lt j`$ をみたす $`l`$ に対し $`l \le j`$ であるから
$`(\ast)`$ より $`E\langle l\rangle = H\langle l\rangle`$ であり、
$`H`$ についての条件がそのまま $`E_{0,j} \le E_{0,l}`$ を与える。

**(B) $`\lvert G\rvert + \lvert B\rvert \le j`$ のとき。**
まず $`0 \lt \lvert B\rvert`$ である。実際 $`\lvert B\rvert = 0`$ とすると
$`j \lt \lvert G\rvert + n \cdot 0 = \lvert G\rvert`$ となるが、
$`\lvert G\rvert \le \lvert G\rvert + \lvert B\rvert \le j`$ に反する。
$`j \lt \lvert G\rvert + n\lvert B\rvert`$ より $`j - \lvert G\rvert \lt n\lvert B\rvert`$ であるから、
[T.index_decomp](#t-index_decomp) より $`k \lt n`$、$`q \lt \lvert B\rvert`$、
$`j - \lvert G\rvert = k\lvert B\rvert + q`$ をみたす $`k, q`$ が存在する。
$`\lvert G\rvert \le j`$ であるから $`j = \lvert G\rvert + (k\lvert B\rvert + q)`$ である。
さらに $`0 \lt k`$ である。実際 $`k = 0`$ とすると
$`j = \lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert`$ となり、
場合 (B) の仮定に反する。
[T.copyExp_getD_copy](#t-copyExp_getD_copy) より

```math
E\langle j\rangle = \bigl(B_{0,q} + k d_0,\ B_{1,q}\bigr),
```

とくに $`0 \lt B_{0,q} + k d_0`$ である。$`q`$ より前の位置の行 $`0`$ の値との大小で場合分けする。

**(B-1) $`\forall r \lt q,\ B_{0,q} \le B_{0,r}`$ のとき。**
仮定 (hmin) を $`k, q`$ に適用すればよい。得られる $`p`$ が条件 (1)〜(4) を
みたすことは (hmin) の結論そのものである（$`E_{0,j} = B_{0,q} + k d_0`$、
$`E_{1,j} = B_{1,q}`$ による）。

**(B-2) ある $`r \lt q`$ が $`B_{0,r} \lt B_{0,q}`$ をみたすとき。**
$`0 \le B_{0,r} \lt B_{0,q}`$ より $`0 \lt B_{0,q}`$ である。
[T.hostM_length](#t-hostM_length) より
$`\lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$ であり、
[T.hostM_getD_blk](#t-hostM_getD_blk) より $`H\langle \lvert G\rvert + q\rangle = B\langle q\rangle`$、
とくに $`0 \lt H_{0,\lvert G\rvert + q}`$ である。
仮定 (hr) を添字 $`\lvert G\rvert + q`$ に適用して、$`H`$ における
第 $`\lvert G\rvert + q`$ 列の証人 $`p`$ を得る。すなわち

```math
\begin{aligned}
&p \lt \lvert G\rvert + q, \cr
&H_{0,p} + 1 = H_{0,\lvert G\rvert + q} = B_{0,q}, \cr
&\forall l\ \bigl(p \lt l \wedge l \lt \lvert G\rvert + q \to B_{0,q} \le H_{0,l}\bigr), \cr
&B_{1,q} = H_{1,\lvert G\rvert + q} \le H_{1,p} + 1 .
\end{aligned}
```

ここで $`\lvert G\rvert + r \le p`$ である。実際 $`p \lt \lvert G\rvert + r`$ とすると、
$`r \lt q`$ より $`\lvert G\rvert + r \lt \lvert G\rvert + q`$ であるから第 3 の条件を
$`l := \lvert G\rvert + r`$ に適用でき、[T.hostM_getD_blk](#t-hostM_getD_blk) より
$`B_{0,q} \le H_{0,\lvert G\rvert + r} = B_{0,r}`$ となって $`B_{0,r} \lt B_{0,q}`$ に矛盾する。

したがって $`r' := p - \lvert G\rvert`$ とおけば $`p = \lvert G\rvert + r'`$ であり、
$`p \lt \lvert G\rvert + q`$ より $`r' \lt q`$、よって $`r' \lt \lvert B\rvert`$ である。
[T.hostM_getD_blk](#t-hostM_getD_blk) より $`H\langle p\rangle = B\langle r'\rangle`$ であるから、
上の条件は

```math
B_{0,r'} + 1 = B_{0,q}, \qquad B_{1,q} \le B_{1,r'} + 1
```

と書き直せる。$`E`$ における第 $`j`$ 列の証人として
$`p^{*} := \lvert G\rvert + (k\lvert B\rvert + r')`$ を取る。
$`\mathrm{r1ok}`$ の定義（D.r1ok）の 4 条件を確かめる。

**(1)** $`r' \lt q`$ より
$`p^{*} = \lvert G\rvert + (k\lvert B\rvert + r') \lt \lvert G\rvert + (k\lvert B\rvert + q) = j`$。

**(2)** [T.copyExp_getD_copy](#t-copyExp_getD_copy) を $`k`$, $`r'`$ に適用して
$`E_{0,p^{*}} = B_{0,r'} + k d_0`$ である。よって

```math
E_{0,p^{*}} + 1 = B_{0,r'} + k d_0 + 1 = (B_{0,r'} + 1) + k d_0 = B_{0,q} + k d_0 = E_{0,j} .
```

**(3)** $`p^{*} \lt l`$ かつ $`l \lt j`$ をみたす $`l`$ を取る。
$`\lvert G\rvert + k\lvert B\rvert \le p^{*} \lt l \lt \lvert G\rvert + (k\lvert B\rvert + q)`$ であるから、
$`rr := l - \lvert G\rvert - k\lvert B\rvert`$ とおくと
$`l = \lvert G\rvert + (k\lvert B\rvert + rr)`$、$`r' \lt rr`$、$`rr \lt q`$ である。
とくに $`rr \lt \lvert B\rvert`$ であるから
[T.copyExp_getD_copy](#t-copyExp_getD_copy) より $`E_{0,l} = B_{0,rr} + k d_0`$ である。
他方 $`p = \lvert G\rvert + r' \lt \lvert G\rvert + rr \lt \lvert G\rvert + q`$ であるから、
$`H`$ についての第 3 の条件を $`l := \lvert G\rvert + rr`$ に適用し、
[T.hostM_getD_blk](#t-hostM_getD_blk) より $`B_{0,q} \le B_{0,rr}`$ を得る。よって

```math
E_{0,j} = B_{0,q} + k d_0 \le B_{0,rr} + k d_0 = E_{0,l} .
```

**(4)** [T.copyExp_getD_copy](#t-copyExp_getD_copy) より
$`E_{1,p^{*}} = B_{1,r'}`$ であり、$`E_{1,j} = B_{1,q} \le B_{1,r'} + 1 = E_{1,p^{*}} + 1`$。∎
