[← README](README.md) ｜ Column [1](Column.md) [2](Column-2.md) **3** [4](Column-4.md)

<a id="t-getD_mem"></a>
## 定理: 範囲内の成分は要素である (T.getD_mem)

### 定理

$`L`$ を対の列、$`i \lt \lvert L\rvert`$ とすると $`L\langle i\rangle \in L`$（[D.entry](Pss.md#d-entry)）。

### 証明

$`i \lt \lvert L\rvert`$ であるから $`L\langle i\rangle`$ の定義（D.entry）の第 1 の場合が選ばれ、
$`L\langle i\rangle`$ は $`L`$ の第 $`i`$ 要素である。列の第 $`i`$ 要素は
（$`i`$ が範囲内である限り）その列の要素である。∎

<a id="t-dominated_PM_zero"></a>
## 定理: 支配されたブロックで行 0 が最小になる位置は先頭に限る (T.dominated_PM_zero)

### 定理

$`v_0, w_0 \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$（[D.PairSeq](Pss.md#d-PairSeq)）、$`q \in \mathbb{N}`$ とし、
$`B := (v_0,w_0) :: R`$ とおく。次の 3 つを仮定する。

```math
\begin{aligned}
&\text{(hdom)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hq)}\quad q \lt \lvert B\rvert, \cr
&\text{(hPM)}\quad \forall r \lt q,\ B_{0,q} \le B_{0,r} .
\end{aligned}
```

このとき $`q = 0`$。

### 証明

$`q \ne 0`$ と仮定して矛盾を導く。$`q \ne 0`$ より $`q = q' + 1`$ と書ける。
$`\lvert B\rvert = \lvert R\rvert + 1`$ であるから (hq) より $`q' \lt \lvert R\rvert`$ である。
[T.getD_mem](#t-getD_mem) より $`R\langle q'\rangle \in R`$ であり、(hdom) より

```math
v_0 \lt R_{0,q'} .
```

他方 (hPM) を $`r := 0`$ に適用すると（$`0 \lt q`$ である）$`B_{0,q} \le B_{0,0}`$ を得る。
$`B = (v_0,w_0) :: R`$ であるから $`B\langle 0\rangle = (v_0,w_0)`$、すなわち $`B_{0,0} = v_0`$ であり、
また $`B\langle q' + 1\rangle = R\langle q'\rangle`$ であるから $`B_{0,q} = R_{0,q'}`$ である。
よって $`R_{0,q'} \le v_0`$ となり、$`v_0 \lt R_{0,q'}`$ に矛盾する。∎

<a id="t-r1ok_min_d0zero"></a>
## 定理: 複製部の証人（$`d_0 = 0`$ の場合） (T.r1ok_min_d0zero)

### 定理

$`G, R \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、$`n, v_0, w_0 \in \mathbb{N}`$、
$`B := (v_0,w_0) :: R`$、$`E := \mathrm{copyExp}(G,B,0,n)`$（[D.copyExp](Column-2.md#d-copyExp)）とおく。次を仮定する。

```math
\begin{aligned}
&\text{(hdom)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hr)}\quad \mathrm{r1ok}\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr), \cr
&\text{(hk1)}\quad 0 \lt k, \qquad
 \text{(hk)}\quad k \lt n, \qquad
 \text{(hq)}\quad q \lt \lvert B\rvert, \cr
&\text{(hPM)}\quad \forall r \lt q,\ B_{0,q} \le B_{0,r}, \cr
&\text{(hpos)}\quad 0 \lt B_{0,q} + k \cdot 0 .
\end{aligned}
```

（$`\mathrm{r1ok}`$ [D.r1ok](Column-2.md#d-r1ok)）

このとき次をみたす $`p`$ が存在する。

```math
\begin{aligned}
&p \lt \lvert G\rvert + (k\lvert B\rvert + q), \cr
&E_{0,p} + 1 = B_{0,q} + k \cdot 0, \cr
&\forall l,\ \bigl(p \lt l \wedge l \lt \lvert G\rvert + (k\lvert B\rvert + q)\bigr)
   \to B_{0,q} + k \cdot 0 \le E_{0,l}, \cr
&B_{1,q} \le E_{1,p} + 1 .
\end{aligned}
```

### 証明

$`H := G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ とおく。
[T.dominated_PM_zero](#t-dominated_PM_zero) を (hdom), (hq), (hPM) に適用して $`q = 0`$ を得る。
以下 $`q = 0`$ とする。$`B\langle 0\rangle = (v_0,w_0)`$ であるから $`B_{0,0} = v_0`$、$`B_{1,0} = w_0`$ であり、
$`k \cdot 0 = 0`$ であるから (hpos) は $`0 \lt v_0`$ を与える。

$`0 \lt \lvert B\rvert`$ であるから [T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) を $`q := 0`$ に適用して
$`H\langle \lvert G\rvert\rangle = B\langle 0\rangle = (v_0,w_0)`$ を得る。
[T.hostM_length](Column-2.md#t-hostM_length) より
$`\lvert G\rvert \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$ であり、
$`H_{0,\lvert G\rvert} = v_0 \gt 0`$ である。
仮定 (hr) を添字 $`\lvert G\rvert`$ に適用して、$`H`$ における第 $`\lvert G\rvert`$ 列の証人 $`p`$ を得る。
すなわち

```math
\begin{aligned}
&p \lt \lvert G\rvert, \cr
&H_{0,p} + 1 = v_0, \cr
&\forall l\ \bigl(p \lt l \wedge l \lt \lvert G\rvert \to v_0 \le H_{0,l}\bigr), \cr
&w_0 \le H_{1,p} + 1 .
\end{aligned}
```

$`p \lt \lvert G\rvert`$ であるから [T.hostM_getD_pre](Column-2.md#t-hostM_getD_pre) より
$`H\langle p\rangle = G\langle p\rangle`$ であり、上の 2 番目と 4 番目は

```math
G_{0,p} + 1 = v_0, \qquad w_0 \le G_{1,p} + 1
```

となる。この $`p`$ が求めるものであることを示す。
[T.copyExp_getD_pre](Column-2.md#t-copyExp_getD_pre) より $`E\langle p\rangle = G\langle p\rangle`$ である。

**第 1 の条件。** $`p \lt \lvert G\rvert \le \lvert G\rvert + (k\lvert B\rvert + 0)`$。

**第 2 の条件。** $`E_{0,p} + 1 = G_{0,p} + 1 = v_0 = v_0 + k \cdot 0 = B_{0,0} + k \cdot 0`$。

**第 3 の条件。** $`p \lt l`$ かつ $`l \lt \lvert G\rvert + (k\lvert B\rvert + 0)`$ をみたす $`l`$ を取る。
示すべきは $`v_0 + k \cdot 0 \le E_{0,l}`$、すなわち $`v_0 \le E_{0,l}`$ である。$`l`$ の位置で場合分けする。

**(a) $`l \lt \lvert G\rvert`$ のとき。**
[T.copyExp_getD_pre](Column-2.md#t-copyExp_getD_pre) より $`E\langle l\rangle = G\langle l\rangle`$ であり、
上の 3 番目の条件と [T.hostM_getD_pre](Column-2.md#t-hostM_getD_pre) より
$`v_0 \le H_{0,l} = G_{0,l} = E_{0,l}`$。

**(b) $`\lvert G\rvert \le l`$ のとき。**
(hk) より $`k \le n`$ であるから $`k\lvert B\rvert \le n\lvert B\rvert`$ であり、
$`l \lt \lvert G\rvert + k\lvert B\rvert`$ から $`l - \lvert G\rvert \lt n\lvert B\rvert`$ である。
$`0 \lt \lvert B\rvert`$ であるから [T.index_decomp](Column-2.md#t-index_decomp) より
$`k' \lt n`$、$`r \lt \lvert B\rvert`$、$`l - \lvert G\rvert = k'\lvert B\rvert + r`$ をみたす $`k', r`$ が
存在し、$`l = \lvert G\rvert + (k'\lvert B\rvert + r)`$ である。
[T.copyExp_getD_copy](Column-2.md#t-copyExp_getD_copy) より
$`E_{0,l} = B_{0,r} + k' \cdot 0 = B_{0,r}`$ である。
$`v_0 \le B_{0,r}`$ を $`r`$ で場合分けして示す。

- $`r = 0`$ のとき。$`B_{0,0} = v_0`$ であるから $`v_0 \le v_0`$。
- $`r = r' + 1`$ のとき。$`B\langle r' + 1\rangle = R\langle r'\rangle`$ であり、
  $`r \lt \lvert B\rvert = \lvert R\rvert + 1`$ より $`r' \lt \lvert R\rvert`$ であるから
  [T.getD_mem](#t-getD_mem) より $`R\langle r'\rangle \in R`$、
  (hdom) より $`v_0 \lt R_{0,r'} = B_{0,r}`$。

**第 4 の条件。** $`B_{1,0} = w_0 \le G_{1,p} + 1 = E_{1,p} + 1`$。∎

<a id="t-r1ok_min_d0pos"></a>
## 定理: 複製部の証人（$`0 \lt d_0`$ の場合） (T.r1ok_min_d0pos)

### 定理

$`G, R \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、$`n, v_0, w_0, d_0 \in \mathbb{N}`$、
$`B := (v_0,w_0) :: R`$、$`E := \mathrm{copyExp}(G,B,d_0,n)`$ とおく。次を仮定する。

```math
\begin{aligned}
&\text{(hdom)}\quad     &&\forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hd0)}\quad      &&0 \lt d_0, \cr
&\text{(hlp)}\quad      &&\ell_1 = v_0 + d_0, \cr
&\text{(hstep)}\quad    &&\forall r,\ r + 1 \lt \lvert B\rvert \to B_{0,r+1} \le B_{0,r} + 1, \cr
&\text{(hlpstep)}\quad  &&\ell_1 \le B_{0,\lvert B\rvert - 1} + 1, \cr
&\text{(hclimb)}\quad   &&\forall r' \lt \lvert B\rvert,\
   \Bigl(B_{0,r'} = v_0 + d_0 - 1 \cr
& &&\qquad \wedge \bigl(\forall rr,\ r' \lt rr \wedge rr \lt \lvert B\rvert
   \to v_0 + d_0 \le B_{0,rr}\bigr)\Bigr) \cr
& &&\qquad \to w_0 \le B_{1,r'} + 1, \cr
&\text{(hk1)}\quad      &&0 \lt k, \qquad
 \text{(hk)}\quad k \lt n, \qquad
 \text{(hq)}\quad q \lt \lvert B\rvert, \cr
&\text{(hPM)}\quad      &&\forall r \lt q,\ B_{0,q} \le B_{0,r}, \cr
&\text{(hpos)}\quad     &&0 \lt B_{0,q} + k d_0 .
\end{aligned}
```

このとき次をみたす $`p`$ が存在する。

```math
\begin{aligned}
&p \lt \lvert G\rvert + (k\lvert B\rvert + q), \cr
&E_{0,p} + 1 = B_{0,q} + k d_0, \cr
&\forall l,\ \bigl(p \lt l \wedge l \lt \lvert G\rvert + (k\lvert B\rvert + q)\bigr)
   \to B_{0,q} + k d_0 \le E_{0,l}, \cr
&B_{1,q} \le E_{1,p} + 1 .
\end{aligned}
```

### 証明

[T.dominated_PM_zero](#t-dominated_PM_zero) を (hdom), (hq), (hPM) に適用して $`q = 0`$ を得る。
以下 $`q = 0`$ とする。$`B = (v_0,w_0) :: R`$ であるから
$`0 \lt \lvert B\rvert`$ であり $`B\langle 0\rangle = (v_0,w_0)`$、すなわち
$`B_{0,0} = v_0`$、$`B_{1,0} = w_0`$ である。

**証人の候補。** 述語 $`P`$ を

```math
P(r) :\equiv B_{0,r} \le v_0 + d_0 - 1
```

で定める。(hd0) より $`d_0 \ge 1`$ であるから $`v_0 \le v_0 + d_0 - 1`$ であり、
$`B_{0,0} = v_0`$ であるから $`P(0)`$ が成り立つ。
集合 $`\{\, r \le \lvert B\rvert - 1 \mid P(r)\,\}`$ は $`0`$ を含むので空でなく、
$`\lvert B\rvert - 1`$ で上に有界であるから最大元をもつ。それを $`r'`$ とおく。すなわち

```math
P(r'), \qquad r' \le \lvert B\rvert - 1, \qquad
\forall rr,\ \bigl(r' \lt rr \wedge rr \le \lvert B\rvert - 1\bigr) \to \neg P(rr) .
```

$`0 \lt \lvert B\rvert`$ より $`r' \lt \lvert B\rvert`$ である。
また $`0 \lt \lvert B\rvert`$ より $`rr \lt \lvert B\rvert`$ と $`rr \le \lvert B\rvert - 1`$ は同値である。
$`\neg P(rr)`$ は $`v_0 + d_0 - 1 \lt B_{0,rr}`$ のことであり、$`d_0 \ge 1`$ より
$`(v_0 + d_0 - 1) + 1 = v_0 + d_0`$ であるから、これは $`v_0 + d_0 \le B_{0,rr}`$ と同値である。したがって

```math
(\dagger)\qquad \forall rr,\ \bigl(r' \lt rr \wedge rr \lt \lvert B\rvert\bigr)
  \to v_0 + d_0 \le B_{0,rr} .
```

**証人における行 0 の値。** $`B_{0,r'} = v_0 + d_0 - 1`$ を示す。
$`P(r')`$ より $`B_{0,r'} \le v_0 + d_0 - 1`$ である。逆向きを $`r'`$ と $`\lvert B\rvert - 1`$ の
大小で場合分けして示す。

**(a) $`r' \lt \lvert B\rvert - 1`$ のとき。**
$`r' \lt r' + 1 \le \lvert B\rvert - 1`$ であるから $`\neg P(r'+1)`$、すなわち
$`v_0 + d_0 - 1 \lt B_{0,r'+1}`$ である。また $`r' + 1 \lt \lvert B\rvert`$ であるから
(hstep) より $`B_{0,r'+1} \le B_{0,r'} + 1`$ である。よって

```math
v_0 + d_0 - 1 \lt B_{0,r'} + 1,
```

すなわち $`v_0 + d_0 - 1 \le B_{0,r'}`$。

**(b) $`r' = \lvert B\rvert - 1`$ のとき。**
(hlp) と (hlpstep) より $`v_0 + d_0 = \ell_1 \le B_{0,\lvert B\rvert - 1} + 1 = B_{0,r'} + 1`$ であり、
$`v_0 + d_0 - 1 \le B_{0,r'}`$。

いずれの場合も $`v_0 + d_0 - 1 \le B_{0,r'}`$ であり、上界と合わせて

```math
(\ddagger)\qquad B_{0,r'} = v_0 + d_0 - 1 .
```

**乗法の書き換え。** (hk1) より $`k \ge 1`$ であるから $`k = (k-1) + 1`$ と書け、

```math
k\lvert B\rvert = (k-1)\lvert B\rvert + \lvert B\rvert, \qquad
k d_0 = (k-1) d_0 + d_0
```

である。また (hk) より $`k - 1 \lt n`$ である。

**証人。** $`p^{*} := \lvert G\rvert + \bigl((k-1)\lvert B\rvert + r'\bigr)`$ を取る。
$`k - 1 \lt n`$ と $`r' \lt \lvert B\rvert`$ により
[T.copyExp_getD_copy](Column-2.md#t-copyExp_getD_copy) が使えて

```math
E\langle p^{*}\rangle = \bigl(B_{0,r'} + (k-1)d_0,\ B_{1,r'}\bigr)
```

である。4 つの条件を確かめる。

**第 1 の条件。** $`r' \lt \lvert B\rvert`$ より
$`(k-1)\lvert B\rvert + r' \lt (k-1)\lvert B\rvert + \lvert B\rvert = k\lvert B\rvert`$ であるから
$`p^{*} \lt \lvert G\rvert + (k\lvert B\rvert + 0)`$。

**第 2 の条件。** $`(\ddagger)`$ と $`d_0 \ge 1`$ より

```math
E_{0,p^{*}} + 1 = (v_0 + d_0 - 1) + (k-1)d_0 + 1 = v_0 + d_0 + (k-1)d_0 = v_0 + k d_0
  = B_{0,0} + k d_0 .
```

**第 3 の条件。** $`p^{*} \lt l`$ かつ $`l \lt \lvert G\rvert + (k\lvert B\rvert + 0)`$ をみたす $`l`$ を取る。
$`\lvert G\rvert \le p^{*} \lt l`$ である。(hk) より $`k\lvert B\rvert \le n\lvert B\rvert`$ であるから
$`l - \lvert G\rvert \lt k\lvert B\rvert \le n\lvert B\rvert`$ であり、
[T.index_decomp](Column-2.md#t-index_decomp) より $`k'' \lt n`$、$`rr \lt \lvert B\rvert`$、
$`l - \lvert G\rvert = k''\lvert B\rvert + rr`$ をみたす $`k'', rr`$ が存在する。
$`k'' = k - 1`$ であることを三分律で示す。

- $`k'' \lt k - 1`$ とすると $`k'' + 1 \le k - 1`$ であるから
  $`(k''+1)\lvert B\rvert \le (k-1)\lvert B\rvert`$、すなわち
  $`k''\lvert B\rvert + \lvert B\rvert \le (k-1)\lvert B\rvert`$ である。
  $`rr \lt \lvert B\rvert`$ より
  $`l - \lvert G\rvert = k''\lvert B\rvert + rr \lt (k-1)\lvert B\rvert \le (k-1)\lvert B\rvert + r'`$
  となり、$`p^{*} \lt l`$ に矛盾する。
- $`k - 1 \lt k''`$ とすると $`k \le k''`$ であるから $`k\lvert B\rvert \le k''\lvert B\rvert`$ であり、
  $`l - \lvert G\rvert = k''\lvert B\rvert + rr \ge k\lvert B\rvert`$ となって
  $`l - \lvert G\rvert \lt k\lvert B\rvert`$ に矛盾する。

よって $`k'' = k - 1`$ である。すると $`p^{*} \lt l`$ は
$`(k-1)\lvert B\rvert + r' \lt (k-1)\lvert B\rvert + rr`$、すなわち $`r' \lt rr`$ を与える。
[T.copyExp_getD_copy](Column-2.md#t-copyExp_getD_copy) より
$`E_{0,l} = B_{0,rr} + (k-1)d_0`$ であり、$`(\dagger)`$ より $`v_0 + d_0 \le B_{0,rr}`$ であるから

```math
B_{0,0} + k d_0 = v_0 + k d_0 = (v_0 + d_0) + (k-1)d_0 \le B_{0,rr} + (k-1)d_0 = E_{0,l} .
```

**第 4 の条件。** $`E_{1,p^{*}} = B_{1,r'}`$ であるから、示すべきは
$`B_{1,0} = w_0 \le B_{1,r'} + 1`$ である。これは (hclimb) を $`r'`$ に適用したものであり、
その前提は $`r' \lt \lvert B\rvert`$、$`(\ddagger)`$、$`(\dagger)`$ で与えられている。∎

<a id="t-hostM_getD_lp"></a>
## 定理: 連結列 $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ の末尾の成分 (T.hostM_getD_lp)

### 定理

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)
  \bigl\langle \lvert G\rvert + \lvert B\rvert\bigr\rangle = \ell .
```

### 証明

$`\lvert G \mathbin{+\!\!+} B\rvert = \lvert G\rvert + \lvert B\rvert`$ であるから
$`\lvert G \mathbin{+\!\!+} B\rvert \le \lvert G\rvert + \lvert B\rvert`$ であり、
[T.getD_append_right](Column-2.md#t-getD_append_right) を $`G := G \mathbin{+\!\!+} B`$、$`X := (\ell)`$ に適用して

```math
\bigl((G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)\bigr)\bigl\langle \lvert G\rvert + \lvert B\rvert\bigr\rangle
  = (\ell)\bigl\langle (\lvert G\rvert + \lvert B\rvert) - (\lvert G\rvert + \lvert B\rvert)\bigr\rangle
  = (\ell)\langle 0\rangle
```

を得る。$`0 \lt 1 = \lvert (\ell)\rvert`$ であるから $`(\ell)\langle 0\rangle = \ell`$ である。∎

<a id="t-r1ok_Pred"></a>
## 定理: 行 1 の規律は前者に遺伝する (T.r1ok_Pred)

### 定理

$`\mathrm{r1ok}(M)`$ ならば $`\mathrm{r1ok}(\mathrm{Pred}\,M)`$（[D.Pred](Pss.md#d-Pred)）。

### 証明

$`\mathrm{Pred}`$ の定義（D.Pred）の場合分けによる。

- $`\lvert M\rvert \le 1`$ のとき。$`\mathrm{Pred}\,M = M`$ であり、仮定そのものである。
- $`\lvert M\rvert \ge 2`$ のとき。$`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ であり、
  [T.r1ok_dropLast](Column-2.md#t-r1ok_dropLast) を適用すればよい。∎

<a id="t-climb_bound"></a>
## 定理: ブロック先頭の行 1 の値の上界 (T.climb_bound)

### 定理

$`M, G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ とし、
$`B := (v_0,w_0) :: R`$ とおく。次を仮定する。

```math
\begin{aligned}
&\text{(hM)}\quad M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell), \cr
&\text{(hd0)}\quad 0 \lt d_0, \cr
&\text{(hlp1)}\quad \ell_1 = v_0 + d_0, \cr
&\text{(hwlt)}\quad w_0 \lt \ell_2, \cr
&\text{(hnl1)}\quad \lvert G\rvert \to^M_1 (\lvert M\rvert - 1), \cr
&\text{(hr')}\quad r' \lt \lvert B\rvert, \cr
&\text{(hlev)}\quad B_{0,r'} = v_0 + d_0 - 1, \cr
&\text{(hafter)}\quad \forall rr,\ \bigl(r' \lt rr \wedge rr \lt \lvert B\rvert\bigr)
   \to v_0 + d_0 \le B_{0,rr} .
\end{aligned}
```

（$`\to^M_1`$ [D.nextrel1](Pss.md#d-nextrel1)）

このとき $`w_0 \le B_{1,r'} + 1`$。

### 証明

$`r'`$ が $`0`$ かどうかで場合分けする。

**(a) $`r' = 0`$ のとき。** $`B = (v_0,w_0) :: R`$ より $`B\langle 0\rangle = (v_0,w_0)`$、
すなわち $`B_{1,0} = w_0`$ である。よって示すべきは $`w_0 \le w_0 + 1`$ であり、これは成り立つ。

**(b) $`0 \lt r'`$ のとき。**
以下 (hM) により $`M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ と書く。
[T.hostM_length](Column-2.md#t-hostM_length) より
$`\lvert M\rvert = \lvert G\rvert + \lvert B\rvert + 1`$ であり、したがって

```math
\lvert M\rvert - 1 = \lvert G\rvert + \lvert B\rvert .
```

まず 2 つの成分を計算する。$`M_{0,j}`$ の定義（D.entry）と
[T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk)（$`r' \lt \lvert B\rvert`$）より

```math
M_{0,\lvert G\rvert + r'} = B_{0,r'} = v_0 + d_0 - 1 ,
```

[T.hostM_getD_lp](#t-hostM_getD_lp) と (hlp1) より

```math
M_{0,\lvert G\rvert + \lvert B\rvert} = \ell_1 = v_0 + d_0 .
```

**行 0 の親子関係。** $`\lvert G\rvert + r' \to^M_0 \lvert G\rvert + \lvert B\rvert`$（[D.nextrel0](Pss.md#d-nextrel0)）を示す。
$`\to^M_0`$ の定義（D.nextrel0）の 5 条件を確かめる。

**(1)** $`r' \lt \lvert B\rvert`$ より
$`\lvert G\rvert + r' \lt \lvert G\rvert + \lvert B\rvert \lt \lvert M\rvert`$。

**(2)** $`\lvert G\rvert + \lvert B\rvert \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert M\rvert`$。

**(3)** $`r' \lt \lvert B\rvert`$ より $`\lvert G\rvert + r' \lt \lvert G\rvert + \lvert B\rvert`$。

**(4)** (hd0) より $`d_0 \ge 1`$ であるから
$`M_{0,\lvert G\rvert + r'} = v_0 + d_0 - 1 \lt v_0 + d_0 = M_{0,\lvert G\rvert + \lvert B\rvert}`$。

**(5)** $`\lvert G\rvert + r' \lt j`$ かつ $`j \lt \lvert G\rvert + \lvert B\rvert`$ をみたす $`j`$ を取る。
$`rr := j - \lvert G\rvert`$ とおくと $`j = \lvert G\rvert + rr`$、$`r' \lt rr`$、$`rr \lt \lvert B\rvert`$ である。
[T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) より $`M_{0,j} = B_{0,rr}`$ であり、
(hafter) より $`v_0 + d_0 \le B_{0,rr}`$、すなわち
$`M_{0,\lvert G\rvert + \lvert B\rvert} \le M_{0,j}`$。

**行 0 の祖先関係。** $`\le^M_0`$（[D.le0](Pss.md#d-le0)）の定義の 3 条件のうち (1), (2) は上の (1), (2) であり、
(3) は 1 歩の $`\to^M_0`$ からなる鎖として得られる。よって

```math
\lvert G\rvert + r' \le^M_0 \lvert G\rvert + \lvert B\rvert = \lvert M\rvert - 1 .
```

**最大性の適用。** (hnl1) すなわち $`\lvert G\rvert \to^M_1 (\lvert M\rvert - 1)`$ の
$`\to^M_1`$ の定義（D.nextrel1）の条件 (6) を $`j := \lvert G\rvert + r'`$ に適用する。
その前提は $`\lvert G\rvert \lt \lvert G\rvert + r'`$（$`0 \lt r'`$ による）と、
いま示した $`\lvert G\rvert + r' \le^M_0 \lvert M\rvert - 1`$ である。よって

```math
M_{1,\lvert M\rvert - 1} \le M_{1,\lvert G\rvert + r'} .
```

$`M_{1,j}`$ の定義（D.entry）と [T.hostM_getD_lp](#t-hostM_getD_lp) より
$`M_{1,\lvert M\rvert - 1} = M_{1,\lvert G\rvert + \lvert B\rvert} = \ell_2`$ であり、
[T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) より $`M_{1,\lvert G\rvert + r'} = B_{1,r'}`$ である。
したがって $`\ell_2 \le B_{1,r'}`$ であり、(hwlt) の $`w_0 \lt \ell_2`$ と合わせて

```math
w_0 \lt \ell_2 \le B_{1,r'} \le B_{1,r'} + 1 . \qquad \blacksquare
```

<a id="t-r1ok_oper"></a>
## 定理: 行 1 の規律は展開で保たれる (T.r1ok_oper)

### 定理

$`1 \le n`$、$`\mathrm{r1ok}(M)`$、$`\mathrm{steps}_1(M)`$（[D.steps1](Seqlex.md#d-steps1)）ならば
$`\mathrm{r1ok}(M[n])`$（[D.oper](Pss.md#d-oper)）。

### 証明

$`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$（[D.idx1](Pss.md#d-idx1)）とおく。
$`M[n]`$ の定義（D.oper）の 4 つの分岐で場合分けする。

**(a) $`j_1 = 0`$ のとき。**
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より $`M[n] = M`$ であり、
結論は仮定 $`\mathrm{r1ok}(M)`$ そのものである。

**(b) $`j_1 \ne 0`$ かつ $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。**
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) より
$`M[n] = \mathrm{Pred}\,M`$ であり、
[T.r1ok_Pred](#t-r1ok_Pred) を仮定 $`\mathrm{r1ok}(M)`$ に適用すればよい。

**(c) $`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$（[D.hasParent](Pss.md#d-hasParent)）のとき。**
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) より
$`M[n] = \mathrm{Pred}\,M`$ であり、[T.r1ok_Pred](#t-r1ok_Pred) を適用すればよい。

**(d) $`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
$`1 \lt \lvert M\rvert`$ である。実際 $`\lvert M\rvert \le 1`$ とすると、自然数の減法は
$`0`$ で切り捨てるから $`j_1 = \lvert M\rvert - 1 = 0`$ となり、この場合の仮定
$`j_1 \ne 0`$ に反する。
[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) を適用して、
$`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ で
次をみたすものを得る。$`B := (v_0,w_0) :: R`$ とおく。

```math
\begin{aligned}
&\text{(1)}\ M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell), \cr
&\text{(2)}\ M[n] = G \mathbin{+\!\!+} B^{+0\cdot d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}, \cr
&\text{(3)}\ \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(5)}\ \bigl(d_0 = 0 \wedge i_1 = 0\bigr) \ \vee\
   \bigl(0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 j_1\bigr).
\end{aligned}
```

（[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) の 6 つの主張のうち、
以下で用いる 4 つを同じ番号で挙げた。また $`\mathrm{copyExp}`$ の定義（D.copyExp）により
(2) の右辺は $`\mathrm{copyExp}(G,B,d_0,n)`$ である。）
(1) より $`\mathrm{r1ok}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$ と
$`\mathrm{steps}_1(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$ が仮定から従う。

**段差条件。** $`r + 1 \lt \lvert B\rvert`$ をみたす $`r`$ に対し
$`B_{0,r+1} \le B_{0,r} + 1`$ を示す。
[T.hostM_length](Column-2.md#t-hostM_length) より
$`\lvert G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\rvert = \lvert G\rvert + \lvert B\rvert + 1`$ であり、
$`r + 1 \lt \lvert B\rvert`$ より
$`(\lvert G\rvert + r) + 1 \lt \lvert G\rvert + \lvert B\rvert + 1`$ である。
[T.steps1_iff](Seqlex.md#t-steps1_iff) を
$`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ の添字 $`\lvert G\rvert + r`$ に適用して

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + (r+1)}
  \le \bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + r} + 1
```

を得る。$`r + 1 \lt \lvert B\rvert`$ と $`r \lt \lvert B\rvert`$ に
[T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) を適用すると、これは
$`B_{0,r+1} \le B_{0,r} + 1`$ である。

**末尾の段差条件。** $`\ell_1 \le B_{0,\lvert B\rvert - 1} + 1`$ を示す。
$`0 \lt \lvert B\rvert`$ であるから

```math
\bigl(\lvert G\rvert + (\lvert B\rvert - 1)\bigr) + 1 = \lvert G\rvert + \lvert B\rvert
  \lt \lvert G\rvert + \lvert B\rvert + 1
```

である。
[T.steps1_iff](Seqlex.md#t-steps1_iff) を添字 $`\lvert G\rvert + (\lvert B\rvert - 1)`$ に適用して

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + \lvert B\rvert}
  \le \bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + (\lvert B\rvert - 1)} + 1
```

を得る。左辺は [T.hostM_getD_lp](#t-hostM_getD_lp) より $`\ell_1`$、
右辺は [T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk)（$`\lvert B\rvert - 1 \lt \lvert B\rvert`$）より
$`B_{0,\lvert B\rvert - 1} + 1`$ である。

**組み立て。** [T.r1ok_copyExp](Column-2.md#t-r1ok_copyExp) を
$`G, B, \ell, n, d_0`$ に適用する。仮定 (hr) は
$`\mathrm{r1ok}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$ である。仮定 (hmin) を示すために
$`0 \lt k`$、$`k \lt n`$、$`q \lt \lvert B\rvert`$、$`\forall r \lt q,\ B_{0,q} \le B_{0,r}`$、
$`0 \lt B_{0,q} + k d_0`$ を取り、(5) の選言で場合分けする。

**第 1 の選言 $`d_0 = 0 \wedge i_1 = 0`$ のとき。**
[T.r1ok_min_d0zero](#t-r1ok_min_d0zero) を (3) と
$`\mathrm{r1ok}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$ に適用すればよい。

**第 2 の選言のとき。** すなわち

```math
0 \lt d_0 \ \wedge\ w_0 \lt \ell_2 \ \wedge\ \ell_1 = v_0 + d_0
  \ \wedge\ \lvert G\rvert \to^M_1 j_1
```

が成り立つとき。[T.r1ok_min_d0pos](#t-r1ok_min_d0pos) を適用する。その仮定 (hdom) は (3)、
(hd0), (hlp) はこの選言の第 1・第 3 成分、(hstep), (hlpstep) は上で示した
2 つの段差条件である。残る仮定 (hclimb) は、$`r' \lt \lvert B\rvert`$、
$`B_{0,r'} = v_0 + d_0 - 1`$、および

```math
\forall rr,\ \bigl(r' \lt rr \wedge rr \lt \lvert B\rvert\bigr) \to v_0 + d_0 \le B_{0,rr}
```

を仮定して $`w_0 \le B_{1,r'} + 1`$ を導くものであり、
[T.climb_bound](#t-climb_bound) を (1) と、この選言の第 1・第 2・第 3・第 4 成分に
適用して得られる。

以上より [T.r1ok_copyExp](Column-2.md#t-r1ok_copyExp) が使えて
$`\mathrm{r1ok}(\mathrm{copyExp}(G,B,d_0,n))`$ を得る。(2) よりこれは
$`\mathrm{r1ok}(M[n])`$ である。∎

<a id="t-r1ok_ST_PS"></a>
## 定理: 標準形は $`\mathrm{r1ok}`$ をみたす (T.r1ok_ST_PS)

### 定理

$`M \in \mathrm{ST\_PS}`$（[D.ST_PS](Pss.md#d-ST_PS)）ならば $`\mathrm{r1ok}(M)`$。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M) :\equiv \mathrm{r1ok}(M).
```

- **基底段**（規則 (diag)）：$`M = \Delta_0^v`$（[D.diagSeq](Pss.md#d-diagSeq)）である。
  [T.r1ok_diagSeq](Column-2.md#t-r1ok_diagSeq) が $`\Phi(\Delta_0^v)`$ そのものである。

- **帰納段**（規則 (oper)）：$`N \in \mathrm{ST\_PS}`$、$`1 \le n`$ とする。帰納法の仮定は
  $`\Phi(N)`$、すなわち $`\mathrm{r1ok}(N)`$ であり、示すべきは $`\mathrm{r1ok}(N[n])`$ である。
  [T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS) を $`N \in \mathrm{ST\_PS}`$ に適用して
  $`\mathrm{blockok}(0, N)`$（[D.blockok](Seqlex.md#d-blockok)）を得る。$`\mathrm{blockok}`$ の定義（D.blockok）は
  3 つの連言であり、その第 3 連言子は $`\mathrm{steps}_1(N)`$ である。
  [T.r1ok_oper](#t-r1ok_oper) を $`1 \le n`$、$`\mathrm{r1ok}(N)`$、$`\mathrm{steps}_1(N)`$ に
  適用すれば $`\mathrm{r1ok}(N[n])`$ を得る。∎

<a id="t-nextrel0_bound"></a>
## 定理: 行 0 の親子の行き先は範囲内 (T.nextrel0_bound)

### 定理

$`a \to^M_0 b`$ ならば $`b \lt \lvert M\rvert`$。

### 証明

$`\to^M_0`$ の定義（D.nextrel0）の第 2 条件そのものである。∎

<a id="t-le0_le"></a>
## 定理: 行 0 の祖先関係は添字の大小を含む (T.le0_le)

### 定理

$`a \le^M_0 b`$ ならば $`a \le b`$。

### 証明

$`\le^M_0`$ の定義（D.le0）の第 3 条件により $`a \mathbin{(\to^M_0)^{*}} b`$ である。
鎖 $`a \mathbin{(\to^M_0)^{*}} b`$ の構成に関する帰納法。帰納法の述語は

```math
\Phi(j) :\equiv a \le j .
```

- **基底段**（$`j = a`$、鎖の長さ $`0`$）：$`a \le a`$ は $`\le`$ の反射性による。

- **帰納段**（$`a \mathbin{(\to^M_0)^{*}} y`$ と $`y \to^M_0 z`$ から $`a \mathbin{(\to^M_0)^{*}} z`$）：
  帰納法の仮定は $`\Phi(y)`$、すなわち $`a \le y`$ である。
  [T.nextrel0_lt](Column.md#t-nextrel0_lt) より $`y \lt z`$ であるから $`a \le y \le z`$、
  すなわち $`\Phi(z)`$。∎

<a id="d-z0ok"></a>
## 定義: 行 0 が 0 の列の規律 (D.z0ok)

$`M \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{z0ok}(M) :\iff \forall j,\ j \lt \lvert M\rvert \to \bigl(M_{0,j} = 0 \to M_{1,j} = 0\bigr).
```

すなわち行 $`0`$ の値が $`0`$ である列は行 $`1`$ の値も $`0`$ である、と読む。

<a id="t-z0ok_diagSeq"></a>
## 定理: 対角列は $`\mathrm{z0ok}`$ をみたす (T.z0ok_diagSeq)

### 定理

任意の $`v \in \mathbb{N}`$ に対し $`\mathrm{z0ok}(\Delta_0^v)`$。

### 証明

$`j`$ を取り $`j \lt \lvert \Delta_0^v\rvert`$、$`(\Delta_0^v)_{0,j} = 0`$ とする。
[T.diagSeq0_length](Column-2.md#t-diagSeq0_length) より $`\lvert \Delta_0^v\rvert = v + 1`$ であるから
$`j \lt v + 1`$ であり、[T.diagSeq0_getD](Column-2.md#t-diagSeq0_getD) より
$`\Delta_0^v\langle j\rangle = (j, j)`$ である。$`M_{i,j}`$ の定義（D.entry）により

```math
(\Delta_0^v)_{0,j} = j, \qquad (\Delta_0^v)_{1,j} = j
```

である。仮定 $`(\Delta_0^v)_{0,j} = 0`$ は $`j = 0`$ を与えるから、
$`(\Delta_0^v)_{1,j} = j = 0`$ である。∎

<a id="t-z0ok_take"></a>
## 定理: 前部分列は $`\mathrm{z0ok}`$ をみたす (T.z0ok_take)

### 定理

$`\mathrm{z0ok}(M)`$ ならば、任意の $`m \in \mathbb{N}`$ に対し
$`\mathrm{z0ok}(\mathrm{take}_m M)`$。

### 証明

$`j`$ を取り $`j \lt \lvert \mathrm{take}_m M\rvert`$、$`(\mathrm{take}_m M)_{0,j} = 0`$ とする。
$`\lvert \mathrm{take}_m M\rvert = \min(m, \lvert M\rvert)`$ であるから
$`j \lt m`$ かつ $`j \lt \lvert M\rvert`$ である。

$`j \lt m`$ に [T.getD_take](Column-2.md#t-getD_take) を適用すると
$`(\mathrm{take}_m M)\langle j\rangle = M\langle j\rangle`$ であり、したがって

```math
(\mathrm{take}_m M)_{0,j} = M_{0,j}, \qquad (\mathrm{take}_m M)_{1,j} = M_{1,j}
```

である。仮定より $`M_{0,j} = 0`$ であるから、$`\mathrm{z0ok}(M)`$ の定義（D.z0ok）を
$`j \lt \lvert M\rvert`$ に適用して $`M_{1,j} = 0`$ を得る。
これは $`(\mathrm{take}_m M)_{1,j} = 0`$ に等しい。∎

<a id="t-z0ok_Pred"></a>
## 定理: 前者は $`\mathrm{z0ok}`$ をみたす (T.z0ok_Pred)

### 定理

$`\mathrm{z0ok}(M)`$ ならば $`\mathrm{z0ok}(\mathrm{Pred}\,M)`$。

### 証明

$`\mathrm{Pred}`$ の定義（D.Pred）の場合分けによる。

- $`\lvert M\rvert \le 1`$ のとき。$`\mathrm{Pred}\,M = M`$ であり、仮定そのものである。

- $`\lvert M\rvert \ge 2`$ のとき。
  $`\mathrm{Pred}\,M = \mathrm{dropLast}\,M = \mathrm{take}_{\lvert M\rvert - 1} M`$ である
  （どれも $`M`$ の先頭 $`\lvert M\rvert - 1`$ 要素からなる列である）。
  よって [T.z0ok_take](#t-z0ok_take) を $`m := \lvert M\rvert - 1`$ に適用すればよい。∎

<a id="t-z0ok_copyExp"></a>
## 定理: コピー展開は $`\mathrm{z0ok}`$ をみたす (T.z0ok_copyExp)

### 定理

$`G, B \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、$`d_0, n \in \mathbb{N}`$ とする。
$`\mathrm{z0ok}\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)`$ ならば
$`\mathrm{z0ok}\bigl(\mathrm{copyExp}(G, B, d_0, n)\bigr)`$。

### 証明

$`E := \mathrm{copyExp}(G, B, d_0, n)`$、$`H := G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ とおく。
[T.hostM_length](Column-2.md#t-hostM_length) より
$`\lvert H\rvert = \lvert G\rvert + \lvert B\rvert + 1`$ である。

$`j`$ を取り $`j \lt \lvert E\rvert`$、$`E_{0,j} = 0`$ とする。
[T.copyExp_length](Column-2.md#t-copyExp_length) より
$`\lvert E\rvert = \lvert G\rvert + n \lvert B\rvert`$ であるから
$`j \lt \lvert G\rvert + n \lvert B\rvert`$ である。$`j`$ と $`\lvert G\rvert`$ の大小で場合分けする。

**(a) $`j \lt \lvert G\rvert`$ のとき。**
[T.copyExp_getD_pre](Column-2.md#t-copyExp_getD_pre) より $`E\langle j\rangle = G\langle j\rangle`$、
[T.hostM_getD_pre](Column-2.md#t-hostM_getD_pre) より $`H\langle j\rangle = G\langle j\rangle`$ である。
$`j \lt \lvert G\rvert \le \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$ であるから、
$`\mathrm{z0ok}(H)`$ の定義（D.z0ok）を添字 $`j`$ に適用できる。その前件は
$`H_{0,j} = G_{0,j} = E_{0,j} = 0`$ で成り立つから、$`H_{1,j} = 0`$、すなわち
$`E_{1,j} = G_{1,j} = H_{1,j} = 0`$ を得る。

**(b) $`\lvert G\rvert \le j`$ のとき。**
まず $`0 \lt \lvert B\rvert`$ を示す。$`\lvert B\rvert = 0`$ とすると
$`n \lvert B\rvert = 0`$ となり $`j \lt \lvert G\rvert`$ となって、この場合の仮定に矛盾する。

$`j - \lvert G\rvert \lt n \lvert B\rvert`$ であるから、
[T.index_decomp](Column-2.md#t-index_decomp) を $`L := \lvert B\rvert`$ に適用して
$`k \lt n`$、$`q \lt \lvert B\rvert`$、$`j - \lvert G\rvert = k \lvert B\rvert + q`$ なる
$`k, q`$ を取る。$`\lvert G\rvert \le j`$ より
$`j = \lvert G\rvert + (k \lvert B\rvert + q)`$ である。

[T.copyExp_getD_copy](Column-2.md#t-copyExp_getD_copy) より

```math
E\langle j\rangle = \bigl(\pi_1(B\langle q\rangle) + k d_0,\ \pi_2(B\langle q\rangle)\bigr)
```

であり、$`M_{i,j}`$ の定義（D.entry）により
$`E_{0,j} = B_{0,q} + k d_0`$、$`E_{1,j} = B_{1,q}`$ である。
仮定 $`E_{0,j} = 0`$ より $`B_{0,q} + k d_0 = 0`$、したがって $`B_{0,q} = 0`$ である。

$`q \lt \lvert B\rvert`$ に [T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) を適用すると
$`H\langle \lvert G\rvert + q\rangle = B\langle q\rangle`$ である。
$`\lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$ であるから、
$`\mathrm{z0ok}(H)`$ の定義（D.z0ok）を添字 $`\lvert G\rvert + q`$ に適用できる。その前件は
$`H_{0,\lvert G\rvert + q} = B_{0,q} = 0`$ で成り立つから、
$`B_{1,q} = H_{1,\lvert G\rvert + q} = 0`$、すなわち $`E_{1,j} = 0`$ を得る。∎
