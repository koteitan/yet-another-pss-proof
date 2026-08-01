[← README](README-ja.md) | [English](Cnf-3.md) | [Japanese](Cnf-3-ja.md) | Cnf [1](Cnf-ja.md) [2](Cnf-2-ja.md) **3**

<a id="t-copies_succ_front"></a>
## 定理: コピー列の先頭からの分解 (T.copies_succ_front)

### 定理

$`d, n \in \mathbb{N}`$、$`B \in \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）に対し

```math
\mathrm{cp}_d(B, n+1) = B \mathbin{+\!\!+} \bigl(\mathrm{cp}_d(B, n)\bigr)^{+d} .
```

（$`\mathrm{cp}`$ [D.copies](Cnf-2-ja.md#d-copies)、$`B^{+d}`$ [D.shiftr0](Cnf-2-ja.md#d-shiftr0)）

### 証明

$`\mathrm{range}(n+1) = (0, 1, \dots, n)`$ であり、先頭の $`0`$ を切り出せば

```math
\mathrm{range}(n+1) = (0) \mathbin{+\!\!+} \bigl(\,k+1\,\bigr)_{k \in \mathrm{range}(n)}
```

である。よって $`\mathrm{cp}`$ の定義（D.copies）より

```math
\mathrm{cp}_d(B, n+1)
  = B^{+0\cdot d} \mathbin{+\!\!+} \bigl(B^{+(k+1)d}\bigr)_{k \in \mathrm{range}(n)}
    \text{ の連結}
```

である。以下 2 点を示す。

**第 1 点：$`B^{+0\cdot d} = B`$。**
$`0 \cdot d = 0`$ であるから [T.shiftr0_zero](Cnf-2-ja.md#t-shiftr0_zero) により $`B^{+0} = B`$。

**第 2 点：$`k \in \mathrm{range}(n)`$ にわたる $`B^{+(k+1)d}`$ の連結は
$`\bigl(\mathrm{cp}_d(B,n)\bigr)^{+d}`$ に等しい。**
まず各 $`k`$ について

```math
\bigl(B^{+kd}\bigr)^{+d} = B^{+(k+1)d}
```

である。実際、$`B`$ の要素 $`p`$ は左辺では $`((p_1 + kd) + d,\ p_2)`$ に写り、
$`\mathbb{N}`$ の加法の結合則と $`kd + d = (k+1)d`$ から
$`(p_1 + kd) + d = p_1 + (k+1)d`$ であるから、右辺の $`(p_1 + (k+1)d,\ p_2)`$ に一致する。

次に $`(\cdot)^{+d}`$ は各要素を写す操作であるから、列の連結と交換する。すなわち列
$`L_0, \dots, L_{n-1}`$ について

```math
\bigl(L_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} L_{n-1}\bigr)^{+d}
  = L_0^{+d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} L_{n-1}^{+d} .
```

これを $`L_k := B^{+kd}`$ に適用すると、$`\mathrm{cp}`$ の定義（D.copies）より
$`\mathrm{cp}_d(B,n) = L_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} L_{n-1}`$ であるから

```math
\bigl(\mathrm{cp}_d(B,n)\bigr)^{+d}
  = \bigl(B^{+0\cdot d}\bigr)^{+d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl(B^{+(n-1)d}\bigr)^{+d}
  = B^{+1\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+n\,d}
```

となり、これが求める連結である。

第 1 点と第 2 点を合わせて $`\mathrm{cp}_d(B,n+1) = B \mathbin{+\!\!+} (\mathrm{cp}_d(B,n))^{+d}`$。∎

<a id="t-copies_one"></a>
## 定理: コピー 1 個 (T.copies_one)

### 定理

$`d \in \mathbb{N}`$、$`B \in \mathrm{PairSeq}`$ に対し $`\mathrm{cp}_d(B, 1) = B`$。

### 証明

[T.copies_succ_front](#t-copies_succ_front) を $`n := 0`$ に適用して

```math
\mathrm{cp}_d(B, 1) = B \mathbin{+\!\!+} \bigl(\mathrm{cp}_d(B, 0)\bigr)^{+d}
```

を得る。[T.copies_zero](Cnf-2-ja.md#t-copies_zero) より $`\mathrm{cp}_d(B,0) = ()`$ であり、
[T.shiftr0_nil](Cnf-2-ja.md#t-shiftr0_nil) より $`()^{+d} = ()`$ である。
$`B \mathbin{+\!\!+} () = B`$ であるから結論を得る。∎

<a id="t-copies_succ_cons"></a>
## 定理: コピー列の先頭付き分解 (T.copies_succ_cons)

### 定理

$`d, v_0, w_0, n \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ に対し、$`B := (v_0,w_0) :: R`$ とおくと

```math
\mathrm{cp}_d(B, n+1) = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} (\mathrm{cp}_d(B, n))^{+d}\bigr).
```

### 証明

[T.copies_succ_front](#t-copies_succ_front) より
$`\mathrm{cp}_d(B, n+1) = B \mathbin{+\!\!+} (\mathrm{cp}_d(B,n))^{+d}`$ である。
$`B = (v_0,w_0) :: R`$ であるから、連結の定義により

```math
\bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} S = (v_0,w_0) :: (R \mathbin{+\!\!+} S)
```

が任意の列 $`S`$ について成り立つ。$`S := (\mathrm{cp}_d(B,n))^{+d}`$ とすればよい。∎

<a id="t-copies_v0_le"></a>
## 定理: コピー列の行 0 の下界 (T.copies_v0_le)

### 定理

$`v_0, w_0, d, n \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ とし、
$`\forall x \in R,\ v_0 \le x_1`$ を仮定する。このとき

```math
\forall x \in \mathrm{cp}_d\bigl((v_0,w_0) :: R,\ n\bigr),\ v_0 \le x_1 .
```

### 証明

$`x \in \mathrm{cp}_d((v_0,w_0) :: R,\ n)`$ とする。$`\mathrm{cp}`$ の定義（D.copies）より、
$`\mathrm{cp}_d((v_0,w_0)::R, n)`$ は $`k \in \mathrm{range}(n)`$ にわたる
$`((v_0,w_0)::R)^{+kd}`$ の連結であるから、ある $`k \in \mathrm{range}(n)`$ が存在して
$`x \in ((v_0,w_0)::R)^{+kd}`$ である。
[T.mem_shiftr0](Cnf-2-ja.md#t-mem_shiftr0) より、ある $`p \in (v_0,w_0) :: R`$ が存在して
$`x = (p_1 + kd,\ p_2)`$ である。

$`p \in (v_0,w_0) :: R`$ を場合分けする。

- $`p = (v_0,w_0)`$ のとき。$`p_1 = v_0`$ であるから $`v_0 \le p_1`$。
- $`p \in R`$ のとき。仮定より $`v_0 \le p_1`$。

いずれの場合も $`v_0 \le p_1`$ である。$`x_1 = p_1 + kd`$ であり、
$`\mathbb{N}`$ において $`p_1 \le p_1 + kd`$ であるから、$`\le`$ の推移律より
$`v_0 \le x_1`$。∎

<a id="t-copies_tl_gt"></a>
## 定理: コピー列の尾部の行 0 の狭義下界 (T.copies_tl_gt)

### 定理

$`v_0, w_0, d, n \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ とし、$`B := (v_0,w_0) :: R`$ とおく。
$`\forall x \in R,\ v_0 \lt x_1`$、$`0 \lt d`$、$`1 \le n`$ を仮定する。このとき

```math
\forall x \in R \mathbin{+\!\!+} \bigl(\mathrm{cp}_d(B,\ n-1)\bigr)^{+d},\ v_0 \lt x_1 .
```

### 証明

$`x \in R \mathbin{+\!\!+} (\mathrm{cp}_d(B, n-1))^{+d}`$ とし、$`x`$ がどちらの側の要素かで場合分けする。

- $`x \in R`$ のとき。仮定 $`\forall x \in R,\ v_0 \lt x_1`$ そのものである。

- $`x \in (\mathrm{cp}_d(B, n-1))^{+d}`$ のとき。[T.mem_shiftr0](Cnf-2-ja.md#t-mem_shiftr0) より、
  ある $`p \in \mathrm{cp}_d(B, n-1)`$ が存在して $`x = (p_1 + d,\ p_2)`$ である。
  仮定 $`\forall x \in R,\ v_0 \lt x_1`$ から $`\forall x \in R,\ v_0 \le x_1`$ が従うので、
  [T.copies_v0_le](#t-copies_v0_le) を $`n := n-1`$ に適用して $`v_0 \le p_1`$ を得る。
  $`0 \lt d`$ であるから $`p_1 \lt p_1 + d`$ であり、
  $`v_0 \le p_1 \lt p_1 + d = x_1`$ より $`v_0 \lt x_1`$。∎

<a id="t-cnf_copies"></a>
## 定理: 上昇コピー列は CNF (T.cnf_copies)

### 定理

$`v_0, w_0, d_0 \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ とし、
$`B := (v_0,w_0) :: R`$ とおく。次の 5 つを仮定する。

```math
\begin{aligned}
&\text{(hR)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(d0pos)}\quad 0 \lt d_0, \cr
&\text{(w0lt)}\quad w_0 \lt \ell_2, \cr
&\text{(lphd)}\quad \ell_1 = v_0 + d_0, \cr
&\text{(cBlp)}\quad \mathrm{cnf}\bigl(\mathrm{tr}(B \mathbin{+\!\!+} (\ell))\bigr).
\end{aligned}
```

（$`\mathrm{cnf}`$ [D.cnf](Cnf-ja.md#d-cnf)、$`\mathrm{tr}`$ [D.translate](Term-ja.md#d-translate)）

このとき任意の $`n \in \mathbb{N}`$ に対し

```math
\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{cp}_{d_0}(B, n))\bigr).
```

### 証明

$`n`$ に関する自然数の帰納法。

```math
\Phi(n) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{cp}_{d_0}(B, n))\bigr)
```

を $`n`$ について示す。

**基底段** $`n = 0`$。
[T.copies_zero](Cnf-2-ja.md#t-copies_zero) より $`\mathrm{cp}_{d_0}(B,0) = ()`$ であり、
$`\mathrm{tr}`$ の定義（D.translate）より $`\mathrm{tr}\,() = \mathsf{Z}`$（[D.Three](Term-ja.md#d-Three)）である。
[T.cnf_Z](Cnf-ja.md#t-cnf_Z) より $`\mathrm{cnf}(\mathsf{Z})`$ が成り立つ。よって $`\Phi(0)`$。

**帰納段** $`n \to n+1`$：$`\Phi(n)`$、すなわち
$`\mathrm{cnf}(\mathrm{tr}(\mathrm{cp}_{d_0}(B,n)))`$ を仮定する。$`n`$ で場合分けする。

**(i) $`n = 0`$ のとき。** 示すべきは $`\Phi(1)`$ である。
[T.copies_one](#t-copies_one) より $`\mathrm{cp}_{d_0}(B,1) = B`$ である。
また $`B \mathbin{+\!\!+} (\ell)`$ の末尾 1 要素を落とすと $`B`$ に戻るから
$`B = \mathrm{dropLast}\,(B \mathbin{+\!\!+} (\ell))`$ である。
$`B \mathbin{+\!\!+} (\ell)`$ は $`\ell`$ を要素にもつので空列ではない。
よって [T.cnf_dropLast](Cnf-ja.md#t-cnf_dropLast) を $`C := B \mathbin{+\!\!+} (\ell)`$ に適用し、
(cBlp) から $`\mathrm{cnf}(\mathrm{tr}(B))`$、すなわち $`\Phi(1)`$ を得る。

**(ii) $`n = m + 1`$ のとき。** 示すべきは $`\Phi(m+2)`$ である。$`\Phi(m+1)`$、すなわち $`\mathrm{cnf}(\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1)))`$ を仮定する。
以下 $`Q := \mathrm{cp}_{d_0}(B, m)`$、$`S := R \mathbin{+\!\!+} Q^{+d_0}`$ と略記する。

**ステップ 1：$`\mathrm{cp}_{d_0}(B, m+1)`$ とその平行移動の形。**
[T.copies_succ_cons](#t-copies_succ_cons) より

```math
\text{(F)}\qquad \mathrm{cp}_{d_0}(B, m+1) = (v_0,w_0) :: S
```

である。これに [T.shiftr0_cons](Cnf-2-ja.md#t-shiftr0_cons) を適用して

```math
\text{(G)}\qquad \bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)^{+d_0} = (v_0 + d_0,\ w_0) :: S^{+d_0}
```

を得る。

**ステップ 2：翻訳の形。**
[T.copies_tl_gt](#t-copies_tl_gt) を (hR)、(d0pos)、$`n := m+1`$（$`1 \le m+1`$）に適用すると
$`n - 1 = m`$ であるから

```math
\text{(tlgt)}\qquad \forall x \in S,\ v_0 \lt x_1
```

を得る。(F) と [T.translate_single_tree](Term-ja.md#t-translate_single_tree) より

```math
\text{(st1)}\qquad \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
```

である。また (G) と [T.translate_shiftr0](Cnf-2-ja.md#t-translate_shiftr0) より

```math
\mathrm{tr}\bigl((v_0+d_0,\ w_0) :: S^{+d_0}\bigr) = \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)
```

であるから、(st1) と合わせて

```math
\text{(tZ1)}\qquad \mathrm{tr}\bigl((v_0+d_0,\ w_0) :: S^{+d_0}\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
```

を得る。さらに $`\mathrm{tr}`$ の定義（D.translate）を $`p := \ell`$、$`L := ()`$ に適用すると
$`\mathrm{tw}_{\ell_1}() = ()`$、$`\mathrm{dw}_{\ell_1}() = ()`$ であるから

```math
\text{(tlp)}\qquad \mathrm{tr}\,(\ell) = \mathsf{P}(\ell_2,\ \mathsf{Z},\ \mathsf{Z}).
```

**ステップ 3：狭義減少と先頭主要項の比較。**
(tZ1), (tlp) と [T.olt_P_P](Term-ja.md#t-olt_P_P) の右辺の第 1 選言 $`w_0 \lt \ell_2`$（(w0lt)）より

```math
\text{(decr)}\qquad \mathrm{tr}\bigl((v_0+d_0,\ w_0) :: S^{+d_0}\bigr) \prec \mathrm{tr}\,(\ell).
```

（$`\prec`$ [D.olt](Term-ja.md#d-olt)）

同じ第 1 選言により $`\mathsf{P}(w_0, \mathrm{tr}\,S, \mathsf{Z}) \prec \mathsf{P}(\ell_2, \mathsf{Z}, \mathsf{Z})`$
であるから、$`\preceq`$（[D.ole](Term-ja.md#d-ole)）の定義（D.ole）の第 1 選言により

```math
\text{(leadle)}\qquad
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
  \preceq \mathsf{P}\bigl(\ell_2,\ \mathsf{Z},\ \mathsf{Z}\bigr)
```

が成り立つ。(tZ1) の右辺の添字と引数は $`w_0`$, $`\mathrm{tr}\,S`$、(tlp) の右辺の添字と引数は
$`\ell_2`$, $`\mathsf{Z}`$ であるから、(leadle) は [T.cnf_ctx_cong](Cnf-2-ja.md#t-cnf_ctx_cong) の仮定
(leadle) の形をしている。

**ステップ 4：$`(v_0+d_0, w_0) :: S^{+d_0}`$ の CNF。**
(G) と [T.translate_shiftr0](Cnf-2-ja.md#t-translate_shiftr0) より
$`\mathrm{tr}\bigl((v_0+d_0,w_0) :: S^{+d_0}\bigr) = \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B,m+1)\bigr)`$
であるから、帰納法の仮定 $`\Phi(m+1)`$ がそのまま

```math
\text{(cZ1)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}((v_0+d_0,\ w_0) :: S^{+d_0})\bigr)
```

を与える。

**ステップ 5：文脈による合同。**
$`x \in S^{+d_0}`$ とすると、[T.mem_shiftr0](Cnf-2-ja.md#t-mem_shiftr0) より、ある $`p \in S`$ が存在して
$`x = (p_1 + d_0,\ p_2)`$ である。(tlgt) より $`v_0 \lt p_1`$、とくに $`v_0 \le p_1`$ であるから

```math
\bigl((v_0+d_0,\ w_0)\bigr)_1 = v_0 + d_0 \le p_1 + d_0 = x_1 .
```

すなわち

```math
\text{(r1)}\qquad \forall x \in S^{+d_0},\ \bigl((v_0+d_0,\ w_0)\bigr)_1 \le x_1 .
```

また (lphd) より $`\bigl((v_0+d_0, w_0)\bigr)_1 = v_0 + d_0 = \ell_1`$ である。

[T.cnf_ctx_cong](Cnf-2-ja.md#t-cnf_ctx_cong) を

```math
z_1 := (v_0+d_0,\ w_0),\quad T_1 := S^{+d_0},\quad
z_2 := \ell,\quad T_2 := (),\quad G := B
```

として適用する。その 7 つの仮定は次のように満たされる。

- $`\mathrm{cnf}(\mathrm{tr}(z_1 :: T_1))`$：ステップ 4 の (cZ1)。
- $`\mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2)`$：$`z_2 :: T_2 = (\ell)`$ であり、
  ステップ 3 の (decr)。
- $`(z_1)_1 = (z_2)_1`$：(lphd) による $`v_0 + d_0 = \ell_1`$。
- (leadle)：ステップ 3 の (leadle) を (tZ1), (tlp) と合わせたもの。
- $`\forall x \in T_1,\ (z_1)_1 \le x_1`$：ステップ 5 の (r1)。
- $`\forall x \in T_2,\ (z_2)_1 \le x_1`$：$`T_2 = ()`$ は要素をもたないから前件が偽であり成り立つ。
- $`\mathrm{cnf}(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2))`$：$`G \mathbin{+\!\!+} z_2 :: T_2 = B \mathbin{+\!\!+} (\ell)`$
  であり、仮定 (cBlp)。

結論として

```math
\mathrm{cnf}\Bigl(\mathrm{tr}\bigl(B \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S^{+d_0}\bigr)\Bigr)
```

を得る。一方 [T.copies_succ_front](#t-copies_succ_front) と (G) より

```math
\mathrm{cp}_{d_0}(B, m+2) = B \mathbin{+\!\!+} \bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)^{+d_0}
  = B \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S^{+d_0}
```

であるから、これは $`\Phi(m+2)`$ そのものである。∎

<a id="t-cnf_oper_i1eq1"></a>
## 定理: 上昇コピー分岐での CNF 保存 (T.cnf_oper_i1eq1)

### 定理

$`v_0, w_0, d_0, n \in \mathbb{N}`$、$`R, G \in \mathrm{PairSeq}`$、
$`\ell \in \mathbb{N}\times\mathbb{N}`$ とし、$`B := (v_0,w_0) :: R`$ とおく。次の 6 つを仮定する。

```math
\begin{aligned}
&\text{(hR)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(d0pos)}\quad 0 \lt d_0, \cr
&\text{(w0lt)}\quad w_0 \lt \ell_2, \cr
&\text{(lphd)}\quad \ell_1 = v_0 + d_0, \cr
&\text{(n1)}\quad 1 \le n, \cr
&\text{(cM)}\quad \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))\bigr).
\end{aligned}
```

このとき

```math
\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n))\bigr).
```

### 証明

(n1) より $`n = m+1`$ をみたす $`m \in \mathbb{N}`$ が取れる。
以下 $`Q := \mathrm{cp}_{d_0}(B, m)`$、$`S := R \mathbin{+\!\!+} Q^{+d_0}`$ と略記する。

まず (lphd) と (d0pos) より $`\ell_1 = v_0 + d_0`$ かつ $`0 \lt d_0`$ であるから

```math
\text{(lpv)}\qquad v_0 \lt \ell_1 .
```

また $`R \mathbin{+\!\!+} (\ell)`$ の全要素 $`x`$ は $`v_0 \lt x_1`$ をみたす
（$`x \in R`$ なら (hR)、$`x = \ell`$ なら (lpv)）。これを (Rlp) とよぶ。

**ステップ 1：狭義減少 $`\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1)) \prec \mathrm{tr}(B \mathbin{+\!\!+} (\ell))`$。**

$`m`$ で場合分けする。

**(i) $`m = 0`$ のとき。** [T.copies_one](#t-copies_one) より
$`\mathrm{cp}_{d_0}(B,1) = B`$ であるから、
[T.translate_snoc_increase](Decrease-ja.md#t-translate_snoc_increase) を $`C := B`$、$`m := \ell`$ に
適用して $`\mathrm{tr}\,B \prec \mathrm{tr}(B \mathbin{+\!\!+} (\ell))`$ を得る。

**(ii) $`m = m' + 1`$ のとき。**
$`Q' := \mathrm{cp}_{d_0}(B, m')`$、$`S' := R \mathbin{+\!\!+} Q'^{+d_0}`$ とおく。
[T.copies_succ_cons](#t-copies_succ_cons) より
$`\mathrm{cp}_{d_0}(B, m'+1) = (v_0,w_0) :: S'`$ であり、
[T.shiftr0_cons](Cnf-2-ja.md#t-shiftr0_cons) より

```math
\text{(G')}\qquad \bigl(\mathrm{cp}_{d_0}(B, m'+1)\bigr)^{+d_0} = (v_0+d_0,\ w_0) :: S'^{+d_0} .
```

[T.copies_tl_gt](#t-copies_tl_gt) を (hR)、(d0pos)、$`n := m'+1`$ に適用して

```math
\text{(tlgt')}\qquad \forall x \in S',\ v_0 \lt x_1
```

を得る。$`x \in S'^{+d_0}`$ とすると [T.mem_shiftr0](Cnf-2-ja.md#t-mem_shiftr0) より、ある $`p \in S'`$ が
存在して $`x = (p_1+d_0,\ p_2)`$ であり、(tlgt') から $`v_0 \le p_1`$、したがって

```math
\text{(Cge)}\qquad \forall x \in S'^{+d_0},\ v_0 + d_0 \le x_1 .
```

ここで [T.core_i1](Decrease-ja.md#t-core_i1) を

```math
v_0 := v_0,\quad w_0 := w_0,\quad R := R,\quad
c := (v_0+d_0,\ w_0),\quad C' := S'^{+d_0},\quad \ell := \ell
```

として適用する。その 5 つの仮定は次のように満たされる。

- $`\forall x \in R,\ v_0 \lt x_1`$：(hR)。
- $`\forall x \in C',\ c_1 \le x_1`$：(Cge)（$`c_1 = v_0 + d_0`$）。
- $`c_1 = \ell_1`$：(lphd)。
- $`v_0 \lt \ell_1`$：(lpv)。
- $`c_2 \lt \ell_2`$：$`c_2 = w_0`$ であり (w0lt)。

結論として

```math
\mathrm{tr}\bigl(B \mathbin{+\!\!+} ((v_0+d_0,\ w_0) :: S'^{+d_0})\bigr)
  \prec \mathrm{tr}\bigl(B \mathbin{+\!\!+} (\ell)\bigr)
```

を得る。一方 [T.copies_succ_front](#t-copies_succ_front) と (G') より

```math
\mathrm{cp}_{d_0}(B, m'+2) = B \mathbin{+\!\!+} \bigl(\mathrm{cp}_{d_0}(B, m'+1)\bigr)^{+d_0}
  = B \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0) :: S'^{+d_0}\bigr)
```

であるから、これは $`\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1)) \prec \mathrm{tr}(B \mathbin{+\!\!+} (\ell))`$
そのものである。

以上 (i), (ii) により

```math
\text{(decr)}\qquad
\mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr) \prec \mathrm{tr}\bigl(B \mathbin{+\!\!+} (\ell)\bigr).
```

**ステップ 2：両辺の翻訳の形。**
[T.copies_succ_cons](#t-copies_succ_cons) より

```math
\text{(cpcons)}\qquad \mathrm{cp}_{d_0}(B, m+1) = (v_0,w_0) :: S
```

である。[T.copies_tl_gt](#t-copies_tl_gt) を (hR)、(d0pos)、$`n := m+1`$ に適用して

```math
\text{(tlgt)}\qquad \forall x \in S,\ v_0 \lt x_1
```

を得るから、[T.translate_single_tree](Term-ja.md#t-translate_single_tree) より

```math
\text{(st1)}\qquad \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr).
```

また $`B \mathbin{+\!\!+} (\ell) = (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))`$ であり (Rlp) が成り立つから、
ふたたび [T.translate_single_tree](Term-ja.md#t-translate_single_tree) より

```math
\text{(st2)}\qquad \mathrm{tr}\bigl(B \mathbin{+\!\!+} (\ell)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr).
```

**ステップ 3：ブロックの CNF。**
$`\mathbin{+\!\!+}`$ の結合則より
$`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell) = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)`$
であるから、(cM) は

```math
\text{(cM')}\qquad
\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell)))\bigr)
```

と同一の命題である。(Rlp) より

```math
\text{(rT)}\qquad \forall x \in R \mathbin{+\!\!+} (\ell),\ \bigl((v_0,w_0)\bigr)_1 \le x_1
```

であるから、[T.cnf_tail](Cnf-2-ja.md#t-cnf_tail) を $`t := (v_0,w_0)`$、$`T' := R \mathbin{+\!\!+} (\ell)`$、
$`G := G`$ として適用して

```math
\text{(cBlp)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}(B \mathbin{+\!\!+} (\ell))\bigr)
```

を得る（$`B \mathbin{+\!\!+} (\ell) = (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))`$ による）。

**ステップ 4：コピー列そのものの CNF。**
[T.cnf_copies](#t-cnf_copies) を (hR)、(d0pos)、(w0lt)、(lphd)、(cBlp)、$`n := m+1`$ に適用して

```math
\text{(cCopies)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1))\bigr)
```

を得る。(cpcons) によりこれは $`\mathrm{cnf}\bigl(\mathrm{tr}((v_0,w_0) :: S)\bigr)`$ と同一の命題である。

**ステップ 5：引数どうしの狭義減少。**
(decr) に (st1), (st2) を代入すると

```math
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
  \prec \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

である。[T.olt_P_P](Term-ja.md#t-olt_P_P) により右辺の 3 つの選言のいずれかが成り立つ。

- 第 1 選言 $`w_0 \lt w_0`$：$`\lt`$ の非反射性に矛盾する。
- 第 2 選言 $`w_0 = w_0 \wedge \mathrm{tr}\,S \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell))`$：
  求める結論そのものである。
- 第 3 選言 $`w_0 = w_0 \wedge \mathrm{tr}\,S = \mathrm{tr}(R \mathbin{+\!\!+} (\ell)) \wedge \mathsf{Z} \prec \mathsf{Z}`$：
  最後の連言子は [T.not_olt_Z](Term-ja.md#t-not_olt_Z) に矛盾する。

よって第 2 選言のみが可能であり

```math
\text{(argA)}\qquad \mathrm{tr}\,S \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell)).
```

**ステップ 6：文脈による合同。**
(argA) に [T.olt_P_b](Term-ja.md#t-olt_P_b) を $`a := w_0`$、$`c_1 := \mathsf{Z}`$、$`c_2 := \mathsf{Z}`$
として適用すると

```math
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
  \prec \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

であるから、$`\preceq`$ の定義（D.ole）の第 1 選言により

```math
\text{(leadle)}\qquad
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
  \preceq \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

が成り立つ。(st1) を (cpcons) で書き換えたもの、および (st2) を
$`B \mathbin{+\!\!+} (\ell) = (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))`$ で書き換えたものにより、
(leadle) は [T.cnf_ctx_cong](Cnf-2-ja.md#t-cnf_ctx_cong) の仮定 (leadle) の形をしている。

また (decr) を (cpcons) と $`B \mathbin{+\!\!+} (\ell) = (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))`$ で
書き換えると

```math
\text{(decr')}\qquad
\mathrm{tr}\bigl((v_0,w_0) :: S\bigr) \prec \mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
```

である。(tlgt) から

```math
\text{(r1)}\qquad \forall x \in S,\ \bigl((v_0,w_0)\bigr)_1 \le x_1
```

も得られる。

[T.cnf_ctx_cong](Cnf-2-ja.md#t-cnf_ctx_cong) を

```math
z_1 := (v_0,w_0),\quad T_1 := S,\quad
z_2 := (v_0,w_0),\quad T_2 := R \mathbin{+\!\!+} (\ell),\quad G := G
```

として適用する。その 7 つの仮定は次のように満たされる。

- $`\mathrm{cnf}(\mathrm{tr}(z_1 :: T_1))`$：ステップ 4 の (cCopies)（(cpcons) による）。
- $`\mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2)`$：(decr')。
- $`(z_1)_1 = (z_2)_1`$：両辺とも $`v_0`$ であり $`=`$ の反射性による。
- (leadle)：ステップ 6 の (leadle)。
- $`\forall x \in T_1,\ (z_1)_1 \le x_1`$：(r1)。
- $`\forall x \in T_2,\ (z_2)_1 \le x_1`$：ステップ 3 の (rT)。
- $`\mathrm{cnf}(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2))`$：ステップ 3 の (cM')。

結論として $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} (v_0,w_0) :: S)\bigr)`$ を得る。
(cpcons) より $`(v_0,w_0) :: S = \mathrm{cp}_{d_0}(B, m+1) = \mathrm{cp}_{d_0}(B, n)`$ であるから、
これは求める $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n))\bigr)`$ である。∎

<a id="t-copies_replicate"></a>
## 定理: 平行移動量 0 のコピー列は完全コピー (T.copies_replicate)

### 定理

$`B \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ に対し

```math
\mathrm{cp}_0(B, n) = B^{\ast n}
```

である。ここで $`B^{\ast n}`$ は [T.cnf_replicate_block](Cnf-ja.md#t-cnf_replicate_block) と同じく $`B`$ を
$`n`$ 個連結した列である。

### 証明

任意の $`k \in \mathbb{N}`$ について $`k \cdot 0 = 0`$ であり、
[T.shiftr0_zero](Cnf-2-ja.md#t-shiftr0_zero) より $`B^{+k\cdot 0} = B^{+0} = B`$ である。
すなわち $`\mathrm{cp}`$ の定義（D.copies）で $`\mathrm{range}(n)`$ の各要素 $`k`$ に対応させる列は
$`k`$ に依らず $`B`$ である。

したがって $`\mathrm{cp}_0(B,n)`$ は、$`\mathrm{range}(n)`$ の各要素を $`B`$ に写して得られる列の
並びを連結したものである。$`\lvert \mathrm{range}(n)\rvert = n`$ であるから、その並びは
$`B`$ を $`n`$ 個並べたものであり、その連結は $`B^{\ast n}`$ である。∎

<a id="t-cnf_oper"></a>
## 定理: 展開は CNF を保つ (T.cnf_oper)

### 定理

$`M \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とし、$`1 \le n`$ かつ
$`\mathrm{cnf}(\mathrm{tr}\,M)`$ を仮定する。このとき $`\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)`$（[D.oper](Pss-ja.md#d-oper)）。

### 証明

以下 $`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$（[D.idx1](Pss-ja.md#d-idx1)）と書く
（自然数の減法は切り捨て減法である）。$`j_1 = 0`$ か否かで場合分けする。

**(a) $`j_1 = 0`$ のとき。**
[T.oper_eq_self_of_short](Decrease-ja.md#t-oper_eq_self_of_short) より $`M[n] = M`$ である。
よって示すべきことは仮定 $`\mathrm{cnf}(\mathrm{tr}\,M)`$ そのものである。

以下 $`j_1 \ne 0`$ とする。このとき $`\lvert M\rvert - 1 \ne 0`$ であるから $`1 \lt \lvert M\rvert`$ で
ある。とくに $`M \ne ()`$ である（$`M = ()`$ なら $`\lvert M\rvert = 0`$ となり
$`1 \lt \lvert M\rvert`$ に反する）。また $`\neg(\lvert M\rvert \le 1)`$ であるから、
$`\mathrm{Pred}`$（[D.Pred](Pss-ja.md#d-Pred)）の定義（D.Pred）の第 2 の場合が選ばれ

```math
\text{(hPred)}\qquad \mathrm{Pred}\,M = \mathrm{dropLast}\,M
```

である。

**(b) $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$（[D.entry](Pss-ja.md#d-entry)）のとき。**
[T.oper_eq_pred_of_zero](Decrease-ja.md#t-oper_eq_pred_of_zero) より $`M[n] = \mathrm{Pred}\,M`$ で
あり、(hPred) より $`M[n] = \mathrm{dropLast}\,M`$ である。
$`M \ne ()`$ と仮定 $`\mathrm{cnf}(\mathrm{tr}\,M)`$ に [T.cnf_dropLast](Cnf-ja.md#t-cnf_dropLast) を適用して
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,M)\bigr)`$ を得る。

以下 $`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$ とする。
$`\mathrm{hasParent}(M, i_1, j_1)`$（[D.hasParent](Pss-ja.md#d-hasParent)）が成り立つか否かでさらに分ける。

**(c) $`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
[T.oper_eq_pred_of_noParent](Decrease-ja.md#t-oper_eq_pred_of_noParent) より
$`M[n] = \mathrm{Pred}\,M`$ であり、(hPred) より $`M[n] = \mathrm{dropLast}\,M`$ である。
$`M \ne ()`$ と仮定 $`\mathrm{cnf}(\mathrm{tr}\,M)`$ に [T.cnf_dropLast](Cnf-ja.md#t-cnf_dropLast) を適用して
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,M)\bigr)`$ を得る。

**(d) $`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
$`1 \lt \lvert M\rvert`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、
$`\mathrm{hasParent}(M, i_1, j_1)`$、$`1 \le n`$ が揃っているので
[T.oper_bad_blocks](Decrease-ja.md#t-oper_bad_blocks) を適用する。
$`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$
が得られ、$`B := (v_0,w_0) :: R`$ とおくと次が成り立つ（同定理の主張のうち、以下で
用いるものだけを挙げる。$`(5)`$ の 2 つの選言子の末尾の連言子は用いない）。

```math
\begin{aligned}
&(1)\ M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell), \cr
&(2)\ M[n] = G \mathbin{+\!\!+} B^{+0\cdot d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}, \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ v_0 \lt \ell_1, \cr
&(5)\ \bigl(d_0 = 0 \wedge \cdots\bigr) \ \vee\
        \bigl(0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0 \wedge \cdots\bigr).
\end{aligned}
```

(2) の右辺の $`G`$ より後ろの部分は、$`\mathrm{cp}`$ の定義（D.copies）そのものであるから

```math
\text{(2')}\qquad M[n] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n)
```

である。また (1) と仮定 $`\mathrm{cnf}(\mathrm{tr}\,M)`$ より

```math
\text{(cM')}\qquad \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))\bigr)
```

である。(5) の選言で場合分けする。

**(d-1) 第 1 選言子、とくに $`d_0 = 0`$ のとき。**
$`d_0 = 0`$ であるから [T.copies_replicate](#t-copies_replicate) により
$`\mathrm{cp}_{d_0}(B,n) = \mathrm{cp}_0(B,n) = B^{\ast n}`$ である。
[T.cnf_oper_i1eq0](Cnf-2-ja.md#t-cnf_oper_i1eq0) を (3)（仮定 (hR)）、(4)（仮定 (lpv)）、
$`1 \le n`$（仮定 (n1)）、(cM')（仮定 (cM)）に適用して

```math
\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B^{\ast n})\bigr)
```

を得る。これは (2') により $`\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)`$ である。

**(d-2) 第 2 選言子、とくに
$`0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0`$ のとき。**
[T.cnf_oper_i1eq1](#t-cnf_oper_i1eq1) を (3)（仮定 (hR)）、$`0 \lt d_0`$（仮定 (d0pos)）、
$`w_0 \lt \ell_2`$（仮定 (w0lt)）、$`\ell_1 = v_0 + d_0`$（仮定 (lphd)）、
$`1 \le n`$（仮定 (n1)）、(cM')（仮定 (cM)）に適用して

```math
\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n))\bigr)
```

を得る。これは (2') により $`\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)`$ である。

以上 (a)〜(d) で場合分けは尽きている。∎

<a id="t-cnf_ST_PS"></a>
## 定理: 標準形の翻訳は CNF (T.cnf_ST_PS)

### 定理

$`M \in \mathrm{ST\_PS}`$（[D.ST_PS](Pss-ja.md#d-ST_PS)）ならば $`\mathrm{cnf}(\mathrm{tr}\,M)`$。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法（[T.ST_PS.rec](Pss-ja.md#t-ST_PS.rec)）。

```math
\Phi(M) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}\,M\bigr)
```

を $`M`$ について示す。

$`\mathrm{ST\_PS}`$ の定義（D.ST_PS）の 2 つの規則に対応して次を示せばよい。

- **規則 (diag)**：$`\forall v \in \mathbb{N},\ \Phi(\Delta_0^v)`$（[D.diagSeq](Pss-ja.md#d-diagSeq)）。
  [T.cnf_diag](Cnf-ja.md#t-cnf_diag) がこれそのものである。

- **規則 (oper)**：$`M \in \mathrm{ST\_PS}`$、$`1 \le n`$、および帰納法の仮定 $`\Phi(M)`$、
  すなわち $`\mathrm{cnf}(\mathrm{tr}\,M)`$ を仮定して $`\Phi(M[n])`$ を示す。
  [T.cnf_oper](#t-cnf_oper) を $`1 \le n`$ と帰納法の仮定 $`\mathrm{cnf}(\mathrm{tr}\,M)`$ に
  適用すると $`\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)`$、すなわち $`\Phi(M[n])`$ を得る。

よって $`\forall M \in \mathrm{ST\_PS},\ \Phi(M)`$ が成り立つ。∎
