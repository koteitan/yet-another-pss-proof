[← README](README.md)

以下、$`M \in \mathrm{PairSeq}`$（[D.PairSeq](Pss.md#d-PairSeq)）に対し
$`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$（[D.idx1](Pss.md#d-idx1)）と書く。

<a id="t-oper_eq_self_of_short"></a>
## 定理: 短い列では展開は恒等 (T.oper_eq_self_of_short)

### 定理

$`j_1 = 0`$ ならば、任意の $`n`$ に対し $`M[n] = M`$（[D.oper](Pss.md#d-oper)）。

### 証明

$`M[n]`$ の定義（D.oper）の分岐 (a) の条件が仮定そのものである。∎

<a id="t-oper_eq_pred_of_zero"></a>
## 定理: 末尾が $`(0,0)`$ のときの展開 (T.oper_eq_pred_of_zero)

### 定理

$`j_1 \ne 0`$ かつ $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$（[D.entry](Pss.md#d-entry)）ならば、
任意の $`n`$ に対し $`M[n] = \mathrm{Pred}\,M`$（[D.Pred](Pss.md#d-Pred)）。

### 証明

$`M[n]`$ の定義（D.oper）の分岐 (a) の条件は $`j_1 = 0`$ であり、仮定によりこれは偽である。
分岐 (b) の条件が仮定の第 2 の連言子そのものであるから、分岐 (b) が選ばれる。∎

<a id="t-oper_eq_pred_of_noParent"></a>
## 定理: 親がないときの展開 (T.oper_eq_pred_of_noParent)

### 定理

$`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$（[D.hasParent](Pss.md#d-hasParent)）ならば、
任意の $`n`$ に対し $`M[n] = \mathrm{Pred}\,M`$。

### 証明

$`M[n]`$ の定義（D.oper）の分岐 (a), (b) の条件はいずれも仮定により偽である。
分岐 (c) の条件が仮定の第 3 の連言子そのものであるから、分岐 (c) が選ばれる。∎

<a id="t-oper_bad_unfold"></a>
## 定理: 展開の第 4 分岐の展開形 (T.oper_bad_unfold)

### 定理

$`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\mathrm{hasParent}(M, i_1, j_1)`$ とする。
$`j_0 := \mathrm{par}^M_{i_1}(j_1)`$（[D.parent](Pss.md#d-parent)）、

```math
d_0 := \begin{cases} M_{0,j_1} - M_{0,j_0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
```

とおくと、任意の $`n`$ に対し

```math
M[n] = (M_0, \dots, M_{j_0-1}) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1} .
```

すなわち **$`B_k`$ の第 2 成分には $`k`$ に依る項が現れない**。

### 証明

$`M[n]`$ の定義（D.oper）の分岐 (a), (b), (c) の条件はいずれも仮定により偽であるから、
分岐 (d) が選ばれる。その定義の $`B_k`$ は第 2 成分が $`M_{1,j} + k\,d_1`$ であり、

```math
d_1 = \begin{cases} M_{1,j_1} - M_{1,j_0} & (1 \lt i_1) \cr 0 & (i_1 \le 1) \end{cases}
```

であった。[T.idx1_le1](Term.md#t-idx1_le1) より $`i_1 \le 1`$ であるから条件 $`1 \lt i_1`$ は
偽であり、$`d_1 = 0`$ である。したがって第 2 成分は $`M_{1,j} + k\cdot 0 = M_{1,j}`$ である。∎

<a id="t-oper_eq_self_short"></a>
## 定理: 長さ 1 以下では展開は恒等 (T.oper_eq_self_short)

### 定理

$`\lvert M\rvert \le 1`$ ならば、任意の $`n`$ に対し $`M[n] = M`$。

### 証明

自然数の減法は切り捨て減法であるから、$`\lvert M\rvert \le 1`$ のとき
$`j_1 = \lvert M\rvert - 1 = 0`$ である。
[T.oper_eq_self_of_short](#t-oper_eq_self_of_short) を適用する。∎

<a id="t-translate_snoc_increase"></a>
## 定理: 末尾への 1 列の付加は翻訳を真に増やす (T.translate_snoc_increase)

### 定理

任意の $`C \in \mathrm{PairSeq}`$、$`m \in \mathbb{N}\times\mathbb{N}`$ に対し

```math
\mathrm{tr}\,C \prec \mathrm{tr}\,(C \mathbin{+\!\!+} (m)) .
```

（$`\mathrm{tr}`$ [D.translate](Term.md#d-translate)、$`\prec`$ [D.olt](Term.md#d-olt)）

### 証明

$`\mathrm{tr}`$ の再帰に沿う帰納法（$`m`$ は固定しない：帰納法の述語を $`m`$ について
全称量化しておく）。帰納法の述語は

```math
\Psi(C) :\equiv \forall m,\ \mathrm{tr}\,C \prec \mathrm{tr}\,(C \mathbin{+\!\!+} (m)) .
```

- **基底段** $`C = ()`$：左辺は $`\mathsf{Z}`$、右辺は $`\mathrm{tr}\,(m)`$ である。
  $`\mathrm{tr}`$ の定義（D.translate）より $`\mathrm{tr}\,(m) = \mathsf{P}(m_2, \mathsf{Z}, \mathsf{Z})`$
  であるから、[T.olt_Z_P](Term.md#t-olt_Z_P) より $`\mathsf{Z} \prec \mathrm{tr}\,(m)`$。

**帰納段** $`C = p :: L`$：帰納法の仮定は $`\Psi(\mathrm{tw}_{p_1} L)`$ と
$`\Psi(\mathrm{dw}_{p_1} L)`$ である。$`L`$ の全要素が $`p_1 \lt x_1`$ をみたすかどうかで
場合分けする。

**(a) $`L`$ の全要素が $`p_1 \lt x_1`$ をみたすとき。**
このとき $`\mathrm{tw}_{p_1} L = L`$、$`\mathrm{dw}_{p_1} L = ()`$ であり、
[T.translate_single_tree](Term.md#t-translate_single_tree) より
$`\mathrm{tr}(p :: L) = \mathsf{P}(p_2, \mathrm{tr}\,L, \mathsf{Z})`$ である。
さらに $`m`$ が述語をみたすかどうかで分ける。

**$`p_1 \lt m_1`$ のとき。** $`L \mathbin{+\!\!+} (m)`$ の全要素も $`p_1 \lt x_1`$ をみたすから、
ふたたび [T.translate_single_tree](Term.md#t-translate_single_tree) より

```math
\mathrm{tr}\bigl(p :: (L \mathbin{+\!\!+} (m))\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}(L \mathbin{+\!\!+} (m)),\ \mathsf{Z}\bigr).
```

帰納法の仮定 $`\Psi(\mathrm{tw}_{p_1} L) = \Psi(L)`$ を $`m`$ に適用して
$`\mathrm{tr}\,L \prec \mathrm{tr}(L \mathbin{+\!\!+} (m))`$ を得る。
これに [T.olt_P_b](Term.md#t-olt_P_b) を適用すればよい。

**$`\neg(p_1 \lt m_1)`$ のとき。**[T.takeWhile_append_all](Term.md#t-takeWhile_append_all) と
[T.dropWhile_append_all](Term.md#t-dropWhile_append_all) より
$`\mathrm{tw}_{p_1}(L \mathbin{+\!\!+} (m)) = L`$、$`\mathrm{dw}_{p_1}(L \mathbin{+\!\!+} (m)) = (m)`$
であるから、$`\mathrm{tr}`$ の定義（D.translate）より

```math
\mathrm{tr}\bigl(p :: (L \mathbin{+\!\!+} (m))\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}\,L,\ \mathrm{tr}\,(m)\bigr).
```

左辺の後続和は $`\mathsf{Z}`$、右辺の後続和は $`\mathrm{tr}\,(m) = \mathsf{P}(m_2,\mathsf{Z},\mathsf{Z})`$
であり、[T.olt_Z_P](Term.md#t-olt_Z_P) より $`\mathsf{Z} \prec \mathrm{tr}\,(m)`$ である。
これに [T.olt_P_c](Term.md#t-olt_P_c) を適用すればよい。

**(b) $`L`$ のある要素 $`x`$ が $`\neg(p_1 \lt x_1)`$ をみたすとき。**
[T.takeWhile_append_not](Term.md#t-takeWhile_append_not) と
[T.dropWhile_append_not](Term.md#t-dropWhile_append_not) より

```math
\mathrm{tw}_{p_1}(L \mathbin{+\!\!+} (m)) = \mathrm{tw}_{p_1} L,
\qquad
\mathrm{dw}_{p_1}(L \mathbin{+\!\!+} (m)) = \mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m)
```

であるから、$`\mathrm{tr}`$ の定義（D.translate）より両辺は

```math
\mathrm{tr}(p :: L) = \mathsf{P}\bigl(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\ \mathrm{tr}(\mathrm{dw}_{p_1} L)\bigr),
```
```math
\mathrm{tr}\bigl(p :: (L \mathbin{+\!\!+} (m))\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\ \mathrm{tr}(\mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m))\bigr)
```

であり、添字と引数が共通である。帰納法の仮定 $`\Psi(\mathrm{dw}_{p_1} L)`$ を $`m`$ に適用して
$`\mathrm{tr}(\mathrm{dw}_{p_1} L) \prec \mathrm{tr}(\mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m))`$ を得る。
これに [T.olt_P_c](Term.md#t-olt_P_c) を適用すればよい。∎

<a id="t-translate_dropLast_decrease"></a>
## 定理: 末尾の 1 列を落とすと翻訳は真に減る (T.translate_dropLast_decrease)

### 定理

$`C \ne ()`$ ならば $`\mathrm{tr}\,(\mathrm{dropLast}\,C) \prec \mathrm{tr}\,C`$。
ここで $`\mathrm{dropLast}\,C`$ は $`C`$ の末尾 1 要素を落とした列である。

### 証明

$`C \ne ()`$ であるから、$`C`$ の最後の要素を $`\ell`$ とすると

```math
C = \mathrm{dropLast}\,C \mathbin{+\!\!+} (\ell)
```

である。[T.translate_snoc_increase](#t-translate_snoc_increase) を
$`C := \mathrm{dropLast}\,C`$、$`m := \ell`$ に適用すると

```math
\mathrm{tr}(\mathrm{dropLast}\,C) \prec \mathrm{tr}\bigl(\mathrm{dropLast}\,C \mathbin{+\!\!+} (\ell)\bigr)
= \mathrm{tr}\,C . \qquad \blacksquare
```

<a id="t-translate_takeWhile_snoc_le"></a>
## 定理: 先頭ブロックは末尾付加で減らない (T.translate_takeWhile_snoc_le)

### 定理

$`a \in \mathbb{N}`$、$`C \in \mathrm{PairSeq}`$、$`m \in \mathbb{N}\times\mathbb{N}`$ に対し

```math
\mathrm{tr}\bigl(\mathrm{tw}_a C\bigr) \preceq \mathrm{tr}\bigl(\mathrm{tw}_a (C \mathbin{+\!\!+} (m))\bigr)
```

（$`\preceq`$ [D.ole](Term.md#d-ole)）。

### 証明

$`C`$ の全要素が $`a \lt x_1`$ をみたすかどうかで場合分けする。

**(a) 全要素がみたすとき。** $`\mathrm{tw}_a C = C`$ である。$`m`$ について分ける。

- $`a \lt m_1`$ のとき。$`C \mathbin{+\!\!+} (m)`$ の全要素も述語をみたすから
  $`\mathrm{tw}_a(C \mathbin{+\!\!+} (m)) = C \mathbin{+\!\!+} (m)`$ である。
  [T.translate_snoc_increase](#t-translate_snoc_increase) より
  $`\mathrm{tr}\,C \prec \mathrm{tr}(C \mathbin{+\!\!+} (m))`$ であり、$`\preceq`$ の定義（D.ole）の
  第 1 選言が成り立つ。

- $`\neg(a \lt m_1)`$ のとき。[T.takeWhile_append_all](Term.md#t-takeWhile_append_all) より
  $`\mathrm{tw}_a(C \mathbin{+\!\!+} (m)) = C \mathbin{+\!\!+} \mathrm{tw}_a\,(m) = C`$ である
  （$`m`$ が述語を破るので $`\mathrm{tw}_a\,(m) = ()`$）。よって両辺は同一の項であり、
  $`\preceq`$ の定義（D.ole）の第 2 選言が成り立つ。

**(b) ある要素 $`x`$ が $`\neg(a \lt x_1)`$ をみたすとき。**
[T.takeWhile_append_not](Term.md#t-takeWhile_append_not) より
$`\mathrm{tw}_a(C \mathbin{+\!\!+} (m)) = \mathrm{tw}_a C`$ である。よって両辺は同一の項であり、
$`\preceq`$ の定義（D.ole）の第 2 選言が成り立つ。∎

<a id="t-core_i0"></a>
## 定理: 完全コピーの核 (T.core_i0)

### 定理

$`v_0, w_0 \in \mathbb{N}`$、$`R, T \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ とし、

```math
\forall x \in R,\ v_0 \lt x_1,
\qquad v_0 \lt \ell_1,
\qquad T = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,T)_1\bigr)
```

を仮定する。このとき

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} T\bigr)
  \prec \mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr).
```

### 証明

左辺は [T.translate_block_append](Term.md#t-translate_block_append) により

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} T\bigr) = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T\bigr)
```

である。右辺については、$`R \mathbin{+\!\!+} (\ell)`$ の全要素が $`v_0 \lt x_1`$ をみたす
（$`R`$ の要素は第 1 の仮定、$`\ell`$ は第 2 の仮定による）から、
[T.translate_single_tree](Term.md#t-translate_single_tree) により

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr)
= \mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
= \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

である。両者は添字が共通の $`w_0`$ であり、引数は
[T.translate_snoc_increase](#t-translate_snoc_increase) により
$`\mathrm{tr}\,R \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell))`$ をみたす。
[T.olt_P_b](Term.md#t-olt_P_b) を適用すればよい。∎

<a id="t-core_i1"></a>
## 定理: 上昇コピーの核 (T.core_i1)

### 定理

$`v_0, w_0 \in \mathbb{N}`$、$`R, C' \in \mathrm{PairSeq}`$、
$`c, \ell \in \mathbb{N}\times\mathbb{N}`$ とし、

```math
\forall x \in R,\ v_0 \lt x_1,
\qquad \forall x \in C',\ c_1 \le x_1,
\qquad c_1 = \ell_1,
\qquad v_0 \lt \ell_1,
\qquad c_2 \lt \ell_2
```

を仮定する。このとき

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (c :: C')\bigr)
  \prec \mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr).
```

### 証明

3 段に分ける。

**第 1 段：$`\mathrm{tr}(c :: C') \prec \mathrm{tr}\,(\ell)`$。**
[T.lead_translate](Term.md#t-lead_translate) より
$`\mathrm{lead}\,\mathrm{tr}(c :: C') = c_2`$ であり、仮定より $`c_2 \lt \ell_2`$ である。
一方 $`\mathrm{tr}`$ の定義（D.translate）より
$`\mathrm{tr}\,(\ell) = \mathsf{P}(\ell_2, \mathsf{Z}, \mathsf{Z})`$ である。
[T.olt_P_of_lead_lt](Term.md#t-olt_P_of_lead_lt) を
$`t := \mathrm{tr}(c :: C')`$、$`w := \ell_2`$ に適用して第 1 段を得る。

**第 2 段：$`\mathrm{tr}(R \mathbin{+\!\!+} c :: C') \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell))`$。**
[T.translate_ctx_cong](Term.md#t-translate_ctx_cong) を
$`z_1 := c`$、$`T_1 := C'`$、$`z_2 := \ell`$、$`T_2 := ()`$、$`G := R`$ として適用する。
4 つの仮定は次のように満たされる。

- (base)：第 1 段。
- (root)：$`c_1 = \ell_1`$ は仮定である。
- (r1)：$`\forall x \in C',\ c_1 \le x_1`$ は仮定である。
- (r2)：$`T_2 = ()`$ は要素をもたないから前件が偽であり、成り立つ。

**第 3 段：根 $`(v_0,w_0)`$ を被せる。**
$`R \mathbin{+\!\!+} c :: C'`$ の全要素 $`x`$ が $`v_0 \lt x_1`$ をみたすことを示す。
$`x \in R`$ のときは仮定による。$`x = c`$ のときは $`c_1 = \ell_1`$ と $`v_0 \lt \ell_1`$ から
$`v_0 \lt c_1`$。$`x \in C'`$ のときは、いま示した $`v_0 \lt c_1`$ と仮定 $`c_1 \le x_1`$ から
$`v_0 \lt x_1`$。同様に $`R \mathbin{+\!\!+} (\ell)`$ の全要素も $`v_0 \lt x_1`$ をみたす。

したがって [T.translate_single_tree](Term.md#t-translate_single_tree) により

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (c :: C')\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} c :: C'),\ \mathsf{Z}\bigr),
```
```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

である。第 2 段と [T.olt_P_b](Term.md#t-olt_P_b) から結論が従う。∎

<a id="t-translate_oper_pred"></a>
## 定理: 前者分岐での減少 (T.translate_oper_pred)

### 定理

$`1 \lt \lvert M\rvert`$ とし、

```math
\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr) \ \vee\ \neg\,\mathrm{hasParent}(M, i_1, j_1)
```

を仮定する。このとき任意の $`n`$ に対し $`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$。

### 証明

$`1 \lt \lvert M\rvert`$ より $`j_1 = \lvert M\rvert - 1 \ne 0`$ である。

まず $`M[n] = \mathrm{Pred}\,M`$ を示す。仮定の選言で場合分けする。第 1 選言のときは
[T.oper_eq_pred_of_zero](#t-oper_eq_pred_of_zero) による。第 2 選言のときは、
$`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ が成り立つかどうかでさらに分け、成り立つならふたたび
[T.oper_eq_pred_of_zero](#t-oper_eq_pred_of_zero)、成り立たないなら
[T.oper_eq_pred_of_noParent](#t-oper_eq_pred_of_noParent) による。

次に $`1 \lt \lvert M\rvert`$ より $`\neg(\lvert M\rvert \le 1)`$ であるから、
$`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合が選ばれ $`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。

最後に $`M \ne ()`$ である（$`M = ()`$ なら $`\lvert M\rvert = 0`$ となり
$`1 \lt \lvert M\rvert`$ に反する）。よって
[T.translate_dropLast_decrease](#t-translate_dropLast_decrease) が適用できて

```math
\mathrm{tr}\,(M[n]) = \mathrm{tr}(\mathrm{dropLast}\,M) \prec \mathrm{tr}\,M . \qquad \blacksquare
```

<a id="t-parent_nextR"></a>
## 定理: 親は親子関係をみたす (T.parent_nextR)

### 定理

$`\mathrm{hasParent}(M, i, j_1)`$ ならば
$`\mathrm{par}^M_i(j_1)`$ $`\to^M_i j_1`$（[D.nextR](Pss.md#d-nextR)）。

### 証明

$`\mathrm{hasParent}`$ の定義（D.hasParent）より、$`j_0 \to^M_i j_1`$ をみたす $`j_0`$ が存在する。
$`\mathrm{par}`$ の定義（D.parent）の $`\varepsilon`$ は、その条件をみたす値が存在するとき
条件をみたす値を返す。∎

<a id="t-nextR_index_lt"></a>
## 定理: 親子では添字が増える (T.nextR_index_lt)

### 定理

$`j_0 \to^M_i j_1`$ ならば $`j_0 \lt j_1`$。

### 証明

$`\to^M_i`$ の定義（D.nextR）の場合分けによる。$`i = 0`$ のときは $`j_0 \to^M_0 j_1`$ であり、
$`\to^M_0`$ の定義（D.nextrel0）の第 3 条件が $`j_0 \lt j_1`$ である。
$`i \ne 0`$ のときは $`j_0 \to^M_1 j_1`$ であり、$`\to^M_1`$ の定義（D.nextrel1）の
第 3 条件が $`j_0 \lt j_1`$ である。∎

<a id="t-nextR_chain0"></a>
## 定理: 親子は行 0 の祖先の鎖を与える (T.nextR_chain0)

### 定理

$`j_0 \to^M_i j_1`$ ならば $`j_0 \mathbin{(\to^M_0)^{*}} j_1`$。

### 証明

$`\to^M_i`$ の定義（D.nextR）の場合分けによる。

- $`i = 0`$ のとき。$`j_0 \to^M_0 j_1`$ であるから、長さ $`1`$ の鎖として
  $`j_0 \mathbin{(\to^M_0)^{*}} j_1`$ が成り立つ。

- $`i \ne 0`$ のとき。$`j_0 \to^M_1 j_1`$ であり、$`\to^M_1`$ の定義（D.nextrel1）の
  第 5 条件は $`j_0 \le^M_0 j_1`$ である。$`\le^M_0`$ の定義（D.le0）の第 3 条件が
  $`j_0 \mathbin{(\to^M_0)^{*}} j_1`$ である。∎

<a id="t-oper_bad_blocks"></a>
## 定理: 第 4 分岐のブロック分解 (T.oper_bad_blocks)

### 定理

$`1 \lt \lvert M\rvert`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、
$`\mathrm{hasParent}(M, i_1, j_1)`$、$`1 \le n`$ を仮定する。
このとき $`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、
$`\ell \in \mathbb{N}\times\mathbb{N}`$ が存在して次の 6 つが成り立つ。

```math
\begin{aligned}
&(1)\ M = G \mathbin{+\!\!+} ((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell), \cr
&(2)\ M[n] = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+0\cdot d_0}
        \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+(n-1)d_0}, \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ v_0 \lt \ell_1, \cr
&(5)\ \bigl(d_0 = 0 \wedge i_1 = 0\bigr) \ \vee\
        \bigl(0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0
              \wedge \lvert G\rvert \to^M_1 j_1\bigr), \cr
&(6)\ \lvert G\rvert \to^M_{i_1} j_1 .
\end{aligned}
```

ここで $`L^{+e}`$ は $`L`$ の各対の第 1 成分に $`e`$ を足した列である
（[T.translate_shift](Term.md#t-translate_shift) の記法）。

### 証明

$`j_0 := \mathrm{par}^M_{i_1}(j_1)`$ とおく。
[T.parent_nextR](#t-parent_nextR) より $`j_0 \to^M_{i_1} j_1`$ であり、
[T.nextR_index_lt](#t-nextR_index_lt) より $`j_0 \lt j_1`$、
[T.nextR_chain0](#t-nextR_chain0) より $`j_0 \mathbin{(\to^M_0)^{*}} j_1`$ である。
最後の事実に [T.le0_interval_gt](Term.md#t-le0_interval_gt) を適用して

```math
(\ast)\qquad \forall k,\ \bigl(j_0 \lt k \wedge k \le j_1\bigr) \to M_{0,j_0} \lt M_{0,k}
```

を得る。$`d_0`$ を [T.oper_bad_unfold](#t-oper_bad_unfold) と同じ式で定める。
求める対象を次のように取る。

```math
G := (M_0,\dots,M_{j_0-1}), \quad
v_0 := M_{0,j_0}, \quad
w_0 := M_{1,j_0},
```
```math
R := \bigl(\,(M_{0,j},\ M_{1,j})\,\bigr)_{j=j_0+1}^{j_1-1}, \quad
\ell := M\langle j_1\rangle .
```

$`\lvert G\rvert = j_0`$ である（$`j_0 \lt j_1 \lt \lvert M\rvert`$ なので先頭 $`j_0`$ 要素が
ちょうど取れる）。以下 6 つを順に示す。

**(1)** $`M`$ を位置 $`j_0`$ で切ると $`M = G \mathbin{+\!\!+} \mathrm{drop}_{j_0} M`$ である。
[T.drop_eq_map_getD](Term.md#t-drop_eq_map_getD) より

```math
\mathrm{drop}_{j_0} M = \bigl(M\langle j_0\rangle,\ M\langle j_0+1\rangle,\ \dots,\ M\langle j_1\rangle\bigr)
```

であり（$`\lvert M\rvert - j_0 = (j_1 - j_0) + 1`$ による）、
$`j \le j_1 \lt \lvert M\rvert`$ の範囲では $`M\langle j\rangle = (M_{0,j}, M_{1,j})`$ である
（$`M_{i,j}`$ の定義 D.entry）。先頭を切り出し末尾を切り出せば

```math
\mathrm{drop}_{j_0} M = \bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} (\ell)
```

となり、(1) を得る。

**(2)** [T.oper_bad_unfold](#t-oper_bad_unfold) より

```math
M[n] = G \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
```

である。添字 $`j`$ の範囲 $`[j_0, j_1)`$ を先頭 $`j_0`$ とそれ以降に分ければ、
$`B_k`$ の第 1 要素は $`(v_0 + k\,d_0,\ w_0)`$、残りは $`R`$ の各対の第 1 成分に
$`k\,d_0`$ を足したものである。すなわち $`B_k = ((v_0,w_0) :: R)^{+k\,d_0}`$ であり、(2) を得る。

**(3)** $`R`$ の要素は $`j_0 \lt j \lt j_1`$ なる $`j`$ について $`(M_{0,j}, M_{1,j})`$ の形である。
$`(\ast)`$ を $`k := j`$ に適用すると $`v_0 = M_{0,j_0} \lt M_{0,j}`$ を得る。

**(4)** $`(\ast)`$ を $`k := j_1`$ に適用する（$`j_0 \lt j_1`$ かつ $`j_1 \le j_1`$）。
$`\ell_1 = M_{0,j_1}`$ であるから $`v_0 \lt \ell_1`$。

**(5)** $`i_1`$ で場合分けする。

- $`i_1 = 0`$ のとき。$`d_0`$ の定義の条件 $`0 \lt i_1`$ が偽であるから $`d_0 = 0`$ であり、
  第 1 選言が成り立つ。

- $`0 \lt i_1`$ のとき。$`\to^M_i`$ の定義（D.nextR）より $`j_0 \to^M_{i_1} j_1`$ は
  $`j_0 \to^M_1 j_1`$ である。$`d_0 = M_{0,j_1} - M_{0,j_0}`$ であり、(4) の証明で得た
  $`M_{0,j_0} \lt M_{0,j_1}`$ から $`0 \lt d_0`$ および
  $`M_{0,j_1} = M_{0,j_0} + d_0`$、すなわち $`\ell_1 = v_0 + d_0`$ を得る。
  また $`\to^M_1`$ の定義（D.nextrel1）の第 4 条件は $`M_{1,j_0} \lt M_{1,j_1}`$、
  すなわち $`w_0 \lt \ell_2`$ である。$`\lvert G\rvert = j_0`$ であったから
  $`\lvert G\rvert \to^M_1 j_1`$ も成り立つ。よって第 2 選言が成り立つ。

**(6)** $`\lvert G\rvert = j_0`$ であり、$`j_0 \to^M_{i_1} j_1`$ は最初に示した。∎

<a id="t-translate_oper_bad"></a>
## 定理: 第 4 分岐での減少 (T.translate_oper_bad)

### 定理

$`1 \lt \lvert M\rvert`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、
$`\mathrm{hasParent}(M, i_1, j_1)`$、$`1 \le n`$ を仮定すると
$`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$。

### 証明

[T.oper_bad_blocks](#t-oper_bad_blocks) により $`G, v_0, w_0, R, d_0, \ell`$ を取る。
$`(v_0,w_0) :: R`$ を **基本ブロック**と呼ぶ。

**第 1 段：両辺を同じ形に整える。**
(2) の $`k = 0`$ の項は $`((v_0,w_0) :: R)^{+0} = (v_0,w_0) :: R`$ であるから、
$`k \ge 1`$ の項をまとめて

```math
C := \bigl((v_0,w_0) :: R\bigr)^{+1\cdot d_0} \mathbin{+\!\!+} \cdots
      \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+(n-1)d_0}
```

とおくと、(1)(2) は

```math
M[n] = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: (R \mathbin{+\!\!+} C)\bigr),
\qquad
M = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
```

と書ける。

**第 2 段：$`C`$ の要素はすべて行 0 が $`v_0`$ 以上。**
$`x \in C`$ とすると、ある $`k \ge 1`$ と基本ブロックの要素 $`p`$ について
$`x = (p_1 + k\,d_0,\ p_2)`$ である。$`p = (v_0,w_0)`$ なら $`p_1 = v_0`$、
$`p \in R`$ なら (3) より $`v_0 \lt p_1`$ であるから、いずれにせよ $`v_0 \le p_1`$。
したがって $`v_0 \le p_1 \le p_1 + k\,d_0 = x_1`$。

**第 3 段（核）：$`\mathrm{tr}(((v_0,w_0) :: R) \mathbin{+\!\!+} C) \prec \mathrm{tr}(((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell))`$。**
$`n`$ で場合分けする。

- **$`n = 1`$ のとき。** $`C`$ は空の連結であり $`C = ()`$ である。
  [T.core_i0](#t-core_i0) を $`T := ()`$ として適用する（第 3 の仮定の第 1 選言）。

**$`n \ge 2`$ のとき。** $`C`$ の先頭ブロックを取り出すと

```math
C = (v_0 + d_0,\ w_0) :: \Bigl(R^{+d_0} \mathbin{+\!\!+}
      \bigl((v_0,w_0) :: R\bigr)^{+2 d_0} \mathbin{+\!\!+} \cdots
      \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+(n-1)d_0}\Bigr)
```

である。(5) の選言で場合分けする。

- **$`d_0 = 0`$（完全コピー）のとき。** $`C`$ の先頭は $`(v_0 + 0,\ w_0) = (v_0, w_0)`$ で
  あるから $`\neg\bigl(v_0 \lt (\mathrm{head}\,C)_1\bigr)`$ である。
  [T.core_i0](#t-core_i0) を $`T := C`$ として適用する（第 3 の仮定の第 2 選言）。

- **$`0 \lt d_0`$（上昇コピー）のとき。**
  [T.core_i1](#t-core_i1) を $`c := (v_0 + d_0,\ w_0)`$、$`C' := C`$ の残り、として適用する。
  5 つの仮定を確認する。
  - $`\forall x \in R,\ v_0 \lt x_1`$：(3) である。
  - $`\forall x \in C',\ c_1 \le x_1`$：$`x`$ が $`R^{+d_0}`$ の要素なら、(3) より
    $`v_0 \lt p_1`$ なる $`p`$ について $`x_1 = p_1 + d_0 \ge v_0 + d_0 = c_1`$。
    $`x`$ が $`k \ge 2`$ のブロックの要素なら、第 2 段と同じ議論で $`v_0 \le p_1`$ であり、
    $`d_0 \le k\,d_0`$ であるから $`x_1 = p_1 + k\,d_0 \ge v_0 + d_0 = c_1`$。
  - $`c_1 = \ell_1`$：$`c_1 = v_0 + d_0`$ であり、(5) の第 2 選言に $`\ell_1 = v_0 + d_0`$ がある。
  - $`v_0 \lt \ell_1`$：(4) である。
  - $`c_2 \lt \ell_2`$：$`c_2 = w_0`$ であり、(5) の第 2 選言に $`w_0 \lt \ell_2`$ がある。

**第 4 段：良い部分 $`G`$ を通して持ち上げる。**
[T.translate_ctx_cong](Term.md#t-translate_ctx_cong) を
$`z_1 := (v_0,w_0)`$、$`T_1 := R \mathbin{+\!\!+} C`$、
$`z_2 := (v_0,w_0)`$、$`T_2 := R \mathbin{+\!\!+} (\ell)`$、$`G := G`$ として適用する。
4 つの仮定は次のように満たされる。

- (base)：第 3 段の結論を、$`((v_0,w_0) :: R) \mathbin{+\!\!+} X = (v_0,w_0) :: (R \mathbin{+\!\!+} X)`$
  と書き換えたものである。
- (root)：両辺の根は同一の $`(v_0,w_0)`$ であるから $`v_0 = v_0`$。
- (r1)：$`x \in R`$ なら (3) より $`v_0 \lt x_1`$、$`x \in C`$ なら第 2 段より $`v_0 \le x_1`$。
- (r2)：$`x \in R`$ なら同上、$`x = \ell`$ なら (4) より $`v_0 \lt \ell_1`$。

得られる結論は第 1 段の書き換えにより $`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$ である。∎

<a id="t-m_step_decreases"></a>
## 定理: 展開は測度を真に減らす (T.m_step_decreases)

### 定理

$`1 \lt \lvert M\rvert`$ かつ $`1 \le n`$ ならば
$`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$。

### 証明

$`M[n]`$ の定義（D.oper）の分岐に沿って場合分けする。$`1 \lt \lvert M\rvert`$ より
$`j_1 \ne 0`$ であるから、分岐 (a) は起こらない。

- $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。
  [T.translate_oper_pred](#t-translate_oper_pred) を第 1 選言で適用する。

- そうでなく $`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。
  [T.translate_oper_bad](#t-translate_oper_bad) を適用する。

- そうでなく $`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ のとき。
  [T.translate_oper_pred](#t-translate_oper_pred) を第 2 選言で適用する。

いずれの場合も結論が得られた。∎
