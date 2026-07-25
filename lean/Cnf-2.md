[← README](README.md) ｜ Cnf [1](Cnf.md) **2** [3](Cnf-3.md)

<a id="t-cnf_ctx_cong"></a>
## 定理: 条件の文脈による合同 (T.cnf_ctx_cong)

### 定理

$`z_1, z_2 \in \mathbb{N}\times\mathbb{N}`$、$`T_1, T_2, G \in \mathrm{PairSeq}`$ とし、次の 6 つを仮定する。

```math
\begin{aligned}
&\text{(cZ1)}\quad   &&\mathrm{cnf}\bigl(\mathrm{tr}(z_1 :: T_1)\bigr), \cr
&\text{(decr)}\quad  &&\mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2), \cr
&\text{(root)}\quad  &&(z_1)_1 = (z_2)_1, \cr
&\text{(leadle)}\quad&&\exists\, a_1, b_1, c_1, a_2, b_2, c_2,\ \bigl[\
   \mathrm{tr}(z_1 :: T_1) = \mathsf{P}(a_1,b_1,c_1) \cr
& &&\qquad\ \wedge\ \mathrm{tr}(z_2 :: T_2) = \mathsf{P}(a_2,b_2,c_2) \cr
& &&\qquad\ \wedge\ \mathsf{P}(a_1,b_1,\mathsf{Z}) \preceq \mathsf{P}(a_2,b_2,\mathsf{Z})\ \bigr], \cr
&\text{(r1)}\quad    &&\forall x \in T_1,\ (z_1)_1 \le x_1, \cr
&\text{(r2)}\quad    &&\forall x \in T_2,\ (z_2)_1 \le x_1 .
\end{aligned}
```

このとき $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2)\bigr)`$ ならば
$`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} z_1 :: T_1)\bigr)`$。

### 証明

$`z_1, z_2, T_1, T_2`$ と 6 つの仮定を固定し、$`\lvert G\rvert`$ に関する強帰納法を行う。
帰納法の述語は

```math
\Phi(G) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2)\bigr)
  \to \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} z_1 :: T_1)\bigr)
```

であり、帰納法の仮定は「$`\lvert G'\rvert \lt \lvert G\rvert`$ なるすべての $`G'`$ について $`\Phi(G')`$」である。
以下、(leadle) の $`a_1, b_1, c_1, a_2, b_2, c_2`$ を取り、

```math
\mathrm{tr}(z_1 :: T_1) = \mathsf{P}(a_1,b_1,c_1), \quad
\mathrm{tr}(z_2 :: T_2) = \mathsf{P}(a_2,b_2,c_2), \quad
\mathsf{P}(a_1,b_1,\mathsf{Z}) \preceq \mathsf{P}(a_2,b_2,\mathsf{Z})
```

と書く。

**$`G = ()`$ のとき。** $`() \mathbin{+\!\!+} z_1 :: T_1 = z_1 :: T_1`$ であるから、結論は (cZ1) そのものである。

**$`G = g :: G'`$ のとき。** $`G'`$ の全要素が $`g_1 \lt x_1`$ をみたすかどうかで場合分けする。

**(a) $`G'`$ のある要素 $`x`$ が $`\neg(g_1 \lt x_1)`$ をみたすとき。**
[T.takeWhile_append_not](Term.md#t-takeWhile_append_not) と
[T.dropWhile_append_not](Term.md#t-dropWhile_append_not) を $`xs := G'`$、$`ys := z_i :: T_i`$ に
適用すると、$`i = 1, 2`$ のいずれでも

```math
\mathrm{tw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = \mathrm{tw}_{g_1} G',
\qquad
\mathrm{dw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = \mathrm{dw}_{g_1} G' \mathbin{+\!\!+} z_i :: T_i
```

である。また $`\mathrm{dw}_{g_1} G' \ne ()`$ である。実際 $`\mathrm{dw}_{g_1} G' = ()`$ とすると
$`G'`$ の全要素が $`g_1 \lt x_1`$ をみたすことになり、$`x`$ について仮定に矛盾する。
そこで $`\mathrm{dw}_{g_1} G' = d :: D'`$ と書く。$`\mathrm{tr}`$ の定義（D.translate）より
$`i = 1, 2`$ のいずれでも

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_i :: T_i)\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}(\mathrm{tw}_{g_1} G'),\
      \mathrm{tr}((d :: D') \mathbin{+\!\!+} z_i :: T_i)\bigr)
```

であり、$`(d :: D') \mathbin{+\!\!+} z_i :: T_i = d :: (D' \mathbin{+\!\!+} z_i :: T_i)`$ であるから、
ふたたび定義より

```math
\mathrm{tr}\bigl((d :: D') \mathbin{+\!\!+} z_i :: T_i\bigr)
  = \mathsf{P}\bigl(d_2,\ A_i,\ \mathrm{tr}(\mathrm{dw}_{d_1}(D' \mathbin{+\!\!+} z_i :: T_i))\bigr),
\qquad
A_i := \mathrm{tr}\bigl(\mathrm{tw}_{d_1}(D' \mathbin{+\!\!+} z_i :: T_i)\bigr)
```

である。

[T.translate_ctx_cong](Term.md#t-translate_ctx_cong) を仮定 (decr), (root), (r1), (r2) と
$`G := d :: D'`$ に適用すると

```math
\mathrm{tr}\bigl((d :: D') \mathbin{+\!\!+} z_1 :: T_1\bigr)
  \prec \mathrm{tr}\bigl((d :: D') \mathbin{+\!\!+} z_2 :: T_2\bigr)
```

を得る。両辺を上の形に書き換えて [T.olt_P_P](Term.md#t-olt_P_P) を使うと、
次の 3 つのいずれかが成り立つ。

- $`d_2 \lt d_2`$。$`\lt`$ の非反射性によりこれは起こらない。
- $`d_2 = d_2 \wedge A_1 \prec A_2`$。
- $`d_2 = d_2 \wedge A_1 = A_2 \wedge (\cdots)`$。

したがって

```math
(\ast)\qquad A_1 \prec A_2 \ \vee\ A_1 = A_2
```

である。

次に前件 $`\mathrm{cnf}\bigl(\mathrm{tr}(g :: (G' \mathbin{+\!\!+} z_2 :: T_2))\bigr)`$ を上の形に書き換え、
[T.cnf_P_P](Cnf.md#t-cnf_P_P) を使うと次の 3 つを得る。

1. $`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{tw}_{g_1} G')\bigr)`$。
2. $`\neg\bigl(\mathsf{P}(g_2, \mathrm{tr}(\mathrm{tw}_{g_1} G'), \mathsf{Z}) \prec \mathsf{P}(d_2, A_2, \mathsf{Z})\bigr)`$。
3. $`\mathrm{cnf}\bigl(\mathsf{P}(d_2, A_2, \mathrm{tr}(\mathrm{dw}_{d_1}(D' \mathbin{+\!\!+} z_2 :: T_2)))\bigr)`$、
   すなわち $`\mathrm{cnf}\bigl(\mathrm{tr}((d :: D') \mathbin{+\!\!+} z_2 :: T_2)\bigr)`$。

$`d :: D' = \mathrm{dw}_{g_1} G'`$ は $`G'`$ の部分列であるから
$`\lvert d :: D'\rvert \le \lvert G'\rvert \lt \lvert g :: G'\rvert`$ であり、帰納法の仮定を
$`G' := d :: D'`$ に適用できる。3 とあわせて

```math
\mathrm{cnf}\bigl(\mathrm{tr}((d :: D') \mathbin{+\!\!+} z_1 :: T_1)\bigr)
```

を得る。

次に

```math
\neg\bigl(\mathsf{P}(g_2,\ \mathrm{tr}(\mathrm{tw}_{g_1} G'),\ \mathsf{Z})
  \prec \mathsf{P}(d_2,\ A_1,\ \mathsf{Z})\bigr)
```

を示す。内側が成り立つとすると [T.olt_P_P](Term.md#t-olt_P_P) より次の 3 つのいずれかである。

- $`g_2 \lt d_2`$。このとき [T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 1 選言により
  $`\mathsf{P}(g_2, \mathrm{tr}(\mathrm{tw}_{g_1} G'), \mathsf{Z}) \prec \mathsf{P}(d_2, A_2, \mathsf{Z})`$
  であり、2 に矛盾する。
- $`g_2 = d_2 \wedge \mathrm{tr}(\mathrm{tw}_{g_1} G') \prec A_1`$。$`(\ast)`$ で場合分けする。
  $`A_1 \prec A_2`$ のときは [T.olt_trans](Term.md#t-olt_trans) より
  $`\mathrm{tr}(\mathrm{tw}_{g_1} G') \prec A_2`$。$`A_1 = A_2`$ のときは書き換えて同じ結論を得る。
  いずれの場合も [T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 2 選言により
  $`\mathsf{P}(g_2, \mathrm{tr}(\mathrm{tw}_{g_1} G'), \mathsf{Z}) \prec \mathsf{P}(d_2, A_2, \mathsf{Z})`$
  であり、2 に矛盾する。
- $`g_2 = d_2 \wedge \mathrm{tr}(\mathrm{tw}_{g_1} G') = A_1 \wedge \mathsf{Z} \prec \mathsf{Z}`$。
  [T.not_olt_Z](Term.md#t-not_olt_Z) に矛盾する。

最後に、$`i = 1`$ についての上の 2 つの式より

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_1 :: T_1)\bigr)
  = \mathsf{P}\Bigl(g_2,\ \mathrm{tr}(\mathrm{tw}_{g_1} G'),\
      \mathsf{P}\bigl(d_2,\ A_1,\ \mathrm{tr}(\mathrm{dw}_{d_1}(D' \mathbin{+\!\!+} z_1 :: T_1))\bigr)\Bigr)
```

であるから、[T.cnf_P_P](Cnf.md#t-cnf_P_P) に 1、いま示した否定、および帰納法の仮定から得た
$`\mathrm{cnf}\bigl(\mathrm{tr}((d :: D') \mathbin{+\!\!+} z_1 :: T_1)\bigr)`$ を与えると
$`\mathrm{cnf}\bigl(\mathrm{tr}(g :: (G' \mathbin{+\!\!+} z_1 :: T_1))\bigr)`$、すなわち $`\Phi(g :: G')`$ の結論を得る。

**(b) $`G'`$ の全要素が $`g_1 \lt x_1`$ をみたし、かつ $`g_1 \lt (z_1)_1`$ のとき。**
(root) より $`g_1 \lt (z_2)_1`$ でもある。(r1) より $`T_1`$ の任意の要素 $`x`$ について
$`g_1 \lt (z_1)_1 \le x_1`$ であるから、$`z_1 :: T_1`$ の全要素が $`g_1 \lt x_1`$ をみたす。
また (r2) より $`T_2`$ の任意の要素 $`x`$ について $`g_1 \lt (z_2)_1 \le x_1`$ であるから、
$`z_2 :: T_2`$ の全要素も $`g_1 \lt x_1`$ をみたす。よって $`G' \mathbin{+\!\!+} z_i :: T_i`$ の全要素が
$`g_1 \lt x_1`$ をみたし、[T.translate_single_tree](Term.md#t-translate_single_tree) より
$`i = 1, 2`$ のいずれでも

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_i :: T_i)\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}(G' \mathbin{+\!\!+} z_i :: T_i),\ \mathsf{Z}\bigr)
```

である。前件をこの形に書き換え [T.cnf_P_Z](Cnf.md#t-cnf_P_Z) を使うと
$`\mathrm{cnf}\bigl(\mathrm{tr}(G' \mathbin{+\!\!+} z_2 :: T_2)\bigr)`$ を得る。
$`\lvert G'\rvert \lt \lvert g :: G'\rvert`$ であるから帰納法の仮定を $`G'`$ に適用して
$`\mathrm{cnf}\bigl(\mathrm{tr}(G' \mathbin{+\!\!+} z_1 :: T_1)\bigr)`$ を得る。
ふたたび [T.cnf_P_Z](Cnf.md#t-cnf_P_Z) より
$`\mathrm{cnf}\bigl(\mathrm{tr}(g :: (G' \mathbin{+\!\!+} z_1 :: T_1))\bigr)`$ が成り立つ。

**(c) $`G'`$ の全要素が $`g_1 \lt x_1`$ をみたし、かつ $`\neg\bigl(g_1 \lt (z_1)_1\bigr)`$ のとき。**
(root) より $`\neg\bigl(g_1 \lt (z_2)_1\bigr)`$ でもある。
[T.takeWhile_append_all](Term.md#t-takeWhile_append_all) と
[T.dropWhile_append_all](Term.md#t-dropWhile_append_all) より、$`i = 1, 2`$ のいずれでも

```math
\mathrm{tw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = G' \mathbin{+\!\!+} \mathrm{tw}_{g_1}(z_i :: T_i),
\qquad
\mathrm{dw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = \mathrm{dw}_{g_1}(z_i :: T_i)
```

であり、先頭の $`z_i`$ が述語を破るから $`\mathrm{tw}_{g_1}(z_i :: T_i) = ()`$、
$`\mathrm{dw}_{g_1}(z_i :: T_i) = z_i :: T_i`$ である。よって $`\mathrm{tr}`$ の定義（D.translate）と
(leadle) の 2 つの等式より

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_i :: T_i)\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}\,G',\ \mathsf{P}(a_i,b_i,c_i)\bigr)
```

である。前件をこの形（$`i = 2`$）に書き換え [T.cnf_P_P](Cnf.md#t-cnf_P_P) を使うと次の 3 つを得る。

1. $`\mathrm{cnf}(\mathrm{tr}\,G')`$。
2. $`\neg\bigl(\mathsf{P}(g_2, \mathrm{tr}\,G', \mathsf{Z}) \prec \mathsf{P}(a_2,b_2,\mathsf{Z})\bigr)`$。
3. $`\mathrm{cnf}\bigl(\mathsf{P}(a_2,b_2,c_2)\bigr)`$（これは使わない）。

ここで

```math
\neg\bigl(\mathsf{P}(g_2,\ \mathrm{tr}\,G',\ \mathsf{Z}) \prec \mathsf{P}(a_1,b_1,\mathsf{Z})\bigr)
```

を示す。内側が成り立つとすると、(leadle) の
$`\mathsf{P}(a_1,b_1,\mathsf{Z}) \preceq \mathsf{P}(a_2,b_2,\mathsf{Z})`$ と
[T.olt_ole_trans](Term.md#t-olt_ole_trans) より
$`\mathsf{P}(g_2, \mathrm{tr}\,G', \mathsf{Z}) \prec \mathsf{P}(a_2,b_2,\mathsf{Z})`$ となり、2 に矛盾する。

また (cZ1) と $`\mathrm{tr}(z_1 :: T_1) = \mathsf{P}(a_1,b_1,c_1)`$ より
$`\mathrm{cnf}\bigl(\mathsf{P}(a_1,b_1,c_1)\bigr)`$ である。
[T.cnf_P_P](Cnf.md#t-cnf_P_P) に 1、いま示した否定、およびこれを与えると
$`\mathrm{cnf}\bigl(\mathsf{P}(g_2, \mathrm{tr}\,G', \mathsf{P}(a_1,b_1,c_1))\bigr)`$、
すなわち $`\mathrm{cnf}\bigl(\mathrm{tr}(g :: (G' \mathbin{+\!\!+} z_1 :: T_1))\bigr)`$ を得る。

以上 3 つの場合すべてで $`\Phi(g :: G')`$ が示された。∎

<a id="t-cnf_tail"></a>
## 定理: 再開する後部分列は条件をみたす (T.cnf_tail)

### 定理

$`t \in \mathbb{N}\times\mathbb{N}`$、$`T', G \in \mathrm{PairSeq}`$ とし、
$`\forall x \in T',\ t_1 \le x_1`$ を仮定する。
$`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} t :: T')\bigr)`$ ならば $`\mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)`$。

### 証明

$`t, T'`$ と仮定 $`\forall x \in T',\ t_1 \le x_1`$ を固定し、$`\lvert G\rvert`$ に関する強帰納法を行う。
帰納法の述語は

```math
\Psi(G) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} t :: T')\bigr)
  \to \mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)
```

であり、帰納法の仮定は「$`\lvert G'\rvert \lt \lvert G\rvert`$ なるすべての $`G'`$ について $`\Psi(G')`$」である。

**$`G = ()`$ のとき。** $`() \mathbin{+\!\!+} t :: T' = t :: T'`$ であるから、結論は前件そのものである。

**$`G = g :: G'`$ のとき。** $`G'`$ の全要素が $`g_1 \lt x_1`$ をみたすかどうかで場合分けする。

**(a) $`G'`$ のある要素 $`x`$ が $`\neg(g_1 \lt x_1)`$ をみたすとき。**
[T.takeWhile_append_not](Term.md#t-takeWhile_append_not) と
[T.dropWhile_append_not](Term.md#t-dropWhile_append_not) を $`xs := G'`$、$`ys := t :: T'`$ に
適用して

```math
\mathrm{tw}_{g_1}(G' \mathbin{+\!\!+} t :: T') = \mathrm{tw}_{g_1} G',
\qquad
\mathrm{dw}_{g_1}(G' \mathbin{+\!\!+} t :: T') = \mathrm{dw}_{g_1} G' \mathbin{+\!\!+} t :: T'
```

を得る。また $`\mathrm{dw}_{g_1} G' \ne ()`$ である（$`\mathrm{dw}_{g_1} G' = ()`$ とすると $`G'`$ の
全要素が $`g_1 \lt x_1`$ をみたすことになり、$`x`$ について仮定に矛盾する）。
そこで $`\mathrm{dw}_{g_1} G' = d :: D'`$ と書くと、$`\mathrm{tr}`$ の定義（D.translate）より

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} t :: T')\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}(\mathrm{tw}_{g_1} G'),\
      \mathrm{tr}((d :: D') \mathbin{+\!\!+} t :: T')\bigr),
```
```math
\mathrm{tr}\bigl((d :: D') \mathbin{+\!\!+} t :: T'\bigr)
  = \mathsf{P}\bigl(d_2,\ \mathrm{tr}(\mathrm{tw}_{d_1}(D' \mathbin{+\!\!+} t :: T')),\
      \mathrm{tr}(\mathrm{dw}_{d_1}(D' \mathbin{+\!\!+} t :: T'))\bigr)
```

である（第 2 式では $`(d :: D') \mathbin{+\!\!+} t :: T' = d :: (D' \mathbin{+\!\!+} t :: T')`$ を使った）。
前件をこの形に書き換え [T.cnf_P_P](Cnf.md#t-cnf_P_P) を使うと、その右辺の第 3 連言子として
$`\mathrm{cnf}\bigl(\mathrm{tr}((d :: D') \mathbin{+\!\!+} t :: T')\bigr)`$ を得る。
$`d :: D' = \mathrm{dw}_{g_1} G'`$ は $`G'`$ の部分列であるから
$`\lvert d :: D'\rvert \le \lvert G'\rvert \lt \lvert g :: G'\rvert`$ であり、帰納法の仮定を
$`G' := d :: D'`$ に適用して $`\mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)`$ を得る。

**(b) $`G'`$ の全要素が $`g_1 \lt x_1`$ をみたし、かつ $`g_1 \lt t_1`$ のとき。**
仮定 $`\forall x \in T',\ t_1 \le x_1`$ より、$`T'`$ の任意の要素 $`x`$ について
$`g_1 \lt t_1 \le x_1`$ であるから、$`t :: T'`$ の全要素が $`g_1 \lt x_1`$ をみたす。
よって $`G' \mathbin{+\!\!+} t :: T'`$ の全要素が $`g_1 \lt x_1`$ をみたし、
[T.translate_single_tree](Term.md#t-translate_single_tree) より

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} t :: T')\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}(G' \mathbin{+\!\!+} t :: T'),\ \mathsf{Z}\bigr)
```

である。前件をこの形に書き換え [T.cnf_P_Z](Cnf.md#t-cnf_P_Z) を使うと
$`\mathrm{cnf}\bigl(\mathrm{tr}(G' \mathbin{+\!\!+} t :: T')\bigr)`$ を得る。
$`\lvert G'\rvert \lt \lvert g :: G'\rvert`$ であるから帰納法の仮定を $`G'`$ に適用して
$`\mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)`$ を得る。

**(c) $`G'`$ の全要素が $`g_1 \lt x_1`$ をみたし、かつ $`\neg(g_1 \lt t_1)`$ のとき。**
[T.takeWhile_append_all](Term.md#t-takeWhile_append_all) と
[T.dropWhile_append_all](Term.md#t-dropWhile_append_all) より

```math
\mathrm{tw}_{g_1}(G' \mathbin{+\!\!+} t :: T') = G' \mathbin{+\!\!+} \mathrm{tw}_{g_1}(t :: T'),
\qquad
\mathrm{dw}_{g_1}(G' \mathbin{+\!\!+} t :: T') = \mathrm{dw}_{g_1}(t :: T')
```

であり、先頭の $`t`$ が述語を破るから $`\mathrm{tw}_{g_1}(t :: T') = ()`$、
$`\mathrm{dw}_{g_1}(t :: T') = t :: T'`$ である。よって $`\mathrm{tr}`$ の定義（D.translate）より

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} t :: T')\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}\,G',\ \mathrm{tr}(t :: T')\bigr),
```
```math
\mathrm{tr}(t :: T')
  = \mathsf{P}\bigl(t_2,\ \mathrm{tr}(\mathrm{tw}_{t_1} T'),\ \mathrm{tr}(\mathrm{dw}_{t_1} T')\bigr)
```

である。前件をこの形に書き換え [T.cnf_P_P](Cnf.md#t-cnf_P_P) を使うと、その右辺の第 3 連言子が
$`\mathrm{cnf}\bigl(\mathsf{P}(t_2, \mathrm{tr}(\mathrm{tw}_{t_1} T'), \mathrm{tr}(\mathrm{dw}_{t_1} T'))\bigr)`$、
すなわち $`\mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)`$ である。

以上 3 つの場合すべてで $`\Psi(g :: G')`$ が示された。∎

<a id="t-cnf_oper_i1eq0"></a>
## 定理: 完全コピー分岐での CNF 保存 (T.cnf_oper_i1eq0)

### 定理

$`v_0, w_0 \in \mathbb{N}`$、$`R, G \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、
$`n \in \mathbb{N}`$ とする。以下 $`B := (v_0,w_0) :: R`$ とおき、列を $`k`$ 個連結する記法
$`L^{\ast k}`$ は [T.cnf_replicate_block](Cnf.md#t-cnf_replicate_block) のものを用いる。
次の 4 つを仮定する。

```math
\begin{aligned}
&\text{(hR)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(lpv)}\quad v_0 \lt \ell_1, \cr
&\text{(n1)}\quad 1 \le n, \cr
&\text{(cM)}\quad \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))\bigr).
\end{aligned}
```

このとき

```math
\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B^{\ast n})\bigr).
```

### 証明

(n1) より $`n = m + 1`$ をみたす $`m \in \mathbb{N}`$ が取れる（$`m := n - 1`$ とおけばよい）。
以下 $`T := B^{\ast m}`$ と略記する。

**第 1 段：2 つの列の翻訳の形。**

まず $`R \mathbin{+\!\!+} (\ell)`$ の全要素 $`x`$ が $`v_0 \lt x_1`$ をみたす。実際、
$`x \in R`$ のときは (hR)、$`x = \ell`$ のときは (lpv) による。よって
[T.translate_single_tree](Term.md#t-translate_single_tree) を $`p := (v_0,w_0)`$、
$`R := R \mathbin{+\!\!+} (\ell)`$ に適用して

```math
\text{(A)}\qquad
\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

を得る。

次に $`L^{\ast k}`$ の定義と $`B = (v_0,w_0) :: R`$ から

```math
\text{(B)}\qquad
B^{\ast(m+1)} = B \mathbin{+\!\!+} T = (v_0,w_0) :: (R \mathbin{+\!\!+} T)
```

である。さらに $`T`$ について次が成り立つ。

```math
\text{(C)}\qquad T = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,T)_1\bigr).
```

実際、$`m = 0`$ のときは $`T = B^{\ast 0} = ()`$ であり第 1 選言が成り立つ。
$`m = m' + 1`$ のときは $`T = B \mathbin{+\!\!+} B^{\ast m'}`$ であってその先頭要素は
$`B`$ の先頭要素 $`(v_0,w_0)`$ であるから $`(\mathrm{head}\,T)_1 = v_0`$ であり、
$`\lt`$ の非反射性より $`\neg(v_0 \lt v_0)`$、すなわち第 2 選言が成り立つ。

(hR) と (C) に [T.translate_block_append](Term.md#t-translate_block_append) を適用して

```math
\text{(D)}\qquad
\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} T)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T\bigr)
```

を得る。

**第 2 段：ブロック本体の CNF。**

$`\mathbin{+\!\!+}`$ の結合則と $`B = (v_0,w_0) :: R`$ より

```math
G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell) = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
```

であるから、(cM) は $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell)))\bigr)`$
と同一の命題である。これを (cM') とよぶ。

第 1 段で示したとおり $`R \mathbin{+\!\!+} (\ell)`$ の全要素 $`x`$ は $`v_0 \lt x_1`$ をみたすから、
とくに

```math
\text{(rT)}\qquad \forall x \in R \mathbin{+\!\!+} (\ell),\ \bigl((v_0,w_0)\bigr)_1 \le x_1
```

である。[T.cnf_tail](#t-cnf_tail) を $`t := (v_0,w_0)`$、$`T' := R \mathbin{+\!\!+} (\ell)`$、$`G := G`$
として (rT) と (cM') に適用して

```math
\mathrm{cnf}\bigl(\mathrm{tr}((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell)))\bigr)
```

を得る。ここに (A) を代入すると $`\mathrm{cnf}\bigl(\mathsf{P}(w_0, \mathrm{tr}(R \mathbin{+\!\!+} (\ell)), \mathsf{Z})\bigr)`$
であり、[T.cnf_P_Z](Cnf.md#t-cnf_P_Z) より

```math
\mathrm{cnf}\bigl(\mathrm{tr}(R \mathbin{+\!\!+} (\ell))\bigr)
```

を得る。これに [T.cnf_snoc](Cnf.md#t-cnf_snoc) を $`D := R`$、$`m := \ell`$ として適用して

```math
\text{(cR)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}\,R\bigr)
```

を得る。

**第 3 段：コピー列そのものの CNF。**

[T.cnf_replicate_block](Cnf.md#t-cnf_replicate_block) を (hR)、(cR)、$`n := m+1`$ に適用して

```math
\text{(cZ1)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}(B^{\ast(m+1)})\bigr)
```

を得る。(B) によりこれは $`\mathrm{cnf}\bigl(\mathrm{tr}((v_0,w_0) :: (R \mathbin{+\!\!+} T))\bigr)`$ と同一の命題である。

**第 4 段：狭義減少と先頭主要項の比較。**

[T.translate_snoc_increase](Decrease.md#t-translate_snoc_increase) を $`C := R`$、$`m := \ell`$ に
適用して

```math
\text{(E)}\qquad \mathrm{tr}\,R \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell))
```

を得る。(E) に [T.olt_P_b](Term.md#t-olt_P_b) を $`a := w_0`$、$`c_1 := \mathrm{tr}\,T`$、
$`c_2 := \mathsf{Z}`$ として適用すると

```math
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T\bigr)
  \prec \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

であり、(D) と (A) を代入して

```math
\text{(decr)}\qquad
\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} T)\bigr)
  \prec \mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
```

を得る。同じく (E) に [T.olt_P_b](Term.md#t-olt_P_b) を $`c_1 := \mathsf{Z}`$、$`c_2 := \mathsf{Z}`$
として適用すると

```math
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathsf{Z}\bigr)
  \prec \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

であるから、$`\preceq`$ の定義（D.ole）の第 1 選言により

```math
\text{(leadle)}\qquad
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathsf{Z}\bigr)
  \preceq \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

が成り立つ。(D) の右辺の添字と引数はそれぞれ $`w_0`$, $`\mathrm{tr}\,R`$、(A) の右辺の添字と引数は
それぞれ $`w_0`$, $`\mathrm{tr}(R \mathbin{+\!\!+} (\ell))`$ であるから、(leadle) は
[T.cnf_ctx_cong](#t-cnf_ctx_cong) の仮定 (leadle) の形をしている。

**第 5 段：文脈による合同。**

$`T = B^{\ast m}`$ の各要素は $`B`$ の要素である。実際、$`T`$ は $`B`$ を $`m`$ 個連結した列だから、
$`x \in T`$ ならば $`x`$ はそのいずれかの $`B`$ の要素であり、$`B`$ は共通である。
$`B = (v_0,w_0) :: R`$ であるから $`x = (v_0,w_0)`$ または $`x \in R`$ であり、
前者では $`x_1 = v_0`$、後者では (hR) より $`v_0 \lt x_1`$ である。いずれの場合も $`v_0 \le x_1`$。
これと (hR) を合わせて

```math
\text{(r1)}\qquad \forall x \in R \mathbin{+\!\!+} T,\ \bigl((v_0,w_0)\bigr)_1 \le x_1
```

を得る。

[T.cnf_ctx_cong](#t-cnf_ctx_cong) を

```math
z_1 := (v_0,w_0),\quad T_1 := R \mathbin{+\!\!+} T,\quad
z_2 := (v_0,w_0),\quad T_2 := R \mathbin{+\!\!+} (\ell),\quad G := G
```

として適用する。その 7 つの仮定は次のように満たされる。

- $`\mathrm{cnf}(\mathrm{tr}(z_1 :: T_1))`$：第 3 段の (cZ1)（(B) による）。
- $`\mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2)`$：第 4 段の (decr)。
- $`(z_1)_1 = (z_2)_1`$：両辺とも $`v_0`$ であり $`=`$ の反射性による。
- (leadle)：第 4 段の (leadle) を (D), (A) と合わせたもの。
- $`\forall x \in T_1,\ (z_1)_1 \le x_1`$：第 5 段の (r1)。
- $`\forall x \in T_2,\ (z_2)_1 \le x_1`$：第 2 段の (rT)。
- $`\mathrm{cnf}(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2))`$：第 2 段の (cM')。

結論として $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} (v_0,w_0) :: (R \mathbin{+\!\!+} T))\bigr)`$ を得る。
(B) より $`(v_0,w_0) :: (R \mathbin{+\!\!+} T) = B^{\ast(m+1)} = B^{\ast n}`$ であるから、
これは求める $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B^{\ast n})\bigr)`$ である。∎

<a id="d-shiftr0"></a>
## 定義: 行 0 の平行移動 (D.shiftr0)

$`d \in \mathbb{N}`$、$`M \in \mathrm{PairSeq}`$ に対し、$`M`$ の各対の第 1 成分に一様に $`d`$ を
足した列を $`M^{+d}`$ と書く。すなわち $`M = (M_0, \dots, M_{X-1})`$、$`X = \lvert M\rvert`$ のとき

```math
M^{+d} := \bigl(\,(M_{0,0} + d,\ M_{1,0}),\ \dots,\ (M_{0,X-1} + d,\ M_{1,X-1})\,\bigr).
```

<a id="d-copies"></a>
## 定義: 上昇コピー列 (D.copies)

$`d, n \in \mathbb{N}`$、$`B \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{cp}_d(B, n) := B^{+0\cdot d} \mathbin{+\!\!+} B^{+1\cdot d} \mathbin{+\!\!+} \cdots
  \mathbin{+\!\!+} B^{+(n-1)d}
```

とおく。正確には、$`\mathrm{range}(n) := (0, 1, \dots, n-1)`$ の各要素 $`k`$ を列 $`B^{+kd}`$ に
写し、得られた $`n`$ 個の列を左から順に連結した列である。$`n = 0`$ のとき $`\mathrm{range}(0) = ()`$
であるから $`\mathrm{cp}_d(B,0) = ()`$ である。

<a id="t-shiftr0_zero"></a>
## 定理: 平行移動量 0 は恒等 (T.shiftr0_zero)

### 定理

任意の $`M \in \mathrm{PairSeq}`$ に対し $`M^{+0} = M`$。

### 証明

$`M^{+d}`$ の定義（D.shiftr0）より $`M^{+0}`$ の第 $`i`$ 要素は $`(M_{0,i} + 0,\ M_{1,i})`$ である。
$`\mathbb{N}`$ において $`M_{0,i} + 0 = M_{0,i}`$ であるから、これは $`(M_{0,i},\ M_{1,i}) = M_i`$、
すなわち $`M`$ の第 $`i`$ 要素に等しい。長さも $`\lvert M^{+0}\rvert = \lvert M\rvert`$ で一致する。∎

<a id="t-shiftr0_nil"></a>
## 定理: 空列の平行移動 (T.shiftr0_nil)

### 定理

任意の $`d \in \mathbb{N}`$ に対し $`()^{+d} = ()`$。

### 証明

$`M^{+d}`$ の定義（D.shiftr0）は $`M`$ の各要素を写す操作であり、$`M = ()`$ は要素をもたないから
結果も要素をもたない。∎

<a id="t-shiftr0_eq_nil"></a>
## 定理: 平行移動が空列になる条件 (T.shiftr0_eq_nil)

### 定理

$`d \in \mathbb{N}`$、$`M \in \mathrm{PairSeq}`$ に対し
$`M^{+d} = () \iff M = ()`$。

### 証明

$`M^{+d}`$ の定義（D.shiftr0）より $`\lvert M^{+d}\rvert = \lvert M\rvert`$ である。
列が空であることと長さが $`0`$ であることは同値であるから

```math
M^{+d} = () \iff \lvert M^{+d}\rvert = 0 \iff \lvert M\rvert = 0 \iff M = () . \qquad \blacksquare
```

<a id="t-translate_shiftr0"></a>
## 定理: 平行移動は翻訳を変えない (T.translate_shiftr0)

### 定理

$`d \in \mathbb{N}`$、$`M \in \mathrm{PairSeq}`$ に対し
$`\mathrm{tr}\,(M^{+d}) = \mathrm{tr}\,M`$。

### 証明

[T.translate_shift](Term.md#t-translate_shift) そのものである。∎

<a id="t-shiftr0_cons"></a>
## 定理: 先頭付き列の平行移動 (T.shiftr0_cons)

### 定理

$`d \in \mathbb{N}`$、$`p \in \mathbb{N}\times\mathbb{N}`$、$`M \in \mathrm{PairSeq}`$ に対し

```math
(p :: M)^{+d} = (p_1 + d,\ p_2) :: M^{+d} .
```

### 証明

$`M^{+d}`$ の定義（D.shiftr0）は各要素を $`q \mapsto (q_1 + d, q_2)`$ で写す操作であり、
この操作を $`p :: M`$ に施すと、先頭要素 $`p`$ が $`(p_1 + d, p_2)`$ に写り、残りの列 $`M`$ が
$`M^{+d}`$ に写る。∎

<a id="t-mem_shiftr0"></a>
## 定理: 平行移動列の要素判定 (T.mem_shiftr0)

### 定理

$`d \in \mathbb{N}`$、$`M \in \mathrm{PairSeq}`$、$`x \in \mathbb{N}\times\mathbb{N}`$ に対し

```math
x \in M^{+d} \iff \exists p \in M,\ (p_1 + d,\ p_2) = x .
```

### 証明

$`M^{+d}`$ の定義（D.shiftr0）より $`M^{+d}`$ は $`M`$ の各要素 $`p`$ を $`(p_1+d, p_2)`$ に
写した列である。写した列の要素であることは、写す前の列にその原像が存在することと同値である。∎

<a id="t-copies_zero"></a>
## 定理: コピー 0 個 (T.copies_zero)

### 定理

$`d \in \mathbb{N}`$、$`B \in \mathrm{PairSeq}`$ に対し $`\mathrm{cp}_d(B, 0) = ()`$。

### 証明

$`\mathrm{cp}`$ の定義（D.copies）において $`\mathrm{range}(0) = ()`$ であり、
空列の各要素を写して連結した列は空列である。∎
