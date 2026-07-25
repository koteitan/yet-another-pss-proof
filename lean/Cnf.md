[← README](README.md)

<a id="t-getD_eq_getElem'"></a>
## 定理: 既定値つき添字づけの値 (T.getD_eq_getElem')

### 定理

$`l`$ を列、$`d`$ を既定値、$`i \in \mathbb{N}`$ とする。$`i \lt \lvert l\rvert`$ ならば

```math
l\langle i\rangle = l_i .
```

ここで $`l\langle i\rangle`$ は、$`i \lt \lvert l\rvert`$ のとき $`l`$ の第 $`i`$ 要素、そうでないとき $`d`$ を返す
操作であり、$`l_i`$ は $`i \lt \lvert l\rvert`$ の証拠を伴う第 $`i`$ 要素である。

### 証明

$`l\langle i\rangle`$ は次の 2 段の合成として定義されている。第 1 段は $`l`$ の第 $`i`$ 要素の探索であり、
$`i \lt \lvert l\rvert`$ のときは「第 $`i`$ 要素 $`l_i`$ が見つかった」という結果を、
$`\lvert l\rvert \le i`$ のときは「見つからなかった」という結果を返す。第 2 段はその結果に対し、
見つかったときはその値を、見つからなかったときは $`d`$ を返す。

仮定 $`i \lt \lvert l\rvert`$ より第 1 段は「$`l_i`$ が見つかった」を返すから、第 2 段の値は $`l_i`$ である。∎

<a id="t-oper_eq_dropLast_append"></a>
## 定理: 展開は末尾を落とした列への後続の連結 (T.oper_eq_dropLast_append)

### 定理

$`M \in \mathrm{PairSeq}`$（[D.PairSeq](Pss.md#d-PairSeq)）、$`n \in \mathbb{N}`$ とし、$`1 \lt \lvert M\rvert`$ と
$`1 \le n`$ を仮定する。このとき $`R \in \mathrm{PairSeq}`$ が存在して

```math
M[n] = \mathrm{dropLast}\,M \mathbin{+\!\!+} R
\qquad\text{かつ}\qquad
\mathrm{snd}(R) \subseteq \mathrm{snd}(\mathrm{dropLast}\,M)
```

が成り立つ。ここで $`\mathrm{dropLast}\,M`$ は $`M`$ の末尾 1 要素を落とした列である
（$`M[n]`$ [D.oper](Pss.md#d-oper)、$`\mathrm{snd}`$ [D.sndSet](Term.md#d-sndSet)）。

### 証明

$`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$（[D.idx1](Pss.md#d-idx1)）とおく。
$`1 \lt \lvert M\rvert`$ より $`j_1 \ne 0`$ であり、また $`\neg(\lvert M\rvert \le 1)`$ であるから
$`\mathrm{Pred}\,M`$（[D.Pred](Pss.md#d-Pred)）の定義（D.Pred）の第 2 の場合が選ばれて

```math
\mathrm{Pred}\,M = \mathrm{dropLast}\,M
```

である。次の 3 つの場合に分ける。

**(a) $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$（[D.entry](Pss.md#d-entry)）のとき。**
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) より
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。$`R := ()`$ と取る。
第 1 式は $`\mathrm{dropLast}\,M \mathbin{+\!\!+} () = \mathrm{dropLast}\,M`$ により成り立つ。
第 2 式は [T.sndSet_nil](Term.md#t-sndSet_nil) より $`\mathrm{snd}(()) = \emptyset`$ であり、
空集合は任意の集合の部分集合であるから成り立つ。

**(b) $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ かつ
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$（[D.hasParent](Pss.md#d-hasParent)）のとき。**
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) より
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。$`R := ()`$ と取る。
第 1 式は $`\mathrm{dropLast}\,M \mathbin{+\!\!+} () = \mathrm{dropLast}\,M`$ により成り立つ。
第 2 式は [T.sndSet_nil](Term.md#t-sndSet_nil) より $`\mathrm{snd}(()) = \emptyset`$ であり、
空集合は任意の集合の部分集合であるから成り立つ。

**(c) $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ かつ $`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) を適用して
$`G, R_0 \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ を取る。
その (1) と (2) は

```math
M = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R_0\bigr) \mathbin{+\!\!+} (\ell),
```
```math
M[n] = G \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} B_1 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k := \bigl((v_0,w_0) :: R_0\bigr)^{+k\,d_0}
```

である。ここで $`L^{+e}`$ は $`L`$ の各対の第 1 成分に $`e`$ を足した列である。

まず $`M`$ の末尾 1 要素は $`\ell`$ であるから、(1) より

```math
\mathrm{dropLast}\,M = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R_0\bigr)
```

である。次に $`1 \le n`$ であるから (2) の連結には $`B_0`$ が現れる。
$`B_0 = ((v_0,w_0) :: R_0)^{+0\cdot d_0}`$ は各対の第 1 成分に $`0`$ を足したものだから
$`B_0 = (v_0,w_0) :: R_0`$ である。そこで

```math
R := B_1 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1}
```

と取ると（$`n = 1`$ のときは $`R = ()`$）、(2) は

```math
M[n] = \Bigl(G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R_0\bigr)\Bigr) \mathbin{+\!\!+} R
  = \mathrm{dropLast}\,M \mathbin{+\!\!+} R
```

となり、第 1 式が成り立つ。

第 2 式を示す。$`y \in \mathrm{snd}(R)`$ とすると、[T.mem_sndSet](Term.md#t-mem_sndSet) より
$`p \in R`$ で $`p_2 = y`$ なるものが存在する。$`R`$ は $`B_1, \dots, B_{n-1}`$ の連結であるから、
ある $`k`$（$`1 \le k \le n-1`$）について $`p \in B_k`$ である。
$`B_k = ((v_0,w_0) :: R_0)^{+k\,d_0}`$ の要素は、$`q \in (v_0,w_0) :: R_0`$ について
$`(q_1 + k\,d_0,\ q_2)`$ の形であるから、$`p_2 = q_2`$、すなわち $`y = q_2`$ である。
いま $`q \in (v_0,w_0) :: R_0`$ であり、$`\mathrm{dropLast}\,M = G \mathbin{+\!\!+} ((v_0,w_0) :: R_0)`$
であるから $`q \in \mathrm{dropLast}\,M`$ である。ふたたび [T.mem_sndSet](Term.md#t-mem_sndSet) より
$`y \in \mathrm{snd}(\mathrm{dropLast}\,M)`$ を得る。∎

<a id="t-diagSeq_cons"></a>
## 定理: 対角列の先頭の切り出し (T.diagSeq_cons)

### 定理

$`u \le v`$ ならば $`\Delta_u^v = (u,u) :: \Delta_{u+1}^v`$（[D.diagSeq](Pss.md#d-diagSeq)）。

### 証明

$`\Delta_a^b`$ の定義（D.diagSeq）より、$`\Delta_u^v`$ は $`u`$ から始まる長さ $`v + 1 - u`$ の
連続整数列 $`(u,\ u+1,\ \dots)`$ の各項 $`j`$ を対 $`(j,j)`$ に写した列である。

仮定 $`u \le v`$ より $`v + 1 - u = \bigl(v + 1 - (u+1)\bigr) + 1`$ である。
長さ $`m + 1`$ の、$`u`$ から始まる連続整数列は、先頭の項 $`u`$ と、$`u+1`$ から始まる長さ $`m`$ の
連続整数列に分かれる。各項に $`j \mapsto (j,j)`$ を施すと、先頭は $`(u,u)`$ となり、
残りは $`u+1`$ から始まる長さ $`v + 1 - (u+1)`$ の連続整数列を写した列、
すなわち $`\Delta_{u+1}^v`$ である。∎

<a id="t-fst_in_diagSeq"></a>
## 定理: 対角列の要素の行 0 の下界 (T.fst_in_diagSeq)

### 定理

$`q \in \Delta_a^b`$ ならば $`a \le q_1`$。

### 証明

$`\Delta_a^b`$ の定義（D.diagSeq）より、$`q`$ はある $`j`$ について $`(j,j)`$ の形であり、
その $`j`$ は $`a`$ から始まる長さ $`b + 1 - a`$ の連続整数列の要素、すなわちある
$`i \lt b + 1 - a`$ について $`j = a + i`$ である。よって $`q_1 = a + i`$ であり、$`a \le a + i`$ である。∎

<a id="t-translate_diagSeq"></a>
## 定理: 対角列の翻訳 (T.translate_diagSeq)

### 定理

$`u \le v`$ ならば

```math
\mathrm{tr}(\Delta_u^v) = \mathsf{P}\bigl(u,\ \mathrm{tr}(\Delta_{u+1}^v),\ \mathsf{Z}\bigr)
```

（$`\mathrm{tr}`$ [D.translate](Term.md#d-translate)、$`\mathsf{Z}`$ と $`\mathsf{P}`$ [D.Three](Term.md#d-Three)）。

### 証明

[T.diagSeq_cons](#t-diagSeq_cons) より $`\Delta_u^v = (u,u) :: \Delta_{u+1}^v`$ である。
[T.translate_single_tree](Term.md#t-translate_single_tree) を $`p := (u,u)`$、
$`R := \Delta_{u+1}^v`$ として適用する。その仮定「$`R`$ の全要素 $`x`$ が $`p_1 \lt x_1`$ をみたす」は
次のように確かめられる。$`x \in \Delta_{u+1}^v`$ とすると
[T.fst_in_diagSeq](#t-fst_in_diagSeq) より $`u + 1 \le x_1`$ であり、したがって $`u \lt x_1`$ である。
$`p_1 = u`$ であるからこれが求める条件である。

結論は $`\mathrm{tr}((u,u) :: \Delta_{u+1}^v) = \mathsf{P}(p_2, \mathrm{tr}(\Delta_{u+1}^v), \mathsf{Z})`$
であり、$`p_2 = u`$ である。∎

<a id="d-cnf"></a>
## 定義: Cantor 標準形条件 (D.cnf)

$`\mathrm{Three}`$ 上の述語 $`\mathrm{cnf}`$ を、項の構造に関する再帰で定める。

```math
\begin{aligned}
\mathrm{cnf}(\mathsf{Z}) &:\iff \top, \cr
\mathrm{cnf}\bigl(\mathsf{P}(a,b,\mathsf{Z})\bigr) &:\iff \mathrm{cnf}(b), \cr
\mathrm{cnf}\bigl(\mathsf{P}(a,b,\mathsf{P}(e,f,g))\bigr) &:\iff
  \mathrm{cnf}(b)
  \ \wedge\ \neg\bigl(\mathsf{P}(a,b,\mathsf{Z}) \prec \mathsf{P}(e,f,\mathsf{Z})\bigr)
  \ \wedge\ \mathrm{cnf}\bigl(\mathsf{P}(e,f,g)\bigr).
\end{aligned}
```

第 1 引数の構成子と、それが $`\mathsf{P}`$ のときの第 3 引数の構成子で場合分けしており、
3 つの式は $`\mathrm{Three}`$ のすべての元を尽くし、互いに重ならない。
再帰呼び出しは第 2 式では $`b`$、第 3 式では $`b`$ と $`\mathsf{P}(e,f,g)`$ であり、
いずれも与えられた項の真部分項であるから、この定義は整合的である。

第 3 式の第 2 連言子
$`\neg\bigl(\mathsf{P}(a,b,\mathsf{Z}) \prec \mathsf{P}(e,f,\mathsf{Z})\bigr)`$（[D.olt](Term.md#d-olt)）は、
後続和の先頭の主要項から後続和を除いた $`\mathsf{P}(e,f,\mathsf{Z})`$ が、
先頭の主要項から後続和を除いた $`\mathsf{P}(a,b,\mathsf{Z})`$ より真に大きくないことを述べている。

<a id="t-cnf_Z"></a>
## 定理: $`\mathsf{Z}`$ は条件をみたす (T.cnf_Z)

### 定理

$`\mathrm{cnf}(\mathsf{Z})`$。

### 証明

$`\mathrm{cnf}`$ の定義（D.cnf）の第 1 式により $`\mathrm{cnf}(\mathsf{Z})`$ は $`\top`$ と定義により
同一の命題であり、$`\top`$ は成り立つ。∎

<a id="t-cnf_P_Z"></a>
## 定理: 後続和が $`\mathsf{Z}`$ のときの判定 (T.cnf_P_Z)

### 定理

任意の $`a \in \mathbb{N}`$, $`b \in \mathrm{Three}`$ に対し

```math
\mathrm{cnf}\bigl(\mathsf{P}(a,b,\mathsf{Z})\bigr) \iff \mathrm{cnf}(b).
```

### 証明

$`\mathrm{cnf}`$ の定義（D.cnf）の第 2 式そのものであり、両辺は定義により同一の命題である。∎

<a id="t-cnf_P_P"></a>
## 定理: 後続和が主要項のときの判定 (T.cnf_P_P)

### 定理

任意の $`a, e \in \mathbb{N}`$, $`b, f, g \in \mathrm{Three}`$ に対し

```math
\mathrm{cnf}\bigl(\mathsf{P}(a,b,\mathsf{P}(e,f,g))\bigr) \iff
  \mathrm{cnf}(b)
  \ \wedge\ \neg\bigl(\mathsf{P}(a,b,\mathsf{Z}) \prec \mathsf{P}(e,f,\mathsf{Z})\bigr)
  \ \wedge\ \mathrm{cnf}\bigl(\mathsf{P}(e,f,g)\bigr).
```

### 証明

$`\mathrm{cnf}`$ の定義（D.cnf）の第 3 式そのものであり、両辺は定義により同一の命題である。∎

<a id="t-cnf_translate_diagSeq_aux"></a>
## 定理: 対角列の翻訳は条件をみたす（一般の始点） (T.cnf_translate_diagSeq_aux)

### 定理

任意の $`n, u \in \mathbb{N}`$ に対し $`\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_u^{u+n})\bigr)`$。

### 証明

$`n`$ に関する帰納法を行う（$`u`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(n) :\equiv \forall u \in \mathbb{N},\ \mathrm{cnf}\bigl(\mathrm{tr}(\Delta_u^{u+n})\bigr).
```

**基底段** $`n = 0`$：$`u`$ を取る。$`u + 0 = u`$ である。
[T.translate_diagSeq](#t-translate_diagSeq) を $`u \le u`$ に適用して

```math
\mathrm{tr}(\Delta_u^u) = \mathsf{P}\bigl(u,\ \mathrm{tr}(\Delta_{u+1}^u),\ \mathsf{Z}\bigr)
```

を得る。$`\Delta_{u+1}^u`$ は $`\Delta_a^b`$ の定義（D.diagSeq）より長さ
$`u + 1 - (u + 1) = 0`$ の列、すなわち $`()`$ である。$`\mathrm{tr}`$ の定義（D.translate）より
$`\mathrm{tr}\,() = \mathsf{Z}`$ であるから $`\mathrm{tr}(\Delta_u^u) = \mathsf{P}(u, \mathsf{Z}, \mathsf{Z})`$
である。[T.cnf_P_Z](#t-cnf_P_Z) よりこれが条件をみたすことは $`\mathrm{cnf}(\mathsf{Z})`$ と同値であり、
それは [T.cnf_Z](#t-cnf_Z) である。よって $`\Phi(0)`$。

**帰納段** $`n \to n+1`$：帰納法の仮定は $`\Phi(n)`$、すなわち
$`\forall u,\ \mathrm{cnf}(\mathrm{tr}(\Delta_u^{u+n}))`$ である。$`u`$ を取る。
$`u \le u + (n+1)`$ であるから [T.translate_diagSeq](#t-translate_diagSeq) より

```math
\mathrm{tr}\bigl(\Delta_u^{u+(n+1)}\bigr)
  = \mathsf{P}\bigl(u,\ \mathrm{tr}\bigl(\Delta_{u+1}^{u+(n+1)}\bigr),\ \mathsf{Z}\bigr)
```

である。$`u + (n+1) = (u+1) + n`$ であるから
$`\Delta_{u+1}^{u+(n+1)} = \Delta_{u+1}^{(u+1)+n}`$ であり、帰納法の仮定 $`\Phi(n)`$ を
$`u := u + 1`$ に適用して $`\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_{u+1}^{(u+1)+n})\bigr)`$ を得る。
[T.cnf_P_Z](#t-cnf_P_Z) よりこれは
$`\mathrm{cnf}\bigl(\mathsf{P}(u, \mathrm{tr}(\Delta_{u+1}^{u+(n+1)}), \mathsf{Z})\bigr)`$ と同値であるから、
$`\Phi(n+1)`$ が成り立つ。∎

<a id="t-cnf_diag"></a>
## 定理: 対角列の翻訳は条件をみたす (T.cnf_diag)

### 定理

任意の $`v \in \mathbb{N}`$ に対し $`\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_0^v)\bigr)`$。

### 証明

[T.cnf_translate_diagSeq_aux](#t-cnf_translate_diagSeq_aux) を $`n := v`$、$`u := 0`$ に適用すると
$`\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_0^{0+v})\bigr)`$ を得る。$`0 + v = v`$ であるから、
これが求める主張である。∎

<a id="t-cnf_snoc"></a>
## 定理: 末尾に 1 列を付けた列が条件をみたせばもとの列もみたす (T.cnf_snoc)

### 定理

$`D \in \mathrm{PairSeq}`$、$`m \in \mathbb{N}\times\mathbb{N}`$ とする。
$`\mathrm{cnf}\bigl(\mathrm{tr}(D \mathbin{+\!\!+} (m))\bigr)`$ ならば $`\mathrm{cnf}(\mathrm{tr}\,D)`$。

### 証明

$`m`$ を固定し、$`\mathrm{tr}`$ の再帰に沿う帰納法を行う。帰納法の述語は

```math
\Psi(D) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(D \mathbin{+\!\!+} (m))\bigr) \to \mathrm{cnf}(\mathrm{tr}\,D).
```

**基底段** $`D = ()`$：結論は $`\mathrm{cnf}(\mathrm{tr}\,())`$ である。
$`\mathrm{tr}`$ の定義（D.translate）より $`\mathrm{tr}\,() = \mathsf{Z}`$ であり、
[T.cnf_Z](#t-cnf_Z) より $`\mathrm{cnf}(\mathsf{Z})`$ が成り立つ（前件は使わない）。

**帰納段** $`D = p :: L`$：帰納法の仮定は $`\Psi(\mathrm{tw}_{p_1} L)`$ と $`\Psi(\mathrm{dw}_{p_1} L)`$ である。
前件 $`\mathrm{cnf}\bigl(\mathrm{tr}((p :: L) \mathbin{+\!\!+} (m))\bigr)`$ を仮定する。
$`L`$ の全要素が $`p_1 \lt x_1`$ をみたすかどうかで場合分けする。

**(a) $`L`$ の全要素が $`p_1 \lt x_1`$ をみたすとき。**
このとき $`\mathrm{tw}_{p_1} L = L`$、$`\mathrm{dw}_{p_1} L = ()`$ であり、$`\mathrm{tr}`$ の定義（D.translate）より

```math
\mathrm{tr}(p :: L) = \mathsf{P}\bigl(p_2,\ \mathrm{tr}\,L,\ \mathsf{Z}\bigr)
```

である。$`m`$ が述語をみたすかどうかでさらに分ける。

**$`p_1 \lt m_1`$ のとき。** $`L \mathbin{+\!\!+} (m)`$ の全要素も $`p_1 \lt x_1`$ をみたすから
$`\mathrm{tw}_{p_1}(L \mathbin{+\!\!+} (m)) = L \mathbin{+\!\!+} (m)`$、$`\mathrm{dw}_{p_1}(L \mathbin{+\!\!+} (m)) = ()`$ であり、
$`(p :: L) \mathbin{+\!\!+} (m) = p :: (L \mathbin{+\!\!+} (m))`$ とあわせて $`\mathrm{tr}`$ の定義（D.translate）より

```math
\mathrm{tr}\bigl((p :: L) \mathbin{+\!\!+} (m)\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}(L \mathbin{+\!\!+} (m)),\ \mathsf{Z}\bigr)
```

である。前件にこれを代入し [T.cnf_P_Z](#t-cnf_P_Z) を使うと
$`\mathrm{cnf}\bigl(\mathrm{tr}(L \mathbin{+\!\!+} (m))\bigr)`$ を得る。
帰納法の仮定 $`\Psi(\mathrm{tw}_{p_1} L)`$ は $`\mathrm{tw}_{p_1} L = L`$ より $`\Psi(L)`$ であるから、
これを適用して $`\mathrm{cnf}(\mathrm{tr}\,L)`$ を得る。
ふたたび [T.cnf_P_Z](#t-cnf_P_Z) より $`\mathrm{cnf}\bigl(\mathsf{P}(p_2, \mathrm{tr}\,L, \mathsf{Z})\bigr)`$、
すなわち $`\mathrm{cnf}(\mathrm{tr}(p :: L))`$ が成り立つ。

**$`\neg(p_1 \lt m_1)`$ のとき。**
[T.takeWhile_append_all](Term.md#t-takeWhile_append_all) と
[T.dropWhile_append_all](Term.md#t-dropWhile_append_all) より
$`\mathrm{tw}_{p_1}(L \mathbin{+\!\!+} (m)) = L \mathbin{+\!\!+} \mathrm{tw}_{p_1}(m)`$、
$`\mathrm{dw}_{p_1}(L \mathbin{+\!\!+} (m)) = \mathrm{dw}_{p_1}(m)`$ であり、$`m`$ が述語を破るから
$`\mathrm{tw}_{p_1}(m) = ()`$、$`\mathrm{dw}_{p_1}(m) = (m)`$ である。よって

```math
\mathrm{tr}\bigl((p :: L) \mathbin{+\!\!+} (m)\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}\,L,\ \mathrm{tr}\,(m)\bigr)
```

である。さらに $`\mathrm{tr}`$ の定義（D.translate）より
$`\mathrm{tr}\,(m) = \mathsf{P}(m_2, \mathsf{Z}, \mathsf{Z})`$ である。
前件にこれらを代入し [T.cnf_P_P](#t-cnf_P_P) を使うと、その右辺の第 1 連言子として
$`\mathrm{cnf}(\mathrm{tr}\,L)`$ を得る。
[T.cnf_P_Z](#t-cnf_P_Z) より $`\mathrm{cnf}\bigl(\mathsf{P}(p_2, \mathrm{tr}\,L, \mathsf{Z})\bigr)`$、
すなわち $`\mathrm{cnf}(\mathrm{tr}(p :: L))`$ が成り立つ。

**(b) $`L`$ のある要素 $`x`$ が $`\neg(p_1 \lt x_1)`$ をみたすとき。**
[T.takeWhile_append_not](Term.md#t-takeWhile_append_not) と
[T.dropWhile_append_not](Term.md#t-dropWhile_append_not) より

```math
\mathrm{tw}_{p_1}(L \mathbin{+\!\!+} (m)) = \mathrm{tw}_{p_1} L,
\qquad
\mathrm{dw}_{p_1}(L \mathbin{+\!\!+} (m)) = \mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m)
```

である。また $`\mathrm{dw}_{p_1} L \ne ()`$ である。実際 $`\mathrm{dw}_{p_1} L = ()`$ とすると
$`L`$ の全要素が $`p_1 \lt x_1`$ をみたすことになり、$`x`$ について仮定に矛盾する。
そこで $`\mathrm{dw}_{p_1} L = q :: L_2`$ と書く。$`\mathrm{tr}`$ の定義（D.translate）より

```math
\mathrm{tr}(\mathrm{dw}_{p_1} L)
  = \mathsf{P}\bigl(q_2,\ \mathrm{tr}(\mathrm{tw}_{q_1} L_2),\ \mathrm{tr}(\mathrm{dw}_{q_1} L_2)\bigr),
```
```math
\mathrm{tr}\bigl(\mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m)\bigr)
  = \mathsf{P}\bigl(q_2,\ \mathrm{tr}(\mathrm{tw}_{q_1}(L_2 \mathbin{+\!\!+} (m))),\
      \mathrm{tr}(\mathrm{dw}_{q_1}(L_2 \mathbin{+\!\!+} (m)))\bigr)
```

である（第 2 式では $`(q :: L_2) \mathbin{+\!\!+} (m) = q :: (L_2 \mathbin{+\!\!+} (m))`$ を使った）。
以下 $`A := \mathrm{tr}(\mathrm{tw}_{q_1} L_2)`$、$`A' := \mathrm{tr}(\mathrm{tw}_{q_1}(L_2 \mathbin{+\!\!+} (m)))`$ と略記する。
[T.translate_takeWhile_snoc_le](Decrease.md#t-translate_takeWhile_snoc_le) より
$`A \preceq A'`$（[D.ole](Term.md#d-ole)）である。

前件は、$`\mathrm{tr}`$ の定義（D.translate）と上の 2 式により

```math
\mathrm{cnf}\Bigl(\mathsf{P}\bigl(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\
  \mathsf{P}(q_2,\ A',\ \mathrm{tr}(\mathrm{dw}_{q_1}(L_2 \mathbin{+\!\!+} (m))))\bigr)\Bigr)
```

と書ける。[T.cnf_P_P](#t-cnf_P_P) より次の 3 つが成り立つ。

1. $`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{tw}_{p_1} L)\bigr)`$。
2. $`\neg\bigl(\mathsf{P}(p_2, \mathrm{tr}(\mathrm{tw}_{p_1} L), \mathsf{Z}) \prec \mathsf{P}(q_2, A', \mathsf{Z})\bigr)`$。
3. $`\mathrm{cnf}\bigl(\mathsf{P}(q_2, A', \mathrm{tr}(\mathrm{dw}_{q_1}(L_2 \mathbin{+\!\!+} (m))))\bigr)`$、
   すなわち $`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m))\bigr)`$。

3 に帰納法の仮定 $`\Psi(\mathrm{dw}_{p_1} L)`$ を適用して
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dw}_{p_1} L)\bigr)`$ を得る。

次に

```math
\mathsf{P}(q_2,\ A,\ \mathsf{Z}) \preceq \mathsf{P}(q_2,\ A',\ \mathsf{Z})
```

を示す。$`A \preceq A'`$ は $`\preceq`$ の定義（D.ole）より $`A \prec A'`$ か $`A = A'`$ である。
前者のときは [T.olt_P_b](Term.md#t-olt_P_b) より
$`\mathsf{P}(q_2, A, \mathsf{Z}) \prec \mathsf{P}(q_2, A', \mathsf{Z})`$ であり、$`\preceq`$ の定義の第 1 選言が成り立つ。
後者のときは両辺が同一の項であり、第 2 選言が成り立つ。

これを用いて

```math
\neg\bigl(\mathsf{P}(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\ \mathsf{Z}) \prec \mathsf{P}(q_2,\ A,\ \mathsf{Z})\bigr)
```

を示す。左辺の内側が成り立つとすると、いま示した $`\preceq`$ と
[T.olt_ole_trans](Term.md#t-olt_ole_trans) より
$`\mathsf{P}(p_2, \mathrm{tr}(\mathrm{tw}_{p_1} L), \mathsf{Z}) \prec \mathsf{P}(q_2, A', \mathsf{Z})`$
となり、2 に矛盾する。

最後に $`\mathrm{tr}`$ の定義（D.translate）より

```math
\mathrm{tr}(p :: L) = \mathsf{P}\bigl(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\
  \mathsf{P}(q_2,\ A,\ \mathrm{tr}(\mathrm{dw}_{q_1} L_2))\bigr)
```

であり、[T.cnf_P_P](#t-cnf_P_P) に 1、いま示した否定、および
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dw}_{p_1} L)\bigr)`$（これは
$`\mathrm{cnf}\bigl(\mathsf{P}(q_2, A, \mathrm{tr}(\mathrm{dw}_{q_1} L_2))\bigr)`$ に他ならない）を与えると
$`\mathrm{cnf}(\mathrm{tr}(p :: L))`$ を得る。∎

<a id="t-cnf_dropLast"></a>
## 定理: 末尾の 1 列を落としても条件は保たれる (T.cnf_dropLast)

### 定理

$`C \in \mathrm{PairSeq}`$、$`C \ne ()`$ とする。$`\mathrm{cnf}(\mathrm{tr}\,C)`$ ならば
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,C)\bigr)`$。

### 証明

$`C \ne ()`$ であるから $`C`$ の最後の要素 $`\ell`$ が取れて

```math
C = \mathrm{dropLast}\,C \mathbin{+\!\!+} (\ell)
```

である。仮定 $`\mathrm{cnf}(\mathrm{tr}\,C)`$ はこれにより
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,C \mathbin{+\!\!+} (\ell))\bigr)`$ と書ける。
[T.cnf_snoc](#t-cnf_snoc) を $`D := \mathrm{dropLast}\,C`$、$`m := \ell`$ として適用すればよい。∎

<a id="t-cnf_take"></a>
## 定理: 前部分列でも条件は保たれる (T.cnf_take)

### 定理

$`M \in \mathrm{PairSeq}`$ とし $`\mathrm{cnf}(\mathrm{tr}\,M)`$ を仮定する。
このとき任意の $`k \in \mathbb{N}`$ に対し $`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}_k M)\bigr)`$。
ここで $`\mathrm{take}_k M`$ は $`M`$ の先頭 $`k`$ 要素からなる列であり、
$`\lvert M\rvert \le k`$ のときは $`M`$ 自身である。

### 証明

次の主張を示せば、$`d := \lvert M\rvert - k`$ として結論が得られる。

```math
\forall d,\ \forall k,\ \bigl(\lvert M\rvert - k = d\bigr) \to \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}_k M)\bigr).
```

$`d`$ に関する帰納法を行う（$`k`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Xi(d) :\equiv \forall k,\ \bigl(\lvert M\rvert - k = d\bigr)
  \to \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}_k M)\bigr).
```

**基底段** $`d = 0`$：$`k`$ を取り $`\lvert M\rvert - k = 0`$ とする。自然数の減法は切り捨て減法であるから
これは $`\lvert M\rvert \le k`$ を意味し、$`\mathrm{take}_k M = M`$ である。
結論は仮定 $`\mathrm{cnf}(\mathrm{tr}\,M)`$ そのものである。

**帰納段** $`d \to d+1`$：帰納法の仮定は $`\Xi(d)`$ である。$`k`$ を取り
$`\lvert M\rvert - k = d + 1`$ とする。$`\lvert M\rvert - k \ne 0`$ であるから $`k \lt \lvert M\rvert`$、
すなわち $`k + 1 \le \lvert M\rvert`$ である。また $`\lvert M\rvert - (k+1) = d`$ であるから、
帰納法の仮定 $`\Xi(d)`$ を $`k + 1`$ に適用して
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}_{k+1} M)\bigr)`$ を得る。

$`k + 1 \le \lvert M\rvert`$ より $`\lvert \mathrm{take}_{k+1} M\rvert = k + 1`$ であり、
$`k + 1 \ne 0`$ であるから $`\mathrm{take}_{k+1} M \ne ()`$ である。
さらに、長さ $`k+1`$ の列の末尾 1 要素を落とすとその先頭 $`k`$ 要素になるから

```math
\mathrm{dropLast}\bigl(\mathrm{take}_{k+1} M\bigr) = \mathrm{take}_k\bigl(\mathrm{take}_{k+1} M\bigr) = \mathrm{take}_k M
```

である（第 2 の等号は $`k \le k+1`$ による）。
[T.cnf_dropLast](#t-cnf_dropLast) を $`C := \mathrm{take}_{k+1} M`$ に適用して
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}_k M)\bigr)`$ を得る。よって $`\Xi(d+1)`$。∎

<a id="t-cnf_replicate_block"></a>
## 定理: 同一ブロックの反復は条件をみたす (T.cnf_replicate_block)

### 定理

$`v_0, w_0 \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ とし、
$`\forall x \in R,\ v_0 \lt x_1`$ と $`\mathrm{cnf}(\mathrm{tr}\,R)`$ を仮定する。
$`B := (v_0,w_0) :: R`$ とおく。また列 $`L`$ と $`k \in \mathbb{N}`$ に対し、$`L`$ を $`k`$ 個連結した
列を $`L^{\ast k}`$ と書く。すなわち

```math
L^{\ast 0} := (), \qquad L^{\ast(k+1)} := L \mathbin{+\!\!+} L^{\ast k} .
```

このとき任意の $`n \in \mathbb{N}`$ に対し $`\mathrm{cnf}\bigl(\mathrm{tr}(B^{\ast n})\bigr)`$。

### 証明

はじめに、任意の $`k \in \mathbb{N}`$ について

```math
(\ast)\qquad B^{\ast k} = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,B^{\ast k})_1\bigr)
```

が成り立つことを見る。$`k = 0`$ のときは $`B^{\ast 0} = ()`$ であり第 1 選言が成り立つ。
$`k = k' + 1`$ のときは $`B^{\ast(k'+1)} = B \mathbin{+\!\!+} B^{\ast k'}`$ の先頭は $`B`$ の先頭 $`(v_0,w_0)`$ であり、
$`\neg(v_0 \lt v_0)`$ であるから第 2 選言が成り立つ。

したがって [T.translate_block_append](Term.md#t-translate_block_append) を
$`T := B^{\ast k}`$ として適用でき、任意の $`k`$ について

```math
(\ast\ast)\qquad \mathrm{tr}\bigl(B^{\ast(k+1)}\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}(B^{\ast k})\bigr)
```

が成り立つ（第 1 の仮定が $`\forall x \in R,\ v_0 \lt x_1`$ である）。

$`n`$ に関する帰納法を行う。帰納法の述語は

```math
\Phi(n) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(B^{\ast n})\bigr).
```

**基底段** $`n = 0`$：$`B^{\ast 0} = ()`$ であり、$`\mathrm{tr}`$ の定義（D.translate）より
$`\mathrm{tr}\,() = \mathsf{Z}`$ である。[T.cnf_Z](#t-cnf_Z) より $`\Phi(0)`$。

**帰納段** $`n = m + 1`$：帰納法の仮定は $`\Phi(m)`$、すなわち
$`\mathrm{cnf}\bigl(\mathrm{tr}(B^{\ast m})\bigr)`$ である。$`m`$ で場合分けする。

**$`m = 0`$ のとき。** $`(\ast\ast)`$ を $`k := 0`$ として使うと

```math
\mathrm{tr}(B^{\ast 1}) = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,()\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathsf{Z}\bigr)
```

である。
[T.cnf_P_Z](#t-cnf_P_Z) よりこれが条件をみたすことは $`\mathrm{cnf}(\mathrm{tr}\,R)`$ と同値であり、
それは仮定である。よって $`\Phi(1)`$。

**$`m = m' + 1`$ のとき。** $`(\ast\ast)`$ を $`k := m`$ と $`k := m'`$ として使うと

```math
\mathrm{tr}\bigl(B^{\ast(m+1)}\bigr)
  = \mathsf{P}\Bigl(w_0,\ \mathrm{tr}\,R,\
      \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}(B^{\ast m'})\bigr)\Bigr)
```

である。[T.cnf_P_P](#t-cnf_P_P) により、これが条件をみたすためには次の 3 つを示せばよい。

1. $`\mathrm{cnf}(\mathrm{tr}\,R)`$：仮定である。
2. $`\neg\bigl(\mathsf{P}(w_0, \mathrm{tr}\,R, \mathsf{Z}) \prec \mathsf{P}(w_0, \mathrm{tr}\,R, \mathsf{Z})\bigr)`$：
   [T.olt_irrefl](Term.md#t-olt_irrefl) である。
3. $`\mathrm{cnf}\bigl(\mathsf{P}(w_0, \mathrm{tr}\,R, \mathrm{tr}(B^{\ast m'}))\bigr)`$：
   $`(\ast\ast)`$ を $`k := m'`$ として使うとこの項は $`\mathrm{tr}(B^{\ast(m'+1)}) = \mathrm{tr}(B^{\ast m})`$ であり、
   主張は帰納法の仮定 $`\Phi(m)`$ である。

よって $`\Phi(m+1)`$。∎

<a id="t-cnf_ctx_cong"></a>
## 定理: 条件の文脈による合同 (T.cnf_ctx_cong)

### 定理

$`z_1, z_2 \in \mathbb{N}\times\mathbb{N}`$、$`T_1, T_2, G \in \mathrm{PairSeq}`$ とし、次の 6 つを仮定する。

```math
\begin{aligned}
&\text{(cZ1)}\quad \mathrm{cnf}\bigl(\mathrm{tr}(z_1 :: T_1)\bigr), \cr
&\text{(decr)}\quad \mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2), \cr
&\text{(root)}\quad (z_1)_1 = (z_2)_1, \cr
&\text{(leadle)}\quad \exists\, a_1, b_1, c_1, a_2, b_2, c_2,\ \bigl[\
   \mathrm{tr}(z_1 :: T_1) = \mathsf{P}(a_1,b_1,c_1)
   \ \wedge\ \mathrm{tr}(z_2 :: T_2) = \mathsf{P}(a_2,b_2,c_2) \cr
&\hphantom{\text{(leadle)}\quad \exists\, a_1, b_1, c_1, a_2, b_2, c_2,\ \bigl[\ }
   \ \wedge\ \mathsf{P}(a_1,b_1,\mathsf{Z}) \preceq \mathsf{P}(a_2,b_2,\mathsf{Z})\ \bigr], \cr
&\text{(r1)}\quad \forall x \in T_1,\ (z_1)_1 \le x_1, \cr
&\text{(r2)}\quad \forall x \in T_2,\ (z_2)_1 \le x_1 .
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
[T.cnf_P_P](#t-cnf_P_P) を使うと次の 3 つを得る。

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

であるから、[T.cnf_P_P](#t-cnf_P_P) に 1、いま示した否定、および帰納法の仮定から得た
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

である。前件をこの形に書き換え [T.cnf_P_Z](#t-cnf_P_Z) を使うと
$`\mathrm{cnf}\bigl(\mathrm{tr}(G' \mathbin{+\!\!+} z_2 :: T_2)\bigr)`$ を得る。
$`\lvert G'\rvert \lt \lvert g :: G'\rvert`$ であるから帰納法の仮定を $`G'`$ に適用して
$`\mathrm{cnf}\bigl(\mathrm{tr}(G' \mathbin{+\!\!+} z_1 :: T_1)\bigr)`$ を得る。
ふたたび [T.cnf_P_Z](#t-cnf_P_Z) より
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

である。前件をこの形（$`i = 2`$）に書き換え [T.cnf_P_P](#t-cnf_P_P) を使うと次の 3 つを得る。

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
[T.cnf_P_P](#t-cnf_P_P) に 1、いま示した否定、およびこれを与えると
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
前件をこの形に書き換え [T.cnf_P_P](#t-cnf_P_P) を使うと、その右辺の第 3 連言子として
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

である。前件をこの形に書き換え [T.cnf_P_Z](#t-cnf_P_Z) を使うと
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

である。前件をこの形に書き換え [T.cnf_P_P](#t-cnf_P_P) を使うと、その右辺の第 3 連言子が
$`\mathrm{cnf}\bigl(\mathsf{P}(t_2, \mathrm{tr}(\mathrm{tw}_{t_1} T'), \mathrm{tr}(\mathrm{dw}_{t_1} T'))\bigr)`$、
すなわち $`\mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)`$ である。

以上 3 つの場合すべてで $`\Psi(g :: G')`$ が示された。∎

<a id="t-cnf_oper_i1eq0"></a>
## 定理: 完全コピー分岐での CNF 保存 (T.cnf_oper_i1eq0)

### 定理

$`v_0, w_0 \in \mathbb{N}`$、$`R, G \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、
$`n \in \mathbb{N}`$ とする。以下 $`B := (v_0,w_0) :: R`$ とおき、列を $`k`$ 個連結する記法
$`L^{\ast k}`$ は [T.cnf_replicate_block](#t-cnf_replicate_block) のものを用いる。
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
であり、[T.cnf_P_Z](#t-cnf_P_Z) より

```math
\mathrm{cnf}\bigl(\mathrm{tr}(R \mathbin{+\!\!+} (\ell))\bigr)
```

を得る。これに [T.cnf_snoc](#t-cnf_snoc) を $`D := R`$、$`m := \ell`$ として適用して

```math
\text{(cR)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}\,R\bigr)
```

を得る。

**第 3 段：コピー列そのものの CNF。**

[T.cnf_replicate_block](#t-cnf_replicate_block) を (hR)、(cR)、$`n := m+1`$ に適用して

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

<a id="t-copies_succ_front"></a>
## 定理: コピー列の先頭からの分解 (T.copies_succ_front)

### 定理

$`d, n \in \mathbb{N}`$、$`B \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{cp}_d(B, n+1) = B \mathbin{+\!\!+} \bigl(\mathrm{cp}_d(B, n)\bigr)^{+d} .
```

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
$`0 \cdot d = 0`$ であるから [T.shiftr0_zero](#t-shiftr0_zero) により $`B^{+0} = B`$。

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

を得る。[T.copies_zero](#t-copies_zero) より $`\mathrm{cp}_d(B,0) = ()`$ であり、
[T.shiftr0_nil](#t-shiftr0_nil) より $`()^{+d} = ()`$ である。
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
[T.mem_shiftr0](#t-mem_shiftr0) より、ある $`p \in (v_0,w_0) :: R`$ が存在して
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

- $`x \in (\mathrm{cp}_d(B, n-1))^{+d}`$ のとき。[T.mem_shiftr0](#t-mem_shiftr0) より、
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

このとき任意の $`n \in \mathbb{N}`$ に対し

```math
\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{cp}_{d_0}(B, n))\bigr).
```

### 証明

$`n`$ に関する自然数の帰納法。帰納法の述語は

```math
\Phi(n) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{cp}_{d_0}(B, n))\bigr).
```

**基底段** $`n = 0`$。
[T.copies_zero](#t-copies_zero) より $`\mathrm{cp}_{d_0}(B,0) = ()`$ であり、
$`\mathrm{tr}`$ の定義（D.translate）より $`\mathrm{tr}\,() = \mathsf{Z}`$ である。
[T.cnf_Z](#t-cnf_Z) より $`\mathrm{cnf}(\mathsf{Z})`$ が成り立つ。よって $`\Phi(0)`$。

**帰納段** $`n \to n+1`$：帰納法の仮定は $`\Phi(n)`$、すなわち
$`\mathrm{cnf}(\mathrm{tr}(\mathrm{cp}_{d_0}(B,n)))`$ である。$`n`$ で場合分けする。

**(i) $`n = 0`$ のとき。** 示すべきは $`\Phi(1)`$ である。
[T.copies_one](#t-copies_one) より $`\mathrm{cp}_{d_0}(B,1) = B`$ である。
また $`B \mathbin{+\!\!+} (\ell)`$ の末尾 1 要素を落とすと $`B`$ に戻るから
$`B = \mathrm{dropLast}\,(B \mathbin{+\!\!+} (\ell))`$ である。
$`B \mathbin{+\!\!+} (\ell)`$ は $`\ell`$ を要素にもつので空列ではない。
よって [T.cnf_dropLast](#t-cnf_dropLast) を $`C := B \mathbin{+\!\!+} (\ell)`$ に適用し、
(cBlp) から $`\mathrm{cnf}(\mathrm{tr}(B))`$、すなわち $`\Phi(1)`$ を得る。

**(ii) $`n = m + 1`$ のとき。** 示すべきは $`\Phi(m+2)`$ であり、帰納法の仮定は
$`\Phi(m+1)`$、すなわち $`\mathrm{cnf}(\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1)))`$ である。
以下 $`Q := \mathrm{cp}_{d_0}(B, m)`$、$`S := R \mathbin{+\!\!+} Q^{+d_0}`$ と略記する。

**第 1 段：$`\mathrm{cp}_{d_0}(B, m+1)`$ とその平行移動の形。**
[T.copies_succ_cons](#t-copies_succ_cons) より

```math
\text{(F)}\qquad \mathrm{cp}_{d_0}(B, m+1) = (v_0,w_0) :: S
```

である。これに [T.shiftr0_cons](#t-shiftr0_cons) を適用して

```math
\text{(G)}\qquad \bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)^{+d_0} = (v_0 + d_0,\ w_0) :: S^{+d_0}
```

を得る。

**第 2 段：翻訳の形。**
[T.copies_tl_gt](#t-copies_tl_gt) を (hR)、(d0pos)、$`n := m+1`$（$`1 \le m+1`$）に適用すると
$`n - 1 = m`$ であるから

```math
\text{(tlgt)}\qquad \forall x \in S,\ v_0 \lt x_1
```

を得る。(F) と [T.translate_single_tree](Term.md#t-translate_single_tree) より

```math
\text{(st1)}\qquad \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
```

である。また (G) と [T.translate_shiftr0](#t-translate_shiftr0) より

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

**第 3 段：狭義減少と先頭主要項の比較。**
(tZ1), (tlp) と [T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 1 選言 $`w_0 \lt \ell_2`$（(w0lt)）より

```math
\text{(decr)}\qquad \mathrm{tr}\bigl((v_0+d_0,\ w_0) :: S^{+d_0}\bigr) \prec \mathrm{tr}\,(\ell).
```

同じ第 1 選言により $`\mathsf{P}(w_0, \mathrm{tr}\,S, \mathsf{Z}) \prec \mathsf{P}(\ell_2, \mathsf{Z}, \mathsf{Z})`$
であるから、$`\preceq`$ の定義（D.ole）の第 1 選言により

```math
\text{(leadle)}\qquad
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
  \preceq \mathsf{P}\bigl(\ell_2,\ \mathsf{Z},\ \mathsf{Z}\bigr)
```

が成り立つ。(tZ1) の右辺の添字と引数は $`w_0`$, $`\mathrm{tr}\,S`$、(tlp) の右辺の添字と引数は
$`\ell_2`$, $`\mathsf{Z}`$ であるから、(leadle) は [T.cnf_ctx_cong](#t-cnf_ctx_cong) の仮定
(leadle) の形をしている。

**第 4 段：$`(v_0+d_0, w_0) :: S^{+d_0}`$ の CNF。**
(G) と [T.translate_shiftr0](#t-translate_shiftr0) より
$`\mathrm{tr}\bigl((v_0+d_0,w_0) :: S^{+d_0}\bigr) = \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B,m+1)\bigr)`$
であるから、帰納法の仮定 $`\Phi(m+1)`$ がそのまま

```math
\text{(cZ1)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}((v_0+d_0,\ w_0) :: S^{+d_0})\bigr)
```

を与える。

**第 5 段：文脈による合同。**
$`x \in S^{+d_0}`$ とすると、[T.mem_shiftr0](#t-mem_shiftr0) より、ある $`p \in S`$ が存在して
$`x = (p_1 + d_0,\ p_2)`$ である。(tlgt) より $`v_0 \lt p_1`$、とくに $`v_0 \le p_1`$ であるから

```math
\bigl((v_0+d_0,\ w_0)\bigr)_1 = v_0 + d_0 \le p_1 + d_0 = x_1 .
```

すなわち

```math
\text{(r1)}\qquad \forall x \in S^{+d_0},\ \bigl((v_0+d_0,\ w_0)\bigr)_1 \le x_1 .
```

また (lphd) より $`\bigl((v_0+d_0, w_0)\bigr)_1 = v_0 + d_0 = \ell_1`$ である。

[T.cnf_ctx_cong](#t-cnf_ctx_cong) を

```math
z_1 := (v_0+d_0,\ w_0),\quad T_1 := S^{+d_0},\quad
z_2 := \ell,\quad T_2 := (),\quad G := B
```

として適用する。その 7 つの仮定は次のように満たされる。

- $`\mathrm{cnf}(\mathrm{tr}(z_1 :: T_1))`$：第 4 段の (cZ1)。
- $`\mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2)`$：$`z_2 :: T_2 = (\ell)`$ であり、
  第 3 段の (decr)。
- $`(z_1)_1 = (z_2)_1`$：(lphd) による $`v_0 + d_0 = \ell_1`$。
- (leadle)：第 3 段の (leadle) を (tZ1), (tlp) と合わせたもの。
- $`\forall x \in T_1,\ (z_1)_1 \le x_1`$：第 5 段の (r1)。
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

**第 1 段：狭義減少 $`\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1)) \prec \mathrm{tr}(B \mathbin{+\!\!+} (\ell))`$。**

$`m`$ で場合分けする。

**(i) $`m = 0`$ のとき。** [T.copies_one](#t-copies_one) より
$`\mathrm{cp}_{d_0}(B,1) = B`$ であるから、
[T.translate_snoc_increase](Decrease.md#t-translate_snoc_increase) を $`C := B`$、$`m := \ell`$ に
適用して $`\mathrm{tr}\,B \prec \mathrm{tr}(B \mathbin{+\!\!+} (\ell))`$ を得る。

**(ii) $`m = m' + 1`$ のとき。**
$`Q' := \mathrm{cp}_{d_0}(B, m')`$、$`S' := R \mathbin{+\!\!+} Q'^{+d_0}`$ とおく。
[T.copies_succ_cons](#t-copies_succ_cons) より
$`\mathrm{cp}_{d_0}(B, m'+1) = (v_0,w_0) :: S'`$ であり、
[T.shiftr0_cons](#t-shiftr0_cons) より

```math
\text{(G')}\qquad \bigl(\mathrm{cp}_{d_0}(B, m'+1)\bigr)^{+d_0} = (v_0+d_0,\ w_0) :: S'^{+d_0} .
```

[T.copies_tl_gt](#t-copies_tl_gt) を (hR)、(d0pos)、$`n := m'+1`$ に適用して

```math
\text{(tlgt')}\qquad \forall x \in S',\ v_0 \lt x_1
```

を得る。$`x \in S'^{+d_0}`$ とすると [T.mem_shiftr0](#t-mem_shiftr0) より、ある $`p \in S'`$ が
存在して $`x = (p_1+d_0,\ p_2)`$ であり、(tlgt') から $`v_0 \le p_1`$、したがって

```math
\text{(Cge)}\qquad \forall x \in S'^{+d_0},\ v_0 + d_0 \le x_1 .
```

ここで [T.core_i1](Decrease.md#t-core_i1) を

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

**第 2 段：両辺の翻訳の形。**
[T.copies_succ_cons](#t-copies_succ_cons) より

```math
\text{(cpcons)}\qquad \mathrm{cp}_{d_0}(B, m+1) = (v_0,w_0) :: S
```

である。[T.copies_tl_gt](#t-copies_tl_gt) を (hR)、(d0pos)、$`n := m+1`$ に適用して

```math
\text{(tlgt)}\qquad \forall x \in S,\ v_0 \lt x_1
```

を得るから、[T.translate_single_tree](Term.md#t-translate_single_tree) より

```math
\text{(st1)}\qquad \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr).
```

また $`B \mathbin{+\!\!+} (\ell) = (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))`$ であり (Rlp) が成り立つから、
ふたたび [T.translate_single_tree](Term.md#t-translate_single_tree) より

```math
\text{(st2)}\qquad \mathrm{tr}\bigl(B \mathbin{+\!\!+} (\ell)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr).
```

**第 3 段：ブロックの CNF。**
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

であるから、[T.cnf_tail](#t-cnf_tail) を $`t := (v_0,w_0)`$、$`T' := R \mathbin{+\!\!+} (\ell)`$、
$`G := G`$ として適用して

```math
\text{(cBlp)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}(B \mathbin{+\!\!+} (\ell))\bigr)
```

を得る（$`B \mathbin{+\!\!+} (\ell) = (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))`$ による）。

**第 4 段：コピー列そのものの CNF。**
[T.cnf_copies](#t-cnf_copies) を (hR)、(d0pos)、(w0lt)、(lphd)、(cBlp)、$`n := m+1`$ に適用して

```math
\text{(cCopies)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1))\bigr)
```

を得る。(cpcons) によりこれは $`\mathrm{cnf}\bigl(\mathrm{tr}((v_0,w_0) :: S)\bigr)`$ と同一の命題である。

**第 5 段：引数どうしの狭義減少。**
(decr) に (st1), (st2) を代入すると

```math
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
  \prec \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

である。[T.olt_P_P](Term.md#t-olt_P_P) により右辺の 3 つの選言のいずれかが成り立つ。

- 第 1 選言 $`w_0 \lt w_0`$：$`\lt`$ の非反射性に矛盾する。
- 第 2 選言 $`w_0 = w_0 \wedge \mathrm{tr}\,S \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell))`$：
  求める結論そのものである。
- 第 3 選言 $`w_0 = w_0 \wedge \mathrm{tr}\,S = \mathrm{tr}(R \mathbin{+\!\!+} (\ell)) \wedge \mathsf{Z} \prec \mathsf{Z}`$：
  最後の連言子は [T.not_olt_Z](Term.md#t-not_olt_Z) に矛盾する。

よって第 2 選言のみが可能であり

```math
\text{(argA)}\qquad \mathrm{tr}\,S \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell)).
```

**第 6 段：文脈による合同。**
(argA) に [T.olt_P_b](Term.md#t-olt_P_b) を $`a := w_0`$、$`c_1 := \mathsf{Z}`$、$`c_2 := \mathsf{Z}`$
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
(leadle) は [T.cnf_ctx_cong](#t-cnf_ctx_cong) の仮定 (leadle) の形をしている。

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

[T.cnf_ctx_cong](#t-cnf_ctx_cong) を

```math
z_1 := (v_0,w_0),\quad T_1 := S,\quad
z_2 := (v_0,w_0),\quad T_2 := R \mathbin{+\!\!+} (\ell),\quad G := G
```

として適用する。その 7 つの仮定は次のように満たされる。

- $`\mathrm{cnf}(\mathrm{tr}(z_1 :: T_1))`$：第 4 段の (cCopies)（(cpcons) による）。
- $`\mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2)`$：(decr')。
- $`(z_1)_1 = (z_2)_1`$：両辺とも $`v_0`$ であり $`=`$ の反射性による。
- (leadle)：第 6 段の (leadle)。
- $`\forall x \in T_1,\ (z_1)_1 \le x_1`$：(r1)。
- $`\forall x \in T_2,\ (z_2)_1 \le x_1`$：第 3 段の (rT)。
- $`\mathrm{cnf}(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2))`$：第 3 段の (cM')。

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

である。ここで $`B^{\ast n}`$ は [T.cnf_replicate_block](#t-cnf_replicate_block) と同じく $`B`$ を
$`n`$ 個連結した列である。

### 証明

任意の $`k \in \mathbb{N}`$ について $`k \cdot 0 = 0`$ であり、
[T.shiftr0_zero](#t-shiftr0_zero) より $`B^{+k\cdot 0} = B^{+0} = B`$ である。
すなわち $`\mathrm{cp}`$ の定義（D.copies）で $`\mathrm{range}(n)`$ の各要素 $`k`$ に対応させる列は
$`k`$ に依らず $`B`$ である。

したがって $`\mathrm{cp}_0(B,n)`$ は、$`\mathrm{range}(n)`$ の各要素を $`B`$ に写して得られる列の
並びを連結したものである。$`\lvert \mathrm{range}(n)\rvert = n`$ であるから、その並びは
$`B`$ を $`n`$ 個並べたものであり、その連結は $`B^{\ast n}`$ である。∎

<a id="t-cnf_oper"></a>
## 定理: 展開は CNF を保つ (T.cnf_oper)

### 定理

$`M \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とし、$`1 \le n`$ かつ
$`\mathrm{cnf}(\mathrm{tr}\,M)`$ を仮定する。このとき $`\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)`$。

### 証明

以下 $`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$ と書く
（自然数の減法は切り捨て減法である）。$`j_1 = 0`$ か否かで場合分けする。

**(a) $`j_1 = 0`$ のとき。**
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より $`M[n] = M`$ である。
よって示すべきことは仮定 $`\mathrm{cnf}(\mathrm{tr}\,M)`$ そのものである。

以下 $`j_1 \ne 0`$ とする。このとき $`\lvert M\rvert - 1 \ne 0`$ であるから $`1 \lt \lvert M\rvert`$ で
ある。とくに $`M \ne ()`$ である（$`M = ()`$ なら $`\lvert M\rvert = 0`$ となり
$`1 \lt \lvert M\rvert`$ に反する）。また $`\neg(\lvert M\rvert \le 1)`$ であるから、
$`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合が選ばれ

```math
\text{(hPred)}\qquad \mathrm{Pred}\,M = \mathrm{dropLast}\,M
```

である。

**(b) $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。**
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) より $`M[n] = \mathrm{Pred}\,M`$ で
あり、(hPred) より $`M[n] = \mathrm{dropLast}\,M`$ である。
$`M \ne ()`$ と仮定 $`\mathrm{cnf}(\mathrm{tr}\,M)`$ に [T.cnf_dropLast](#t-cnf_dropLast) を適用して
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,M)\bigr)`$ を得る。

以下 $`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$ とする。
$`\mathrm{hasParent}(M, i_1, j_1)`$ が成り立つか否かでさらに分ける。

**(c) $`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) より
$`M[n] = \mathrm{Pred}\,M`$ であり、(hPred) より $`M[n] = \mathrm{dropLast}\,M`$ である。
$`M \ne ()`$ と仮定 $`\mathrm{cnf}(\mathrm{tr}\,M)`$ に [T.cnf_dropLast](#t-cnf_dropLast) を適用して
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,M)\bigr)`$ を得る。

**(d) $`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
$`1 \lt \lvert M\rvert`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、
$`\mathrm{hasParent}(M, i_1, j_1)`$、$`1 \le n`$ が揃っているので
[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) を適用する。
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
[T.cnf_oper_i1eq0](#t-cnf_oper_i1eq0) を (3)（仮定 (hR)）、(4)（仮定 (lpv)）、
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

$`M \in \mathrm{ST\_PS}`$（[D.ST_PS](Pss.md#d-ST_PS)）ならば $`\mathrm{cnf}(\mathrm{tr}\,M)`$。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}\,M\bigr).
```

$`\mathrm{ST\_PS}`$ の定義（D.ST_PS）の 2 つの規則に対応して次を示せばよい。

- **規則 (diag)**：$`\forall v \in \mathbb{N},\ \Phi(\Delta_0^v)`$。
  [T.cnf_diag](#t-cnf_diag) がこれそのものである。

- **規則 (oper)**：$`M \in \mathrm{ST\_PS}`$、$`1 \le n`$、および帰納法の仮定 $`\Phi(M)`$、
  すなわち $`\mathrm{cnf}(\mathrm{tr}\,M)`$ を仮定して $`\Phi(M[n])`$ を示す。
  [T.cnf_oper](#t-cnf_oper) を $`1 \le n`$ と帰納法の仮定 $`\mathrm{cnf}(\mathrm{tr}\,M)`$ に
  適用すると $`\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)`$、すなわち $`\Phi(M[n])`$ を得る。

よって $`\forall M \in \mathrm{ST\_PS},\ \Phi(M)`$ が成り立つ。∎
