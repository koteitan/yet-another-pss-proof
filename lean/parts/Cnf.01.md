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

[$`M \in \mathrm{PairSeq}`$](Pss.md#d-PairSeq)、$`n \in \mathbb{N}`$ とし、$`1 \lt \lvert M\rvert`$ と
$`1 \le n`$ を仮定する。このとき $`R \in \mathrm{PairSeq}`$ が存在して

```math
M[n] = \mathrm{dropLast}\,M \mathbin{+\!\!+} R
\qquad\text{かつ}\qquad
\mathrm{snd}(R) \subseteq \mathrm{snd}(\mathrm{dropLast}\,M)
```

が成り立つ。ここで $`\mathrm{dropLast}\,M`$ は $`M`$ の末尾 1 要素を落とした列である
（[$`M[n]`$](Pss.md#d-oper)、[$`\mathrm{snd}`$](Term.md#d-sndSet)）。

### 証明

$`j_1 := \lvert M\rvert - 1`$、[$`i_1 := \mathrm{idx}_1(M, j_1)`$](Pss.md#d-idx1) とおく。
$`1 \lt \lvert M\rvert`$ より $`j_1 \ne 0`$ であり、また $`\neg(\lvert M\rvert \le 1)`$ であるから
[$`\mathrm{Pred}\,M`$](Pss.md#d-Pred) の定義（D.Pred）の第 2 の場合が選ばれて

```math
\mathrm{Pred}\,M = \mathrm{dropLast}\,M
```

である。次の 3 つの場合に分ける。

**(a) [$`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$](Pss.md#d-entry) のとき。**
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) より
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。$`R := ()`$ と取る。
第 1 式は $`\mathrm{dropLast}\,M \mathbin{+\!\!+} () = \mathrm{dropLast}\,M`$ により成り立つ。
第 2 式は [T.sndSet_nil](Term.md#t-sndSet_nil) より $`\mathrm{snd}(()) = \emptyset`$ であり、
空集合は任意の集合の部分集合であるから成り立つ。

**(b) $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ かつ
[$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$](Pss.md#d-hasParent) のとき。**
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) より
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。$`R := ()`$ と取れば (a) と同じ議論で
2 つの式が成り立つ。

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

$`u \le v`$ ならば [$`\Delta_u^v = (u,u) :: \Delta_{u+1}^v`$](Pss.md#d-diagSeq)。

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

（[$`\mathrm{tr}`$](Term.md#d-translate)、[$`\mathsf{Z}`$ と $`\mathsf{P}`$](Term.md#d-Three)）。

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
[$`\neg\bigl(\mathsf{P}(a,b,\mathsf{Z}) \prec \mathsf{P}(e,f,\mathsf{Z})\bigr)`$](Term.md#d-olt) は、
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

- **基底段** $`n = 0`$：$`u`$ を取る。$`u + 0 = u`$ である。
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

- **基底段** $`D = ()`$：結論は $`\mathrm{cnf}(\mathrm{tr}\,())`$ である。
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
[$`A \preceq A'`$](Term.md#d-ole) である。

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

- **基底段** $`d = 0`$：$`k`$ を取り $`\lvert M\rvert - k = 0`$ とする。自然数の減法は切り捨て減法であるから
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
$`B := (v_0,w_0) :: R`$ とおき、$`B`$ を $`n`$ 個連結した列を

```math
B^{(0)} := (), \qquad B^{(k+1)} := B \mathbin{+\!\!+} B^{(k)}
```

で定める。このとき任意の $`n \in \mathbb{N}`$ に対し $`\mathrm{cnf}\bigl(\mathrm{tr}(B^{(n)})\bigr)`$。

### 証明

はじめに、任意の $`k \in \mathbb{N}`$ について

```math
(\ast)\qquad B^{(k)} = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,B^{(k)})_1\bigr)
```

が成り立つことを見る。$`k = 0`$ のときは $`B^{(0)} = ()`$ であり第 1 選言が成り立つ。
$`k = k' + 1`$ のときは $`B^{(k'+1)} = B \mathbin{+\!\!+} B^{(k')}`$ の先頭は $`B`$ の先頭 $`(v_0,w_0)`$ であり、
$`\neg(v_0 \lt v_0)`$ であるから第 2 選言が成り立つ。

したがって [T.translate_block_append](Term.md#t-translate_block_append) を
$`T := B^{(k)}`$ として適用でき、任意の $`k`$ について

```math
(\ast\ast)\qquad \mathrm{tr}\bigl(B^{(k+1)}\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}(B^{(k)})\bigr)
```

が成り立つ（第 1 の仮定が $`\forall x \in R,\ v_0 \lt x_1`$ である）。

$`n`$ に関する帰納法を行う。帰納法の述語は

```math
\Phi(n) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(B^{(n)})\bigr).
```

- **基底段** $`n = 0`$：$`B^{(0)} = ()`$ であり、$`\mathrm{tr}`$ の定義（D.translate）より
  $`\mathrm{tr}\,() = \mathsf{Z}`$ である。[T.cnf_Z](#t-cnf_Z) より $`\Phi(0)`$。

**帰納段** $`n = m + 1`$：帰納法の仮定は $`\Phi(m)`$、すなわち
$`\mathrm{cnf}\bigl(\mathrm{tr}(B^{(m)})\bigr)`$ である。$`m`$ で場合分けする。

**$`m = 0`$ のとき。** $`(\ast\ast)`$ を $`k := 0`$ として使うと

```math
\mathrm{tr}(B^{(1)}) = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,()\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathsf{Z}\bigr)
```

である。
[T.cnf_P_Z](#t-cnf_P_Z) よりこれが条件をみたすことは $`\mathrm{cnf}(\mathrm{tr}\,R)`$ と同値であり、
それは仮定である。よって $`\Phi(1)`$。

**$`m = m' + 1`$ のとき。** $`(\ast\ast)`$ を $`k := m`$ と $`k := m'`$ として使うと

```math
\mathrm{tr}\bigl(B^{(m+1)}\bigr)
  = \mathsf{P}\Bigl(w_0,\ \mathrm{tr}\,R,\
      \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}(B^{(m')})\bigr)\Bigr)
```

である。[T.cnf_P_P](#t-cnf_P_P) により、これが条件をみたすためには次の 3 つを示せばよい。

1. $`\mathrm{cnf}(\mathrm{tr}\,R)`$：仮定である。
2. $`\neg\bigl(\mathsf{P}(w_0, \mathrm{tr}\,R, \mathsf{Z}) \prec \mathsf{P}(w_0, \mathrm{tr}\,R, \mathsf{Z})\bigr)`$：
   [T.olt_irrefl](Term.md#t-olt_irrefl) である。
3. $`\mathrm{cnf}\bigl(\mathsf{P}(w_0, \mathrm{tr}\,R, \mathrm{tr}(B^{(m')}))\bigr)`$：
   $`(\ast\ast)`$ を $`k := m'`$ として使うとこの項は $`\mathrm{tr}(B^{(m'+1)}) = \mathrm{tr}(B^{(m)})`$ であり、
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
&\text{(lead)}\quad \exists\, a_1, b_1, c_1, a_2, b_2, c_2,\ \bigl[\
   \mathrm{tr}(z_1 :: T_1) = \mathsf{P}(a_1,b_1,c_1)
   \ \wedge\ \mathrm{tr}(z_2 :: T_2) = \mathsf{P}(a_2,b_2,c_2) \cr
&\hphantom{\text{(lead)}\quad \exists\, a_1, b_1, c_1, a_2, b_2, c_2,\ \bigl[\ }
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
以下、(lead) の $`a_1, b_1, c_1, a_2, b_2, c_2`$ を取り、

```math
\mathrm{tr}(z_1 :: T_1) = \mathsf{P}(a_1,b_1,c_1), \quad
\mathrm{tr}(z_2 :: T_2) = \mathsf{P}(a_2,b_2,c_2), \quad
\mathsf{P}(a_1,b_1,\mathsf{Z}) \preceq \mathsf{P}(a_2,b_2,\mathsf{Z})
```

と書く。

- **$`G = ()`$ のとき**：$`() \mathbin{+\!\!+} z_1 :: T_1 = z_1 :: T_1`$ であるから、結論は (cZ1) そのものである。

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
$`z_2 :: T_2`$ についても (r2) から同様である。よって $`G' \mathbin{+\!\!+} z_i :: T_i`$ の全要素が
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
(lead) の 2 つの等式より

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

を示す。内側が成り立つとすると、(lead) の
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

- **$`G = ()`$ のとき**：$`() \mathbin{+\!\!+} t :: T' = t :: T'`$ であるから、結論は前件そのものである。

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
