[← README](README-ja.md) | [English](ArgDom-5.md) | [Japanese](ArgDom-5-ja.md) | ArgDom [1](ArgDom-ja.md) [2](ArgDom-2-ja.md) [3](ArgDom-3-ja.md) [4](ArgDom-4-ja.md) **5**

<a id="t-argDomCoreOn_bad"></a>
## 定理: 第 4 分岐での ArgDomCoreOn の保存 (T.argDomCoreOn_bad)

### 定理

$`M, G, R \in \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）、$`v_0, w_0, d_0, n \in \mathbb{N}`$、
$`\ell \in \mathbb{N}\times\mathbb{N}`$ とし、$`\mathrm{blk} := (v_0,w_0) :: R`$ とおく。
[T.argDomCoreOn_bad_A2](ArgDom-4-ja.md#t-argDomCoreOn_bad_A2) の仮定 (hM) から (hSTn) までと (hn)、すなわち

```math
\begin{aligned}
&\text{(hM)}\quad M \in \mathrm{ST\_PS}, \qquad
 \text{(hMon)}\quad \mathrm{ArgDomCoreOn}(M), \cr
&\text{(hMeq)}\quad M = G \mathbin{+\!\!+} \mathrm{blk} \mathbin{+\!\!+} (\ell), \cr
&\text{(hRgt)}\quad \forall x \in R,\ v_0 \lt x_1, \qquad
 \text{(hlp)}\quad v_0 \lt \ell_1, \cr
&\text{(hdisj)}\quad \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr)
   \ \vee\ \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 (\lvert M\rvert - 1)\bigr), \cr
&\text{(hSTn)}\quad \forall m,\ 1 \le m \to G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m) \in \mathrm{ST\_PS}, \cr
&\text{(hn)}\quad 1 \le n
\end{aligned}
```

（$`\mathrm{ST\_PS}`$ [D.ST_PS](Pss-ja.md#d-ST_PS)、$`\mathrm{ArgDomCoreOn}`$ [D.ArgDomCoreOn](ArgDom-ja.md#d-ArgDomCoreOn)、
$`\to^M_1`$ [D.nextrel1](Pss-ja.md#d-nextrel1)、$`\mathrm{copies}_{d_0}`$ [D.copies](Cnf-2-ja.md#d-copies)）

を仮定する。このとき
$`\mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n)\bigr)`$。

### 証明

$`n`$ に関する完全帰納法による。帰納法の述語は

```math
\Phi(n) :\equiv \Bigl(1 \le n \to
  \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n)\bigr)\Bigr)
```

である（結論の $`1 \le n`$ を前件に戻して量化する）。完全帰納法の帰納段は
「任意の $`n`$ について、$`\forall m \lt n,\ \Phi(m)`$ を仮定して $`\Phi(n)`$ を示す」であり、
基底段はこの帰納段の $`n = 0`$ の場合、すなわち前件 $`1 \le 0`$ が偽であることから
$`\Phi(0)`$ が成り立つ場合として含まれている。

**帰納段。** $`n`$ を固定し、帰納法の仮定

```math
\text{(IH)}\qquad \forall m,\ m \lt n \to
  \Bigl(1 \le m \to \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)\Bigr)
```

をおく。$`1 \le n`$ とし、$`\mathrm{ArgDomCoreOn}`$ の定義に従って
$`X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$、$`u, w, e \in \mathbb{N}`$ と
[T.argDomCoreOn_bad_A2](ArgDom-4-ja.md#t-argDomCoreOn_bad_A2) の仮定 (heq) から (h6) までを与えられたとして

```math
B \preceq_{\mathrm{lex}}
  \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

（$`\preceq_{\mathrm{lex}}`$ [D.sle](Cofinality-ja.md#d-sle)、$`L^{+e}`$ [D.shiftr0](Cnf-2-ja.md#d-shiftr0)）

を示す。(IH) を書き直すと、これは
[T.argDomCoreOn_bad_A2](ArgDom-4-ja.md#t-argDomCoreOn_bad_A2) の仮定 (hIH)

```math
\forall m,\ 1 \le m \to m \lt n \to
  \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)
```

そのものである。

$`i := \lvert X\rvert`$、$`j := \lvert X\rvert + (\lvert A_1\rvert + 1)`$、
$`p := \lvert G\rvert + (\lvert R\rvert + 1)`$ とおく。自然数の全順序性により
$`j \lt p`$ または $`p \le j`$ であり、後者の場合さらに $`i \lt p`$ または $`p \le i`$ である。
この 3 通りは互いに排反で、かつすべての場合を尽くす。

- $`j \lt p`$ のとき。[T.argDomCoreOn_bad_B](ArgDom-3-ja.md#t-argDomCoreOn_bad_B) を
  (hM) から (hSTn) まで、(hIH)、(hn)、(heq) から (h6) まで、および
  その判別条件 (hcase) $`j \lt p`$ に適用する。
- $`p \le j`$ かつ $`i \lt p`$ のとき。[T.argDomCoreOn_bad_A2](ArgDom-4-ja.md#t-argDomCoreOn_bad_A2) を
  (hM) から (hSTn) まで、(hIH)、(hn)、(heq) から (h6) まで、および
  その判別条件 (hcaseL) $`i \lt p`$、(hcaseR) $`p \le j`$ に適用する。
- $`p \le j`$ かつ $`p \le i`$ のとき。[T.argDomCoreOn_bad_A1](ArgDom-2-ja.md#t-argDomCoreOn_bad_A1) を
  (hM) から (hSTn) まで、(hIH)、(hn)、(heq) から (h6) まで、および
  その判別条件 (hcase) $`p \le i`$ に適用する。

いずれの場合も結論が得られた。∎

<a id="t-argDomCoreOn_oper"></a>
## 定理: 展開による ArgDomCoreOn の保存 (T.argDomCoreOn_oper)

### 定理

$`M \in \mathrm{ST\_PS}`$、$`\mathrm{ArgDomCoreOn}(M)`$、$`1 \le n`$ ならば
$`\mathrm{ArgDomCoreOn}(M[n])`$（$`M[n]`$ [D.oper](Pss-ja.md#d-oper)）。

### 証明

$`j_1 := \lvert M\rvert - 1`$ と書く。$`M[n]`$ の定義（D.oper）の分岐に沿って場合分けする。

**(a) $`j_1 = 0`$ のとき。**
[T.oper_eq_self_of_short](Decrease-ja.md#t-oper_eq_self_of_short) より $`M[n] = M`$ であるから、
仮定 $`\mathrm{ArgDomCoreOn}(M)`$ がそのまま結論である。

**(b) $`j_1 \ne 0`$ かつ $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$（[D.entry](Pss-ja.md#d-entry)）のとき。**
[T.oper_eq_pred_of_zero](Decrease-ja.md#t-oper_eq_pred_of_zero) より
$`M[n] = \mathrm{Pred}\,M`$（[D.Pred](Pss-ja.md#d-Pred)）である。$`j_1 = \lvert M\rvert - 1 \ne 0`$ より
$`2 \le \lvert M\rvert`$、すなわち $`\neg(\lvert M\rvert \le 1)`$ であるから、
$`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合が選ばれて
$`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。

$`M \ne ()`$ である（$`M = ()`$ なら $`\lvert M\rvert = 0`$ となり $`2 \le \lvert M\rvert`$ に反する）。
また $`M_{i,j}`$ の定義（D.entry）より仮定は
$`(M\langle j_1\rangle)_1 = 0`$ かつ $`(M\langle j_1\rangle)_2 = 0`$、すなわち
$`M\langle j_1\rangle = (0,0)`$ である。
[T.dropLast_snoc_getD](Cofinality-ja.md#t-dropLast_snoc_getD) より

```math
\mathrm{dropLast}\,M \mathbin{+\!\!+} \bigl((0,0)\bigr) = M
```

であるから、仮定 $`\mathrm{ArgDomCoreOn}(M)`$ は
$`\mathrm{ArgDomCoreOn}\bigl(\mathrm{dropLast}\,M \mathbin{+\!\!+} ((0,0))\bigr)`$ に他ならない。
$`(0,0)`$ の第 1 成分は $`0`$ であるから
[T.argDomCoreOn_snoc_zero](ArgDom-2-ja.md#t-argDomCoreOn_snoc_zero) が適用でき、
$`\mathrm{ArgDomCoreOn}(\mathrm{dropLast}\,M) = \mathrm{ArgDomCoreOn}(M[n])`$ を得る。

**(c) $`j_1 \ne 0`$ かつ $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ のとき。**
$`2 \le \lvert M\rvert`$ より $`0 \lt \lvert M\rvert`$ であるから、
[T.hasParent_last_ST_PS](Cofinality-ja.md#t-hasParent_last_ST_PS) より、探索行
$`\mathrm{idx}_1(M,j_1)`$（[D.idx1](Pss-ja.md#d-idx1)）について
$`\mathrm{hasParent}(M, \mathrm{idx}_1(M,j_1), j_1)`$（[D.hasParent](Pss-ja.md#d-hasParent)）が成り立つ。

[T.blockok_ST_PS](Seqlex-2-ja.md#t-blockok_ST_PS) より $`\mathrm{blockok}(0, M)`$（[D.blockok](Seqlex-ja.md#d-blockok)）であり、
その第 3 連言子が $`\mathrm{steps}_1(M)`$（[D.steps1](Seqlex-ja.md#d-steps1)）である。
また [T.r1ok_ST_PS](Column-3-ja.md#t-r1ok_ST_PS) より
$`\mathrm{r1ok}(M)`$（[D.r1ok](Column-2-ja.md#d-r1ok)）である。$`1 \lt \lvert M\rvert`$ とこれらに
[T.oper_bad_blocks_all](Cofinality-ja.md#t-oper_bad_blocks_all) を適用して、
$`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$
であって、$`\mathrm{blk} := (v_0,w_0) :: R`$ とおくと

```math
\begin{aligned}
&M = G \mathbin{+\!\!+} \mathrm{blk} \mathbin{+\!\!+} (\ell), \cr
&\forall k,\ 1 \le k \to M[k] = G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, k), \cr
&\forall x \in R,\ v_0 \lt x_1, \qquad v_0 \lt \ell_1, \cr
&\bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr)
   \ \vee\ \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 (\lvert M\rvert - 1)\bigr)
\end{aligned}
```

をみたすものを取る。

各 $`k \ge 1`$ について
$`G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, k) = M[k]`$ であり、
$`\mathrm{ST\_PS}`$ の定義（D.ST_PS）の構成子 $`\mathrm{oper}`$ を $`M \in \mathrm{ST\_PS}`$ と
$`1 \le k`$ に適用すると $`M[k] \in \mathrm{ST\_PS}`$ であるから

```math
\forall k,\ 1 \le k \to G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, k) \in \mathrm{ST\_PS}
```

が成り立つ。最後に $`M[n] = G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n)`$ と書き直し、
[T.argDomCoreOn_bad](#t-argDomCoreOn_bad) を適用すればよい。∎

<a id="t-argDomCoreOn_ST_PS"></a>
## 定理: 標準形上の ArgDomCoreOn (T.argDomCoreOn_ST_PS)

### 定理

$`N \in \mathrm{ST\_PS}`$ ならば $`\mathrm{ArgDomCoreOn}(N)`$。

### 証明

[T.ST_PS.rec](Pss-ja.md#t-ST_PS.rec) による。帰納法の述語は

```math
\Phi(N) :\equiv \mathrm{ArgDomCoreOn}(N)
```

である。構成子は 2 つであるから、次の 2 ステップを示せばよい。

**基底段（構成子 $`\mathrm{diag}`$）。** $`N = \Delta_0^v`$（[D.diagSeq](Pss-ja.md#d-diagSeq)）の場合である。
[T.argDomCoreOn_diag](ArgDom-2-ja.md#t-argDomCoreOn_diag) がそのまま
$`\Phi(\Delta_0^v)`$ である。

**帰納段（構成子 $`\mathrm{oper}`$）。** $`N = M[n]`$ であって、
$`M \in \mathrm{ST\_PS}`$ と $`1 \le n`$ からこの構成子で導出された場合である。
$`\Phi(M) = \mathrm{ArgDomCoreOn}(M)`$ を仮定する。
[T.argDomCoreOn_oper](#t-argDomCoreOn_oper) を $`M \in \mathrm{ST\_PS}`$、
帰納法の仮定 $`\mathrm{ArgDomCoreOn}(M)`$、$`1 \le n`$ に適用して
$`\mathrm{ArgDomCoreOn}(M[n]) = \Phi(N)`$ を得る。∎

<a id="t-argDomCore_holds"></a>
## 定理: ArgDomCore の成立 (T.argDomCore_holds)

### 定理

$`\mathrm{ArgDomCore}`$（[D.ArgDomCore](ArgDom-ja.md#d-ArgDomCore)）。

### 証明

[T.argDomCore_of_on](ArgDom-ja.md#t-argDomCore_of_on) は
$`\forall N,\ N \in \mathrm{ST\_PS} \to \mathrm{ArgDomCoreOn}(N)`$ から
$`\mathrm{ArgDomCore}`$ を導く。その前提は
[T.argDomCoreOn_ST_PS](#t-argDomCoreOn_ST_PS) そのものである。∎
