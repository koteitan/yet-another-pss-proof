[← README](README.md) ｜ ArgDom [1](ArgDom.md) [2](ArgDom-2.md) **3** [4](ArgDom-4.md) [5](ArgDom-5.md)

<a id="t-seqlex_of_sle_snoc'"></a>
## 定理: 末尾列の差し替え、上界相対形 (T.seqlex_of_sle_snoc')

### 定理

$`X, V, E \in \mathrm{PairSeq}`$（[D.PairSeq](Pss.md#d-PairSeq)）、$`\ell, q \in \mathbb{N}\times\mathbb{N}`$ が

```math
X \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} E,
\qquad q \prec_{\mathrm{p}} \ell,
\qquad \lvert X\rvert \lt \lvert V\rvert
```

（$`\preceq_{\mathrm{lex}}`$ [D.sle](Cofinality.md#d-sle)、$`\prec_{\mathrm{p}}`$ [D.pairlt](Seqlex.md#d-pairlt)）

をみたすならば、任意の $`S', E' \in \mathrm{PairSeq}`$ に対し

```math
X \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V \mathbin{+\!\!+} E' .
```

（$`\prec_{\mathrm{lex}}`$ [D.seqlex](Seqlex.md#d-seqlex)）

### 証明

$`X`$ の構成子に関する帰納法（$`V, E, \ell, q, S', E'`$ は全称量化したまま動かす）。
帰納法の述語は

```math
\Phi(X) :\equiv \forall V, E, \ell, q,\
  \bigl(X \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} E
   \wedge q \prec_{\mathrm{p}} \ell \wedge \lvert X\rvert \lt \lvert V\rvert\bigr)
  \to \forall S', E',\ X \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V \mathbin{+\!\!+} E' .
```

**基底段** $`X = ()`$。$`\lvert V\rvert \gt 0`$ であるから $`V = v :: V'`$ と書ける
（$`V = ()`$ なら $`\lvert V\rvert = 0`$ となり $`0 \lt \lvert V\rvert`$ に反する）。
示すべきことは $`q :: S' \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E')`$ であり、
$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式によりその第 1 選言 $`q \prec_{\mathrm{p}} v`$ を
示せば十分である。仮定は $`(\ell) \preceq_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E)`$ であり、
$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）で場合分けする。

- $`(\ell) = v :: (V' \mathbin{+\!\!+} E)`$ のとき。両辺の先頭要素を比べて $`\ell = v`$ である。
  仮定 $`q \prec_{\mathrm{p}} \ell`$ がそのまま $`q \prec_{\mathrm{p}} v`$ を与える。

- $`(\ell) \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E)`$ のとき。$`(\ell) = \ell :: ()`$ であるから
  D.seqlex の第 3 式より、$`\ell \prec_{\mathrm{p}} v`$ または
  $`\ell = v \wedge () \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$ である。
  前者のときは [T.pairlt_trans](Cofinality.md#t-pairlt_trans) を
  $`q \prec_{\mathrm{p}} \ell`$ と $`\ell \prec_{\mathrm{p}} v`$ に適用して $`q \prec_{\mathrm{p}} v`$。
  後者のときは $`\ell = v`$ を $`q \prec_{\mathrm{p}} \ell`$ に代入して $`q \prec_{\mathrm{p}} v`$。

**帰納段** $`X = x :: X'`$。帰納法の仮定は $`\Phi(X')`$ である。
$`\lvert x :: X'\rvert \lt \lvert V\rvert`$ より $`V \ne ()`$ であるから $`V = v :: V'`$ と書け、
このとき $`\lvert X'\rvert + 1 \lt \lvert V'\rvert + 1`$、すなわち $`\lvert X'\rvert \lt \lvert V'\rvert`$ である。
仮定は

```math
x :: \bigl(X' \mathbin{+\!\!+} (\ell)\bigr) \preceq_{\mathrm{lex}} v :: \bigl(V' \mathbin{+\!\!+} E\bigr)
```

であり、示すべきことは
$`x :: (X' \mathbin{+\!\!+} q :: S') \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E')`$、
すなわち D.seqlex の第 3 式により

```math
x \prec_{\mathrm{p}} v
\quad\text{または}\quad
\bigl(x = v \wedge X' \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E'\bigr)
```

である。仮定を D.sle で場合分けする。

- 等号 $`x :: (X' \mathbin{+\!\!+} (\ell)) = v :: (V' \mathbin{+\!\!+} E)`$ のとき。
  先頭要素を比べて $`x = v`$、残りを比べて $`X' \mathbin{+\!\!+} (\ell) = V' \mathbin{+\!\!+} E`$ である。
  後者は D.sle の第 1 選言により
  $`X' \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$ を与える。
  帰納法の仮定 $`\Phi(X')`$ を $`V', E, \ell, q`$ に適用する（残りの仮定は
  $`q \prec_{\mathrm{p}} \ell`$ と $`\lvert X'\rvert \lt \lvert V'\rvert`$）と
  $`X' \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E'`$ が得られ、第 2 選言が成り立つ。

- $`x :: (X' \mathbin{+\!\!+} (\ell)) \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E)`$ のとき。
  D.seqlex の第 3 式より 2 つに分かれる。

  - $`x \prec_{\mathrm{p}} v`$ のとき。これが第 1 選言そのものである。
  - $`x = v \wedge X' \mathbin{+\!\!+} (\ell) \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$ のとき。
    後半は D.sle の第 2 選言により
    $`X' \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$ を与える。
    帰納法の仮定 $`\Phi(X')`$ を $`V', E, \ell, q`$ に適用する（残りの仮定は
    $`q \prec_{\mathrm{p}} \ell`$ と $`\lvert X'\rvert \lt \lvert V'\rvert`$）と
    $`X' \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E'`$ が得られ、
    $`x = v`$ と合わせて第 2 選言が成り立つ。∎

<a id="t-argDomCoreOn_bad_B"></a>
## 定理: 展開の第 4 分岐の場合 B (T.argDomCoreOn_bad_B)

### 定理

$`M, G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0, n \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、
$`\mathrm{blk} := (v_0,w_0) :: R`$ とし、
[T.argDomCoreOn_bad_A1](ArgDom-2.md#t-argDomCoreOn_bad_A1) の仮定
(hM), (hMon), (hMeq), (hRgt), (hlp), (hdisj), (hSTn), (hIH), (hn) および
$`X, A_1, B, A_2, Z, u, w, e`$ についての (heq), (he), (h1), (h2), (h3), (h4), (h5), (h6) を
そのまま仮定する。さらに

```math
\text{(hcase)}\qquad
\lvert X\rvert + (\lvert A_1\rvert + 1) \lt \lvert G\rvert + (\lvert R\rvert + 1)
```

を仮定する。このとき

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e} .
```

（$`L^{+d}`$ [D.shiftr0](Cnf-2.md#d-shiftr0)）

### 証明

(hn) より $`n = m + 1`$ と書く。

```math
T := \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0},
\qquad
C_p := X \mathbin{+\!\!+} (u,w) :: \bigl(A_1 \mathbin{+\!\!+} ((u+e,w))\bigr)
```

（$`\mathrm{copies}_d(B, n)`$ [D.copies](Cnf-2.md#d-copies)）

とおく。$`C_p`$ は分解の先頭から深い方の印付き列 $`(u+e,w)`$ までを含む部分であり、
$`\lvert C_p\rvert = \lvert X\rvert + 1 + (\lvert A_1\rvert + 1)`$ である。

**第 1 段：共通部分で切る。**
[T.copies_succ_front](Cnf-3.md#t-copies_succ_front) と連結の結合律より

```math
G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1) = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} T
```

である。また (heq) の右辺を結合律で並べ替えると

```math
(G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} T
 = C_p \mathbin{+\!\!+} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

を得る。長さは

```math
\lvert C_p\rvert = \lvert X\rvert + \bigl(\lvert A_1\rvert + 1\bigr) + 1,
\qquad
\lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert = \lvert G\rvert + (\lvert R\rvert + 1)
```

である。$`\mathbb{N}`$ において $`a \lt b`$ は $`a + 1 \le b`$ と同値であるから、(hcase) は

```math
\lvert C_p\rvert = \bigl(\lvert X\rvert + (\lvert A_1\rvert + 1)\bigr) + 1
  \le \lvert G\rvert + (\lvert R\rvert + 1) = \lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert
```

を与える。
[T.split_prefix_left](ArgDom-2.md#t-split_prefix_left) を適用して
$`D := \mathrm{drop}_{\lvert C_p\rvert}(G \mathbin{+\!\!+} \mathrm{blk})`$ とおくと

```math
G \mathbin{+\!\!+} \mathrm{blk} = C_p \mathbin{+\!\!+} D,
\qquad
B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} T
```

である。第 1 の等式と (hMeq) を合わせ、結合律により

```math
M = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} (\ell)
  = \bigl(C_p \mathbin{+\!\!+} D\bigr) \mathbin{+\!\!+} (\ell)
  = C_p \mathbin{+\!\!+} \bigl(D \mathbin{+\!\!+} (\ell)\bigr)
```

を得る。すなわち $`M`$ は $`C_p`$ の右に $`D \mathbin{+\!\!+} (\ell)`$ を続けたものである。

**第 2 段：$`M`$ の分解に (hMon) を適用する。**
次を示す。$`B', A_2', Z' \in \mathrm{PairSeq}`$ が

```math
D \mathbin{+\!\!+} (\ell) = B' \mathbin{+\!\!+} (A_2' \mathbin{+\!\!+} Z'),
\qquad \forall x \in B',\ u + e \lt x_1,
\qquad \forall x \in A_2',\ u \lt x_1,
```
```math
A_2' = () \ \vee\ (\mathrm{head}\,A_2')_1 \le u+e,
\qquad
Z' = () \ \vee\ (\mathrm{head}\,Z')_1 \le u
```

をみたすならば

```math
B' \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B'^{+e} .
```

実際、第 1 段の $`M = C_p \mathbin{+\!\!+} (D \mathbin{+\!\!+} (\ell))`$ に分解の仮定を代入し、
$`C_p`$ の定義と結合律で並べ替えると

```math
M = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B' \mathbin{+\!\!+} A_2'))\bigr) \mathbin{+\!\!+} Z'
```

である。これは [D.ArgDomCoreOn](ArgDom.md#d-ArgDomCoreOn) が要求する分解の形であるから、(hMon) をこの分解と
(he)、(h1)、上に挙げた $`B'`$、$`A_2'`$、$`Z'`$ についての 4 条件、(h6) に適用して

```math
B' \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+e}
```

を得る。[T.argbound_split](ArgDom-2.md#t-argbound_split) により右辺は

```math
\bigl(A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B'^{+e}\bigr) \mathbin{+\!\!+} A_2'^{+e}
```

に等しく、[T.argbound_len](ArgDom-2.md#t-argbound_len) により
$`\lvert B'\rvert \le \lvert A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B'^{+e}\rvert`$ である。
[T.sle_take_of_short](ArgDom.md#t-sle_take_of_short) を適用して主張を得る。

**第 3 段：結論を同じ形に直す。**

```math
B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}
```

が示せれば結論が従う。実際、[T.argbound_split](ArgDom-2.md#t-argbound_split) により結論の右辺は
$`(A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}) \mathbin{+\!\!+} A_2^{+e}`$ であり、
[T.sle_append_mono](Cofinality.md#t-sle_append_mono) を
$`C := A_2^{+e}`$ として適用すればよい。以下この形を示す。

**第 4 段：$`\lvert B\rvert`$ と $`\lvert D\rvert`$ で場合分けする。**

**(a) $`\lvert B\rvert \lt \lvert D\rvert`$ のとき。**
[T.split_prefix_right](ArgDom-2.md#t-split_prefix_right) を第 1 段の
$`B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} T`$ と $`\lvert B\rvert \le \lvert D\rvert`$ に適用し、
$`D_r := \mathrm{drop}_{\lvert B\rvert} D`$ とおくと

```math
D = B \mathbin{+\!\!+} D_r,
\qquad
A_2 \mathbin{+\!\!+} Z = D_r \mathbin{+\!\!+} T
```

である。

まず $`D_r \ne ()`$ である。$`D_r = ()`$ とすると $`D = B`$ となり
$`\lvert B\rvert \lt \lvert D\rvert = \lvert B\rvert`$ となって矛盾する。
したがって $`A_2 \mathbin{+\!\!+} Z = D_r \mathbin{+\!\!+} T \ne ()`$ であり、
[T.headI_append_left](Seqlex-2.md#t-headI_append_left) より
$`\mathrm{head}(A_2 \mathbin{+\!\!+} Z) = \mathrm{head}\,D_r`$ である。

次に $`(\mathrm{head}\,D_r)_1 \le u + e`$ を示す。$`A_2`$ が空かどうかで分ける。

- $`A_2 = ()`$ のとき。$`A_2 \mathbin{+\!\!+} Z = Z`$ であり、これは空でないから
  (h5) の第 1 選言 $`Z = ()`$ は偽である。よって第 2 選言により
  $`(\mathrm{head}\,Z)_1 \le u \le u + e`$ であり、
  $`\mathrm{head}\,D_r = \mathrm{head}(A_2 \mathbin{+\!\!+} Z) = \mathrm{head}\,Z`$ である。

- $`A_2 \ne ()`$ のとき。[T.headI_append_left](Seqlex-2.md#t-headI_append_left) より
  $`\mathrm{head}(A_2 \mathbin{+\!\!+} Z) = \mathrm{head}\,A_2`$ であり、(h4) の第 1 選言は偽であるから
  第 2 選言により $`(\mathrm{head}\,A_2)_1 \le u + e`$ である。

[T.arg_split](ArgDom-2.md#t-arg_split) を $`L := u`$、$`E := D_r \mathbin{+\!\!+} (\ell)`$ に適用して
$`A_2', Z'`$ を取る。すなわち

```math
D_r \mathbin{+\!\!+} (\ell) = A_2' \mathbin{+\!\!+} Z',
\qquad \forall x \in A_2',\ u \lt x_1,
\qquad Z' = () \vee (\mathrm{head}\,Z')_1 \le u .
```

$`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u+e`$ を示す。$`A_2' = ()`$ なら第 1 選言。
$`A_2' \ne ()`$ なら [T.headI_append_left](Seqlex-2.md#t-headI_append_left) より
$`\mathrm{head}(D_r \mathbin{+\!\!+} (\ell)) = \mathrm{head}\,A_2'`$ であり、
$`D_r \ne ()`$ であるからふたたび同じ定理により
$`\mathrm{head}(D_r \mathbin{+\!\!+} (\ell)) = \mathrm{head}\,D_r`$ である。
よって $`(\mathrm{head}\,A_2')_1 = (\mathrm{head}\,D_r)_1 \le u+e`$。

第 2 段の主張を $`B' := B`$、$`A_2'`$、$`Z'`$ に適用する。分解の条件は

```math
D \mathbin{+\!\!+} (\ell) = (B \mathbin{+\!\!+} D_r) \mathbin{+\!\!+} (\ell)
 = B \mathbin{+\!\!+} \bigl(D_r \mathbin{+\!\!+} (\ell)\bigr)
 = B \mathbin{+\!\!+} \bigl(A_2' \mathbin{+\!\!+} Z'\bigr)
```

であり、$`\forall x \in B,\ u+e \lt x_1`$ は (h2)、残りの 3 条件は上で確かめた。よって

```math
B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}
```

を得る。第 3 段により結論が従う。

**(b) $`\lvert D\rvert \le \lvert B\rvert`$ のとき。**
[T.split_prefix_left](ArgDom-2.md#t-split_prefix_left) を
$`B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} T`$ に適用し、
$`B_2 := \mathrm{drop}_{\lvert D\rvert} B`$ とおくと

```math
B = D \mathbin{+\!\!+} B_2,
\qquad
T = B_2 \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)
```

である。$`D`$ の要素は $`B`$ の要素であるから (h2) より
$`\forall x \in D,\ u+e \lt x_1`$ である。

**第 4 段 (b) の補助 1：$`B_2`$ が空でないときの先頭。**
$`B_2 = q :: B_2'`$ と書けるとき $`q = (v_0+d_0,\ w_0)`$ である。
まず $`m \ne 0`$ である。$`m = 0`$ とすると
[T.copies_zero](Cnf-2.md#t-copies_zero) と [T.shiftr0_nil](Cnf-2.md#t-shiftr0_nil) より $`T = ()`$ となるが、
$`T = B_2 \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)`$ の右辺は $`B_2 = q :: B_2'`$ を含むので空でなく、矛盾する。
よって $`m = m' + 1`$ と書ける。
[T.copies_succ_cons](Cnf-3.md#t-copies_succ_cons) より

```math
\mathrm{copies}_{d_0}(\mathrm{blk}, m'+1)
 = (v_0, w_0) :: \Bigl(R \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m')\bigr)^{+d_0}\Bigr)
```

であり、[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons) より

```math
T = (v_0 + d_0,\ w_0) :: \Bigl(R \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m')\bigr)^{+d_0}\Bigr)^{+d_0}
```

である。一方 $`T = B_2 \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = q :: \bigl(B_2' \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)`$
であるから、cons の単射性により $`q = (v_0+d_0,\ w_0)`$ である。

**第 4 段 (b) の補助 2：$`q`$ と $`\ell`$ の比較。**
$`B_2 = q :: B_2'`$ のとき、次の 2 つが成り立つ。

- $`q_1 \le \ell_1`$。(hdisj) の第 1 選言のときは $`d_0 = 0`$ かつ $`\ell_1 = v_0 + 1`$ であり、
  $`q_1 = v_0 + d_0 = v_0 \le v_0 + 1 = \ell_1`$。
  第 2 選言のときは $`\ell_1 = v_0 + d_0 = q_1`$。

- $`q \prec_{\mathrm{p}} \ell`$。(hdisj) の第 1 選言のときは
  $`q_1 = v_0 \lt v_0 + 1 = \ell_1`$ であり、$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 1 選言が成り立つ。
  第 2 選言のときは $`q_1 = v_0 + d_0 = \ell_1`$ かつ $`q_2 = w_0 \lt w_0 + 1 = \ell_2`$ であり、
  D.pairlt の第 2 選言が成り立つ。

$`u+e`$ と $`\ell_1`$ で場合分けする。

**(b-1) $`u + e \lt \ell_1`$ のとき。**
$`\forall x \in D \mathbin{+\!\!+} (\ell),\ u+e \lt x_1`$ である
（$`x \in D`$ なら上で示したこと、$`x = \ell`$ なら本場合の仮定による）。
第 2 段の主張を $`B' := D \mathbin{+\!\!+} (\ell)`$、$`A_2' := ()`$、$`Z' := ()`$ に適用する。
分解の条件は $`D \mathbin{+\!\!+} (\ell) = (D \mathbin{+\!\!+} (\ell)) \mathbin{+\!\!+} (() \mathbin{+\!\!+} ())`$、
$`A_2' = ()`$ は要素をもたず頭の条件は第 1 選言、$`Z' = ()`$ も同様である。よって

```math
D \mathbin{+\!\!+} (\ell)
 \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: \bigl(D \mathbin{+\!\!+} (\ell)\bigr)^{+e} .
```

[T.shiftr0_append](Cofinality-3.md#t-shiftr0_append) と連結の結合律により、
$`V := A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: D^{+e}`$ とおくと右辺は
$`V \mathbin{+\!\!+} (\ell)^{+e}`$ に等しい。すなわち

```math
(\dagger)\qquad D \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} (\ell)^{+e} .
```

なお [T.shiftr0_length](Cofinality-2.md#t-shiftr0_length) より
$`\lvert V\rvert = \lvert A_1\rvert + 1 + \lvert D\rvert`$ である。$`B_2`$ で場合分けする。

**$`B_2 = ()`$ のとき。** $`B = D \mathbin{+\!\!+} () = D`$ である。
[T.sle_of_append_left](ArgDom.md#t-sle_of_append_left) を $`(\dagger)`$ に適用して
$`D \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} (\ell)^{+e}`$ を得る。
$`\lvert D\rvert \le \lvert A_1\rvert + 1 + \lvert D\rvert = \lvert V\rvert`$ であるから、
[T.sle_take_of_short](ArgDom.md#t-sle_take_of_short) を適用して $`D \preceq_{\mathrm{lex}} V`$。
$`B = D`$ より、これは
$`B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}`$ そのものである。
第 3 段により結論が従う。

**$`B_2 = q :: B_2'`$ のとき。** $`\lvert D\rvert \lt \lvert A_1\rvert + 1 + \lvert D\rvert = \lvert V\rvert`$ である。
[T.seqlex_of_sle_snoc'](#t-seqlex_of_sle_snoc') を、その主張に現れる列と対に
$`D`$、$`V`$、$`(\ell)^{+e}`$、$`\ell`$、$`q`$ をこの順に対応させて適用する。
3 つの仮定は $`(\dagger)`$、補助 2 の $`q \prec_{\mathrm{p}} \ell`$、いま示した $`\lvert D\rvert \lt \lvert V\rvert`$ である。
結論の 2 つの全称量化された列を $`B_2'`$ と $`(q_1+e,\ q_2) :: B_2'^{+e}`$ に取ると

```math
D \mathbin{+\!\!+} q :: B_2'
 \prec_{\mathrm{lex}} V \mathbin{+\!\!+} \bigl((q_1+e,\ q_2) :: B_2'^{+e}\bigr)
```

を得る。左辺は $`B = D \mathbin{+\!\!+} B_2 = D \mathbin{+\!\!+} q :: B_2'`$ である。
右辺は [T.shiftr0_append](Cofinality-3.md#t-shiftr0_append)、
[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons) と結合律により

```math
V \mathbin{+\!\!+} \bigl((q_1+e,\ q_2) :: B_2'^{+e}\bigr)
 = A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: \bigl(D^{+e} \mathbin{+\!\!+} (q_1+e,\ q_2) :: B_2'^{+e}\bigr)
 = A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}
```

に等しい。よって $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言により
$`B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}`$ であり、
第 3 段により結論が従う。

**(b-2) $`\neg(u + e \lt \ell_1)`$ のとき。**
まず $`B_2 = ()`$ である。$`B_2 = q :: B_2'`$ とすると、$`q`$ は $`B = D \mathbin{+\!\!+} B_2`$ の要素であるから
(h2) より $`u + e \lt q_1`$ であり、補助 2 より $`q_1 \le \ell_1`$、本場合の仮定より
$`\ell_1 \le u+e`$ であるから $`u+e \lt q_1 \le \ell_1 \le u+e`$ となって矛盾する。
よって $`B = D`$ であり、$`D \mathbin{+\!\!+} (\ell) = B \mathbin{+\!\!+} (\ell)`$ である。
$`u`$ と $`\ell_1`$ でさらに場合分けする。

- $`u \lt \ell_1`$ のとき。第 2 段の主張を $`B' := B`$、$`A_2' := (\ell)`$、$`Z' := ()`$ に適用する。
  分解の条件は $`B \mathbin{+\!\!+} (\ell) = B \mathbin{+\!\!+} ((\ell) \mathbin{+\!\!+} ())`$、
  $`\forall x \in B,\ u+e \lt x_1`$ は (h2)、
  $`\forall x \in (\ell),\ u \lt x_1`$ は本場合の仮定 $`u \lt \ell_1`$、
  $`(\mathrm{head}(\ell))_1 = \ell_1 \le u+e`$ は (b-2) の仮定、
  $`Z' = ()`$ は第 1 選言である。

- $`\neg(u \lt \ell_1)`$、すなわち $`\ell_1 \le u`$ のとき。
  第 2 段の主張を $`B' := B`$、$`A_2' := ()`$、$`Z' := (\ell)`$ に適用する。
  分解の条件は $`B \mathbin{+\!\!+} (\ell) = B \mathbin{+\!\!+} (() \mathbin{+\!\!+} (\ell))`$、
  $`A_2' = ()`$ は要素をもたず頭の条件は第 1 選言、
  $`(\mathrm{head}(\ell))_1 = \ell_1 \le u`$ である。

いずれの場合も
$`B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}`$ が得られ、
第 3 段により結論が従う。∎

<a id="t-shiftr0_add"></a>
## 定理: 平行移動の合成 (T.shiftr0_add)

### 定理

$`a, b \in \mathbb{N}`$、$`X \in \mathrm{PairSeq}`$ に対し

```math
X^{+(a+b)} = \bigl(X^{+b}\bigr)^{+a} .
```

### 証明

$`L^{+d}`$ は各要素 $`p`$ を $`(p_1 + d,\ p_2)`$ に置き換えるものであるから、
左辺は $`X`$ の各要素 $`p`$ を $`(p_1 + (a+b),\ p_2)`$ に置き換えた列であり、
右辺は $`p`$ をまず $`(p_1 + b,\ p_2)`$ に、次に $`((p_1 + b) + a,\ p_2)`$ に置き換えた列である。
$`\mathbb{N}`$ の加法の結合律と交換律により

```math
p_1 + (a+b) = (p_1 + b) + a
```

であるから、2 つの置き換えは各要素で同じ値を与える。要素ごとの置き換えが一致すれば
列全体も一致する。∎

<a id="t-sle_of_prefix"></a>
## 定理: 前部分列は広義に小さい (T.sle_of_prefix)

### 定理

$`X, Y \in \mathrm{PairSeq}`$ とし、$`X \sqsubseteq Y`$ を

```math
X \sqsubseteq Y :\iff \exists t \in \mathrm{PairSeq},\ Y = X \mathbin{+\!\!+} t
```

で定める（$`X`$ は $`Y`$ の**前部分列**である）。$`X \sqsubseteq Y`$ ならば
$`X \preceq_{\mathrm{lex}} Y`$。

### 証明

$`Y = X \mathbin{+\!\!+} t`$ なる $`t`$ を取り、$`t`$ の構成子で場合分けする。

- $`t = ()`$ のとき。$`Y = X \mathbin{+\!\!+} () = X`$ であるから、
  $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 1 選言が成り立つ。

- $`t = a :: t'`$ のとき。$`t \ne ()`$ であるから
  [T.seqlex_prefix](Seqlex.md#t-seqlex_prefix) を $`v := t`$、$`u := X`$ として適用して
  $`X \prec_{\mathrm{lex}} X \mathbin{+\!\!+} t = Y`$ を得る。D.sle の第 2 選言が成り立つ。∎

<a id="t-shiftr0_prefix"></a>
## 定理: 平行移動は前部分列関係を保つ (T.shiftr0_prefix)

### 定理

$`d \in \mathbb{N}`$、$`X, Y \in \mathrm{PairSeq}`$ とする。$`X \sqsubseteq Y`$ ならば
$`X^{+d} \sqsubseteq Y^{+d}`$。

### 証明

$`Y = X \mathbin{+\!\!+} t`$ なる $`t`$ を取る。
[T.shiftr0_append](Cofinality-3.md#t-shiftr0_append) より

```math
Y^{+d} = \bigl(X \mathbin{+\!\!+} t\bigr)^{+d} = X^{+d} \mathbin{+\!\!+} t^{+d}
```

である。よって $`t^{+d}`$ が $`X^{+d} \sqsubseteq Y^{+d}`$ の証人である。∎

<a id="t-prefix_append_left"></a>
## 定理: 共通の左因子と前部分列 (T.prefix_append_left)

### 定理

$`P, X, Y \in \mathrm{PairSeq}`$ とする。$`X \sqsubseteq Y`$ ならば
$`P \mathbin{+\!\!+} X \sqsubseteq P \mathbin{+\!\!+} Y`$。

### 証明

$`Y = X \mathbin{+\!\!+} t`$ なる $`t`$ を取る。連結の結合律より

```math
P \mathbin{+\!\!+} Y = P \mathbin{+\!\!+} \bigl(X \mathbin{+\!\!+} t\bigr) = \bigl(P \mathbin{+\!\!+} X\bigr) \mathbin{+\!\!+} t
```

である。よって $`t`$ が $`P \mathbin{+\!\!+} X \sqsubseteq P \mathbin{+\!\!+} Y`$ の証人である。∎

<a id="t-copies_length"></a>
## 定理: コピー塔の長さ (T.copies_length)

### 定理

$`d \in \mathbb{N}`$、$`\mathrm{blk} \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ に対し

```math
\bigl\lvert \mathrm{copies}_d(\mathrm{blk}, n)\bigr\rvert = n \cdot \lvert \mathrm{blk}\rvert .
```

### 証明

$`n`$ に関する帰納法（$`d`$, $`\mathrm{blk}`$ は固定する）。帰納法の述語は

```math
\Phi(n) :\equiv \bigl\lvert \mathrm{copies}_d(\mathrm{blk}, n)\bigr\rvert = n \cdot \lvert \mathrm{blk}\rvert .
```

- **基底段** $`n = 0`$：[T.copies_zero](Cnf-2.md#t-copies_zero) より
  $`\mathrm{copies}_d(\mathrm{blk}, 0) = ()`$ であり、その長さは $`0`$ である。
  一方 $`0 \cdot \lvert \mathrm{blk}\rvert = 0`$ である。

**帰納段** $`n = k + 1`$。帰納法の仮定は $`\Phi(k)`$、すなわち
$`\lvert \mathrm{copies}_d(\mathrm{blk}, k)\rvert = k \cdot \lvert \mathrm{blk}\rvert`$ である。
[T.copies_succ_back](Cofinality-3.md#t-copies_succ_back) より

```math
\mathrm{copies}_d(\mathrm{blk}, k+1)
 = \mathrm{copies}_d(\mathrm{blk}, k) \mathbin{+\!\!+} \mathrm{blk}^{+k d}
```

であるから、連結の長さは各因子の長さの和であり

```math
\bigl\lvert \mathrm{copies}_d(\mathrm{blk}, k+1)\bigr\rvert
 = \bigl\lvert \mathrm{copies}_d(\mathrm{blk}, k)\bigr\rvert + \bigl\lvert \mathrm{blk}^{+k d}\bigr\rvert .
```

[T.shiftr0_length](Cofinality-2.md#t-shiftr0_length) より
$`\lvert \mathrm{blk}^{+k d}\rvert = \lvert \mathrm{blk}\rvert`$ であり、帰納法の仮定と合わせて

```math
\bigl\lvert \mathrm{copies}_d(\mathrm{blk}, k+1)\bigr\rvert
 = k \cdot \lvert \mathrm{blk}\rvert + \lvert \mathrm{blk}\rvert = (k+1) \cdot \lvert \mathrm{blk}\rvert
```

を得る。よって $`\Phi(k+1)`$。∎

<a id="t-split_append_left"></a>
## 定理: 分割の存在形 (T.split_append_left)

### 定理

$`C, D, E, F \in \mathrm{PairSeq}`$ が $`C \mathbin{+\!\!+} D = E \mathbin{+\!\!+} F`$ と
$`\lvert E\rvert \le \lvert C\rvert`$ をみたすならば、$`K \in \mathrm{PairSeq}`$ が存在して

```math
C = E \mathbin{+\!\!+} K \qquad\text{かつ}\qquad F = K \mathbin{+\!\!+} D .
```

### 証明

$`K := \mathrm{drop}_{\lvert E\rvert} C`$ と取る。
[T.split_prefix_left](ArgDom-2.md#t-split_prefix_left) の 2 つの結論が求める 2 つの等式そのものである。∎

<a id="t-prefix_cons_append"></a>
## 定理: 共通の左因子と共通の列に続く前部分列 (T.prefix_cons_append)

### 定理

$`A, P, Q \in \mathrm{PairSeq}`$、$`c \in \mathbb{N}\times\mathbb{N}`$ とする。$`P \sqsubseteq Q`$ ならば

```math
A \mathbin{+\!\!+} c :: P \ \sqsubseteq\ A \mathbin{+\!\!+} c :: Q .
```

### 証明

$`Q = P \mathbin{+\!\!+} t`$ なる $`t`$ を取る。cons と連結の関係
$`c :: (P \mathbin{+\!\!+} t) = (c :: P) \mathbin{+\!\!+} t`$ および連結の結合律より

```math
A \mathbin{+\!\!+} c :: Q = A \mathbin{+\!\!+} \bigl((c :: P) \mathbin{+\!\!+} t\bigr)
 = \bigl(A \mathbin{+\!\!+} c :: P\bigr) \mathbin{+\!\!+} t
```

である。よって $`t`$ が求める証人である。∎

<a id="t-spineOK_of_nextrel1_strict"></a>
## 定理: 背骨条件の強形 (T.spineOK_of_nextrel1_strict)

### 定理

$`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$ とし

```math
\ell := (v_0 + d_0,\ w_0 + 1),
\qquad
M := \bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} (\ell),
\qquad
j_1 := \bigl\lvert G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr\rvert
```

とおく。$`\lvert G\rvert \to^M_1 j_1`$（[D.nextrel1](Pss.md#d-nextrel1)）ならば

```math
\mathrm{SpineOK}\bigl(R,\ v_0 + d_0,\ w_0 + 1\bigr).
```

（$`\mathrm{SpineOK}`$ [D.SpineOK](ArgDom.md#d-SpineOK)）

### 証明

$`\mathrm{SpineOK}`$ の定義（D.SpineOK）により、$`U, V \in \mathrm{PairSeq}`$ と
$`x \in \mathbb{N}\times\mathbb{N}`$ が

```math
R = U \mathbin{+\!\!+} x :: V,
\qquad x_1 \lt v_0 + d_0,
\qquad \forall y \in V,\ x_1 \lt y_1
```

をみたすとき $`w_0 + 1 \le x_2`$ を示せばよい。

$`\to^M_1`$ の定義（D.nextrel1）により、仮定 $`\lvert G\rvert \to^M_1 j_1`$ からとくに
条件 (5)

```math
\lvert G\rvert \le^M_0 j_1
```

と条件 (6)

```math
\forall j,\ \bigl(\lvert G\rvert \lt j \wedge j \le^M_0 j_1\bigr) \to M_{1,j_1} \le M_{1,j}
```

が得られる（$`\le^M_0`$ [D.le0](Pss.md#d-le0)、$`M_{i,j}`$ [D.entry](Pss.md#d-entry)）。
$`A := G \mathbin{+\!\!+} ((v_0,w_0) :: U)`$ とおく。

**第 1 段：位置の勘定。**
$`R = U \mathbin{+\!\!+} x :: V`$ を $`M`$ の定義に代入し、連結の結合律で並べ替えると

```math
M = A \mathbin{+\!\!+} \bigl(x :: (V \mathbin{+\!\!+} (\ell))\bigr)
```

である。長さは

```math
\lvert A\rvert = \lvert G\rvert + 1 + \lvert U\rvert,
\qquad
j_1 = \lvert G\rvert + 1 + \lvert R\rvert
    = \lvert G\rvert + 1 + \lvert U\rvert + 1 + \lvert V\rvert
    = \lvert A\rvert + 1 + \lvert V\rvert
```

である。とくに $`\lvert G\rvert \lt \lvert A\rvert`$ かつ $`\lvert A\rvert \le j_1`$ である。

[T.getD_append_right'](Cofinality.md#t-getD_append_right') を
$`A`$、$`x :: (V \mathbin{+\!\!+} (\ell))`$、$`i := 0`$ に適用すると
$`M\langle \lvert A\rvert\rangle = x`$ である。したがって
[T.entry_zero](Cofinality.md#t-entry_zero) と [T.entry_one](Cofinality.md#t-entry_one) より

```math
M_{0,\lvert A\rvert} = x_1, \qquad M_{1,\lvert A\rvert} = x_2 .
```

**第 2 段：位置 $`\lvert A\rvert`$ より右、$`j_1`$ までのすべての列は行 $`0`$ が上。**
すなわち

```math
\forall y,\ \bigl(\lvert A\rvert \lt y \wedge y \le j_1\bigr) \to M_{0,\lvert A\rvert} \lt M_{0,y}
```

を示す。$`\lvert A\rvert \lt y`$ より $`y = \lvert A\rvert + (t+1)`$ なる $`t`$ が取れる。
第 1 段の分解と [T.getD_append_right'](Cofinality.md#t-getD_append_right') により

```math
M\bigl\langle \lvert A\rvert + (t+1)\bigr\rangle
 = \bigl(x :: (V \mathbin{+\!\!+} (\ell))\bigr)\langle t+1\rangle
 = \bigl(V \mathbin{+\!\!+} (\ell)\bigr)\langle t\rangle
```

である。$`y \le j_1 = \lvert A\rvert + 1 + \lvert V\rvert`$ より $`t \le \lvert V\rvert`$ であり、
$`t`$ で場合分けする。

- $`t \lt \lvert V\rvert`$ のとき。$`(V \mathbin{+\!\!+} (\ell))\langle t\rangle = V\langle t\rangle`$ であり、
  $`t \lt \lvert V\rvert`$ よりこれは $`V`$ の要素である。仮定 $`\forall y \in V,\ x_1 \lt y_1`$ を
  これに適用して $`x_1 \lt (V\langle t\rangle)_1`$、すなわち
  $`M_{0,\lvert A\rvert} \lt M_{0,y}`$ を得る。

- $`t = \lvert V\rvert`$ のとき。ふたたび
  [T.getD_append_right'](Cofinality.md#t-getD_append_right') を $`V`$、$`(\ell)`$、$`i := 0`$ に適用して
  $`(V \mathbin{+\!\!+} (\ell))\langle \lvert V\rvert\rangle = \ell`$ である。
  仮定 $`x_1 \lt v_0 + d_0 = \ell_1`$ より $`M_{0,\lvert A\rvert} \lt M_{0,y}`$ を得る。

**第 3 段：$`x`$ は落とされる列の行 $`0`$ の祖先である。**
[T.le0_through_pivot](Column-4.md#t-le0_through_pivot) を
$`a := \lvert G\rvert`$、$`\rho := \lvert A\rvert`$、$`b := j_1`$ として適用する。
仮定は条件 (5) の $`\lvert G\rvert \le^M_0 j_1`$、第 1 段の $`\lvert G\rvert \lt \lvert A\rvert`$ と
$`\lvert A\rvert \le j_1`$、および第 2 段である。結論は

```math
\lvert A\rvert \le^M_0 j_1 .
```

**第 4 段：最小性の条件を使う。**
[T.getD_append_right'](Cofinality.md#t-getD_append_right') を
$`G \mathbin{+\!\!+} ((v_0,w_0) :: R)`$、$`(\ell)`$、$`i := 0`$ に適用して
$`M\langle j_1\rangle = \ell`$ である。よって
[T.entry_one](Cofinality.md#t-entry_one) より $`M_{1,j_1} = \ell_2 = w_0 + 1`$ である。

条件 (6) を $`j := \lvert A\rvert`$ に適用する。その前件は第 1 段の
$`\lvert G\rvert \lt \lvert A\rvert`$ と第 3 段の $`\lvert A\rvert \le^M_0 j_1`$ である。
したがって

```math
w_0 + 1 = M_{1,j_1} \le M_{1,\lvert A\rvert} = x_2 . \qquad \blacksquare
```
