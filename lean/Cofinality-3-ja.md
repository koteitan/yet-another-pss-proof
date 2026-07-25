[← README](README-ja.md) | [English](Cofinality-3.md) | [Japanese](Cofinality-3-ja.md) | Cofinality [1](Cofinality-ja.md) [2](Cofinality-2-ja.md) **3**

<a id="d-AscArgDom"></a>
## 定義: 上昇コピーの引数支配 (D.AscArgDom)

命題 $`\mathrm{AscArgDom}`$ を次で定める。ここで $`B := (v_0,w_0) :: R`$、
$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr)`$ と略記する。

```math
\begin{aligned}
\mathrm{AscArgDom} :\equiv\ &\forall G, R, S \in \mathrm{PairSeq},\ \forall v_0, w_0, d_0 \in \mathbb{N}, \cr
&\quad H \in \mathrm{ST\_PS}
  \ \to\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS} \cr
&\quad \to\ \bigl(\forall x \in R,\ v_0 \lt x_1\bigr) \ \to\ 0 \lt d_0 \cr
&\quad \to\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert \cr
&\quad \to\ \exists m,\
   \mathrm{tw}_{v_0+d_0} S \preceq_{\mathrm{lex}}
     \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B^{+d_0},\ m)\bigr)^{+d_0} .
\end{aligned}
```

（$`\mathrm{PairSeq}`$ [D.PairSeq](Pss-ja.md#d-PairSeq)、$`\mathrm{ST\_PS}`$ [D.ST_PS](Pss-ja.md#d-ST_PS)、
$`j_0 \to^M_1 j_1`$ [D.nextrel1](Pss-ja.md#d-nextrel1)、
$`\mathrm{tw}_a L`$ と $`\mathrm{tr}`$ [D.translate](Term-ja.md#d-translate)、
$`\preceq_{\mathrm{lex}}`$ [D.sle](Cofinality-ja.md#d-sle)、
$`\mathrm{cp}_d(B,n)`$ [D.copies](Cnf-2-ja.md#d-copies)、$`L^{+d}`$ [D.shiftr0](Cnf-2-ja.md#d-shiftr0)）

<a id="t-shiftr0_append"></a>
## 定理: 平行移動は連結を保つ (T.shiftr0_append)

### 定理

$`d \in \mathbb{N}`$、$`A, B \in \mathrm{PairSeq}`$ に対し
$`(A \mathbin{+\!\!+} B)^{+d} = A^{+d} \mathbin{+\!\!+} B^{+d}`$。

### 証明

$`X^{+d}`$ の定義（D.shiftr0）より $`X^{+d}`$ は $`X`$ の各要素への写像 $`x \mapsto (x_1+d,\ x_2)`$ の
適用であり、連結した列の各要素への写像の適用は、それぞれに適用してから連結したものに等しい。∎

<a id="t-copies_succ_back"></a>
## 定理: コピー塔の末尾の 1 個 (T.copies_succ_back)

### 定理

$`d, n \in \mathbb{N}`$、$`B \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{cp}_d(B, n+1) = \mathrm{cp}_d(B, n) \mathbin{+\!\!+} B^{+nd} .
```

### 証明

$`\mathrm{cp}_d`$ の定義（D.copies）は、添字 $`k`$ を $`0`$ から $`n`$ まで（すなわち長さ $`n+1`$ の
添字列にわたって）走らせた $`B^{+kd}`$ の連結である。添字列を先頭 $`n`$ 個と最後の 1 個 $`k = n`$ に
分ければ

```math
\mathrm{cp}_d(B, n+1)
 = \bigl(B^{+0\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d}\bigr) \mathbin{+\!\!+} B^{+nd}
```

であり、括弧の中は $`\mathrm{cp}_d(B, n)`$ そのものである。∎

<a id="t-asc_crux1_of_argdom"></a>
## 定理: 引数支配から頭を取った核心 (T.asc_crux1_of_argdom)

### 定理

$`\mathrm{AscArgDom}`$ ならば $`\mathrm{AscCrux1}`$（[D.AscCrux1](Cofinality-2-ja.md#d-AscCrux1)）。

### 証明

$`G, R, S \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$ を取り、$`\mathrm{AscCrux1}`$ の
5 つの仮定

```math
\begin{aligned}
&(1)\ H \in \mathrm{ST\_PS}
  \quad\bigl(H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} ((v_0+d_0,\ w_0+1)),\ B := (v_0,w_0) :: R\bigr), \cr
&(2)\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS}, \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ 0 \lt d_0, \cr
&(5)\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert
\end{aligned}
```

を仮定する。$`\mathrm{AscArgDom}`$ をこの (1)〜(5) に適用して、$`m`$ と

```math
(\ast)\qquad S_{\mathrm{hi}} \preceq_{\mathrm{lex}}
  \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0},
\qquad
S_{\mathrm{hi}} := \mathrm{tw}_{v_0+d_0} S,\quad B' := B^{+d_0}
```

を得る。さらに $`S_{\mathrm{lo}} := \mathrm{dw}_{v_0+d_0} S`$ とおくと
$`S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}} = S`$ である。
また $`X^{+d}`$ の定義（D.shiftr0）より

```math
B' = B^{+d_0} = (v_0 + d_0,\ w_0) :: R^{+d_0}
```

である。

**第 1 段：$`\forall x \in R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m),\ v_0 \lt x_1`$。**
$`x \in R`$ のときは (3) による。$`x \in \mathrm{cp}_{d_0}(B', m)`$ のときは次のようにする。
(3) より $`\forall y \in R,\ v_0 \le y_1`$ であるから、
[T.mem_shiftr0_le](Cofinality-2-ja.md#t-mem_shiftr0_le) を $`d := v_0`$、$`e := d_0`$ として適用して
$`\forall y \in R^{+d_0},\ v_0 + d_0 \le y_1`$ を得る。
[T.copies_v0_le](Cnf-3-ja.md#t-copies_v0_le) を、基点 $`v_0 + d_0`$、行 $`1`$ の値 $`w_0`$、
尾部 $`R^{+d_0}`$（すなわち $`B' = (v_0+d_0,\ w_0) :: R^{+d_0}`$）、$`d := d_0`$、$`n := m`$ として
適用すると $`v_0 + d_0 \le x_1`$ を得る。(4) より $`v_0 \lt v_0 + d_0 \le x_1`$ である。

**第 2 段：$`S_{\mathrm{lo}} = ()`$ または $`(\mathrm{head}\,S_{\mathrm{lo}})_1 \le v_0 + d_0`$。**
$`S_{\mathrm{lo}} = \mathrm{dw}_{v_0+d_0} S`$ が空でなければ、その先頭要素 $`z`$ は述語を破る、
すなわち $`\neg(v_0 + d_0 \lt z_1)`$ をみたすから $`z_1 \le v_0 + d_0`$ である。

**第 3 段：目標の展開。**
求める添字として $`m + 2`$ を取る（$`1 \le m+2`$）。
$`E := \bigl((B')^{+m d_0}\bigr)^{+d_0}`$ とおく。

```math
\begin{aligned}
\bigl(\mathrm{cp}_{d_0}(B,\ m+2)\bigr)^{+d_0}
 &= \mathrm{cp}_{d_0}(B',\ m+2) \cr
 &= B' \mathbin{+\!\!+} \bigl(\mathrm{cp}_{d_0}(B',\ m+1)\bigr)^{+d_0} \cr
 &= B' \mathbin{+\!\!+} \Bigl(\bigl(\mathrm{cp}_{d_0}(B',\ m)\bigr)^{+d_0} \mathbin{+\!\!+} E\Bigr) \cr
 &= (v_0+d_0,\ w_0) :: \Bigl(R^{+d_0} \mathbin{+\!\!+}
      \bigl(\mathrm{cp}_{d_0}(B',\ m)\bigr)^{+d_0} \mathbin{+\!\!+} E\Bigr) \cr
 &= (v_0+d_0,\ w_0) :: \Bigl(\bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',\ m)\bigr)^{+d_0}
      \mathbin{+\!\!+} E\Bigr).
\end{aligned}
```

第 1 の等号は [T.shiftr0_copies](Cofinality-2-ja.md#t-shiftr0_copies)（$`B' = B^{+d_0}`$）、
第 2 の等号は [T.copies_succ_front](Cnf-3-ja.md#t-copies_succ_front)、
第 3 の等号は [T.copies_succ_back](#t-copies_succ_back) と [T.shiftr0_append](#t-shiftr0_append)、
第 4 の等号は $`B' = (v_0+d_0,\ w_0) :: R^{+d_0}`$ と結合律、
第 5 の等号は [T.shiftr0_append](#t-shiftr0_append) による。

**第 4 段：$`E`$ の形。**
$`B' = (v_0+d_0,\ w_0) :: R^{+d_0} \ne ()`$ であり、
[T.shiftr0_length](Cofinality-2-ja.md#t-shiftr0_length) を 2 回使うと $`\lvert E\rvert = \lvert B'\rvert \gt 0`$、
すなわち $`E \ne ()`$ である。また $`X^{+d}`$ の定義（D.shiftr0）は先頭要素を先頭要素に写すから、
$`B'`$ の先頭 $`(v_0+d_0,\ w_0)`$ に対応する $`E`$ の先頭は
$`\bigl(v_0 + d_0 + m d_0 + d_0,\ w_0\bigr)`$ であり、

```math
(\mathrm{head}\,E)_1 = v_0 + d_0 + m d_0 + d_0 .
```

**第 5 段：頭の消去。**
示すべきは第 3 段より

```math
(v_0+d_0,\ w_0) :: S \ \preceq_{\mathrm{lex}}\
 (v_0+d_0,\ w_0) :: \Bigl(\bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0} \mathbin{+\!\!+} E\Bigr)
```

である。両辺は長さ $`1`$ の列 $`\bigl((v_0+d_0,\ w_0)\bigr)`$ を共通の左側にもつ連結であるから、
[T.sle_append_cancel](Cofinality-ja.md#t-sle_append_cancel) によりこれは

```math
S \ \preceq_{\mathrm{lex}}\
 \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0} \mathbin{+\!\!+} E
```

と同値である。$`(\ast)`$ を $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）に従って 2 つの場合に分ける。

**(a) $`S_{\mathrm{hi}} = \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0}`$ のとき。**
$`S = S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}}`$ であるから、示すべきは

```math
S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}} \ \preceq_{\mathrm{lex}}\ S_{\mathrm{hi}} \mathbin{+\!\!+} E
```

であり、[T.sle_append_cancel](Cofinality-ja.md#t-sle_append_cancel) により
$`S_{\mathrm{lo}} \preceq_{\mathrm{lex}} E`$ を示せばよい。第 2 段で場合分けする。

- $`S_{\mathrm{lo}} = ()`$ のとき。第 4 段より $`E \ne ()`$ であるから、
  $`\prec_{\mathrm{lex}}`$ の定義（[D.seqlex](Seqlex-ja.md#d-seqlex)）の第 1 式により
  $`() \prec_{\mathrm{lex}} E`$ であり、
  $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言が成り立つ。
- $`S_{\mathrm{lo}} = z :: Z`$ かつ $`z_1 \le v_0 + d_0`$ のとき。第 4 段より $`E \ne ()`$ だから
  $`E = e :: E'`$ と書け、$`e_1 = v_0 + d_0 + m d_0 + d_0`$ である。
  (4) の $`0 \lt d_0`$ より $`v_0 + d_0 \lt v_0 + d_0 + m d_0 + d_0`$ であるから
  $`z_1 \le v_0 + d_0 \lt e_1`$ であり、
  $`\prec_{\mathrm{p}}`$ の定義（[D.pairlt](Seqlex-ja.md#d-pairlt)）の第 1 選言により
  $`z \prec_{\mathrm{p}} e`$、$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式の第 1 選言により
  $`z :: Z \prec_{\mathrm{lex}} e :: E'`$ を得る。

**(b) $`S_{\mathrm{hi}} \prec_{\mathrm{lex}} \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0}`$ のとき。**
[T.seqlex_splice](Cofinality-2-ja.md#t-seqlex_splice) を、小さい側の列を $`S_{\mathrm{hi}}`$、
大きい側の列を $`\bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0}`$、
小さい側に付ける列を $`S_{\mathrm{lo}}`$、大きい側に付ける列を $`E`$ として適用する。
残る仮定は次の選言である。

```math
S_{\mathrm{lo}} = ()
 \quad\vee\quad
\forall x \in \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',m)\bigr)^{+d_0},\
 \mathrm{head}\,S_{\mathrm{lo}} \prec_{\mathrm{p}} x
```

第 2 段で場合分けする。

- $`S_{\mathrm{lo}} = ()`$ のとき。第 1 選言である。
- $`(\mathrm{head}\,S_{\mathrm{lo}})_1 \le v_0 + d_0`$ のとき。
  $`x \in \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',m)\bigr)^{+d_0}`$ とすると、
  [T.mem_shiftr0](Cnf-2-ja.md#t-mem_shiftr0) よりある $`y \in R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',m)`$ が
  存在して $`x = (y_1 + d_0,\ y_2)`$ である。第 1 段より $`v_0 \lt y_1`$ であるから
  $`(\mathrm{head}\,S_{\mathrm{lo}})_1 \le v_0 + d_0 \lt y_1 + d_0 = x_1`$ であり、
  $`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 1 選言により
  $`\mathrm{head}\,S_{\mathrm{lo}} \prec_{\mathrm{p}} x`$ が成り立つ。

こうして

```math
S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}} \prec_{\mathrm{lex}}
 \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0} \mathbin{+\!\!+} E
```

が得られ、$`S = S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}}`$ であるから、
第 5 段の目標が $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言として得られた。∎

<a id="t-asc_head_step"></a>
## 定理: 上昇コピーの核心の頭段 (T.asc_head_step)

### 定理

$`\mathrm{AscCrux1}`$ ならば $`\mathrm{AscCrux}`$（[D.AscCrux](Cofinality-2-ja.md#d-AscCrux)）。

### 証明

$`G, R, S \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell, q \in \mathbb{N}\times\mathbb{N}`$ を
取り、$`B := (v_0,w_0) :: R`$、$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$ とおいて
$`\mathrm{AscCrux}`$ の 8 つの仮定

```math
\begin{aligned}
&(1)\ H \in \mathrm{ST\_PS}, \qquad
 (2)\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S \in \mathrm{ST\_PS}, \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \qquad
 (4)\ 0 \lt d_0, \cr
&(5)\ \ell_2 = w_0 + 1, \qquad
 (6)\ \ell_1 = v_0 + d_0, \cr
&(7)\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert, \qquad
 (8)\ q \prec_{\mathrm{p}} \ell
\end{aligned}
```

を仮定する。(5)(6) より対 $`\ell`$ は両成分が定まり
$`\ell = (v_0 + d_0,\ w_0 + 1)`$ である。$`q`$ で場合分けする。

**(a) $`q = (v_0 + d_0,\ w_0)`$ のとき。**
$`\ell = (v_0+d_0,\ w_0+1)`$ により (1) と (7) を書き換えると、それぞれ
$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr) \in \mathrm{ST\_PS}`$ と
$`\lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert`$（$`H`$ も同じく書き換わる）になる。
また (2) は $`q = (v_0+d_0,\ w_0)`$ により
$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS}`$ である。
これらと (3)(4) に $`\mathrm{AscCrux1}`$ を適用すれば、求める $`m`$ と
$`q :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B,m)\bigr)^{+d_0}`$ が得られる。

**(b) $`q \ne (v_0 + d_0,\ w_0)`$ のとき。**
$`m := 1`$ と取る。[T.copies_one](Cnf-3-ja.md#t-copies_one) より $`\mathrm{cp}_{d_0}(B, 1) = B`$ であり、
$`X^{+d}`$ の定義（D.shiftr0）より

```math
B^{+d_0} = (v_0 + d_0,\ w_0) :: R^{+d_0}
```

である。よって $`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式の第 1 選言により
$`q \prec_{\mathrm{p}} (v_0+d_0,\ w_0)`$ を示せばよい。
$`\ell = (v_0+d_0,\ w_0+1)`$ を (8) に代入すると、$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）より

```math
q_1 \lt v_0 + d_0 \quad\text{または}\quad \bigl(q_1 = v_0 + d_0 \ \wedge\ q_2 \lt w_0 + 1\bigr)
```

である。また $`q \ne (v_0+d_0,\ w_0)`$ は、対の相等が成分ごとの相等であることから
$`\neg\bigl(q_1 = v_0 + d_0 \ \wedge\ q_2 = w_0\bigr)`$ と同値である。場合分けする。

- $`q_1 \lt v_0 + d_0`$ のとき。$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 1 選言が成り立つ。
- $`q_1 = v_0 + d_0`$ かつ $`q_2 \lt w_0 + 1`$ のとき。$`q_2 \le w_0`$ である。
  もし $`q_2 = w_0`$ なら $`q_1 = v_0 + d_0`$ と合わせて上の否定に反するから $`q_2 \ne w_0`$、
  よって $`q_2 \lt w_0`$ である。$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 2 選言が成り立つ。

いずれの場合も $`q :: S \prec_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B,1)\bigr)^{+d_0}`$ であり、
$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言により結論を得る。∎

<a id="t-seqlex_cof_bad"></a>
## 定理: 第 4 分岐の共終性 (T.seqlex_cof_bad)

### 定理

$`\mathrm{AscCrux}`$ を仮定する。$`M, N \in \mathrm{PairSeq}`$ とし
$`j_1 := \lvert M\rvert - 1`$ とおく。

```math
M \in \mathrm{ST\_PS},\quad
N \in \mathrm{ST\_PS},\quad
1 \lt \lvert M\rvert,\quad
\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr),\quad
N \prec_{\mathrm{lex}} M
```

ならば、$`1 \le n`$ なる $`n`$ が存在して $`N \preceq_{\mathrm{lex}} M[n]`$。

（$`M_{i,j}`$ [D.entry](Pss-ja.md#d-entry)、$`M[n]`$ [D.oper](Pss-ja.md#d-oper)）

### 証明

**第 1 段：ブロック分解。**
$`1 \lt \lvert M\rvert`$ より $`0 \lt \lvert M\rvert`$ であるから、
[T.hasParent_last_ST_PS](Cofinality-ja.md#t-hasParent_last_ST_PS) により
$`\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M, j_1),\ j_1\bigr)`$ が成り立つ
（$`\mathrm{hasParent}`$ [D.hasParent](Pss-ja.md#d-hasParent)、$`\mathrm{idx}_1`$ [D.idx1](Pss-ja.md#d-idx1)）。
また [T.blockok_ST_PS](Seqlex-2-ja.md#t-blockok_ST_PS) と
$`\mathrm{blockok}`$ の定義（[D.blockok](Seqlex-ja.md#d-blockok)）の
第 3 連言子より $`\mathrm{steps}_1(M)`$（[D.steps1](Seqlex-ja.md#d-steps1)）、
[T.r1ok_ST_PS](Column-3-ja.md#t-r1ok_ST_PS) より
$`\mathrm{r1ok}(M)`$（[D.r1ok](Column-2-ja.md#d-r1ok)）である。これらに [T.oper_bad_blocks_all](Cofinality-ja.md#t-oper_bad_blocks_all) を適用して
$`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ を取り、
$`B := (v_0,w_0) :: R`$ とおくと

```math
\begin{aligned}
&(1)\ M = (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell), \cr
&(2)\ \forall n \ge 1,\ M[n] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n), \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ v_0 \lt \ell_1, \cr
&(5)\ \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr) \ \vee\
      \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
            \wedge \lvert G\rvert \to^M_1 j_1\bigr)
\end{aligned}
```

が成り立つ。

**第 2 段：$`N`$ の場合分け。**
(1) により仮定 $`N \prec_{\mathrm{lex}} M`$ は
$`N \prec_{\mathrm{lex}} (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$ である。
[T.seqlex_snoc_cases](Cofinality-ja.md#t-seqlex_snoc_cases) を $`D := G \mathbin{+\!\!+} B`$ として適用すると、
次の 2 つの場合に分かれる。

**(a) $`N \preceq_{\mathrm{lex}} G \mathbin{+\!\!+} B`$ のとき。**
$`n := 1`$ と取る。(2) と [T.copies_one](Cnf-3-ja.md#t-copies_one) より
$`M[1] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B,1) = G \mathbin{+\!\!+} B`$ であるから、
仮定がそのまま結論である。

**(b) $`N = (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S`$ かつ $`q \prec_{\mathrm{p}} \ell`$ なる
$`q, S`$ が存在するとき。**
まず、$`1 \le m`$ なる $`m`$ で

```math
(\dagger)\qquad q :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B, m)\bigr)^{+d_0}
```

をみたすものを構成する。(5) の選言で場合分けする。

**(b-1) $`d_0 = 0`$、$`\ell_2 = 0`$、$`\ell_1 = v_0 + 1`$ のとき。**
$`X^{+0} = X`$（$`X^{+d}`$ の定義 D.shiftr0 で $`d = 0`$ とすると各要素が変わらない）であるから、
$`(\dagger)`$ は $`q :: S \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$ と同じ主張である。
[T.crux_zero](Cofinality-2-ja.md#t-crux_zero) を、その仮定 (1) として
$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S = N \in \mathrm{ST\_PS}`$、
仮定 (2) として本証明の (3)、仮定 (3) として $`\ell_2 = 0 \wedge \ell_1 = v_0+1`$、
仮定 (4) として $`q \prec_{\mathrm{p}} \ell`$ を与えて適用すればよい。

**(b-2) $`0 \lt d_0`$、$`\ell_2 = w_0 + 1`$、$`\ell_1 = v_0 + d_0`$、
$`\lvert G\rvert \to^M_1 j_1`$ のとき。**
(1) より $`\lvert M\rvert = \lvert G \mathbin{+\!\!+} B\rvert + 1`$ であるから
$`j_1 = \lvert M\rvert - 1 = \lvert G \mathbin{+\!\!+} B\rvert`$ であり、(1) と合わせて
$`\lvert G\rvert \to^M_1 j_1`$ は

```math
\lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert,
\qquad H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)
```

と同じ主張である。$`\mathrm{AscCrux}`$ を、その 8 つの仮定として
$`H = M \in \mathrm{ST\_PS}`$、$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S = N \in \mathrm{ST\_PS}`$、
本証明の (3)、$`0 \lt d_0`$、$`\ell_2 = w_0+1`$、$`\ell_1 = v_0+d_0`$、
いま書き換えた $`\lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert`$、$`q \prec_{\mathrm{p}} \ell`$ を
与えて適用すると $`(\dagger)`$ を得る。

**第 3 段：結論。**
$`n := m + 1`$ と取る（$`1 \le m + 1`$）。(2) と
[T.copies_succ_front](Cnf-3-ja.md#t-copies_succ_front) より

```math
M[m+1] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, m+1)
 = G \mathbin{+\!\!+} \Bigl(B \mathbin{+\!\!+} \bigl(\mathrm{cp}_{d_0}(B,m)\bigr)^{+d_0}\Bigr)
```

であり、他方 (b) の $`N`$ は結合律により
$`N = G \mathbin{+\!\!+} \bigl(B \mathbin{+\!\!+} q :: S\bigr)`$ である。
[T.sle_append_cancel](Cofinality-ja.md#t-sle_append_cancel) を左側 $`G`$ について適用し、ついで左側 $`B`$ について
適用すると、示すべき $`N \preceq_{\mathrm{lex}} M[m+1]`$ は $`(\dagger)`$ と同値になる。∎

<a id="t-seqlex_cofinality_of_crux"></a>
## 定理: 核心からの列辞書式共終性 (T.seqlex_cofinality_of_crux)

### 定理

$`\mathrm{AscCrux}`$ ならば $`\mathrm{SeqlexCofinality}`$（[D.SeqlexCofinality](Cofinality-ja.md#d-SeqlexCofinality)）。

### 証明

$`M, N \in \mathrm{PairSeq}`$ を取り、$`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、
$`N \prec_{\mathrm{lex}} M`$ を仮定する。$`j_1 := \lvert M\rvert - 1`$ とおく。
求めるのは $`1 \le n`$ なる $`n`$ で $`N \preceq_{\mathrm{lex}} M[n]`$ をみたすものである。

**(a) $`j_1 = 0`$ のとき。**
[T.seqlex_cof_short](Cofinality-ja.md#t-seqlex_cof_short) を適用する。

**(b) $`j_1 \ne 0`$ かつ $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。**
自然数の減法は切り捨て減法であるから、$`\lvert M\rvert - 1 \ne 0`$ は $`1 \lt \lvert M\rvert`$ と
同値である。[T.seqlex_cof_zero](Cofinality-ja.md#t-seqlex_cof_zero) を適用する。

**(c) $`j_1 \ne 0`$ かつ $`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$ のとき。**
(b) と同じく $`1 \lt \lvert M\rvert`$ である。
[T.seqlex_cof_bad](#t-seqlex_cof_bad) を $`\mathrm{AscCrux}`$ の仮定のもとで適用する。

3 つの場合は $`j_1 = 0`$ か否か、および $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ か否かで
尽くされている。∎

<a id="t-pss_cofinality_of_crux"></a>
## 定理: 核心からの PSS 共終性 (T.pss_cofinality_of_crux)

### 定理

$`\mathrm{AscCrux1}`$ を仮定する。$`M, N \in \mathrm{PairSeq}`$ が
$`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ を
みたすならば、$`1 \le n`$ なる $`n`$ が存在して
$`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$。

（$`\prec`$ [D.olt](Term-ja.md#d-olt)、$`\preceq`$ [D.ole](Term-ja.md#d-ole)）

### 証明

[T.asc_head_step](#t-asc_head_step) を仮定 $`\mathrm{AscCrux1}`$ に適用して $`\mathrm{AscCrux}`$ を得る。
これに [T.seqlex_cofinality_of_crux](#t-seqlex_cofinality_of_crux) を適用して
$`\mathrm{SeqlexCofinality}`$ を得る。
これに [T.pss_cofinality_of_seqlex](Cofinality-ja.md#t-pss_cofinality_of_seqlex) を
$`M`$、$`N`$、および 3 つの仮定 $`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ とともに適用すれば結論を得る。∎

<a id="t-pss_cofinality_of_argdom"></a>
## 定理: 引数支配からの PSS 共終性 (T.pss_cofinality_of_argdom)

### 定理

$`\mathrm{AscArgDom}`$ を仮定する。$`M, N \in \mathrm{PairSeq}`$ が
$`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ を
みたすならば、$`1 \le n`$ なる $`n`$ が存在して
$`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$。

### 証明

[T.asc_crux1_of_argdom](#t-asc_crux1_of_argdom) を仮定 $`\mathrm{AscArgDom}`$ に適用して
$`\mathrm{AscCrux1}`$ を得る。これに [T.pss_cofinality_of_crux](#t-pss_cofinality_of_crux) を
$`M`$、$`N`$、および 3 つの仮定 $`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ とともに適用すれば結論を得る。∎
