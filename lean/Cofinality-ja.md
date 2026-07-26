[← README](README-ja.md) | [English](Cofinality.md) | [Japanese](Cofinality-ja.md) | Cofinality **1** [2](Cofinality-2-ja.md) [3](Cofinality-3-ja.md)

<a id="t-pairlt_trans"></a>
## 定理: 対の順序の推移律 (T.pairlt_trans)

### 定理

$`p, q, r \in \mathbb{N}\times\mathbb{N}`$ とする。$`p \prec_{\mathrm{p}} q`$（[D.pairlt](Seqlex-ja.md#d-pairlt)）かつ
$`q \prec_{\mathrm{p}} r`$ ならば $`p \prec_{\mathrm{p}} r`$。

### 証明

$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）は

```math
x \prec_{\mathrm{p}} y \iff x_1 \lt y_1 \ \vee\ (x_1 = y_1 \wedge x_2 \lt y_2)
```

である。仮定 $`p \prec_{\mathrm{p}} q`$ は次のいずれかである。

- (1) $`p_1 \lt q_1`$
- (2) $`p_1 = q_1 \wedge p_2 \lt q_2`$

仮定 $`q \prec_{\mathrm{p}} r`$ は次のいずれかである。

- (I) $`q_1 \lt r_1`$
- (II) $`q_1 = r_1 \wedge q_2 \lt r_2`$

4 通りすべてについて、$`p \prec_{\mathrm{p}} r`$ の右辺のどの選言が成り立つかを示す。

| | (I) | (II) |
|---|---|---|
| **(1)** | $`p_1 \lt r_1`$ | $`p_1 \lt r_1`$ |
| **(2)** | $`p_1 \lt r_1`$ | $`p_1 = r_1 \wedge p_2 \lt r_2`$ |

各欄の根拠は次の通りである。

- **(1)(I)**：$`p_1 \lt q_1`$ と $`q_1 \lt r_1`$ に $`\mathbb{N}`$ の $`\lt`$ の推移律を適用する。
- **(1)(II)**：$`q_1 = r_1`$ を $`p_1 \lt q_1`$ に代入して $`p_1 \lt r_1`$。
- **(2)(I)**：$`p_1 = q_1`$ を $`q_1 \lt r_1`$ に代入して $`p_1 \lt r_1`$。
- **(2)(II)**：$`p_1 = q_1 = r_1`$ であり、$`p_2 \lt q_2`$ と $`q_2 \lt r_2`$ に $`\mathbb{N}`$ の $`\lt`$ の
  推移律を適用して $`p_2 \lt r_2`$。∎

<a id="t-seqlex_trans"></a>
## 定理: 列辞書式順序の推移律 (T.seqlex_trans)

### 定理

$`A, B, C \in \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）とする。
$`A \prec_{\mathrm{lex}} B`$（[D.seqlex](Seqlex-ja.md#d-seqlex)）かつ $`B \prec_{\mathrm{lex}} C`$ ならば
$`A \prec_{\mathrm{lex}} C`$。

### 証明

$`A`$ の構成子（$`()`$ か $`::`$ か）に関する帰納法を行う（$`B`$, $`C`$ は全称量化したまま動かす）。
帰納法の述語は

```math
\Phi(A) :\equiv \forall B, C \in \mathrm{PairSeq},\
  \bigl(A \prec_{\mathrm{lex}} B \wedge B \prec_{\mathrm{lex}} C\bigr) \to A \prec_{\mathrm{lex}} C .
```

- **基底段** $`A = ()`$：$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式より、示すべきことは
  $`C \ne ()`$ である。$`C = ()`$ と仮定して矛盾を導く。仮定 $`B \prec_{\mathrm{lex}} ()`$ について
  $`B`$ の構成子で分ける。$`B = ()`$ なら定義（D.seqlex）の第 1 式より
  $`B \prec_{\mathrm{lex}} ()`$ は $`() \ne ()`$ であり偽である。$`B = b :: B'`$ なら
  定義（D.seqlex）の第 2 式より $`B \prec_{\mathrm{lex}} ()`$ は $`\bot`$ である。
  いずれも矛盾であるから $`C \ne ()`$。

- **帰納段** $`A = a :: A'`$：$`\Phi(A')`$ を仮定する。
  $`B`$, $`C`$ を取り $`a :: A' \prec_{\mathrm{lex}} B`$、$`B \prec_{\mathrm{lex}} C`$ とする。
  $`B = ()`$ とすると定義（D.seqlex）の第 2 式より第 1 の仮定が $`\bot`$ になるから
  $`B = b :: B'`$ と書ける。$`C = ()`$ とするとやはり定義（D.seqlex）の第 2 式より
  第 2 の仮定が $`\bot`$ になるから $`C = c :: C'`$ と書ける。
  定義（D.seqlex）の第 3 式より第 1 の仮定は次のいずれかである。

  - (1) $`a \prec_{\mathrm{p}} b`$
  - (2) $`a = b \wedge A' \prec_{\mathrm{lex}} B'`$

  同じく第 2 の仮定は次のいずれかである。

  - (I) $`b \prec_{\mathrm{p}} c`$
  - (II) $`b = c \wedge B' \prec_{\mathrm{lex}} C'`$

  4 通りすべてについて、定義（D.seqlex）の第 3 式の右辺のどの選言が成り立つかを示す。

  | | (I) | (II) |
  |---|---|---|
  | **(1)** | $`a \prec_{\mathrm{p}} c`$ | $`a \prec_{\mathrm{p}} c`$ |
  | **(2)** | $`a \prec_{\mathrm{p}} c`$ | $`a = c \wedge A' \prec_{\mathrm{lex}} C'`$ |

  各欄の根拠は次の通りである。

  - **(1)(I)**：[T.pairlt_trans](#t-pairlt_trans) を $`a \prec_{\mathrm{p}} b`$ と
    $`b \prec_{\mathrm{p}} c`$ に適用する。
  - **(1)(II)**：$`b = c`$ を $`a \prec_{\mathrm{p}} b`$ に代入する。
  - **(2)(I)**：$`a = b`$ を $`b \prec_{\mathrm{p}} c`$ に代入する。
  - **(2)(II)**：$`a = b = c`$ であり、$`A' \prec_{\mathrm{lex}} B'`$ と $`B' \prec_{\mathrm{lex}} C'`$ に
    帰納法の仮定 $`\Phi(A')`$ を適用して $`A' \prec_{\mathrm{lex}} C'`$ を得る。

  いずれの場合も $`a :: A' \prec_{\mathrm{lex}} c :: C'`$ が得られたので $`\Phi(a :: A')`$。∎

<a id="d-sle"></a>
## 定義: 列辞書式広義順序 (D.sle)

$`M, N \in \mathrm{PairSeq}`$ に対し

```math
M \preceq_{\mathrm{lex}} N :\iff M = N \ \vee\ M \prec_{\mathrm{lex}} N .
```

<a id="t-sle_refl"></a>
## 定理: 列辞書式広義順序の反射性 (T.sle_refl)

### 定理

任意の $`M \in \mathrm{PairSeq}`$ に対し $`M \preceq_{\mathrm{lex}} M`$。

### 証明

$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 1 選言 $`M = M`$ が $`=`$ の反射性により成り立つ。∎

<a id="t-seqlex_sle_trans"></a>
## 定理: 狭義と広義の合成 (T.seqlex_sle_trans)

### 定理

$`A \prec_{\mathrm{lex}} B`$ かつ $`B \preceq_{\mathrm{lex}} C`$ ならば $`A \prec_{\mathrm{lex}} C`$。

### 証明

$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）より $`B \preceq_{\mathrm{lex}} C`$ は $`B = C`$ か
$`B \prec_{\mathrm{lex}} C`$ である。前者のときは $`C`$ を $`B`$ に書き換えれば仮定
$`A \prec_{\mathrm{lex}} B`$ そのものである。後者のときは [T.seqlex_trans](#t-seqlex_trans) を
$`A \prec_{\mathrm{lex}} B`$ と $`B \prec_{\mathrm{lex}} C`$ に適用する。∎

<a id="t-seqlex_append_mono"></a>
## 定理: 大きい側への後置は順序を保つ (T.seqlex_append_mono)

### 定理

$`A \prec_{\mathrm{lex}} B`$ ならば、任意の $`C \in \mathrm{PairSeq}`$ に対し
$`A \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$。

### 証明

$`A`$ の構成子に関する帰納法。帰納法の述語は

```math
\Phi(A) :\equiv \forall B \in \mathrm{PairSeq},\ A \prec_{\mathrm{lex}} B \to
  \forall C \in \mathrm{PairSeq},\ A \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C .
```

- **基底段** $`A = ()`$：$`B = ()`$ とすると、$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式より
  仮定 $`() \prec_{\mathrm{lex}} ()`$ は $`() \ne ()`$ であり偽である。よって $`B = b :: B'`$ と書け、
  $`B \mathbin{+\!\!+} C = b :: (B' \mathbin{+\!\!+} C) \ne ()`$ である。
  ふたたび定義（D.seqlex）の第 1 式より $`() \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$。

- **帰納段** $`A = a :: A'`$：$`\Phi(A')`$ を仮定する。
  $`B = ()`$ とすると定義（D.seqlex）の第 2 式より仮定が $`\bot`$ になるから
  $`B = b :: B'`$ と書ける。定義（D.seqlex）の第 3 式より仮定は次のいずれかである。

  - $`a \prec_{\mathrm{p}} b`$ のとき。
    $`(a :: A') \mathbin{+\!\!+} C = a :: (A' \mathbin{+\!\!+} C)`$、
    $`(b :: B') \mathbin{+\!\!+} C = b :: (B' \mathbin{+\!\!+} C)`$ であるから、
    定義（D.seqlex）の第 3 式の右辺の第 1 選言がそのまま成り立つ。

  - $`a = b \wedge A' \prec_{\mathrm{lex}} B'`$ のとき。帰納法の仮定 $`\Phi(A')`$ を
    $`B'`$ と $`C`$ に適用して $`A' \prec_{\mathrm{lex}} B' \mathbin{+\!\!+} C`$ を得る。
    これと $`a = b`$ により定義（D.seqlex）の第 3 式の右辺の第 2 選言が成り立つ。∎

<a id="t-sle_append_mono"></a>
## 定理: 広義版の後置単調性 (T.sle_append_mono)

### 定理

$`A \preceq_{\mathrm{lex}} B`$ ならば、任意の $`C \in \mathrm{PairSeq}`$ に対し
$`A \preceq_{\mathrm{lex}} B \mathbin{+\!\!+} C`$。

### 証明

$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の選言で場合分けする。

- $`A = B`$ のとき。$`C`$ の構成子で分ける。
  - $`C = ()`$ のとき。$`B \mathbin{+\!\!+} () = B = A`$ であるから、定義（D.sle）の第 1 選言が成り立つ。
  - $`C = c :: C'`$ のとき。$`C \ne ()`$ であるから
    [T.seqlex_prefix](Seqlex-ja.md#t-seqlex_prefix) を $`u := A`$、$`v := C`$ に適用して
    $`A \prec_{\mathrm{lex}} A \mathbin{+\!\!+} C = B \mathbin{+\!\!+} C`$ を得る。
    定義（D.sle）の第 2 選言が成り立つ。

- $`A \prec_{\mathrm{lex}} B`$ のとき。[T.seqlex_append_mono](#t-seqlex_append_mono) より
  $`A \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$ であり、定義（D.sle）の第 2 選言が成り立つ。∎

<a id="t-seqlex_snoc_cases"></a>
## 定理: 末尾に 1 列を付けた列の下側の場合分け (T.seqlex_snoc_cases)

### 定理

$`D, N \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ とする。
$`N \prec_{\mathrm{lex}} D \mathbin{+\!\!+} (\ell)`$ ならば

```math
N \preceq_{\mathrm{lex}} D
\qquad\text{または}\qquad
\exists q, S,\ \bigl(N = D \mathbin{+\!\!+} q :: S \wedge q \prec_{\mathrm{p}} \ell\bigr).
```

### 証明

$`D`$ の構成子に関する帰納法（$`\ell`$, $`N`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(D) :\equiv \forall \ell, N,\ N \prec_{\mathrm{lex}} D \mathbin{+\!\!+} (\ell) \to
  \Bigl(N \preceq_{\mathrm{lex}} D \ \vee\
    \exists q, S,\ \bigl(N = D \mathbin{+\!\!+} q :: S \wedge q \prec_{\mathrm{p}} \ell\bigr)\Bigr).
```

- **基底段** $`D = ()`$：$`D \mathbin{+\!\!+} (\ell) = (\ell)`$ である。$`N`$ の構成子で分ける。
  - $`N = ()`$ のとき。[T.sle_refl](#t-sle_refl) より $`() \preceq_{\mathrm{lex}} ()`$ であり、
    第 1 の選言が成り立つ。
  - $`N = q :: S`$ のとき。$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式より仮定は
    $`q \prec_{\mathrm{p}} \ell`$ か $`(q = \ell \wedge S \prec_{\mathrm{lex}} ())`$ である。
    後者の第 2 連言子は、$`S = ()`$ なら定義（D.seqlex）の第 1 式より $`() \ne ()`$、
    $`S = s :: S'`$ なら定義（D.seqlex）の第 2 式より $`\bot`$ であり、どちらも偽である。
    よって $`q \prec_{\mathrm{p}} \ell`$ であり、$`N = () \mathbin{+\!\!+} q :: S`$ であるから
    第 2 の選言が成り立つ。

- **帰納段** $`D = d :: D'`$：$`\Phi(D')`$ を仮定する。
  $`(d :: D') \mathbin{+\!\!+} (\ell) = d :: (D' \mathbin{+\!\!+} (\ell))`$ である。$`N`$ の構成子で分ける。

  - $`N = ()`$ のとき。$`d :: D' \ne ()`$ であるから定義（D.seqlex）の第 1 式より
    $`() \prec_{\mathrm{lex}} d :: D'`$ であり、定義（D.sle）の第 2 選言により
    $`N \preceq_{\mathrm{lex}} D`$。第 1 の選言が成り立つ。

  - $`N = q :: S`$ のとき。定義（D.seqlex）の第 3 式より仮定は次のいずれかである。

    - $`q \prec_{\mathrm{p}} d`$ のとき。定義（D.seqlex）の第 3 式の第 1 選言により
      $`q :: S \prec_{\mathrm{lex}} d :: D'`$ であるから、定義（D.sle）の第 2 選言により
      $`N \preceq_{\mathrm{lex}} D`$。第 1 の選言が成り立つ。

    - $`q = d \wedge S \prec_{\mathrm{lex}} D' \mathbin{+\!\!+} (\ell)`$ のとき。
      帰納法の仮定 $`\Phi(D')`$ を $`\ell`$ と $`S`$ に適用する。

      - $`S \preceq_{\mathrm{lex}} D'`$ が得られたとき。定義（D.sle）で分ける。
        $`S = D'`$ なら $`N = d :: S = d :: D' = D`$ であり、定義（D.sle）の第 1 選言が成り立つ。
        $`S \prec_{\mathrm{lex}} D'`$ なら、$`q = d`$ と合わせて定義（D.seqlex）の第 3 式の
        第 2 選言により $`N = d :: S \prec_{\mathrm{lex}} d :: D' = D`$ であり、
        定義（D.sle）の第 2 選言が成り立つ。いずれも第 1 の選言である。

      - $`S = D' \mathbin{+\!\!+} q' :: S'`$ かつ $`q' \prec_{\mathrm{p}} \ell`$ が得られたとき。
        $`N = d :: S = (d :: D') \mathbin{+\!\!+} q' :: S' = D \mathbin{+\!\!+} q' :: S'`$ であるから、
        第 2 の選言が成り立つ。∎

<a id="d-SeqlexCofinality"></a>
## 定義: 共終性の列辞書式形 (D.SeqlexCofinality)

命題 $`\mathrm{SeqlexCofinality}`$ を次で定める。

```math
\begin{aligned}
&\mathrm{SeqlexCofinality} :\equiv
  \forall M, N \in \mathrm{PairSeq},\ \cr
&\qquad \bigl(M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS}
  \wedge N \prec_{\mathrm{lex}} M\bigr) \cr
&\qquad \to \exists n,\ \bigl(1 \le n \wedge N \preceq_{\mathrm{lex}} M[n]\bigr).
\end{aligned}
```

（$`\mathrm{ST\_PS}`$ [D.ST_PS](Pss-ja.md#d-ST_PS)、$`M[n]`$ [D.oper](Pss-ja.md#d-oper)）

<a id="t-pss_cofinality_of_seqlex"></a>
## 定理: 列辞書式形からの共終性 (T.pss_cofinality_of_seqlex)

### 定理

$`\mathrm{SeqlexCofinality}`$ が成り立つとする。このとき $`M, N \in \mathrm{ST\_PS}`$ が
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$（[D.translate](Term-ja.md#d-translate)）をみたすならば

```math
\exists n,\ \bigl(1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])\bigr).
```

（$`\prec`$ [D.olt](Term-ja.md#d-olt)、$`\preceq`$ [D.ole](Term-ja.md#d-ole)）

### 証明

まず $`N \ne M`$ である。$`N = M`$ とすると仮定は $`\mathrm{tr}\,M \prec \mathrm{tr}\,M`$ となり、
[T.olt_irrefl](Term-ja.md#t-olt_irrefl) に反する。

$`N \ne M`$ と $`N, M \in \mathrm{ST\_PS}`$ により
[T.olt_ST_iff_seqlex](Seqlex-2-ja.md#t-olt_ST_iff_seqlex) が使えて、仮定から
$`N \prec_{\mathrm{lex}} M`$ を得る。これに $`\mathrm{SeqlexCofinality}`$ を適用して、
$`1 \le n`$ かつ $`N \preceq_{\mathrm{lex}} M[n]`$ なる $`n`$ を取る。この $`n`$ について
$`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$ を示せばよい。
$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）で場合分けする。

- $`N = M[n]`$ のとき。両辺の翻訳が同一の項であるから、$`\preceq`$ の定義（D.ole）の
  第 2 選言が成り立つ。

- $`N \prec_{\mathrm{lex}} M[n]`$ のとき。さらに $`N = M[n]`$ か否かで分ける。
  - $`N = M[n]`$ のとき。上と同じく $`\preceq`$ の定義（D.ole）の第 2 選言が成り立つ。
  - $`N \ne M[n]`$ のとき。$`\mathrm{ST\_PS}`$ の定義（D.ST_PS）の規則 (oper) を
    $`M \in \mathrm{ST\_PS}`$ と $`1 \le n`$ に適用して $`M[n] \in \mathrm{ST\_PS}`$ を得る。
    [T.olt_ST_iff_seqlex](Seqlex-2-ja.md#t-olt_ST_iff_seqlex) を $`N`$ と $`M[n]`$ に適用して
    $`\mathrm{tr}\,N \prec \mathrm{tr}\,(M[n])`$ を得るから、$`\preceq`$ の定義（D.ole）の
    第 1 選言が成り立つ。∎

<a id="t-entry_zero"></a>
## 定理: 行 0 の成分 (T.entry_zero)

### 定理

任意の $`M \in \mathrm{PairSeq}`$, $`j \in \mathbb{N}`$ に対し
$`M_{0,j} = \pi_1\bigl(M\langle j\rangle\bigr)`$（[D.entry](Pss-ja.md#d-entry)）。

### 証明

$`M_{i,j}`$ の定義（D.entry）の場合分けの条件 $`i = 0`$ が $`i := 0`$ で成り立つから、
第 1 の場合が選ばれる。∎

<a id="t-entry_one"></a>
## 定理: 行 1 の成分 (T.entry_one)

### 定理

任意の $`M \in \mathrm{PairSeq}`$, $`j \in \mathbb{N}`$ に対し
$`M_{1,j} = \pi_2\bigl(M\langle j\rangle\bigr)`$。

### 証明

$`M_{i,j}`$ の定義（D.entry）の場合分けの条件 $`i = 0`$ は $`i := 1`$ のとき $`1 = 0`$ であり
偽である。よって第 2 の場合が選ばれる。∎

<a id="t-dropLast_snoc_getD"></a>
## 定理: 末尾の 1 列の切り出し (T.dropLast_snoc_getD)

### 定理

$`M \ne ()`$ ならば

```math
\mathrm{dropLast}\,M \mathbin{+\!\!+} \bigl(M\langle \lvert M\rvert - 1\rangle\bigr) = M .
```

### 証明

$`M \ne ()`$ より $`0 \lt \lvert M\rvert`$ であるから $`\lvert M\rvert - 1 \lt \lvert M\rvert`$ であり、
$`M\langle j\rangle`$ の定義（D.entry）の第 1 の場合により
$`M\langle \lvert M\rvert - 1\rangle = M_{\lvert M\rvert - 1}`$、すなわち $`M`$ の最後の要素である。
$`\mathrm{dropLast}\,M`$ は $`M`$ から最後の要素を除いた列であるから、これに最後の要素を
後置すれば $`M`$ に戻る。∎

<a id="t-seqlex_cof_short"></a>
## 定理: 長さ 1 以下の分岐での共終性 (T.seqlex_cof_short)

### 定理

$`\lvert M\rvert - 1 = 0`$ かつ $`N \prec_{\mathrm{lex}} M`$ ならば

```math
\exists n,\ \bigl(1 \le n \wedge N \preceq_{\mathrm{lex}} M[n]\bigr).
```

### 証明

$`n := 1`$ と取る。$`1 \le 1`$ である。
[T.oper_eq_self_of_short](Decrease-ja.md#t-oper_eq_self_of_short) を仮定
$`\lvert M\rvert - 1 = 0`$ と $`n := 1`$ に適用して $`M[1] = M`$ を得るから、
示すべきことは $`N \preceq_{\mathrm{lex}} M`$ である。
仮定 $`N \prec_{\mathrm{lex}} M`$ により $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の
第 2 選言が成り立つ。∎

<a id="t-seqlex_cof_zero"></a>
## 定理: 末尾が $`(0,0)`$ の分岐での共終性 (T.seqlex_cof_zero)

### 定理

$`1 \lt \lvert M\rvert`$、$`M_{0,\lvert M\rvert - 1} = 0 \wedge M_{1,\lvert M\rvert - 1} = 0`$、
かつ $`N \prec_{\mathrm{lex}} M`$ ならば

```math
\exists n,\ \bigl(1 \le n \wedge N \preceq_{\mathrm{lex}} M[n]\bigr).
```

### 証明

$`j_1 := \lvert M\rvert - 1`$ とおく。$`1 \lt \lvert M\rvert`$ より $`M \ne ()`$ であり、
$`j_1 \ne 0`$ である。

**第 1 段：$`M\langle j_1\rangle = (0,0)`$。**
[T.entry_zero](#t-entry_zero) と [T.entry_one](#t-entry_one) より
$`\pi_1(M\langle j_1\rangle) = M_{0,j_1} = 0`$、$`\pi_2(M\langle j_1\rangle) = M_{1,j_1} = 0`$ である。
対は両成分で決まるから $`M\langle j_1\rangle = (0,0)`$。

**第 2 段：$`M[1] = \mathrm{dropLast}\,M`$。**
[T.oper_eq_pred_of_zero](Decrease-ja.md#t-oper_eq_pred_of_zero) を $`j_1 \ne 0`$ と仮定の
第 2 連言子に適用して $`M[1] = \mathrm{Pred}\,M`$（[D.Pred](Pss-ja.md#d-Pred)）を得る。
$`1 \lt \lvert M\rvert`$ より $`\neg(\lvert M\rvert \le 1)`$ であるから、
$`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合が選ばれ $`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。

**第 3 段：$`N \preceq_{\mathrm{lex}} \mathrm{dropLast}\,M`$。**
[T.dropLast_snoc_getD](#t-dropLast_snoc_getD) より
$`\mathrm{dropLast}\,M \mathbin{+\!\!+} (M\langle j_1\rangle) = M`$ であるから、仮定
$`N \prec_{\mathrm{lex}} M`$ は $`N \prec_{\mathrm{lex}} \mathrm{dropLast}\,M \mathbin{+\!\!+} (M\langle j_1\rangle)`$
に他ならない。[T.seqlex_snoc_cases](#t-seqlex_snoc_cases) を
$`D := \mathrm{dropLast}\,M`$、$`\ell := M\langle j_1\rangle`$ として適用する。

- 第 1 の選言 $`N \preceq_{\mathrm{lex}} \mathrm{dropLast}\,M`$ が得られたときは、これが目標である。
- 第 2 の選言が得られたときは、$`q \prec_{\mathrm{p}} M\langle j_1\rangle = (0,0)`$ なる $`q`$ が
  存在することになる。$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）よりこれは
  $`q_1 \lt 0`$ または $`(q_1 = 0 \wedge q_2 \lt 0)`$ であり、$`\mathbb{N}`$ には $`0`$ より小さい元が
  ないからどちらも偽である。よってこの場合は起こらない。

$`n := 1`$ と取れば、第 2 段と第 3 段により $`N \preceq_{\mathrm{lex}} M[1]`$ である。∎

<a id="t-hasParent_last_ST_PS"></a>
## 定理: 標準形の末尾列は必ず親をもつ (T.hasParent_last_ST_PS)

### 定理

$`M \in \mathrm{ST\_PS}`$、$`0 \lt \lvert M\rvert`$、かつ
$`\neg\bigl(M_{0,\lvert M\rvert - 1} = 0 \wedge M_{1,\lvert M\rvert - 1} = 0\bigr)`$ ならば

```math
\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M, \lvert M\rvert - 1),\ \lvert M\rvert - 1\bigr) .
```

（$`\mathrm{hasParent}`$ [D.hasParent](Pss-ja.md#d-hasParent)、$`\mathrm{idx}_1`$ [D.idx1](Pss-ja.md#d-idx1)）

### 証明

$`j_1 := \lvert M\rvert - 1`$ とおく。[T.hp_last](Column-4-ja.md#t-hp_last) を適用する。
その 4 つの仮定は次のように満たされる。

- $`\mathrm{blockok}(0, M)`$（[D.blockok](Seqlex-ja.md#d-blockok)）：
  [T.blockok_ST_PS](Seqlex-2-ja.md#t-blockok_ST_PS) による。
- $`\mathrm{z0ok}(M)`$（[D.z0ok](Column-3-ja.md#d-z0ok)）：[T.z0ok_ST_PS](Column-4-ja.md#t-z0ok_ST_PS) による。
- $`0 \lt \lvert M\rvert`$：仮定である。
- $`\neg\bigl(M\langle j_1\rangle = (0,0)\bigr)`$：$`M\langle j_1\rangle = (0,0)`$ と仮定すると、
  [T.entry_zero](#t-entry_zero) より $`M_{0,j_1} = \pi_1((0,0)) = 0`$、
  [T.entry_one](#t-entry_one) より $`M_{1,j_1} = \pi_2((0,0)) = 0`$ となり、
  仮定の第 3 のものに矛盾する。∎

<a id="t-sle_append_cancel"></a>
## 定理: 共通の前置列の消去 (T.sle_append_cancel)

### 定理

$`A, u, v \in \mathrm{PairSeq}`$ に対し

```math
A \mathbin{+\!\!+} u \preceq_{\mathrm{lex}} A \mathbin{+\!\!+} v \iff u \preceq_{\mathrm{lex}} v .
```

### 証明

$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）より、左辺は

```math
A \mathbin{+\!\!+} u = A \mathbin{+\!\!+} v \ \vee\ A \mathbin{+\!\!+} u \prec_{\mathrm{lex}} A \mathbin{+\!\!+} v
```

である。第 2 選言は [T.seqlex_append_cancel](Seqlex-ja.md#t-seqlex_append_cancel) により
$`u \prec_{\mathrm{lex}} v`$ と同値である。第 1 選言については、連結の左からの消去、すなわち

```math
A \mathbin{+\!\!+} u = A \mathbin{+\!\!+} v \iff u = v
```

が成り立つ（$`\Leftarrow`$ は両辺に $`A`$ を前置するだけであり、$`\Rightarrow`$ は両列から
先頭 $`\lvert A\rvert`$ 要素を落とせばよい）。したがって左辺は $`u = v \vee u \prec_{\mathrm{lex}} v`$、
すなわち定義（D.sle）により $`u \preceq_{\mathrm{lex}} v`$ と同値である。∎

<a id="t-getD_append_right'"></a>
## 定理: 連結列の後半の添字表示 (T.getD_append_right')

### 定理

$`A, B \in \mathrm{PairSeq}`$、$`i \in \mathbb{N}`$ に対し

```math
(A \mathbin{+\!\!+} B)\langle \lvert A\rvert + i\rangle = B\langle i\rangle .
```

### 証明

$`\lvert A \mathbin{+\!\!+} B\rvert = \lvert A\rvert + \lvert B\rvert`$ である。$`i`$ と $`\lvert B\rvert`$ で
場合分けする。

- $`i \lt \lvert B\rvert`$ のとき。$`\lvert A\rvert + i \lt \lvert A\rvert + \lvert B\rvert = \lvert A \mathbin{+\!\!+} B\rvert`$
  であるから、$`M\langle j\rangle`$ の定義（D.entry）の第 1 の場合により両辺とも実際の要素を読む。
  連結列 $`A \mathbin{+\!\!+} B`$ の第 $`\lvert A\rvert + i`$ 要素は、添字が $`\lvert A\rvert`$ 以上であるから
  $`B`$ の第 $`(\lvert A\rvert + i) - \lvert A\rvert = i`$ 要素である。よって両辺は等しい。

- $`\lvert B\rvert \le i`$ のとき。$`\lvert A \mathbin{+\!\!+} B\rvert = \lvert A\rvert + \lvert B\rvert \le \lvert A\rvert + i`$
  であるから、$`M\langle j\rangle`$ の定義（D.entry）の第 2 の場合により両辺とも $`(0,0)`$ である。∎

<a id="t-getD_last_of_snoc"></a>
## 定理: 末尾に付けた 1 列の読み出し (T.getD_last_of_snoc)

### 定理

$`D \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ に対し

```math
\bigl(D \mathbin{+\!\!+} (\ell)\bigr)\bigl\langle \lvert D \mathbin{+\!\!+} (\ell)\rvert - 1\bigr\rangle = \ell .
```

### 証明

$`\lvert D \mathbin{+\!\!+} (\ell)\rvert = \lvert D\rvert + 1`$ であるから
$`\lvert D \mathbin{+\!\!+} (\ell)\rvert - 1 = \lvert D\rvert`$ である。
[T.getD_append_right'](#t-getD_append_right') を、左側の列を $`D`$、右側の列を $`(\ell)`$、
添字を $`0`$ として適用すると

```math
\bigl(D \mathbin{+\!\!+} (\ell)\bigr)\langle \lvert D\rvert + 0\rangle = (\ell)\langle 0\rangle
```

であり、$`0 \lt 1 = \lvert (\ell)\rvert`$ であるから $`M\langle j\rangle`$ の定義（D.entry）の
第 1 の場合により $`(\ell)\langle 0\rangle = \ell`$ である。∎

<a id="t-nextrel1_snd_succ"></a>
## 定理: 行 1 の親子では行 1 がちょうど 1 増える (T.nextrel1_snd_succ)

### 定理

$`\mathrm{r1ok}(M)`$（[D.r1ok](Column-2-ja.md#d-r1ok)）かつ $`j_0 \to^M_1 j_1`$（[D.nextrel1](Pss-ja.md#d-nextrel1)）ならば

```math
M_{1,j_1} = M_{1,j_0} + 1 .
```

### 証明

$`\to^M_1`$ の定義（D.nextrel1）より、仮定は次の 6 つの連言である。

```math
\begin{aligned}
&(1)\ j_0 \lt \lvert M\rvert, \cr
&(2)\ j_1 \lt \lvert M\rvert, \cr
&(3)\ j_0 \lt j_1, \cr
&(4)\ M_{1,j_0} \lt M_{1,j_1}, \cr
&(5)\ j_0 \le^M_0 j_1, \cr
&(6)\ \forall j\ \bigl(j_0 \lt j \wedge j \le^M_0 j_1 \to M_{1,j_1} \le M_{1,j}\bigr).
\end{aligned}
```

（$`\le^M_0`$ [D.le0](Pss-ja.md#d-le0)）

**第 1 段：行 $`0`$ の鎖の第 1 歩 $`c`$ を取る。**
(5) と $`\le^M_0`$ の定義（D.le0）の第 3 条件より
$`j_0 \mathbin{(\to^M_0)^{*}} j_1`$（[D.nextrel0](Pss-ja.md#d-nextrel0)）である。
反射推移閉包は「$`j_0 = j_1`$」か「ある $`c`$ について
$`j_0 \to^M_0 c`$ かつ $`c \mathbin{(\to^M_0)^{*}} j_1`$」の
いずれかであるが、前者は (3) の $`j_0 \lt j_1`$ に反する。よって後者の $`c`$ が取れる。

$`\to^M_0`$ の定義（D.nextrel0）の第 3 条件より $`j_0 \lt c`$、第 2 条件より $`c \lt \lvert M\rvert`$ である。
これと (2)、および $`c \mathbin{(\to^M_0)^{*}} j_1`$ から、$`\le^M_0`$ の定義（D.le0）の 3 条件が
そろって $`c \le^M_0 j_1`$ を得る。

**第 2 段：$`M_{1,j_1} \le M_{1,c}`$。**
(6) を $`j := c`$ に適用する。前件は第 1 段の $`j_0 \lt c`$ と $`c \le^M_0 j_1`$ である。

**第 3 段：$`\mathrm{r1ok}(M)`$ を $`c`$ に適用する。**
$`\to^M_0`$ の定義（D.nextrel0）の第 4 条件より $`M_{0,j_0} \lt M_{0,c}`$ であり、
[T.entry_zero](#t-entry_zero) によりこれは $`\pi_1(M\langle j_0\rangle) \lt \pi_1(M\langle c\rangle)`$ である。
とくに $`0 \lt \pi_1(M\langle c\rangle)`$ である。$`c \lt \lvert M\rvert`$ と合わせて
$`\mathrm{r1ok}(M)`$ を $`j := c`$ に適用すると、次の 4 つをみたす $`k`$ が得られる。

```math
\begin{aligned}
&\text{(i)}\ k \lt c, \cr
&\text{(ii)}\ \pi_1(M\langle k\rangle) + 1 = \pi_1(M\langle c\rangle), \cr
&\text{(iii)}\ \forall l\ \bigl(k \lt l \wedge l \lt c \to \pi_1(M\langle c\rangle) \le \pi_1(M\langle l\rangle)\bigr), \cr
&\text{(iv)}\ \pi_2(M\langle c\rangle) \le \pi_2(M\langle k\rangle) + 1 .
\end{aligned}
```

**第 4 段：$`k = j_0`$。**
$`k \to^M_0 c`$ を示す。$`\to^M_0`$ の定義（D.nextrel0）の 5 条件を順に確かめる。

- (1) $`k \lt \lvert M\rvert`$：(i) の $`k \lt c`$ と $`c \lt \lvert M\rvert`$ による。
- (2) $`c \lt \lvert M\rvert`$：第 1 段で得た。
- (3) $`k \lt c`$：(i) である。
- (4) $`M_{0,k} \lt M_{0,c}`$：[T.entry_zero](#t-entry_zero) によりこれは
  $`\pi_1(M\langle k\rangle) \lt \pi_1(M\langle c\rangle)`$ であり、(ii) から従う。
- (5) $`\forall l\ (k \lt l \wedge l \lt c \to M_{0,c} \le M_{0,l})`$：
  [T.entry_zero](#t-entry_zero) により (iii) そのものである。

第 1 段で $`j_0 \to^M_0 c`$ も得ているから、
[T.nextrel0_unique](Column-4-ja.md#t-nextrel0_unique) より $`k = j_0`$ である。

**第 5 段：結論。**
(iv) に $`k = j_0`$ を代入し、[T.entry_one](#t-entry_one) で書き直すと

```math
M_{1,c} \le M_{1,j_0} + 1
```

である。第 2 段と合わせて $`M_{1,j_1} \le M_{1,c} \le M_{1,j_0} + 1`$ を得る。
一方 (4) より $`M_{1,j_0} \lt M_{1,j_1}`$、すなわち $`M_{1,j_0} + 1 \le M_{1,j_1}`$ である。
$`\le`$ の反対称性により $`M_{1,j_1} = M_{1,j_0} + 1`$。∎

<a id="t-oper_bad_blocks_all"></a>
## 定理: 第 4 分岐のブロック分解（$`n`$ に一様） (T.oper_bad_blocks_all)

### 定理

$`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$ とおく。
$`1 \lt \lvert M\rvert`$、$`\mathrm{steps}_1(M)`$（[D.steps1](Seqlex-ja.md#d-steps1)）、$`\mathrm{r1ok}(M)`$、
$`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$、$`\mathrm{hasParent}(M, i_1, j_1)`$ を仮定する。
このとき $`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、
$`\ell \in \mathbb{N}\times\mathbb{N}`$ が存在して、$`B := (v_0,w_0) :: R`$ とおくと次の 5 つが成り立つ。

```math
\begin{aligned}
&(1)\ M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell), \cr
&(2)\ \forall n,\ 1 \le n \to M[n] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n), \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ v_0 \lt \ell_1, \cr
&(5)\ \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr) \ \vee\
        \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
              \wedge \lvert G\rvert \to^M_1 j_1\bigr).
\end{aligned}
```

（$`\mathrm{cp}_{d}(B,n)`$ [D.copies](Cnf-2-ja.md#d-copies)）

### 証明

**第 1 段：$`n = 1`$ でブロック分解を取る。**
[T.oper_bad_blocks](Decrease-ja.md#t-oper_bad_blocks) を $`n := 1`$ として適用する。
その 4 つの仮定 $`1 \lt \lvert M\rvert`$、$`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$、
$`\mathrm{hasParent}(M, i_1, j_1)`$、$`1 \le n`$ のうち初めの 3 つは本定理の仮定であり、
最後のものは $`1 \le 1`$ である。こうして $`G, v_0, w_0, R, d_0, \ell`$ を得る。
得られる主張のうち (1), (3), (4) は上の (1), (3), (4) そのものであり、残りは

```math
\begin{aligned}
&(5')\ \bigl(d_0 = 0 \wedge i_1 = 0\bigr) \ \vee\
        \bigl(0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0
              \wedge \lvert G\rvert \to^M_1 j_1\bigr), \cr
&(6)\ \lvert G\rvert \to^M_{i_1} j_1
\end{aligned}
```

である（$`\to^M_i`$ [D.nextR](Pss-ja.md#d-nextR)）。

**第 2 段：位置の同定。**
(1) と連結の結合則より $`M = G \mathbin{+\!\!+} \bigl(B \mathbin{+\!\!+} (\ell)\bigr)`$ である。
したがって

```math
\lvert M\rvert = \lvert G\rvert + \bigl(\lvert R\rvert + 2\bigr)
```

である（$`\lvert B\rvert = \lvert R\rvert + 1`$ による）。次の 2 つを示す。

- $`M\langle \lvert G\rvert\rangle = (v_0,w_0)`$。
  [T.getD_append_right'](#t-getD_append_right') を、左側の列を $`G`$、右側の列を
  $`B \mathbin{+\!\!+} (\ell)`$、添字を $`0`$ として適用すると
  $`M\langle \lvert G\rvert + 0\rangle = \bigl(B \mathbin{+\!\!+} (\ell)\bigr)\langle 0\rangle`$ であり、
  $`B \mathbin{+\!\!+} (\ell)`$ の先頭要素は $`(v_0,w_0)`$ である。

- $`\ell = M\langle j_1\rangle`$。
  (1) を $`M = \bigl(G \mathbin{+\!\!+} B\bigr) \mathbin{+\!\!+} (\ell)`$ と見て
  [T.getD_last_of_snoc](#t-getD_last_of_snoc) を $`D := G \mathbin{+\!\!+} B`$ に適用すると
  $`M\langle \lvert M\rvert - 1\rangle = \ell`$、すなわち $`M\langle j_1\rangle = \ell`$ である。

**第 3 段：$`(5')`$ から (5) を導く。**
$`(5')`$ の選言で場合分けする。

**(a) $`d_0 = 0 \wedge i_1 = 0`$ のとき。**
まず $`\ell_2 = 0`$ を示す。$`\mathrm{idx}_1`$ の定義（D.idx1）は $`0 \lt M_{1,j_1}`$ のとき $`1`$、
$`M_{1,j_1} = 0`$ のとき $`0`$ である。いま $`i_1 = 0`$ であり $`1 \ne 0`$ であるから
第 1 の場合ではない。よって $`M_{1,j_1} = 0`$ であり、
[T.entry_one](#t-entry_one) と第 2 段の $`\ell = M\langle j_1\rangle`$ より
$`\ell_2 = \pi_2(M\langle j_1\rangle) = M_{1,j_1} = 0`$。

次に $`\ell_1 = v_0 + 1`$ を示す。次の 5 つを用意する。

1. $`\lvert G\rvert \to^M_0 j_1`$。(6) に $`i_1 = 0`$ を代入し、
   [T.nextR_zero_iff](Column-4-ja.md#t-nextR_zero_iff) を使う。
2. $`j_1 = \lvert G\rvert + 1 + \lvert R\rvert`$。第 2 段の長さの式と $`j_1 = \lvert M\rvert - 1`$ による。
3. $`M_{0,\lvert G\rvert + 1} \le M_{0,\lvert G\rvert} + 1`$。
   [T.steps1_iff](Seqlex-ja.md#t-steps1_iff) を $`\mathrm{steps}_1(M)`$ と $`j := \lvert G\rvert`$ に
   適用する（前件 $`\lvert G\rvert + 1 \lt \lvert M\rvert`$ は第 2 段の長さの式による）。
   得られる不等式を [T.entry_zero](#t-entry_zero) で書き直したものである。
4. $`M_{0,\lvert G\rvert} = v_0`$。[T.entry_zero](#t-entry_zero) と第 2 段の
   $`M\langle \lvert G\rvert\rangle = (v_0,w_0)`$ による。
5. $`\ell_1 = M_{0,j_1}`$。[T.entry_zero](#t-entry_zero) と第 2 段の $`\ell = M\langle j_1\rangle`$ による。

さらに $`M_{0,j_1} \le M_{0,\lvert G\rvert + 1}`$ を示す。2 より $`\lvert G\rvert + 1 \le j_1`$ であるから、
$`\lvert G\rvert + 1 = j_1`$ か $`\lvert G\rvert + 1 \lt j_1`$ である。前者なら両辺は同一である。
後者なら 1 の $`\to^M_0`$ の定義（D.nextrel0）の第 5 条件を $`j := \lvert G\rvert + 1`$ に適用する
（前件は $`\lvert G\rvert \lt \lvert G\rvert + 1`$ と $`\lvert G\rvert + 1 \lt j_1`$）。

以上を合わせると

```math
\ell_1 = M_{0,j_1} \le M_{0,\lvert G\rvert + 1} \le M_{0,\lvert G\rvert} + 1 = v_0 + 1
```

である。一方 (4) より $`v_0 \lt \ell_1`$、すなわち $`v_0 + 1 \le \ell_1`$ であるから
$`\ell_1 = v_0 + 1`$。よって (5) の第 1 選言が成り立つ。

**(b) $`0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0 \wedge \lvert G\rvert \to^M_1 j_1`$ のとき。**
[T.nextrel1_snd_succ](#t-nextrel1_snd_succ) を $`\mathrm{r1ok}(M)`$ と
$`\lvert G\rvert \to^M_1 j_1`$ に適用して $`M_{1,j_1} = M_{1,\lvert G\rvert} + 1`$ を得る。
[T.entry_one](#t-entry_one) で両辺を書き直し、第 2 段の $`M\langle j_1\rangle = \ell`$ と
$`M\langle \lvert G\rvert\rangle = (v_0,w_0)`$ を代入すると $`\ell_2 = w_0 + 1`$ である。
$`0 \lt d_0`$、$`\ell_1 = v_0 + d_0`$、$`\lvert G\rvert \to^M_1 j_1`$ はそのままであるから、
(5) の第 2 選言が成り立つ。

**第 4 段：(2) — 分解が $`n`$ によらないこと。**
$`n`$ を取り $`1 \le n`$ とする。[T.oper_bad_blocks](Decrease-ja.md#t-oper_bad_blocks) を
この $`n`$ で適用し、$`G', v_0', w_0', R', d_0', \ell'`$ とその主張 $`(1_n)`$–$`(6_n)`$ を得る。
$`B' := (v_0',w_0') :: R'`$ とおく。

**(i) $`\lvert G'\rvert = \lvert G\rvert`$。**
$`(6_n)`$ は $`\lvert G'\rvert \to^M_{i_1} j_1`$、(6) は $`\lvert G\rvert \to^M_{i_1} j_1`$ である。
$`\mathrm{hasParent}(M, i_1, j_1)`$ の定義（D.hasParent）は $`j_0 \to^M_{i_1} j_1`$ をみたす
$`j_0`$ の一意存在であるから、$`\lvert G'\rvert = \lvert G\rvert`$。

**(ii) $`G' = G`$、$`v_0' = v_0`$、$`w_0' = w_0`$、$`R' = R`$、$`\ell' = \ell`$。**
$`(1_n)`$ と (1) より

```math
\bigl(G' \mathbin{+\!\!+} B'\bigr) \mathbin{+\!\!+} (\ell') = M = \bigl(G \mathbin{+\!\!+} B\bigr) \mathbin{+\!\!+} (\ell)
```

である。末尾の 2 つの列 $`(\ell')`$ と $`(\ell)`$ は長さが等しく $`1`$ であるから、
両辺を末尾から $`1`$ 要素ずつ比べて $`(\ell') = (\ell)`$、すなわち $`\ell' = \ell`$ を得、
残りから $`G' \mathbin{+\!\!+} B' = G \mathbin{+\!\!+} B`$ を得る。さらに $`\lvert G'\rvert = \lvert G\rvert`$ で
あるから、両辺を先頭から $`\lvert G\rvert`$ 要素ずつ比べて $`G' = G`$ と $`B' = B`$ を得る。
$`B' = B`$ は $`(v_0',w_0') :: R' = (v_0,w_0) :: R`$ であるから、先頭を比べて
$`v_0' = v_0`$、$`w_0' = w_0`$、尾を比べて $`R' = R`$ である。

**(iii) $`d_0' = d_0`$。**
まず補助的に次を示す。任意の $`e`$ について $`e \to^M_1 j_1`$ ならば $`i_1 \ne 0`$ である。
実際 $`\to^M_1`$ の定義（D.nextrel1）の第 4 条件より $`M_{1,e} \lt M_{1,j_1}`$ であるから
$`0 \lt M_{1,j_1}`$ であり、$`\mathrm{idx}_1`$ の定義（D.idx1）の第 1 の場合が選ばれて
$`i_1 = 1 \ne 0`$ である。

$`(5')`$ と $`(5'_n)`$ の選言について 4 通りを尽くす。

- 両方とも第 1 選言のとき。$`d_0 = 0`$ かつ $`d_0' = 0`$ であるから $`d_0' = d_0`$。
- $`(5')`$ が第 1 選言、$`(5'_n)`$ が第 2 選言のとき。前者から $`i_1 = 0`$、後者から
  $`\lvert G'\rvert \to^M_1 j_1`$ であり、補助の主張を $`e := \lvert G'\rvert`$ に適用すると
  $`i_1 \ne 0`$ となって矛盾する。よってこの場合は起こらない。
- $`(5')`$ が第 2 選言、$`(5'_n)`$ が第 1 選言のとき。後者から $`i_1 = 0`$、
  前者から $`\lvert G\rvert \to^M_1 j_1`$ であり、補助の主張を $`e := \lvert G\rvert`$ に適用すると
  $`i_1 \ne 0`$ となって矛盾する。よってこの場合は起こらない。
- 両方とも第 2 選言のとき。$`\ell_1 = v_0 + d_0`$ と $`\ell'_1 = v_0' + d_0'`$ であり、
  $`\ell' = \ell`$、$`v_0' = v_0`$ であるから $`v_0 + d_0 = v_0 + d_0'`$、すなわち $`d_0' = d_0`$。

以上より $`(2_n)`$ の右辺の $`G', B', d_0'`$ をすべて $`G, B, d_0`$ に書き換えてよい。
$`(2_n)`$ は

```math
M[n] = G \mathbin{+\!\!+} B^{+0\cdot d_0} \mathbin{+\!\!+} B^{+1\cdot d_0}
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}
```

であり（$`L^{+e}`$ [D.shiftr0](Cnf-2-ja.md#d-shiftr0)は $`L`$ の各対の第 1 成分に $`e`$ を足した列である）、
右辺の $`B^{+0\cdot d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}`$ は
$`\mathrm{cp}`$ の定義（D.copies）そのものであるから
$`\mathrm{cp}_{d_0}(B, n)`$ に等しい。よって (2) を得る。∎
