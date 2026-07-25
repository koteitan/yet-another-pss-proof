[← README](README.md)

<a id="t-pairlt_trans"></a>
## 定理: 対の順序の推移律 (T.pairlt_trans)

### 定理

$`p, q, r \in \mathbb{N}\times\mathbb{N}`$ とする。[$`p \prec_{\mathrm{p}} q`$](Seqlex.md#d-pairlt) かつ
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

[$`A, B, C \in \mathrm{PairSeq}`$](Pss.md#d-PairSeq) とする。
[$`A \prec_{\mathrm{lex}} B`$](Seqlex.md#d-seqlex) かつ $`B \prec_{\mathrm{lex}} C`$ ならば
$`A \prec_{\mathrm{lex}} C`$。

### 証明

$`A`$ の構成子（空列か cons か）に関する帰納法を行う（$`B`$, $`C`$ は全称量化したまま動かす）。
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

- **帰納段** $`A = a :: A'`$：帰納法の仮定は $`\Phi(A')`$ である。
  $`B`$, $`C`$ を取り $`a :: A' \prec_{\mathrm{lex}} B`$、$`B \prec_{\mathrm{lex}} C`$ とする。
  $`B = ()`$ とすると定義（D.seqlex）の第 2 式より第 1 の仮定が $`\bot`$ になるから
  $`B = b :: B'`$ と書ける。同様に $`C = ()`$ とすると第 2 の仮定が $`\bot`$ になるから
  $`C = c :: C'`$ と書ける。定義（D.seqlex）の第 3 式より第 1 の仮定は次のいずれかである。

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

- **帰納段** $`A = a :: A'`$：帰納法の仮定は $`\Phi(A')`$ である。
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
    [T.seqlex_prefix](Seqlex.md#t-seqlex_prefix) を $`u := A`$、$`v := C`$ に適用して
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

- **帰納段** $`D = d :: D'`$：帰納法の仮定は $`\Phi(D')`$ である。
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
\mathrm{SeqlexCofinality} :\equiv
\forall M, N \in \mathrm{PairSeq},\
  \bigl(M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS} \wedge N \prec_{\mathrm{lex}} M\bigr)
  \to \exists n,\ \bigl(1 \le n \wedge N \preceq_{\mathrm{lex}} M[n]\bigr).
```

（[$`\mathrm{ST\_PS}`$](Pss.md#d-ST_PS)、[$`M[n]`$](Pss.md#d-oper)）

<a id="t-pss_cofinality_of_seqlex"></a>
## 定理: 列辞書式形からの共終性 (T.pss_cofinality_of_seqlex)

### 定理

$`\mathrm{SeqlexCofinality}`$ が成り立つとする。このとき $`M, N \in \mathrm{ST\_PS}`$ が
[$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$](Term.md#d-translate) をみたすならば

```math
\exists n,\ \bigl(1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])\bigr).
```

（[$`\prec`$](Term.md#d-olt)、[$`\preceq`$](Term.md#d-ole)）

### 証明

まず $`N \ne M`$ である。$`N = M`$ とすると仮定は $`\mathrm{tr}\,M \prec \mathrm{tr}\,M`$ となり、
[T.olt_irrefl](Term.md#t-olt_irrefl) に反する。

$`N \ne M`$ と $`N, M \in \mathrm{ST\_PS}`$ により
[T.olt_ST_iff_seqlex](Seqlex.md#t-olt_ST_iff_seqlex) が使えて、仮定から
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
    [T.olt_ST_iff_seqlex](Seqlex.md#t-olt_ST_iff_seqlex) を $`N`$ と $`M[n]`$ に適用して
    $`\mathrm{tr}\,N \prec \mathrm{tr}\,(M[n])`$ を得るから、$`\preceq`$ の定義（D.ole）の
    第 1 選言が成り立つ。∎

<a id="t-entry_zero"></a>
## 定理: 行 0 の成分 (T.entry_zero)

### 定理

任意の $`M \in \mathrm{PairSeq}`$, $`j \in \mathbb{N}`$ に対し
[$`M_{0,j} = \pi_1\bigl(M\langle j\rangle\bigr)`$](Pss.md#d-entry)。

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
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) を仮定
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
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) を $`j_1 \ne 0`$ と仮定の
第 2 連言子に適用して [$`M[1] = \mathrm{Pred}\,M`$](Pss.md#d-Pred) を得る。
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

（[$`\mathrm{hasParent}`$](Pss.md#d-hasParent)、[$`\mathrm{idx}_1`$](Pss.md#d-idx1)）

### 証明

$`j_1 := \lvert M\rvert - 1`$ とおく。[T.hp_last](Column.md#t-hp_last) を適用する。
その 4 つの仮定は次のように満たされる。

- [$`\mathrm{blockok}(0, M)`$](Seqlex.md#d-blockok)：
  [T.blockok_ST_PS](Seqlex.md#t-blockok_ST_PS) による。
- [$`\mathrm{z0ok}(M)`$](Column.md#d-z0ok)：[T.z0ok_ST_PS](Column.md#t-z0ok_ST_PS) による。
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

である。第 2 選言は [T.seqlex_append_cancel](Seqlex.md#t-seqlex_append_cancel) により
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
[T.getD_append_right'](#t-getD_append_right') を $`A := D`$、$`B := (\ell)`$、$`i := 0`$ に適用すると

```math
\bigl(D \mathbin{+\!\!+} (\ell)\bigr)\langle \lvert D\rvert + 0\rangle = (\ell)\langle 0\rangle
```

であり、$`0 \lt 1 = \lvert (\ell)\rvert`$ であるから $`M\langle j\rangle`$ の定義（D.entry）の
第 1 の場合により $`(\ell)\langle 0\rangle = \ell`$ である。∎

<a id="t-nextrel1_snd_succ"></a>
## 定理: 行 1 の親子では行 1 がちょうど 1 増える (T.nextrel1_snd_succ)

### 定理

[$`\mathrm{r1ok}(M)`$](Column.md#d-r1ok) かつ [$`j_0 \to^M_1 j_1`$](Pss.md#d-nextrel1) ならば

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

（[$`\le^M_0`$](Pss.md#d-le0)）

**第 1 段：行 $`0`$ の鎖の第 1 歩 $`c`$ を取る。**
(5) と $`\le^M_0`$ の定義（D.le0）の第 3 条件より $`j_0 \mathbin{(\to^M_0)^{*}} j_1`$ である。
反射推移閉包は「$`j_0 = j_1`$」か「ある $`c`$ について
[$`j_0 \to^M_0 c`$](Pss.md#d-nextrel0) かつ $`c \mathbin{(\to^M_0)^{*}} j_1`$」の
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
[T.nextrel0_unique](Column.md#t-nextrel0_unique) より $`k = j_0`$ である。

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
$`1 \lt \lvert M\rvert`$、[$`\mathrm{steps}_1(M)`$](Seqlex.md#d-steps1)、$`\mathrm{r1ok}(M)`$、
$`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$、$`\mathrm{hasParent}(M, i_1, j_1)`$ を仮定する。
このとき $`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、
$`\ell \in \mathbb{N}\times\mathbb{N}`$ が存在して、$`K := (v_0,w_0) :: R`$ とおくと次の 5 つが成り立つ。

```math
\begin{aligned}
&(1)\ M = G \mathbin{+\!\!+} K \mathbin{+\!\!+} (\ell), \cr
&(2)\ \forall n,\ 1 \le n \to M[n] = G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(K, n), \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ v_0 \lt \ell_1, \cr
&(5)\ \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr) \ \vee\
        \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
              \wedge \lvert G\rvert \to^M_1 j_1\bigr).
\end{aligned}
```

（[$`\mathrm{copies}_{d}(K,n)`$](Cnf.md#d-copies)）

### 証明

**第 1 段：$`n = 1`$ でブロック分解を取る。**
[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) を $`n := 1`$ として適用する。
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

である（[$`\to^M_i`$](Pss.md#d-nextR)）。

**第 2 段：位置の同定。**
(1) と連結の結合則より $`M = G \mathbin{+\!\!+} \bigl(K \mathbin{+\!\!+} (\ell)\bigr)`$ である。
したがって

```math
\lvert M\rvert = \lvert G\rvert + \bigl(\lvert R\rvert + 2\bigr)
```

である（$`\lvert K\rvert = \lvert R\rvert + 1`$ による）。次の 2 つを示す。

- $`M\langle \lvert G\rvert\rangle = (v_0,w_0)`$。
  [T.getD_append_right'](#t-getD_append_right') を $`A := G`$、$`B := K \mathbin{+\!\!+} (\ell)`$、
  $`i := 0`$ に適用すると
  $`M\langle \lvert G\rvert + 0\rangle = \bigl(K \mathbin{+\!\!+} (\ell)\bigr)\langle 0\rangle`$ であり、
  $`K \mathbin{+\!\!+} (\ell)`$ の先頭要素は $`(v_0,w_0)`$ である。

- $`\ell = M\langle j_1\rangle`$。
  (1) を $`M = \bigl(G \mathbin{+\!\!+} K\bigr) \mathbin{+\!\!+} (\ell)`$ と見て
  [T.getD_last_of_snoc](#t-getD_last_of_snoc) を $`D := G \mathbin{+\!\!+} K`$ に適用すると
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
   [T.nextR_zero_iff](Column.md#t-nextR_zero_iff) を使う。
2. $`j_1 = \lvert G\rvert + 1 + \lvert R\rvert`$。第 2 段の長さの式と $`j_1 = \lvert M\rvert - 1`$ による。
3. $`M_{0,\lvert G\rvert + 1} \le M_{0,\lvert G\rvert} + 1`$。
   [T.steps1_iff](Seqlex.md#t-steps1_iff) を $`\mathrm{steps}_1(M)`$ と $`j := \lvert G\rvert`$ に
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
$`n`$ を取り $`1 \le n`$ とする。[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) を
この $`n`$ で適用し、$`G', v_0', w_0', R', d_0', \ell'`$ とその主張 $`(1_n)`$–$`(6_n)`$ を得る。
$`K' := (v_0',w_0') :: R'`$ とおく。

**(i) $`\lvert G'\rvert = \lvert G\rvert`$。**
$`(6_n)`$ は $`\lvert G'\rvert \to^M_{i_1} j_1`$、(6) は $`\lvert G\rvert \to^M_{i_1} j_1`$ である。
$`\mathrm{hasParent}(M, i_1, j_1)`$ の定義（D.hasParent）は $`j_0 \to^M_{i_1} j_1`$ をみたす
$`j_0`$ の一意存在であるから、$`\lvert G'\rvert = \lvert G\rvert`$。

**(ii) $`G' = G`$、$`v_0' = v_0`$、$`w_0' = w_0`$、$`R' = R`$、$`\ell' = \ell`$。**
$`(1_n)`$ と (1) より

```math
\bigl(G' \mathbin{+\!\!+} K'\bigr) \mathbin{+\!\!+} (\ell') = M = \bigl(G \mathbin{+\!\!+} K\bigr) \mathbin{+\!\!+} (\ell)
```

である。末尾の 2 つの列 $`(\ell')`$ と $`(\ell)`$ は長さが等しく $`1`$ であるから、
両辺を末尾から $`1`$ 要素ずつ比べて $`(\ell') = (\ell)`$、すなわち $`\ell' = \ell`$ を得、
残りから $`G' \mathbin{+\!\!+} K' = G \mathbin{+\!\!+} K`$ を得る。さらに $`\lvert G'\rvert = \lvert G\rvert`$ で
あるから、両辺を先頭から $`\lvert G\rvert`$ 要素ずつ比べて $`G' = G`$ と $`K' = K`$ を得る。
$`K' = K`$ は $`(v_0',w_0') :: R' = (v_0,w_0) :: R`$ であるから、先頭を比べて
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
- $`(5')`$ が第 2 選言、$`(5'_n)`$ が第 1 選言のとき。同様に、後者から $`i_1 = 0`$、
  前者から $`\lvert G\rvert \to^M_1 j_1`$ であり、補助の主張を $`e := \lvert G\rvert`$ に適用して
  矛盾する。よってこの場合は起こらない。
- 両方とも第 2 選言のとき。$`\ell_1 = v_0 + d_0`$ と $`\ell'_1 = v_0' + d_0'`$ であり、
  $`\ell' = \ell`$、$`v_0' = v_0`$ であるから $`v_0 + d_0 = v_0 + d_0'`$、すなわち $`d_0' = d_0`$。

以上より $`(2_n)`$ の右辺の $`G', K', d_0'`$ をすべて $`G, K, d_0`$ に書き換えてよい。
$`(2_n)`$ は

```math
M[n] = G \mathbin{+\!\!+} K^{+0\cdot d_0} \mathbin{+\!\!+} K^{+1\cdot d_0}
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} K^{+(n-1)d_0}
```

であり（[$`L^{+e}`$](Cnf.md#d-shiftr0) は $`L`$ の各対の第 1 成分に $`e`$ を足した列である）、
右辺の $`K^{+0\cdot d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} K^{+(n-1)d_0}`$ は
$`\mathrm{copies}`$ の定義（D.copies）そのものであるから
$`\mathrm{copies}_{d_0}(K, n)`$ に等しい。よって (2) を得る。∎

<a id="t-seqlex_splice"></a>
## 定理: 接合 (T.seqlex_splice)

### 定理

$`A \prec_{\mathrm{lex}} B`$ とし、$`U \in \mathrm{PairSeq}`$ が

```math
U = () \ \vee\ \forall x \in B,\ \mathrm{head}\,U \prec_{\mathrm{p}} x
```

をみたすとする。このとき任意の $`C \in \mathrm{PairSeq}`$ に対し

```math
A \mathbin{+\!\!+} U \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C .
```

ここで $`\mathrm{head}\,U`$ は $`U`$ の先頭要素である。

### 証明

$`A`$ の構成子に関する帰納法（$`B`$, $`U`$, $`C`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(A) :\equiv \forall B,\ A \prec_{\mathrm{lex}} B \to \forall U,\
  \bigl(U = () \vee \forall x \in B,\ \mathrm{head}\,U \prec_{\mathrm{p}} x\bigr) \to
  \forall C,\ A \mathbin{+\!\!+} U \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C .
```

- **基底段** $`A = ()`$：$`B = ()`$ とすると $`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式より
  仮定が $`() \ne ()`$ となり偽である。よって $`B = b_0 :: B'`$ と書ける。$`U`$ の構成子で分ける。

  - $`U = ()`$ のとき。$`A \mathbin{+\!\!+} U = ()`$ であり、
    $`B \mathbin{+\!\!+} C = b_0 :: (B' \mathbin{+\!\!+} C) \ne ()`$ であるから、
    定義（D.seqlex）の第 1 式より $`() \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$。

  - $`U = u :: U'`$ のとき。第 1 選言 $`U = ()`$ は偽であるから第 2 選言が成り立ち、
    $`\mathrm{head}\,U = u`$ であるから $`\forall x \in B,\ u \prec_{\mathrm{p}} x`$ である。
    これを $`x := b_0`$（$`b_0 \in B`$）に適用して $`u \prec_{\mathrm{p}} b_0`$ を得る。
    $`A \mathbin{+\!\!+} U = u :: U'`$、$`B \mathbin{+\!\!+} C = b_0 :: (B' \mathbin{+\!\!+} C)`$ であるから、
    定義（D.seqlex）の第 3 式の右辺の第 1 選言が成り立つ。

- **帰納段** $`A = a :: A'`$：帰納法の仮定は $`\Phi(A')`$ である。
  $`B = ()`$ とすると定義（D.seqlex）の第 2 式より仮定 $`A \prec_{\mathrm{lex}} B`$ が $`\bot`$ に
  なるから、$`B = b_0 :: B'`$ と書ける。定義（D.seqlex）の第 3 式より仮定は次のいずれかである。

  - $`a \prec_{\mathrm{p}} b_0`$ のとき。
    $`A \mathbin{+\!\!+} U = a :: (A' \mathbin{+\!\!+} U)`$、
    $`B \mathbin{+\!\!+} C = b_0 :: (B' \mathbin{+\!\!+} C)`$ であるから、
    定義（D.seqlex）の第 3 式の右辺の第 1 選言がそのまま成り立つ。

  - $`a = b_0 \wedge A' \prec_{\mathrm{lex}} B'`$ のとき。帰納法の仮定 $`\Phi(A')`$ を
    $`B'`$, $`U`$, $`C`$ に適用する。その前件のうち $`U`$ についての条件は次のように満たされる。
    $`U = ()`$ ならそのまま第 1 選言である。そうでなければ仮定の第 2 選言
    $`\forall x \in B,\ \mathrm{head}\,U \prec_{\mathrm{p}} x`$ が成り立ち、
    $`B' \subseteq B`$（$`x \in B'`$ ならば $`x \in b_0 :: B' = B`$）であるから
    $`\forall x \in B',\ \mathrm{head}\,U \prec_{\mathrm{p}} x`$ である。
    こうして $`A' \mathbin{+\!\!+} U \prec_{\mathrm{lex}} B' \mathbin{+\!\!+} C`$ を得るから、
    $`a = b_0`$ と合わせて定義（D.seqlex）の第 3 式の右辺の第 2 選言が成り立つ。∎

<a id="t-split_block"></a>
## 定理: 基底の深さでのブロック分割 (T.split_block)

### 定理

$`v_0 \in \mathbb{N}`$、$`R, Y \in \mathrm{PairSeq}`$ とし、
$`\forall x \in R,\ v_0 \lt x_1`$ かつ

```math
Y = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,Y)_1\bigr)
```

を仮定する。このとき

```math
\mathrm{tw}_{v_0}(R \mathbin{+\!\!+} Y) = R
\qquad\text{かつ}\qquad
\mathrm{dw}_{v_0}(R \mathbin{+\!\!+} Y) = Y .
```

ここで $`\mathrm{tw}_a`$, $`\mathrm{dw}_a`$ は $`\mathrm{tr}`$ の定義（D.translate）の記法、
すなわち述語 $`x \mapsto a \lt x_1`$ についての takeWhile と dropWhile である。

### 証明

仮定より $`R`$ のすべての要素が述語 $`x \mapsto v_0 \lt x_1`$ をみたす。$`Y`$ で場合分けする。

- $`Y = ()`$ のとき。$`R \mathbin{+\!\!+} () = R`$ である。$`R`$ の全要素が述語をみたすから
  $`\mathrm{tw}_{v_0} R = R`$ であり、$`\mathrm{tw}_{v_0} R \mathbin{+\!\!+} \mathrm{dw}_{v_0} R = R`$ より
  $`\mathrm{dw}_{v_0} R = () = Y`$ である。

- $`Y = y :: Y'`$ のとき。仮定の第 1 選言は偽であるから第 2 選言が成り立ち、
  $`\mathrm{head}\,Y = y`$ より $`\neg(v_0 \lt y_1)`$ である。
  [T.takeWhile_append_all](Term.md#t-takeWhile_append_all) を $`xs := R`$、$`ys := Y`$ に
  適用して $`\mathrm{tw}_{v_0}(R \mathbin{+\!\!+} Y) = R \mathbin{+\!\!+} \mathrm{tw}_{v_0} Y`$ を得る。
  $`Y`$ の先頭 $`y`$ が述語を破るから $`\mathrm{tw}_{v_0} Y = ()`$ であり、右辺は $`R`$ である。
  同様に [T.dropWhile_append_all](Term.md#t-dropWhile_append_all) より
  $`\mathrm{dw}_{v_0}(R \mathbin{+\!\!+} Y) = \mathrm{dw}_{v_0} Y`$ であり、$`y`$ が述語を破るから
  $`\mathrm{dw}_{v_0} Y = Y`$ である。∎

<a id="t-copy_dom_zero"></a>
## 定理: 完全コピーによる支配 (T.copy_dom_zero)

### 定理

$`d \in \mathbb{N}`$、$`Y, R \in \mathrm{PairSeq}`$、$`v_0, w_0 \in \mathbb{N}`$ とし、
$`K := (v_0,w_0) :: R`$ とおく。次の 5 つを仮定する。

```math
\begin{aligned}
&\text{(len)}\quad \lvert Y\rvert \le d, \cr
&\text{(blk)}\quad \mathrm{blockok}\bigl(v_0,\ (v_0,w_0) :: (R \mathbin{+\!\!+} Y)\bigr), \cr
&\text{(R)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hd)}\quad Y = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,Y)_1\bigr), \cr
&\text{(cnf)}\quad \mathrm{cnf}\bigl(\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} Y)\bigr)\bigr).
\end{aligned}
```

このとき

```math
\exists m,\ \bigl(1 \le m \wedge Y \preceq_{\mathrm{lex}} \mathrm{copies}_0(K, m)\bigr).
```

（[$`\mathrm{cnf}`$](Cnf.md#d-cnf)。以下 $`\mathsf{Z}`$ と $`\mathsf{P}`$ は
[$`\mathrm{Three}`$](Term.md#d-Three) の構成子である。）

### 証明

自然数 $`d`$ に関する帰納法。帰納法の述語は

```math
\Phi(d) :\equiv \forall Y, v_0, w_0, R,\
  \bigl(\text{(len)} \wedge \text{(blk)} \wedge \text{(R)} \wedge \text{(hd)} \wedge \text{(cnf)}\bigr)
  \to \exists m,\ \bigl(1 \le m \wedge Y \preceq_{\mathrm{lex}} \mathrm{copies}_0(K, m)\bigr).
```

ここで (len), (blk), (R), (hd), (cnf) は定理の 5 つの仮定であり、$`Y, v_0, w_0, R`$ は
$`\Phi(d)`$ の束縛変数である（$`K = (v_0,w_0) :: R`$ もそれに従って動く）。

- **基底段** $`d = 0`$：(len) は $`\lvert Y\rvert \le 0`$、すなわち $`\lvert Y\rvert = 0`$ であるから
  $`Y = ()`$ である。$`m := 1`$ と取る。[T.copies_one](Cnf.md#t-copies_one) より
  $`\mathrm{copies}_0(K, 1) = K = (v_0,w_0) :: R \ne ()`$ であるから、
  $`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式より
  $`() \prec_{\mathrm{lex}} \mathrm{copies}_0(K,1)`$ であり、
  $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言が成り立つ。

**帰納段** $`d + 1`$：帰納法の仮定は $`\Phi(d)`$ である。$`Y`$ の構成子で場合分けする。

**(a) $`Y = ()`$ のとき。** 基底段と同じく $`m := 1`$ と取ればよい。

**(b) $`Y = y :: Y'`$ のとき。** 以下このときを扱う。

**第 1 段：$`y = (v_0, y_2)`$。**
$`y`$ は $`(v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$ の要素であるから、(blk) すなわち
$`\mathrm{blockok}`$ の定義（D.blockok）の第 2 連言子
$`\forall p \in (v_0,w_0) :: (R \mathbin{+\!\!+} Y),\ v_0 \le p_1`$ より $`v_0 \le y_1`$ である。
また (hd) の第 1 選言は $`Y = y :: Y' \ne ()`$ により偽であるから第 2 選言が成り立ち、
$`\mathrm{head}\,Y = y`$ より $`\neg(v_0 \lt y_1)`$、すなわち $`y_1 \le v_0`$ である。
よって $`y_1 = v_0`$ であり、対は両成分で決まるから $`y = (v_0, y_2)`$。

**第 2 段：$`Y'`$ の分割。**

```math
R' := \mathrm{tw}_{v_0} Y', \qquad Y'' := \mathrm{dw}_{v_0} Y'
```

とおく。$`\mathrm{tw}`$, $`\mathrm{dw}`$ の定義（$`\mathrm{tr}`$ の定義 D.translate の記法）より
$`R' \mathbin{+\!\!+} Y'' = Y'`$ である。また

- $`\forall x \in R',\ v_0 \lt x_1`$：$`\mathrm{tw}_{v_0} Y'`$ の要素は述語 $`x \mapsto v_0 \lt x_1`$ を
  みたす。
- $`Y'' = () \vee \neg\bigl(v_0 \lt (\mathrm{head}\,Y'')_1\bigr)`$：$`\mathrm{dw}_{v_0} Y'`$ が空でなければ
  その先頭要素は述語を破る。

**第 3 段：2 つの翻訳の形。**
第 1 段と第 2 段より $`\bigl((v_0,y_2) :: R'\bigr) \mathbin{+\!\!+} Y'' = (v_0,y_2) :: Y' = y :: Y'`$ である。
[T.translate_block_append](Term.md#t-translate_block_append) を
$`v_0 := v_0`$、$`w_0 := y_2`$、$`R := R'`$、$`T := Y''`$ として適用する。
その 2 つの仮定「$`R'`$ の全要素 $`x`$ が $`v_0 \lt x_1`$」と
「$`Y'' = ()`$ または $`\neg\bigl(v_0 \lt (\mathrm{head}\,Y'')_1\bigr)`$」は第 2 段で示した。
こうして

```math
\mathrm{tr}(y :: Y') = \mathsf{P}\bigl(y_2,\ \mathrm{tr}\,R',\ \mathrm{tr}\,Y''\bigr) .
```

同様に $`\bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} (y :: Y') = (v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$ であり、
(R) と (hd) が [T.translate_block_append](Term.md#t-translate_block_append) の仮定であるから

```math
\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} Y)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}(y :: Y')\bigr) .
```

**第 4 段：CNF の分解。**
第 3 段の 2 式を (cnf) に代入すると

```math
\mathrm{cnf}\Bigl(\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\
  \mathsf{P}(y_2,\ \mathrm{tr}\,R',\ \mathrm{tr}\,Y'')\bigr)\Bigr)
```

である。[T.cnf_P_P](Cnf.md#t-cnf_P_P) よりこれは次の 3 つの連言と同値である。

```math
\begin{aligned}
&\text{(c1)}\quad \mathrm{cnf}(\mathrm{tr}\,R), \cr
&\text{(c2)}\quad \neg\bigl(\mathsf{P}(w_0, \mathrm{tr}\,R, \mathsf{Z})
  \prec \mathsf{P}(y_2, \mathrm{tr}\,R', \mathsf{Z})\bigr), \cr
&\text{(c3)}\quad \mathrm{cnf}\bigl(\mathsf{P}(y_2, \mathrm{tr}\,R', \mathrm{tr}\,Y'')\bigr).
\end{aligned}
```

**第 5 段：$`y_2 \le w_0`$。**
$`w_0 \lt y_2`$ と仮定すると、[T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 1 選言により
$`\mathsf{P}(w_0, \mathrm{tr}\,R, \mathsf{Z}) \prec \mathsf{P}(y_2, \mathrm{tr}\,R', \mathsf{Z})`$ となり
(c2) に矛盾する。よって $`y_2 \le w_0`$ である。$`y_2 \lt w_0`$ か $`y_2 = w_0`$ で場合分けする。

**第 6 段：$`y_2 \lt w_0`$ のとき。**
$`m := 1`$ と取る。[T.copies_one](Cnf.md#t-copies_one) より
$`\mathrm{copies}_0(K, 1) = (v_0,w_0) :: R`$ である。第 1 段より $`y = (v_0,y_2)`$ であり、
$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 2 選言（$`v_0 = v_0`$ かつ $`y_2 \lt w_0`$）により
$`y \prec_{\mathrm{p}} (v_0,w_0)`$ である。$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式の
第 1 選言により $`y :: Y' \prec_{\mathrm{lex}} (v_0,w_0) :: R`$ であり、
$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言が成り立つ。

**第 7 段：$`y_2 = w_0`$ のとき（準備）。**
第 1 段より $`y = (v_0,w_0)`$ である。次の 4 つを用意する。

1. $`\neg\bigl(\mathrm{tr}\,R \prec \mathrm{tr}\,R'\bigr)`$。もし $`\mathrm{tr}\,R \prec \mathrm{tr}\,R'`$ なら、
   $`w_0 = y_2`$ と合わせて [T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 2 選言が成り立ち
   (c2) に矛盾する。
2. $`\mathrm{blockok}(v_0,\ y :: Y')`$。[T.split_block](#t-split_block) を (R) と (hd) に適用して
   $`\mathrm{dw}_{v_0}(R \mathbin{+\!\!+} Y) = Y`$ を得る。
   [T.blockok_tail](Seqlex.md#t-blockok_tail) を (blk) に適用すると
   $`\mathrm{blockok}\bigl(v_0,\ \mathrm{dw}_{v_0}(R \mathbin{+\!\!+} Y)\bigr)`$ であり、これは
   $`\mathrm{blockok}(v_0, Y) = \mathrm{blockok}(v_0,\ y :: Y')`$ である。
3. $`\mathrm{blockok}(v_0 + 1,\ R)`$。[T.split_block](#t-split_block) より
   $`\mathrm{tw}_{v_0}(R \mathbin{+\!\!+} Y) = R`$ であり、
   [T.blockok_arg](Seqlex.md#t-blockok_arg) を (blk) に適用すると
   $`\mathrm{blockok}\bigl(v_0+1,\ \mathrm{tw}_{v_0}(R \mathbin{+\!\!+} Y)\bigr) = \mathrm{blockok}(v_0+1,\ R)`$。
4. $`\mathrm{blockok}(v_0 + 1,\ R')`$。2 と $`y = (v_0,w_0)`$ より
   $`\mathrm{blockok}\bigl(v_0,\ (v_0,w_0) :: Y'\bigr)`$ であり、
   [T.blockok_arg](Seqlex.md#t-blockok_arg) を適用すると
   $`\mathrm{blockok}\bigl(v_0+1,\ \mathrm{tw}_{v_0} Y'\bigr) = \mathrm{blockok}(v_0+1,\ R')`$。

$`R' = R`$ か否かでさらに場合分けする。

**第 8 段：$`R' = R`$ のとき。**
第 1 段、第 2 段と $`R' = R`$ より

```math
y :: Y' = (v_0,w_0) :: (R' \mathbin{+\!\!+} Y'') = \bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} Y''
  = K \mathbin{+\!\!+} Y''
```

である。帰納法の仮定 $`\Phi(d)`$ を $`Y := Y''`$、$`v_0, w_0, R`$ はそのままとして適用する。
その 5 つの前件は次のように満たされる。

- (len)：$`\lvert R'\rvert + \lvert Y''\rvert = \lvert Y'\rvert`$ であり、いまの (len) は
  $`\lvert y :: Y'\rvert = \lvert Y'\rvert + 1 \le d + 1`$、すなわち $`\lvert Y'\rvert \le d`$ である。
  よって $`\lvert Y''\rvert \le \lvert Y'\rvert \le d`$。
- (blk)：$`(v_0,w_0) :: (R \mathbin{+\!\!+} Y'') = K \mathbin{+\!\!+} Y'' = y :: Y'`$ であるから、
  第 7 段の 2 そのものである。
- (R)：いまの (R) そのものである。
- (hd)：第 2 段で示した $`Y''`$ についての選言である。
- (cnf)：$`\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} Y'')\bigr) = \mathrm{tr}(y :: Y')`$ であり、
  第 3 段よりこれは $`\mathsf{P}(y_2, \mathrm{tr}\,R', \mathrm{tr}\,Y'')`$ であるから (c3) である。

こうして $`1 \le m`$ かつ $`Y'' \preceq_{\mathrm{lex}} \mathrm{copies}_0(K, m)`$ なる $`m`$ が得られる。
求める添字として $`m + 1`$ を取る。$`1 \le m + 1`$ である。
[T.copies_succ_cons](Cnf.md#t-copies_succ_cons) と
[T.shiftr0_zero](Cnf.md#t-shiftr0_zero) より

```math
\mathrm{copies}_0(K, m+1) = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} \mathrm{copies}_0(K, m)^{+0}\bigr)
  = K \mathbin{+\!\!+} \mathrm{copies}_0(K, m)
```

である。したがって示すべきことは
$`K \mathbin{+\!\!+} Y'' \preceq_{\mathrm{lex}} K \mathbin{+\!\!+} \mathrm{copies}_0(K, m)`$ であり、
[T.sle_append_cancel](#t-sle_append_cancel) によりこれは
$`Y'' \preceq_{\mathrm{lex}} \mathrm{copies}_0(K, m)`$ と同値である。これは得られたものである。

**第 9 段：$`R' \ne R`$ のとき。**
まず $`R' \prec_{\mathrm{lex}} R`$ を示す。[T.seqlex_total](Seqlex.md#t-seqlex_total) より
$`R' = R`$、$`R' \prec_{\mathrm{lex}} R`$、$`R \prec_{\mathrm{lex}} R'`$ のいずれかである。
第 1 のものは仮定に反する。第 3 のものとすると、第 7 段の 3 と 4 を用いて
[T.seqlex_imp_olt](Seqlex.md#t-seqlex_imp_olt) を $`d := v_0 + 1`$、$`M := R`$、$`N := R'`$ に
適用でき、$`\mathrm{tr}\,R \prec \mathrm{tr}\,R'`$ となって第 7 段の 1 に矛盾する。
よって第 2 のもの、すなわち $`R' \prec_{\mathrm{lex}} R`$ である。

$`m := 2`$ と取る。$`1 \le 2`$ である。
[T.copies_succ_cons](Cnf.md#t-copies_succ_cons)、[T.shiftr0_zero](Cnf.md#t-shiftr0_zero)、
[T.copies_one](Cnf.md#t-copies_one) より

```math
\mathrm{copies}_0(K, 2) = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} \mathrm{copies}_0(K,1)^{+0}\bigr)
  = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} K\bigr)
```

である。第 1 段と $`y_2 = w_0`$ より $`y :: Y' = (v_0,w_0) :: Y'`$ であるから、
$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式の第 2 選言により、示すべきことは

```math
Y' \prec_{\mathrm{lex}} R \mathbin{+\!\!+} K
```

である。$`Y' = R' \mathbin{+\!\!+} Y''`$ であるから、
[T.seqlex_splice](#t-seqlex_splice) を $`A := R'`$、$`B := R`$、$`U := Y''`$、$`C := K`$ として
適用すればよい。その 2 つの仮定は次のように満たされる。

- $`R' \prec_{\mathrm{lex}} R`$：いま示した。
- $`Y'' = () \vee \forall x \in R,\ \mathrm{head}\,Y'' \prec_{\mathrm{p}} x`$：
  第 2 段の $`Y''`$ についての選言で分ける。$`Y'' = ()`$ ならそのまま第 1 選言である。
  そうでなければ $`\neg\bigl(v_0 \lt (\mathrm{head}\,Y'')_1\bigr)`$、すなわち
  $`(\mathrm{head}\,Y'')_1 \le v_0`$ である。$`x \in R`$ に対し (R) より $`v_0 \lt x_1`$ であるから
  $`(\mathrm{head}\,Y'')_1 \lt x_1`$ であり、$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の
  第 1 選言により $`\mathrm{head}\,Y'' \prec_{\mathrm{p}} x`$ である。

以上で $`Y' \prec_{\mathrm{lex}} R \mathbin{+\!\!+} K`$ が得られ、
$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言が成り立つ。∎

<a id="t-copies_zero_succ"></a>
## 定理: 完全コピーの後置分解 (T.copies_zero_succ)

### 定理

$`B \in \mathrm{PairSeq}`$、$`m \in \mathbb{N}`$ に対し

```math
\mathrm{copies}_0(B, m+1) = \mathrm{copies}_0(B, m) \mathbin{+\!\!+} B .
```

### 証明

$`\mathrm{copies}`$ の定義（D.copies）より

```math
\mathrm{copies}_d(B, n) = B^{+0 \cdot d} \mathbin{+\!\!+} B^{+1 \cdot d}
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d}
```

である。すなわち添字の列 $`(0, 1, \dots, n-1)`$ の各 $`k`$ に $`B^{+k d}`$ を対応させて
連結したものである。$`n := m+1`$ のとき、この添字の列は $`(0, 1, \dots, m-1)`$ の後ろに
$`m`$ を付けたものであるから、連結は

```math
\mathrm{copies}_d(B, m+1) = \mathrm{copies}_d(B, m) \mathbin{+\!\!+} B^{+m d}
```

と分かれる。$`d := 0`$ とすると $`m \cdot 0 = 0`$ であり、
[T.shiftr0_zero](Cnf.md#t-shiftr0_zero) より $`B^{+0} = B`$ である。∎
