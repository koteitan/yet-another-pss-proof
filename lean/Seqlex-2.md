[← README](README.md) ｜ Seqlex [1](Seqlex.md) **2**

<a id="t-seqlex_imp_olt"></a>
## 定理: 列辞書式順序から項の順序へ (T.seqlex_imp_olt)

### 定理

$`d \in \mathbb{N}`$、$`M, N \in \mathrm{PairSeq}`$（[D.PairSeq](Pss.md#d-PairSeq)）とする。
$`\mathrm{blockok}(d, M)`$（[D.blockok](Seqlex.md#d-blockok)）、$`\mathrm{blockok}(d, N)`$、
$`M \prec_{\mathrm{lex}} N`$（[D.seqlex](Seqlex.md#d-seqlex)）ならば

```math
\mathrm{tr}\,M \prec \mathrm{tr}\,N .
```

（$`\mathrm{tr}`$ [D.translate](Term.md#d-translate)、$`\prec`$ [D.olt](Term.md#d-olt)）

### 証明

$`\lvert M\rvert + \lvert N\rvert`$ に関する強帰納法を行う。深さ $`d`$ は再帰の途中で
$`d`$ から $`d+1`$ へ動くので、帰納法の述語では $`d`$ を全称量化しておく。すなわち

```math
\Phi(M, N) :\equiv \forall d \in \mathbb{N},\
  \bigl(\mathrm{blockok}(d,M) \wedge \mathrm{blockok}(d,N) \wedge M \prec_{\mathrm{lex}} N\bigr)
  \to \mathrm{tr}\,M \prec \mathrm{tr}\,N
```

とおき、帰納法の仮定は
「$`\lvert M'\rvert + \lvert N'\rvert \lt \lvert M\rvert + \lvert N\rvert`$ なるすべての $`M', N'`$ について $`\Phi(M', N')`$」である。

$`M`$ と $`N`$ の構成子で 4 通りに場合分けする。

**(1) $`M = ()`$、$`N = ()`$ のとき。**
$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式により $`() \prec_{\mathrm{lex}} ()`$ は $`() \ne ()`$ と
同一の命題であり、$`=`$ の反射性に矛盾する。よって前件が偽である。

**(2) $`M = ()`$、$`N = q :: N'`$ のとき。**
$`\mathrm{tr}`$ の定義（D.translate）の第 1 式より $`\mathrm{tr}\,() = \mathsf{Z}`$（[D.Three](Term.md#d-Three)）であり、
第 2 式より $`\mathrm{tr}(q :: N') = \mathsf{P}\bigl(q_2, \mathrm{tr}(\mathrm{tw}_{q_1}N'), \mathrm{tr}(\mathrm{dw}_{q_1}N')\bigr)`$
である。[T.olt_Z_P](Term.md#t-olt_Z_P) より $`\mathsf{Z} \prec \mathsf{P}(\cdot,\cdot,\cdot)`$。

**(3) $`M = p :: r`$、$`N = ()`$ のとき。**
[T.not_seqlex_nil](Seqlex.md#t-not_seqlex_nil) より $`(p :: r) \prec_{\mathrm{lex}} ()`$ は偽であり、前件が偽である。

**(4) $`M = p :: r`$、$`N = q :: r'`$ のとき。**
$`\mathrm{blockok}(d, p :: r)`$ の第 1 の連言子を $`p :: r \ne ()`$ に適用すると
$`\bigl(\mathrm{head}(p :: r)\bigr)_1 = d`$、すなわち $`p_1 = d`$ を得る。
$`\mathrm{blockok}(d, q :: r')`$ の第 1 の連言子を $`q :: r' \ne ()`$ に適用すると
$`\bigl(\mathrm{head}(q :: r')\bigr)_1 = d`$、すなわち $`q_1 = d`$ を得る。
そこで $`y := p_2`$、$`y' := q_2`$ とおけば $`p = (d, y)`$、$`q = (d, y')`$ と書ける。
$`\mathrm{tr}`$ の定義（D.translate）の第 2 式より

```math
\mathrm{tr}\bigl((d,y) :: r\bigr)
  = \mathsf{P}\bigl(y,\ \mathrm{tr}(\mathrm{tw}_{d}\,r),\ \mathrm{tr}(\mathrm{dw}_{d}\,r)\bigr),
```
```math
\mathrm{tr}\bigl((d,y') :: r'\bigr)
  = \mathsf{P}\bigl(y',\ \mathrm{tr}(\mathrm{tw}_{d}\,r'),\ \mathrm{tr}(\mathrm{dw}_{d}\,r')\bigr)
```

である。$`y`$ と $`y'`$ が等しいかどうかで場合分けする。

**(4a) $`y = y'`$ のとき。**
[T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons) より、仮定 $`(d,y) :: r \prec_{\mathrm{lex}} (d,y) :: r'`$ は
$`(d,y) \prec_{\mathrm{p}} (d,y)`$（[D.pairlt](Seqlex.md#d-pairlt)）または
$`\bigl((d,y) = (d,y) \wedge r \prec_{\mathrm{lex}} r'\bigr)`$ である。
第 1 の選言は $`\prec_{\mathrm{p}}`$ の定義（D.pairlt）より $`d \lt d`$ または
$`(d = d \wedge y \lt y)`$ であり、$`\lt`$ の非反射性によりいずれも偽である。
よって $`r \prec_{\mathrm{lex}} r'`$ が成り立つ。

[T.seqlex_arg_or_tail](Seqlex.md#t-seqlex_arg_or_tail) を $`d`$ と $`r \prec_{\mathrm{lex}} r'`$ に適用すると、
次のいずれかが成り立つ。

- (i) $`\mathrm{tw}_d\,r = \mathrm{tw}_d\,r'`$ かつ $`\mathrm{dw}_d\,r \prec_{\mathrm{lex}} \mathrm{dw}_d\,r'`$
- (ii) $`\mathrm{tw}_d\,r \ne \mathrm{tw}_d\,r'`$ かつ $`\mathrm{tw}_d\,r \prec_{\mathrm{lex}} \mathrm{tw}_d\,r'`$

**(i) のとき。**[T.blockok_tail](Seqlex.md#t-blockok_tail) を $`\mathrm{blockok}(d, (d,y) :: r)`$ と
$`\mathrm{blockok}(d, (d,y) :: r')`$ に適用すると $`\mathrm{blockok}(d, \mathrm{dw}_d\,r)`$ と
$`\mathrm{blockok}(d, \mathrm{dw}_d\,r')`$ を得る。$`\mathrm{tw}`$ と $`\mathrm{dw}`$ の定義（D.translate）より
$`\mathrm{tw}_d\,r \mathbin{+\!\!+} \mathrm{dw}_d\,r = r`$ であるから
$`\lvert \mathrm{dw}_d\,r\rvert \le \lvert \mathrm{tw}_d\,r\rvert + \lvert \mathrm{dw}_d\,r\rvert = \lvert r\rvert`$ であり、
同じ等式を $`r'`$ について用いて
$`\lvert \mathrm{dw}_d\,r'\rvert \le \lvert \mathrm{tw}_d\,r'\rvert + \lvert \mathrm{dw}_d\,r'\rvert = \lvert r'\rvert`$ である。よって

```math
\lvert \mathrm{dw}_d\,r\rvert + \lvert \mathrm{dw}_d\,r'\rvert
  \le \lvert r\rvert + \lvert r'\rvert
  \lt \lvert (d,y) :: r\rvert + \lvert (d,y) :: r'\rvert
```

である。よって帰納法の仮定を $`(\mathrm{dw}_d\,r, \mathrm{dw}_d\,r')`$ に、深さ $`d`$ で適用でき、

```math
\mathrm{tr}(\mathrm{dw}_d\,r) \prec \mathrm{tr}(\mathrm{dw}_d\,r')
```

を得る。(i) の第 1 の連言子より $`\mathrm{tr}(\mathrm{tw}_d\,r) = \mathrm{tr}(\mathrm{tw}_d\,r')`$ であるから、
[T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 3 選言
$`y = y \wedge \mathrm{tr}(\mathrm{tw}_d r) = \mathrm{tr}(\mathrm{tw}_d r') \wedge \mathrm{tr}(\mathrm{dw}_d r) \prec \mathrm{tr}(\mathrm{dw}_d r')`$
が成り立ち、結論が従う。

**(ii) のとき。**[T.blockok_arg](Seqlex.md#t-blockok_arg) を同じ 2 つの仮定に適用すると
$`\mathrm{blockok}(d+1, \mathrm{tw}_d\,r)`$ と $`\mathrm{blockok}(d+1, \mathrm{tw}_d\,r')`$ を得る。
$`\mathrm{tw}`$ と $`\mathrm{dw}`$ の定義（D.translate）より
$`\mathrm{tw}_d\,r \mathbin{+\!\!+} \mathrm{dw}_d\,r = r`$ であるから
$`\lvert \mathrm{tw}_d\,r\rvert \le \lvert \mathrm{tw}_d\,r\rvert + \lvert \mathrm{dw}_d\,r\rvert = \lvert r\rvert`$ であり、
同じ等式を $`r'`$ について用いて
$`\lvert \mathrm{tw}_d\,r'\rvert \le \lvert \mathrm{tw}_d\,r'\rvert + \lvert \mathrm{dw}_d\,r'\rvert = \lvert r'\rvert`$ である。よって

```math
\lvert \mathrm{tw}_d\,r\rvert + \lvert \mathrm{tw}_d\,r'\rvert
  \le \lvert r\rvert + \lvert r'\rvert
  \lt \lvert (d,y) :: r\rvert + \lvert (d,y) :: r'\rvert
```

である。よって帰納法の仮定を $`(\mathrm{tw}_d\,r, \mathrm{tw}_d\,r')`$ に、深さ $`d+1`$ で適用でき、

```math
\mathrm{tr}(\mathrm{tw}_d\,r) \prec \mathrm{tr}(\mathrm{tw}_d\,r')
```

を得る。[T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 2 選言
$`y = y \wedge \mathrm{tr}(\mathrm{tw}_d r) \prec \mathrm{tr}(\mathrm{tw}_d r')`$ が成り立ち、結論が従う。

**(4b) $`y \ne y'`$ のとき。**
[T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons) より、仮定は
$`(d,y) \prec_{\mathrm{p}} (d,y')`$ または $`\bigl((d,y) = (d,y') \wedge r \prec_{\mathrm{lex}} r'\bigr)`$ である。
第 2 の選言が成り立つとすると、対の構成子の単射性より $`y = y'`$ となり仮定に矛盾する。
よって $`(d,y) \prec_{\mathrm{p}} (d,y')`$ であり、$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）より
$`d \lt d`$ または $`(d = d \wedge y \lt y')`$ である。前者は $`\lt`$ の非反射性に反するから
$`y \lt y'`$ である。[T.olt_P_P](Term.md#t-olt_P_P) の右辺の第 1 選言がこれであるから、
上に書いた 2 つの翻訳の式と合わせて結論が従う。∎

<a id="t-seqlex_total"></a>
## 定理: 列辞書式順序の三分律 (T.seqlex_total)

### 定理

任意の $`M, N \in \mathrm{PairSeq}`$ に対し

```math
M = N \ \vee\ M \prec_{\mathrm{lex}} N \ \vee\ N \prec_{\mathrm{lex}} M .
```

### 証明

$`M`$ のリスト構造に関する帰納法を行う（$`N`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(M) :\equiv \forall N \in \mathrm{PairSeq},\
  \bigl(M = N \vee M \prec_{\mathrm{lex}} N \vee N \prec_{\mathrm{lex}} M\bigr).
```

**基底段 $`M = ()`$。** $`N`$ の構成子で場合分けする。

- $`N = ()`$ のとき。$`M = N`$ が成り立つ（第 1 選言）。
- $`N = q :: N'`$ のとき。[T.seqlex_nil_iff](Seqlex.md#t-seqlex_nil_iff) より
  $`() \prec_{\mathrm{lex}} (q :: N')`$ は $`q :: N' \ne ()`$ と同値であり、列の構成子の像が交わらない
  ことからこれは成り立つ（第 2 選言）。

**帰納段 $`M = p :: M'`$。** 帰納法の仮定は $`\Phi(M')`$、すなわち
$`\forall N,\ (M' = N \vee M' \prec_{\mathrm{lex}} N \vee N \prec_{\mathrm{lex}} M')`$ である。
$`N`$ の構成子で場合分けする。

- $`N = ()`$ のとき。[T.seqlex_nil_iff](Seqlex.md#t-seqlex_nil_iff) より
  $`() \prec_{\mathrm{lex}} (p :: M')`$ は $`p :: M' \ne ()`$ と同値であり、これは成り立つ（第 3 選言）。

- $`N = q :: N'`$ のとき。さらに $`p = q`$ かどうかで分ける。

**$`p = q`$ のとき。** 帰納法の仮定 $`\Phi(M')`$ を $`N'`$ に適用して 3 通りに分ける。

- $`M' = N'`$ のとき。$`p = q`$ と合わせて $`p :: M' = q :: N'`$（第 1 選言）。
- $`M' \prec_{\mathrm{lex}} N'`$ のとき。[T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons) の右辺の第 2 選言
  $`p = q \wedge M' \prec_{\mathrm{lex}} N'`$ が成り立つから $`p :: M' \prec_{\mathrm{lex}} q :: N'`$（第 2 選言）。
- $`N' \prec_{\mathrm{lex}} M'`$ のとき。[T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons) の右辺の第 2 選言
  $`q = p \wedge N' \prec_{\mathrm{lex}} M'`$ が成り立つから
  $`q :: N' \prec_{\mathrm{lex}} p :: M'`$（第 3 選言）。

**$`p \ne q`$ のとき。** まず
$`p \prec_{\mathrm{p}} q \vee q \prec_{\mathrm{p}} p`$ を示す。
$`\mathbb{N}`$ の $`\lt`$ の三分律を $`p_1`$ と $`q_1`$ に適用して 3 通りに分ける。

- $`p_1 \lt q_1`$ のとき。$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 1 選言により
  $`p \prec_{\mathrm{p}} q`$。
- $`p_1 = q_1`$ のとき。さらに $`\mathbb{N}`$ の $`\lt`$ の三分律を $`p_2`$ と $`q_2`$ に適用する。
  - $`p_2 \lt q_2`$ のとき。$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 2 選言
    $`p_1 = q_1 \wedge p_2 \lt q_2`$ により $`p \prec_{\mathrm{p}} q`$。
  - $`p_2 = q_2`$ のとき。$`p_1 = q_1`$ と $`p_2 = q_2`$ から対の外延性により $`p = q`$ となり、
    仮定 $`p \ne q`$ に矛盾する。
  - $`q_2 \lt p_2`$ のとき。$`q_1 = p_1`$ と合わせて $`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の
    第 2 選言により $`q \prec_{\mathrm{p}} p`$。
- $`q_1 \lt p_1`$ のとき。$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 1 選言により
  $`q \prec_{\mathrm{p}} p`$。

いずれの場合も $`p \prec_{\mathrm{p}} q`$ か $`q \prec_{\mathrm{p}} p`$ が得られた。
前者のときは [T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons) の右辺の第 1 選言 $`p \prec_{\mathrm{p}} q`$ により
$`p :: M' \prec_{\mathrm{lex}} q :: N'`$（第 2 選言）であり、後者のときは
[T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons) の右辺の第 1 選言 $`q \prec_{\mathrm{p}} p`$ により
$`q :: N' \prec_{\mathrm{lex}} p :: M'`$（第 3 選言）である。∎

<a id="t-olt_iff_seqlex"></a>
## 定理: ブロック上の順序同型 (T.olt_iff_seqlex)

### 定理

$`d \in \mathbb{N}`$、$`M, N \in \mathrm{PairSeq}`$ とする。
$`\mathrm{blockok}(d, M)`$、$`\mathrm{blockok}(d, N)`$、$`M \ne N`$ ならば

```math
\mathrm{tr}\,M \prec \mathrm{tr}\,N \iff M \prec_{\mathrm{lex}} N .
```

### 証明

両方向を示す。

**（$`\Rightarrow`$）** $`\mathrm{tr}\,M \prec \mathrm{tr}\,N`$ とする。
$`M \prec_{\mathrm{lex}} N`$ が成り立たないと仮定して矛盾を導く。
[T.seqlex_total](#t-seqlex_total) を $`M`$, $`N`$ に適用すると次の 3 通りである。

- $`M = N`$ のとき。仮定 $`M \ne N`$ に矛盾する。
- $`M \prec_{\mathrm{lex}} N`$ のとき。いま仮定した「$`M \prec_{\mathrm{lex}} N`$ が成り立たない」に矛盾する。
- $`N \prec_{\mathrm{lex}} M`$ のとき。[T.seqlex_imp_olt](#t-seqlex_imp_olt) を
  $`d`$, $`N`$, $`M`$, $`\mathrm{blockok}(d,N)`$, $`\mathrm{blockok}(d,M)`$ に適用して
  $`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ を得る。これと $`\mathrm{tr}\,M \prec \mathrm{tr}\,N`$ に
  [T.olt_trans](Term.md#t-olt_trans) を適用すると $`\mathrm{tr}\,M \prec \mathrm{tr}\,M`$ となり、
  [T.olt_irrefl](Term.md#t-olt_irrefl) に矛盾する。

いずれの場合も矛盾するから $`M \prec_{\mathrm{lex}} N`$ である。

**（$`\Leftarrow`$）** [T.seqlex_imp_olt](#t-seqlex_imp_olt) を $`d`$, $`M`$, $`N`$ に適用すればよい。∎

<a id="t-getLastD_eq_getD"></a>
## 定理: 末尾要素の添字表示 (T.getLastD_eq_getD)

### 定理

型 $`\alpha`$ の有限列 $`l`$ と $`d \in \alpha`$ に対し

```math
\mathrm{last}_d\,l = l\langle \lvert l\rvert - 1\rangle_d .
```

ここで

```math
l\langle i\rangle_d := \begin{cases} l_i & (i \lt \lvert l\rvert) \cr d & (i \ge \lvert l\rvert) \end{cases}
```

であり、減法は自然数の切り捨て減法である。$`\alpha = \mathbb{N}\times\mathbb{N}`$ かつ $`d = (0,0)`$ のときの
$`l\langle i\rangle_{(0,0)}`$ が、$`M_{i,j}`$（[D.entry](Pss.md#d-entry)）の定義の $`l\langle i\rangle`$ である。

### 証明

$`l`$ が空かどうかで場合分けする。

- $`l = ()`$ のとき。左辺は $`\mathrm{last}_d`$ の定義の第 1 式より $`d`$ である。
  右辺は $`\lvert l\rvert - 1 = 0 - 1 = 0`$ であり、$`0 \lt \lvert l\rvert = 0`$ は偽だから
  $`\langle\cdot\rangle_d`$ の定義の第 2 式より $`d`$ である。

- $`l \ne ()`$ のとき。$`1 \le \lvert l\rvert`$ であるから $`\lvert l\rvert - 1 \lt \lvert l\rvert`$ であり、
  右辺は $`\langle\cdot\rangle_d`$ の定義の第 1 式より $`l_{\lvert l\rvert - 1}`$ である。
  左辺も $`\mathrm{last}_d`$ の定義の第 2 式より $`l_{\lvert l\rvert - 1}`$ である。∎

<a id="t-getLastD_ne_nil_indep"></a>
## 定理: 空でない列の末尾要素は既定値に依らない (T.getLastD_ne_nil_indep)

### 定理

型 $`\alpha`$ の有限列 $`B`$ が $`B \ne ()`$ をみたすならば、任意の $`d, d' \in \alpha`$ に対し

```math
\mathrm{last}_d\,B = \mathrm{last}_{d'}\,B .
```

### 証明

$`B`$ の構成子で場合分けする。

- $`B = ()`$ のとき。仮定 $`B \ne ()`$ に矛盾する。

- $`B = b :: bs`$ のとき。$`\mathrm{last}_d`$ の定義の第 2 式より、両辺とも
  $`(b :: bs)_{\lvert b :: bs\rvert - 1}`$ に等しい。この値は $`d`$ にも $`d'`$ にも依らない。∎

<a id="t-headI_append_left"></a>
## 定理: 左が空でない連結の先頭 (T.headI_append_left)

### 定理

型 $`\alpha`$ の有限列 $`A, B`$ について、$`A \ne ()`$ ならば

```math
\mathrm{head}(A \mathbin{+\!\!+} B) = \mathrm{head}\,A .
```

### 証明

$`A`$ の構成子で場合分けする。

- $`A = ()`$ のとき。仮定 $`A \ne ()`$ に矛盾する。

- $`A = a :: as`$ のとき。$`(a :: as) \mathbin{+\!\!+} B = a :: (as \mathbin{+\!\!+} B)`$ であるから、
  $`\mathrm{head}`$ の定義より左辺は $`a`$ である。右辺も $`\mathrm{head}(a :: as) = a`$ である。∎

<a id="t-getLastD_append_right"></a>
## 定理: 右が空でない連結の末尾 (T.getLastD_append_right)

### 定理

型 $`\alpha`$ の有限列 $`A, B`$ について、$`B \ne ()`$ ならば、任意の $`d \in \alpha`$ に対し

```math
\mathrm{last}_d(A \mathbin{+\!\!+} B) = \mathrm{last}_d\,B .
```

### 証明

$`A`$ のリスト構造に関する帰納法を行う（$`d`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(A) :\equiv \forall d \in \alpha,\ \mathrm{last}_d(A \mathbin{+\!\!+} B) = \mathrm{last}_d\,B .
```

- **基底段** $`A = ()`$：$`() \mathbin{+\!\!+} B = B`$ であるから両辺は同一である。

**帰納段 $`A = a :: A'`$。** 帰納法の仮定は $`\Phi(A')`$、すなわち
$`\forall d,\ \mathrm{last}_d(A' \mathbin{+\!\!+} B) = \mathrm{last}_d\,B`$ である。
まず、任意の $`b \in \alpha`$ と型 $`\alpha`$ の有限列 $`bs`$ に対し

```math
\mathrm{last}_d(b :: bs) = \mathrm{last}_b\,bs
```

が成り立つことを示す。$`bs = ()`$ のとき、$`b :: bs = (b) \ne ()`$ であるから
$`\mathrm{last}_d`$ の定義の第 2 式より左辺は $`(b)_{\lvert (b)\rvert - 1} = (b)_0 = b`$ であり、
右辺は $`\mathrm{last}_b\,()`$ であって同じ定義の第 1 式より $`b`$ である。
$`bs \ne ()`$ のとき、$`b :: bs \ne ()`$ でもあるから
$`\mathrm{last}_d`$ の定義の第 2 式を両辺に用いて、左辺は
$`(b :: bs)_{\lvert b :: bs\rvert - 1} = (b :: bs)_{\lvert bs\rvert}`$、右辺は
$`bs_{\lvert bs\rvert - 1}`$ である。$`\lvert bs\rvert \ge 1`$ であるから
$`b :: bs`$ の第 $`\lvert bs\rvert`$ 要素は $`bs`$ の第 $`\lvert bs\rvert - 1`$ 要素であり、
両辺は等しい。

$`(a :: A') \mathbin{+\!\!+} B = a :: (A' \mathbin{+\!\!+} B)`$ であるから、この式を
$`b := a`$、$`bs := A' \mathbin{+\!\!+} B`$ に適用して

```math
\mathrm{last}_d\bigl(a :: (A' \mathbin{+\!\!+} B)\bigr) = \mathrm{last}_a(A' \mathbin{+\!\!+} B)
```

である。ここに帰納法の仮定 $`\Phi(A')`$ を $`d := a`$ に適用して
$`\mathrm{last}_a(A' \mathbin{+\!\!+} B) = \mathrm{last}_a\,B`$ を得る。
最後に $`B \ne ()`$ と [T.getLastD_ne_nil_indep](#t-getLastD_ne_nil_indep) より
$`\mathrm{last}_a\,B = \mathrm{last}_d\,B`$ である。よって $`\Phi(a :: A')`$。∎

<a id="t-steps1_flatMap"></a>
## 定理: ブロックの連結の段差 1 (T.steps1_flatMap)

### 定理

$`F : \mathbb{N} \to \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とし、

```math
\mathrm{cat}_n F := F(0) \mathbin{+\!\!+} F(1) \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} F(n-1)
```

とおく（$`n = 0`$ のときは空列）。次の 3 つを仮定する。

```math
\begin{aligned}
&\text{(F1)}\quad \forall k \lt n,\ \mathrm{steps}_1\bigl(F(k)\bigr), \cr
&\text{(Fne)}\quad \forall k \lt n,\ F(k) \ne (), \cr
&\text{(Fj)}\quad \forall k,\ k + 1 \lt n \to
   \bigl(\mathrm{head}\,F(k+1)\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)} F(k)\bigr)_1 + 1 .
\end{aligned}
```

（$`\mathrm{steps}_1`$ [D.steps1](Seqlex.md#d-steps1)）

このとき $`\mathrm{steps}_1(\mathrm{cat}_n F)`$ が成り立ち、さらに $`0 \lt n`$ ならば

```math
\mathrm{cat}_n F \ne (),
\qquad
\mathrm{head}(\mathrm{cat}_n F) = \mathrm{head}\,F(0),
\qquad
\mathrm{last}_{(0,0)}(\mathrm{cat}_n F) = \mathrm{last}_{(0,0)} F(n-1)
```

が成り立つ。

### 証明

$`n`$ に関する自然数の帰納法。$`F`$ は固定する。帰納法の述語は

```math
\begin{aligned}
\Phi(n) :\equiv\ &\Bigl(\forall k \lt n,\ \mathrm{steps}_1(F(k))\Bigr)
  \wedge \Bigl(\forall k \lt n,\ F(k) \ne ()\Bigr) \cr
&\wedge \Bigl(\forall k,\ k+1 \lt n \to
   (\mathrm{head}\,F(k+1))_1 \le (\mathrm{last}_{(0,0)} F(k))_1 + 1\Bigr) \cr
&\to\ \mathrm{steps}_1(\mathrm{cat}_n F) \wedge \Bigl(0 \lt n \to
   \bigl(\mathrm{cat}_n F \ne ()
   \wedge \mathrm{head}(\mathrm{cat}_n F) = \mathrm{head}\,F(0) \cr
&\qquad\qquad\qquad
   \wedge \mathrm{last}_{(0,0)}(\mathrm{cat}_n F) = \mathrm{last}_{(0,0)} F(n-1)\bigr)\Bigr) .
\end{aligned}
```

**基底段 $`n = 0`$。** $`\mathrm{cat}_0 F = ()`$ である。
[T.steps1_nil](Seqlex.md#t-steps1_nil) より $`\mathrm{steps}_1(())`$ が成り立つ。
第 2 の連言子の前件 $`0 \lt 0`$ は偽であるから、その含意は成り立つ。

**帰納段 $`n = m + 1`$。** 帰納法の仮定は $`\Phi(m)`$ である。
$`\mathrm{cat}`$ の定義と連結の結合性より

```math
\mathrm{cat}_{m+1} F = \mathrm{cat}_m F \mathbin{+\!\!+} F(m)
```

である。$`m`$ が $`0`$ かどうかで場合分けする。

**(a) $`m = 0`$ のとき。** $`\mathrm{cat}_1 F = F(0)`$ である。
(F1) を $`k := 0 \lt 1`$ に適用して $`\mathrm{steps}_1(F(0))`$ を得る。
また $`0 \lt 1`$ のとき、(Fne) を $`k := 0`$ に適用して $`F(0) \ne ()`$、
$`\mathrm{head}(\mathrm{cat}_1 F) = \mathrm{head}\,F(0)`$ は両辺が同一、
$`\mathrm{last}_{(0,0)}(\mathrm{cat}_1 F) = \mathrm{last}_{(0,0)} F(0) = \mathrm{last}_{(0,0)} F(1-1)`$
も両辺が同一である。

**(b) $`m \ne 0`$ のとき。** $`k \lt m`$ ならば $`k \lt m + 1`$、
$`k + 1 \lt m`$ ならば $`k + 1 \lt m + 1`$ であるから、(F1), (Fne), (Fj) は $`n := m`$ でも
成り立つ。よって帰納法の仮定 $`\Phi(m)`$ が使えて、

```math
\mathrm{steps}_1(\mathrm{cat}_m F)
```

を得る。さらに $`m \ne 0`$ より $`0 \lt m`$ であるから

```math
\mathrm{cat}_m F \ne (),
\qquad
\mathrm{head}(\mathrm{cat}_m F) = \mathrm{head}\,F(0),
\qquad
\mathrm{last}_{(0,0)}(\mathrm{cat}_m F) = \mathrm{last}_{(0,0)} F(m-1)
```

も得られる。

つぎに接合部の評価

```math
\bigl(\mathrm{head}\,F(m)\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)}(\mathrm{cat}_m F)\bigr)_1 + 1
```

を示す。上の第 3 式により右辺は $`\bigl(\mathrm{last}_{(0,0)} F(m-1)\bigr)_1 + 1`$ に等しい。
$`m \ne 0`$ より $`(m-1) + 1 = m \lt m + 1`$ であるから、(Fj) を $`k := m - 1`$ に適用して

```math
\bigl(\mathrm{head}\,F(m)\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)} F(m-1)\bigr)_1 + 1
```

を得る。また (Fne) を $`k := m \lt m + 1`$ に適用して $`F(m) \ne ()`$ である。

以上のもとで 4 つの結論を示す。

**段差 1。**上の分解と [T.steps1_append](Seqlex.md#t-steps1_append) により、
$`\mathrm{steps}_1(\mathrm{cat}_m F \mathbin{+\!\!+} F(m))`$ を示すには
$`\mathrm{steps}_1(\mathrm{cat}_m F)`$、$`\mathrm{steps}_1(F(m))`$、および
「$`\mathrm{cat}_m F = ()`$ または $`F(m) = ()`$ または
$`(\mathrm{head}\,F(m))_1 \le (\mathrm{last}_{(0,0)}(\mathrm{cat}_m F))_1 + 1`$」
の 3 つを言えばよい。第 1 は上で得た。第 2 は (F1) を $`k := m \lt m+1`$ に適用して得る。
第 3 は上で示した接合部の評価が第 3 選言である。

**空でないこと。**$`\mathrm{cat}_m F \mathbin{+\!\!+} F(m) = ()`$ とすると、連結が空になるのは
両方が空のときに限るから $`\mathrm{cat}_m F = ()`$ となり、上で得た $`\mathrm{cat}_m F \ne ()`$ に
矛盾する。

**先頭。**[T.headI_append_left](#t-headI_append_left) を $`A := \mathrm{cat}_m F \ne ()`$ に適用して

```math
\mathrm{head}(\mathrm{cat}_{m+1} F) = \mathrm{head}(\mathrm{cat}_m F) = \mathrm{head}\,F(0)
```

を得る（第 2 の等号は帰納法の仮定から得た式である）。

**末尾。**[T.getLastD_append_right](#t-getLastD_append_right) を $`B := F(m) \ne ()`$ に適用して

```math
\mathrm{last}_{(0,0)}(\mathrm{cat}_{m+1} F) = \mathrm{last}_{(0,0)} F(m)
```

を得る。$`(m+1) - 1 = m`$ であるからこれが求める式である。∎

<a id="t-steps1_diag_range"></a>
## 定理: 対角区間の段差 1 (T.steps1_diag_range)

### 定理

任意の $`m, s \in \mathbb{N}`$ に対し

```math
\mathrm{steps}_1\bigl(\,\bigl((s,s),\ (s+1,s+1),\ \dots,\ (s+m-1,s+m-1)\bigr)\,\bigr).
```

すなわち $`s`$ から始まる長さ $`m`$ の連続整数の列の各要素 $`j`$ を $`(j,j)`$ に写した列は
段差 1 の条件をみたす。

### 証明

$`m`$ に関する自然数の帰納法（$`s`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(m) :\equiv \forall s \in \mathbb{N},\
  \mathrm{steps}_1\bigl(\,\bigl((s+i,\,s+i)\bigr)_{i=0}^{m-1}\,\bigr).
```

- **基底段** $`m = 0`$：列は空列であり、[T.steps1_nil](Seqlex.md#t-steps1_nil) による。

**帰納段 $`m + 1`$。** 帰納法の仮定は $`\Phi(m)`$、すなわち
$`\forall s,\ \mathrm{steps}_1\bigl((\,(s+i,s+i)\,)_{i=0}^{m-1}\bigr)`$ である。
$`s`$ を取る。長さ $`m+1`$ の列は先頭を分離して

```math
\bigl((s+i,\,s+i)\bigr)_{i=0}^{m} = (s,s) :: \bigl((s+1+i,\,s+1+i)\bigr)_{i=0}^{m-1}
```

と書ける。$`m`$ が $`0`$ かどうかでさらに分ける。

**$`m = 0`$ のとき。** 右辺は $`\bigl((s,s)\bigr)`$、すなわち長さ 1 の列であり、
[T.steps1_single](Seqlex.md#t-steps1_single) による。

**$`m = m' + 1`$ のとき。** もう一度先頭を分離して

```math
\bigl((s+1+i,\,s+1+i)\bigr)_{i=0}^{m-1}
  = (s+1,s+1) :: \bigl((s+2+i,\,s+2+i)\bigr)_{i=0}^{m'-1}
```

である。よって示すべき列は $`(s,s) :: (s+1,s+1) :: \cdots`$ の形であり、
[T.steps1_cons_cons](Seqlex.md#t-steps1_cons_cons) により次の 2 つを示せばよい。

第 1 は $`(s+1,s+1)_1 \le (s,s)_1 + 1`$、すなわち $`s + 1 \le s + 1`$ であり、
$`\le`$ の反射性による。

第 2 は $`\mathrm{steps}_1\bigl((s+1,s+1) :: ((s+2+i,s+2+i))_{i=0}^{m'-1}\bigr)`$ であり、
これは帰納法の仮定 $`\Phi(m)`$ を $`s := s + 1`$ に適用して得られる
$`\mathrm{steps}_1\bigl(((s+1+i,s+1+i))_{i=0}^{m-1}\bigr)`$ を、上の先頭分離の式で
書き換えたものにほかならない。∎

<a id="t-blockok_diagSeq"></a>
## 定理: 対角列はブロック (T.blockok_diagSeq)

### 定理

任意の $`v \in \mathbb{N}`$ に対し $`\mathrm{blockok}(0, \Delta_0^v)`$（[D.diagSeq](Pss.md#d-diagSeq)）。

### 証明

$`\mathrm{blockok}`$ の定義（D.blockok）の 3 つの連言子を順に示す。

**第 1（先頭は深さ $`0`$）。** $`\Delta_0^v \ne ()`$ とする。
$`0 \le v`$ であるから [T.diagSeq_cons](Cnf.md#t-diagSeq_cons) より
$`\Delta_0^v = (0,0) :: \Delta_1^v`$ である。よって
$`\mathrm{head}\,\Delta_0^v = (0,0)`$ であり、その第 1 成分は $`0`$ である。

**第 2（行 $`0`$ の値は $`0`$ 以上）。** 任意の $`p \in \Delta_0^v`$ に対し
$`0 \le p_1`$ は、$`0`$ が自然数の最小元であることによる。

**第 3（段差 1）。** $`\Delta_0^v`$ の定義（D.diagSeq）より、$`\Delta_0^v`$ は
$`0`$ から始まる長さ $`v + 1 - 0`$ の連続整数の列の各要素 $`j`$ を $`(j,j)`$ に写した列である。
[T.steps1_diag_range](#t-steps1_diag_range) を $`m := v + 1`$, $`s := 0`$ に適用すればよい。∎

<a id="t-blockok_oper"></a>
## 定理: 展開はブロックを保つ (T.blockok_oper)

### 定理

$`M \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とする。
$`\mathrm{blockok}(0, M)`$ かつ $`1 \le n`$ ならば $`\mathrm{blockok}(0, M[n])`$（[D.oper](Pss.md#d-oper)）。

### 証明

以下 $`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$（[D.idx1](Pss.md#d-idx1)）と書く。
$`j_1 = 0`$ かどうかで場合分けする。

**(A) $`j_1 = 0`$ のとき。**
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より $`M[n] = M`$ であり、
結論は仮定 $`\mathrm{blockok}(0, M)`$ そのものである。

**(B) $`j_1 \ne 0`$ のとき。**
$`j_1 = \lvert M\rvert - 1 \ne 0`$ より $`1 \lt \lvert M\rvert`$ であり、とくに $`M \ne ()`$ である。
また $`\mathrm{Pred}\,M`$（[D.Pred](Pss.md#d-Pred)）の定義（D.Pred）の場合分けで $`\lvert M\rvert \le 1`$ が偽であるから

```math
\mathrm{Pred}\,M = \mathrm{dropLast}\,M
```

である。$`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ が成り立つかどうかで分ける。

**(B-1) $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。**
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) より
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。
[T.blockok_dropLast](Seqlex.md#t-blockok_dropLast) を $`\mathrm{blockok}(0,M)`$ に適用すればよい。

**(B-2) $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ かつ
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$（[D.hasParent](Pss.md#d-hasParent)）のとき。**
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) より
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ である。
[T.blockok_dropLast](Seqlex.md#t-blockok_dropLast) を適用すればよい。

**(B-3) $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ かつ $`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
[T.parent_nextR](Decrease.md#t-parent_nextR) より、$`j_0 := \mathrm{par}^M_{i_1}(j_1)`$（[D.parent](Pss.md#d-parent)）とおくと
$`j_0 \to^M_{i_1} j_1`$（[D.nextR](Pss.md#d-nextR)）である。[T.nextR_index_lt](Decrease.md#t-nextR_index_lt) より
$`j_0 \lt j_1`$ である。さらに

```math
d_0 := \begin{cases} M_{0,j_1} - M_{0,j_0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
```

とおく。

**行 $`0`$ の段差（式 E1）。** $`\mathrm{blockok}(0,M)`$ の第 3 の連言子は
$`\mathrm{steps}_1(M)`$ である。[T.steps1_iff](Seqlex.md#t-steps1_iff) により

```math
\forall j,\ j + 1 \lt \lvert M\rvert \ \to\ M_{0,j+1} \le M_{0,j} + 1 .
```

（$`M\langle j\rangle`$ の第 1 成分が $`M_{0,j}`$ であることは $`M_{i,j}`$ の定義（D.entry）による。）

**接合部の評価（式 E2）。**

```math
M_{0,j_0} + d_0 \le M_{0,j_1 - 1} + 1 .
```

これを示す。まず $`j_1 \ne 0`$ より $`(j_1 - 1) + 1 = j_1 \lt \lvert M\rvert`$ であるから、
式 E1 を $`j := j_1 - 1`$ に適用して

```math
M_{0,j_1} \le M_{0,j_1 - 1} + 1
```

を得る。$`i_1`$ が $`0`$ かどうかで分ける。

**$`0 \lt i_1`$ のとき。** $`\to^M_{i}`$ の定義（D.nextR）の第 2 式より
$`j_0 \to^M_{i_1} j_1`$ は $`j_0 \to^M_1 j_1`$（[D.nextrel1](Pss.md#d-nextrel1)）である。
$`\to^M_1`$ の定義（D.nextrel1）の第 5 条件は $`j_0 \le^M_0 j_1`$（[D.le0](Pss.md#d-le0)）であり、
[T.le0_entry0_mono](Term.md#t-le0_entry0_mono) より $`M_{0,j_0} \le M_{0,j_1}`$ である。
$`d_0`$ の定義の第 1 式より $`d_0 = M_{0,j_1} - M_{0,j_0}`$ であり、切り捨て減法は
$`M_{0,j_0} \le M_{0,j_1}`$ のとき

```math
M_{0,j_0} + d_0 = M_{0,j_0} + (M_{0,j_1} - M_{0,j_0}) = M_{0,j_1}
```

をみたす。これと上の式を合わせて $`M_{0,j_0} + d_0 \le M_{0,j_1-1} + 1`$ を得る。

**$`i_1 = 0`$ のとき。** $`\to^M_{i}`$ の定義（D.nextR）の第 1 式より
$`j_0 \to^M_0 j_1`$（[D.nextrel0](Pss.md#d-nextrel0)）である。[T.nextrel0_entry0_less](Term.md#t-nextrel0_entry0_less) より
$`M_{0,j_0} \lt M_{0,j_1}`$ である。$`d_0`$ の定義の第 2 式より $`d_0 = 0`$ であるから

```math
M_{0,j_0} + d_0 = M_{0,j_0} \lt M_{0,j_1} \le M_{0,j_1-1} + 1
```

であり、とくに $`M_{0,j_0} + d_0 \le M_{0,j_1-1} + 1`$ を得る。

**展開の形。**[T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) より

```math
M[n] = \mathrm{take}_{j_0} M \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
```

である。ここで $`\mathrm{take}_{j_0} M := (M_0, \dots, M_{j_0-1})`$ である。
$`F(k) := B_k`$ とおけば右辺は $`\mathrm{take}_{j_0} M \mathbin{+\!\!+} \mathrm{cat}_n F`$ である。

**各ブロックの性質。** $`j_0 \lt j_1`$ より $`1 \le j_1 - j_0`$ であるから、
$`B_k`$ の添字の走る列は

```math
(j_0,\ j_0+1,\ \dots,\ j_1-1) = j_0 :: (j_0+1,\ \dots,\ j_1-1)
```

と先頭を分離できる。これより次の 5 つが従う。

**(F-ne)** $`B_k \ne ()`$。上の分離により $`B_k`$ は少なくとも 1 要素をもつ。

**(F-hd)** $`\mathrm{head}\,B_k = (M_{0,j_0} + k\,d_0,\ M_{1,j_0})`$。上の分離の先頭 $`j_0`$ の像である。

**(F-len)** $`\lvert B_k\rvert = j_1 - j_0`$。添字の列の長さがそれだけだからである。

**(F-get)** $`j \lt j_1 - j_0`$ ならば
$`B_k\langle j\rangle = (M_{0,j_0+j} + k\,d_0,\ M_{1,j_0+j})`$。
添字の列の第 $`j`$ 要素は $`j_0 + j`$ であり、その像がこれである。

**(F-last)** $`\mathrm{last}_{(0,0)} B_k = (M_{0,j_1-1} + k\,d_0,\ M_{1,j_1-1})`$。
[T.getLastD_eq_getD](#t-getLastD_eq_getD) と (F-len) より
$`\mathrm{last}_{(0,0)} B_k = B_k\langle j_1 - j_0 - 1\rangle`$ であり、
(F-get) を $`j := j_1 - j_0 - 1`$（これは $`j_1 - j_0`$ 未満）に適用すると、
$`j_0 + (j_1 - j_0 - 1) = j_1 - 1`$ よりこの値になる。

**(F-steps) 各ブロックの段差 1。** $`\mathrm{steps}_1(B_k)`$ を示す。
[T.steps1_iff](Seqlex.md#t-steps1_iff) により、$`j + 1 \lt \lvert B_k\rvert = j_1 - j_0`$ なる $`j`$ について
$`\bigl(B_k\langle j+1\rangle\bigr)_1 \le \bigl(B_k\langle j\rangle\bigr)_1 + 1`$ を示せばよい。
(F-get) を $`j`$ と $`j+1`$ に適用すると、示すべき式は

```math
M_{0,j_0+j+1} + k\,d_0 \le M_{0,j_0+j} + k\,d_0 + 1
```

である。$`j + 1 \lt j_1 - j_0`$ より $`j_0 + j + 1 \lt j_1 \lt \lvert M\rvert`$ であるから、
式 E1 を $`j := j_0 + j`$ に適用して $`M_{0,j_0+j+1} \le M_{0,j_0+j} + 1`$ を得る。
両辺に $`k\,d_0`$ を加えれば上の式になる。

**(F-junc) ブロック間の接合。** $`k + 1 \lt n`$ なる $`k`$ について

```math
\bigl(\mathrm{head}\,B_{k+1}\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)} B_k\bigr)_1 + 1
```

を示す。(F-hd) と (F-last) により、示すべき式は

```math
M_{0,j_0} + (k+1)\,d_0 \le M_{0,j_1-1} + k\,d_0 + 1
```

である。$`(k+1)\,d_0 = k\,d_0 + d_0`$ であるから、これは
$`M_{0,j_0} + d_0 \le M_{0,j_1-1} + 1`$ の両辺に $`k\,d_0`$ を加えたものであり、式 E2 による。

**連結したブロック列。**[T.steps1_flatMap](#t-steps1_flatMap) を
$`F(k) = B_k`$、この $`n`$ に適用する。仮定 (F1) は (F-steps)、(Fne) は (F-ne)、
(Fj) は (F-junc) である。結論として $`\mathrm{steps}_1(\mathrm{cat}_n F)`$ を得る。
また $`1 \le n`$ より $`0 \lt n`$ であるから

```math
\mathrm{cat}_n F \ne (),
\qquad
\mathrm{head}(\mathrm{cat}_n F) = \mathrm{head}\,B_0
```

も得られる。(F-hd) を $`k := 0`$ に適用すると $`\mathrm{head}\,B_0 = (M_{0,j_0} + 0\cdot d_0, M_{1,j_0})`$
であり、$`0 \cdot d_0 = 0`$ であるから

```math
\mathrm{head}(\mathrm{cat}_n F) = (M_{0,j_0},\ M_{1,j_0}) .
```

**前置部分の段差 1。** $`\mathrm{steps}_1(\mathrm{take}_{j_0} M)`$ を示す。
[T.steps1_iff](Seqlex.md#t-steps1_iff) により、$`j + 1 \lt \lvert \mathrm{take}_{j_0} M\rvert`$ なる $`j`$ について
$`\bigl((\mathrm{take}_{j_0} M)\langle j+1\rangle\bigr)_1 \le \bigl((\mathrm{take}_{j_0} M)\langle j\rangle\bigr)_1 + 1`$
を示せばよい。$`\lvert \mathrm{take}_{j_0} M\rvert = \min(j_0, \lvert M\rvert)`$ であり、
これは $`\lvert M\rvert`$ 以下であるから $`j + 1 \lt \lvert M\rvert`$ である。
また $`j`$ も $`j+1`$ も $`\lvert \mathrm{take}_{j_0} M\rvert`$ 未満であるから、
前置部分の第 $`j`$ 要素と第 $`j+1`$ 要素はそれぞれ $`M`$ の第 $`j`$ 要素と第 $`j+1`$ 要素に等しく、

```math
(\mathrm{take}_{j_0} M)\langle j\rangle = M\langle j\rangle,
\qquad
(\mathrm{take}_{j_0} M)\langle j+1\rangle = M\langle j+1\rangle
```

である。したがって示すべき式は $`M_{0,j+1} \le M_{0,j} + 1`$ であり、式 E1 による。

**前置部分と連結ブロックの接合。** 次の 3 選言のいずれかが成り立つことを示す。

```math
\mathrm{take}_{j_0} M = ()
\ \vee\ \mathrm{cat}_n F = ()
\ \vee\ \bigl(\mathrm{head}(\mathrm{cat}_n F)\bigr)_1
        \le \bigl(\mathrm{last}_{(0,0)}(\mathrm{take}_{j_0} M)\bigr)_1 + 1 .
```

$`j_0`$ が $`0`$ かどうかで分ける。

**$`j_0 = 0`$ のとき。** $`\mathrm{take}_0 M = ()`$ であり、第 1 選言が成り立つ。

**$`j_0 \ne 0`$ のとき。** $`j_0 \lt j_1 \lt \lvert M\rvert`$ より $`j_0 \le \lvert M\rvert`$ であるから
$`\lvert \mathrm{take}_{j_0} M\rvert = \min(j_0, \lvert M\rvert) = j_0`$ である。
[T.getLastD_eq_getD](#t-getLastD_eq_getD) より
$`\mathrm{last}_{(0,0)}(\mathrm{take}_{j_0} M) = (\mathrm{take}_{j_0} M)\langle j_0 - 1\rangle`$ であり、
$`j_0 - 1 \lt j_0 \le \lvert M\rvert`$ であるからこれは $`M\langle j_0 - 1\rangle`$ に等しい。
また $`j_0 \ne 0`$ より $`(j_0 - 1) + 1 = j_0 \lt \lvert M\rvert`$ であるから、式 E1 を
$`j := j_0 - 1`$ に適用して

```math
M_{0,j_0} \le M_{0,j_0-1} + 1
```

を得る。上で求めた $`\mathrm{head}(\mathrm{cat}_n F) = (M_{0,j_0}, M_{1,j_0})`$ と合わせると
これが第 3 選言である。

**結論。** $`\mathrm{blockok}`$ の定義（D.blockok）の 3 つの連言子を
$`M[n] = \mathrm{take}_{j_0} M \mathbin{+\!\!+} \mathrm{cat}_n F`$ について順に示す。

**第 1（先頭は深さ $`0`$）。** $`M[n] \ne ()`$ とする。$`j_0`$ が $`0`$ かどうかで分ける。

- $`j_0 = 0`$ のとき。$`\mathrm{take}_0 M = ()`$ であるから
  $`M[n] = \mathrm{cat}_n F`$ であり、上で求めたとおり
  $`\mathrm{head}(M[n]) = (M_{0,j_0}, M_{1,j_0}) = (M_{0,0}, M_{1,0})`$ である。
  その第 1 成分は $`M_{0,0}`$ である。$`M \ne ()`$ であるから $`M = x :: xs`$ と書け、
  $`\mathrm{head}\,M = x`$ かつ $`M\langle 0\rangle = x`$ であるから $`M_{0,0} = x_1`$ である。
  $`\mathrm{blockok}(0,M)`$ の第 1 の連言子を $`M \ne ()`$ に適用すると $`x_1 = 0`$ を得る。

- $`j_0 \ne 0`$ のとき。$`\lvert \mathrm{take}_{j_0} M\rvert = \min(j_0, \lvert M\rvert)`$ であり、
  $`0 \lt j_0`$ かつ $`0 \lt \lvert M\rvert`$ であるからこの値は $`0`$ より大きく、
  $`\mathrm{take}_{j_0} M \ne ()`$ である。
  [T.headI_append_left](#t-headI_append_left) より
  $`\mathrm{head}(M[n]) = \mathrm{head}(\mathrm{take}_{j_0} M)`$ である。
  $`M = x :: xs`$ と書き、$`j_0 = m + 1`$ とおくと
  $`\mathrm{take}_{m+1}(x :: xs) = x :: \mathrm{take}_m\,xs`$ であるから
  $`\mathrm{head}(\mathrm{take}_{j_0} M) = x = \mathrm{head}\,M`$ である。
  $`\mathrm{blockok}(0,M)`$ の第 1 の連言子を $`M \ne ()`$ に適用すると
  $`(\mathrm{head}\,M)_1 = 0`$ を得る。

**第 2（行 $`0`$ の値は $`0`$ 以上）。** 任意の $`p \in M[n]`$ に対し $`0 \le p_1`$ は、
$`0`$ が自然数の最小元であることによる。

**第 3（段差 1）。**[T.steps1_append](Seqlex.md#t-steps1_append) により、
$`\mathrm{steps}_1(\mathrm{take}_{j_0} M)`$、$`\mathrm{steps}_1(\mathrm{cat}_n F)`$、および
上で示した 3 選言の 3 つを言えばよく、いずれもすでに示した。∎

<a id="t-blockok_ST_PS"></a>
## 定理: 標準形はブロック (T.blockok_ST_PS)

### 定理

$`M \in \mathrm{ST\_PS}`$（[D.ST_PS](Pss.md#d-ST_PS)）ならば $`\mathrm{blockok}(0, M)`$。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M) :\equiv \mathrm{blockok}(0, M).
```

- **基底段**（規則 (diag)、$`M = \Delta_0^v`$）：[T.blockok_diagSeq](#t-blockok_diagSeq) が
  $`\Phi(\Delta_0^v)`$ そのものである。

- **帰納段**（規則 (oper)、$`M \in \mathrm{ST\_PS}`$ と $`1 \le n`$ から $`M[n]`$）：
  帰納法の仮定は $`\Phi(M)`$、すなわち $`\mathrm{blockok}(0, M)`$ である。
  [T.blockok_oper](#t-blockok_oper) をこれと $`1 \le n`$ に適用して
  $`\mathrm{blockok}(0, M[n])`$、すなわち $`\Phi(M[n])`$ を得る。∎

<a id="t-olt_ST_iff_seqlex"></a>
## 定理: 標準形上の順序同型 (T.olt_ST_iff_seqlex)

### 定理

$`M, N \in \mathrm{ST\_PS}`$ かつ $`M \ne N`$ ならば

```math
\mathrm{tr}\,M \prec \mathrm{tr}\,N \iff M \prec_{\mathrm{lex}} N .
```

### 証明

[T.blockok_ST_PS](#t-blockok_ST_PS) を $`M`$ と $`N`$ に適用して
$`\mathrm{blockok}(0, M)`$ と $`\mathrm{blockok}(0, N)`$ を得る。
これらと $`M \ne N`$ に [T.olt_iff_seqlex](#t-olt_iff_seqlex) を $`d := 0`$ で適用すればよい。∎
