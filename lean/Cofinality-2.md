[← README](README.md) ｜ Cofinality [1](Cofinality.md) **2** [3](Cofinality-3.md)

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

ここで $`\mathrm{tw}_a L`$ は $`L`$ の先頭から第 1 成分が $`a`$ より大きい要素が続く極大な
前部分列、$`\mathrm{dw}_a L`$ は $`L`$ から $`\mathrm{tw}_a L`$ を取り除いた残りの列であり、
どちらも $`\mathrm{tr}`$ の定義（D.translate）の記法である。

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
  [T.dropWhile_append_all](Term.md#t-dropWhile_append_all) を同じく $`xs := R`$、$`ys := Y`$ に
  適用して $`\mathrm{dw}_{v_0}(R \mathbin{+\!\!+} Y) = \mathrm{dw}_{v_0} Y`$ を得る。
  $`Y`$ の先頭 $`y`$ が述語を破るから $`\mathrm{dw}_{v_0} Y = Y`$ である。∎

<a id="t-copy_dom_zero"></a>
## 定理: 完全コピーによる支配 (T.copy_dom_zero)

### 定理

$`d \in \mathbb{N}`$、$`Y, R \in \mathrm{PairSeq}`$、$`v_0, w_0 \in \mathbb{N}`$ とし、
$`B := (v_0,w_0) :: R`$ とおく。次の 5 つを仮定する。

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
\exists m,\ \bigl(1 \le m \wedge Y \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)\bigr).
```

（$`\mathrm{cnf}`$ [D.cnf](Cnf.md#d-cnf)。以下 $`\mathsf{Z}`$ と $`\mathsf{P}`$ は
$`\mathrm{Three}`$ [D.Three](Term.md#d-Three)の構成子である。）

### 証明

自然数 $`d`$ に関する帰納法。帰納法の述語は

```math
\Phi(d) :\equiv \forall Y, v_0, w_0, R,\
  \bigl(\text{(len)} \wedge \text{(blk)} \wedge \text{(R)} \wedge \text{(hd)} \wedge \text{(cnf)}\bigr)
  \to \exists m,\ \bigl(1 \le m \wedge Y \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)\bigr).
```

ここで (len), (blk), (R), (hd), (cnf) は定理の 5 つの仮定であり、$`Y, v_0, w_0, R`$ は
$`\Phi(d)`$ の束縛変数である（$`B = (v_0,w_0) :: R`$ もそれに従って動く）。

- **基底段** $`d = 0`$：(len) は $`\lvert Y\rvert \le 0`$、すなわち $`\lvert Y\rvert = 0`$ であるから
  $`Y = ()`$ である。$`m := 1`$ と取る。[T.copies_one](Cnf-3.md#t-copies_one) より
  $`\mathrm{cp}_0(B, 1) = B = (v_0,w_0) :: R \ne ()`$ であるから、
  $`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式より
  $`() \prec_{\mathrm{lex}} \mathrm{cp}_0(B,1)`$ であり、
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

また $`Y = y :: Y'`$ により
$`\bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} (y :: Y') = (v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$ である。
[T.translate_block_append](Term.md#t-translate_block_append) を
$`v_0 := v_0`$、$`w_0 := w_0`$、$`R := R`$、$`T := y :: Y'`$ として適用する。
その 2 つの仮定「$`R`$ の全要素 $`x`$ が $`v_0 \lt x_1`$」と
「$`y :: Y' = ()`$ または $`\neg\bigl(v_0 \lt (\mathrm{head}\,(y :: Y'))_1\bigr)`$」は
それぞれ (R) と (hd) である。こうして

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
$`m := 1`$ と取る。[T.copies_one](Cnf-3.md#t-copies_one) より
$`\mathrm{cp}_0(B, 1) = (v_0,w_0) :: R`$ である。第 1 段より $`y = (v_0,y_2)`$ であり、
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
  = B \mathbin{+\!\!+} Y''
```

である。帰納法の仮定 $`\Phi(d)`$ を $`Y := Y''`$、$`v_0, w_0, R`$ はそのままとして適用する。
その 5 つの前件は次のように満たされる。

- (len)：$`\lvert R'\rvert + \lvert Y''\rvert = \lvert Y'\rvert`$ であり、いまの (len) は
  $`\lvert y :: Y'\rvert = \lvert Y'\rvert + 1 \le d + 1`$、すなわち $`\lvert Y'\rvert \le d`$ である。
  よって $`\lvert Y''\rvert \le \lvert Y'\rvert \le d`$。
- (blk)：$`(v_0,w_0) :: (R \mathbin{+\!\!+} Y'') = B \mathbin{+\!\!+} Y'' = y :: Y'`$ であるから、
  第 7 段の 2 そのものである。
- (R)：いまの (R) そのものである。
- (hd)：第 2 段で示した $`Y''`$ についての選言である。
- (cnf)：$`\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} Y'')\bigr) = \mathrm{tr}(y :: Y')`$ であり、
  第 3 段よりこれは $`\mathsf{P}(y_2, \mathrm{tr}\,R', \mathrm{tr}\,Y'')`$ であるから (c3) である。

こうして $`1 \le m`$ かつ $`Y'' \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$ なる $`m`$ が得られる。
求める添字として $`m + 1`$ を取る。$`1 \le m + 1`$ である。
[T.copies_succ_cons](Cnf-3.md#t-copies_succ_cons) と
[T.shiftr0_zero](Cnf-2.md#t-shiftr0_zero) より

```math
\mathrm{cp}_0(B, m+1) = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} \mathrm{cp}_0(B, m)^{+0}\bigr)
  = B \mathbin{+\!\!+} \mathrm{cp}_0(B, m)
```

である。したがって示すべきことは
$`B \mathbin{+\!\!+} Y'' \preceq_{\mathrm{lex}} B \mathbin{+\!\!+} \mathrm{cp}_0(B, m)`$ であり、
[T.sle_append_cancel](Cofinality.md#t-sle_append_cancel) によりこれは
$`Y'' \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$ と同値である。これは得られたものである。

**第 9 段：$`R' \ne R`$ のとき。**
まず $`R' \prec_{\mathrm{lex}} R`$ を示す。[T.seqlex_total](Seqlex-2.md#t-seqlex_total) より
$`R' = R`$、$`R' \prec_{\mathrm{lex}} R`$、$`R \prec_{\mathrm{lex}} R'`$ のいずれかである。
第 1 のものは仮定に反する。第 3 のものとすると、第 7 段の 3 と 4 を用いて
[T.seqlex_imp_olt](Seqlex-2.md#t-seqlex_imp_olt) を $`d := v_0 + 1`$、$`M := R`$、$`N := R'`$ に
適用でき、$`\mathrm{tr}\,R \prec \mathrm{tr}\,R'`$ となって第 7 段の 1 に矛盾する。
よって第 2 のもの、すなわち $`R' \prec_{\mathrm{lex}} R`$ である。

$`m := 2`$ と取る。$`1 \le 2`$ である。
[T.copies_succ_cons](Cnf-3.md#t-copies_succ_cons)、[T.shiftr0_zero](Cnf-2.md#t-shiftr0_zero)、
[T.copies_one](Cnf-3.md#t-copies_one) より

```math
\mathrm{cp}_0(B, 2) = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} \mathrm{cp}_0(B,1)^{+0}\bigr)
  = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} B\bigr)
```

である。第 1 段と $`y_2 = w_0`$ より $`y :: Y' = (v_0,w_0) :: Y'`$ であるから、
$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 3 式の第 2 選言により、示すべきことは

```math
Y' \prec_{\mathrm{lex}} R \mathbin{+\!\!+} B
```

である。$`Y' = R' \mathbin{+\!\!+} Y''`$ であるから、
[T.seqlex_splice](#t-seqlex_splice) を、小さい側の列を $`R'`$、大きい側の列を $`R`$、
小さい側に付ける列を $`Y''`$、大きい側に付ける列を $`B`$ として適用すればよい。
その 2 つの仮定は次のように満たされる。

- $`R' \prec_{\mathrm{lex}} R`$：いま示した。
- $`Y'' = () \vee \forall x \in R,\ \mathrm{head}\,Y'' \prec_{\mathrm{p}} x`$：
  第 2 段の $`Y''`$ についての選言で分ける。$`Y'' = ()`$ ならそのまま第 1 選言である。
  そうでなければ $`\neg\bigl(v_0 \lt (\mathrm{head}\,Y'')_1\bigr)`$、すなわち
  $`(\mathrm{head}\,Y'')_1 \le v_0`$ である。$`x \in R`$ に対し (R) より $`v_0 \lt x_1`$ であるから
  $`(\mathrm{head}\,Y'')_1 \lt x_1`$ であり、$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の
  第 1 選言により $`\mathrm{head}\,Y'' \prec_{\mathrm{p}} x`$ である。

以上で $`Y' \prec_{\mathrm{lex}} R \mathbin{+\!\!+} B`$ が得られ、
$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言が成り立つ。∎

<a id="t-copies_zero_succ"></a>
## 定理: 完全コピーの後置分解 (T.copies_zero_succ)

### 定理

$`B \in \mathrm{PairSeq}`$、$`m \in \mathbb{N}`$ に対し

```math
\mathrm{cp}_0(B, m+1) = \mathrm{cp}_0(B, m) \mathbin{+\!\!+} B .
```

### 証明

$`\mathrm{cp}`$ の定義（D.copies）より

```math
\mathrm{cp}_d(B, n) = B^{+0 \cdot d} \mathbin{+\!\!+} B^{+1 \cdot d}
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d}
```

である。すなわち添字の列 $`(0, 1, \dots, n-1)`$ の各 $`k`$ に $`B^{+k d}`$ を対応させて
連結したものである。$`n := m+1`$ のとき、この添字の列は $`(0, 1, \dots, m-1)`$ の後ろに
$`m`$ を付けたものであるから、連結は

```math
\mathrm{cp}_d(B, m+1) = \mathrm{cp}_d(B, m) \mathbin{+\!\!+} B^{+m d}
```

と分かれる。$`d := 0`$ とすると $`m \cdot 0 = 0`$ であり、
[T.shiftr0_zero](Cnf-2.md#t-shiftr0_zero) より $`B^{+0} = B`$ である。∎

<a id="t-crux_zero"></a>
## 定理: 完全コピー分岐の核心 (T.crux_zero)

### 定理

$`G, R, S \in \mathrm{PairSeq}`$、$`v_0, w_0 \in \mathbb{N}`$、$`\ell, q \in \mathbb{N}\times\mathbb{N}`$ とし、
$`B := (v_0, w_0) :: R`$ とおく。次の 4 つを仮定する。

```math
\begin{aligned}
&(1)\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S \in \mathrm{ST\_PS}, \cr
&(2)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(3)\ \ell_2 = 0 \ \wedge\ \ell_1 = v_0 + 1, \cr
&(4)\ q \prec_{\mathrm{p}} \ell .
\end{aligned}
```

このとき $`1 \le m`$ なる $`m \in \mathbb{N}`$ が存在して

```math
q :: S \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m) .
```

### 証明

以下、$`\mathrm{tw}_p`$、$`\mathrm{dw}_p`$ を一般の述語 $`p`$ について書く（$`\mathrm{tw}_p L`$ は
$`L`$ の先頭から $`p`$ をみたす要素が続く極大な前部分列、$`\mathrm{dw}_p L`$ はその残りである）。

**第 1 段：$`q_1 \le v_0`$。**
$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）より、仮定 (4) は
$`q_1 \lt \ell_1`$ または（$`q_1 = \ell_1`$ かつ $`q_2 \lt \ell_2`$）である。
後者のとき、仮定 (3) の $`\ell_2 = 0`$ より $`q_2 \lt 0`$ となるが、自然数に $`0`$ より小さいものは
ないから矛盾であり、この場合は起こらない。前者のとき、仮定 (3) の $`\ell_1 = v_0 + 1`$ より
$`q_1 \lt v_0 + 1`$、すなわち $`q_1 \le v_0`$ である。

**第 2 段：$`q_1 \lt v_0`$ の場合。**
$`m := 1`$ と取る。[T.copies_one](Cnf-3.md#t-copies_one) より $`\mathrm{cp}_0(B, 1) = B = (v_0,w_0) :: R`$ である。
$`q_1 \lt v_0`$ であるから $`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 1 選言により
$`q \prec_{\mathrm{p}} (v_0,w_0)`$ が成り立ち、$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の
第 3 式の第 1 選言により $`q :: S \prec_{\mathrm{lex}} B`$ を得る。
$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言により結論を得る。

**第 3 段：以下 $`q_1 = v_0`$ とする。**
第 1 段と $`\neg(q_1 \lt v_0)`$ から $`q_1 = v_0`$ である。述語 $`p`$ を
$`p(x) :\equiv v_0 \le x_1`$ で定め、

```math
Y := \mathrm{tw}_p(q :: S), \qquad V := \mathrm{dw}_p(q :: S)
```

とおく。次の 4 つが成り立つ。

**(i)** $`Y \mathbin{+\!\!+} V = q :: S`$。$`\mathrm{tw}_p`$ と $`\mathrm{dw}_p`$ の定義そのものである。

**(ii)** $`Y = q :: \mathrm{tw}_p S`$。$`q_1 = v_0`$ より $`p(q)`$ が成り立つので、
$`\mathrm{tw}_p`$ は先頭の $`q`$ を取り込む。とくに $`Y \ne ()`$ であり
$`(\mathrm{head}\,Y)_1 = q_1 = v_0`$ である。

**(iii)** $`\forall x \in Y,\ v_0 \le x_1`$。$`\mathrm{tw}_p`$ の要素はすべて $`p`$ をみたすからである。

**(iv)** $`V = ()`$、または $`V = z :: Z`$ かつ $`z_1 \lt v_0`$ なる $`z, Z`$ が存在する。
実際 $`V \ne ()`$ ならばその先頭要素 $`z`$ は $`\neg p(z)`$、すなわち $`\neg(v_0 \le z_1)`$ を
みたすから $`z_1 \lt v_0`$ である。

**第 4 段：$`B \mathbin{+\!\!+} Y`$ を用いた分解。**
(i) と結合律により

```math
(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S = \bigl(G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)\bigr) \mathbin{+\!\!+} V
```

である。この列を $`N`$ と書く。

**第 5 段：$`\mathrm{steps}_1(B \mathbin{+\!\!+} Y)`$。**
仮定 (1) と [T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS) より $`\mathrm{blockok}(0, N)`$ が成り立ち、
$`\mathrm{blockok}`$ の定義（D.blockok）の第 3 連言子より $`\mathrm{steps}_1(N)`$ である。
第 4 段の分解に [T.steps1_append](Seqlex.md#t-steps1_append) を適用すると、その第 1 連言子として
$`\mathrm{steps}_1\bigl(G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)\bigr)`$ を得る。これにふたたび
[T.steps1_append](Seqlex.md#t-steps1_append) を適用すると、その第 2 連言子として
$`\mathrm{steps}_1(B \mathbin{+\!\!+} Y)`$ を得る。

**第 6 段：$`\mathrm{blockok}(v_0,\ B \mathbin{+\!\!+} Y)`$。**
$`\mathrm{blockok}`$ の定義（D.blockok）の 3 つの連言子を確かめる。
第 1 連言子は「空でなければ先頭の第 1 成分が $`v_0`$」であり、先頭は $`(v_0,w_0)`$ だから成り立つ。
第 2 連言子は $`\forall x \in B \mathbin{+\!\!+} Y,\ v_0 \le x_1`$ である。
$`x = (v_0,w_0)`$ なら $`x_1 = v_0`$、$`x \in R`$ なら仮定 (2) より $`v_0 \lt x_1`$、
$`x \in Y`$ なら (iii) より $`v_0 \le x_1`$ である。第 3 連言子は第 5 段である。

**第 7 段：$`(v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$ の $`\mathrm{cnf}`$。**
仮定 (1) と [T.cnf_ST_PS](Cnf-3.md#t-cnf_ST_PS) より $`\mathrm{cnf}(\mathrm{tr}\,N)`$ である。
第 4 段の分解によりこれは
$`\mathrm{cnf}\bigl(\mathrm{tr}\bigl((G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)) \mathbin{+\!\!+} V\bigr)\bigr)`$ である。
[T.cnf_take](Cnf.md#t-cnf_take) を $`k := \lvert G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)\rvert`$ に適用する。
連結の左側の長さで切り取ると左側そのものが得られるから

```math
\mathrm{cnf}\bigl(\mathrm{tr}\,(G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y))\bigr)
```

を得る。$`B \mathbin{+\!\!+} Y = (v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$ であるから、これは
$`\mathrm{cnf}\bigl(\mathrm{tr}\,(G \mathbin{+\!\!+} ((v_0,w_0) :: (R \mathbin{+\!\!+} Y)))\bigr)`$ と同じ命題である。
[T.cnf_tail](Cnf-2.md#t-cnf_tail) を $`t := (v_0,w_0)`$、$`T' := R \mathbin{+\!\!+} Y`$、$`G := G`$ として
適用する。その仮定 $`\forall x \in R \mathbin{+\!\!+} Y,\ v_0 \le x_1`$ は第 6 段の第 2 連言子から
（$`R \mathbin{+\!\!+} Y`$ の要素は $`B \mathbin{+\!\!+} Y`$ の要素でもあるから）従う。よって

```math
\mathrm{cnf}\bigl(\mathrm{tr}\,((v_0,w_0) :: (R \mathbin{+\!\!+} Y))\bigr) .
```

**第 8 段：完全コピーによる支配。**
[T.copy_dom_zero](#t-copy_dom_zero) を $`d := \lvert Y\rvert`$、$`Y := Y`$、$`v_0`$、$`w_0`$、$`R`$ として
適用する。5 つの仮定は次のように満たされる。

- $`\lvert Y\rvert \le \lvert Y\rvert`$：等号による。
- $`\mathrm{blockok}\bigl(v_0,\ (v_0,w_0) :: (R \mathbin{+\!\!+} Y)\bigr)`$：第 6 段を
  $`B \mathbin{+\!\!+} Y = (v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$ と書き換えたものである。
- $`\forall x \in R,\ v_0 \lt x_1`$：仮定 (2) である。
- $`Y = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,Y)_1\bigr)`$：(ii) より
  $`(\mathrm{head}\,Y)_1 = v_0`$ であるから第 2 選言が成り立つ。
- $`\mathrm{cnf}\bigl(\mathrm{tr}\,((v_0,w_0) :: (R \mathbin{+\!\!+} Y))\bigr)`$：第 7 段である。

こうして $`1 \le m`$ なる $`m`$ と $`Y \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$ を得る。

**第 9 段：結論。**
求める添字として $`m + 1`$ を取る（$`1 \le m + 1`$）。
[T.copies_zero_succ](#t-copies_zero_succ) より
$`\mathrm{cp}_0(B, m+1) = \mathrm{cp}_0(B, m) \mathbin{+\!\!+} B`$ であり、(i) より $`q :: S = Y \mathbin{+\!\!+} V`$
であるから、示すべきは

```math
Y \mathbin{+\!\!+} V \prec_{\mathrm{lex}} \mathrm{cp}_0(B, m) \mathbin{+\!\!+} B
```

である（これが言えれば $`\preceq_{\mathrm{lex}}`$ の定義（D.sle）の第 2 選言により結論を得る）。
第 8 段の $`\preceq_{\mathrm{lex}}`$ を、$`\preceq_{\mathrm{lex}}`$ の定義（D.sle）に従って 2 つの場合に分ける。

**(a) $`Y = \mathrm{cp}_0(B, m)`$ のとき。**
示すべきは $`Y \mathbin{+\!\!+} V \prec_{\mathrm{lex}} Y \mathbin{+\!\!+} B`$ である。
[T.seqlex_append_cancel](Seqlex.md#t-seqlex_append_cancel) により
$`V \prec_{\mathrm{lex}} B`$ を示せばよい。(iv) で場合分けする。

- $`V = ()`$ のとき。$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の第 1 式により
  $`B \ne ()`$ を示せばよく、$`B = (v_0,w_0) :: R`$ は空でない。
- $`V = z :: Z`$ かつ $`z_1 \lt v_0`$ のとき。$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の第 1 選言により
  $`z \prec_{\mathrm{p}} (v_0,w_0)`$ であり、$`\prec_{\mathrm{lex}}`$ の定義（D.seqlex）の
  第 3 式の第 1 選言により $`z :: Z \prec_{\mathrm{lex}} (v_0,w_0) :: R`$ を得る。

**(b) $`Y \prec_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$ のとき。**
[T.seqlex_splice](#t-seqlex_splice) を、小さい側の列を $`Y`$、大きい側の列を $`\mathrm{cp}_0(B, m)`$、
小さい側に付ける列を $`V`$、大きい側に付ける列を $`B`$ として適用する。
残る仮定は「$`V = ()`$、または $`\forall x \in \mathrm{cp}_0(B,m),\ \mathrm{head}\,V \prec_{\mathrm{p}} x`$」
である。(iv) で場合分けする。

- $`V = ()`$ のとき。第 1 選言である。
- $`V = z :: Z`$ かつ $`z_1 \lt v_0`$ のとき。仮定 (2) より $`R`$ の各要素 $`y`$ は
  $`v_0 \le y_1`$ をみたすから、[T.copies_v0_le](Cnf-3.md#t-copies_v0_le) を $`d := 0`$、$`n := m`$ として
  適用して $`\forall x \in \mathrm{cp}_0(B, m),\ v_0 \le x_1`$ を得る。
  $`\mathrm{head}\,V = z`$ であり $`z_1 \lt v_0 \le x_1`$ であるから、$`\prec_{\mathrm{p}}`$ の定義（D.pairlt）の
  第 1 選言により $`z \prec_{\mathrm{p}} x`$ が成り立つ。

いずれの場合も $`Y \mathbin{+\!\!+} V \prec_{\mathrm{lex}} \mathrm{cp}_0(B,m) \mathbin{+\!\!+} B`$ が得られた。∎

<a id="d-AscCrux"></a>
## 定義: 上昇コピーの核心 (D.AscCrux)

命題 $`\mathrm{AscCrux}`$ を次で定める。ここで $`B := (v_0,w_0) :: R`$、
$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$ と略記する（$`(\ell)`$ は $`\ell`$ のみからなる長さ $`1`$ の列）。

```math
\begin{aligned}
\mathrm{AscCrux} :\equiv\ &\forall G, R, S \in \mathrm{PairSeq},\ \forall v_0, w_0, d_0 \in \mathbb{N},\
   \forall \ell, q \in \mathbb{N}\times\mathbb{N}, \cr
&\quad H \in \mathrm{ST\_PS}
  \ \to\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S \in \mathrm{ST\_PS} \cr
&\quad \to\ \bigl(\forall x \in R,\ v_0 \lt x_1\bigr)
  \ \to\ 0 \lt d_0 \ \to\ \ell_2 = w_0 + 1 \ \to\ \ell_1 = v_0 + d_0 \cr
&\quad \to\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert
  \ \to\ q \prec_{\mathrm{p}} \ell \cr
&\quad \to\ \exists m,\ 1 \le m \ \wedge\
   q :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B, m)\bigr)^{+d_0} .
\end{aligned}
```

<a id="d-AscCrux1"></a>
## 定義: 頭を取った上昇コピーの核心 (D.AscCrux1)

命題 $`\mathrm{AscCrux1}`$ を次で定める。ここで $`B := (v_0,w_0) :: R`$、
$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr)`$ と略記する。

```math
\begin{aligned}
\mathrm{AscCrux1} :\equiv\ &\forall G, R, S \in \mathrm{PairSeq},\ \forall v_0, w_0, d_0 \in \mathbb{N}, \cr
&\quad H \in \mathrm{ST\_PS}
  \ \to\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS} \cr
&\quad \to\ \bigl(\forall x \in R,\ v_0 \lt x_1\bigr) \ \to\ 0 \lt d_0 \cr
&\quad \to\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert \cr
&\quad \to\ \exists m,\ 1 \le m \ \wedge\
   (v_0+d_0,\ w_0) :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B, m)\bigr)^{+d_0} .
\end{aligned}
```

<a id="t-shiftr0_length"></a>
## 定理: 平行移動は長さを変えない (T.shiftr0_length)

### 定理

$`d \in \mathbb{N}`$、$`X \in \mathrm{PairSeq}`$ に対し $`\lvert X^{+d}\rvert = \lvert X\rvert`$。

### 証明

$`X^{+d}`$ の定義（D.shiftr0）より $`X^{+d}`$ は $`X`$ の各要素 $`x`$ を $`(x_1+d,\ x_2)`$ に写した列で
あり、写像の適用は列の長さを変えない。∎

<a id="t-mem_shiftr0_le"></a>
## 定理: 平行移動後の行 0 の下界 (T.mem_shiftr0_le)

### 定理

$`d, e \in \mathbb{N}`$、$`X \in \mathrm{PairSeq}`$ とする。
$`\forall x \in X,\ d \le x_1`$ ならば $`\forall x \in X^{+e},\ d + e \le x_1`$。

### 証明

$`x \in X^{+e}`$ とする。[T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) より、ある $`y \in X`$ が存在して
$`x = (y_1 + e,\ y_2)`$ である。仮定より $`d \le y_1`$ であるから
$`d + e \le y_1 + e = x_1`$ である。∎

<a id="t-shiftr0_copies"></a>
## 定理: 平行移動とコピー塔の交換 (T.shiftr0_copies)

### 定理

$`d, n \in \mathbb{N}`$、$`B \in \mathrm{PairSeq}`$ に対し

```math
\bigl(\mathrm{cp}_d(B, n)\bigr)^{+d} = \mathrm{cp}_d\bigl(B^{+d},\ n\bigr) .
```

### 証明

$`\mathrm{cp}_d`$ の定義（D.copies）より

```math
\mathrm{cp}_d(B, n) = B^{+0\cdot d} \mathbin{+\!\!+} B^{+1\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d}
```

である。$`\cdot^{+d}`$ は各要素への写像の適用であるから連結を保ち、
$`(X \mathbin{+\!\!+} Y)^{+d} = X^{+d} \mathbin{+\!\!+} Y^{+d}`$ が成り立つ。これを繰り返して

```math
\bigl(\mathrm{cp}_d(B, n)\bigr)^{+d}
  = \bigl(B^{+0\cdot d}\bigr)^{+d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl(B^{+(n-1)d}\bigr)^{+d}
```

を得る。他方

```math
\mathrm{cp}_d\bigl(B^{+d},\ n\bigr)
  = \bigl(B^{+d}\bigr)^{+0\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl(B^{+d}\bigr)^{+(n-1)d}
```

である。両者の第 $`k`$ 項（$`k = 0, \dots, n-1`$）を比べる。$`x \in B`$ に対し
$`\bigl(B^{+kd}\bigr)^{+d}`$ の対応する要素は $`(x_1 + kd + d,\ x_2)`$、
$`\bigl(B^{+d}\bigr)^{+kd}`$ の対応する要素は $`(x_1 + d + kd,\ x_2)`$ であり、
自然数の加法の結合律と交換律により $`x_1 + kd + d = x_1 + d + kd`$ である。
第 2 成分はどちらも $`x_2`$ で変わらない。よって第 $`k`$ 項どうしは等しく、
連結も等しい。∎
