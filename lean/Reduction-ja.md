[← README](README-ja.md) | [English](Reduction.md) | [Japanese](Reduction-ja.md)

<a id="d-Acc"></a>
## 定義: 到達可能な元の集合 (D.Acc)

集合 $`A`$ 上の関係 $`R \subseteq A \times A`$ と $`Y \subseteq A`$ に対し、$`Y`$ が
$`R`$ について**閉じている**ことを

```math
\forall x \in A,\ \bigl(\forall y \in A,\ y \mathbin{R} x \to y \in Y\bigr) \to x \in Y
```

が成り立つことと定義する。そのうえで $`\mathrm{Acc}_R \subseteq A`$ を

```math
\mathrm{Acc}_R := \bigcap\, \bigl\{\, Y \subseteq A \ \bigm|\ Y \text{ は } R \text{ について閉じている} \,\bigr\}
```

と定義する。すなわち $`x \in \mathrm{Acc}_R`$ とは、$`R`$ について閉じているすべての
$`Y \subseteq A`$ に対し $`x \in Y`$ が成り立つことである。

<a id="t-Acc.intro"></a>
## 定理: 到達可能な元の集合は閉じている (T.Acc.intro)

### 定理

$`x \in A`$ とする。$`\forall y \in A,\ y \mathbin{R} x \to y \in \mathrm{Acc}_R`$ ならば
$`x \in \mathrm{Acc}_R`$。

### 証明

$`Y \subseteq A`$ を $`R`$ について閉じている任意の集合とする。$`x \in Y`$ を示せば、
$`Y`$ が任意だったから $`\mathrm{Acc}_R`$ の定義（D.Acc）より $`x \in \mathrm{Acc}_R`$ が従う。

$`y \in A`$ が $`y \mathbin{R} x`$ をみたすとする。仮定より $`y \in \mathrm{Acc}_R`$ であり、
$`\mathrm{Acc}_R`$ の定義（D.Acc）より $`y`$ は閉じているすべての集合に属するから、とくに
$`y \in Y`$ である。よって $`\forall y \in A,\ y \mathbin{R} x \to y \in Y`$ が成り立つ。
$`Y`$ は閉じているから $`x \in Y`$。∎

<a id="t-Acc.rec"></a>
## 定理: 到達可能な元の集合の導出に関する帰納法 (T.Acc.rec)

### 定理

$`A`$ 上の述語 $`\Phi`$ が

```math
\forall x \in A,\
  \Bigl(\bigl(\forall y \in A,\ y \mathbin{R} x \to y \in \mathrm{Acc}_R\bigr)
  \wedge \bigl(\forall y \in A,\ y \mathbin{R} x \to \Phi(y)\bigr)\Bigr)
  \to \Phi(x)
```

をみたすならば、$`\forall x \in \mathrm{Acc}_R,\ \Phi(x)`$ が成り立つ。

### 証明

```math
Y := \{\, x \in A \mid x \in \mathrm{Acc}_R \wedge \Phi(x) \,\}
```

とおく。$`Y`$ が $`R`$ について閉じていることを示す。$`x \in A`$ を取り
$`\forall y \in A,\ y \mathbin{R} x \to y \in Y`$ を仮定する。$`Y`$ の定義より、これは

```math
\bigl(\forall y \in A,\ y \mathbin{R} x \to y \in \mathrm{Acc}_R\bigr)
\ \wedge\
\bigl(\forall y \in A,\ y \mathbin{R} x \to \Phi(y)\bigr)
```

に等しい。第 1 連言子と [T.Acc.intro](#t-Acc.intro) より $`x \in \mathrm{Acc}_R`$ である。
また 2 つの連言子は本定理の仮定の前件そのものであるから、その仮定を $`x`$ に適用して
$`\Phi(x)`$ を得る。よって $`x \in Y`$ であり、$`Y`$ は閉じている。

$`\mathrm{Acc}_R`$ の定義（D.Acc）より $`\mathrm{Acc}_R \subseteq Y`$ である。
$`x \in \mathrm{Acc}_R`$ を取ると $`x \in Y`$、すなわち $`\Phi(x)`$ が成り立つ。∎

<a id="d-WellFounded"></a>
## 定義: 整礎 (D.WellFounded)

関係 $`R \subseteq A \times A`$ が**整礎**であることを、
$`\forall x \in A,\ x \in \mathrm{Acc}_R`$ が成り立つことと定義する。

<a id="d-NF"></a>
## 定義: 正規形の集合 (D.NF)

$`\mathrm{Three}`$（[D.Three](Term-ja.md#d-Three)）の部分集合 $`\mathrm{NF}`$ を、
$`M \in \mathrm{ST\_PS}`$（[D.ST_PS](Pss-ja.md#d-ST_PS)）なる
$`M \in \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）の
$`\mathrm{tr}`$（[D.translate](Term-ja.md#d-translate)）による像として定める。

```math
\mathrm{NF} := \{\, t \in \mathrm{Three} \mid \exists M,\ M \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,M = t \,\} .
```

$`\mathrm{NF}`$ の元を**正規形**と呼ぶ。

<a id="d-Rnf"></a>
## 定義: 正規形上の順序 (D.Rnf)

$`u, v \in \mathrm{Three}`$ に対し、関係 $`R_{\mathrm{NF}}`$ を次で定める。

```math
v \mathbin{R_{\mathrm{NF}}} u :\iff v \prec u \ \wedge\ u \in \mathrm{NF} \ \wedge\ v \in \mathrm{NF} .
```

（$`\prec`$ [D.olt](Term-ja.md#d-olt)）

<a id="d-stepRel"></a>
## 定義: 標準形上の 1 段展開関係 (D.stepRel)

$`T, M \in \mathrm{PairSeq}`$ に対し、関係 $`R_{\mathrm{PS}}`$ を次で定める。

```math
T \mathbin{R_{\mathrm{PS}}} M :\iff M \in \mathrm{ST\_PS} \ \wedge\ M \Rightarrow T .
```

（$`M \Rightarrow T`$ [D.step](Pss-ja.md#d-step)）

第 1 引数 $`T`$ が展開の結果、第 2 引数 $`M`$ が展開の元である。$`R_{\mathrm{NF}}`$ の定義（D.Rnf）で
第 1 引数 $`v`$ が $`v \prec u`$ の左辺に置かれるのと同じ引数の順である。

<a id="t-step_terminates_cond"></a>
## 定理: 条件付きの停止性 (T.step_terminates_cond)

### 定理

次の 2 つを仮定する。

**(dec)** 任意の $`M \in \mathrm{PairSeq}`$ と $`n \in \mathbb{N}`$ に対し、
$`M \in \mathrm{ST\_PS}`$ かつ $`1 \lt \lvert M\rvert`$ かつ $`1 \le n`$ ならば

```math
\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M .
```

（$`M[n]`$ [D.oper](Pss-ja.md#d-oper)）

**(wfimg)** $`R_{\mathrm{NF}}`$ は整礎である。

(dec) と (wfimg) の下で、$`R_{\mathrm{PS}}`$ は整礎である。

### 証明

$`\mathrm{tr}`$ による $`R_{\mathrm{NF}}`$ の逆像を

```math
T \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M :\iff \mathrm{tr}\,T \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M
```

と書く。3 段に分ける。

**第 1 段：$`T \mathbin{R_{\mathrm{PS}}} M`$ ならば $`T \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M`$。**

$`T \mathbin{R_{\mathrm{PS}}} M`$ とする。$`R_{\mathrm{PS}}`$ の定義（D.stepRel）より
$`M \in \mathrm{ST\_PS}`$ かつ $`M \Rightarrow T`$ である。$`\Rightarrow`$ の定義（D.step）は
規則 (step_oper) ただ 1 つからなるから、$`n \in \mathbb{N}`$ が存在して

```math
1 \lt \lvert M\rvert, \qquad 1 \le n, \qquad T = M[n]
```

が成り立つ。$`R_{\mathrm{NF}}`$ の定義（D.Rnf）の 3 つの連言子を順に示す。

1. $`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$：仮定 (dec) を $`M`$ と $`n`$ に適用する。
   その 3 つの前件 $`M \in \mathrm{ST\_PS}`$、$`1 \lt \lvert M\rvert`$、$`1 \le n`$ は
   いま得たものである。
2. $`\mathrm{tr}\,M \in \mathrm{NF}`$：$`\mathrm{NF}`$ の定義（D.NF）の存在量化子を
   $`M`$ 自身で満たす。実際 $`M \in \mathrm{ST\_PS}`$ であり $`\mathrm{tr}\,M = \mathrm{tr}\,M`$ である。
3. $`\mathrm{tr}\,(M[n]) \in \mathrm{NF}`$：$`\mathrm{ST\_PS}`$ の定義（D.ST_PS）の規則 (oper) を
   $`M \in \mathrm{ST\_PS}`$ と $`1 \le n`$ に適用して $`M[n] \in \mathrm{ST\_PS}`$ を得る。
   $`\mathrm{NF}`$ の定義の存在量化子を $`M[n]`$ で満たせばよい。

すなわち $`\mathrm{tr}\,(M[n]) \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M`$ である。
$`T = M[n]`$ であるから、これは $`\mathrm{tr}\,T \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M`$、
すなわち $`T \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M`$ である。

**第 2 段：$`R^{\mathrm{tr}}_{\mathrm{NF}}`$ は整礎である。**

$`\mathrm{Acc}_{R_{\mathrm{NF}}}`$ の導出に関する帰納法（[T.Acc.rec](#t-Acc.rec)）を行う。帰納法の述語は

```math
\Phi(t) :\equiv \forall M \in \mathrm{PairSeq},\
  \mathrm{tr}\,M = t \to M \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}} .
```

**帰納段**：$`t \in \mathrm{Three}`$ を取り、帰納法の仮定

```math
\forall s \in \mathrm{Three},\ s \mathbin{R_{\mathrm{NF}}} t \to \Phi(s)
```

を仮定する（規則の前提 $`\forall s \in \mathrm{Three},\ s \mathbin{R_{\mathrm{NF}}} t \to s \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$
も同時に使えるが、以下では用いない）。$`M \in \mathrm{PairSeq}`$ を $`\mathrm{tr}\,M = t`$ なる列とする。
$`M \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}`$ を示すには、[T.Acc.intro](#t-Acc.intro)により

```math
\forall N \in \mathrm{PairSeq},\ N \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M \to N \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}
```

を示せばよい。$`N \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M`$ とすると、逆像の定義より
$`\mathrm{tr}\,N \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M`$ であり、$`\mathrm{tr}\,M = t`$ であるから
$`\mathrm{tr}\,N \mathbin{R_{\mathrm{NF}}} t`$ である。帰納法の仮定を $`s := \mathrm{tr}\,N`$ に適用して
$`\Phi(\mathrm{tr}\,N)`$ を得、これを $`N`$ と $`\mathrm{tr}\,N = \mathrm{tr}\,N`$ に適用して
$`N \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}`$ を得る。よって $`\Phi(t)`$ が成り立つ。

以上より $`\forall t \in \mathrm{Acc}_{R_{\mathrm{NF}}},\ \Phi(t)`$ である。仮定 (wfimg) より
任意の $`t \in \mathrm{Three}`$ が $`\mathrm{Acc}_{R_{\mathrm{NF}}}`$ に属するから、任意の
$`M \in \mathrm{PairSeq}`$ について $`\Phi(\mathrm{tr}\,M)`$ が成り立ち、これを $`M`$ と
$`\mathrm{tr}\,M = \mathrm{tr}\,M`$ に適用して $`M \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}`$ を得る。
すなわち $`R^{\mathrm{tr}}_{\mathrm{NF}}`$ は整礎である。

**第 3 段：$`R_{\mathrm{PS}}`$ は整礎である。**

$`\mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}`$ の導出に関する帰納法（[T.Acc.rec](#t-Acc.rec)）を行う。帰納法の述語は

```math
\Psi(M) :\equiv M \in \mathrm{Acc}_{R_{\mathrm{PS}}} .
```

**帰納段**：$`M \in \mathrm{PairSeq}`$ を取り、帰納法の仮定

```math
\forall N \in \mathrm{PairSeq},\ N \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M \to \Psi(N)
```

を仮定する。$`T \mathbin{R_{\mathrm{PS}}} M`$ なる任意の $`T`$ について、第 1 段より
$`T \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M`$ であるから、帰納法の仮定より $`\Psi(T)`$、すなわち
$`T \in \mathrm{Acc}_{R_{\mathrm{PS}}}`$ である。よって

```math
\forall T \in \mathrm{PairSeq},\ T \mathbin{R_{\mathrm{PS}}} M \to T \in \mathrm{Acc}_{R_{\mathrm{PS}}}
```

が成り立ち、[T.Acc.intro](#t-Acc.intro)より $`M \in \mathrm{Acc}_{R_{\mathrm{PS}}}`$、すなわち $`\Psi(M)`$。

以上より $`\forall M \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}},\ \Psi(M)`$ である。第 2 段より
任意の $`M \in \mathrm{PairSeq}`$ が $`\mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}`$ に属するから、
$`\forall M \in \mathrm{PairSeq},\ \Psi(M)`$、すなわち $`R_{\mathrm{PS}}`$ は整礎である。∎

<a id="t-no_infinite_expansion_cond"></a>
## 定理: 条件付きの無限展開列の非存在 (T.no_infinite_expansion_cond)

### 定理

[T.step_terminates_cond](#t-step_terminates_cond) と同じ 2 つの仮定 (dec), (wfimg) を置く。
このとき、次の 2 条件をみたす $`S : \mathbb{N} \to \mathrm{PairSeq}`$ は存在しない。

```math
\forall i \in \mathbb{N},\ S_i \in \mathrm{ST\_PS},
\qquad
\forall i \in \mathbb{N},\ S_i \Rightarrow S_{i+1} .
```

ここで $`S_i`$ は $`S`$ の $`i`$ における値である。

### 証明

2 条件をみたす $`S`$ が存在したとして矛盾を導く。

まず [T.step_terminates_cond](#t-step_terminates_cond) を仮定 (dec), (wfimg) に適用して、
$`R_{\mathrm{PS}}`$ が整礎であることを得る。

次に、任意の $`i \in \mathbb{N}`$ について

```math
(\ast)\qquad S_{i+1} \mathbin{R_{\mathrm{PS}}} S_i
```

が成り立つ。実際 $`R_{\mathrm{PS}}`$ の定義（D.stepRel）の 2 つの連言子は、$`S`$ の第 1 の条件を
$`i`$ に適用した $`S_i \in \mathrm{ST\_PS}`$ と、第 2 の条件を $`i`$ に適用した
$`S_i \Rightarrow S_{i+1}`$ そのものである。

$`\mathrm{Acc}_{R_{\mathrm{PS}}}`$ の導出に関する帰納法（[T.Acc.rec](#t-Acc.rec)）を行う。帰納法の述語は

```math
\Theta(x) :\equiv \forall i \in \mathbb{N},\ S_i = x \to \bot .
```

**帰納段**：$`x \in \mathrm{PairSeq}`$ を取り、帰納法の仮定

```math
\forall y \in \mathrm{PairSeq},\ y \mathbin{R_{\mathrm{PS}}} x \to \Theta(y)
```

を仮定する。$`i \in \mathbb{N}`$ を取り $`S_i = x`$ とする。$`(\ast)`$ より
$`S_{i+1} \mathbin{R_{\mathrm{PS}}} S_i`$ であり、$`S_i = x`$ を代入して
$`S_{i+1} \mathbin{R_{\mathrm{PS}}} x`$ を得る。帰納法の仮定を $`y := S_{i+1}`$ に適用して
$`\Theta(S_{i+1})`$ を得、これを $`i + 1`$ と $`S_{i+1} = S_{i+1}`$ に適用して $`\bot`$ を得る。
よって $`\Theta(x)`$ が成り立つ。

以上より $`\forall x \in \mathrm{Acc}_{R_{\mathrm{PS}}},\ \Theta(x)`$ である。$`R_{\mathrm{PS}}`$ は
整礎であるから $`S_0 \in \mathrm{Acc}_{R_{\mathrm{PS}}}`$ であり、$`\Theta(S_0)`$ を $`0`$ と
$`S_0 = S_0`$ に適用して $`\bot`$ を得る。これが求める矛盾である。∎

<a id="t-step_terminates"></a>
## 定理: 停止性 (T.step_terminates)

### 定理

$`R_{\mathrm{NF}}`$ が整礎ならば $`R_{\mathrm{PS}}`$ は整礎である。

### 証明

[T.step_terminates_cond](#t-step_terminates_cond) の仮定 (dec) を示す。
$`M \in \mathrm{PairSeq}`$ と $`n \in \mathbb{N}`$ を取り、$`M \in \mathrm{ST\_PS}`$、
$`1 \lt \lvert M\rvert`$、$`1 \le n`$ を仮定する。
[T.m_step_decreases](Decrease-ja.md#t-m_step_decreases) は $`1 \lt \lvert M\rvert`$ と $`1 \le n`$ の
2 つのみを前件とし、$`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$ を結論とする。よって仮定
$`M \in \mathrm{ST\_PS}`$ を用いずに結論が得られ、(dec) が成り立つ。

これと本定理の仮定 $`R_{\mathrm{NF}}`$ の整礎性を (wfimg) として
[T.step_terminates_cond](#t-step_terminates_cond) に与えればよい。∎

<a id="t-no_infinite_expansion"></a>
## 定理: 無限展開列の非存在 (T.no_infinite_expansion)

### 定理

$`R_{\mathrm{NF}}`$ が整礎ならば、次の 2 条件をみたす $`S : \mathbb{N} \to \mathrm{PairSeq}`$ は
存在しない。

```math
\forall i \in \mathbb{N},\ S_i \in \mathrm{ST\_PS},
\qquad
\forall i \in \mathbb{N},\ S_i \Rightarrow S_{i+1} .
```

### 証明

[T.no_infinite_expansion_cond](#t-no_infinite_expansion_cond) の仮定 (dec) を示す。
$`M \in \mathrm{PairSeq}`$ と $`n \in \mathbb{N}`$ を取り、$`M \in \mathrm{ST\_PS}`$、
$`1 \lt \lvert M\rvert`$、$`1 \le n`$ を仮定する。
[T.m_step_decreases](Decrease-ja.md#t-m_step_decreases) は $`1 \lt \lvert M\rvert`$ と $`1 \le n`$ の
2 つのみを前件とし、$`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$ を結論とする。よって仮定
$`M \in \mathrm{ST\_PS}`$ を用いずに結論が得られ、(dec) が成り立つ。

これと本定理の仮定 $`R_{\mathrm{NF}}`$ の整礎性を (wfimg) として
[T.no_infinite_expansion_cond](#t-no_infinite_expansion_cond) に与えればよい。∎
