[← README](README-ja.md) | [English](Final.md) | [Japanese](Final-ja.md)

<a id="t-acc_Rnf_of_acc_PS"></a>
## 定理: 到達可能性の項側への移送 (T.acc_Rnf_of_acc_PS)

### 定理

$`M \in \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）上の関係 $`R_{\mathrm{st}}`$（[D.Rst](Wset-ja.md#d-Rst)）の定義（D.Rst）は

```math
a \mathbin{R_{\mathrm{st}}} b :\iff
  a \in \mathrm{ST\_PS} \ \wedge\ b \in \mathrm{ST\_PS} \ \wedge\ \mathrm{tr}\,a \prec \mathrm{tr}\,b
```

である（$`\mathrm{ST\_PS}`$ [D.ST_PS](Pss-ja.md#d-ST_PS)、$`\mathrm{tr}`$ [D.translate](Term-ja.md#d-translate)、$`\prec`$ [D.olt](Term-ja.md#d-olt)）。

（$`\mathrm{Acc}_R`$ [D.Acc](Reduction-ja.md#d-Acc)、整礎 [D.WellFounded](Reduction-ja.md#d-WellFounded)）

このとき、任意の $`M \in \mathrm{PairSeq}`$ に対し、$`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ かつ
$`M \in \mathrm{ST\_PS}`$ ならば $`\mathrm{tr}\,M \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ である。

（$`R_{\mathrm{NF}}`$ [D.Rnf](Reduction-ja.md#d-Rnf)）

### 証明

$`M \in \mathrm{PairSeq}`$ と $`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ を取り、
$`\mathrm{Acc}_{R_{\mathrm{st}}}`$ の導出に関する帰納法（[T.Acc.rec](Reduction-ja.md#t-Acc.rec)）を行う。

```math
\Phi(M_0) :\equiv M_0 \in \mathrm{ST\_PS} \to \mathrm{tr}\,M_0 \in \mathrm{Acc}_{R_{\mathrm{NF}}}
```

を $`M_0`$ について示す。

**帰納段**：$`M_0 \in \mathrm{PairSeq}`$ を取り、帰納法の仮定

```math
\forall N \in \mathrm{PairSeq},\ N \mathbin{R_{\mathrm{st}}} M_0 \to \Phi(N)
```

を仮定する（規則のもう一方の前提
$`\forall N,\ N \mathbin{R_{\mathrm{st}}} M_0 \to N \in \mathrm{Acc}_{R_{\mathrm{st}}}`$
も同時に使えるが、以下では用いない）。$`M_0 \in \mathrm{ST\_PS}`$ を仮定して
$`\mathrm{tr}\,M_0 \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ を示す。[T.Acc.intro](Reduction-ja.md#t-Acc.intro)により、

```math
\forall v \in \mathrm{Three},\
  v \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M_0 \to v \in \mathrm{Acc}_{R_{\mathrm{NF}}}
```

を示せばよい（$`\mathrm{Three}`$ [D.Three](Term-ja.md#d-Three)）。
$`v \in \mathrm{Three}`$ を取り $`v \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M_0`$ とする。
$`R_{\mathrm{NF}}`$ の定義（D.Rnf）より次の 3 つが成り立つ。

```math
v \prec \mathrm{tr}\,M_0, \qquad
\mathrm{tr}\,M_0 \in \mathrm{NF}, \qquad
v \in \mathrm{NF} .
```

（$`\mathrm{NF}`$ [D.NF](Reduction-ja.md#d-NF)）第 2 の連言子 $`\mathrm{tr}\,M_0 \in \mathrm{NF}`$ は以下で用いない。

第 3 の連言子 $`v \in \mathrm{NF}`$ に $`\mathrm{NF}`$ の定義（D.NF）を適用すると、
$`N \in \mathrm{PairSeq}`$ が存在して

```math
N \in \mathrm{ST\_PS}, \qquad \mathrm{tr}\,N = v
```

が成り立つ。以下 $`v`$ を $`\mathrm{tr}\,N`$ で置き換える。第 1 の連言子は
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M_0`$ となる。

$`R_{\mathrm{st}}`$ の定義（D.Rst）の 3 つの連言子は、いま得た $`N \in \mathrm{ST\_PS}`$、
帰納段の仮定 $`M_0 \in \mathrm{ST\_PS}`$、および $`\mathrm{tr}\,N \prec \mathrm{tr}\,M_0`$ であるから、
$`N \mathbin{R_{\mathrm{st}}} M_0`$ が成り立つ。帰納法の仮定をこれに適用して $`\Phi(N)`$ を得、
さらに $`\Phi(N)`$ を $`N \in \mathrm{ST\_PS}`$ に適用して
$`\mathrm{tr}\,N \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ を得る。これは $`v \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ である。

よって $`\Phi(M_0)`$ が成り立つ。帰納法により
$`\forall M \in \mathrm{Acc}_{R_{\mathrm{st}}},\ \Phi(M)`$ である。∎

<a id="t-wf_Rnf_of_wf_PS"></a>
## 定理: 整礎性の項側への移送 (T.wf_Rnf_of_wf_PS)

### 定理

$`R_{\mathrm{st}}`$ が整礎ならば $`R_{\mathrm{NF}}`$ は整礎である。

### 証明

$`u \in \mathrm{Three}`$ を取り、$`u \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ を示す。
排中律により $`u \in \mathrm{NF}`$ と $`u \notin \mathrm{NF}`$ で場合分けする。

**(a) $`u \in \mathrm{NF}`$ のとき。** $`\mathrm{NF}`$ の定義（D.NF）より
$`M \in \mathrm{PairSeq}`$ が存在して $`M \in \mathrm{ST\_PS}`$ かつ $`\mathrm{tr}\,M = u`$ である。
以下 $`u`$ を $`\mathrm{tr}\,M`$ で置き換える。本定理の仮定「$`R_{\mathrm{st}}`$ は整礎」を
$`M`$ に適用して $`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ を得る。これと $`M \in \mathrm{ST\_PS}`$ を
[T.acc_Rnf_of_acc_PS](#t-acc_Rnf_of_acc_PS) に与えて
$`\mathrm{tr}\,M \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$、すなわち $`u \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ を得る。

**(b) $`u \notin \mathrm{NF}`$ のとき。** [T.Acc.intro](Reduction-ja.md#t-Acc.intro)により

```math
\forall v \in \mathrm{Three},\ v \mathbin{R_{\mathrm{NF}}} u \to v \in \mathrm{Acc}_{R_{\mathrm{NF}}}
```

を示せばよい。$`v \in \mathrm{Three}`$ を取り $`v \mathbin{R_{\mathrm{NF}}} u`$ とすると、
$`R_{\mathrm{NF}}`$ の定義（D.Rnf）の第 2 の連言子より $`u \in \mathrm{NF}`$ である。これは
場合分けの仮定 $`u \notin \mathrm{NF}`$ と矛盾する。よって前件が偽であり、結論
$`v \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ が従う。

いずれの場合も $`u \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ であるから、$`R_{\mathrm{NF}}`$ は整礎である。∎

<a id="t-pss_cofinality_holds"></a>
## 定理: PSS の共終性 (T.pss_cofinality_holds)

### 定理

$`M, N \in \mathrm{PairSeq}`$ とする。$`M \in \mathrm{ST\_PS}`$ かつ $`N \in \mathrm{ST\_PS}`$ かつ
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ ならば

```math
\exists n \in \mathbb{N},\ 1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n]) .
```

（$`M[n]`$ [D.oper](Pss-ja.md#d-oper)、$`\preceq`$ [D.ole](Term-ja.md#d-ole)）

### 証明

$`M, N \in \mathrm{PairSeq}`$ を取り、本定理の 3 つの仮定に名前を付ける。

```math
(\mathrm{h}_1)\ M \in \mathrm{ST\_PS}, \qquad
(\mathrm{h}_2)\ N \in \mathrm{ST\_PS}, \qquad
(\mathrm{h}_3)\ \mathrm{tr}\,N \prec \mathrm{tr}\,M
```

**第 1 段（中核の調達）.** [T.argDomCore_holds](ArgDom-5-ja.md#t-argDomCore_holds) は前件を
持たない定理であり、その結論は命題
$`\mathrm{ArgDomCore}`$（[D.ArgDomCore](ArgDom-ja.md#d-ArgDomCore)）そのものである。
よって $`\mathrm{ArgDomCore}`$ が成り立つ。これを $`(\mathrm{H})`$ とおく。

**第 2 段（共終性定理の具体化）.** [T.pss_cofinality_of_core](ArgDom-ja.md#t-pss_cofinality_of_core)
の主張は次の形をしている。

```math
\begin{aligned}
&\mathrm{ArgDomCore} \ \longrightarrow\
  \forall M', N' \in \mathrm{PairSeq}, \cr
&\qquad M' \in \mathrm{ST\_PS} \ \to\ N' \in \mathrm{ST\_PS}
  \ \to\ \mathrm{tr}\,N' \prec \mathrm{tr}\,M' \cr
&\qquad\qquad \to\ \exists n \in \mathbb{N},\ 1 \le n \ \wedge\
  \mathrm{tr}\,N' \preceq \mathrm{tr}\,(M'[n])
\end{aligned}
```

全称量化された $`M'`$、$`N'`$ を本定理の $`M`$、$`N`$ でそれぞれ具体化する。すると前件は

```math
\mathrm{ArgDomCore}, \qquad M \in \mathrm{ST\_PS}, \qquad N \in \mathrm{ST\_PS},
\qquad \mathrm{tr}\,N \prec \mathrm{tr}\,M
```

の 4 つ、後件は

```math
\exists n \in \mathbb{N},\ 1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])
```

となる。

**第 3 段（適用）.** 第 2 段の 4 つの前件は、順に $`(\mathrm{H})`$、$`(\mathrm{h}_1)`$、
$`(\mathrm{h}_2)`$、$`(\mathrm{h}_3)`$ である。これらを与えると後件が得られる。後件は
本定理の結論と同一の命題であるから、求める $`n`$ が存在する。∎

<a id="t-wf_olt_ST_PS_holds"></a>
## 定理: 標準形上の順序の整礎性 (T.wf_olt_ST_PS_holds)

### 定理

$`R_{\mathrm{st}}`$ は整礎である。

### 証明

**第 1 段（前件の調達）.** まず次の $`(\mathrm{cof})`$ を示す。

```math
\begin{aligned}
(\mathrm{cof})\ \ &\forall M, N \in \mathrm{PairSeq}, \cr
&\quad M \in \mathrm{ST\_PS} \ \to\ N \in \mathrm{ST\_PS}
  \ \to\ \mathrm{tr}\,N \prec \mathrm{tr}\,M \cr
&\qquad \to\ \exists n \in \mathbb{N},\ 1 \le n \ \wedge\
  \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])
\end{aligned}
```

$`M, N \in \mathrm{PairSeq}`$ を取り、$`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ を仮定する。
[T.pss_cofinality_holds](#t-pss_cofinality_holds) はこの 3 つを前件とし

```math
\exists n \in \mathbb{N},\ 1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])
```

を結論とする定理であるから、3 つを与えて結論を得る。$`M`$、$`N`$ と 3 つの仮定は
任意に取ったものであったから、$`(\mathrm{cof})`$ が成り立つ。

**第 2 段（引用定理の形）.** [T.wf_olt_ST_PS_of_cofinality](Wset-4-ja.md#t-wf_olt_ST_PS_of_cofinality)
の主張は次の形をしている。

```math
(\mathrm{cof}) \ \longrightarrow\ \mathrm{WellFounded}(\rho),
\qquad
a \mathbin{\rho} b :\iff
  a \in \mathrm{ST\_PS} \ \wedge\ b \in \mathrm{ST\_PS} \ \wedge\ \mathrm{tr}\,a \prec \mathrm{tr}\,b
```

全称量化された変数は $`(\mathrm{cof})`$ の内部にあるだけなので、主張そのものへの具体化は
不要である。また $`\rho`$ は $`R_{\mathrm{st}}`$ の定義（[D.Rst](Wset-ja.md#d-Rst)）の右辺を
書き下したものであるから、$`\rho`$ と $`R_{\mathrm{st}}`$ は定義により同一の関係である。

**第 3 段（適用）.** 第 2 段の前件は第 1 段で示した $`(\mathrm{cof})`$ そのものである。これを
与えると後件 $`\mathrm{WellFounded}(\rho)`$、すなわち「$`R_{\mathrm{st}}`$ は整礎である」を
得る。これは本定理の結論と同一の命題である。∎

<a id="t-wf_Rnf_holds"></a>
## 定理: 正規形上の順序の整礎性 (T.wf_Rnf_holds)

### 定理

$`R_{\mathrm{NF}}`$ は整礎である。

### 証明

**第 1 段（前件の調達）.** [T.wf_olt_ST_PS_holds](#t-wf_olt_ST_PS_holds) は前件を持たない
定理であり、その結論は「$`R_{\mathrm{st}}`$ は整礎である」（整礎
[D.WellFounded](Reduction-ja.md#d-WellFounded)）である。よってこれが成り立つ。これを
$`(\mathrm{h})`$ とおく。

```math
(\mathrm{h})\ \ \mathrm{WellFounded}(R_{\mathrm{st}})
```

**第 2 段（移送定理の形）.** [T.wf_Rnf_of_wf_PS](#t-wf_Rnf_of_wf_PS) の主張は次の形をしている。

```math
\mathrm{WellFounded}(R_{\mathrm{st}}) \ \longrightarrow\ \mathrm{WellFounded}(R_{\mathrm{NF}})
```

全称量化された変数はないので、具体化は不要である。

**第 3 段（適用）.** 第 2 段の前件は第 1 段の $`(\mathrm{h})`$ そのものである。これを与えると
後件 $`\mathrm{WellFounded}(R_{\mathrm{NF}})`$、すなわち「$`R_{\mathrm{NF}}`$ は整礎である」を
得る。これは本定理の結論と同一の命題である。∎

<a id="t-PSS_terminates_unconditional"></a>
## 定理: PSS の停止性 (T.PSS_terminates_unconditional)

### 定理

$`R_{\mathrm{PS}}`$ は整礎である。

（$`R_{\mathrm{PS}}`$ [D.stepRel](Reduction-ja.md#d-stepRel)）

### 証明

**第 1 段（前件の調達）.** [T.wf_Rnf_holds](#t-wf_Rnf_holds) は前件を持たない定理であり、
その結論は「$`R_{\mathrm{NF}}`$ は整礎である」である。よってこれが成り立つ。これを
$`(\mathrm{h})`$ とおく。

```math
(\mathrm{h})\ \ \mathrm{WellFounded}(R_{\mathrm{NF}})
```

**第 2 段（停止性定理の形）.** [T.step_terminates](Reduction-ja.md#t-step_terminates) の主張は
次の形をしている。

```math
\mathrm{WellFounded}(R_{\mathrm{NF}}) \ \longrightarrow\ \mathrm{WellFounded}(R_{\mathrm{PS}})
```

全称量化された変数はないので、具体化は不要である。

**第 3 段（適用）.** 第 2 段の前件は第 1 段の $`(\mathrm{h})`$ そのものである。これを与えると
後件 $`\mathrm{WellFounded}(R_{\mathrm{PS}})`$、すなわち「$`R_{\mathrm{PS}}`$ は整礎である」を
得る。これは本定理の結論と同一の命題である。∎

<a id="t-no_infinite_expansion_holds"></a>
## 定理: 無限展開列の非存在 (T.no_infinite_expansion_holds)

### 定理

次の 2 条件をみたす $`S : \mathbb{N} \to \mathrm{PairSeq}`$ は存在しない。

```math
\forall i \in \mathbb{N},\ S_i \in \mathrm{ST\_PS},
\qquad
\forall i \in \mathbb{N},\ S_i \Rightarrow S_{i+1} .
```

ここで $`S_i`$ は $`S`$ の $`i`$ における値である（$`M \Rightarrow N`$ [D.step](Pss-ja.md#d-step)）。

### 証明

**第 1 段（前件の調達）.** [T.wf_Rnf_holds](#t-wf_Rnf_holds) は前件を持たない定理であり、
その結論は「$`R_{\mathrm{NF}}`$ は整礎である」である。よってこれが成り立つ。これを
$`(\mathrm{h})`$ とおく。

```math
(\mathrm{h})\ \ \mathrm{WellFounded}(R_{\mathrm{NF}})
```

**第 2 段（非存在定理の形）.** [T.no_infinite_expansion](Reduction-ja.md#t-no_infinite_expansion)
の主張は次の形をしている。

```math
\begin{aligned}
&\mathrm{WellFounded}(R_{\mathrm{NF}}) \ \longrightarrow\ \cr
&\qquad \neg\ \exists S : \mathbb{N} \to \mathrm{PairSeq},\
  \bigl(\forall i \in \mathbb{N},\ S_i \in \mathrm{ST\_PS}\bigr)
  \ \wedge\ \bigl(\forall i \in \mathbb{N},\ S_i \Rightarrow S_{i+1}\bigr)
\end{aligned}
```

全称量化された変数はないので、具体化は不要である。

**第 3 段（適用）.** 第 2 段の前件は第 1 段の $`(\mathrm{h})`$ そのものである。これを与えると
後件が得られる。後件は本定理の結論と同一の命題であるから、上の 2 条件をみたす
$`S : \mathbb{N} \to \mathrm{PairSeq}`$ は存在しない。∎
