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

関係 $`R`$ に対する $`\mathrm{Acc}_R`$ の定義、その最小性（$`\mathrm{Acc}_R`$ の導出に関する帰納法）、
および $`R`$ が整礎であることの定義は、[T.step_terminates_cond](Reduction-ja.md#t-step_terminates_cond)
の定理文で与えたものをそのまま用いる。

このとき、任意の $`M \in \mathrm{PairSeq}`$ に対し、$`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ かつ
$`M \in \mathrm{ST\_PS}`$ ならば $`\mathrm{tr}\,M \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ である。

（$`R_{\mathrm{NF}}`$ [D.Rnf](Reduction-ja.md#d-Rnf)）

### 証明

$`M \in \mathrm{PairSeq}`$ と $`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ を取り、
$`\mathrm{Acc}_{R_{\mathrm{st}}}`$ の導出に関する帰納法を行う。帰納法の述語は

```math
\Phi(M_0) :\equiv M_0 \in \mathrm{ST\_PS} \to \mathrm{tr}\,M_0 \in \mathrm{Acc}_{R_{\mathrm{NF}}} .
```

**帰納段**：$`M_0 \in \mathrm{PairSeq}`$ を取り、帰納法の仮定

```math
\forall N \in \mathrm{PairSeq},\ N \mathbin{R_{\mathrm{st}}} M_0 \to \Phi(N)
```

を仮定する（規則のもう一方の前提
$`\forall N,\ N \mathbin{R_{\mathrm{st}}} M_0 \to N \in \mathrm{Acc}_{R_{\mathrm{st}}}`$
も同時に使えるが、以下では用いない）。$`M_0 \in \mathrm{ST\_PS}`$ を仮定して
$`\mathrm{tr}\,M_0 \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ を示す。$`\mathrm{Acc}`$ の規則により、

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

**(b) $`u \notin \mathrm{NF}`$ のとき。** $`\mathrm{Acc}`$ の規則により

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

[T.pss_cofinality_of_core](ArgDom-ja.md#t-pss_cofinality_of_core) は、命題
$`\mathrm{ArgDomCore}`$（[D.ArgDomCore](ArgDom-ja.md#d-ArgDomCore)）を仮定として、任意の $`M, N \in \mathrm{PairSeq}`$ について $`M \in \mathrm{ST\_PS}`$、
$`N \in \mathrm{ST\_PS}`$、$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ の 3 つから本定理の結論を導く。

その仮定 $`\mathrm{ArgDomCore}`$ は [T.argDomCore_holds](ArgDom-5-ja.md#t-argDomCore_holds) であり、
これは仮定を持たない。よって
[T.pss_cofinality_of_core](ArgDom-ja.md#t-pss_cofinality_of_core) に
[T.argDomCore_holds](ArgDom-5-ja.md#t-argDomCore_holds) と本定理の 3 つの仮定を与えれば、
求める $`n`$ が得られる。∎

<a id="t-wf_olt_ST_PS_holds"></a>
## 定理: 標準形上の順序の整礎性 (T.wf_olt_ST_PS_holds)

### 定理

$`R_{\mathrm{st}}`$ は整礎である。

### 証明

[T.wf_olt_ST_PS_of_cofinality](Wset-4-ja.md#t-wf_olt_ST_PS_of_cofinality) は、仮定

```math
\forall M, N \in \mathrm{PairSeq},\
  \bigl(M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,N \prec \mathrm{tr}\,M\bigr)
  \to \exists n,\ 1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])
```

から $`R_{\mathrm{st}}`$ の整礎性を導く。この仮定は
[T.pss_cofinality_holds](#t-pss_cofinality_holds) を $`M`$ と $`N`$ について全称量化したもの
そのものである。よってこれを
[T.wf_olt_ST_PS_of_cofinality](Wset-4-ja.md#t-wf_olt_ST_PS_of_cofinality) に与えればよい。∎

<a id="t-wf_Rnf_holds"></a>
## 定理: 正規形上の順序の整礎性 (T.wf_Rnf_holds)

### 定理

$`R_{\mathrm{NF}}`$ は整礎である。

### 証明

[T.wf_Rnf_of_wf_PS](#t-wf_Rnf_of_wf_PS) は $`R_{\mathrm{st}}`$ の整礎性を仮定として
$`R_{\mathrm{NF}}`$ の整礎性を導く。その仮定は [T.wf_olt_ST_PS_holds](#t-wf_olt_ST_PS_holds)
であり、これは仮定を持たない。よって
[T.wf_olt_ST_PS_holds](#t-wf_olt_ST_PS_holds) を
[T.wf_Rnf_of_wf_PS](#t-wf_Rnf_of_wf_PS) に与えればよい。∎

<a id="t-PSS_terminates_unconditional"></a>
## 定理: PSS の停止性 (T.PSS_terminates_unconditional)

### 定理

$`R_{\mathrm{PS}}`$ は整礎である。

（$`R_{\mathrm{PS}}`$ [D.stepRel](Reduction-ja.md#d-stepRel)）

### 証明

[T.step_terminates](Reduction-ja.md#t-step_terminates) は $`R_{\mathrm{NF}}`$ の整礎性を仮定として
$`R_{\mathrm{PS}}`$ の整礎性を導く。その仮定は [T.wf_Rnf_holds](#t-wf_Rnf_holds) であり、
これは仮定を持たない。よって [T.wf_Rnf_holds](#t-wf_Rnf_holds) を
[T.step_terminates](Reduction-ja.md#t-step_terminates) に与えればよい。∎

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

[T.no_infinite_expansion](Reduction-ja.md#t-no_infinite_expansion) は $`R_{\mathrm{NF}}`$ の整礎性を
仮定として、上の 2 条件をみたす $`S`$ が存在しないことを導く。その仮定は
[T.wf_Rnf_holds](#t-wf_Rnf_holds) であり、これは仮定を持たない。よって
[T.wf_Rnf_holds](#t-wf_Rnf_holds) を
[T.no_infinite_expansion](Reduction-ja.md#t-no_infinite_expansion) に与えればよい。∎
