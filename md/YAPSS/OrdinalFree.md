[← 目次](README.md)

# OrdinalFree — ペア列側の整礎性から項側の関係 $R_{\mathrm{NF}}$ への転送

ペア列上の関係「$a$ と $b$ がともに標準形（[(D.ST_PS)](Def.md#d-ST_PS)）であって
翻訳（[(D.translate)](Mechanized.md#d-translate)）が $\mathrm{tr}\,a \prec \mathrm{tr}\,b$
（[(D.olt)](Mechanized.md#d-olt)）をみたす」が整礎であることを仮定して、
項側の関係 [(D.Rnf)](Proofs.md#d-Rnf)（$\prec$ を [(D.NF)](Proofs.md#d-NF) に制限したもの）の整礎性を導く。
本章の宣言は 2 個で、いずれも定理である。第 1 の定理は 1 つのペア列 $M$ の到達可能性を
項 $\mathrm{tr}\,M$ の到達可能性へ移し、第 2 の定理はそれを用いて
[(D.Three)](Mechanized.md#d-Three) のすべての項の到達可能性を示す。新しい定義は導入しない。

## 記法

本章で用いる Lean 名と本文の記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `PairSeq` | $\mathrm{PairSeq}$ | ペア列の型（[(D.PairSeq)](Def.md#d-PairSeq)） |
| `Three` | $\mathrm{Three}$ | 三分岐記法の項の型（[(D.Three)](Mechanized.md#d-Three)） |
| `translate M` | $\mathrm{tr}\,M$ | 翻訳（[(D.translate)](Mechanized.md#d-translate)） |
| `x <o y` | $x \prec y$ | 添字優先辞書式順序（[(D.olt)](Mechanized.md#d-olt)） |
| `ST_PS M` | $M \in \mathrm{ST\_PS}$ | $M$ は標準形（[(D.ST_PS)](Def.md#d-ST_PS)） |
| `NF` | $\mathrm{NF}$ | $\mathrm{tr}$ による $\mathrm{ST\_PS}$ の像（[(D.NF)](Proofs.md#d-NF)） |
| `Rnf v u` | $R_{\mathrm{NF}}(v,u)$ | $\mathrm{NF}$ に制限した $\prec$（[(D.Rnf)](Proofs.md#d-Rnf)） |
| `fun a b : PairSeq => ST_PS a ∧ ST_PS b ∧ translate a <o translate b` | $R_{\mathrm{PS}}(a,b)$ | 下の略記 |
| `Acc r x` | $\mathrm{Acc}(r,x)$ | $x$ は関係 $r$ について到達可能 |
| `WellFounded r` | $\mathrm{WF}(r)$ | 関係 $r$ は整礎 |

以下、本章を通じて 2 つの関係を次の略記で書く。

```math
R_{\mathrm{PS}}(a,b) \ :\iff\ a \in \mathrm{ST\_PS} \ \wedge\ b \in \mathrm{ST\_PS} \ \wedge\ \mathrm{tr}\,a \prec \mathrm{tr}\,b
\qquad (a,b \in \mathrm{PairSeq}),
```

```math
R_{\mathrm{NF}}(v,u) \ :\iff\ v \prec u \ \wedge\ u \in \mathrm{NF} \ \wedge\ v \in \mathrm{NF}
\qquad (u,v \in \mathrm{Three}).
```

第 2 式は [(D.Rnf)](Proofs.md#d-Rnf) の定義そのものである。
また [(D.NF)](Proofs.md#d-NF) は

```math
\mathrm{NF} = \{\,t \in \mathrm{Three} \mid \exists M \in \mathrm{PairSeq},\ M \in \mathrm{ST\_PS} \ \wedge\ \mathrm{tr}\,M = t \,\}
```

である。

**引数の順序.** どちらの関係も第 1 引数が「下」である。すなわち $R_{\mathrm{NF}}(v,u)$ は
「$v$ は $u$ より下」を表し、Isabelle 側の $(v,u) \in \mathrm{Rnf}$ に対応する。

**到達可能性と整礎性.** $\mathrm{Acc}$ は次の 1 つの導入規則で生成される最小の述語である。

```math
\frac{\ \forall y,\ r\,y\,x \to \mathrm{Acc}(r,y)\ }{\ \mathrm{Acc}(r,x)\ }\ \text{(Acc.intro)}
```

したがって $\mathrm{Acc}$ について次の 2 つが使える。

1. （構成）$\forall y,\ \bigl(r\,y\,x \to \mathrm{Acc}(r,y)\bigr)$ を示せば $\mathrm{Acc}(r,x)$ が得られる。
   特に $x$ が $r$-前者をもたない（$\forall y,\ \neg\, r\,y\,x$）ならば前提は空虚に真であるから
   $\mathrm{Acc}(r,x)$ である。
2. （$\mathrm{Acc}$ の導出に関する帰納法、Lean の `Acc.rec`）述語 $C$ が
   ```math
   \forall x,\ \Bigl(\bigl(\forall y,\ r\,y\,x \to \mathrm{Acc}(r,y)\bigr) \ \wedge\ \bigl(\forall y,\ r\,y\,x \to C(y)\bigr)\Bigr) \to C(x)
   ```
   をみたすならば、$\forall x,\ \mathrm{Acc}(r,x) \to C(x)$。
   導入規則が 1 つしかないから帰納段も 1 つであり、基底段に相当するのは
   $x$ が $r$-前者をもたない場合、すなわち帰納法の仮定 $\forall y,\ r\,y\,x \to C(y)$ が
   空虚に真である場合である。

$\mathrm{WF}$ も 1 つの導入規則で生成される。

```math
\frac{\ \forall a,\ \mathrm{Acc}(r,a)\ }{\ \mathrm{WF}(r)\ }\ \text{(WellFounded.intro)}
```

その逆向きの読み（Lean の `WellFounded.apply`）は
$\mathrm{WF}(r) \to \forall a,\ \mathrm{Acc}(r,a)$ である。

## 転送

<a id="t-acc_Rnf_of_acc_PS"></a>
### 定理 到達可能性の転送 (T.acc_Rnf_of_acc_PS)

**主張** 任意の $M \in \mathrm{PairSeq}$ について

```math
\mathrm{Acc}(R_{\mathrm{PS}}, M) \ \wedge\ M \in \mathrm{ST\_PS}
\ \Longrightarrow\ \mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,M).
```

**証明** $\mathrm{Acc}(R_{\mathrm{PS}}, M)$ の導出に関する帰納法を行う。帰納法の述語を

```math
\Phi(M) \ :\equiv\ \bigl(M \in \mathrm{ST\_PS} \to \mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,M)\bigr)
```

とする（$M$ は $\mathrm{Acc}(R_{\mathrm{PS}},\cdot)$ が成り立つペア列を走る）。
上の $\mathrm{Acc}$ の帰納法原理により、$\forall M,\ \mathrm{Acc}(R_{\mathrm{PS}},M) \to \Phi(M)$ を示すには
次の 1 つの段を示せばよい。

**帰納段.** $M_0 \in \mathrm{PairSeq}$ が与えられ、

- $\forall N,\ R_{\mathrm{PS}}(N, M_0) \to \mathrm{Acc}(R_{\mathrm{PS}}, N)$（本証明では使わない）、
- 帰納法の仮定
  ```math
  \mathrm{IH} \ :\equiv\ \forall N,\ R_{\mathrm{PS}}(N, M_0) \to \bigl(N \in \mathrm{ST\_PS} \to \mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,N)\bigr)
  ```

が成り立つとき、$\Phi(M_0)$ を示す。

$M_0 \in \mathrm{ST\_PS}$ を仮定する。示すべきは $\mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,M_0)$ である。
$\mathrm{Acc}$ の構成規則（上の 1）により、

```math
\forall v \in \mathrm{Three},\ R_{\mathrm{NF}}(v, \mathrm{tr}\,M_0) \to \mathrm{Acc}(R_{\mathrm{NF}}, v)
```

を示せば足りる。そこで $v \in \mathrm{Three}$ を取り $R_{\mathrm{NF}}(v, \mathrm{tr}\,M_0)$ を仮定する。
[(D.Rnf)](Proofs.md#d-Rnf) よりこれは 3 つの連言

```math
v \prec \mathrm{tr}\,M_0, \qquad \mathrm{tr}\,M_0 \in \mathrm{NF}, \qquad v \in \mathrm{NF}
```

である。第 2 の連言は以下で用いない。第 3 の連言 $v \in \mathrm{NF}$ に
[(D.NF)](Proofs.md#d-NF) を適用すると、ある $N \in \mathrm{PairSeq}$ が存在して

```math
N \in \mathrm{ST\_PS} \qquad\text{かつ}\qquad \mathrm{tr}\,N = v
```

が成り立つ。$v$ を $\mathrm{tr}\,N$ で置き換えると、第 1 の連言は
$\mathrm{tr}\,N \prec \mathrm{tr}\,M_0$ となり、示すべき目標は $\mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,N)$ となる。

ここで $R_{\mathrm{PS}}(N, M_0)$ が成り立つ。実際、その定義の 3 つの連言は順に

1. $N \in \mathrm{ST\_PS}$ — 上で得た。
2. $M_0 \in \mathrm{ST\_PS}$ — 帰納段の冒頭で仮定した。
3. $\mathrm{tr}\,N \prec \mathrm{tr}\,M_0$ — 上で得た。

である。よって帰納法の仮定 $\mathrm{IH}$ を $N$ とこの $R_{\mathrm{PS}}(N,M_0)$ に適用し、
さらに $N \in \mathrm{ST\_PS}$ を渡すと $\mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,N)$ が得られる。
これが示すべきものであった。

（基底段に相当する場合、すなわち $M_0$ が $R_{\mathrm{PS}}$-前者をもたない場合も、この同じ論法に含まれている。
その場合、上で構成した $R_{\mathrm{PS}}(N, M_0)$ は偽であるから、そもそも
$R_{\mathrm{NF}}(v, \mathrm{tr}\,M_0)$ をみたす $v$ が存在せず、$\mathrm{Acc}$ の構成規則の前提は空虚に真である。）∎

<a id="t-wf_Rnf_of_wf_PS"></a>
### 定理 整礎性の転送 (T.wf_Rnf_of_wf_PS)

**主張**

```math
\mathrm{WF}(R_{\mathrm{PS}}) \ \Longrightarrow\ \mathrm{WF}(R_{\mathrm{NF}}).
```

すなわち、ペア列上の関係「$a$ と $b$ がともに標準形であって $\mathrm{tr}\,a \prec \mathrm{tr}\,b$」が整礎ならば、
[(D.Rnf)](Proofs.md#d-Rnf) は整礎である。

**証明** $\mathrm{WF}(R_{\mathrm{PS}})$ を仮定する。$\mathrm{WF}$ の導入規則により、

```math
\forall u \in \mathrm{Three},\ \mathrm{Acc}(R_{\mathrm{NF}}, u)
```

を示せばよい。$u \in \mathrm{Three}$ を固定し、排中律により $u \in \mathrm{NF}$ か $u \notin \mathrm{NF}$ かで場合分けする。

**場合 (i): $u \in \mathrm{NF}$.**
[(D.NF)](Proofs.md#d-NF) より、ある $M \in \mathrm{PairSeq}$ が存在して
$M \in \mathrm{ST\_PS}$ かつ $\mathrm{tr}\,M = u$ である。$u$ を $\mathrm{tr}\,M$ で置き換えると、
示すべきは $\mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,M)$ である。
仮定 $\mathrm{WF}(R_{\mathrm{PS}})$ を $M$ に適用して（`WellFounded.apply`）
$\mathrm{Acc}(R_{\mathrm{PS}}, M)$ を得る。これと $M \in \mathrm{ST\_PS}$ に
[(T.acc_Rnf_of_acc_PS)](#t-acc_Rnf_of_acc_PS) を適用すると
$\mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,M)$ が得られる。

**場合 (ii): $u \notin \mathrm{NF}$.**
$\mathrm{Acc}$ の構成規則により、

```math
\forall v \in \mathrm{Three},\ R_{\mathrm{NF}}(v, u) \to \mathrm{Acc}(R_{\mathrm{NF}}, v)
```

を示せばよい。$v$ を取り $R_{\mathrm{NF}}(v,u)$ を仮定する。
[(D.Rnf)](Proofs.md#d-Rnf) の 3 つの連言のうち第 2 のものは $u \in \mathrm{NF}$ である。
これは場合 (ii) の仮定 $u \notin \mathrm{NF}$ と矛盾する。矛盾からは任意の命題が従うので、
特に $\mathrm{Acc}(R_{\mathrm{NF}}, v)$ が従う。
（言い換えると、$u \notin \mathrm{NF}$ なる $u$ は $R_{\mathrm{NF}}$-前者を 1 つももたないから、
$\mathrm{Acc}$ の構成規則の前提が空虚に真である。）

以上 2 つの場合で $\mathrm{Acc}(R_{\mathrm{NF}}, u)$ が示されたから $\mathrm{WF}(R_{\mathrm{NF}})$ である。∎

**注（用いた古典論理）** 本章の 2 つの証明で古典論理を用いる箇所は、
[(T.wf_Rnf_of_wf_PS)](#t-wf_Rnf_of_wf_PS) の場合分け $u \in \mathrm{NF} \vee u \notin \mathrm{NF}$ のみである
（Lean の `by_cases`）。Lean ソースは末尾で
`#print axioms acc_Rnf_of_acc_PS` と `#print axioms wf_Rnf_of_wf_PS` を実行し、
両定理が依存する公理を機械的に出力する。

## 残っている債務（Lean ソースの `## What is left` 節）

Lean ソース `lean/YAPSS/OrdinalFree.lean` の同名の節は、その節が書かれた時点で
未証明であった唯一の命題を記録している。それは `AscArgDomExplicit` という名の命題であり、
[(D.shiftr0)](Wf.md#d-shiftr0) / [(D.copies)](Wf.md#d-copies) / `List.takeWhile` から作られる
2 つの明示的なペア列の $\preceq_{\mathrm{lex}}$（[(D.sle)](Cofinality.md#d-sle)）比較であって、
順序数・$\psi$・$\Omega$・順序数評価写像 [(D.oV)](Otembed.md#d-oV)・および $\prec$ の
いずれも含まない、という性質をもつ。

現在の Lean ソースには `AscArgDomExplicit` という名前の**宣言は存在しない**
（この名前が現れるのは `lean/YAPSS/OrdinalFree.lean` と `lean/YAPSS/AscArg.lean` の
コメント中のみである）。対応する内容は仮定なしの定理
[(T.argDomCore_holds)](AscArg.md#t-argDomCore_holds) として証明されている。
したがって本章の 2 定理を含む次の連鎖には、未証明の仮定は残っていない。

1. [(T.argDomCore_holds)](AscArg.md#t-argDomCore_holds)（[(D.ArgDomCore)](AscArg.md#d-ArgDomCore) の証明）
2. [(T.pss_cofinality_of_core)](AscArg.md#t-pss_cofinality_of_core) により
   [(T.pss_cofinality_holds)](Final.md#t-pss_cofinality_holds)（PSS の Bachmann 共終性）
3. [(T.wf_olt_ST_PS_of_cofinality)](Wset.md#t-wf_olt_ST_PS_of_cofinality) により
   [(T.wf_olt_ST_PS_holds)](Final.md#t-wf_olt_ST_PS_holds)、すなわち $\mathrm{WF}(R_{\mathrm{PS}})$
4. [(T.wf_Rnf_of_wf_PS)](#t-wf_Rnf_of_wf_PS)（本章）により
   [(T.wf_Rnf_holds)](Final.md#t-wf_Rnf_holds)、すなわち $\mathrm{WF}(R_{\mathrm{NF}})$
5. [(T.step_terminates)](Proofs.md#t-step_terminates) により
   [(T.PSS_terminates_unconditional)](Final.md#t-PSS_terminates_unconditional)、
   すなわち [(D.stepRel)](Proofs.md#d-stepRel) の整礎性

である。この合成を実際に行うのは [`Final.md`](Final.md) である。

なお Lean ソースの冒頭コメントは、この経路が順序数評価写像 `oV`、Buchholz の
[(D.wf3)](Otembed.md#d-wf3) 埋め込み、および係数優越の事実（[(D.Gterm)](Otembed.md#d-Gterm) を用いる形の命題。
コメント中で `H0clause` と呼ばれているものは、現在の Lean ソースには宣言として存在しない）
のいずれも用いず、
Bachmann 共終性（[`Cofinality.md`](Cofinality.md), [`AscArg.md`](AscArg.md)）と
反復帰納的集合 $W_u$（[`Wset.md`](Wset.md)）でこれらを置き換えたものであることを記録している。
