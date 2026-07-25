[← 目次](README.md)

# OrdinalFree — ペア列側の整礎性から項側の関係 $`R_{\mathrm{NF}}`$ への転送

ペア列上の関係「$`a`$ と $`b`$ がともに標準形（[(D.ST_PS)](Def.md#d-ST_PS)）であって
翻訳（[(D.translate)](Mechanized.md#d-translate)）が $`\mathrm{tr}\,a \prec \mathrm{tr}\,b`$
（[(D.olt)](Mechanized.md#d-olt)）をみたす」が整礎であることを仮定して、
項側の関係 [(D.Rnf)](Proofs.md#d-Rnf)（$`\prec`$ を [(D.NF)](Proofs.md#d-NF) に制限したもの）の整礎性を導く。
第 1 の定理は 1 つのペア列 $`M`$ の到達可能性を
項 $`\mathrm{tr}\,M`$ の到達可能性へ移し、第 2 の定理はそれを用いて
[(D.Three)](Mechanized.md#d-Three) のすべての項の到達可能性を示す。新しい定義は導入しない。

## 記法

本章で用いる Lean 名と本文の記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `PairSeq` | $`\mathrm{PairSeq}`$ | ペア列の型（[(D.PairSeq)](Def.md#d-PairSeq)） |
| `Three` | $`\mathrm{Three}`$ | 三分岐記法の項の型（[(D.Three)](Mechanized.md#d-Three)） |
| `translate M` | $`\mathrm{tr}\,M`$ | 翻訳（[(D.translate)](Mechanized.md#d-translate)） |
| `x <o y` | $`x \prec y`$ | 添字優先辞書式順序（[(D.olt)](Mechanized.md#d-olt)） |
| `ST_PS M` | $`M \in \mathrm{ST\_PS}`$ | $`M`$ は標準形（[(D.ST_PS)](Def.md#d-ST_PS)） |
| `NF` | $`\mathrm{NF}`$ | $`\mathrm{tr}`$ による $`\mathrm{ST\_PS}`$ の像（[(D.NF)](Proofs.md#d-NF)） |
| `Rnf v u` | $`R_{\mathrm{NF}}(v,u)`$ | $`\mathrm{NF}`$ に制限した $`\prec`$（[(D.Rnf)](Proofs.md#d-Rnf)） |
| `fun a b : PairSeq => ST_PS a ∧ ST_PS b ∧ translate a <o translate b` | $`R_{\mathrm{PS}}(a,b)`$ | 下の略記 |
| `Acc r x` | $`\mathrm{Acc}(r,x)`$ | $`x`$ は関係 $`r`$ について到達可能 |
| `WellFounded r` | $`\mathrm{WF}(r)`$ | 関係 $`r`$ は整礎 |

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

**引数の順序.** どちらの関係も第 1 引数が「下」である。すなわち $`R_{\mathrm{NF}}(v,u)`$ は
「$`v`$ は $`u`$ より下」を表す。

**到達可能性と整礎性.** $`\mathrm{Acc}`$ は次の 1 つの導入規則で生成される最小の述語である。

```math
\frac{\ \forall y,\ r\,y\,x \to \mathrm{Acc}(r,y)\ }{\ \mathrm{Acc}(r,x)\ }\ \text{(Acc.intro)}
```

したがって $`\mathrm{Acc}`$ について次の 2 つが使える。

1. （構成）$`\forall y,\ \bigl(r\,y\,x \to \mathrm{Acc}(r,y)\bigr)`$ を示せば $`\mathrm{Acc}(r,x)`$ が得られる。
   特に $`x`$ が $`r`$-前者をもたない（$`\forall y,\ \neg\, r\,y\,x`$）ならば前提は空虚に真であるから
   $`\mathrm{Acc}(r,x)`$ である。
2. （$`\mathrm{Acc}`$ の導出に関する帰納法、Lean の `Acc.rec`）述語 $`C`$ が
   ```math
   \forall x,\ \Bigl(\bigl(\forall y,\ r\,y\,x \to \mathrm{Acc}(r,y)\bigr) \ \wedge\ \bigl(\forall y,\ r\,y\,x \to C(y)\bigr)\Bigr) \to C(x)
   ```
   をみたすならば、$`\forall x,\ \mathrm{Acc}(r,x) \to C(x)`$。
   導入規則が 1 つしかないから帰納段も 1 つであり、基底段に相当するのは
   $`x`$ が $`r`$-前者をもたない場合、すなわち帰納法の仮定 $`\forall y,\ r\,y\,x \to C(y)`$ が
   空虚に真である場合である。

$`\mathrm{WF}`$ も 1 つの導入規則で生成される。

```math
\frac{\ \forall a,\ \mathrm{Acc}(r,a)\ }{\ \mathrm{WF}(r)\ }\ \text{(WellFounded.intro)}
```

その逆向きの読み（Lean の `WellFounded.apply`）は
$`\mathrm{WF}(r) \to \forall a,\ \mathrm{Acc}(r,a)`$ である。

## 転送

<a id="t-acc_Rnf_of_acc_PS"></a>
### 定理 到達可能性の転送 (T.acc_Rnf_of_acc_PS)

**主張** 任意の $`M \in \mathrm{PairSeq}`$ について

```math
\mathrm{Acc}(R_{\mathrm{PS}}, M) \ \wedge\ M \in \mathrm{ST\_PS}
\ \Longrightarrow\ \mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,M).
```

**証明** $`\mathrm{Acc}(R_{\mathrm{PS}}, M)`$ の導出に関する帰納法を行う。帰納法の述語を

```math
\Phi(M) \ :\equiv\ \bigl(M \in \mathrm{ST\_PS} \to \mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,M)\bigr)
```

とする（$`M`$ は $`\mathrm{Acc}(R_{\mathrm{PS}},\cdot)`$ が成り立つペア列を走る）。
上の $`\mathrm{Acc}`$ の帰納法原理により、$`\forall M,\ \mathrm{Acc}(R_{\mathrm{PS}},M) \to \Phi(M)`$ を示すには
次の 1 つの段を示せばよい。

**帰納段.** $`M_0 \in \mathrm{PairSeq}`$ が与えられ、

- $`\forall N,\ R_{\mathrm{PS}}(N, M_0) \to \mathrm{Acc}(R_{\mathrm{PS}}, N)`$（本証明では使わない）、
- 帰納法の仮定
  ```math
  \mathrm{IH} \ :\equiv\ \forall N,\ R_{\mathrm{PS}}(N, M_0) \to \bigl(N \in \mathrm{ST\_PS} \to \mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,N)\bigr)
  ```

が成り立つとき、$`\Phi(M_0)`$ を示す。

$`M_0 \in \mathrm{ST\_PS}`$ を仮定する。示すべきは $`\mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,M_0)`$ である。
$`\mathrm{Acc}`$ の構成規則（上の 1）により、

```math
\forall v \in \mathrm{Three},\ R_{\mathrm{NF}}(v, \mathrm{tr}\,M_0) \to \mathrm{Acc}(R_{\mathrm{NF}}, v)
```

を示せば足りる。そこで $`v \in \mathrm{Three}`$ を取り $`R_{\mathrm{NF}}(v, \mathrm{tr}\,M_0)`$ を仮定する。
[(D.Rnf)](Proofs.md#d-Rnf) よりこれは 3 つの連言

```math
v \prec \mathrm{tr}\,M_0, \qquad \mathrm{tr}\,M_0 \in \mathrm{NF}, \qquad v \in \mathrm{NF}
```

である。第 2 の連言は以下で用いない。第 3 の連言 $`v \in \mathrm{NF}`$ に
[(D.NF)](Proofs.md#d-NF) を適用すると、ある $`N \in \mathrm{PairSeq}`$ が存在して

```math
N \in \mathrm{ST\_PS} \qquad\text{かつ}\qquad \mathrm{tr}\,N = v
```

が成り立つ。$`v`$ を $`\mathrm{tr}\,N`$ で置き換えると、第 1 の連言は
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M_0`$ となり、示すべき目標は $`\mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,N)`$ となる。

ここで $`R_{\mathrm{PS}}(N, M_0)`$ が成り立つ。実際、その定義の 3 つの連言は順に

1. $`N \in \mathrm{ST\_PS}`$ — 上で得た。
2. $`M_0 \in \mathrm{ST\_PS}`$ — 帰納段の冒頭で仮定した。
3. $`\mathrm{tr}\,N \prec \mathrm{tr}\,M_0`$ — 上で得た。

である。よって帰納法の仮定 $`\mathrm{IH}`$ を $`N`$ とこの $`R_{\mathrm{PS}}(N,M_0)`$ に適用し、
さらに $`N \in \mathrm{ST\_PS}`$ を渡すと $`\mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,N)`$ が得られる。
これが示すべきものであった。

（基底段に相当する場合、すなわち $`M_0`$ が $`R_{\mathrm{PS}}`$-前者をもたない場合も、この同じ論法に含まれている。
その場合、上で構成した $`R_{\mathrm{PS}}(N, M_0)`$ は偽であるから、そもそも
$`R_{\mathrm{NF}}(v, \mathrm{tr}\,M_0)`$ をみたす $`v`$ が存在せず、$`\mathrm{Acc}`$ の構成規則の前提は空虚に真である。）∎

<a id="t-wf_Rnf_of_wf_PS"></a>
### 定理 整礎性の転送 (T.wf_Rnf_of_wf_PS)

**主張**

```math
\mathrm{WF}(R_{\mathrm{PS}}) \ \Longrightarrow\ \mathrm{WF}(R_{\mathrm{NF}}).
```

すなわち、ペア列上の関係「$`a`$ と $`b`$ がともに標準形であって $`\mathrm{tr}\,a \prec \mathrm{tr}\,b`$」が整礎ならば、
[(D.Rnf)](Proofs.md#d-Rnf) は整礎である。

**証明** $`\mathrm{WF}(R_{\mathrm{PS}})`$ を仮定する。$`\mathrm{WF}`$ の導入規則により、

```math
\forall u \in \mathrm{Three},\ \mathrm{Acc}(R_{\mathrm{NF}}, u)
```

を示せばよい。$`u \in \mathrm{Three}`$ を固定し、排中律により $`u \in \mathrm{NF}`$ か $`u \notin \mathrm{NF}`$ かで場合分けする。

**場合 (i): $`u \in \mathrm{NF}`$.**
[(D.NF)](Proofs.md#d-NF) より、ある $`M \in \mathrm{PairSeq}`$ が存在して
$`M \in \mathrm{ST\_PS}`$ かつ $`\mathrm{tr}\,M = u`$ である。$`u`$ を $`\mathrm{tr}\,M`$ で置き換えると、
示すべきは $`\mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,M)`$ である。
仮定 $`\mathrm{WF}(R_{\mathrm{PS}})`$ を $`M`$ に適用して（`WellFounded.apply`）
$`\mathrm{Acc}(R_{\mathrm{PS}}, M)`$ を得る。これと $`M \in \mathrm{ST\_PS}`$ に
[(T.acc_Rnf_of_acc_PS)](#t-acc_Rnf_of_acc_PS) を適用すると
$`\mathrm{Acc}(R_{\mathrm{NF}}, \mathrm{tr}\,M)`$ が得られる。

**場合 (ii): $`u \notin \mathrm{NF}`$.**
$`\mathrm{Acc}`$ の構成規則により、

```math
\forall v \in \mathrm{Three},\ R_{\mathrm{NF}}(v, u) \to \mathrm{Acc}(R_{\mathrm{NF}}, v)
```

を示せばよい。$`v`$ を取り $`R_{\mathrm{NF}}(v,u)`$ を仮定する。
[(D.Rnf)](Proofs.md#d-Rnf) の 3 つの連言のうち第 2 のものは $`u \in \mathrm{NF}`$ である。
これは場合 (ii) の仮定 $`u \notin \mathrm{NF}`$ と矛盾する。矛盾からは任意の命題が従うので、
特に $`\mathrm{Acc}(R_{\mathrm{NF}}, v)`$ が従う。
（言い換えると、$`u \notin \mathrm{NF}`$ なる $`u`$ は $`R_{\mathrm{NF}}`$-前者を 1 つももたないから、
$`\mathrm{Acc}`$ の構成規則の前提が空虚に真である。）

以上 2 つの場合で $`\mathrm{Acc}(R_{\mathrm{NF}}, u)`$ が示されたから $`\mathrm{WF}(R_{\mathrm{NF}})`$ である。∎

**注（用いた古典論理）** 本章の 2 つの証明で古典論理を用いる箇所は、
[(T.wf_Rnf_of_wf_PS)](#t-wf_Rnf_of_wf_PS) の場合分け $`u \in \mathrm{NF} \vee u \notin \mathrm{NF}`$ のみである。
