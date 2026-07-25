[← 目次](README.md)

# Nrmstep — 射影 $`\mathrm{proj}`$ の一段定理、`ins` の単調性、列側の不変量 $`\mathrm{r1ok}`$ / $`\mathrm{z0ok}`$

本章は 3 つの独立な内容を含む。
第 1 に、臨界項の上界 $`\mathrm{maxo}`$ と射影 $`\mathrm{proj}`$ の基本性質（増大性・一段定理・
発火述語 $`\mathrm{fire}`$）、および和挿入 $`\mathrm{ins}`$ の無条件な狭義単調性を確立する。
第 2 に、列 $`M`$ の末尾に 1 列を付加したとき正規化像 $`\mathrm{nrm}(\mathrm{tr}\,M)`$ が狭義増加するための
条件束 $`\mathrm{snocok}`$ と、その主帰納法 [(T.nrm_snoc_seg)](#t-nrm_snoc_seg) を与える。
第 3 に、標準形 $`\mathrm{ST\_PS}`$ の列が満たす 2 つの位置的不変量
$`\mathrm{r1ok}`$（[(T.r1ok_ST_PS)](#t-r1ok_ST_PS)）と $`\mathrm{z0ok}`$（[(T.z0ok_ST_PS)](#t-z0ok_ST_PS)）を
展開 $`M[n]`$ の全分岐について証明し、その帰結として
「$`\mathrm{ST\_PS}`$ 型の列の非零な最終列には親が一意に存在する」
（[(T.hp_last)](#t-hp_last)）を得る。

本章は 107 個の宣言をもつ。Lean 側のファイルは、形式化されなかった経路についての
節見出しコメントを多数含む。宣言を伴わない節見出しは
[「宣言を含まない節見出し」](#no-decl-sections)にまとめて列挙する。

## 記法

この章で導入する Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `pfire u b` | $`\mathrm{fire}_u(b)`$ | $`b`$ が水準 $`u`$ で発火する |
| `(Glist u b).filter (fun g => ¬ olt g b)` | $`\mathrm{Bad}_u(b)`$ | 水準 $`u`$ の違反者リスト |
| `maxo (Bad).headI (Bad).tail` | $`\mathrm{mx}_u(b)`$ | 違反者リストの $`\mathrm{maxo}`$ |
| `lext`, `lflip`, `einc`, `eflip` | 同名 | 1 箇所増加の 4 関係 |
| `snocok C q` | $`\mathrm{snocok}(C,q)`$ | 末尾付加の条件束 |
| `maxr1 S` | $`\mathrm{maxr1}\,S`$ | 列 $`S`$ の行 1 の最大値 |
| `r1ok M` | $`\mathrm{r1ok}(M)`$ | 行 1 の登攀規律 |
| `copyExp G B d0 n` | $`\mathrm{cE}(G,B,d_0,n)`$ | コピー展開の形 |
| `hdarg t` | $`\mathrm{hdarg}\,t`$ | 先頭引数 |
| `noabsorb a b t` | $`\mathrm{noabsorb}(a,b,t)`$ | 吸収が起きない条件 |
| `descok t` | $`\mathrm{descok}(t)`$ | 連続添字降下述語 |
| `mvstep b` | $`\mathrm{mv}(b)`$ | 射影の 1 段 |
| `Rdesc x y` | $`\mathrm{Rdesc}(x,y)`$ | 降下対関係 |
| `SubBlock M K` | $`\mathrm{SubBlock}(M,K)`$ | 部分ブロック関係 |
| `repB B n` | $`\mathrm{repB}(B,n)`$ | $`B`$ の $`n`$ 回反復 |
| `z0ok M` | $`\mathrm{z0ok}(M)`$ | 水準 0 の列は $`(0,0)`$ |
| `sclimb M` | $`\mathrm{sclimb}(M)`$ | 単一登攀規律 |
| `predGuard N` | $`\mathrm{predGuard}(N)`$ | $`\mathrm{oper}`$ が切り詰める条件 |
| `predImages M N` | $`\mathrm{predImages}(M,N)`$ | 条件つき切り詰めの反復像 |

他章で定義済みの記号については、[`Mechanized.md`](Mechanized.md) と同じ記法を用いる。

| Lean | 本文 | 意味 |
|---|---|---|
| `M.length` | $`\lvert M\rvert`$ | 列の長さ |
| `p.1`, `p.2` | $`\pi_0 p`$, $`\pi_1 p`$ | 対の第 0・第 1 成分 |
| `M.getD j (0,0)` | $`M\langle j\rangle`$ | 第 $`j`$ 対（範囲外なら $`(0,0)`$） |
| `entry M i j` | $`M_{i,j}`$ | 第 $`j`$ 対の第 $`i`$ 成分 |
| `M⟦n⟧` | $`M[n]`$ | 展開（コピー数 $`n`$） |
| `x <o y`, `x ≤o y` | $`x\prec y`$, $`x\preceq y`$ | 添字優先辞書式順序とその広義形 |
| `translate M` | $`\mathrm{tr}\,M`$ | ペア列の翻訳 |
| `tsize t` | $`\lVert t\rVert`$ | 項の構造的サイズ |
| `xs ++ ys`, `x :: xs` | $`xs \mathbin{+\!\!+} ys`$, $`x\mathbin{::}xs`$ | 連結・先頭付加 |
| `L.take j`, `L.dropLast` | $`\mathrm{take}\,j\,L`$, $`\mathrm{dropLast}\,L`$ | 前 $`j`$ 個、末尾 1 個を除いた列 |
| `L.headI`, `L.tail` | $`\mathrm{headI}\,L`$, $`\mathrm{tail}\,L`$ | 先頭要素（空列なら既定値）と残り |
| `List.range n`, `List.range' a m` | $`\mathrm{range}(n)`$, $`\mathrm{range}'(a,m)`$ | $`[0,\dots,n-1]`$, $`[a,\dots,a+m-1]`$ |
| `L.map f`, `L.flatMap f` | $`\mathrm{map}\,f\,L`$, $`\mathrm{flatMap}\,f\,L`$ | 各要素に $`f`$ を適用（後者は連結） |
| `L.filter p` | $`\mathrm{filter}\,p\,L`$ | 条件 $`p`$ を満たす要素のみを残した列 |

行 0 の値 $`a`$ を基準とする `takeWhile` / `dropWhile` は [`Mechanized.md`](Mechanized.md) と同じく

```math
\mathrm{tw}_a L := L.\mathrm{takeWhile}\,(\lambda q.\ a < \pi_0 q),\qquad
  \mathrm{dw}_a L := L.\mathrm{dropWhile}\,(\lambda q.\ a < \pi_0 q)
```

と書く。$`\mathrm{tw}_a L \mathbin{+\!\!+} \mathrm{dw}_a L = L`$ が成り立つ。

本章を通じて、$`u\in\mathbb{N}`$、$`b\in\mathrm{Three}`$ に対し

```math
\mathrm{Bad}_u(b) := \mathrm{filter}\bigl(\lambda g.\ \neg(g\prec b)\bigr)\ \mathrm{Glist}_u(b),
\qquad
\mathrm{mx}_u(b) := \mathrm{maxo}\bigl(\mathrm{headI}\,\mathrm{Bad}_u(b),\ \mathrm{tail}\,\mathrm{Bad}_u(b)\bigr)
```

と略記する（[(D.Glist)](Nrm.md#d-Glist), [(D.maxo)](Nrm.md#d-maxo)）。
$`\mathrm{Bad}_u(b)`$ を **$`b`$ の水準 $`u`$ における違反者リスト**と呼ぶ。これは
$`\mathrm{Glist}_u(b)`$ の要素のうち $`g\prec b`$ が成り立たないものだけを、$`\mathrm{Glist}_u(b)`$ での
出現順に残した列である。

自然数の減法はすべて切り捨て減法である（$`a\lt b`$ のとき $`a-b=0`$）。

`Nat.findGreatest P m` は「$`P(k)`$ かつ $`k\le m`$ なる最大の $`k`$、そのような $`k`$ が無ければ $`0`$」を表す。
本章で用いるその性質は次の 3 つである。

- $`\mathrm{findGreatest\_le}`$ : $`\mathrm{findGreatest}\,P\,m \le m`$。
- $`\mathrm{findGreatest\_spec}`$ : $`k\le m`$ かつ $`P(k)`$ ならば $`P(\mathrm{findGreatest}\,P\,m)`$。
- $`\mathrm{findGreatest\_is\_greatest}`$ : $`\mathrm{findGreatest}\,P\,m \lt l`$ かつ $`l\le m`$ ならば $`\neg P(l)`$。

---

## $`\mathrm{maxo}`$ は上界である

<a id="t-maxo_ub"></a>
### 定理 $`\mathrm{maxo}`$ の上界性 (T.maxo_ub)

**主張** 任意の $`x\in\mathrm{Three}`$、$`ys\in\mathrm{List}\,\mathrm{Three}`$ に対し

```math
\forall y\in x\mathbin{::}ys,\quad y \preceq \mathrm{maxo}(x,ys).
```

**証明** リスト $`ys`$ の構造に関する帰納法（$`x`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(ys) :\equiv \forall x\in\mathrm{Three},\ \forall y\in x\mathbin{::}ys,\ y\preceq\mathrm{maxo}(x,ys).
```

**基底段** $`ys=[]`$。$`y\in[x]`$ は $`y=x`$ を意味し、[(T.maxo_nil)](Nrm.md#t-maxo_nil) より
$`\mathrm{maxo}(x,[])=x`$ であるから $`y=\mathrm{maxo}(x,[])`$、すなわち
[(D.ole)](Mechanized.md#d-ole) の第 2 選言により $`y\preceq\mathrm{maxo}(x,[])`$。

**帰納段** $`ys=z\mathbin{::}zs`$。帰納法の仮定は $`\Phi(zs)`$、すなわち
「任意の $`x'`$ と任意の $`y\in x'\mathbin{::}zs`$ について $`y\preceq\mathrm{maxo}(x',zs)`$」である。
[(T.maxo_cons)](Nrm.md#t-maxo_cons) より

```math
\mathrm{maxo}(x,z\mathbin{::}zs)=\mathrm{maxo}\bigl(\ \text{if }x\prec z\text{ then }z\text{ else }x,\ zs\bigr).
```

- **場合 1 : $`x\prec z`$。** このとき $`\mathrm{maxo}(x,z\mathbin{::}zs)=\mathrm{maxo}(z,zs)`$。
  $`y\in x\mathbin{::}z\mathbin{::}zs`$ を取る。
  - $`y=x`$ のとき。$`\Phi(zs)`$ を $`x':=z`$、$`y:=z`$（$`z\in z\mathbin{::}zs`$）に適用して
    $`z\preceq\mathrm{maxo}(z,zs)`$。仮定 $`x\prec z`$ から $`x\preceq z`$ であるから、
    [(T.ole_trans)](Wfsum.md#t-ole_trans) により $`x\preceq\mathrm{maxo}(z,zs)`$。
  - $`y\in z\mathbin{::}zs`$ のとき。$`\Phi(zs)`$ を $`x':=z`$ に適用して直ちに
    $`y\preceq\mathrm{maxo}(z,zs)`$。
- **場合 2 : $`\neg(x\prec z)`$。** このとき $`\mathrm{maxo}(x,z\mathbin{::}zs)=\mathrm{maxo}(x,zs)`$。
  $`y\in x\mathbin{::}z\mathbin{::}zs`$ を取る。
  - $`y=x`$ のとき。$`\Phi(zs)`$ を $`x':=x`$、$`y:=x`$（$`x\in x\mathbin{::}zs`$）に適用して
    $`x\preceq\mathrm{maxo}(x,zs)`$。
  - $`y=z`$ のとき。[(T.olt_total)](Mechanized.md#t-olt_total) より
    $`z\prec x`$、$`z=x`$、$`x\prec z`$ のいずれかである。第 3 は場合 2 の仮定に反するので、
    $`z\prec x`$ または $`z=x`$、すなわち $`z\preceq x`$。$`\Phi(zs)`$ より $`x\preceq\mathrm{maxo}(x,zs)`$
    であるから、[(T.ole_trans)](Wfsum.md#t-ole_trans) により $`z\preceq\mathrm{maxo}(x,zs)`$。
  - $`y\in zs`$ のとき。$`y\in x\mathbin{::}zs`$ であるから $`\Phi(zs)`$ より
    $`y\preceq\mathrm{maxo}(x,zs)`$。∎

<a id="t-maxo_ub_mem"></a>
### 定理 非空リストに対する上界性 (T.maxo_ub_mem)

**主張** $`gs\ne[]`$ ならば $`\forall y\in gs,\ y\preceq\mathrm{maxo}(\mathrm{headI}\,gs,\ \mathrm{tail}\,gs)`$。

**証明** $`gs`$ の構成子で場合分けする。$`gs=[]`$ は仮定 $`gs\ne[]`$ に反する。
$`gs=g\mathbin{::}gs'`$ のときは $`\mathrm{headI}\,gs=g`$、$`\mathrm{tail}\,gs=gs'`$ であるから、
主張は $`\forall y\in g\mathbin{::}gs',\ y\preceq\mathrm{maxo}(g,gs')`$ となり、これは
[(T.maxo_ub)](#t-maxo_ub) そのものである。∎

---

## 臨界項関係の推移性

<a id="t-Gterm_trans"></a>
### 定理 臨界項関係の推移性 (T.Gterm_trans)

**主張** $`x\in G_u(g)`$ かつ $`g\in G_u(t)`$ ならば $`x\in G_u(t)`$
（[(D.Gterm)](Otembed.md#d-Gterm)）。

**証明** 項 $`t`$ の構造に関する帰納法（$`u`$, $`x`$, $`g`$ と仮定 $`x\in G_u(g)`$ は固定）。
帰納法の述語は

```math
\Phi(t) :\equiv \bigl(g\in G_u(t)\ \to\ x\in G_u(t)\bigr).
```

**基底段** $`t=\mathsf Z`$。$`G_u(\mathsf Z)=\emptyset`$ であるから前件 $`g\in\emptyset`$ は偽であり、
$`\Phi(\mathsf Z)`$ が成り立つ。

**帰納段** $`t=\mathsf P(a,b,c)`$。帰納法の仮定は $`\Phi(b)`$ と $`\Phi(c)`$ である。
$`g\in G_u(\mathsf P(a,b,c))`$ を仮定する。[(T.mem_Gterm_P)](Otembed.md#t-mem_Gterm_P) より、これは

```math
\bigl(u\le a\ \wedge\ (g=b\ \vee\ g\in G_u(b))\bigr)\ \vee\ g\in G_u(c)
```

と同値である。

- $`u\le a`$ かつ $`g=b`$ のとき。固定した仮定 $`x\in G_u(g)`$ は $`x\in G_u(b)`$ である。
  [(T.mem_Gterm_P)](Otembed.md#t-mem_Gterm_P) の右辺の第 1 選言（$`u\le a`$、$`x\in G_u(b)`$）が
  成り立つので $`x\in G_u(\mathsf P(a,b,c))`$。
- $`u\le a`$ かつ $`g\in G_u(b)`$ のとき。$`\Phi(b)`$ より $`x\in G_u(b)`$。
  [(T.mem_Gterm_P)](Otembed.md#t-mem_Gterm_P) の右辺の第 1 選言（$`u\le a`$、$`x\in G_u(b)`$）により
  $`x\in G_u(\mathsf P(a,b,c))`$。
- $`g\in G_u(c)`$ のとき。$`\Phi(c)`$ より $`x\in G_u(c)`$。
  [(T.mem_Gterm_P)](Otembed.md#t-mem_Gterm_P) の右辺の第 2 選言により $`x\in G_u(\mathsf P(a,b,c))`$。∎

---

## 射影は増大的である

<a id="t-mem_filter_Gterm"></a>
### 定理 違反者は臨界項である (T.mem_filter_Gterm)

**主張** $`g\in\mathrm{Bad}_u(b)`$ ならば $`g\in G_u(b)`$。

**証明** $`\mathrm{Bad}_u(b)`$ は $`\mathrm{Glist}_u(b)`$ の部分列であるから
$`g\in\mathrm{Glist}_u(b)`$（`List.mem_of_mem_filter`）。
[(T.mem_Glist)](Nrm.md#t-mem_Glist) より $`g\in\mathrm{Glist}_u(b)\iff g\in G_u(b)`$ であるから
$`g\in G_u(b)`$。∎

<a id="t-mem_filter_not_olt"></a>
### 定理 違反者は $`b`$ より小さくない (T.mem_filter_not_olt)

**主張** $`g\in\mathrm{Bad}_u(b)`$ ならば $`\neg(g\prec b)`$。

**証明** $`\mathrm{filter}`$ の要素は述語を満たす（`List.of_mem_filter`）。
$`\mathrm{Bad}_u(b)`$ の述語は $`\lambda g.\ \neg(g\prec b)`$ であるから、$`g`$ について
$`\neg(g\prec b)`$ が成り立つ。∎

<a id="t-proj_ole"></a>
### 定理 射影の増大性 (T.proj_ole)

**主張** 任意の $`u\in\mathbb{N}`$、$`b\in\mathrm{Three}`$ に対し $`b\preceq\mathrm{proj}_u(b)`$
（[(D.proj)](Nrm.md#d-proj)）。

**証明** $`n:=\lVert b\rVert`$（[(D.tsize)](Wfsum.md#d-tsize)）に関する強帰納法。帰納法の述語は

```math
\Phi(n) :\equiv \forall b\in\mathrm{Three},\ \lVert b\rVert=n\ \to\ b\preceq\mathrm{proj}_u(b).
```

$`n`$ を固定し、帰納法の仮定として $`\forall m\lt n,\ \Phi(m)`$ を仮定する。
$`\lVert b\rVert=n`$ なる $`b`$ を取り、$`\mathrm{Bad}_u(b)`$ が空か否かで場合分けする。

- **$`\mathrm{Bad}_u(b)=[]`$ のとき。** [(T.proj_id)](Nrm.md#t-proj_id) より
  $`\mathrm{proj}_u(b)=b`$ であるから、$`b=\mathrm{proj}_u(b)`$、したがって
  [(D.ole)](Mechanized.md#d-ole) の第 2 選言により $`b\preceq\mathrm{proj}_u(b)`$。
- **$`\mathrm{Bad}_u(b)\ne[]`$ のとき。** [(T.proj_rec)](Nrm.md#t-proj_rec) より
  $`\mathrm{proj}_u(b)=\mathrm{proj}_u(\mathrm{mx}_u(b))`$。
  [(T.maxo_hdtl_in)](Nrm.md#t-maxo_hdtl_in) より $`\mathrm{mx}_u(b)\in\mathrm{Bad}_u(b)`$ であるから、
  [(T.mem_filter_Gterm)](#t-mem_filter_Gterm) より $`\mathrm{mx}_u(b)\in G_u(b)`$、
  [(T.mem_filter_not_olt)](#t-mem_filter_not_olt) より $`\neg(\mathrm{mx}_u(b)\prec b)`$。
  [(T.olt_total)](Mechanized.md#t-olt_total) を $`b`$ と $`\mathrm{mx}_u(b)`$ に適用すると
  $`b\prec\mathrm{mx}_u(b)`$、$`b=\mathrm{mx}_u(b)`$、$`\mathrm{mx}_u(b)\prec b`$ のいずれかであり、
  第 3 は上で否定したから

  ```math
  b\preceq\mathrm{mx}_u(b).
  ```

  一方 [(T.Gterm_tsize)](Otembed.md#t-Gterm_tsize) を $`\mathrm{mx}_u(b)\in G_u(b)`$ に適用して
  $`\lVert\mathrm{mx}_u(b)\rVert\lt \lVert b\rVert=n`$。帰納法の仮定 $`\Phi(\lVert\mathrm{mx}_u(b)\rVert)`$ より

  ```math
  \mathrm{mx}_u(b)\preceq\mathrm{proj}_u(\mathrm{mx}_u(b))=\mathrm{proj}_u(b).
  ```

  [(T.ole_trans)](Wfsum.md#t-ole_trans) により $`b\preceq\mathrm{proj}_u(b)`$。∎

---

## 一段定理

この節に宣言はない。次節の $`\mathrm{fire}`$ と
[(T.proj_eq_maxo_bad)](#t-proj_eq_maxo_bad) が実際の一段定理である。

---

## 発火述語と射影の劣単調性

<a id="d-pfire"></a>
### 定義 発火述語 (D.pfire)

```math
\mathrm{fire}_u(b)\ :\iff\ \mathrm{Bad}_u(b)\ne[].
```

すなわち $`b`$ は水準 $`u`$ の臨界項のうち $`b`$ より真に小さくないものを少なくとも 1 つもつ。
[(T.proj_id)](Nrm.md#t-proj_id) と [(T.proj_rec)](Nrm.md#t-proj_rec) の場合分けは、
ちょうどこの述語の真偽による場合分けである。

<a id="t-pfire_iff"></a>
### 定理 発火の言い換え (T.pfire_iff)

**主張** $`\mathrm{fire}_u(b)\ \iff\ \exists g\in G_u(b),\ \neg(g\prec b)`$。

**証明**

$`(\Rightarrow)`$ $`\mathrm{Bad}_u(b)\ne[]`$ ならば、その要素 $`g`$ が存在する
（`List.exists_mem_of_ne_nil`）。[(T.mem_filter_Gterm)](#t-mem_filter_Gterm) より
$`g\in G_u(b)`$、[(T.mem_filter_not_olt)](#t-mem_filter_not_olt) より $`\neg(g\prec b)`$。

$`(\Leftarrow)`$ $`g\in G_u(b)`$ かつ $`\neg(g\prec b)`$ とする。
[(T.mem_Glist)](Nrm.md#t-mem_Glist) より $`g\in\mathrm{Glist}_u(b)`$ であり、
$`\mathrm{Bad}_u(b)`$ の述語 $`\neg(g\prec b)`$ も満たすから
$`g\in\mathrm{Bad}_u(b)`$（`List.mem_filter`）。
ここで $`\mathrm{Bad}_u(b)=[]`$ と仮定すると $`g\in[]`$ となって矛盾する。
よって $`\mathrm{Bad}_u(b)\ne[]`$。∎

<a id="t-proj_nofire"></a>
### 定理 非発火なら射影は恒等 (T.proj_nofire)

**主張** $`\neg\,\mathrm{fire}_u(b)`$ ならば $`\mathrm{proj}_u(b)=b`$。

**証明** $`\neg\,\mathrm{fire}_u(b)`$ は $`\neg(\mathrm{Bad}_u(b)\ne[])`$ であり、二重否定除去により
$`\mathrm{Bad}_u(b)=[]`$。[(T.proj_id)](Nrm.md#t-proj_id) より $`\mathrm{proj}_u(b)=b`$。∎

<a id="t-olt_ole_trans"></a>
### 定理 狭義・広義の混合推移律 (T.olt_ole_trans)

**主張** $`x\prec y`$ かつ $`y\preceq z`$ ならば $`x\prec z`$。

**証明** [(D.ole)](Mechanized.md#d-ole) より $`y\preceq z`$ は $`y\prec z`$ または $`y=z`$ である。
前者のときは [(T.olt_trans)](Mechanized.md#t-olt_trans) より $`x\prec z`$。
後者のときは $`z=y`$ を代入して $`x\prec z`$。∎

この命題は名前空間 `YAPSS` における
[(T.olt_ole_trans)](Mechanized.md#t-olt_ole_trans)（名前空間 `YAPSS.Three`）の
同一内容の再掲であり、両者は同じ主張・同じ証明をもつ。以降、本章で
$`\prec`$ と $`\preceq`$ を混ぜて推移させる箇所ではこのどちらかを用いる。

---

## `ins` の尾部に関する無条件な狭義単調性

<a id="t-absorb_mono"></a>
### 定理 吸収条件の右向き伝播 (T.absorb_mono)

**主張** $`a,e,e'\in\mathbb{N}`$、$`b,f,f',g,g'\in\mathrm{Three}`$ とする。

```math
\bigl(a<e\ \vee\ (a=e\wedge b\prec f)\bigr)\ \wedge\ \mathsf P(e,f,g)\prec\mathsf P(e',f',g')
\ \Longrightarrow\ a<e'\ \vee\ (a=e'\wedge b\prec f').
```

**証明** [(T.olt_P_P)](Mechanized.md#t-olt_P_P) により、第 2 の仮定は次の 3 つのいずれかである。

- **(i) $`e\lt e'`$。** 第 1 の仮定が $`a\lt e`$ ならば $`a\lt e\lt e'`$ より $`a\lt e'`$。
  第 1 の仮定が $`a=e\wedge b\prec f`$ ならば $`a=e\lt e'`$ より $`a\lt e'`$。どちらも左選言。
- **(ii) $`e=e'`$ かつ $`f\prec f'`$。** 第 1 の仮定が $`a\lt e`$ ならば $`a\lt e=e'`$ より左選言。
  第 1 の仮定が $`a=e\wedge b\prec f`$ ならば $`a=e=e'`$ であり、
  [(T.olt_trans)](Mechanized.md#t-olt_trans) より $`b\prec f\prec f'`$、すなわち $`b\prec f'`$。
  よって右選言 $`a=e'\wedge b\prec f'`$。
- **(iii) $`e=e'`$、$`f=f'`$、$`g\prec g'`$。** $`e=e'`$ と $`f=f'`$ を代入すれば、
  第 1 の仮定はそのまま結論と同じ命題である。∎

<a id="t-ins_olt_mono"></a>
### 定理 `ins` の尾部単調性 (T.ins_olt_mono)

**主張** $`t\prec t'`$ ならば $`\mathrm{ins}_a(b,t)\prec\mathrm{ins}_a(b,t')`$
（[(D.ins)](Nrm.md#d-ins)）。側条件は一切ない。

**証明** $`t`$ と $`t'`$ の構成子で場合分けする。

- **$`t=\mathsf Z`$、$`t'=\mathsf Z`$。** 仮定 $`\mathsf Z\prec\mathsf Z`$ は
  [(T.olt_Z_Z)](Mechanized.md#t-olt_Z_Z) に反するので、この場合は起こらない。
- **$`t=\mathsf Z`$、$`t'=\mathsf P(e,f,g)`$。**
  [(T.ins_Z)](Nrm.md#t-ins_Z) より $`\mathrm{ins}_a(b,\mathsf Z)=\mathsf P(a,b,\mathsf Z)`$。
  [(T.ins_P)](Nrm.md#t-ins_P) より、$`A:\equiv\bigl(a\lt e\vee(a=e\wedge b\prec f)\bigr)`$ とおくと
  $`\mathrm{ins}_a(b,\mathsf P(e,f,g))`$ は $`A`$ のとき $`\mathsf P(e,f,g)`$、そうでないとき
  $`\mathsf P(a,b,\mathsf P(e,f,g))`$ である。
  - $`A`$ のとき。目標は $`\mathsf P(a,b,\mathsf Z)\prec\mathsf P(e,f,g)`$。
    $`a\lt e`$ ならば [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 1 選言、
    $`a=e\wedge b\prec f`$ ならば第 2 選言により成立。
  - $`\neg A`$ のとき。目標は $`\mathsf P(a,b,\mathsf Z)\prec\mathsf P(a,b,\mathsf P(e,f,g))`$。
    [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 3 選言（$`a=a`$、$`b=b`$、
    $`\mathsf Z\prec\mathsf P(e,f,g)`$）であり、最後の項は
    [(T.olt_Z_P)](Mechanized.md#t-olt_Z_P) による。
- **$`t=\mathsf P(e,f,g)`$、$`t'=\mathsf Z`$。** 仮定 $`\mathsf P(e,f,g)\prec\mathsf Z`$ は
  [(T.not_olt_Z)](Mechanized.md#t-not_olt_Z) に反するので、この場合は起こらない。
- **$`t=\mathsf P(e,f,g)`$、$`t'=\mathsf P(e',f',g')`$。**
  $`A:\equiv\bigl(a\lt e\vee(a=e\wedge b\prec f)\bigr)`$、
  $`A':\equiv\bigl(a\lt e'\vee(a=e'\wedge b\prec f')\bigr)`$ とおく。
  - $`A`$ のとき。[(T.absorb_mono)](#t-absorb_mono) を仮定 $`A`$ と $`t\prec t'`$ に適用して $`A'`$ を得る。
    このとき [(T.ins_P)](Nrm.md#t-ins_P) より
    $`\mathrm{ins}_a(b,t)=\mathsf P(e,f,g)=t`$、$`\mathrm{ins}_a(b,t')=\mathsf P(e',f',g')=t'`$
    であるから、目標は仮定 $`t\prec t'`$ そのものである。
  - $`\neg A`$ かつ $`A'`$ のとき。$`\mathrm{ins}_a(b,t)=\mathsf P(a,b,\mathsf P(e,f,g))`$、
    $`\mathrm{ins}_a(b,t')=\mathsf P(e',f',g')`$。$`A'`$ の第 1 選言 $`a\lt e'`$ ならば
    [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 1 選言、
    第 2 選言 $`a=e'\wedge b\prec f'`$ ならば第 2 選言により成立。
  - $`\neg A`$ かつ $`\neg A'`$ のとき。$`\mathrm{ins}_a(b,t)=\mathsf P(a,b,\mathsf P(e,f,g))`$、
    $`\mathrm{ins}_a(b,t')=\mathsf P(a,b,\mathsf P(e',f',g'))`$ であるから、
    [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 3 選言（$`a=a`$、$`b=b`$、$`t\prec t'`$）により成立。∎

---

## 1 箇所増加の関係

Lean の当該節は 4 つの帰納的関係を導入する。これらは
「標準的な区間に 1 列を付加したとき正規化像に生じる形」を分類するための語彙であり、
本章の他の宣言はこれらを用いない（下流の章でも本章の他の命題との依存はない）。
ここでは導入規則と、それに伴う帰納法原理の形だけを記録する。

<a id="d-lext"></a>
### 定義 葉の追加 (D.lext)

関係 $`\mathrm{lext}\subseteq\mathrm{Three}\times\mathrm{Three}`$ を次の 3 規則で生成される最小の関係と定める。

```math
\frac{\ }{\ \mathrm{lext}\ \mathsf Z\ \mathsf P(w,\mathsf Z,\mathsf Z)\ }\ \text{(end\_)}\quad(w\in\mathbb{N})
\qquad
\frac{\ \mathrm{lext}\ c\ c'\ }{\ \mathrm{lext}\ \mathsf P(a,b,c)\ \mathsf P(a,b,c')\ }\ \text{(tail)}
\qquad
\frac{\ \mathrm{lext}\ b\ b'\ }{\ \mathrm{lext}\ \mathsf P(a,b,c)\ \mathsf P(a,b',c)\ }\ \text{(arg)}
```

<a id="d-lflip"></a>
### 定義 葉の添字増加 (D.lflip)

```math
\frac{\ w<w'\ }{\ \mathrm{lflip}\ \mathsf P(w,\mathsf Z,\mathsf Z)\ \mathsf P(w',\mathsf Z,\mathsf Z)\ }\ \text{(leaf)}
\qquad
\frac{\ \mathrm{lflip}\ c\ c'\ }{\ \mathrm{lflip}\ \mathsf P(a,b,c)\ \mathsf P(a,b,c')\ }\ \text{(tail)}
\qquad
\frac{\ \mathrm{lflip}\ b\ b'\ }{\ \mathrm{lflip}\ \mathsf P(a,b,c)\ \mathsf P(a,b',c)\ }\ \text{(arg)}
```

<a id="d-einc"></a>
### 定義 末端位置の葉追加 (D.einc)

```math
\frac{\ }{\ \mathrm{einc}\ \mathsf Z\ \mathsf P(w,\mathsf Z,\mathsf Z)\ }\ \text{(end\_)}\quad(w\in\mathbb{N})
\qquad
\frac{\ \mathrm{einc}\ c\ c'\ }{\ \mathrm{einc}\ \mathsf P(a,b,c)\ \mathsf P(a,b,c')\ }\ \text{(tail)}
\qquad
\frac{\ \mathrm{einc}\ b\ b'\ }{\ \mathrm{einc}\ \mathsf P(a,b,\mathsf Z)\ \mathsf P(a,b',\mathsf Z)\ }\ \text{(argZ)}
```

$`\mathrm{lext}`$ との差は第 3 規則にある。$`\mathrm{einc}`$ の (argZ) は尾部が $`\mathsf Z`$ である
主要項にのみ適用でき、$`\mathrm{lext}`$ の (arg) は任意の尾部 $`c`$ に適用できる。

<a id="d-eflip"></a>
### 定義 末端位置の添字増加 (D.eflip)

```math
\frac{\ w<w'\ }{\ \mathrm{eflip}\ \mathsf P(w,\mathsf Z,\mathsf Z)\ \mathsf P(w',\mathsf Z,\mathsf Z)\ }\ \text{(leaf)}
\qquad
\frac{\ \mathrm{eflip}\ c\ c'\ }{\ \mathrm{eflip}\ \mathsf P(a,b,c)\ \mathsf P(a,b,c')\ }\ \text{(tail)}
\qquad
\frac{\ \mathrm{eflip}\ b\ b'\ }{\ \mathrm{eflip}\ \mathsf P(a,b,\mathsf Z)\ \mathsf P(a,b',\mathsf Z)\ }\ \text{(argZ)}
```

**帰納法原理.** これら 4 つはいずれも帰納的関係である。
$`\mathcal R\in\{\mathrm{lext},\mathrm{lflip},\mathrm{einc},\mathrm{eflip}\}`$ とし、
述語 $`Q:\mathrm{Three}\to\mathrm{Three}\to\mathrm{Prop}`$ が $`\mathcal R`$ の 3 つの導入規則それぞれについて
「前提の $`\mathcal R`$ の箇所を $`Q`$ に置き換えた仮定から結論の $`Q`$ が導ける」ならば

```math
\forall x\,y,\ \mathcal R\ x\ y\ \to\ Q\ x\ y
```

が成り立つ。たとえば $`\mathcal R=\mathrm{lext}`$ のとき、示すべき 3 条件は
$`\forall w,\ Q\ \mathsf Z\ \mathsf P(w,\mathsf Z,\mathsf Z)`$、
$`\forall a\,b\,c\,c',\ Q\ c\ c'\to Q\ \mathsf P(a,b,c)\ \mathsf P(a,b,c')`$、
$`\forall a\,b\,b'\,c,\ Q\ b\ b'\to Q\ \mathsf P(a,b,c)\ \mathsf P(a,b',c)`$ である。

---

## 小さな計算補題

<a id="t-translate_nil"></a>
### 定理 空列の翻訳 (T.translate_nil)

**主張** $`\mathrm{tr}\,[]=\mathsf Z`$。

**証明** [(D.translate)](Mechanized.md#d-translate) の第 1 式そのものである。∎

<a id="t-translate_cons"></a>
### 定理 先頭付加の翻訳 (T.translate_cons)

**主張** $`p\in\mathbb{N}\times\mathbb{N}`$、$`\mathit{rest}\in\mathrm{PairSeq}`$ に対し

```math
\mathrm{tr}\,(p\mathbin{::}\mathit{rest})
=\mathsf P\bigl(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p}\mathit{rest}),\ \mathrm{tr}(\mathrm{dw}_{\pi_0 p}\mathit{rest})\bigr).
```

**証明** [(D.translate)](Mechanized.md#d-translate) の第 2 式そのものである。∎

<a id="t-translate_single"></a>
### 定理 1 列の翻訳 (T.translate_single)

**主張** $`\mathrm{tr}\,[q]=\mathsf P(\pi_1 q,\mathsf Z,\mathsf Z)`$。

**証明** [(T.translate_cons)](#t-translate_cons) を $`p:=q`$、$`\mathit{rest}:=[]`$ に適用すると

```math
\mathrm{tr}[q]=\mathsf P\bigl(\pi_1 q,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 q}[]),\ \mathrm{tr}(\mathrm{dw}_{\pi_0 q}[])\bigr).
```

空列の `takeWhile` と `dropWhile` はどちらも空列であるから、
[(T.translate_nil)](#t-translate_nil) より両引数は $`\mathsf Z`$ である。∎

<a id="t-proj_Z"></a>
### 定理 $`\mathsf Z`$ の射影 (T.proj_Z)

**主張** $`\mathrm{proj}_u(\mathsf Z)=\mathsf Z`$。

**証明** [(T.Glist_Z)](Nrm.md#t-Glist_Z) より $`\mathrm{Glist}_u(\mathsf Z)=[]`$ であり、
空列の `filter` は空列であるから $`\mathrm{Bad}_u(\mathsf Z)=[]`$。
[(T.proj_id)](Nrm.md#t-proj_id) より $`\mathrm{proj}_u(\mathsf Z)=\mathsf Z`$。∎

<a id="t-nrm_leaf"></a>
### 定理 葉の正規化 (T.nrm_leaf)

**主張** $`\mathrm{nrm}(\mathsf P(w,\mathsf Z,\mathsf Z))=\mathsf P(w,\mathsf Z,\mathsf Z)`$
（[(D.nrm)](Nrm.md#d-nrm)）。

**証明** [(T.nrm_P)](Nrm.md#t-nrm_P) より

```math
\mathrm{nrm}(\mathsf P(w,\mathsf Z,\mathsf Z))
=\mathrm{ins}_w\bigl(\mathrm{proj}_w(\mathrm{nrm}\,\mathsf Z),\ \mathrm{nrm}\,\mathsf Z\bigr).
```

[(T.nrm_Z)](Nrm.md#t-nrm_Z) より $`\mathrm{nrm}\,\mathsf Z=\mathsf Z`$、
[(T.proj_Z)](#t-proj_Z) より $`\mathrm{proj}_w(\mathsf Z)=\mathsf Z`$、
[(T.ins_Z)](Nrm.md#t-ins_Z) より $`\mathrm{ins}_w(\mathsf Z,\mathsf Z)=\mathsf P(w,\mathsf Z,\mathsf Z)`$。∎

---

## 末尾付加の条件束と主帰納法

<a id="d-snocok"></a>
### 定義 末尾付加の条件束 (D.snocok)

$`C\in\mathrm{PairSeq}`$、$`q\in\mathbb{N}\times\mathbb{N}`$ に対し $`\mathrm{snocok}(C,q)`$ を
$`\lvert C\rvert`$ に関する再帰で定める。

```math
\mathrm{snocok}([],q) := \bot,
```

```math
\mathrm{snocok}(p\mathbin{::}\mathit{rest},\,q) :=
\begin{cases}
\pi_0 p<\pi_0 q\ \to\
 \mathrm{proj}_{\pi_1 p}\bigl(\mathrm{nrm}(\mathrm{tr}\,\mathit{rest})\bigr)
 \prec
 \mathrm{proj}_{\pi_1 p}\bigl(\mathrm{nrm}(\mathrm{tr}(\mathit{rest}\mathbin{+\!\!+}[q]))\bigr)
 & (\mathrm{dw}_{\pi_0 p}\mathit{rest}=[])\cr[2mm]
\mathrm{snocok}(\mathrm{dw}_{\pi_0 p}\mathit{rest},\,q) & (\mathrm{dw}_{\pi_0 p}\mathit{rest}\ne[])
\end{cases}
```

再帰が停止することは、`dropWhile` が長さを増やさないこと
$`\lvert\mathrm{dw}_{\pi_0 p}\mathit{rest}\rvert\le\lvert \mathit{rest}\rvert`$ と
$`\lvert \mathit{rest}\rvert\lt \lvert p\mathbin{::}\mathit{rest}\rvert`$ から従う。

すなわち $`\mathrm{snocok}(C,q)`$ は、$`C`$ を $`\mathrm{dw}`$ で辿って得られる最内の支配区間
（$`\mathrm{dw}`$ が空になる位置）において、引数側の射影が狭義に増加することを要求する条件である。

<a id="t-snocok_nil"></a>
### 定理 空列に対する条件束 (T.snocok_nil)

**主張** $`\neg\,\mathrm{snocok}([],q)`$。

**証明** [(D.snocok)](#d-snocok) の第 1 式により $`\mathrm{snocok}([],q)`$ は $`\bot`$ と
定義により等しい。よって $`\mathrm{snocok}([],q)`$ の仮定からそのまま $`\bot`$ が得られる。∎

<a id="t-snocok_cons"></a>
### 定理 条件束の展開 (T.snocok_cons)

**主張** [(D.snocok)](#d-snocok) の第 2 式（等式としての展開）。

**証明** [(D.snocok)](#d-snocok) の定義式そのものである。∎

<a id="t-nrm_snoc_seg"></a>
### 定理 末尾付加の主帰納法 (T.nrm_snoc_seg)

**主張** $`\mathrm{snocok}(C,q)`$ かつ $`C\ne[]`$ ならば

```math
\mathrm{nrm}(\mathrm{tr}\,C)\ \prec\ \mathrm{nrm}\bigl(\mathrm{tr}(C\mathbin{+\!\!+}[q])\bigr).
```

**証明** $`\lvert C\rvert`$ に関する整礎帰納法。帰納法の述語は

```math
\Psi(C) :\equiv \forall q,\ \mathrm{snocok}(C,q)\to C\ne[]\to
\mathrm{nrm}(\mathrm{tr}\,C)\prec\mathrm{nrm}(\mathrm{tr}(C\mathbin{+\!\!+}[q])).
```

帰納法の仮定は「$`\lvert C'\rvert\lt \lvert C\rvert`$ なるすべての $`C'`$ について $`\Psi(C')`$」であり、
以下では $`C=p\mathbin{::}\mathit{rest}`$、$`C':=\mathrm{dw}_{\pi_0 p}\mathit{rest}`$ の 1 箇所でのみ用いる。
このとき $`\lvert C'\rvert\le\lvert \mathit{rest}\rvert\lt \lvert p\mathbin{::}\mathit{rest}\rvert=\lvert C\rvert`$
であるから、帰納法の仮定が適用できる。

**$`C=[]`$ の場合。** 仮定 $`C\ne[]`$ に反するので、この場合は起こらない。

**$`C=p\mathbin{::}\mathit{rest}`$ の場合。**
$`a:=\pi_0 p`$、$`w:=\pi_1 p`$、$`K:=\mathrm{tw}_a\mathit{rest}`$、$`T:=\mathrm{dw}_a\mathit{rest}`$ とおく。
$`T`$ が空か否かで場合分けする。

**場合 I : $`T=[]`$。**
`dropWhile` が空列であることは、$`\mathit{rest}`$ のすべての要素が述語を満たすことと同値であるから

```math
\forall x\in\mathit{rest},\quad a<\pi_0 x .
```

したがって `takeWhile` は列全体を取り、$`K=\mathit{rest}`$ である。
[(T.translate_cons)](#t-translate_cons)、[(T.translate_nil)](#t-translate_nil)、
[(T.nrm_P)](Nrm.md#t-nrm_P)、[(T.nrm_Z)](Nrm.md#t-nrm_Z)、[(T.ins_Z)](Nrm.md#t-ins_Z) より

```math
\mathrm{nrm}(\mathrm{tr}(p\mathbin{::}\mathit{rest}))
=\mathrm{ins}_w\bigl(\mathrm{proj}_w(\mathrm{nrm}(\mathrm{tr}\,\mathit{rest})),\ \mathsf Z\bigr)
=\mathsf P\bigl(w,\ \mathrm{proj}_w(\mathrm{nrm}(\mathrm{tr}\,\mathit{rest})),\ \mathsf Z\bigr).
\tag{I.1}
```

また [(T.snocok_cons)](#t-snocok_cons) の第 1 分岐により、仮定 $`\mathrm{snocok}(C,q)`$ は

```math
a<\pi_0 q\ \to\
\mathrm{proj}_w(\mathrm{nrm}(\mathrm{tr}\,\mathit{rest}))
\prec\mathrm{proj}_w\bigl(\mathrm{nrm}(\mathrm{tr}(\mathit{rest}\mathbin{+\!\!+}[q]))\bigr)
\tag{I.2}
```

である。$`a\lt \pi_0 q`$ か否かでさらに分ける。

- **場合 I-(C)（引数側の延長）: $`a\lt \pi_0 q`$。**
  [(T.takeWhile_append_all)](Mechanized.md#t-takeWhile_append_all) を
  「$`\mathit{rest}`$ の全要素が述語を満たす」に適用すると
  $`\mathrm{tw}_a(\mathit{rest}\mathbin{+\!\!+}[q])=\mathit{rest}\mathbin{+\!\!+}\mathrm{tw}_a[q]`$ であり、
  $`a\lt \pi_0 q`$ より $`\mathrm{tw}_a[q]=[q]`$、よって

  ```math
  \mathrm{tw}_a(\mathit{rest}\mathbin{+\!\!+}[q])=\mathit{rest}\mathbin{+\!\!+}[q].
  ```

  同じく [(T.dropWhile_append_all)](Mechanized.md#t-dropWhile_append_all) より
  $`\mathrm{dw}_a(\mathit{rest}\mathbin{+\!\!+}[q])=\mathrm{dw}_a[q]=[]`$。したがって

  ```math
  \mathrm{nrm}\bigl(\mathrm{tr}((p\mathbin{::}\mathit{rest})\mathbin{+\!\!+}[q])\bigr)
  =\mathsf P\bigl(w,\ \mathrm{proj}_w(\mathrm{nrm}(\mathrm{tr}(\mathit{rest}\mathbin{+\!\!+}[q]))),\ \mathsf Z\bigr).
  ```

  (I.1) と合わせ、[(T.olt_P_b)](Mechanized.md#t-olt_P_b) を (I.2) の結論に適用すれば主張を得る。
- **場合 I-(A)（新しい和項）: $`\neg(a\lt \pi_0 q)`$。**
  [(T.takeWhile_append_all)](Mechanized.md#t-takeWhile_append_all) と
  [(T.dropWhile_append_all)](Mechanized.md#t-dropWhile_append_all) を同じく適用する。
  今度は $`\neg(a\lt \pi_0 q)`$ より $`\mathrm{tw}_a[q]=[]`$、$`\mathrm{dw}_a[q]=[q]`$ であるから

  ```math
  \mathrm{tw}_a(\mathit{rest}\mathbin{+\!\!+}[q])=\mathit{rest},\qquad
  \mathrm{dw}_a(\mathit{rest}\mathbin{+\!\!+}[q])=[q].
  ```

  よって [(T.translate_single)](#t-translate_single) と [(T.nrm_leaf)](#t-nrm_leaf) より

  ```math
  \mathrm{nrm}\bigl(\mathrm{tr}((p\mathbin{::}\mathit{rest})\mathbin{+\!\!+}[q])\bigr)
  =\mathrm{ins}_w\bigl(\mathrm{proj}_w(\mathrm{nrm}(\mathrm{tr}\,\mathit{rest})),\ \mathsf P(\pi_1 q,\mathsf Z,\mathsf Z)\bigr).
  ```

  (I.1) の中辺と比べると、両者は $`\mathrm{ins}_w(\cdot,-)`$ の第 2 引数だけが
  $`\mathsf Z`$ と $`\mathsf P(\pi_1 q,\mathsf Z,\mathsf Z)`$ で異なる。
  [(T.olt_Z_P)](Mechanized.md#t-olt_Z_P) より $`\mathsf Z\prec\mathsf P(\pi_1 q,\mathsf Z,\mathsf Z)`$
  であるから、[(T.ins_olt_mono)](#t-ins_olt_mono) により主張を得る。

**場合 II : $`T\ne[]`$（尾部側の延長）。**
$`T\ne[]`$ より、$`\mathit{rest}`$ の要素で述語を満たさないものが存在する。実際、
すべての $`x\in\mathit{rest}`$ が $`a\lt \pi_0 x`$ を満たすなら $`T=[]`$ となるからである。
そのような要素を $`x_0\in\mathit{rest}`$、$`\neg(a\lt \pi_0 x_0)`$ とする。
[(T.takeWhile_append_not)](Mechanized.md#t-takeWhile_append_not) と
[(T.dropWhile_append_not)](Mechanized.md#t-dropWhile_append_not) より

```math
\mathrm{tw}_a(\mathit{rest}\mathbin{+\!\!+}[q])=K,\qquad
\mathrm{dw}_a(\mathit{rest}\mathbin{+\!\!+}[q])=T\mathbin{+\!\!+}[q].
```

よって [(T.translate_cons)](#t-translate_cons) と [(T.nrm_P)](Nrm.md#t-nrm_P) より

```math
\mathrm{nrm}(\mathrm{tr}(p\mathbin{::}\mathit{rest}))
=\mathrm{ins}_w\bigl(\mathrm{proj}_w(\mathrm{nrm}(\mathrm{tr}\,K)),\ \mathrm{nrm}(\mathrm{tr}\,T)\bigr),
```

```math
\mathrm{nrm}\bigl(\mathrm{tr}((p\mathbin{::}\mathit{rest})\mathbin{+\!\!+}[q])\bigr)
=\mathrm{ins}_w\bigl(\mathrm{proj}_w(\mathrm{nrm}(\mathrm{tr}\,K)),\ \mathrm{nrm}(\mathrm{tr}(T\mathbin{+\!\!+}[q]))\bigr).
```

[(T.snocok_cons)](#t-snocok_cons) の第 2 分岐により、仮定 $`\mathrm{snocok}(C,q)`$ は
$`\mathrm{snocok}(T,q)`$ である。帰納法の仮定 $`\Psi(T)`$ を $`\mathrm{snocok}(T,q)`$ と $`T\ne[]`$ に
適用して

```math
\mathrm{nrm}(\mathrm{tr}\,T)\prec\mathrm{nrm}(\mathrm{tr}(T\mathbin{+\!\!+}[q])).
```

[(T.ins_olt_mono)](#t-ins_olt_mono) により主張を得る。∎

---

## 行 1 の最大値

<a id="d-maxr1"></a>
### 定義 行 1 の最大値 (D.maxr1)

```math
\mathrm{maxr1}\,S := \mathrm{foldr}\ \bigl(\lambda c\,m.\ \max(\pi_1 c,\ m)\bigr)\ 0\ S .
```

すなわち $`\mathrm{maxr1}[]=0`$、$`\mathrm{maxr1}(c\mathbin{::}S)=\max(\pi_1 c,\ \mathrm{maxr1}\,S)`$。

<a id="t-maxr1_nil"></a>
### 定理 空列の $`\mathrm{maxr1}`$ (T.maxr1_nil)

**主張** $`\mathrm{maxr1}\,[]=0`$。

**証明** [(D.maxr1)](#d-maxr1) の `foldr` の初期値である（定義による等式）。∎

<a id="t-maxr1_cons"></a>
### 定理 $`\mathrm{maxr1}`$ の再帰式 (T.maxr1_cons)

**主張** $`\mathrm{maxr1}(c\mathbin{::}S)=\max(\pi_1 c,\ \mathrm{maxr1}\,S)`$。

**証明** [(D.maxr1)](#d-maxr1) の `foldr` の再帰式である（定義による等式）。∎

<a id="t-le_maxr1"></a>
### 定理 $`\mathrm{maxr1}`$ の上界性 (T.le_maxr1)

**主張** $`\forall c\in S,\ \pi_1 c\le\mathrm{maxr1}\,S`$。

**証明** リスト $`S`$ の構造に関する帰納法。帰納法の述語は

```math
\Phi(S) :\equiv \forall c\in S,\ \pi_1 c\le\mathrm{maxr1}\,S.
```

**基底段** $`S=[]`$。$`c\in[]`$ は偽であるから $`\Phi([])`$。

**帰納段** $`S=d\mathbin{::}S'`$。帰納法の仮定は $`\Phi(S')`$ である。
[(T.maxr1_cons)](#t-maxr1_cons) より $`\mathrm{maxr1}(d\mathbin{::}S')=\max(\pi_1 d,\mathrm{maxr1}\,S')`$。
$`c\in d\mathbin{::}S'`$ を取る。

- $`c=d`$ のとき。$`\pi_1 d\le\max(\pi_1 d,\mathrm{maxr1}\,S')`$。
- $`c\in S'`$ のとき。$`\Phi(S')`$ より $`\pi_1 c\le\mathrm{maxr1}\,S'\le\max(\pi_1 d,\mathrm{maxr1}\,S')`$。∎

---

## 行 1 の登攀規律 $`\mathrm{r1ok}`$

<a id="d-r1ok"></a>
### 定義 行 1 の登攀規律 (D.r1ok)

$`M\in\mathrm{PairSeq}`$ に対し

```math
\mathrm{r1ok}(M) :\iff
\forall j<\lvert M\rvert,\quad 0<\pi_0(M\langle j\rangle)\ \to\ \exists k,\
\begin{aligned}
&k<j\cr
\wedge\ &\pi_0(M\langle k\rangle)+1=\pi_0(M\langle j\rangle)\cr
\wedge\ &\bigl(\forall l,\ k<l\to l<j\to \pi_0(M\langle j\rangle)\le\pi_0(M\langle l\rangle)\bigr)\cr
\wedge\ &\pi_1(M\langle j\rangle)\le\pi_1(M\langle k\rangle)+1 .
\end{aligned}
```

言い換えると、$`\pi_0(M\langle j\rangle)\gt 0`$ なるすべての位置 $`j`$ に対して、
次の 4 条件を満たす位置 $`k`$ が存在するということである。

1. $`k\lt j`$；
2. $`\pi_0(M\langle k\rangle)+1=\pi_0(M\langle j\rangle)`$（行 0 の値がちょうど 1 小さい）；
3. $`k\lt l\lt j`$ なるすべての $`l`$ で $`\pi_0(M\langle j\rangle)\le\pi_0(M\langle l\rangle)`$
   （$`k`$ と $`j`$ の間に行 0 の値が $`\pi_0(M\langle j\rangle)`$ を下回る位置がない）；
4. $`\pi_1(M\langle j\rangle)\le\pi_1(M\langle k\rangle)+1`$
   （行 1 の値は位置 $`k`$ のそれを高々 1 しか超えない）。

条件 1, 2, 3 は、$`k`$ と $`j`$ がともに $`M`$ の添字範囲にあるとき
[(D.nextrel0)](Def.md#d-nextrel0) の条件 3, 4, 5 を満たす。すなわち $`k\to^M_0 j`$ である
（条件 2 の等式は条件 4 の不等式 $`M_{0,k}\lt M_{0,j}`$ を含意する）。
条件 4 が「行 1 は行 0 の親に対して高々 1 しか上がらない」という登攀規律である。

### 相対版 $`\mathrm{r1ok}`$ について

Lean の当該節見出しは、部分ブロックに対する相対版 $`\mathrm{r1okRel}`$ の役割を説明する
コメントであり、宣言を導入しない。以下の 6 つの宣言はこの見出しの直後に置かれている。

<a id="t-diagSeq0_length"></a>
### 定理 対角列の長さ (T.diagSeq0_length)

**主張** $`\lvert\Delta_0^v\rvert=v+1`$（[(D.diagSeq)](Def.md#d-diagSeq)）。

**証明** $`\Delta_0^v=\mathrm{map}\,(j\mapsto(j,j))\,(\mathrm{range}'(0,\,v+1-0))`$ である。
`map` は長さを変えず、$`\lvert\mathrm{range}'(a,m)\rvert=m`$ であるから
$`\lvert\Delta_0^v\rvert=v+1-0=v+1`$。∎

<a id="t-diagSeq0_getD"></a>
### 定理 対角列の成分 (T.diagSeq0_getD)

**主張** $`i\lt v+1`$ ならば $`\Delta_0^v\langle i\rangle=(i,i)`$。

**証明** $`\mathrm{range}'(0,v+1)`$ の第 $`i`$ 要素は、$`i\lt v+1`$ のとき $`0+i=i`$ である
（`List.getElem?_range'`）。`map` は要素ごとに $`j\mapsto(j,j)`$ を適用するから、
$`\Delta_0^v`$ の第 $`i`$ 要素は $`(i,i)`$ である。$`i`$ は範囲内であるから
$`\mathrm{getD}`$ は既定値 $`(0,0)`$ を返さず、$`\Delta_0^v\langle i\rangle=(i,i)`$。∎

<a id="t-r1ok_diagSeq"></a>
### 定理 対角列は $`\mathrm{r1ok}`$ (T.r1ok_diagSeq)

**主張** $`\mathrm{r1ok}(\Delta_0^v)`$。

**証明** [(T.diagSeq0_length)](#t-diagSeq0_length) より $`\lvert\Delta_0^v\rvert=v+1`$。
$`j\lt v+1`$ かつ $`0\lt \pi_0(\Delta_0^v\langle j\rangle)`$ とする。
[(T.diagSeq0_getD)](#t-diagSeq0_getD) より $`\pi_0(\Delta_0^v\langle j\rangle)=j`$ であるから $`0\lt j`$。
$`k:=j-1`$ を取る。$`0\lt j`$ より $`j-1\lt v+1`$ でもあるから、
[(T.diagSeq0_getD)](#t-diagSeq0_getD) は $`k`$ にも適用でき $`\Delta_0^v\langle j-1\rangle=(j-1,j-1)`$。

- $`k\lt j`$ : $`0\lt j`$ より $`j-1\lt j`$。
- $`\pi_0(\Delta_0^v\langle k\rangle)+1=(j-1)+1=j=\pi_0(\Delta_0^v\langle j\rangle)`$（$`0\lt j`$ による）。
- 第 3 条項 : $`j-1\lt l`$ かつ $`l\lt j`$ なる自然数 $`l`$ は存在しない
  （$`j-1\lt l`$ から $`j\le l`$、これと $`l\lt j`$ は両立しない）。よって前件が偽であり成立する。
- 第 4 条項 : $`\pi_1(\Delta_0^v\langle j\rangle)=j`$、$`\pi_1(\Delta_0^v\langle k\rangle)+1=(j-1)+1=j`$
  であるから $`j\le j`$。∎

<a id="t-getD_take"></a>
### 定理 `take` の成分 (T.getD_take)

**主張** $`j\lt m`$ ならば $`(\mathrm{take}\,m\,M)\langle j\rangle=M\langle j\rangle`$。

**証明** `List.getElem?_take` により、$`(\mathrm{take}\,m\,M)`$ の第 $`j`$ 要素（オプション値）は
$`j\lt m`$ のとき $`M`$ の第 $`j`$ 要素（オプション値）に一致する。
$`\mathrm{getD}`$ はこのオプション値に同じ既定値 $`(0,0)`$ を与えたものであるから、
両者は等しい。∎

<a id="t-r1ok_take"></a>
### 定理 $`\mathrm{r1ok}`$ は `take` で保存される (T.r1ok_take)

**主張** $`\mathrm{r1ok}(M)`$ ならば $`\mathrm{r1ok}(\mathrm{take}\,m\,M)`$。

**証明** $`j\lt \lvert\mathrm{take}\,m\,M\rvert=\min(m,\lvert M\rvert)`$ とすると $`j\lt m`$ かつ $`j\lt \lvert M\rvert`$。
[(T.getD_take)](#t-getD_take) より $`(\mathrm{take}\,m\,M)\langle j\rangle=M\langle j\rangle`$ であるから、
仮定 $`0\lt \pi_0((\mathrm{take}\,m\,M)\langle j\rangle)`$ は $`0\lt \pi_0(M\langle j\rangle)`$ と同じである。
$`\mathrm{r1ok}(M)`$ を $`j`$ に適用して $`k\lt j`$ と 3 つの条項を得る。
$`k\lt j\lt m`$ および（第 3 条項に現れる）$`l\lt j\lt m`$ であるから、
$`k`$、$`l`$、$`j`$ のいずれの位置でも [(T.getD_take)](#t-getD_take) が使え、
3 つの条項はそのまま $`\mathrm{take}\,m\,M`$ の成分に関する主張に書き換わる。∎

<a id="t-r1ok_dropLast"></a>
### 定理 $`\mathrm{r1ok}`$ は `dropLast` で保存される (T.r1ok_dropLast)

**主張** $`\mathrm{r1ok}(M)`$ ならば $`\mathrm{r1ok}(\mathrm{dropLast}\,M)`$。

**証明** $`\mathrm{dropLast}\,M=\mathrm{take}\,(\lvert M\rvert-1)\,M`$（`List.dropLast_eq_take`）であるから、
[(T.r1ok_take)](#t-r1ok_take) を $`m:=\lvert M\rvert-1`$ に適用すればよい。∎

---

## コピー分解のための添字管理

<a id="t-getD_append_left"></a>
### 定理 連結の左側成分 (T.getD_append_left)

**主張** $`i\lt \lvert G\rvert`$ ならば $`(G\mathbin{+\!\!+}X)\langle i\rangle=G\langle i\rangle`$。

**証明** `List.getElem?_append_left` により、$`i\lt \lvert G\rvert`$ のとき
$`(G\mathbin{+\!\!+}X)`$ の第 $`i`$ 要素（オプション値）は $`G`$ の第 $`i`$ 要素に一致する。
$`\mathrm{getD}`$ は同じ既定値を与えたものだから等しい。∎

<a id="t-getD_append_right"></a>
### 定理 連結の右側成分 (T.getD_append_right)

**主張** $`\lvert G\rvert\le i`$ ならば $`(G\mathbin{+\!\!+}X)\langle i\rangle=X\langle i-\lvert G\rvert\rangle`$。

**証明** `List.getElem?_append_right` により、$`\lvert G\rvert\le i`$ のとき
$`(G\mathbin{+\!\!+}X)`$ の第 $`i`$ 要素（オプション値）は $`X`$ の第 $`i-\lvert G\rvert`$ 要素に一致する。∎

<a id="t-index_decomp"></a>
### 定理 添字の商・剰余分解 (T.index_decomp)

**主張** $`0\lt L`$ かつ $`i\lt n\,L`$ ならば、$`k\lt n`$、$`q\lt L`$、$`i=k\,L+q`$ なる $`k,q`$ が存在する。

**証明** $`k:=i\ \mathrm{div}\ L`$、$`q:=i\bmod L`$ とおく。

- $`k\lt n`$ : $`0\lt L`$ のもとで $`i\ \mathrm{div}\ L\lt n\iff i\lt n\,L`$（`Nat.div_lt_iff_lt_mul`）であり、
  仮定 $`i\lt n\,L`$ より従う。
- $`q\lt L`$ : $`0\lt L`$ のとき $`i\bmod L\lt L`$（`Nat.mod_lt`）。
- $`i=k\,L+q`$ : 除法の等式 $`i=L\cdot(i\ \mathrm{div}\ L)+i\bmod L`$ の右辺の積を交換して
  $`i=(i\ \mathrm{div}\ L)\cdot L+i\bmod L=k\,L+q`$。∎

<a id="t-copies_map_length"></a>
### 定理 コピー列の長さ (T.copies_map_length)

**主張** 任意の $`B\in\mathrm{PairSeq}`$、$`f:\mathbb{N}\to(\mathbb{N}\times\mathbb{N})\to(\mathbb{N}\times\mathbb{N})`$、
$`n\in\mathbb{N}`$ に対し

```math
\Bigl\lvert\ \mathrm{flatMap}\bigl(k\mapsto\mathrm{map}\,(f\,k)\,B\bigr)\,(\mathrm{range}(n))\ \Bigr\rvert
= n\,\lvert B\rvert .
```

**証明** $`n`$ に関する帰納法。帰納法の述語は

```math
\Phi(n):\equiv \bigl\lvert\mathrm{flatMap}(k\mapsto\mathrm{map}(f\,k)B)(\mathrm{range}(n))\bigr\rvert=n\lvert B\rvert.
```

**基底段** $`n=0`$。$`\mathrm{range}(0)=[]`$、$`\mathrm{flatMap}`$ の値は $`[]`$、長さは $`0=0\cdot\lvert B\rvert`$。

**帰納段** $`n\to n+1`$。帰納法の仮定は $`\Phi(n)`$。
$`\mathrm{range}(n+1)=\mathrm{range}(n)\mathbin{+\!\!+}[n]`$（`List.range_succ`）であり、
$`\mathrm{flatMap}`$ は連結を連結に写すから

```math
\mathrm{flatMap}(\cdots)(\mathrm{range}(n+1))
=\mathrm{flatMap}(\cdots)(\mathrm{range}(n))\mathbin{+\!\!+}\mathrm{map}(f\,n)\,B .
```

長さは和になるので、$`\Phi(n)`$ と $`\lvert\mathrm{map}(f\,n)B\rvert=\lvert B\rvert`$ より

```math
n\lvert B\rvert+\lvert B\rvert=(n+1)\lvert B\rvert .
```

∎

<a id="t-copies_map_getD"></a>
### 定理 コピー列の成分 (T.copies_map_getD)

**主張** $`k\lt n`$ かつ $`q\lt \lvert B\rvert`$ ならば

```math
\Bigl(\mathrm{flatMap}\bigl(k\mapsto\mathrm{map}(f\,k)B\bigr)(\mathrm{range}(n))\Bigr)\bigl\langle k\lvert B\rvert+q\bigr\rangle
= f\,k\,(B\langle q\rangle).
```

**証明** $`n`$ に関する帰納法（$`k`$ に関する仮定 $`k\lt n`$ ごと一般化する）。帰納法の述語は

```math
\Phi(n):\equiv \Bigl(k<n\ \to\
\bigl(\mathrm{flatMap}(\cdots)(\mathrm{range}(n))\bigr)\langle k\lvert B\rvert+q\rangle=f\,k\,(B\langle q\rangle)\Bigr)
```

（$`q`$ と $`q\lt \lvert B\rvert`$ は固定）。

**基底段** $`n=0`$。前件 $`k\lt 0`$ は偽であるから成立する。

**帰納段** $`n\to n+1`$。帰納法の仮定は $`\Phi(n)`$。
$`F_n:=\mathrm{flatMap}(\cdots)(\mathrm{range}(n))`$ とおく。
$`\mathrm{range}(n+1)=\mathrm{range}(n)\mathbin{+\!\!+}[n]`$（`List.range_succ`）と
$`\mathrm{flatMap}`$ が連結を連結に写すことから

```math
\mathrm{flatMap}(\cdots)(\mathrm{range}(n+1))=F_n\mathbin{+\!\!+}\mathrm{map}(f\,n)B,
```

かつ [(T.copies_map_length)](#t-copies_map_length) より $`\lvert F_n\rvert=n\lvert B\rvert`$。
$`k\lt n+1`$ を仮定し、$`k\lt n`$ か $`k=n`$ かで分ける。

- **$`k\lt n`$ のとき。** 添字は左側に入る。実際

  ```math
  k\lvert B\rvert+q<k\lvert B\rvert+\lvert B\rvert=(k+1)\lvert B\rvert\le n\lvert B\rvert=\lvert F_n\rvert
  ```

  （最後の不等号は $`k+1\le n`$ による）。よって
  [(T.getD_append_left)](#t-getD_append_left) により値は $`F_n\langle k\lvert B\rvert+q\rangle`$ に
  等しく、$`\Phi(n)`$ が結論を与える。
- **$`k=n`$ のとき。** 添字は $`n\lvert B\rvert+q\ge\lvert F_n\rvert`$ であるから
  [(T.getD_append_right)](#t-getD_append_right) により値は
  $`(\mathrm{map}(f\,n)B)\langle n\lvert B\rvert+q-n\lvert B\rvert\rangle=(\mathrm{map}(f\,n)B)\langle q\rangle`$。
  $`q\lt \lvert B\rvert=\lvert\mathrm{map}(f\,n)B\rvert`$ であるから、これは $`f\,n\,(B\langle q\rangle)`$ である。∎

---

## コピー展開のもとでの行 1 の登攀規律

<a id="d-copyExp"></a>
### 定義 コピー展開の形 (D.copyExp)

```math
\mathrm{cE}(G,B,d_0,n) := G\mathbin{+\!\!+}\mathrm{flatMap}\Bigl(k\mapsto\mathrm{map}\bigl(p\mapsto(\pi_0 p+k\,d_0,\ \pi_1 p)\bigr)B\Bigr)\bigl(\mathrm{range}(n)\bigr).
```

これは [(T.oper_bad_blocks)](Mechanized.md#t-oper_bad_blocks) が与える
$`M[n]`$ の形（前置部 $`G`$ の後ろにブロック $`B`$ の $`n`$ 個のコピーが並び、
第 $`k`$ コピーは行 0 が $`k\,d_0`$ だけずれる）そのものである。

<a id="t-copyExp_length"></a>
### 定理 コピー展開の長さ (T.copyExp_length)

**主張** $`\lvert\mathrm{cE}(G,B,d_0,n)\rvert=\lvert G\rvert+n\lvert B\rvert`$。

**証明** 連結の長さは和であり、右側の長さは
[(T.copies_map_length)](#t-copies_map_length) により $`n\lvert B\rvert`$ である。∎

<a id="t-copyExp_getD_pre"></a>
### 定理 前置部の成分 (T.copyExp_getD_pre)

**主張** $`i\lt \lvert G\rvert`$ ならば $`\mathrm{cE}(G,B,d_0,n)\langle i\rangle=G\langle i\rangle`$。

**証明** [(T.getD_append_left)](#t-getD_append_left) そのものである。∎

<a id="t-copyExp_getD_copy"></a>
### 定理 コピー部の成分 (T.copyExp_getD_copy)

**主張** $`k\lt n`$ かつ $`q\lt \lvert B\rvert`$ ならば

```math
\mathrm{cE}(G,B,d_0,n)\bigl\langle \lvert G\rvert+(k\lvert B\rvert+q)\bigr\rangle
=\bigl(\pi_0(B\langle q\rangle)+k\,d_0,\ \pi_1(B\langle q\rangle)\bigr).
```

**証明** 添字は $`\lvert G\rvert`$ 以上であるから
[(T.getD_append_right)](#t-getD_append_right) により、右側の列の第
$`\lvert G\rvert+(k\lvert B\rvert+q)-\lvert G\rvert=k\lvert B\rvert+q`$ 成分に等しい。
[(T.copies_map_getD)](#t-copies_map_getD) を
$`f:=\bigl(k\mapsto p\mapsto(\pi_0 p+k\,d_0,\pi_1 p)\bigr)`$ に適用すれば
値は $`f\,k\,(B\langle q\rangle)=(\pi_0(B\langle q\rangle)+k\,d_0,\ \pi_1(B\langle q\rangle))`$。∎

以下、$`G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp]`$ の形の列を**ホスト**と呼ぶ
（Lean の結合規約により $`(G\mathbin{+\!\!+}B)\mathbin{+\!\!+}[lp]`$ と読む）。

<a id="t-hostM_getD_pre"></a>
### 定理 ホストの前置部成分 (T.hostM_getD_pre)

**主張** $`i\lt \lvert G\rvert`$ ならば $`(G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp])\langle i\rangle=G\langle i\rangle`$。

**証明** $`i\lt \lvert G\rvert\le\lvert G\rvert+\lvert B\rvert=\lvert G\mathbin{+\!\!+}B\rvert`$ であるから
[(T.getD_append_left)](#t-getD_append_left) により値は $`(G\mathbin{+\!\!+}B)\langle i\rangle`$ に等しく、
再び同じ補題（$`i\lt \lvert G\rvert`$）により $`G\langle i\rangle`$ に等しい。∎

<a id="t-hostM_getD_blk"></a>
### 定理 ホストのブロック成分 (T.hostM_getD_blk)

**主張** $`q\lt \lvert B\rvert`$ ならば
$`(G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp])\langle\lvert G\rvert+q\rangle=B\langle q\rangle`$。

**証明** $`\lvert G\rvert+q\lt \lvert G\rvert+\lvert B\rvert=\lvert G\mathbin{+\!\!+}B\rvert`$ であるから
[(T.getD_append_left)](#t-getD_append_left) により値は $`(G\mathbin{+\!\!+}B)\langle\lvert G\rvert+q\rangle`$。
$`\lvert G\rvert\le\lvert G\rvert+q`$ であるから
[(T.getD_append_right)](#t-getD_append_right) によりこれは
$`B\langle\lvert G\rvert+q-\lvert G\rvert\rangle=B\langle q\rangle`$。∎

<a id="t-hostM_length"></a>
### 定理 ホストの長さ (T.hostM_length)

**主張** $`\lvert G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp]\rvert=\lvert G\rvert+\lvert B\rvert+1`$。

**証明** 連結の長さは和であり、$`\lvert[lp]\rvert=1`$。∎

<a id="t-r1ok_copyExp"></a>
### 定理 コピー展開の $`\mathrm{r1ok}`$ (T.r1ok_copyExp)

**主張** 次の 2 条件を仮定する。

1. $`\mathrm{r1ok}(G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp])`$。
2. （$`\mathrm{hmin}`$）$`\forall k\,q`$ について、$`0\lt k`$、$`k\lt n`$、$`q\lt \lvert B\rvert`$、
   $`\bigl(\forall r\lt q,\ \pi_0(B\langle q\rangle)\le\pi_0(B\langle r\rangle)\bigr)`$、
   $`0\lt \pi_0(B\langle q\rangle)+k\,d_0`$ が成り立つならば、$`p`$ が存在して

   ```math
   \begin{aligned}
   &p<\lvert G\rvert+(k\lvert B\rvert+q),\cr
   &\pi_0\bigl(\mathrm{cE}(G,B,d_0,n)\langle p\rangle\bigr)+1=\pi_0(B\langle q\rangle)+k\,d_0,\cr
   &\forall l,\ p<l\to l<\lvert G\rvert+(k\lvert B\rvert+q)\to
     \pi_0(B\langle q\rangle)+k\,d_0\le\pi_0\bigl(\mathrm{cE}(G,B,d_0,n)\langle l\rangle\bigr),\cr
   &\pi_1(B\langle q\rangle)\le\pi_1\bigl(\mathrm{cE}(G,B,d_0,n)\langle p\rangle\bigr)+1 .
   \end{aligned}
   ```

このとき $`\mathrm{r1ok}(\mathrm{cE}(G,B,d_0,n))`$。

**証明** 以下 $`E:=\mathrm{cE}(G,B,d_0,n)`$、$`H:=G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp]`$ と書く。
[(T.copyExp_length)](#t-copyExp_length) より $`\lvert E\rvert=\lvert G\rvert+n\lvert B\rvert`$。
$`j\lt \lvert E\rvert`$ かつ $`0\lt \pi_0(E\langle j\rangle)`$ を仮定し、$`j\lt \lvert G\rvert+\lvert B\rvert`$ か否かで分ける。

**場合 1 : $`j\lt \lvert G\rvert+\lvert B\rvert`$（移送領域）。**

まず次を示す。

```math
\forall i\le j,\qquad E\langle i\rangle=H\langle i\rangle .
\tag{1.1}
```

$`i\le j`$ を取る。

- $`i\lt \lvert G\rvert`$ のとき。[(T.copyExp_getD_pre)](#t-copyExp_getD_pre) より $`E\langle i\rangle=G\langle i\rangle`$、
  [(T.hostM_getD_pre)](#t-hostM_getD_pre) より $`H\langle i\rangle=G\langle i\rangle`$。
- $`\lvert G\rvert\le i`$ のとき。$`i\le j\lt \lvert G\rvert+\lvert B\rvert`$ より $`i-\lvert G\rvert\lt \lvert B\rvert`$。
  また $`0\lt n`$ である。実際 $`n=0`$ ならば $`\lvert E\rvert=\lvert G\rvert`$ となり
  $`\lvert G\rvert\le i\le j\lt \lvert G\rvert`$ という矛盾が生じる。
  $`i=\lvert G\rvert+(0\cdot\lvert B\rvert+(i-\lvert G\rvert))`$ と書き
  [(T.copyExp_getD_copy)](#t-copyExp_getD_copy) を $`k:=0`$ に適用すると

  ```math
  E\langle i\rangle=\bigl(\pi_0(B\langle i-\lvert G\rvert\rangle)+0\cdot d_0,\ \pi_1(B\langle i-\lvert G\rvert\rangle)\bigr)
  =B\langle i-\lvert G\rvert\rangle .
  ```

  一方 [(T.hostM_getD_blk)](#t-hostM_getD_blk) より $`H\langle i\rangle=B\langle i-\lvert G\rvert\rangle`$。

これで (1.1) が示された。[(T.hostM_length)](#t-hostM_length) より
$`j\lt \lvert G\rvert+\lvert B\rvert\lt \lvert H\rvert`$、また (1.1) を $`i:=j`$ に用いて
$`0\lt \pi_0(H\langle j\rangle)`$。仮定 1 の $`\mathrm{r1ok}(H)`$ を $`j`$ に適用して
$`p\lt j`$ と 3 つの条項を得る。$`p\lt j`$ および第 3 条項に現れる $`l\lt j`$ に対して (1.1) が使えるから、
3 条項はそのまま $`E`$ の成分についての主張に書き換わり、$`p`$ が求める証人である。

**場合 2 : $`\lvert G\rvert+\lvert B\rvert\le j`$（コピー領域）。**

まず $`0\lt \lvert B\rvert`$ である。実際 $`\lvert B\rvert=0`$ ならば
$`\lvert E\rvert=\lvert G\rvert`$ となり $`\lvert G\rvert\le j\lt \lvert G\rvert`$ という矛盾が生じる。
$`j-\lvert G\rvert\lt n\lvert B\rvert`$ であるから
[(T.index_decomp)](#t-index_decomp) により $`k\lt n`$、$`q\lt \lvert B\rvert`$、
$`j-\lvert G\rvert=k\lvert B\rvert+q`$ なる $`k,q`$ が取れる。
$`k=0`$ とすると $`j-\lvert G\rvert=q\lt \lvert B\rvert`$ より $`j\lt \lvert G\rvert+\lvert B\rvert`$ となって
場合 2 の仮定に反するから $`0\lt k`$。したがって $`j=\lvert G\rvert+(k\lvert B\rvert+q)`$ であり、
[(T.copyExp_getD_copy)](#t-copyExp_getD_copy) より

```math
E\langle j\rangle=\bigl(\pi_0(B\langle q\rangle)+k\,d_0,\ \pi_1(B\langle q\rangle)\bigr).
```

$`\forall r\lt q,\ \pi_0(B\langle q\rangle)\le\pi_0(B\langle r\rangle)`$ が成り立つか否かで分ける。

- **場合 2-(a)（水準最小）: 成り立つとき。** 仮定 2（$`\mathrm{hmin}`$）を
  $`k,q`$ に適用すればそのまま結論を得る。
- **場合 2-(b)（ブロック内の窪み）: 成り立たないとき。**
  $`r\lt q`$ かつ $`\pi_0(B\langle r\rangle)\lt \pi_0(B\langle q\rangle)`$ なる $`r`$ が取れる。
  特に $`0\lt \pi_0(B\langle q\rangle)`$。
  [(T.hostM_length)](#t-hostM_length) より $`\lvert G\rvert+q\lt \lvert H\rvert`$ であり、
  [(T.hostM_getD_blk)](#t-hostM_getD_blk) より $`H\langle\lvert G\rvert+q\rangle=B\langle q\rangle`$
  であるから $`0\lt \pi_0(H\langle\lvert G\rvert+q\rangle)`$。
  仮定 1 の $`\mathrm{r1ok}(H)`$ を位置 $`\lvert G\rvert+q`$ に適用して $`p\lt \lvert G\rvert+q`$ と

  ```math
  \pi_0(H\langle p\rangle)+1=\pi_0(B\langle q\rangle),\qquad
  \forall l,\ p<l<\lvert G\rvert+q\to\pi_0(B\langle q\rangle)\le\pi_0(H\langle l\rangle),
  ```
  ```math
  \pi_1(B\langle q\rangle)\le\pi_1(H\langle p\rangle)+1
  ```

  を得る。ここで $`\lvert G\rvert+r\le p`$ である。実際 $`p\lt \lvert G\rvert+r`$ とすると、
  $`\lvert G\rvert+r`$ は $`p`$ と $`\lvert G\rvert+q`$ の間にあるから第 2 条項が適用でき、
  [(T.hostM_getD_blk)](#t-hostM_getD_blk) と合わせて
  $`\pi_0(B\langle q\rangle)\le\pi_0(B\langle r\rangle)`$ となり、$`r`$ の取り方に反する。
  よって $`\lvert G\rvert\le p`$ であり、$`p=\lvert G\rvert+r'`$ と書ける。
  $`p\lt \lvert G\rvert+q`$ より $`r'\lt q\lt \lvert B\rvert`$ であり、
  [(T.hostM_getD_blk)](#t-hostM_getD_blk) により上の 3 式は

  ```math
  \pi_0(B\langle r'\rangle)+1=\pi_0(B\langle q\rangle),\qquad
  \pi_1(B\langle q\rangle)\le\pi_1(B\langle r'\rangle)+1
  ```

  と、区間 $`(\lvert G\rvert+r',\ \lvert G\rvert+q)`$ 上の条項に書き換わる。
  そこで証人を $`p^\ast:=\lvert G\rvert+(k\lvert B\rvert+r')`$ とする。

  - $`p^\ast\lt j`$ : $`r'\lt q`$ による。
  - [(T.copyExp_getD_copy)](#t-copyExp_getD_copy) より
    $`\pi_0(E\langle p^\ast\rangle)+1=\pi_0(B\langle r'\rangle)+k\,d_0+1 =\pi_0(B\langle q\rangle)+k\,d_0=\pi_0(E\langle j\rangle)`$。
  - 第 3 条項 : $`p^\ast\lt l\lt j`$ とすると
    $`\lvert G\rvert+k\lvert B\rvert+r'\lt l\lt \lvert G\rvert+k\lvert B\rvert+q`$ であるから、
    $`rr:=l-\lvert G\rvert-k\lvert B\rvert`$ とおくと $`r'\lt rr\lt q`$ かつ
    $`l=\lvert G\rvert+(k\lvert B\rvert+rr)`$。
    [(T.copyExp_getD_copy)](#t-copyExp_getD_copy) より
    $`\pi_0(E\langle l\rangle)=\pi_0(B\langle rr\rangle)+k\,d_0`$。
    ホスト側の第 2 条項を $`l:=\lvert G\rvert+rr`$（これは $`p=\lvert G\rvert+r'`$ と
    $`\lvert G\rvert+q`$ の間にある）に適用し
    [(T.hostM_getD_blk)](#t-hostM_getD_blk) で書き換えると
    $`\pi_0(B\langle q\rangle)\le\pi_0(B\langle rr\rangle)`$。両辺に $`k\,d_0`$ を加えて
    $`\pi_0(E\langle j\rangle)\le\pi_0(E\langle l\rangle)`$。
  - 第 4 条項 : [(T.copyExp_getD_copy)](#t-copyExp_getD_copy) より
    $`\pi_1(E\langle p^\ast\rangle)=\pi_1(B\langle r'\rangle)`$、$`\pi_1(E\langle j\rangle)=\pi_1(B\langle q\rangle)`$
    であるから、ホスト側の第 3 式がそのまま
    $`\pi_1(E\langle j\rangle)\le\pi_1(E\langle p^\ast\rangle)+1`$ を与える。∎

---

## 前コピーの証人 : $`q=0`$ への退化と $`d_0=0`$ の場合

<a id="t-getD_mem"></a>
### 定理 範囲内の成分は要素である (T.getD_mem)

**主張** $`i\lt \lvert l\rvert`$ ならば $`l\langle i\rangle\in l`$。

**証明** $`i\lt \lvert l\rvert`$ のとき $`\mathrm{getD}`$ は既定値を返さず、$`l`$ の第 $`i`$ 要素を返す。
第 $`i`$ 要素はリストの要素である（`List.getElem_mem`）。∎

<a id="t-dominated_PM_zero"></a>
### 定理 支配ブロックでは水準最小位置は $`0`$ のみ (T.dominated_PM_zero)

**主張** $`B:=(v_0,w_0)\mathbin{::}R`$ とし、$`\forall x\in R,\ v_0\lt \pi_0 x`$ を仮定する。
$`q\lt \lvert B\rvert`$ かつ $`\forall r\lt q,\ \pi_0(B\langle q\rangle)\le\pi_0(B\langle r\rangle)`$ ならば $`q=0`$。

**証明** $`q\ne0`$ と仮定して矛盾を導く。$`q=q'+1`$ と書ける。
$`q\lt \lvert B\rvert=\lvert R\rvert+1`$ より $`q'\lt \lvert R\rvert`$ であるから、
[(T.getD_mem)](#t-getD_mem) より $`R\langle q'\rangle\in R`$、
したがって仮定より $`v_0\lt \pi_0(R\langle q'\rangle)`$。
一方、水準最小性の仮定を $`r:=0`$ に適用すると
$`\pi_0(B\langle q\rangle)\le\pi_0(B\langle 0\rangle)`$ であり、
$`B\langle 0\rangle=(v_0,w_0)`$、$`B\langle q'+1\rangle=R\langle q'\rangle`$ であるから

```math
\pi_0(R\langle q'\rangle)\le v_0 .
```

これは $`v_0\lt \pi_0(R\langle q'\rangle)`$ と矛盾する。∎

<a id="t-r1ok_min_d0zero"></a>
### 定理 $`d_0=0`$ の場合の前コピー証人 (T.r1ok_min_d0zero)

**主張** $`B=(v_0,w_0)\mathbin{::}R`$、$`\forall x\in R,\ v_0\lt \pi_0 x`$、
$`\mathrm{r1ok}(G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp])`$ を仮定する。
さらに $`0\lt k`$、$`k\lt n`$、$`q\lt \lvert B\rvert`$、
$`\forall r\lt q,\ \pi_0(B\langle q\rangle)\le\pi_0(B\langle r\rangle)`$、
$`0\lt \pi_0(B\langle q\rangle)+k\cdot0`$ を仮定する。
このとき [(T.r1ok_copyExp)](#t-r1ok_copyExp) の仮定 2 の結論（$`d_0:=0`$ とした形）が成り立つ。
すなわち $`p`$ が存在して

```math
\begin{aligned}
&p<\lvert G\rvert+(k\lvert B\rvert+q),\cr
&\pi_0\bigl(\mathrm{cE}(G,B,0,n)\langle p\rangle\bigr)+1=\pi_0(B\langle q\rangle)+k\cdot0,\cr
&\forall l,\ p<l\to l<\lvert G\rvert+(k\lvert B\rvert+q)\to
  \pi_0(B\langle q\rangle)+k\cdot0\le\pi_0\bigl(\mathrm{cE}(G,B,0,n)\langle l\rangle\bigr),\cr
&\pi_1(B\langle q\rangle)\le\pi_1\bigl(\mathrm{cE}(G,B,0,n)\langle p\rangle\bigr)+1 .
\end{aligned}
```

**証明** $`E:=\mathrm{cE}(G,B,0,n)`$、$`H:=G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp]`$ とおく。
[(T.dominated_PM_zero)](#t-dominated_PM_zero) より $`q=0`$。
$`B\langle0\rangle=(v_0,w_0)`$ であるから、仮定 $`0\lt \pi_0(B\langle0\rangle)+k\cdot0=v_0`$ より $`0\lt v_0`$。

[(T.hostM_getD_blk)](#t-hostM_getD_blk) を $`q:=0`$ に適用して
$`H\langle\lvert G\rvert\rangle=B\langle0\rangle=(v_0,w_0)`$。
[(T.hostM_length)](#t-hostM_length) より $`\lvert G\rvert\lt \lvert H\rvert`$、
かつ $`0\lt \pi_0(H\langle\lvert G\rvert\rangle)=v_0`$。
$`\mathrm{r1ok}(H)`$ を位置 $`\lvert G\rvert`$ に適用して $`p\lt \lvert G\rvert`$ と

```math
\pi_0(H\langle p\rangle)+1=v_0,\qquad
\forall l,\ p<l<\lvert G\rvert\to v_0\le\pi_0(H\langle l\rangle),\qquad
w_0\le\pi_1(H\langle p\rangle)+1
```

を得る。$`p\lt \lvert G\rvert`$ であるから
[(T.hostM_getD_pre)](#t-hostM_getD_pre) より $`H\langle p\rangle=G\langle p\rangle`$、
[(T.copyExp_getD_pre)](#t-copyExp_getD_pre) より $`E\langle p\rangle=G\langle p\rangle`$。
すなわち

```math
\pi_0(G\langle p\rangle)+1=v_0,\qquad w_0\le\pi_1(G\langle p\rangle)+1 .
\tag{$\ast$}
```

この $`p`$ が求める証人である。

- $`p\lt \lvert G\rvert\le\lvert G\rvert+(k\lvert B\rvert+0)`$。
- $`\pi_0(E\langle p\rangle)+1=\pi_0(G\langle p\rangle)+1=v_0=v_0+k\cdot0`$（$`(\ast)`$）。
- 第 3 条項 : $`p\lt l\lt \lvert G\rvert+k\lvert B\rvert`$ とし、$`v_0+k\cdot0=v_0\le\pi_0(E\langle l\rangle)`$ を示す。
  - $`l\lt \lvert G\rvert`$ のとき。ホスト側の第 2 条項と
    [(T.hostM_getD_pre)](#t-hostM_getD_pre) より $`v_0\le\pi_0(G\langle l\rangle)`$、
    [(T.copyExp_getD_pre)](#t-copyExp_getD_pre) より $`\pi_0(E\langle l\rangle)=\pi_0(G\langle l\rangle)`$。
  - $`\lvert G\rvert\le l`$ のとき。$`k\lt n`$ より $`k\lvert B\rvert\le n\lvert B\rvert`$ であるから
    $`l-\lvert G\rvert\lt k\lvert B\rvert\le n\lvert B\rvert`$。
    [(T.index_decomp)](#t-index_decomp)（$`0\lt \lvert B\rvert`$ は $`B=(v_0,w_0)\mathbin{::}R`$ による）
    により $`k'\lt n`$、$`r\lt \lvert B\rvert`$、$`l=\lvert G\rvert+(k'\lvert B\rvert+r)`$ と書ける。
    [(T.copyExp_getD_copy)](#t-copyExp_getD_copy) より
    $`\pi_0(E\langle l\rangle)=\pi_0(B\langle r\rangle)+k'\cdot0=\pi_0(B\langle r\rangle)`$。
    $`r=0`$ のとき $`\pi_0(B\langle0\rangle)=v_0`$、$`r=r''+1`$ のとき
    $`B\langle r\rangle=R\langle r''\rangle\in R`$（[(T.getD_mem)](#t-getD_mem)）より
    $`v_0\lt \pi_0(B\langle r\rangle)`$。いずれも $`v_0\le\pi_0(E\langle l\rangle)`$。
- 第 4 条項 : $`\pi_1(B\langle0\rangle)=w_0`$、$`\pi_1(E\langle p\rangle)=\pi_1(G\langle p\rangle)`$ であるから、
  $`(\ast)`$ の第 2 式がそのまま $`w_0\le\pi_1(E\langle p\rangle)+1`$ を与える。∎

<a id="t-r1ok_min_d0pos"></a>
### 定理 $`d_0\ge1`$ の場合の前コピー証人 (T.r1ok_min_d0pos)

**主張** 次を仮定する。

- $`B=(v_0,w_0)\mathbin{::}R`$、$`\forall x\in R,\ v_0\lt \pi_0 x`$；
- $`0\lt d_0`$、$`\pi_0\,lp=v_0+d_0`$；
- （$`\mathrm{hstep}`$）$`\forall r,\ r+1\lt \lvert B\rvert\to\pi_0(B\langle r+1\rangle)\le\pi_0(B\langle r\rangle)+1`$；
- （$`\mathrm{hlpstep}`$）$`\pi_0\,lp\le\pi_0(B\langle\lvert B\rvert-1\rangle)+1`$；
- （$`\mathrm{hclimb}`$）$`\forall r'\lt \lvert B\rvert`$ について、$`\pi_0(B\langle r'\rangle)=v_0+d_0-1`$ かつ
  $`\bigl(\forall rr,\ r'\lt rr\lt \lvert B\rvert\to v_0+d_0\le\pi_0(B\langle rr\rangle)\bigr)`$ ならば
  $`w_0\le\pi_1(B\langle r'\rangle)+1`$；
- $`0\lt k`$、$`k\lt n`$、$`q\lt \lvert B\rvert`$、
  $`\forall r\lt q,\ \pi_0(B\langle q\rangle)\le\pi_0(B\langle r\rangle)`$、
  $`0\lt \pi_0(B\langle q\rangle)+k\,d_0`$。

このとき [(T.r1ok_copyExp)](#t-r1ok_copyExp) の仮定 2 の結論が成り立つ。すなわち $`p`$ が存在して

```math
\begin{aligned}
&p<\lvert G\rvert+(k\lvert B\rvert+q),\cr
&\pi_0\bigl(\mathrm{cE}(G,B,d_0,n)\langle p\rangle\bigr)+1=\pi_0(B\langle q\rangle)+k\,d_0,\cr
&\forall l,\ p<l\to l<\lvert G\rvert+(k\lvert B\rvert+q)\to
  \pi_0(B\langle q\rangle)+k\,d_0\le\pi_0\bigl(\mathrm{cE}(G,B,d_0,n)\langle l\rangle\bigr),\cr
&\pi_1(B\langle q\rangle)\le\pi_1\bigl(\mathrm{cE}(G,B,d_0,n)\langle p\rangle\bigr)+1 .
\end{aligned}
```

**証明** $`E:=\mathrm{cE}(G,B,d_0,n)`$ とおく。
[(T.dominated_PM_zero)](#t-dominated_PM_zero) より $`q=0`$。
$`B=(v_0,w_0)\mathbin{::}R`$ より $`0\lt \lvert B\rvert`$ かつ $`B\langle0\rangle=(v_0,w_0)`$。

**証人位置の選択.** 述語 $`P(r):\iff \pi_0(B\langle r\rangle)\le v_0+d_0-1`$ を考える。
$`\pi_0(B\langle0\rangle)=v_0\le v_0+d_0-1`$（$`0\lt d_0`$ による）であるから $`P(0)`$。
$`r':=\mathrm{findGreatest}\,P\,(\lvert B\rvert-1)`$ とおくと、$`0\le\lvert B\rvert-1`$ と $`P(0)`$ から
$`P(r')`$、また $`r'\le\lvert B\rvert-1`$、さらに

```math
\forall rr,\ r'<rr\le\lvert B\rvert-1\ \Rightarrow\ \neg P(rr).
```

$`\neg P(rr)`$ は $`v_0+d_0-1\lt \pi_0(B\langle rr\rangle)`$ であり、$`0\lt d_0`$ より
$`v_0+d_0-1+1=v_0+d_0`$ であるから

```math
\forall rr,\ r'<rr<\lvert B\rvert\ \Rightarrow\ v_0+d_0\le\pi_0(B\langle rr\rangle).
\tag{2.1}
```

**水準の一致.** $`\pi_0(B\langle r'\rangle)=v_0+d_0-1`$ を示す。$`P(r')`$ より
$`\pi_0(B\langle r'\rangle)\le v_0+d_0-1`$ である。逆向きを示す。

- $`r'\lt \lvert B\rvert-1`$ のとき。$`\neg P(r'+1)`$ より $`v_0+d_0-1\lt \pi_0(B\langle r'+1\rangle)`$。
  $`\mathrm{hstep}`$ を $`r:=r'`$ に適用して $`\pi_0(B\langle r'+1\rangle)\le\pi_0(B\langle r'\rangle)+1`$。
  合わせて $`v_0+d_0-1\lt \pi_0(B\langle r'\rangle)+1`$、すなわち
  $`v_0+d_0-1\le\pi_0(B\langle r'\rangle)`$。
- $`r'=\lvert B\rvert-1`$ のとき。$`\mathrm{hlpstep}`$ と $`\pi_0\,lp=v_0+d_0`$ より
  $`v_0+d_0\le\pi_0(B\langle\lvert B\rvert-1\rangle)+1`$、すなわち
  $`v_0+d_0-1\le\pi_0(B\langle r'\rangle)`$。

いずれの場合も $`\pi_0(B\langle r'\rangle)=v_0+d_0-1`$。 $`(2.2)`$ とおく。

**乗算の整理.** $`0\lt k`$ であるから

```math
k\lvert B\rvert=(k-1)\lvert B\rvert+\lvert B\rvert,\qquad k\,d_0=(k-1)d_0+d_0,\qquad k-1<n .
```

（$`k=m+1`$ と書けば $`(m+1)L=mL+L`$ による。$`k-1\lt k\lt n`$。）
また $`r'\le\lvert B\rvert-1`$ と $`0\lt \lvert B\rvert`$ より $`r'\lt \lvert B\rvert`$。

**証人.** $`p^\ast:=\lvert G\rvert+((k-1)\lvert B\rvert+r')`$ とする。

- $`p^\ast\lt \lvert G\rvert+(k\lvert B\rvert+0)`$ : $`r'\lt \lvert B\rvert`$ より
  $`(k-1)\lvert B\rvert+r'\lt (k-1)\lvert B\rvert+\lvert B\rvert=k\lvert B\rvert`$。
- [(T.copyExp_getD_copy)](#t-copyExp_getD_copy)（$`k-1\lt n`$、$`r'\lt \lvert B\rvert`$）と $`(2.2)`$ より

  ```math
  \pi_0(E\langle p^\ast\rangle)+1=\pi_0(B\langle r'\rangle)+(k-1)d_0+1
  =(v_0+d_0-1)+(k-1)d_0+1=v_0+d_0+(k-1)d_0=v_0+k\,d_0,
  ```

  これは $`\pi_0(B\langle 0\rangle)+k\,d_0`$ に等しい（$`0\lt d_0`$ より $`v_0+d_0-1+1=v_0+d_0`$）。
- 第 3 条項 : $`p^\ast\lt l\lt \lvert G\rvert+k\lvert B\rvert`$ とする。
  $`k\lt n`$ より $`l-\lvert G\rvert\lt k\lvert B\rvert\le n\lvert B\rvert`$ であるから
  [(T.index_decomp)](#t-index_decomp) により $`k''\lt n`$、$`rr\lt \lvert B\rvert`$、
  $`l-\lvert G\rvert=k''\lvert B\rvert+rr`$ と書ける。まず $`k''=k-1`$ を示す。
  - $`k''\lt k-1`$ とすると $`k''+1\le k-1`$ より $`(k''+1)\lvert B\rvert\le(k-1)\lvert B\rvert`$、
    すなわち $`k''\lvert B\rvert+\lvert B\rvert\le(k-1)\lvert B\rvert`$。
    したがって $`l-\lvert G\rvert=k''\lvert B\rvert+rr\lt k''\lvert B\rvert+\lvert B\rvert\le(k-1)\lvert B\rvert\le(k-1)\lvert B\rvert+r'`$
    となり、$`p^\ast\lt l`$ に反する。
  - $`k-1\lt k''`$ とすると $`k\le k''`$ より $`k\lvert B\rvert\le k''\lvert B\rvert\le l-\lvert G\rvert`$ となり、
    $`l\lt \lvert G\rvert+k\lvert B\rvert`$ に反する。

  よって $`k''=k-1`$ であり、$`p^\ast\lt l`$ から $`r'\lt rr`$。
  [(T.copyExp_getD_copy)](#t-copyExp_getD_copy) より
  $`\pi_0(E\langle l\rangle)=\pi_0(B\langle rr\rangle)+(k-1)d_0`$。
  $`(2.1)`$ を $`rr`$ に適用して $`v_0+d_0\le\pi_0(B\langle rr\rangle)`$、よって

  ```math
  \pi_0(B\langle0\rangle)+k\,d_0=v_0+k\,d_0=(v_0+d_0)+(k-1)d_0\le\pi_0(B\langle rr\rangle)+(k-1)d_0
  =\pi_0(E\langle l\rangle).
  ```
- 第 4 条項 : [(T.copyExp_getD_copy)](#t-copyExp_getD_copy) より
  $`\pi_1(E\langle p^\ast\rangle)=\pi_1(B\langle r'\rangle)`$、また $`\pi_1(B\langle0\rangle)=w_0`$。
  $`\mathrm{hclimb}`$ を $`r'`$（$`r'\lt \lvert B\rvert`$、$`(2.2)`$、$`(2.1)`$）に適用して
  $`w_0\le\pi_1(B\langle r'\rangle)+1`$、すなわち
  $`\pi_1(B\langle 0\rangle)\le\pi_1(E\langle p^\ast\rangle)+1`$。∎

---

## 組み立て : $`\mathrm{r1ok}`$ は $`\mathrm{oper}`$ で保たれ、$`\mathrm{ST\_PS}`$ 上で成り立つ

<a id="t-hostM_getD_lp"></a>
### 定理 ホストの最終列 (T.hostM_getD_lp)

**主張** $`(G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp])\langle\lvert G\rvert+\lvert B\rvert\rangle=lp`$。

**証明** $`\lvert G\mathbin{+\!\!+}B\rvert=\lvert G\rvert+\lvert B\rvert`$ であるから、
[(T.getD_append_right)](#t-getD_append_right) により値は
$`[lp]\langle\lvert G\rvert+\lvert B\rvert-(\lvert G\rvert+\lvert B\rvert)\rangle=[lp]\langle0\rangle=lp`$。∎

<a id="t-r1ok_Pred"></a>
### 定理 $`\mathrm{r1ok}`$ は $`\mathrm{Pred}`$ で保存される (T.r1ok_Pred)

**主張** $`\mathrm{r1ok}(M)`$ ならば $`\mathrm{r1ok}(\mathrm{Pred}\,M)`$（[(D.Pred)](Def.md#d-Pred)）。

**証明** [(D.Pred)](Def.md#d-Pred) の定義により場合分けする。
$`\lvert M\rvert\le1`$ のとき $`\mathrm{Pred}\,M=M`$ であるから仮定そのもの。
$`\lvert M\rvert\gt 1`$ のとき $`\mathrm{Pred}\,M=\mathrm{dropLast}\,M`$ であるから
[(T.r1ok_dropLast)](#t-r1ok_dropLast) による。∎

<a id="t-climb_bound"></a>
### 定理 登攀限界 (T.climb_bound)

**主張** $`M=G\mathbin{+\!\!+}((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}[lp]`$、$`B:=(v_0,w_0)\mathbin{::}R`$ とし、

- $`0\lt d_0`$、$`\pi_0\,lp=v_0+d_0`$、$`w_0\lt \pi_1\,lp`$、
- $`\mathrm{nextrel1}\,M\,\lvert G\rvert\,(\lvert M\rvert-1)`$、すなわち
  $`\lvert G\rvert\to^M_1(\lvert M\rvert-1)`$（[(D.nextrel1)](Def.md#d-nextrel1)）、
- $`r'\lt \lvert B\rvert`$、$`\pi_0(B\langle r'\rangle)=v_0+d_0-1`$、
- $`\forall rr,\ r'\lt rr\lt \lvert B\rvert\to v_0+d_0\le\pi_0(B\langle rr\rangle)`$

を仮定する。このとき $`w_0\le\pi_1(B\langle r'\rangle)+1`$。

**証明** $`r'=0`$ か $`r'\gt 0`$ かで分ける。

**$`r'=0`$ のとき。** $`B\langle0\rangle=(v_0,w_0)`$ であるから目標は $`w_0\le w_0+1`$ であり、成り立つ。

**$`0\lt r'`$ のとき。** [(T.hostM_length)](#t-hostM_length) より
$`\lvert M\rvert=\lvert G\rvert+\lvert B\rvert+1`$、したがって
$`j_1:=\lvert M\rvert-1=\lvert G\rvert+\lvert B\rvert`$。
[(D.entry)](Def.md#d-entry)、[(T.hostM_getD_blk)](#t-hostM_getD_blk)、
[(T.hostM_getD_lp)](#t-hostM_getD_lp) より

```math
M_{0,\ \lvert G\rvert+r'}=\pi_0(B\langle r'\rangle)=v_0+d_0-1,\qquad
M_{0,\ j_1}=\pi_0\,lp=v_0+d_0 .
\tag{3.1}
```

**主張 A : $`(\lvert G\rvert+r')\to^M_0 j_1`$**（[(D.nextrel0)](Def.md#d-nextrel0)）。
5 つの条件を順に確かめる。

1. $`\lvert G\rvert+r'\lt \lvert M\rvert`$ : $`r'\lt \lvert B\rvert`$ と $`\lvert M\rvert=\lvert G\rvert+\lvert B\rvert+1`$ による。
2. $`j_1\lt \lvert M\rvert`$ : $`j_1=\lvert M\rvert-1`$ と $`\lvert M\rvert\ge1`$ による。
3. $`\lvert G\rvert+r'\lt j_1=\lvert G\rvert+\lvert B\rvert`$ : $`r'\lt \lvert B\rvert`$ による。
4. $`M_{0,\lvert G\rvert+r'}\lt M_{0,j_1}`$ : $`(3.1)`$ と $`0\lt d_0`$ より $`v_0+d_0-1\lt v_0+d_0`$。
5. $`\lvert G\rvert+r'\lt j\lt j_1`$ なる $`j`$ について $`M_{0,j_1}\le M_{0,j}`$ :
   そのような $`j`$ は $`j=\lvert G\rvert+rr`$（$`r'\lt rr\lt \lvert B\rvert`$）と書け、
   [(T.hostM_getD_blk)](#t-hostM_getD_blk) より $`M_{0,j}=\pi_0(B\langle rr\rangle)`$。
   仮定の最後の条項より $`v_0+d_0\le\pi_0(B\langle rr\rangle)`$ であり、$`(3.1)`$ より
   $`M_{0,j_1}=v_0+d_0`$。

**主張 B : $`(\lvert G\rvert+r')\le^M_0 j_1`$**（[(D.le0)](Def.md#d-le0)）。
主張 A の 1 歩の連鎖を反射推移閉包の 1 歩として取り、長さの条件は主張 A の 1, 2 による。

**結論.** 仮定 $`\lvert G\rvert\to^M_1 j_1`$ の第 6 条項（[(D.nextrel1)](Def.md#d-nextrel1) の
最大性条項）を $`j:=\lvert G\rvert+r'`$ に適用する。その前提は
$`\lvert G\rvert\lt \lvert G\rvert+r'`$（$`0\lt r'`$ による）と主張 B であり、結論は

```math
M_{1,j_1}\le M_{1,\ \lvert G\rvert+r'} .
```

[(D.entry)](Def.md#d-entry) と [(T.hostM_getD_lp)](#t-hostM_getD_lp),
[(T.hostM_getD_blk)](#t-hostM_getD_blk) により
$`M_{1,j_1}=\pi_1\,lp`$、$`M_{1,\lvert G\rvert+r'}=\pi_1(B\langle r'\rangle)`$ であるから

```math
\pi_1\,lp\le\pi_1(B\langle r'\rangle).
```

仮定 $`w_0\lt \pi_1\,lp`$ と合わせて $`w_0\lt \pi_1(B\langle r'\rangle)`$、
したがって $`w_0\le\pi_1(B\langle r'\rangle)+1`$。∎

<a id="t-r1ok_oper"></a>
### 定理 $`\mathrm{r1ok}`$ は展開で保たれる (T.r1ok_oper)

**主張** $`1\le n`$、$`\mathrm{r1ok}(M)`$、$`\mathrm{steps1}(M)`$（[(D.steps1)](Seqlex.md#d-steps1)）ならば
$`\mathrm{r1ok}(M[n])`$。

**証明** [(D.oper)](Def.md#d-oper) の 4 分岐で場合分けする。$`j_1:=\lvert M\rvert-1`$ とおく。

- **分岐 (a) : $`j_1=0`$。** [(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) より
  $`M[n]=M`$ であるから、仮定 $`\mathrm{r1ok}(M)`$ がそのまま結論である。
- **分岐 (b) : $`j_1\ne0`$ かつ $`M_{0,j_1}=0\wedge M_{1,j_1}=0`$。**
  [(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero) より $`M[n]=\mathrm{Pred}\,M`$ であり、
  [(T.r1ok_Pred)](#t-r1ok_Pred) による。
- **分岐 (c) : $`j_1\ne0`$、$`\neg(M_{0,j_1}=0\wedge M_{1,j_1}=0)`$、
  $`\neg\,\mathrm{hasParent}(M,\mathrm{idx}_1(M,j_1),j_1)`$。**
  [(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent) より
  $`M[n]=\mathrm{Pred}\,M`$ であり、[(T.r1ok_Pred)](#t-r1ok_Pred) による。
- **分岐 (d) : 残りの場合。** $`j_1\ne0`$ より $`1\lt \lvert M\rvert`$。
  [(T.oper_bad_blocks)](Mechanized.md#t-oper_bad_blocks) を適用して
  $`G,v_0,w_0,R,d_0,lp`$ を取る。$`B:=(v_0,w_0)\mathbin{::}R`$ とおくと

  ```math
  M=G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp],\qquad M[n]=\mathrm{cE}(G,B,d_0,n),
  ```

  ```math
  \forall x\in R,\ v_0<\pi_0 x,\qquad v_0<\pi_0\,lp,
  ```

  かつ次の選言が成り立つ。

  ```math
  \bigl(d_0=0\ \wedge\ \mathrm{idx}_1(M,j_1)=0\bigr)\ \vee\
  \bigl(0<d_0\ \wedge\ w_0<\pi_1\,lp\ \wedge\ \pi_0\,lp=v_0+d_0\ \wedge\ \lvert G\rvert\to^M_1 j_1\bigr).
  ```

  仮定 $`\mathrm{r1ok}(M)`$、$`\mathrm{steps1}(M)`$ を $`M=G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp]`$ の形に書き換える。

  **$`\mathrm{hstep}`$ の導出.** $`r+1\lt \lvert B\rvert`$ とする。
  [(T.steps1_iff)](Seqlex.md#t-steps1_iff) をホストと添字 $`\lvert G\rvert+r`$ に適用する。
  適用条件 $`\lvert G\rvert+r+1\lt \lvert M\rvert=\lvert G\rvert+\lvert B\rvert+1`$ は $`r+1\lt \lvert B\rvert`$ による。
  結論は $`\pi_0(M\langle\lvert G\rvert+r+1\rangle)\le\pi_0(M\langle\lvert G\rvert+r\rangle)+1`$ であり、
  $`\lvert G\rvert+r+1=\lvert G\rvert+(r+1)`$ と [(T.hostM_getD_blk)](#t-hostM_getD_blk) により

  ```math
  \pi_0(B\langle r+1\rangle)\le\pi_0(B\langle r\rangle)+1 .
  ```

  **$`\mathrm{hlpstep}`$ の導出.** [(T.steps1_iff)](Seqlex.md#t-steps1_iff) を添字
  $`\lvert G\rvert+(\lvert B\rvert-1)`$ に適用する。$`0\lt \lvert B\rvert`$ であるから
  $`\lvert G\rvert+(\lvert B\rvert-1)+1=\lvert G\rvert+\lvert B\rvert\lt \lvert M\rvert`$。
  結論の左辺は [(T.hostM_getD_lp)](#t-hostM_getD_lp) により $`\pi_0\,lp`$、
  右辺は [(T.hostM_getD_blk)](#t-hostM_getD_blk) により
  $`\pi_0(B\langle\lvert B\rvert-1\rangle)+1`$ である。

  そこで [(T.r1ok_copyExp)](#t-r1ok_copyExp) を適用する。仮定 1 は上の書き換えで得ている。
  仮定 2（$`\mathrm{hmin}`$）は上の選言で分けて与える。

  - 第 1 選言（$`d_0=0`$）のとき : [(T.r1ok_min_d0zero)](#t-r1ok_min_d0zero) による。
  - 第 2 選言（$`0\lt d_0`$）のとき : [(T.r1ok_min_d0pos)](#t-r1ok_min_d0pos) による。
    その仮定 $`\mathrm{hclimb}`$ は [(T.climb_bound)](#t-climb_bound) が与える
    （$`M=G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp]`$、$`0\lt d_0`$、$`\pi_0\,lp=v_0+d_0`$、$`w_0\lt \pi_1\,lp`$、
    $`\lvert G\rvert\to^M_1 j_1`$ はすべて第 2 選言に含まれている）。∎

<a id="t-r1ok_ST_PS"></a>
### 定理 標準形は $`\mathrm{r1ok}`$ (T.r1ok_ST_PS)

**主張** $`M\in\mathrm{ST\_PS}`$（[(D.ST_PS)](Def.md#d-ST_PS)）ならば $`\mathrm{r1ok}(M)`$。

**証明** $`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M):\equiv \mathrm{r1ok}(M).
```

**基底段（規則 diag）** $`M=\Delta_0^v`$。[(T.r1ok_diagSeq)](#t-r1ok_diagSeq) により $`\Phi(\Delta_0^v)`$。

**帰納段（規則 oper）** $`M=N[n]`$、ただし $`N\in\mathrm{ST\_PS}`$、$`1\le n`$。
帰納法の仮定は $`\Phi(N)`$、すなわち $`\mathrm{r1ok}(N)`$ である。
[(T.blockok_ST_PS)](Seqlex.md#t-blockok_ST_PS) を $`N\in\mathrm{ST\_PS}`$ に適用すると
$`\mathrm{blockok}\,0\,N`$（[(D.blockok)](Seqlex.md#d-blockok)）が得られ、
その第 3 成分が $`\mathrm{steps1}(N)`$ である。
[(T.r1ok_oper)](#t-r1ok_oper) を $`1\le n`$、$`\mathrm{r1ok}(N)`$、$`\mathrm{steps1}(N)`$ に適用して
$`\mathrm{r1ok}(N[n])`$、すなわち $`\Phi(M)`$。∎

---

## 構造層 : 末尾付加の $`\mathrm{einc}\cup\mathrm{eflip}`$ 特徴づけ

Lean の当該節見出しはこの節の意図（末尾付加が正規化像に対して
「末端位置の 1 箇所増加」を行うこと）を述べるコメントであり、
以下の 4 宣言はそのための語彙である。

<a id="d-hdarg"></a>
### 定義 先頭引数 (D.hdarg)

```math
\mathrm{hdarg}\,\mathsf Z := \mathsf Z,\qquad \mathrm{hdarg}\,\mathsf P(a,b,c) := b .
```

<a id="t-hdarg_Z"></a>
### 定理 $`\mathrm{hdarg}\,\mathsf Z=\mathsf Z`$ (T.hdarg_Z)

**主張** $`\mathrm{hdarg}\,\mathsf Z=\mathsf Z`$。

**証明** [(D.hdarg)](#d-hdarg) の第 1 式である。∎

<a id="t-hdarg_P"></a>
### 定理 $`\mathrm{hdarg}\,\mathsf P(a,b,c)=b`$ (T.hdarg_P)

**主張** $`\mathrm{hdarg}\,\mathsf P(a,b,c)=b`$。

**証明** [(D.hdarg)](#d-hdarg) の第 2 式である。∎

<a id="d-noabsorb"></a>
### 定義 非吸収条件 (D.noabsorb)

```math
\mathrm{noabsorb}(a,b,t) :\iff
\neg\bigl(a<\mathrm{lead}\,t\ \vee\ (a=\mathrm{lead}\,t\ \wedge\ b\prec\mathrm{hdarg}\,t)\bigr)
```

（[(D.lead)](Mechanized.md#d-lead), [(D.hdarg)](#d-hdarg)）。
$`t=\mathsf P(e,f,g)`$ のとき $`\mathrm{lead}\,t=e`$、$`\mathrm{hdarg}\,t=f`$ であるから、
これは [(D.ins)](Nrm.md#d-ins) の分岐条件
$`\bigl(a\lt e\vee(a=e\wedge b\prec f)\bigr)`$ の否定に一致する。すなわち
$`\mathrm{noabsorb}(a,b,t)`$ のとき $`\mathrm{ins}_a(b,t)=\mathsf P(a,b,t)`$ である
（$`t=\mathsf Z`$ のときは $`\mathrm{lead}\,\mathsf Z=0`$、$`\mathrm{hdarg}\,\mathsf Z=\mathsf Z`$ であるから
$`a\lt 0`$ も $`b\prec\mathsf Z`$ も成り立たず、$`\mathrm{noabsorb}(a,b,\mathsf Z)`$ は常に真であり、
[(T.ins_Z)](Nrm.md#t-ins_Z) より $`\mathrm{ins}_a(b,\mathsf Z)=\mathsf P(a,b,\mathsf Z)`$）。
本章の他の宣言はこの述語を用いない。

---

## 射影は発火項の上で一段である

<a id="t-maxo_bad_nofire"></a>
### 定理 違反者の $`\mathrm{maxo}`$ は発火しない (T.maxo_bad_nofire)

**主張** $`\mathrm{Bad}_u(b)\ne[]`$ ならば $`\neg\,\mathrm{fire}_u\bigl(\mathrm{mx}_u(b)\bigr)`$。

**証明** $`m:=\mathrm{mx}_u(b)`$ とおく。
[(T.maxo_hdtl_in)](Nrm.md#t-maxo_hdtl_in) より $`m\in\mathrm{Bad}_u(b)`$ であるから、
[(T.mem_filter_Gterm)](#t-mem_filter_Gterm) より $`m\in G_u(b)`$、
[(T.mem_filter_not_olt)](#t-mem_filter_not_olt) より $`\neg(m\prec b)`$。
[(T.olt_total)](Mechanized.md#t-olt_total) を $`b`$ と $`m`$ に適用すると
$`b\prec m`$、$`b=m`$、$`m\prec b`$ のいずれかであり、第 3 は上で否定したから

```math
b\preceq m .
\tag{4.1}
```

[(T.pfire_iff)](#t-pfire_iff) により、示すべきは
$`\forall g\in G_u(m),\ g\prec m`$ である。$`g\in G_u(m)`$ を取る。

- [(T.Gterm_trans)](#t-Gterm_trans) を $`g\in G_u(m)`$ と $`m\in G_u(b)`$ に適用して $`g\in G_u(b)`$。
- [(T.Gterm_tsize)](Otembed.md#t-Gterm_tsize) を $`g\in G_u(m)`$ に適用して
  $`\lVert g\rVert\lt \lVert m\rVert`$。したがって $`g\ne m`$（$`g=m`$ なら $`\lVert m\rVert\lt \lVert m\rVert`$）。

$`g\prec b`$ か否かで分ける。

- **$`g\prec b`$ のとき。** $`(4.1)`$ と [(T.olt_ole_trans)](Mechanized.md#t-olt_ole_trans) より $`g\prec m`$。
- **$`\neg(g\prec b)`$ のとき。** $`g\in\mathrm{Glist}_u(b)`$（[(T.mem_Glist)](Nrm.md#t-mem_Glist)）かつ
  $`\mathrm{Bad}_u(b)`$ の述語を満たすから $`g\in\mathrm{Bad}_u(b)`$。
  [(T.maxo_ub_mem)](#t-maxo_ub_mem) より $`g\preceq m`$、すなわち $`g\prec m`$ または $`g=m`$。
  後者は上で否定したから $`g\prec m`$。∎

<a id="t-proj_eq_maxo_bad"></a>
### 定理 発火項の射影は一段 (T.proj_eq_maxo_bad)

**主張** $`\mathrm{fire}_u(b)`$ ならば $`\mathrm{proj}_u(b)=\mathrm{mx}_u(b)`$。

**証明** [(D.pfire)](#d-pfire) より $`\mathrm{Bad}_u(b)\ne[]`$。
[(T.proj_rec)](Nrm.md#t-proj_rec) より $`\mathrm{proj}_u(b)=\mathrm{proj}_u(\mathrm{mx}_u(b))`$。
[(T.maxo_bad_nofire)](#t-maxo_bad_nofire) より $`\neg\,\mathrm{fire}_u(\mathrm{mx}_u(b))`$ であるから、
[(T.proj_nofire)](#t-proj_nofire) より $`\mathrm{proj}_u(\mathrm{mx}_u(b))=\mathrm{mx}_u(b)`$。∎

---

## $`\mathrm{descok}`$ : 連続添字の降下述語

<a id="d-descok"></a>
### 定義 連続添字降下述語 (D.descok)

```math
\mathrm{descok}(\mathsf Z) := \bot,
```
```math
\mathrm{descok}(\mathsf P(a,x,y)) :=
\bigl(a=\mathrm{maxsub}(\mathsf P(a,x,y))\bigr)\ \vee\
\bigl(\mathrm{lead}\,x=a+1\ \wedge\ \mathrm{maxsub}\,y<\mathrm{maxsub}\,x\ \wedge\ \mathrm{descok}(x)\bigr)
```

（[(D.maxsub)](Wf.md#d-maxsub), [(D.lead)](Mechanized.md#d-lead)）。
再帰呼び出しの引数 $`x`$ は $`\mathsf P(a,x,y)`$ の真部分項であるから、この定義は
項の構造に関する再帰として整合的である。
本章の他の宣言はこの述語を用いない。

<a id="t-descok_Z"></a>
### 定理 $`\mathsf Z`$ は $`\mathrm{descok}`$ でない (T.descok_Z)

**主張** $`\neg\,\mathrm{descok}(\mathsf Z)`$。

**証明** [(D.descok)](#d-descok) の第 1 式により $`\mathrm{descok}(\mathsf Z)`$ は $`\bot`$ と
定義により等しい。∎

<a id="t-descok_P"></a>
### 定理 $`\mathrm{descok}`$ の展開 (T.descok_P)

**主張**
```math
\mathrm{descok}(\mathsf P(a,x,y))\iff
\bigl(a=\mathrm{maxsub}(\mathsf P(a,x,y))\bigr)\vee
\bigl(\mathrm{lead}\,x=a+1\wedge\mathrm{maxsub}\,y<\mathrm{maxsub}\,x\wedge\mathrm{descok}(x)\bigr).
```

**証明** [(D.descok)](#d-descok) の第 2 式そのものであり、両辺は定義により同一の命題である。∎

---

## $`\mathrm{mv}`$ 降下類と単一の STEP 残件

<a id="d-mvstep"></a>
### 定義 射影の一段 (D.mvstep)

```math
\mathrm{mv}(b) := \begin{cases}
b & (\mathrm{Bad}_0(b)=[])\cr
\mathrm{mx}_0(b) & (\mathrm{Bad}_0(b)\ne[])
\end{cases}
```

すなわち水準 $`0`$ の違反者リストが空でなければその $`\mathrm{maxo}`$ を取り、空なら $`b`$ 自身を返す。

<a id="t-mvstep_nofire"></a>
### 定理 非発火なら $`\mathrm{mv}`$ は恒等 (T.mvstep_nofire)

**主張** $`\neg\,\mathrm{fire}_0(b)`$ ならば $`\mathrm{mv}(b)=b`$。

**証明** $`\neg\,\mathrm{fire}_0(b)`$ は $`\neg(\mathrm{Bad}_0(b)\ne[])`$ であり、二重否定除去により
$`\mathrm{Bad}_0(b)=[]`$。[(D.mvstep)](#d-mvstep) の第 1 分岐である。∎

<a id="t-proj_mvstep"></a>
### 定理 射影は一段を経由する (T.proj_mvstep)

**主張** $`\mathrm{proj}_0(b)=\mathrm{proj}_0(\mathrm{mv}(b))`$。

**証明** $`\mathrm{fire}_0(b)`$ か否かで場合分けする。

- **$`\mathrm{fire}_0(b)`$ のとき。** $`\mathrm{Bad}_0(b)\ne[]`$ であるから
  [(D.mvstep)](#d-mvstep) より $`\mathrm{mv}(b)=\mathrm{mx}_0(b)`$。
  [(T.maxo_bad_nofire)](#t-maxo_bad_nofire) より $`\neg\,\mathrm{fire}_0(\mathrm{mx}_0(b))`$ であるから
  [(T.proj_nofire)](#t-proj_nofire) より $`\mathrm{proj}_0(\mathrm{mx}_0(b))=\mathrm{mx}_0(b)`$。
  一方 [(T.proj_eq_maxo_bad)](#t-proj_eq_maxo_bad) より $`\mathrm{proj}_0(b)=\mathrm{mx}_0(b)`$。
  よって両辺とも $`\mathrm{mx}_0(b)`$ に等しい。
- **$`\neg\,\mathrm{fire}_0(b)`$ のとき。** [(T.mvstep_nofire)](#t-mvstep_nofire) より
  $`\mathrm{mv}(b)=b`$ であり、両辺は同じ項である。∎

<a id="t-tsize_mvstep_lt"></a>
### 定理 一段はサイズを真に減らす (T.tsize_mvstep_lt)

**主張** $`\mathrm{fire}_0(b)`$ ならば $`\lVert\mathrm{mv}(b)\rVert\lt \lVert b\rVert`$。

**証明** $`\mathrm{Bad}_0(b)\ne[]`$ であるから $`\mathrm{mv}(b)=\mathrm{mx}_0(b)`$。
[(T.maxo_hdtl_in)](Nrm.md#t-maxo_hdtl_in) より $`\mathrm{mx}_0(b)\in\mathrm{Bad}_0(b)`$、
したがって [(T.mem_filter_Gterm)](#t-mem_filter_Gterm) より $`\mathrm{mx}_0(b)\in G_0(b)`$。
[(T.Gterm_tsize)](Otembed.md#t-Gterm_tsize) により
$`\lVert\mathrm{mx}_0(b)\rVert\lt \lVert b\rVert`$。∎

<a id="t-proj0_olt_of_mvstep_olt"></a>
### 定理 一段の狭義単調性から射影の狭義単調性へ (T.proj0_olt_of_mvstep_olt)

**主張** 二項関係 $`R\subseteq\mathrm{Three}\times\mathrm{Three}`$ が次の 3 条件を満たすとする。

- （$`\mathrm{hfire}`$）$`\forall x\,y,\ R\,x\,y\to\bigl(\mathrm{fire}_0(x)\iff\mathrm{fire}_0(y)\bigr)`$；
- （$`\mathrm{hpres}`$）$`\forall x\,y,\ R\,x\,y\to\mathrm{fire}_0(x)\to\mathrm{fire}_0(y)\to R\,(\mathrm{mv}(x))\,(\mathrm{mv}(y))`$；
- （$`\mathrm{hstep}`$）$`\forall x\,y,\ R\,x\,y\to x\prec y\to\mathrm{mv}(x)\prec\mathrm{mv}(y)`$。

このとき $`\forall x\,y,\ R\,x\,y\to x\prec y\to\mathrm{proj}_0(x)\prec\mathrm{proj}_0(y)`$。

**証明** $`n:=\lVert x\rVert`$ に関する強帰納法。帰納法の述語は

```math
\Phi(n):\equiv\forall x,\ \lVert x\rVert=n\ \to\ \forall y,\ R\,x\,y\to x\prec y\to
\mathrm{proj}_0(x)\prec\mathrm{proj}_0(y).
```

$`n`$ を固定し、帰納法の仮定として $`\forall m\lt n,\ \Phi(m)`$ を仮定する。
$`\lVert x\rVert=n`$ なる $`x`$ と $`y`$ を取り、$`R\,x\,y`$、$`x\prec y`$ を仮定する。
$`\mathrm{fire}_0(x)`$ か否かで分ける。

- **$`\mathrm{fire}_0(x)`$ のとき。** $`\mathrm{hfire}`$ より $`\mathrm{fire}_0(y)`$。
  [(T.proj_mvstep)](#t-proj_mvstep) より
  $`\mathrm{proj}_0(x)=\mathrm{proj}_0(\mathrm{mv}(x))`$、$`\mathrm{proj}_0(y)=\mathrm{proj}_0(\mathrm{mv}(y))`$
  であるから、示すべきは $`\mathrm{proj}_0(\mathrm{mv}(x))\prec\mathrm{proj}_0(\mathrm{mv}(y))`$。
  [(T.tsize_mvstep_lt)](#t-tsize_mvstep_lt) より $`\lVert\mathrm{mv}(x)\rVert\lt \lVert x\rVert=n`$、
  $`\mathrm{hpres}`$ より $`R\,(\mathrm{mv}(x))\,(\mathrm{mv}(y))`$、
  $`\mathrm{hstep}`$ より $`\mathrm{mv}(x)\prec\mathrm{mv}(y)`$。
  帰納法の仮定 $`\Phi(\lVert\mathrm{mv}(x)\rVert)`$ を適用して結論を得る。
- **$`\neg\,\mathrm{fire}_0(x)`$ のとき。** [(T.proj_nofire)](#t-proj_nofire) より
  $`\mathrm{proj}_0(x)=x`$。[(T.proj_ole)](#t-proj_ole) より $`y\preceq\mathrm{proj}_0(y)`$ であるから、
  $`x\prec y`$ と [(T.olt_ole_trans)](#t-olt_ole_trans) より
  $`x\prec\mathrm{proj}_0(y)`$、すなわち $`\mathrm{proj}_0(x)\prec\mathrm{proj}_0(y)`$。∎

<a id="d-Rdesc"></a>
### 定義 降下対関係 (D.Rdesc)

関係 $`\mathrm{Rdesc}\subseteq\mathrm{Three}\times\mathrm{Three}`$ を次の 2 規則で生成される最小の関係と定める
（[(D.NF)](Proofs.md#d-NF)）。

```math
\frac{\ \mathsf P(0,b,c)\in\mathrm{NF}\quad \mathsf P(0,f,g)\in\mathrm{NF}\quad
 b\prec f\quad \mathrm{maxsub}\,b=\mathrm{maxsub}\,f\quad \mathrm{fire}_0(b)\quad \mathrm{fire}_0(f)\ }
{\ \mathrm{Rdesc}\ b\ f\ }\ \text{(base)}
```

```math
\frac{\ \mathrm{Rdesc}\ x\ y\quad \mathrm{fire}_0(x)\quad \mathrm{fire}_0(y)\ }
{\ \mathrm{Rdesc}\ (\mathrm{mv}(x))\ (\mathrm{mv}(y))\ }\ \text{(step)}
```

すなわち $`\mathrm{Rdesc}`$ は、頭部添字 $`0`$ の $`\mathrm{NF}`$ 項の引数対であって
$`\prec`$ で比較され $`\mathrm{maxsub}`$ が一致し両者とも発火するものから出発して、
[(D.mvstep)](#d-mvstep) を同時に反復して到達する対の全体である。

**帰納法原理.** 述語 $`Q:\mathrm{Three}\to\mathrm{Three}\to\mathrm{Prop}`$ が 2 つの導入規則の
前提から結論を導けるならば $`\forall x\,y,\ \mathrm{Rdesc}\,x\,y\to Q\,x\,y`$。

本章の他の宣言は $`\mathrm{Rdesc}`$ を用いない。これは
[(T.proj0_olt_of_mvstep_olt)](#t-proj0_olt_of_mvstep_olt) の $`R`$ に代入することを意図した
関係であり、その $`\mathrm{hfire}`$ と $`\mathrm{hstep}`$ は本リポジトリでは証明されていない。

---

## 部分ブロック関係

<a id="d-SubBlock"></a>
### 定義 部分ブロック関係 (D.SubBlock)

関係 $`\mathrm{SubBlock}\subseteq\mathrm{PairSeq}\times\mathrm{PairSeq}`$ を次の 3 規則で生成される最小の関係と定める。

```math
\frac{\ }{\ \mathrm{SubBlock}(M,M)\ }\ \text{(refl)}
```

```math
\frac{\ M=p\mathbin{::}\mathit{rest}\qquad \mathrm{SubBlock}\bigl(\mathrm{tw}_{\pi_0 p}\mathit{rest},\ K\bigr)\ }
{\ \mathrm{SubBlock}(M,K)\ }\ \text{(desc)}
```

```math
\frac{\ M=p\mathbin{::}\mathit{rest}\qquad \mathrm{SubBlock}\bigl(\mathrm{dw}_{\pi_0 p}\mathit{rest},\ K\bigr)\ }
{\ \mathrm{SubBlock}(M,K)\ }\ \text{(sib)}
```

すなわち $`\mathrm{SubBlock}(M,K)`$ は、[(D.translate)](Mechanized.md#d-translate) の再帰が辿る
2 つの部分列（子ブロック $`\mathrm{tw}`$ と兄弟部分 $`\mathrm{dw}`$）を有限回たどって
$`M`$ から $`K`$ に到達できることを表す。本章の他の宣言はこの関係を用いない。

---

## 定数コピー領域

<a id="d-repB"></a>
### 定義 ブロックの反復 (D.repB)

```math
\mathrm{repB}(B,0) := [],\qquad \mathrm{repB}(B,n+1) := B\mathbin{+\!\!+}\mathrm{repB}(B,n).
```

これは [(D.copyExp)](#d-copyExp) の $`d_0=0`$ の場合のコピー部（$`B`$ を $`n`$ 回そのまま並べた列）である。
本章の他の宣言はこの関数を用いない。

<a id="t-repB_zero"></a>
### 定理 $`\mathrm{repB}`$ の基底 (T.repB_zero)

**主張** $`\mathrm{repB}(B,0)=[]`$。

**証明** [(D.repB)](#d-repB) の第 1 式である。∎

<a id="t-repB_succ"></a>
### 定理 $`\mathrm{repB}`$ の再帰式 (T.repB_succ)

**主張** $`\mathrm{repB}(B,n+1)=B\mathbin{+\!\!+}\mathrm{repB}(B,n)`$。

**証明** [(D.repB)](#d-repB) の第 2 式である。∎

---

## 親子関係の `take` 移送

<a id="t-nextrel0_bound"></a>
### 定理 行 0 の親子関係の上界 (T.nextrel0_bound)

**主張** $`a\to^M_0 b`$ ならば $`b\lt \lvert M\rvert`$。

**証明** [(D.nextrel0)](Def.md#d-nextrel0) の第 2 条件そのものである。∎

<a id="t-le0_le"></a>
### 定理 祖先関係は添字の大小を含む (T.le0_le)

**主張** $`a\le^M_0 b`$ ならば $`a\le b`$（[(D.le0)](Def.md#d-le0)）。

**証明** [(D.le0)](Def.md#d-le0) より $`\mathrm{ReflTransGen}(\to^M_0)\,a\,b`$ が成り立つ。
この導出に関する帰納法を行う。帰納法の述語は

```math
\Psi(b):\equiv a\le b
```

（$`a`$ は固定、$`b`$ と導出が変数）。

**基底段（refl）** $`b=a`$。$`a\le a`$。

**帰納段（tail）** $`\mathrm{ReflTransGen}(\to^M_0)\,a\,y`$ と $`y\to^M_0 z`$ から
$`\mathrm{ReflTransGen}(\to^M_0)\,a\,z`$ が導かれた場合。帰納法の仮定は $`\Psi(y)`$、すなわち $`a\le y`$。
[(T.nextrel0_lt)](Nrm.md#t-nextrel0_lt) より $`y\lt z`$ であるから $`a\le y\le z`$、
すなわち $`\Psi(z)`$。∎

---

## 水準 0 の列は $`(0,0)`$ である

<a id="d-z0ok"></a>
### 定義 水準 0 規律 (D.z0ok)

```math
\mathrm{z0ok}(M) :\iff \forall j<\lvert M\rvert,\ \ \pi_0(M\langle j\rangle)=0\ \to\ \pi_1(M\langle j\rangle)=0 .
```

<a id="t-z0ok_diagSeq"></a>
### 定理 対角列は $`\mathrm{z0ok}`$ (T.z0ok_diagSeq)

**主張** $`\mathrm{z0ok}(\Delta_0^v)`$。

**証明** [(T.diagSeq0_length)](#t-diagSeq0_length) より $`\lvert\Delta_0^v\rvert=v+1`$。
$`j\lt v+1`$ とすると [(T.diagSeq0_getD)](#t-diagSeq0_getD) より $`\Delta_0^v\langle j\rangle=(j,j)`$。
仮定 $`\pi_0(\Delta_0^v\langle j\rangle)=j=0`$ より $`\pi_1(\Delta_0^v\langle j\rangle)=j=0`$。∎

<a id="t-z0ok_take"></a>
### 定理 $`\mathrm{z0ok}`$ は `take` で保存される (T.z0ok_take)

**主張** $`\mathrm{z0ok}(M)`$ ならば $`\mathrm{z0ok}(\mathrm{take}\,m\,M)`$。

**証明** $`j\lt \lvert\mathrm{take}\,m\,M\rvert=\min(m,\lvert M\rvert)`$ とすると $`j\lt m`$ かつ $`j\lt \lvert M\rvert`$。
[(T.getD_take)](#t-getD_take) より $`(\mathrm{take}\,m\,M)\langle j\rangle=M\langle j\rangle`$ であるから、
仮定と結論はいずれも $`M\langle j\rangle`$ についての主張に書き換わり、$`\mathrm{z0ok}(M)`$ を
$`j`$ に適用すればよい。∎

<a id="t-z0ok_Pred"></a>
### 定理 $`\mathrm{z0ok}`$ は $`\mathrm{Pred}`$ で保存される (T.z0ok_Pred)

**主張** $`\mathrm{z0ok}(M)`$ ならば $`\mathrm{z0ok}(\mathrm{Pred}\,M)`$。

**証明** [(D.Pred)](Def.md#d-Pred) の定義により場合分けする。
$`\lvert M\rvert\le1`$ のとき $`\mathrm{Pred}\,M=M`$ であるから仮定そのもの。
$`\lvert M\rvert\gt 1`$ のとき $`\mathrm{Pred}\,M=\mathrm{dropLast}\,M=\mathrm{take}\,(\lvert M\rvert-1)\,M`$
であるから [(T.z0ok_take)](#t-z0ok_take) による。∎

<a id="t-z0ok_copyExp"></a>
### 定理 コピー展開の $`\mathrm{z0ok}`$ (T.z0ok_copyExp)

**主張** $`\mathrm{z0ok}(G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp])`$ ならば $`\mathrm{z0ok}(\mathrm{cE}(G,B,d_0,n))`$。

**証明** $`E:=\mathrm{cE}(G,B,d_0,n)`$、$`H:=G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp]`$ とおく。
[(T.copyExp_length)](#t-copyExp_length) より $`\lvert E\rvert=\lvert G\rvert+n\lvert B\rvert`$。
$`j\lt \lvert E\rvert`$、$`\pi_0(E\langle j\rangle)=0`$ とし、$`\pi_1(E\langle j\rangle)=0`$ を示す。

- **$`j\lt \lvert G\rvert`$ のとき。**
  [(T.copyExp_getD_pre)](#t-copyExp_getD_pre) より $`E\langle j\rangle=G\langle j\rangle`$、
  [(T.hostM_getD_pre)](#t-hostM_getD_pre) より $`H\langle j\rangle=G\langle j\rangle`$。
  [(T.hostM_length)](#t-hostM_length) より $`j\lt \lvert H\rvert`$ であるから、
  仮定 $`\mathrm{z0ok}(H)`$ を $`j`$ に適用して結論を得る。
- **$`\lvert G\rvert\le j`$ のとき。** まず $`0\lt \lvert B\rvert`$ である。実際 $`\lvert B\rvert=0`$ ならば
  $`\lvert E\rvert=\lvert G\rvert`$ となり $`\lvert G\rvert\le j\lt \lvert G\rvert`$ という矛盾が生じる。
  $`j-\lvert G\rvert\lt n\lvert B\rvert`$ であるから [(T.index_decomp)](#t-index_decomp) により
  $`k\lt n`$、$`q\lt \lvert B\rvert`$、$`j=\lvert G\rvert+(k\lvert B\rvert+q)`$ と書ける。
  [(T.copyExp_getD_copy)](#t-copyExp_getD_copy) より

  ```math
  E\langle j\rangle=\bigl(\pi_0(B\langle q\rangle)+k\,d_0,\ \pi_1(B\langle q\rangle)\bigr).
  ```

  仮定 $`\pi_0(E\langle j\rangle)=0`$ は $`\pi_0(B\langle q\rangle)+k\,d_0=0`$ であり、
  自然数の和が $`0`$ であることから $`\pi_0(B\langle q\rangle)=0`$。
  [(T.hostM_getD_blk)](#t-hostM_getD_blk) より $`H\langle\lvert G\rvert+q\rangle=B\langle q\rangle`$ であり、
  [(T.hostM_length)](#t-hostM_length) より $`\lvert G\rvert+q\lt \lvert H\rvert`$ であるから、
  仮定 $`\mathrm{z0ok}(H)`$ を位置 $`\lvert G\rvert+q`$ に適用して $`\pi_1(B\langle q\rangle)=0`$。
  これは $`\pi_1(E\langle j\rangle)=0`$ である。∎

---

## 親の一意性と行 0 の親の存在

<a id="t-nextrel0_unique"></a>
### 定理 行 0 の親は一意 (T.nextrel0_unique)

**主張** $`k_1\to^M_0 j`$ かつ $`k_2\to^M_0 j`$ ならば $`k_1=k_2`$。

**証明** $`k_1`$ と $`k_2`$ の三分律で場合分けする。

- **$`k_1\lt k_2`$ のとき。** $`k_1\to^M_0 j`$ の第 5 条件（[(D.nextrel0)](Def.md#d-nextrel0)）を
  $`j:=k_2`$ に適用する。前提は $`k_1\lt k_2`$（仮定）と $`k_2\lt j`$（$`k_2\to^M_0 j`$ の第 3 条件）であり、
  結論は $`M_{0,j}\le M_{0,k_2}`$。一方 $`k_2\to^M_0 j`$ の第 4 条件は $`M_{0,k_2}\lt M_{0,j}`$ である。
  この 2 つは両立しない。
- **$`k_1=k_2`$ のとき。** 結論そのもの。
- **$`k_2\lt k_1`$ のとき。** $`k_2\to^M_0 j`$ の第 5 条件を $`j:=k_1`$ に適用すると
  $`M_{0,j}\le M_{0,k_1}`$、$`k_1\to^M_0 j`$ の第 4 条件は $`M_{0,k_1}\lt M_{0,j}`$ であり、両立しない。∎

<a id="t-nextrel1_unique"></a>
### 定理 行 1 の親は一意 (T.nextrel1_unique)

**主張** $`k_1\to^M_1 j`$ かつ $`k_2\to^M_1 j`$ ならば $`k_1=k_2`$。

**証明** $`k_1`$ と $`k_2`$ の三分律で場合分けする。

- **$`k_1\lt k_2`$ のとき。** $`k_1\to^M_1 j`$ の第 6 条件（[(D.nextrel1)](Def.md#d-nextrel1) の最大性条項）を
  $`j:=k_2`$ に適用する。前提は $`k_1\lt k_2`$（仮定）と $`k_2\le^M_0 j`$（$`k_2\to^M_1 j`$ の第 5 条件）であり、
  結論は $`M_{1,j}\le M_{1,k_2}`$。一方 $`k_2\to^M_1 j`$ の第 4 条件は $`M_{1,k_2}\lt M_{1,j}`$ である。
  この 2 つは両立しない。
- **$`k_1=k_2`$ のとき。** 結論そのもの。
- **$`k_2\lt k_1`$ のとき。** $`k_2\to^M_1 j`$ の第 6 条件を $`j:=k_1`$ に適用すると
  $`M_{1,j}\le M_{1,k_1}`$、$`k_1\to^M_1 j`$ の第 4 条件は $`M_{1,k_1}\lt M_{1,j}`$ であり、両立しない。∎

<a id="t-blockok_head_zero"></a>
### 定理 深さ 0 ブロックの先頭は水準 0 (T.blockok_head_zero)

**主張** $`\mathrm{blockok}\,0\,M`$（[(D.blockok)](Seqlex.md#d-blockok)）かつ $`0\lt \lvert M\rvert`$ ならば
$`\pi_0(M\langle0\rangle)=0`$。

**証明** $`0\lt \lvert M\rvert`$ より $`M=m_0\mathbin{::}M'`$ と書ける。
このとき $`M\langle0\rangle=m_0`$ かつ $`\mathrm{headI}\,M=m_0`$。
[(D.blockok)](Seqlex.md#d-blockok) の第 1 成分は「$`M\ne[]`$ ならば $`\pi_0(\mathrm{headI}\,M)=0`$」であり、
$`M=m_0\mathbin{::}M'\ne[]`$ であるから $`\pi_0(m_0)=0`$。∎

<a id="t-parent0_exists"></a>
### 定理 行 0 の親の存在 (T.parent0_exists)

**主張** $`\mathrm{blockok}\,0\,M`$、$`j\lt \lvert M\rvert`$、$`0\lt M_{0,j}`$ ならば
$`\exists k,\ k\to^M_0 j`$。

**証明** まず $`0\lt j`$ である。実際 $`j=0`$ とすると
[(T.blockok_head_zero)](#t-blockok_head_zero) より $`M_{0,0}=\pi_0(M\langle0\rangle)=0`$ となり、
仮定 $`0\lt M_{0,j}=M_{0,0}`$ に反する。

述語 $`P(k):\iff M_{0,k}\lt M_{0,j}`$ を考える。$`M_{0,0}=0\lt M_{0,j}`$ より $`P(0)`$ が成り立つ。
$`k:=\mathrm{findGreatest}\,P\,(j-1)`$ とおく。$`0\le j-1`$ と $`P(0)`$ から $`P(k)`$、また $`k\le j-1`$。
この $`k`$ が [(D.nextrel0)](Def.md#d-nextrel0) の 5 条件を満たすことを示す。

1. $`k\lt \lvert M\rvert`$ : $`k\le j-1\lt j\lt \lvert M\rvert`$（$`0\lt j`$ による）。
2. $`j\lt \lvert M\rvert`$ : 仮定。
3. $`k\lt j`$ : $`k\le j-1`$ と $`0\lt j`$。
4. $`M_{0,k}\lt M_{0,j}`$ : $`P(k)`$ そのもの。
5. $`k\lt l\lt j`$ なる $`l`$ について $`M_{0,j}\le M_{0,l}`$ :
   $`l\le j-1`$ であるから $`\mathrm{findGreatest\_is\_greatest}`$ により $`\neg P(l)`$、
   すなわち $`\neg(M_{0,l}\lt M_{0,j})`$、したがって $`M_{0,j}\le M_{0,l}`$。∎

---

## 親の存在 : このクラス上では親なし分岐は空である

<a id="t-chain_to_zero"></a>
### 定理 水準 0 への連鎖 (T.chain_to_zero)

**主張** $`\mathrm{blockok}\,0\,M`$ ならば、任意の $`lev,j`$ について
$`M_{0,j}=lev`$ かつ $`j\lt \lvert M\rvert`$ ならば

```math
\exists r,\ r\le j\ \wedge\ M_{0,r}=0\ \wedge\ \mathrm{ReflTransGen}(\to^M_0)\,r\,j .
```

**証明** $`lev`$ に関する強帰納法。帰納法の述語は

```math
\Phi(lev):\equiv\forall j,\ M_{0,j}=lev\to j<\lvert M\rvert\to
\exists r,\ r\le j\wedge M_{0,r}=0\wedge\mathrm{ReflTransGen}(\to^M_0)\,r\,j .
```

$`lev`$ を固定し、帰納法の仮定として $`\forall lev'\lt lev,\ \Phi(lev')`$ を仮定する。
$`M_{0,j}=lev`$、$`j\lt \lvert M\rvert`$ なる $`j`$ を取る。

- **$`M_{0,j}=0`$ のとき。** $`r:=j`$ とすればよい。$`j\le j`$、$`M_{0,j}=0`$、
  反射推移閉包の反射性により $`\mathrm{ReflTransGen}(\to^M_0)\,j\,j`$。
- **$`M_{0,j}\ne0`$、すなわち $`0\lt M_{0,j}`$ のとき。**
  [(T.parent0_exists)](#t-parent0_exists) により $`k\to^M_0 j`$ なる $`k`$ が取れる。
  [(D.nextrel0)](Def.md#d-nextrel0) の第 4 条件より $`M_{0,k}\lt M_{0,j}=lev`$、
  第 1 条件より $`k\lt \lvert M\rvert`$、第 3 条件より $`k\lt j`$。
  帰納法の仮定を $`lev':=M_{0,k}`$（$`\lt lev`$）と $`j:=k`$ に適用して、
  $`r\le k`$、$`M_{0,r}=0`$、$`\mathrm{ReflTransGen}(\to^M_0)\,r\,k`$ なる $`r`$ を得る。
  この連鎖の末尾に 1 歩 $`k\to^M_0 j`$ を継ぎ足せば $`\mathrm{ReflTransGen}(\to^M_0)\,r\,j`$、
  また $`r\le k\lt j`$ より $`r\le j`$。∎

<a id="t-parent1_exists"></a>
### 定理 行 1 の親の存在 (T.parent1_exists)

**主張** $`\mathrm{blockok}\,0\,M`$、$`\mathrm{z0ok}(M)`$、$`j\lt \lvert M\rvert`$、$`0\lt M_{1,j}`$ ならば
$`\exists k,\ k\to^M_1 j`$。

**証明** [(T.chain_to_zero)](#t-chain_to_zero) を $`lev:=M_{0,j}`$ に適用して、
$`r\le j`$、$`M_{0,r}=0`$、$`\mathrm{ReflTransGen}(\to^M_0)\,r\,j`$ なる $`r`$ を得る。
$`r\le j\lt \lvert M\rvert`$ であるから $`\mathrm{z0ok}(M)`$ を $`r`$ に適用でき、
$`\pi_0(M\langle r\rangle)=M_{0,r}=0`$ より $`\pi_1(M\langle r\rangle)=0`$、すなわち $`M_{1,r}=0`$。
仮定 $`0\lt M_{1,j}`$ より $`M_{1,r}\ne M_{1,j}`$、したがって $`r\ne j`$、よって $`r\lt j`$。

述語 $`P(k):\iff \bigl(k\le^M_0 j\ \wedge\ M_{1,k}\lt M_{1,j}\bigr)`$ を考える。
$`P(r)`$ が成り立つ。実際 $`r\lt \lvert M\rvert`$、$`j\lt \lvert M\rvert`$、上の連鎖より $`r\le^M_0 j`$ であり、
$`M_{1,r}=0\lt M_{1,j}`$。

$`k:=\mathrm{findGreatest}\,P\,(j-1)`$ とおく。$`r\le j-1`$（$`r\lt j`$ による）と $`P(r)`$ から $`P(k)`$、
また $`k\le j-1`$。この $`k`$ が [(D.nextrel1)](Def.md#d-nextrel1) の 6 条件を満たすことを示す。

1. $`k\lt \lvert M\rvert`$ : $`k\le j-1\lt j\lt \lvert M\rvert`$（$`r\lt j`$ より $`0\lt j`$）。
2. $`j\lt \lvert M\rvert`$ : 仮定。
3. $`k\lt j`$ : $`k\le j-1`$ と $`0\lt j`$。
4. $`M_{1,k}\lt M_{1,j}`$ : $`P(k)`$ の第 2 成分。
5. $`k\le^M_0 j`$ : $`P(k)`$ の第 1 成分。
6. $`k\lt j'`$ かつ $`j'\le^M_0 j`$ なる $`j'`$ について $`M_{1,j}\le M_{1,j'}`$ :
   [(T.le0_le)](#t-le0_le) より $`j'\le j`$。
   - $`j'=j`$ のとき $`M_{1,j}\le M_{1,j}`$。
   - $`j'\lt j`$ のとき、$`M_{1,j'}\lt M_{1,j}`$ と仮定すると $`P(j')`$ が成り立ち、
     $`k\lt j'\le j-1`$ であるから $`\mathrm{findGreatest\_is\_greatest}`$ に反する。
     よって $`M_{1,j}\le M_{1,j'}`$。∎

<a id="t-nextR_one_iff"></a>
### 定理 行 1 の $`\mathrm{nextR}`$ (T.nextR_one_iff)

**主張** $`\mathrm{nextR}\,M\,1\,k\,j\iff k\to^M_1 j`$。

**証明** [(D.nextR)](Def.md#d-nextR) の場合分けは第 2 引数が $`0`$ か否かであり、
$`1\ne0`$ であるから $`\to^M_1`$ の分岐が選ばれる。∎

<a id="t-nextR_zero_iff"></a>
### 定理 行 0 の $`\mathrm{nextR}`$ (T.nextR_zero_iff)

**主張** $`\mathrm{nextR}\,M\,0\,k\,j\iff k\to^M_0 j`$。

**証明** [(D.nextR)](Def.md#d-nextR) の場合分けで第 2 引数が $`0`$ の分岐が選ばれる。∎

<a id="t-hp_last"></a>
### 定理 非零な最終列には一意な親が存在する (T.hp_last)

**主張** $`\mathrm{blockok}\,0\,M`$、$`\mathrm{z0ok}(M)`$、$`0\lt \lvert M\rvert`$、
$`M\langle\lvert M\rvert-1\rangle\ne(0,0)`$ ならば

```math
\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M,\lvert M\rvert-1),\ \lvert M\rvert-1\bigr)
```

（[(D.hasParent)](Def.md#d-hasParent), [(D.idx1)](Def.md#d-idx1)）。

**証明** $`j_1:=\lvert M\rvert-1`$ とおく。$`0\lt \lvert M\rvert`$ より $`j_1\lt \lvert M\rvert`$。
$`0\lt M_{1,j_1}`$ か否かで場合分けする。

- **$`0\lt M_{1,j_1}`$ のとき。** [(D.idx1)](Def.md#d-idx1) より $`\mathrm{idx}_1(M,j_1)=1`$。
  [(T.parent1_exists)](#t-parent1_exists) により $`k\to^M_1 j_1`$ なる $`k`$ が取れる。
  [(T.nextR_one_iff)](#t-nextR_one_iff) よりこれは $`\mathrm{nextR}\,M\,1\,k\,j_1`$、
  すなわち $`\mathrm{nextR}\,M\,(\mathrm{idx}_1(M,j_1))\,k\,j_1`$ である。
  一意性は次のように示す。$`\mathrm{nextR}\,M\,(\mathrm{idx}_1(M,j_1))\,y\,j_1`$ とすると
  $`\mathrm{idx}_1(M,j_1)=1`$ と [(T.nextR_one_iff)](#t-nextR_one_iff) より $`y\to^M_1 j_1`$、
  [(T.nextrel1_unique)](#t-nextrel1_unique) より $`y=k`$。
  よって [(D.hasParent)](Def.md#d-hasParent) の $`\exists!`$ が成り立つ。
- **$`M_{1,j_1}=0`$ のとき。** このとき $`0\lt M_{0,j_1}`$ である。実際 $`M_{0,j_1}=0`$ と仮定すると、
  [(D.entry)](Def.md#d-entry) より $`\pi_0(M\langle j_1\rangle)=0`$ かつ $`\pi_1(M\langle j_1\rangle)=0`$、
  すなわち $`M\langle j_1\rangle=(0,0)`$ となり仮定に反する。
  [(D.idx1)](Def.md#d-idx1) より $`\mathrm{idx}_1(M,j_1)=0`$。
  [(T.parent0_exists)](#t-parent0_exists) により $`k\to^M_0 j_1`$ なる $`k`$ が取れ、
  [(T.nextR_zero_iff)](#t-nextR_zero_iff) よりこれは
  $`\mathrm{nextR}\,M\,(\mathrm{idx}_1(M,j_1))\,k\,j_1`$。
  一意性は [(T.nextrel0_unique)](#t-nextrel0_unique) による。∎

---

## 最終列の親が最後のコピー内にある場合

Lean の当該節見出しの直後に置かれているのは、$`\mathrm{z0ok}`$ の展開保存と標準形上の成立である。

<a id="t-z0ok_oper"></a>
### 定理 $`\mathrm{z0ok}`$ は展開で保たれる (T.z0ok_oper)

**主張** $`1\le n`$ かつ $`\mathrm{z0ok}(M)`$ ならば $`\mathrm{z0ok}(M[n])`$。

**証明** [(T.r1ok_oper)](#t-r1ok_oper) と同じ 4 分岐で場合分けする。$`j_1:=\lvert M\rvert-1`$。

- **分岐 (a) : $`j_1=0`$。** [(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) より
  $`M[n]=M`$、仮定そのもの。
- **分岐 (b) : $`M_{0,j_1}=0\wedge M_{1,j_1}=0`$。**
  [(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero) より $`M[n]=\mathrm{Pred}\,M`$、
  [(T.z0ok_Pred)](#t-z0ok_Pred) による。
- **分岐 (c) : 親をもたない場合。**
  [(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent) より
  $`M[n]=\mathrm{Pred}\,M`$、[(T.z0ok_Pred)](#t-z0ok_Pred) による。
- **分岐 (d) : 残りの場合。** $`j_1\ne0`$ より $`1\lt \lvert M\rvert`$。
  [(T.oper_bad_blocks)](Mechanized.md#t-oper_bad_blocks) により
  $`M=G\mathbin{+\!\!+}((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}[lp]`$ かつ
  $`M[n]=\mathrm{cE}(G,(v_0,w_0)\mathbin{::}R,d_0,n)`$ なる分解が得られる。
  仮定 $`\mathrm{z0ok}(M)`$ をこの形に書き換え、
  [(T.z0ok_copyExp)](#t-z0ok_copyExp) を適用すればよい。∎

<a id="t-z0ok_ST_PS"></a>
### 定理 標準形は $`\mathrm{z0ok}`$ (T.z0ok_ST_PS)

**主張** $`M\in\mathrm{ST\_PS}`$ ならば $`\mathrm{z0ok}(M)`$。

**証明** $`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M):\equiv \mathrm{z0ok}(M).
```

**基底段（規則 diag）** $`M=\Delta_0^v`$。[(T.z0ok_diagSeq)](#t-z0ok_diagSeq) による。

**帰納段（規則 oper）** $`M=N[n]`$、$`N\in\mathrm{ST\_PS}`$、$`1\le n`$。
帰納法の仮定は $`\Phi(N)`$、すなわち $`\mathrm{z0ok}(N)`$。
[(T.z0ok_oper)](#t-z0ok_oper) を適用して $`\mathrm{z0ok}(N[n])`$。∎

---

## 単一登攀規律

<a id="d-sclimb"></a>
### 定義 単一登攀規律 (D.sclimb)

```math
\mathrm{sclimb}(M) :\iff \forall r',r,\quad
\begin{aligned}
&1<\lvert M\rvert\ \to\cr
&\mathrm{nextR}\bigl(M,\ \mathrm{idx}_1(M,\lvert M\rvert-1),\ 0,\ \lvert M\rvert-1\bigr)\ \to\cr
&\mathrm{idx}_1(M,\lvert M\rvert-1)=1\ \to\cr
&0<r'\ \to\ r'+1<\lvert M\rvert\ \to\cr
&\pi_0(M\langle r'\rangle)+1=\pi_0(M\langle\lvert M\rvert-1\rangle)\ \to\cr
&\bigl(\forall l,\ r'<l\to l+1<\lvert M\rvert\to
   \pi_0(M\langle\lvert M\rvert-1\rangle)\le\pi_0(M\langle l\rangle)\bigr)\ \to\cr
&0<r\ \to\ r<r'\ \to\cr
&\pi_0(M\langle r\rangle)+1<\pi_0(M\langle\lvert M\rvert-1\rangle).
\end{aligned}
```

すなわち、行 1 の親辺が先頭（位置 $`0`$）に固定された列において、
先頭と最終列の行 0 の親 $`r'`$ の間にある位置 $`r`$（$`0\lt r\lt r'`$）の行 0 の値は、
最終列の行 0 の値より 2 以上小さい。本章の他の宣言はこの述語を用いない。

---

## `drop` 移送と連鎖のピボット機構

<a id="t-rtg_through_pivot"></a>
### 定理 連鎖はピボットを通過する (T.rtg_through_pivot)

**主張** $`\rho\in\mathbb{N}`$ とする。$`\mathrm{ReflTransGen}(\to^M_0)\,a\,b`$、$`a\lt \rho`$、$`\rho\le b`$、
および

```math
\forall y,\ \rho<y\to y\le b\to M_{0,\rho}<M_{0,y}
```

ならば $`\mathrm{ReflTransGen}(\to^M_0)\,\rho\,b`$。

**証明** 連鎖 $`\mathrm{ReflTransGen}(\to^M_0)\,a\,b`$ の導出に関する帰納法（$`a`$ は固定、
$`b`$ と 3 つの仮定は帰納法の述語の内側に置く）。帰納法の述語は

```math
\Psi(b):\equiv a<\rho\to\rho\le b\to
\bigl(\forall y,\ \rho<y\to y\le b\to M_{0,\rho}<M_{0,y}\bigr)\to
\mathrm{ReflTransGen}(\to^M_0)\,\rho\,b .
```

**基底段（refl）** $`b=a`$。仮定 $`a\lt \rho`$ と $`\rho\le b=a`$ から $`a\lt a`$ となり、前提が偽である。
よって $`\Psi(a)`$ が成り立つ。

**帰納段（tail）** $`\mathrm{ReflTransGen}(\to^M_0)\,a\,y`$ と $`y\to^M_0 z`$ から
$`\mathrm{ReflTransGen}(\to^M_0)\,a\,z`$ が導かれた場合。帰納法の仮定は $`\Psi(y)`$ である。
$`a\lt \rho`$、$`\rho\le z`$、および $`(\rho,z]`$ 上のピボット条件 $`\mathrm{hpiv}`$ を仮定する。

- **$`\rho\le y`$ のとき。** [(T.nextrel0_lt)](Nrm.md#t-nextrel0_lt) より $`y\lt z`$、
  したがって $`y\le z`$。ピボット条件を $`(\rho,y]`$ に制限すると
  ($`\rho\lt y'\le y\le z`$ より) $`\mathrm{hpiv}`$ が使えるから、$`\Psi(y)`$ を
  $`a\lt \rho`$、$`\rho\le y`$、制限したピボット条件に適用して
  $`\mathrm{ReflTransGen}(\to^M_0)\,\rho\,y`$ を得る。
  この連鎖の末尾に 1 歩 $`y\to^M_0 z`$ を継ぎ足して $`\mathrm{ReflTransGen}(\to^M_0)\,\rho\,z`$。
- **$`y\lt \rho`$ のとき。** $`\rho\le z`$ をさらに $`\rho=z`$ と $`\rho\lt z`$ に分ける。
  - $`\rho=z`$ のとき、目標は $`\mathrm{ReflTransGen}(\to^M_0)\,\rho\,\rho`$ であり、反射性による。
  - $`\rho\lt z`$ のとき、$`y\to^M_0 z`$ の第 5 条件（[(D.nextrel0)](Def.md#d-nextrel0)）を $`j:=\rho`$ に
    適用する。前提は $`y\lt \rho`$ と $`\rho\lt z`$ であり、結論は $`M_{0,z}\le M_{0,\rho}`$。
    一方 $`\mathrm{hpiv}`$ を $`y:=z`$（$`\rho\lt z\le z`$）に適用すると $`M_{0,\rho}\lt M_{0,z}`$。
    この 2 つは両立しないから、この場合は起こらない。∎

<a id="t-le0_through_pivot"></a>
### 定理 祖先関係はピボットを通過する (T.le0_through_pivot)

**主張** $`a\le^M_0 b`$、$`a\lt \rho`$、$`\rho\le b`$、
$`\forall y,\ \rho\lt y\to y\le b\to M_{0,\rho}\lt M_{0,y}`$ ならば $`\rho\le^M_0 b`$。

**証明** [(D.le0)](Def.md#d-le0) より $`a\le^M_0 b`$ は
「$`a\lt \lvert M\rvert`$ かつ $`b\lt \lvert M\rvert`$ かつ $`\mathrm{ReflTransGen}(\to^M_0)\,a\,b`$」である。
結論の 3 条件を確かめる。$`\rho\lt \lvert M\rvert`$ は $`\rho\le b\lt \lvert M\rvert`$ による。
$`b\lt \lvert M\rvert`$ はそのまま。連鎖は [(T.rtg_through_pivot)](#t-rtg_through_pivot) による。∎

---

## 親子関係の平行移動不変性

以下、$`S^{+d} := \mathrm{map}\ \bigl(p\mapsto(\pi_0 p+d,\ \pi_1 p)\bigr)\ S`$
（行 0 を一律に $`d`$ だけずらした列）と書く。$`\lvert S^{+d}\rvert=\lvert S\rvert`$ である。

<a id="t-entry_shift"></a>
### 定理 平行移動後の成分 (T.entry_shift)

**主張** $`j\lt \lvert S\rvert`$ ならば

```math
(S^{+d})_{0,j}=S_{0,j}+d\qquad\text{かつ}\qquad (S^{+d})_{1,j}=S_{1,j}.
```

**証明** $`\lvert S^{+d}\rvert=\lvert S\rvert`$ であるから $`j\lt \lvert S^{+d}\rvert`$ であり、
[(T.getD_eq_getElem')](Wf.md#t-getD_eq_getElem') により $`\mathrm{getD}`$ は既定値を返さず
第 $`j`$ 要素そのものである。`map` の第 $`j`$ 要素は写像の値であるから

```math
S^{+d}\langle j\rangle=\bigl(\pi_0(S\langle j\rangle)+d,\ \pi_1(S\langle j\rangle)\bigr).
```

[(D.entry)](Def.md#d-entry) により $`(S^{+d})_{0,j}`$ は第 0 成分、
$`(S^{+d})_{1,j}`$ は第 1 成分であるから、主張の 2 式を得る。∎

<a id="t-nextrel0_shift_iff"></a>
### 定理 行 0 の親子関係は平行移動不変 (T.nextrel0_shift_iff)

**主張** $`b\lt \lvert S\rvert`$ ならば $`\bigl(a\to^{S^{+d}}_0 b\iff a\to^S_0 b\bigr)`$。

**証明** $`\lvert S^{+d}\rvert=\lvert S\rvert`$ であるから、
[(D.nextrel0)](Def.md#d-nextrel0) の第 1・2・3 条件は両辺で同一の命題である。

第 4 条件。第 3 条件 $`a\lt b`$ と $`b\lt \lvert S\rvert`$ より $`a\lt \lvert S\rvert`$ であるから
[(T.entry_shift)](#t-entry_shift) が $`a`$ と $`b`$ の双方に適用でき、

```math
(S^{+d})_{0,a}<(S^{+d})_{0,b}\iff S_{0,a}+d<S_{0,b}+d\iff S_{0,a}<S_{0,b}.
```

第 5 条件。$`a\lt l\lt b`$ なる $`l`$ は $`l\lt b\lt \lvert S\rvert`$ を満たすから
[(T.entry_shift)](#t-entry_shift) が $`l`$ と $`b`$ に適用でき、

```math
(S^{+d})_{0,b}\le(S^{+d})_{0,l}\iff S_{0,b}+d\le S_{0,l}+d\iff S_{0,b}\le S_{0,l}.
```

以上より両辺の 5 条件は同値であり、連言も同値である。∎

<a id="t-rtg_shift_of"></a>
### 定理 平行移動された連鎖はもとの連鎖 (T.rtg_shift_of)

**主張** $`\mathrm{ReflTransGen}(\to^{S^{+d}}_0)\,a\,b`$ ならば $`\mathrm{ReflTransGen}(\to^{S}_0)\,a\,b`$。

**証明** 連鎖の導出に関する帰納法。帰納法の述語は

```math
\Psi(b):\equiv \mathrm{ReflTransGen}(\to^{S}_0)\,a\,b .
```

**基底段（refl）** $`b=a`$。反射性により $`\mathrm{ReflTransGen}(\to^S_0)\,a\,a`$。

**帰納段（tail）** $`\mathrm{ReflTransGen}(\to^{S^{+d}}_0)\,a\,c`$ と $`c\to^{S^{+d}}_0 e`$ の場合。
帰納法の仮定は $`\Psi(c)`$、すなわち $`\mathrm{ReflTransGen}(\to^S_0)\,a\,c`$。
[(T.nextrel0_bound)](#t-nextrel0_bound) を $`c\to^{S^{+d}}_0 e`$ に適用して
$`e\lt \lvert S^{+d}\rvert=\lvert S\rvert`$。
[(T.nextrel0_shift_iff)](#t-nextrel0_shift_iff) により $`c\to^S_0 e`$。
連鎖の末尾にこの 1 歩を継ぎ足して $`\Psi(e)`$。∎

<a id="t-rtg_shift_to"></a>
### 定理 連鎖は平行移動される (T.rtg_shift_to)

**主張** $`\mathrm{ReflTransGen}(\to^{S}_0)\,a\,b`$ ならば $`\mathrm{ReflTransGen}(\to^{S^{+d}}_0)\,a\,b`$。

**証明** 連鎖の導出に関する帰納法。帰納法の述語は

```math
\Psi(b):\equiv \mathrm{ReflTransGen}(\to^{S^{+d}}_0)\,a\,b .
```

**基底段（refl）** $`b=a`$。反射性による。

**帰納段（tail）** $`\mathrm{ReflTransGen}(\to^{S}_0)\,a\,c`$ と $`c\to^{S}_0 e`$ の場合。
帰納法の仮定は $`\Psi(c)`$。[(T.nextrel0_bound)](#t-nextrel0_bound) より $`e\lt \lvert S\rvert`$ であるから
[(T.nextrel0_shift_iff)](#t-nextrel0_shift_iff) により $`c\to^{S^{+d}}_0 e`$。
連鎖の末尾にこの 1 歩を継ぎ足して $`\Psi(e)`$。∎

<a id="t-le0_shift_iff"></a>
### 定理 祖先関係は平行移動不変 (T.le0_shift_iff)

**主張** $`a\le^{S^{+d}}_0 b\iff a\le^S_0 b`$。

**証明** [(D.le0)](Def.md#d-le0) の 3 条件のうち、長さ条件 2 つは
$`\lvert S^{+d}\rvert=\lvert S\rvert`$ により両辺で同一である。
連鎖条件は [(T.rtg_shift_of)](#t-rtg_shift_of) と [(T.rtg_shift_to)](#t-rtg_shift_to) により
双方向に移る。∎

<a id="t-idx1_shift"></a>
### 定理 $`\mathrm{idx}_1`$ は平行移動不変 (T.idx1_shift)

**主張** $`\mathrm{idx}_1(S^{+d},j)=\mathrm{idx}_1(S,j)`$。

**証明** [(D.idx1)](Def.md#d-idx1) は $`S_{1,j}`$ が正か否かで値が決まるから、
$`(S^{+d})_{1,j}=S_{1,j}`$ を示せばよい。

- $`j\lt \lvert S\rvert`$ のとき。[(T.entry_shift)](#t-entry_shift) の第 2 式による。
- $`j\ge\lvert S\rvert`$ のとき。$`\lvert S^{+d}\rvert=\lvert S\rvert`$ であるから
  $`j`$ は両列の範囲外であり、$`\mathrm{getD}`$ はいずれも既定値 $`(0,0)`$ を返す。
  よって [(D.entry)](Def.md#d-entry) より $`(S^{+d})_{1,j}=0=S_{1,j}`$。∎

<a id="t-nextrel1_shift_iff"></a>
### 定理 行 1 の親子関係は平行移動不変 (T.nextrel1_shift_iff)

**主張** $`b\lt \lvert S\rvert`$ ならば $`\bigl(a\to^{S^{+d}}_1 b\iff a\to^S_1 b\bigr)`$。

**証明** $`\lvert S^{+d}\rvert=\lvert S\rvert`$ であるから
[(D.nextrel1)](Def.md#d-nextrel1) の第 1・2・3 条件は両辺で同一である。

第 4 条件。第 3 条件 $`a\lt b`$ と $`b\lt \lvert S\rvert`$ より $`a\lt \lvert S\rvert`$ であるから
[(T.entry_shift)](#t-entry_shift) の第 2 式が $`a`$ と $`b`$ に適用でき、
$`(S^{+d})_{1,a}=S_{1,a}`$、$`(S^{+d})_{1,b}=S_{1,b}`$。よって両辺は同一の命題である。

第 5 条件。[(T.le0_shift_iff)](#t-le0_shift_iff) による。

第 6 条件。$`a\lt l`$ かつ $`l\le^S_0 b`$（[(T.le0_shift_iff)](#t-le0_shift_iff) により
$`l\le^{S^{+d}}_0 b`$ と同値）なる $`l`$ を取ると、[(T.le0_le)](#t-le0_le) より $`l\le b\lt \lvert S\rvert`$ で
あるから [(T.entry_shift)](#t-entry_shift) の第 2 式が $`l`$ と $`b`$ に適用でき、
$`(S^{+d})_{1,b}\le(S^{+d})_{1,l}\iff S_{1,b}\le S_{1,l}`$。

以上より両辺の 6 条件は同値であり、連言も同値である。∎

<a id="d-predGuard"></a>
### 定義 切り詰め条件 (D.predGuard)

```math
\mathrm{predGuard}(N) :\iff
\bigl(N_{0,\lvert N\rvert-1}=0\ \wedge\ N_{1,\lvert N\rvert-1}=0\bigr)\ \vee\
\neg\,\mathrm{hasParent}\bigl(N,\ \mathrm{idx}_1(N,\lvert N\rvert-1),\ \lvert N\rvert-1\bigr).
```

これは [(D.oper)](Def.md#d-oper) の分岐 (b) と分岐 (c) の条件の選言、すなわち
$`\lvert N\rvert-1\ne0`$ のもとで $`N[n]=\mathrm{Pred}\,N`$ となる条件である
（[(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero),
[(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent)）。

<a id="d-predImages"></a>
### 定義 条件つき切り詰めの反復像 (D.predImages)

関係 $`\mathrm{predImages}\subseteq\mathrm{PairSeq}\times\mathrm{PairSeq}`$ を次の 2 規則で生成される最小の関係と定める。

```math
\frac{\ }{\ \mathrm{predImages}(M,M)\ }\ \text{(refl)}
\qquad\qquad
\frac{\ \mathrm{predImages}(M,N)\qquad \mathrm{predGuard}(N)\ }{\ \mathrm{predImages}(M,\ \mathrm{Pred}\,N)\ }\ \text{(step)}
```

すなわち $`\mathrm{predImages}(M,N)`$ は、$`M`$ から出発して
「そのつど $`\mathrm{predGuard}`$ を満たす列に $`\mathrm{Pred}`$ を施す」操作を有限回反復して
$`N`$ に到達できることを表す。本章の他の宣言はこの関係を用いない。

**帰納法原理.** 述語 $`Q:\mathrm{PairSeq}\to\mathrm{Prop}`$ が $`Q(M)`$ を満たし、かつ
$`\mathrm{predImages}(M,N)`$、$`Q(N)`$、$`\mathrm{predGuard}(N)`$ から $`Q(\mathrm{Pred}\,N)`$ を導けるならば、
$`\forall N,\ \mathrm{predImages}(M,N)\to Q(N)`$。

---

<a id="no-decl-sections"></a>
## 宣言を含まない節見出し

Lean のソース `lean/YAPSS/Nrmstep.lean` は、形式化されなかった経路や
本リポジトリの他ファイルにある残件についての記録を、宣言を伴わない
`/-! ## ... -/` 節見出しコメントとして多数含む。それらは本章の数学的内容に
寄与しないので、上ではそれぞれの見出しを再現していない。
対応関係を保つため、ここに出現順で列挙する。各項目に対応する宣言は 1 つも存在しない。

1. `The gap lemmas`
2. `Critical sets under one-position increase`
3. `Fire transport`
4. `The innermost dominated run and the ST_snocok interface`
5. `Case combinators for ST_snoc_C`
6. `proj0_olt_NF: proj-side order on NF arguments`（`Both-fire reduction and the subscript chain` の小節）
7. `maxsub/climb discipline of NF arguments`（同上）
8. `Keystone: the leading-.b-chain descent of proj 0`（同上）
9. `The EQUAL-maxsub both-fire witness`（同上）
10. `The both-fire witness (reduced to the equal-maxsub core)`（同上）
11. `The subscript chain: criticals, projections and nrm never invent subscripts`
12. `The two precise forest residuals (the carrier keystone)`（同上の小節）
13. `The both-fire / proj0_olt_NF chain, wired to _final`（同上の小節）
14. `Head-subscript facts for normalized images`
15. `Low-subscript dominance`
16. `Forest-bridge positional lemmas`（同上の小節）
17. `The dominated-segment classes`
18. `The forest-boundary level squeeze`
19. `Sum-adjacent row-1 non-increase (F1)`
20. `Dominated runs by position`
21. `Runs are blockok segments`
22. `The tie-sibling run dichotomy`
23. `The NT_tie combinator`
24. `The HM⁺ discipline`
25. `HM⁺ under truncation`
26. `The final-block discipline tailok`
27. `H1: closures below the shared base transfer through the truncation`
28. `Drop decomposition of the general copy region`
29. `Run characterization at copy positions`
30. `Assembly helpers for hmok under the copy expansion`
31. `hmok survives the copy expansion`
32. `Wholesale instance transfer below a shared truncation`
33. `Within-copy parenthood transfer`
34. `Segment extraction at copy positions`
35. `Within-copy row-0 instances of tailokA`
36. `Chain lifts between the host block and a copy`
37. `Chains cover their interval without dips`
38. `The Pred branch of the final-block discipline`
39. `Block intervals above a base are hereditarily head-maximal`
40. `The conditional generation closure of the invariant package`
41. `The master segment discipline`
42. `The arg-zone ORDER reframe`（およびその小節
    `H1 head-arg residual`, `H2 transport residuals`, `NRMMONO half`）

なお、本文中で「本章の他の宣言はこれを用いない」と記した定義
（[(D.lext)](#d-lext), [(D.lflip)](#d-lflip), [(D.einc)](#d-einc), [(D.eflip)](#d-eflip),
[(D.noabsorb)](#d-noabsorb), [(D.descok)](#d-descok), [(D.Rdesc)](#d-Rdesc),
[(D.SubBlock)](#d-SubBlock), [(D.repB)](#d-repB), [(D.sclimb)](#d-sclimb),
[(D.predGuard)](#d-predGuard), [(D.predImages)](#d-predImages)）は、
これらの見出しが述べる経路のための語彙である。定義そのものは Lean 側に存在するので、
本章でも定義として記録した。

---

## 本章の成果のまとめ

本章が下流の章に渡すのは次の 5 つである。

- [(T.proj_ole)](#t-proj_ole) : $`b\preceq\mathrm{proj}_u(b)`$。
- [(T.ins_olt_mono)](#t-ins_olt_mono) : $`t\prec t'\Rightarrow\mathrm{ins}_a(b,t)\prec\mathrm{ins}_a(b,t')`$（側条件なし）。
- [(T.nrm_snoc_seg)](#t-nrm_snoc_seg) : 条件束 $`\mathrm{snocok}`$ のもとで末尾付加は正規化像を狭義に増加させる。
- [(T.r1ok_ST_PS)](#t-r1ok_ST_PS), [(T.z0ok_ST_PS)](#t-z0ok_ST_PS) : 標準形の列は 2 つの位置的不変量を満たす。
- [(T.hp_last)](#t-hp_last) : $`\mathrm{blockok}\,0`$ かつ $`\mathrm{z0ok}`$ の列で最終列が $`(0,0)`$ でなければ、
  [(D.oper)](Def.md#d-oper) の分岐 (c)（親をもたない分岐）は起こらない。

