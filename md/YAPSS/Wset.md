[← 目次](README.md)

# Wset — 反復帰納的集合 $`W_u`$、最小不動点帰納法、可到達性への橋

本章は Buchholz (1987) §2 の反復帰納的集合をペア列の系へ移植する。水準 $`u`$ ごとの作用素 $`A_u`$ とその最小不動点 $`W_u`$ を定め、
不動点方程式 (A1) と最小不動点帰納法 (A2) を確立し、共終性を明示の仮定として受け取って
「$`W_u`$ の元は $`\prec`$ について可到達である」（橋 [(T.acc_of_W)](#t-acc_of_W)）を示す。
さらに任意のペア列 $`M`$ が $`W_{\mathrm{maxr1}\,M}`$ に属すること（[(T.W_membership)](#t-W_membership)）をブロック長に関する帰納法で示し、
両者を合わせて [(T.wf_olt_ST_PS_of_cofinality)](#t-wf_olt_ST_PS_of_cofinality) を得る。

## 記法

この章で導入する Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `M.length - 1` | $`\ell_M`$ | 最終添字（切り捨て減法。$`M=[]`$ なら $`\ell_M=0`$） |
| `domT M m` | $`\mathrm{dom}(M)=T_m`$ | $`M`$ の最終対が水準 $`m+1`$ の行 1 孤立点である |
| `graft M z` | $`\mathrm{gr}(M,z)`$ | 最終対をブロック $`z`$ で置換した列 |
| `based z` | $`\mathrm{based}(z)`$ | $`z_{0,0}=0`$ |
| `natDom M` | $`\mathrm{natDom}(M)`$ | $`\forall m,\ \neg(\mathrm{dom}(M)=T_m)`$ |
| `r1cand M j1 j0` | $`\mathrm{r1cand}(M,j_1,j_0)`$ | $`j_0`$ は $`j_1`$ の行 1 親候補 |
| `lfpS f` | $`\mathrm{lfp}\,f`$ | 単調作用素 $`f`$ の最小不動点 |
| `Aop Wfam u X M` | $`M\in A^{\mathcal F}_u(X)`$ | 作用素 $`A_u`$（族パラメータ $`\mathcal F`$） |
| `Aset Wfam u X` | $`A^{\mathcal F}_u(X)`$ | 同上（集合として） |
| `Wf n m` | $`W^{(n)}_m`$ | 段階族（$`m<n`$ でのみ意味をもつ） |
| `W u` | $`W_u`$ | 反復帰納的集合 |
| `Rst a b` | $`a \mathrel{R} b`$ | 目標関係（標準形上の $`\prec`$） |
| `argOK R` | $`\mathrm{argOK}(R)`$ | $`\forall p\in R,\ 0<\pi_0 p`$ |
| `rsum A P` | $`\mathrm{rsum}(A,P)`$ | $`P`$ が $`A\mathbin{+\!\!+}P`$ の最上位末尾ブロックである |
| `XA A X` | $`X^{(A)}`$ | $`\{B \mid \mathrm{rsum}(A,B)\to A\mathbin{+\!\!+}B\in X\}`$ |
| `Wstar` | $`W^{*}`$ | 引数ブロックの集合 |
| `tow v R k` | $`t^{v,R}_k`$ | 塔（$`k`$ 段） |
| `M.map (fun p => (p.1+d, p.2))` | $`\mathrm{sh}_d M`$ | 行 0 の一様平行移動（$`+d`$） |
| `M.map (fun p => (p.1-c, p.2))` | $`\mathrm{sh}^{-}_c M`$ | 行 0 の一様平行移動（$`-c`$、切り捨て減法） |

既出のファイルで定義済みの記号は次のように書く。

| Lean | 本文 | 定義 |
|---|---|---|
| `PairSeq` | $`\mathrm{PairSeq}`$ | [(D.PairSeq)](Def.md#d-PairSeq) |
| `M.length` | $`\lvert M\rvert`$ | 長さ |
| `p.1`, `p.2` | $`\pi_0 p`$, $`\pi_1 p`$ | 対の第 0・第 1 成分 |
| `M.getD j (0,0)` | $`M\langle j\rangle`$ | 第 $`j`$ 対（範囲外なら $`(0,0)`$） |
| `entry M i j` | $`M_{i,j}`$ | [(D.entry)](Def.md#d-entry) |
| `nextrel0 M a b` | $`a\to^M_0 b`$ | [(D.nextrel0)](Def.md#d-nextrel0) |
| `nextrel1 M a b` | $`a\to^M_1 b`$ | [(D.nextrel1)](Def.md#d-nextrel1) |
| `nextR M i a b` | $`a\to^M_i b`$ | [(D.nextR)](Def.md#d-nextR) |
| `le0 M a b` | $`a\le^M_0 b`$ | [(D.le0)](Def.md#d-le0) |
| `idx1 M j` | $`\mathrm{idx}_1(M,j)`$ | [(D.idx1)](Def.md#d-idx1) |
| `hasParent M i j` | $`\mathrm{hasParent}(M,i,j)`$ | [(D.hasParent)](Def.md#d-hasParent) |
| `parent M i j` | $`\mathrm{par}^M_i(j)`$ | [(D.parent)](Def.md#d-parent) |
| `Pred M` | $`\mathrm{Pred}\,M`$ | [(D.Pred)](Def.md#d-Pred) |
| `M⟦n⟧` | $`M[n]`$ | [(D.oper)](Def.md#d-oper) |
| `ST_PS M` | $`M\in\mathrm{ST\_PS}`$ | [(D.ST_PS)](Def.md#d-ST_PS) |
| `Three`, `Z`, `P a b c` | $`\mathrm{Three}`$, $`\mathsf{Z}`$, $`\mathsf{P}(a,b,c)`$ | [(D.Three)](Mechanized.md#d-Three) |
| `x <o y` | $`x\prec y`$ | [(D.olt)](Mechanized.md#d-olt) |
| `x ≤o y` | $`x\preceq y`$ | [(D.ole)](Mechanized.md#d-ole) |
| `translate M` | $`\mathrm{tr}\,M`$ | [(D.translate)](Mechanized.md#d-translate) |
| `maxr1 S` | $`\mathrm{maxr1}\,S`$ | [(D.maxr1)](Nrmstep.md#d-maxr1) |

集合と可到達性については Lean（Mathlib）の標準語彙を次の意味で用いる。

- `Set PairSeq` はペア列上の述語であり、$`M\in X`$ は $`X(M)`$ の別記法である。$`X\subseteq Y`$ は $`\forall M,\ M\in X\to M\in Y`$。
- `⋂₀ S` は $`\{x \mid \forall Y\in S,\ x\in Y\}`$（集合族の共通部分）。
- `Monotone f` は $`\forall X\,Y,\ X\subseteq Y \to f(X)\subseteq f(Y)`$。
- $`\mathrm{Acc}\,R\,x`$（`Acc`）は帰納的述語であり、唯一の導入規則は
  ```math
  \frac{\ \forall y,\ R\,y\,x \to \mathrm{Acc}\,R\,y\ }{\ \mathrm{Acc}\,R\,x\ }\ (\texttt{Acc.intro})
  ```
  である。除去規則として `Acc.inv` $`:\ \mathrm{Acc}\,R\,x \to R\,y\,x \to \mathrm{Acc}\,R\,y`$ を用いる。
- `WellFounded R` は $`\forall x,\ \mathrm{Acc}\,R\,x`$（導入規則 `WellFounded.intro`）。

自然数についての次の 2 事実（Mathlib）を用いる。$`P`$ を $`\mathbb{N}`$ 上の述語とし、
$`\mathrm{fg}(P,b) := `$ `Nat.findGreatest P b` と書く。これは
$`\mathrm{fg}(P,0)=0`$、$`\mathrm{fg}(P,b+1)=\bigl(P(b+1) \text{ ならば } b+1 \text{、さもなくば } \mathrm{fg}(P,b)\bigr)`$
で定まる。

- `Nat.findGreatest_spec`：$`m\le b`$ かつ $`P(m)`$ ならば $`P(\mathrm{fg}(P,b))`$。
- `Nat.le_findGreatest`：$`m\le b`$ かつ $`P(m)`$ ならば $`m\le \mathrm{fg}(P,b)`$。

リストについては次の標準事実を用いる。

- `List.map_map`：$`(\mathrm{map}\,f\,L).\mathrm{map}\,g = \mathrm{map}\,(g\circ f)\,L`$。
- `List.map_congr_left`：$`\forall x\in L,\ f\,x=g\,x`$ ならば $`\mathrm{map}\,f\,L=\mathrm{map}\,g\,L`$。
- `List.map_id`：$`\mathrm{map}\,(\lambda x.\,x)\,L = L`$。
- `List.map_append`, `List.map_take`, `List.map_dropLast`, `List.map_flatMap`：$`\mathrm{map}`$ は
  連結・前部・末尾削除・`flatMap` と可換である。
- `List.flatMap_congr`：$`\forall k\in L,\ f\,k=g\,k`$ ならば $`\mathrm{flatMap}\,f\,L=\mathrm{flatMap}\,g\,L`$。
- `List.dropLast_append_of_ne_nil`：$`P\ne[]`$ ならば $`\mathrm{dropLast}(A\mathbin{+\!\!+}P) = A\mathbin{+\!\!+}\mathrm{dropLast}\,P`$。
- `List.dropLast_subset`：$`\mathrm{dropLast}\,L`$ の要素は $`L`$ の要素である。
- `List.dropLast_eq_take`：$`\mathrm{dropLast}\,L = \mathrm{take}\,(\lvert L\rvert-1)\,L`$。
- `List.range_succ`：$`\mathrm{range}(n+1) = \mathrm{range}(n)\mathbin{+\!\!+}[n]`$。
- `List.range_succ_eq_map`：$`\mathrm{range}(n+1) = 0 \mathbin{::} (\mathrm{range}\,n).\mathrm{map}\,(\lambda j.\,j+1)`$。
- `List.range_eq_range'`：$`\mathrm{range}(n) = \mathrm{range}'(0,n)`$。
- `List.range'_eq_map_range`：$`\mathrm{range}'(a,m) = (\mathrm{range}\,m).\mathrm{map}\,(\lambda j.\,a+j)`$。
- `List.take_succ_cons`：$`\mathrm{take}\,(k+1)\,(p\mathbin{::}L) = p \mathbin{::} \mathrm{take}\,k\,L`$。
- `List.reverseRecOn`（リストの逆向き帰納法）：述語 $`\Phi`$ が $`\Phi([])`$ をみたし、
  かつ任意の $`L`$, $`q`$ について $`\Phi(L)\to\Phi(L\mathbin{+\!\!+}[q])`$ をみたすならば、$`\forall L,\ \Phi(L)`$。

---

## 0. `translate` / `ST_PS` / `oper` についての小事実

<a id="t-translate_eq_Z_iff"></a>
#### 定理 翻訳が $`\mathsf{Z}`$ になるのは空列のみ (T.translate_eq_Z_iff)

**主張** $`\mathrm{tr}\,M = \mathsf{Z} \iff M = []`$。

**証明** $`M`$ の構成子で場合分けする。

- $`M=[]`$：[(D.translate)](Mechanized.md#d-translate) より $`\mathrm{tr}\,[]=\mathsf{Z}`$ であり、$`[]=[]`$。両辺とも真。
- $`M=p\mathbin{::}L`$：[(D.translate)](Mechanized.md#d-translate) より
  $`\mathrm{tr}(p\mathbin{::}L)=\mathsf{P}(\pi_1 p,\cdot,\cdot)`$。
  [(D.Three)](Mechanized.md#d-Three) の構成子相異により $`\mathsf{P}(\cdot,\cdot,\cdot)\ne\mathsf{Z}`$。
  また $`p\mathbin{::}L\ne[]`$。両辺とも偽。∎

<a id="t-eq_Z_of_olt_one"></a>
#### 定理 $`\mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$ 未満は $`\mathsf{Z}`$ のみ (T.eq_Z_of_olt_one)

**主張** $`t\prec\mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$ ならば $`t=\mathsf{Z}`$。

**証明** $`t`$ の構成子で場合分けする。$`t=\mathsf{Z}`$ なら結論そのもの。
$`t=\mathsf{P}(a,b,c)`$ とすると、[(T.olt_P_P)](Mechanized.md#t-olt_P_P) より仮定は
```math
a<0 \ \vee\ (a=0\wedge b\prec\mathsf{Z})\ \vee\ (a=0\wedge b=\mathsf{Z}\wedge c\prec\mathsf{Z})
```
と同値である。第 1 選言は $`\mathbb{N}`$ において $`a<0`$ が偽であるから成立しない。
第 2 選言の $`b\prec\mathsf{Z}`$ と第 3 選言の $`c\prec\mathsf{Z}`$ は
[(T.not_olt_Z)](Mechanized.md#t-not_olt_Z) により成立しない。よって $`t=\mathsf{P}(a,b,c)`$ の場合は起こらない。∎

<a id="t-stps_ne_nil"></a>
#### 定理 標準形は空列でない (T.stps_ne_nil)

**主張** $`M\in\mathrm{ST\_PS}`$ ならば $`M\ne[]`$。

**証明** [(T.stps_len_pos)](Nrm.md#t-stps_len_pos) より $`0<\lvert M\rvert`$。
もし $`M=[]`$ ならば $`\lvert M\rvert=0`$ となり $`0<0`$ を得るが、これは $`<`$ の非反射性に反する。∎

<a id="t-stps_len_one"></a>
#### 定理 長さ 1 の標準形は $`[(0,0)]`$ (T.stps_len_one)

**主張** $`M\in\mathrm{ST\_PS}`$ かつ $`\lvert M\rvert=1`$ ならば $`M=[(0,0)]`$。

**証明** $`\lvert M\rvert=1`$ より $`M`$ は 1 要素列 $`M=[p]`$ と書ける。
[(T.stps_head)](Nrm.md#t-stps_head) より $`M.\mathrm{headD}(0,0)=(0,0)`$ であり、
1 要素列の `headD` は $`p`$ であるから $`p=(0,0)`$。よって $`M=[(0,0)]`$。∎

---

## 1. $`\mathrm{dom}=T_m`$ と $`T_m`$ 添字の基本列（graft）

本節では 2 つの述語 [(D.domT)](#d-domT)、[(D.based)](#d-based) と 1 つの操作 [(D.graft)](#d-graft) を導入する。
これらは Buchholz (1987) の $`\mathrm{dom}(a)=T_m`$ とその添字づけられた基本列 $`a[z]`$ に対応させるために
導入するものであり、対応の根拠となる事実は [(T.hasParent_one_iff)](#t-hasParent_one_iff) と
[(T.domT_iff)](#t-domT_iff) で証明する。定義そのものは以下の式のみによる。

<a id="d-domT"></a>
#### 定義 $`\mathrm{dom}(M)=T_m`$ (D.domT)

$`M\in\mathrm{PairSeq}`$、$`m\in\mathbb{N}`$ に対し
```math
\mathrm{dom}(M)=T_m \ :\Longleftrightarrow\ M_{1,\ell_M}=m+1 \ \wedge\ \neg\,\mathrm{hasParent}(M,1,\ell_M)
```
（$`\ell_M=\lvert M\rvert-1`$、[(D.entry)](Def.md#d-entry)、[(D.hasParent)](Def.md#d-hasParent)）。
すなわち「$`M`$ の最終対は行 1 の値が $`m+1`$ であり、かつ行 1 の親をもたない」。

<a id="d-graft"></a>
#### 定義 $`T_m`$ 添字の基本列（graft） (D.graft)

```math
\mathrm{gr}(M,z) := \mathrm{dropLast}\,M \mathbin{+\!\!+} \mathrm{map}\,\bigl(\lambda p.\ (\pi_0 p + M_{0,\ell_M},\ \pi_1 p)\bigr)\,z .
```

すなわち $`M`$ の最終対を落とし、その最終対の行 0 の値 $`M_{0,\ell_M}`$ を $`z`$ のすべての対の行 0 の値に加えて連結する。

<a id="d-based"></a>
#### 定義 先頭の行 0 の値が $`0`$ のブロック (D.based)

```math
\mathrm{based}(z) \ :\Longleftrightarrow\ z_{0,0}=0 .
```

<a id="t-based_nil"></a>
#### 定理 空列は $`\mathrm{based}`$ (T.based_nil)

**主張** $`\mathrm{based}([])`$。

**証明** [(D.entry)](Def.md#d-entry) より $`[]_{0,0}=\pi_0([]\langle 0\rangle)=\pi_0(0,0)=0`$。∎

<a id="t-graft_nil"></a>
#### 定理 空ブロックの graft (T.graft_nil)

**主張** $`\mathrm{gr}(M,[])=\mathrm{dropLast}\,M`$。

**証明** [(D.graft)](#d-graft) において $`z=[]`$ とすると $`\mathrm{map}\,f\,[]=[]`$ であり、
$`L\mathbin{+\!\!+}[]=L`$ であるから $`\mathrm{gr}(M,[])=\mathrm{dropLast}\,M`$。∎

<a id="t-not_domT_nil"></a>
#### 定理 空列は $`\mathrm{dom}=T_m`$ をみたさない (T.not_domT_nil)

**主張** 任意の $`m`$ に対し $`\neg\bigl(\mathrm{dom}([])=T_m\bigr)`$。

**証明** [(D.domT)](#d-domT) の第 1 条件は $`[]_{1,\ell_{[]}}=m+1`$ である。
$`\ell_{[]}=0-1=0`$（切り捨て減法）であり、[(D.entry)](Def.md#d-entry) より $`[]_{1,0}=\pi_1(0,0)=0`$。
よって $`0=m+1`$ が要求されるが、$`m+1\ge 1`$ であるからこれは偽である。∎

<a id="d-natDom"></a>
#### 定義 $`\mathrm{dom}`$ が $`T_m`$ 型でない (D.natDom)

```math
\mathrm{natDom}(M)\ :\Longleftrightarrow\ \forall m\in\mathbb{N},\ \neg\bigl(\mathrm{dom}(M)=T_m\bigr).
```

<a id="t-natDom_nil"></a>
#### 定理 空列は $`\mathrm{natDom}`$ (T.natDom_nil)

**主張** $`\mathrm{natDom}([])`$。

**証明** [(D.natDom)](#d-natDom) の定義そのものが $`\forall m,\ \neg(\mathrm{dom}([])=T_m)`$ であり、
これは [(T.not_domT_nil)](#t-not_domT_nil) である。∎

<a id="t-natDom_iff"></a>
#### 定理 $`\mathrm{natDom}`$ の言い換え (T.natDom_iff)

**主張**
```math
\mathrm{natDom}(M) \iff \bigl(M_{1,\ell_M}=0 \ \vee\ \mathrm{hasParent}(M,1,\ell_M)\bigr).
```

**証明**

$`(\Rightarrow)`$ $`\mathrm{natDom}(M)`$ を仮定する。$`M_{1,\ell_M}=0`$ ならば右辺の第 1 選言が成立する。
$`M_{1,\ell_M}\ne 0`$ の場合、右辺の第 2 選言を示す。背理法により $`\neg\,\mathrm{hasParent}(M,1,\ell_M)`$ と仮定する。
$`M_{1,\ell_M}\ne 0`$ より $`M_{1,\ell_M}\ge 1`$ であるから、$`m := M_{1,\ell_M}-1`$ とおけば $`M_{1,\ell_M}=m+1`$。
よって [(D.domT)](#d-domT) の 2 条件がともに成立し $`\mathrm{dom}(M)=T_m`$ となるが、これは $`\mathrm{natDom}(M)`$ の
$`m`$ における主張に矛盾する。

$`(\Leftarrow)`$ 右辺を仮定し、$`m`$ を取り $`\mathrm{dom}(M)=T_m`$、すなわち $`M_{1,\ell_M}=m+1`$ かつ
$`\neg\,\mathrm{hasParent}(M,1,\ell_M)`$ と仮定して矛盾を導く。
右辺の第 1 選言 $`M_{1,\ell_M}=0`$ が成立する場合、$`m+1=0`$ となるが $`m+1\ge 1`$ であるから矛盾。
第 2 選言 $`\mathrm{hasParent}(M,1,\ell_M)`$ が成立する場合、$`\neg\,\mathrm{hasParent}(M,1,\ell_M)`$ と直接矛盾する。∎

<a id="t-oper_eq_graft_nil_of_domT"></a>
#### 定理 $`\mathrm{dom}=T_m`$ の枝で $`M[n]`$ は最下段の graft (T.oper_eq_graft_nil_of_domT)

**主張** $`1<\lvert M\rvert`$ かつ $`\mathrm{dom}(M)=T_m`$ ならば、任意の $`n`$ に対し $`M[n]=\mathrm{gr}(M,[])`$。

**証明** [(D.domT)](#d-domT) より $`M_{1,\ell_M}=m+1`$ と $`\neg\,\mathrm{hasParent}(M,1,\ell_M)`$ を得る。

1. $`1<\lvert M\rvert`$ より $`\lvert M\rvert\ge 2`$、よって $`\ell_M=\lvert M\rvert-1\ne 0`$。
2. $`M_{1,\ell_M}=m+1\ge 1>0`$ であるから、[(D.idx1)](Def.md#d-idx1) より $`\mathrm{idx}_1(M,\ell_M)=1`$。
3. $`\neg\bigl(M_{0,\ell_M}=0 \wedge M_{1,\ell_M}=0\bigr)`$：第 2 連言項は $`m+1=0`$ を要求するが $`m+1\ge 1`$。
4. 2 により $`\neg\,\mathrm{hasParent}(M,\mathrm{idx}_1(M,\ell_M),\ell_M)`$ は
   $`\neg\,\mathrm{hasParent}(M,1,\ell_M)`$ に一致する。

1, 3, 4 に [(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent) を適用して
$`M[n]=\mathrm{Pred}\,M`$。[(D.Pred)](Def.md#d-Pred) は $`\lvert M\rvert\le 1`$ か否かの場合分けであり、
$`\lvert M\rvert\ge 2`$ であるから $`\mathrm{Pred}\,M=\mathrm{dropLast}\,M`$。
[(T.graft_nil)](#t-graft_nil) より $`\mathrm{gr}(M,[])=\mathrm{dropLast}\,M`$ であるから、両者は等しい。∎

### 1a. 定義の検証（$`\mathrm{hasParent}`$ と行 0 祖先条件）

[(D.domT)](#d-domT) の第 2 条件 $`\neg\,\mathrm{hasParent}(M,1,\ell_M)`$ が
「$`\ell_M`$ の真の行 0 祖先はすべて行 1 の値が $`M_{1,\ell_M}`$ 以上である」と同値であることを、
[(D.nextrel1)](Def.md#d-nextrel1) についての定理として示す。

<a id="d-r1cand"></a>
#### 定義 行 1 親候補 (D.r1cand)

```math
\mathrm{r1cand}(M,j_1,j_0)\ :\Longleftrightarrow\ j_0<j_1 \ \wedge\ j_0\le^M_0 j_1 \ \wedge\ M_{1,j_0}<M_{1,j_1}
```
（[(D.le0)](Def.md#d-le0)）。すなわち「$`j_0`$ は $`j_1`$ の真の行 0 祖先であって行 1 の値が真に小さい」。

<a id="t-hasParent_one_iff"></a>
#### 定理 行 1 親の存在判定 (T.hasParent_one_iff)

**主張** $`j_1<\lvert M\rvert`$ ならば
```math
\mathrm{hasParent}(M,1,j_1) \iff \exists j_0,\ \mathrm{r1cand}(M,j_1,j_0).
```

**証明** まず、[(D.nextR)](Def.md#d-nextR) の場合分けは `i = 0` か否かであり $`1\ne 0`$ であるから、
任意の $`j_0`$ について
```math
(\ast)\qquad j_0\to^M_1 j_1 \ \text{（$\mathrm{nextR}$ の意味）} \iff j_0\to^M_1 j_1\ \text{（$\mathrm{nextrel1}$ の意味）}
```
であり、以下では両者を同一視する。

$`(\Rightarrow)`$ $`\mathrm{hasParent}(M,1,j_1)`$ は $`\exists!\,j_0,\ j_0\to^M_1 j_1`$ であるから、
特に $`j_0\to^M_1 j_1`$ なる $`j_0`$ が存在する。[(D.nextrel1)](Def.md#d-nextrel1) の条件 3, 5, 4 はそれぞれ
$`j_0<j_1`$、$`j_0\le^M_0 j_1`$、$`M_{1,j_0}<M_{1,j_1}`$ であるから、$`\mathrm{r1cand}(M,j_1,j_0)`$ が成り立つ。

$`(\Leftarrow)`$ $`\mathrm{r1cand}(M,j_1,j_0)`$ なる $`j_0`$ を取る。述語
```math
P(k)\ :\equiv\ \mathrm{r1cand}(M,j_1,k)
```
に対し $`g:=\mathrm{fg}(P,j_1)`$ とおく。$`j_0<j_1`$ より $`j_0\le j_1`$ であり $`P(j_0)`$ が成り立つから、
`Nat.findGreatest_spec` より $`P(g)`$、すなわち
```math
g<j_1,\qquad g\le^M_0 j_1,\qquad M_{1,g}<M_{1,j_1}
```
が成り立つ。また $`P(k)`$ をみたす任意の $`k`$ について $`k<j_1`$ すなわち $`k\le j_1`$ であるから、
`Nat.le_findGreatest` より
```math
(\dagger)\qquad \forall k,\ P(k)\to k\le g .
```

$`g`$ が求める一意の親であることを示す。まず $`g\to^M_1 j_1`$、すなわち
[(D.nextrel1)](Def.md#d-nextrel1) の 6 条件を確かめる。

1. $`g<\lvert M\rvert`$：$`g<j_1`$ と $`j_1<\lvert M\rvert`$ の推移性による。
2. $`j_1<\lvert M\rvert`$：仮定。
3. $`g<j_1`$：$`P(g)`$ の第 1 成分。
4. $`M_{1,g}<M_{1,j_1}`$：$`P(g)`$ の第 3 成分。
5. $`g\le^M_0 j_1`$：$`P(g)`$ の第 2 成分。
6. $`\forall j,\ (g<j \wedge j\le^M_0 j_1)\to M_{1,j_1}\le M_{1,j}`$：
   $`g<j`$ かつ $`j\le^M_0 j_1`$ とし、結論を否定して $`M_{1,j}<M_{1,j_1}`$ と仮定する。
   $`j\le^M_0 j_1`$ の第 3 成分は $`\mathrm{ReflTransGen}(\to^M_0)\ j\ j_1`$ であるから、
   [(T.nextrel0_rtrancl_index_le)](Mechanized.md#t-nextrel0_rtrancl_index_le) より $`j\le j_1`$。
   - $`j=j_1`$ の場合：$`M_{1,j_1}<M_{1,j_1}`$ となり $`<`$ の非反射性に反する。
   - $`j<j_1`$ の場合：$`j<j_1`$、$`j\le^M_0 j_1`$、$`M_{1,j}<M_{1,j_1}`$ より $`P(j)`$ が成り立つ。
     $`(\dagger)`$ より $`j\le g`$ となるが、これは $`g<j`$ に矛盾する。

次に一意性を示す。$`y\to^M_1 j_1`$ とする。[(D.nextrel1)](Def.md#d-nextrel1) の条件 3, 5, 4 より $`P(y)`$、
よって $`(\dagger)`$ から $`y\le g`$。$`y=g`$ ならば示すべきことはない。$`y<g`$ と仮定すると、
$`y`$ についての条件 6 を $`j:=g`$ に適用できる（$`y<g`$ は仮定、$`g\le^M_0 j_1`$ は $`P(g)`$ の第 2 成分）。
これより $`M_{1,j_1}\le M_{1,g}`$ を得るが、$`P(g)`$ の第 3 成分は $`M_{1,g}<M_{1,j_1}`$ であり矛盾する。
よって $`y=g`$。以上より $`\exists!\,j_0,\ j_0\to^M_1 j_1`$、すなわち $`\mathrm{hasParent}(M,1,j_1)`$。∎

<a id="t-domT_iff"></a>
#### 定理 $`\mathrm{dom}=T_m`$ の行 0 祖先条件による表示 (T.domT_iff)

**主張** $`M\ne[]`$ ならば
```math
\mathrm{dom}(M)=T_m \iff \Bigl(M_{1,\ell_M}=m+1 \ \wedge\ \forall j_0,\ j_0<\ell_M \to j_0\le^M_0 \ell_M \to m+1\le M_{1,j_0}\Bigr).
```

**証明** $`M\ne[]`$ より $`0<\lvert M\rvert`$、よって $`\ell_M=\lvert M\rvert-1<\lvert M\rvert`$。
したがって [(T.hasParent_one_iff)](#t-hasParent_one_iff) を $`j_1:=\ell_M`$ に適用でき、
[(D.domT)](#d-domT) の第 2 条件は
```math
\neg\,\exists j_0,\ \bigl(j_0<\ell_M \wedge j_0\le^M_0\ell_M \wedge M_{1,j_0}<M_{1,\ell_M}\bigr)
```
と同値である。

$`(\Rightarrow)`$ 第 1 条件 $`M_{1,\ell_M}=m+1`$ はそのまま。$`j_0<\ell_M`$ かつ $`j_0\le^M_0\ell_M`$ とし、
結論 $`m+1\le M_{1,j_0}`$ を否定して $`M_{1,j_0}<m+1=M_{1,\ell_M}`$ と仮定すると、
$`\mathrm{r1cand}(M,\ell_M,j_0)`$ が成り立ち、上の否定に矛盾する。

$`(\Leftarrow)`$ 第 1 条件はそのまま。$`\mathrm{r1cand}(M,\ell_M,j_0)`$ なる $`j_0`$ が存在したとすると、
右辺の全称条件を $`j_0`$ に適用して $`m+1\le M_{1,j_0}`$ を得る。一方 $`\mathrm{r1cand}`$ の第 3 成分と
第 1 条件より $`M_{1,j_0}<M_{1,\ell_M}=m+1`$。両者から $`m+1\le M_{1,j_0}<m+1`$ となり矛盾する。∎

### 1b. 検証例：1 対からなる列 $`[(x,m+1)]`$

Lean 側に無名の `example` として置かれている計算を記す。

1. $`\mathrm{dom}([(x,m+1)])=T_m`$。
   $`\ell=1-1=0`$、$`[(x,m+1)]_{1,0}=m+1`$ で第 1 条件が成立する。第 2 条件は、
   もし $`j_0\to^M_1 0`$ なる $`j_0`$ が存在すれば [(D.nextrel1)](Def.md#d-nextrel1) の条件 3 より $`j_0<0`$ となり、
   $`\mathbb{N}`$ では偽であることによる。
2. $`\mathrm{gr}([(x,m+1)],z) = \mathrm{map}\,(\lambda p.\,(\pi_0 p+x,\pi_1 p))\,z`$。
   $`\mathrm{dropLast}[(x,m+1)]=[]`$ かつ $`[(x,m+1)]_{0,0}=x`$ による。とくに $`x=0`$ のときは
   $`\mathrm{gr}([(0,m+1)],z)=z`$ である。
3. $`\neg\bigl(\mathrm{dom}([(0,0)])=T_m\bigr)`$。$`[(0,0)]_{1,0}=0`$ であり $`0=m+1`$ は偽。

### 1c. 検証例：$`\mathrm{based}`$ 条件が必要であること

$`M=[(0,3),(1,2),(1,1)]`$ とする。

4. $`\mathrm{dom}(M)=T_0`$。[(T.domT_iff)](#t-domT_iff) を用いる。$`\ell_M=2`$、$`M_{1,2}=1=0+1`$ で第 1 条件が成立。
   第 2 条件は $`j_0<2`$ すなわち $`j_0\in\{0,1\}`$ について $`0+1\le M_{1,j_0}`$ を要求するが、
   $`M_{1,0}=3\ge 1`$、$`M_{1,1}=2\ge 1`$ である。
5. $`\mathrm{tr}[(0,0)]=\mathrm{tr}[(2,0)]=\mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$。
   どちらも [(D.translate)](Mechanized.md#d-translate) で残りが空列であり、行 1 の値が $`0`$ である。
6. $`\mathrm{gr}(M,[(0,0)])=[(0,3),(1,2),(1,0)]`$。
   $`\mathrm{dropLast}\,M=[(0,3),(1,2)]`$、$`M_{0,2}=1`$ であるから $`[(0,0)]`$ は $`[(0+1,0)]=[(1,0)]`$ に移る。
7. $`\mathrm{tr}[(0,3),(1,2),(1,0)]=\mathsf{P}(3,\mathsf{P}(2,\mathsf{Z},\mathsf{P}(0,\mathsf{Z},\mathsf{Z})),\mathsf{Z})`$。
   先頭対 $`(0,3)`$、残り $`[(1,2),(1,0)]`$ はどちらも行 0 が $`1>0`$ だから全体が引数側に入る。
   次に $`[(1,2),(1,0)]`$：先頭 $`(1,2)`$ に対し残り $`[(1,0)]`$ の行 0 は $`1`$ で $`1<1`$ は偽、
   よって引数は空、後続和が $`\mathrm{tr}[(1,0)]=\mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$。
8. $`\mathrm{gr}(M,[(2,0)])=[(0,3),(1,2),(3,0)]`$（$`2+1=3`$）。
9. $`\mathrm{tr}[(0,3),(1,2),(3,0)]=\mathsf{P}(3,\mathsf{P}(2,\mathsf{P}(0,\mathsf{Z},\mathsf{Z}),\mathsf{Z}),\mathsf{Z})`$。
   先頭対 $`(0,3)`$ の後は行 0 が $`1,3`$ でどちらも $`>0`$。次に $`[(1,2),(3,0)]`$：先頭 $`(1,2)`$ に対し
   残り $`[(3,0)]`$ の行 0 は $`3`$ で $`1<3`$ が真、よって $`(3,0)`$ は引数側に入る。

6 と 8 は同じ $`\mathrm{tr}`$ 値をもつ 2 つのブロック（項目 5）を graft した結果であり、
項目 7 と 9 の $`\mathrm{tr}`$ 値は異なる。したがって [(D.graft)](#d-graft) を「$`\mathrm{tr}\,z`$ の代入」として
用いるには [(D.based)](#d-based) の条件が必要である。

---

## 2. 作用素 $`A_u`$ と反復帰納的集合 $`W_u`$

<a id="d-lfpS"></a>
#### 定義 最小不動点 (D.lfpS)

$`f`$ をペア列の集合上の作用素とする。
```math
\mathrm{lfp}\,f := \bigcap\,\{\,Y \mid f(Y)\subseteq Y\,\}
= \{\,x \mid \forall Y,\ f(Y)\subseteq Y \to x\in Y\,\}.
```

すなわち $`f`$ のすべての前不動点（$`f(Y)\subseteq Y`$ なる $`Y`$）の共通部分である。

<a id="t-lfpS_lowerbound"></a>
#### 定理 最小性 (T.lfpS_lowerbound)

**主張** $`f(Y)\subseteq Y`$ ならば $`\mathrm{lfp}\,f\subseteq Y`$。

**証明** $`x\in\mathrm{lfp}\,f`$ とする。[(D.lfpS)](#d-lfpS) より $`x`$ は
「$`f(Y')\subseteq Y'`$ なる任意の $`Y'`$ について $`x\in Y'`$」をみたす。これを $`Y':=Y`$ と仮定 $`f(Y)\subseteq Y`$ に
適用して $`x\in Y`$ を得る。∎

<a id="t-lfpS_unfold_le"></a>
#### 定理 不動点方程式の $`\subseteq`$ 方向 (T.lfpS_unfold_le)

**主張** $`f`$ が単調ならば $`f(\mathrm{lfp}\,f)\subseteq\mathrm{lfp}\,f`$。

**証明** $`x\in f(\mathrm{lfp}\,f)`$ とする。[(D.lfpS)](#d-lfpS) より、$`f(Y)\subseteq Y`$ なる任意の $`Y`$ について
$`x\in Y`$ を示せばよい。[(T.lfpS_lowerbound)](#t-lfpS_lowerbound) より $`\mathrm{lfp}\,f\subseteq Y`$ であり、
$`f`$ の単調性より $`f(\mathrm{lfp}\,f)\subseteq f(Y)`$。よって $`x\in f(Y)\subseteq Y`$。∎

<a id="t-lfpS_unfold_ge"></a>
#### 定理 不動点方程式の $`\supseteq`$ 方向 (T.lfpS_unfold_ge)

**主張** $`f`$ が単調ならば $`\mathrm{lfp}\,f\subseteq f(\mathrm{lfp}\,f)`$。

**証明** [(T.lfpS_lowerbound)](#t-lfpS_lowerbound) を $`Y:=f(\mathrm{lfp}\,f)`$ に適用すればよい。
その前提 $`f\bigl(f(\mathrm{lfp}\,f)\bigr)\subseteq f(\mathrm{lfp}\,f)`$ は、
[(T.lfpS_unfold_le)](#t-lfpS_unfold_le) の結論 $`f(\mathrm{lfp}\,f)\subseteq\mathrm{lfp}\,f`$ に
$`f`$ の単調性を適用して得られる。∎

<a id="t-lfpS_unfold"></a>
#### 定理 不動点方程式 (T.lfpS_unfold)

**主張** $`f`$ が単調ならば $`f(\mathrm{lfp}\,f)=\mathrm{lfp}\,f`$。

**証明** 集合の外延性（両包含）による。$`\subseteq`$ は [(T.lfpS_unfold_le)](#t-lfpS_unfold_le)、
$`\supseteq`$ は [(T.lfpS_unfold_ge)](#t-lfpS_unfold_ge)。∎

<a id="d-Aop"></a>
#### 定義 作用素 $`A_u`$ (D.Aop)

族パラメータ $`\mathcal F:\mathbb{N}\to`$（ペア列の集合）、水準 $`u\in\mathbb{N}`$、集合 $`X`$、ペア列 $`M`$ に対し
```math
M\in A^{\mathcal F}_u(X)\ :\Longleftrightarrow\
\begin{cases}
\text{(枝 1)} & \lvert M\rvert\le 1 \ \wedge\ M_{1,0}=0\\
\text{(枝 2)} & \mathrm{natDom}(M)\ \wedge\ \forall n,\ 1\le n \to M[n]\in X\\
\text{(枝 3)} & \exists m,\ m<u \ \wedge\ \mathrm{dom}(M)=T_m \ \wedge\
 \bigl(\forall z\in\mathcal F(m),\ \mathrm{based}(z)\to \mathrm{gr}(M,z)\in X\bigr)
\end{cases}
```
の 3 つの選言である（[(D.natDom)](#d-natDom), [(D.oper)](Def.md#d-oper), [(D.domT)](#d-domT),
[(D.based)](#d-based), [(D.graft)](#d-graft)）。

枝 1 は $`\mathrm{tr}\,M\in\{\mathsf{Z},\mathsf{P}(0,\mathsf{Z},\mathsf{Z})\}`$ となる終端状態、
枝 2 は $`\mathbb{N}`$ 添字の基本列 $`M[n]`$、枝 3 は $`T_m`$ 添字の基本列 $`\mathrm{gr}(M,z)`$ に対応する。

<a id="d-Aset"></a>
#### 定義 集合としての $`A_u`$ (D.Aset)

```math
A^{\mathcal F}_u(X) := \{\,M \mid M\in A^{\mathcal F}_u(X)\,\}
```
すなわち [(D.Aop)](#d-Aop) の述語をペア列の集合とみなしたものである。

<a id="t-Aop_mono_X"></a>
#### 定理 $`A_u`$ の第 2 引数についての単調性（点ごと） (T.Aop_mono_X)

**主張** $`M\in A^{\mathcal F}_u(X)`$ かつ $`X\subseteq Y`$ ならば $`M\in A^{\mathcal F}_u(Y)`$。

**証明** [(D.Aop)](#d-Aop) の 3 つの選言で場合分けする。

- 枝 1：条件 $`\lvert M\rvert\le 1\wedge M_{1,0}=0`$ は $`X`$ を含まないから、そのまま枝 1 が成立する。
- 枝 2：$`\mathrm{natDom}(M)`$ はそのまま。各 $`n\ge 1`$ について $`M[n]\in X\subseteq Y`$ より $`M[n]\in Y`$。
- 枝 3：$`m`$、$`m<u`$、$`\mathrm{dom}(M)=T_m`$ はそのまま。各 $`z\in\mathcal F(m)`$ で $`\mathrm{based}(z)`$ なるものについて
  $`\mathrm{gr}(M,z)\in X\subseteq Y`$ より $`\mathrm{gr}(M,z)\in Y`$。∎

<a id="t-Aset_mono"></a>
#### 定理 $`A_u`$ は単調 (T.Aset_mono)

**主張** $`X\mapsto A^{\mathcal F}_u(X)`$ は単調である。

**証明** $`X\subseteq Y`$ とし、$`M\in A^{\mathcal F}_u(X)`$ とする。
[(T.Aop_mono_X)](#t-Aop_mono_X) より $`M\in A^{\mathcal F}_u(Y)`$。∎

<a id="t-Aop_mono_level"></a>
#### 定理 水準についての単調性 (T.Aop_mono_level)

**主張** $`u\le v`$ かつ $`M\in A^{\mathcal F}_u(X)`$ ならば $`M\in A^{\mathcal F}_v(X)`$。

**証明** [(D.Aop)](#d-Aop) で $`u`$ が現れるのは枝 3 の条件 $`m<u`$ のみである。

- 枝 1、枝 2：条件に $`u`$ が現れないからそのまま成立する。
- 枝 3：$`m<u`$ と $`u\le v`$ より $`m<v`$。他の条件は変わらない。∎

<a id="t-Aop_cong"></a>
#### 定理 $`A_u`$ は族の $`u`$ 未満の段階しか読まない (T.Aop_cong)

**主張** $`\forall m,\ m<u\to\mathcal F(m)=\mathcal G(m)`$ ならば
```math
M\in A^{\mathcal F}_u(X) \iff M\in A^{\mathcal G}_u(X).
```

**証明** 両方向とも [(D.Aop)](#d-Aop) の 3 選言で場合分けする。枝 1 と枝 2 には $`\mathcal F`$ が現れないから、
そのまま移る。枝 3 の場合、証人 $`m`$ は $`m<u`$ をみたすから仮定より $`\mathcal F(m)=\mathcal G(m)`$ であり、
量化域 $`z\in\mathcal F(m)`$ と $`z\in\mathcal G(m)`$ は同一の条件である。よって枝 3 の条件も両向きに移る。∎

<a id="d-Wf"></a>
#### 定義 段階族 (D.Wf)

$`\mathbb{N}`$ に関する再帰で
```math
W^{(0)}_m := \emptyset,\qquad
W^{(v+1)}_m := \begin{cases}\mathrm{lfp}\bigl(X\mapsto A^{W^{(v)}}_v(X)\bigr) & (m=v)\\[2pt]
W^{(v)}_m & (m\ne v)\end{cases}
```
と定める（[(D.lfpS)](#d-lfpS), [(D.Aset)](#d-Aset)）。ここで $`W^{(v)}`$ は第 1 添字を $`v`$ に固定した族
$`m\mapsto W^{(v)}_m`$ である。

<a id="d-W"></a>
#### 定義 反復帰納的集合 $`W_u`$ (D.W)

```math
W_u := W^{(u+1)}_u .
```

<a id="t-Wf_coh"></a>
#### 定理 段階族の整合性 (T.Wf_coh)

**主張** $`m<n`$ ならば $`W^{(n)}_m = W^{(m+1)}_m`$。

**証明** $`n`$ に関する自然数の帰納法。帰納法の述語は
```math
\Phi(n) :\equiv \forall m,\ m<n \to W^{(n)}_m = W^{(m+1)}_m .
```

- 基底段 $`n=0`$：前提 $`m<0`$ は $`\mathbb{N}`$ において偽であるから $`\Phi(0)`$ は成立する。
- 帰納段 $`n=v+1`$：帰納法の仮定は $`\Phi(v)`$、すなわち $`\forall m,\ m<v\to W^{(v)}_m=W^{(m+1)}_m`$ である。
  $`m<v+1`$ なる $`m`$ を取る。
  - $`m=v`$ の場合：[(D.Wf)](#d-Wf) より $`W^{(v+1)}_v`$ は $`m=v`$ の分岐であり
    $`\mathrm{lfp}(X\mapsto A^{W^{(v)}}_v(X))`$。一方 $`W^{(m+1)}_m`$ は $`m=v`$ を代入すると同じ式である。
    よって両辺は定義により同一である。
  - $`m\ne v`$ の場合：$`m<v+1`$ と $`m\ne v`$ より $`m<v`$。[(D.Wf)](#d-Wf) の第 2 分岐より
    $`W^{(v+1)}_m = W^{(v)}_m`$ であり、帰納法の仮定 $`\Phi(v)`$ を $`m`$ に適用して
    $`W^{(v)}_m = W^{(m+1)}_m`$。∎

<a id="t-Wf_eq_W"></a>
#### 定理 段階族と $`W`$ の一致 (T.Wf_eq_W)

**主張** $`m<n`$ ならば $`W^{(n)}_m = W_m`$。

**証明** [(D.W)](#d-W) より $`W_m = W^{(m+1)}_m`$ であり、これは [(T.Wf_coh)](#t-Wf_coh) の結論そのものである。∎

<a id="t-W_unfold"></a>
#### 定理 $`W_u`$ の定義方程式 (T.W_unfold)

**主張** $`W_u = \mathrm{lfp}\bigl(X\mapsto A^{W}_u(X)\bigr)`$。ここで $`W`$ は族 $`m\mapsto W_m`$ である。

**証明** 3 段に分ける。

1. [(D.W)](#d-W) と [(D.Wf)](#d-Wf) より
   $`W_u = W^{(u+1)}_u`$ であり、$`W^{(u+1)}_u`$ は $`m=u`$、$`v=u`$ の分岐であるから
   $`W_u = \mathrm{lfp}\bigl(X\mapsto A^{W^{(u)}}_u(X)\bigr)`$。
2. $`m<u`$ なる任意の $`m`$ について [(T.Wf_eq_W)](#t-Wf_eq_W) より $`W^{(u)}_m = W_m`$。
3. よって任意の $`X`$ について [(T.Aop_cong)](#t-Aop_cong)（$`\mathcal F:=W^{(u)}`$, $`\mathcal G:=W`$）より
   $`A^{W^{(u)}}_u(X) = A^{W}_u(X)`$。$`X`$ は任意であったから、関数の外延性により
   2 つの作用素 $`X\mapsto A^{W^{(u)}}_u(X)`$ と $`X\mapsto A^{W}_u(X)`$ は等しい。

1 の右辺の作用素を 3 により置き換えて主張を得る。∎

<a id="t-A1"></a>
#### 定理 (A1) 不動点方程式 (T.A1)

**主張** $`A^{W}_u(W_u) = W_u`$。

**証明** [(T.W_unfold)](#t-W_unfold) により $`W_u`$ を $`\mathrm{lfp}(X\mapsto A^W_u(X))`$ で置き換える。
[(T.Aset_mono)](#t-Aset_mono) よりこの作用素は単調であるから、
[(T.lfpS_unfold)](#t-lfpS_unfold) が適用できて主張を得る。∎

<a id="t-A2"></a>
#### 定理 (A2) 最小不動点帰納法 (T.A2)

**主張** $`A^{W}_u(Y)\subseteq Y`$ ならば $`W_u\subseteq Y`$。

**証明** [(T.W_unfold)](#t-W_unfold) により $`W_u=\mathrm{lfp}(X\mapsto A^W_u(X))`$。
仮定はこの作用素の前不動点条件であるから、[(T.lfpS_lowerbound)](#t-lfpS_lowerbound) より $`W_u\subseteq Y`$。∎

これが本章で「$`W_u`$ に関する最小不動点帰納法」と呼ぶ推論である。読み下すと次のとおり。

> 述語 $`Y`$ が、**$`A_u`$ の 3 つの枝それぞれについて**「その枝の前提がすべて $`Y`$ で成り立つならば結論も $`Y`$ で成り立つ」
> をみたすならば、$`W_u`$ のすべての元は $`Y`$ をみたす。

<a id="t-A2'"></a>
#### 定理 (A2′) 最小不動点帰納法（点ごとの形） (T.A2')

**主張** $`\bigl(\forall M,\ M\in A^{W}_u(Y)\to M\in Y\bigr)`$ ならば $`W_u\subseteq Y`$。

**証明** 前提は $`A^{W}_u(Y)\subseteq Y`$ を [(D.Aset)](#d-Aset) に沿って点ごとに書いたものであるから、
[(T.A2)](#t-A2) がそのまま適用できる。∎

<a id="t-A1_intro"></a>
#### 定理 $`W_u`$ の導入規則 (T.A1_intro)

**主張** $`M\in A^{W}_u(W_u)`$ ならば $`M\in W_u`$。

**証明** [(T.A1)](#t-A1) の等式 $`A^{W}_u(W_u)=W_u`$ の左辺の元であるから、右辺の元でもある。∎

<a id="t-W_nil"></a>
#### 定理 (W1) 空列は $`W_u`$ の元 (T.W_nil)

**主張** $`[]\in W_u`$。

**証明** [(T.A1_intro)](#t-A1_intro) により $`[]\in A^{W}_u(W_u)`$ を示せばよく、枝 1 を用いる。
$`\lvert[]\rvert=0\le 1`$ であり、[(D.entry)](Def.md#d-entry) より $`[]_{1,0}=\pi_1(0,0)=0`$。∎

<a id="t-W_mono"></a>
#### 定理 水準についての単調性 (T.W_mono)

**主張** $`u\le v`$ ならば $`W_u\subseteq W_v`$。

**証明** [(T.A2')](#t-A2') を $`Y:=W_v`$ として用いる。これは $`W_u`$ に関する最小不動点帰納法であり、
帰納法の述語は
```math
\Phi(M) :\equiv M\in W_v
```
である。示すべきことは $`\forall M,\ M\in A^{W}_u(W_v)\to M\in W_v`$。
$`M\in A^{W}_u(W_v)`$ とすると、$`u\le v`$ と [(T.Aop_mono_level)](#t-Aop_mono_level) より $`M\in A^{W}_v(W_v)`$、
よって [(T.A1_intro)](#t-A1_intro) より $`M\in W_v`$。∎

---

## 3. 橋：共終性のもとで $`W_u`$ の元はすべて可到達

本節では共終性を明示の仮定
```math
\mathrm{hcof}:\quad \forall M,N,\ M\in\mathrm{ST\_PS}\to N\in\mathrm{ST\_PS}\to \mathrm{tr}\,N\prec\mathrm{tr}\,M
\to \exists n,\ 1\le n \wedge \mathrm{tr}\,N\preceq\mathrm{tr}(M[n])
```
として受け取る（この仮定は [(T.pss_cofinality_holds)](Final.md#t-pss_cofinality_holds) が与える）。

<a id="d-Rst"></a>
#### 定義 目標関係 (D.Rst)

```math
a\mathrel{R}b \ :\Longleftrightarrow\ a\in\mathrm{ST\_PS} \ \wedge\ b\in\mathrm{ST\_PS} \ \wedge\ \mathrm{tr}\,a\prec\mathrm{tr}\,b .
```

<a id="t-acc_of_translate_eq"></a>
#### 定理 可到達性は $`\mathrm{tr}`$ の値のみに依る (T.acc_of_translate_eq)

**主張** $`a\in\mathrm{ST\_PS}`$、$`\mathrm{tr}\,b=\mathrm{tr}\,a`$、$`\mathrm{Acc}\,R\,a`$ ならば $`\mathrm{Acc}\,R\,b`$。

**証明** `Acc.intro` を用いる。$`y\mathrel{R}b`$ なる任意の $`y`$ について $`\mathrm{Acc}\,R\,y`$ を示せばよい。
[(D.Rst)](#d-Rst) より $`y\in\mathrm{ST\_PS}`$、$`b\in\mathrm{ST\_PS}`$、$`\mathrm{tr}\,y\prec\mathrm{tr}\,b`$。
仮定 $`\mathrm{tr}\,b=\mathrm{tr}\,a`$ を代入して $`\mathrm{tr}\,y\prec\mathrm{tr}\,a`$。
$`y\in\mathrm{ST\_PS}`$ と $`a\in\mathrm{ST\_PS}`$ と合わせて $`y\mathrel{R}a`$。
`Acc.inv` を $`\mathrm{Acc}\,R\,a`$ と $`y\mathrel{R}a`$ に適用して $`\mathrm{Acc}\,R\,y`$ を得る。∎

<a id="t-acc_of_nat_branch"></a>
#### 定理 $`\mathbb{N}`$ 枝の可到達性ステップ (T.acc_of_nat_branch)

**主張** $`\mathrm{hcof}`$ を仮定する。$`c\in\mathrm{ST\_PS}`$ かつ
$`\forall n,\ 1\le n\to\mathrm{Acc}\,R\,(c[n])`$ ならば $`\mathrm{Acc}\,R\,c`$。

**証明** `Acc.intro` を用いる。$`b\mathrel{R}c`$ なる任意の $`b`$、すなわち
$`b\in\mathrm{ST\_PS}`$、$`c\in\mathrm{ST\_PS}`$、$`\mathrm{tr}\,b\prec\mathrm{tr}\,c`$ なる $`b`$ について
$`\mathrm{Acc}\,R\,b`$ を示す。

$`\mathrm{hcof}`$ を $`M:=c`$, $`N:=b`$ に適用して、$`1\le n`$ かつ $`\mathrm{tr}\,b\preceq\mathrm{tr}(c[n])`$ なる $`n`$ を得る。
仮定より $`\mathrm{Acc}\,R\,(c[n])`$ であり、[(D.ST_PS)](Def.md#d-ST_PS) の導入規則 (oper) より
$`c[n]\in\mathrm{ST\_PS}`$ である。[(D.ole)](Mechanized.md#d-ole) により $`\preceq`$ は 2 つの場合に分かれる。

- $`\mathrm{tr}\,b\prec\mathrm{tr}(c[n])`$ の場合：$`b\in\mathrm{ST\_PS}`$、$`c[n]\in\mathrm{ST\_PS}`$ と合わせて
  $`b\mathrel{R}(c[n])`$。`Acc.inv` より $`\mathrm{Acc}\,R\,b`$。
- $`\mathrm{tr}\,b=\mathrm{tr}(c[n])`$ の場合：[(T.acc_of_translate_eq)](#t-acc_of_translate_eq) を
  $`a:=c[n]`$, $`b:=b`$ に適用して $`\mathrm{Acc}\,R\,b`$。∎

<a id="t-acc_of_W"></a>
#### 定理 橋：$`W_u`$ の元は可到達 (T.acc_of_W)

**主張** $`\mathrm{hcof}`$ を仮定する。任意の $`u`$ と $`M\in W_u`$ について $`\mathrm{Acc}\,R\,M`$。

**証明** [(T.A2')](#t-A2') による $`W_u`$ の最小不動点帰納法である。帰納法の述語は
```math
\Phi(M) :\equiv \mathrm{Acc}\,R\,M
```
であり、示すべきことは
```math
\forall c,\ c\in A^{W}_u\bigl(\{M\mid\mathrm{Acc}\,R\,M\}\bigr)\ \to\ \mathrm{Acc}\,R\,c .
```

$`c`$ を取り、$`c\in A^W_u(\{M\mid \mathrm{Acc}\,R\,M\})`$ とする。$`c\in\mathrm{ST\_PS}`$ か否かで場合分けする。

**場合 A：$`c\notin\mathrm{ST\_PS}`$.** `Acc.intro` を用いる。$`y\mathrel{R}c`$ なる $`y`$ が存在すれば
[(D.Rst)](#d-Rst) の第 2 成分より $`c\in\mathrm{ST\_PS}`$ となり仮定に反する。
よって $`c`$ は $`R`$ について前者をもたず、$`\mathrm{Acc}\,R\,c`$。

**場合 B：$`c\in\mathrm{ST\_PS}`$.** [(T.stps_ne_nil)](#t-stps_ne_nil) より $`c\ne[]`$。
[(D.Aop)](#d-Aop) の 3 つの枝で場合分けする。

- **枝 1**：$`\lvert c\rvert\le 1`$ かつ $`c_{1,0}=0`$。
  [(T.stps_len_pos)](Nrm.md#t-stps_len_pos) より $`0<\lvert c\rvert`$ であるから $`\lvert c\rvert=1`$、
  すなわち $`c=[p]`$ と書ける。$`c_{1,0}=\pi_1 p`$ であるから $`\pi_1 p=0`$。
  [(D.translate)](Mechanized.md#d-translate) より、残りの列が空であることから
  ```math
  \mathrm{tr}[p]=\mathsf{P}(\pi_1 p,\ \mathrm{tr}\,[],\ \mathrm{tr}\,[])=\mathsf{P}(0,\mathsf{Z},\mathsf{Z}).
  ```
  `Acc.intro` を用いる。$`y\mathrel{R}c`$ なる $`y`$ を取ると $`\mathrm{tr}\,y\prec\mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$、
  [(T.eq_Z_of_olt_one)](#t-eq_Z_of_olt_one) より $`\mathrm{tr}\,y=\mathsf{Z}`$、
  [(T.translate_eq_Z_iff)](#t-translate_eq_Z_iff) より $`y=[]`$。
  一方 [(D.Rst)](#d-Rst) より $`y\in\mathrm{ST\_PS}`$ であり
  [(T.stps_ne_nil)](#t-stps_ne_nil) より $`y\ne[]`$。矛盾であるから $`y`$ は存在せず、$`\mathrm{Acc}\,R\,c`$。
- **枝 2**：$`\forall n\ge 1,\ c[n]\in\{M\mid\mathrm{Acc}\,R\,M\}`$。
  これは [(T.acc_of_nat_branch)](#t-acc_of_nat_branch) の仮定そのものであり、$`\mathrm{Acc}\,R\,c`$ を得る。
- **枝 3**：$`m<u`$、$`\mathrm{dom}(c)=T_m`$、$`\forall z\in W_m,\ \mathrm{based}(z)\to\mathrm{gr}(c,z)`$ が可到達。
  $`1<\lvert c\rvert`$ か否かで場合分けする。
  - $`1<\lvert c\rvert`$ の場合：$`z:=[]`$ を取る。[(T.W_nil)](#t-W_nil) より $`[]\in W_m`$、
    [(T.based_nil)](#t-based_nil) より $`\mathrm{based}([])`$。よって $`\mathrm{Acc}\,R\,(\mathrm{gr}(c,[]))`$。
    各 $`n\ge 1`$ について [(T.oper_eq_graft_nil_of_domT)](#t-oper_eq_graft_nil_of_domT) より
    $`c[n]=\mathrm{gr}(c,[])`$ であるから $`\mathrm{Acc}\,R\,(c[n])`$。
    これに [(T.acc_of_nat_branch)](#t-acc_of_nat_branch) を適用して $`\mathrm{Acc}\,R\,c`$。
  - $`\lvert c\rvert\le 1`$ の場合：[(T.stps_len_pos)](Nrm.md#t-stps_len_pos) と合わせて $`\lvert c\rvert=1`$、
    [(T.stps_len_one)](#t-stps_len_one) より $`c=[(0,0)]`$。
    一方 $`\mathrm{dom}(c)=T_m`$ の第 1 条件は $`c_{1,\ell_c}=c_{1,0}=m+1`$ を要求するが、
    $`[(0,0)]_{1,0}=0`$ であり $`0=m+1`$ は偽である。よってこの場合は起こらない。∎

---

## 4. 所属証明のためのブロック代数

以降で必要になるのは、ペア列を「最上位の木の並び」として分解し、$`M[n]`$・$`\mathrm{gr}`$・$`\mathrm{dom}`$ が
その分解と可換であることを示す道具である。

<a id="d-argOK"></a>
#### 定義 引数ブロック (D.argOK)

```math
\mathrm{argOK}(R)\ :\Longleftrightarrow\ \forall p\in R,\ 0<\pi_0 p .
```

すなわち $`R`$ のすべての対の行 0 の値が $`0`$ より真に大きい。

<a id="d-rsum"></a>
#### 定義 最上位末尾ブロック (D.rsum)

```math
\mathrm{rsum}(A,P)\ :\Longleftrightarrow\ \forall p\in A\mathbin{+\!\!+}P,\ P_{0,0}\le \pi_0 p .
```

すなわち $`P`$ の先頭対の行 0 の値が $`A\mathbin{+\!\!+}P`$ 全体の行 0 の最小値以下である。

### 4a. 行 0 平行移動との可換性

以下 $`\mathrm{sh}_d M := \mathrm{map}\,(\lambda p.\,(\pi_0 p+d,\ \pi_1 p))\,M`$ と書く。
$`\mathrm{map}`$ は長さを変えないから $`\lvert\mathrm{sh}_d M\rvert=\lvert M\rvert`$ である。
また $`j<\lvert S\rvert`$ のとき [(T.entry_shift)](Nrmstep.md#t-entry_shift) より
```math
(\mathrm{sh}_d S)_{0,j}=S_{0,j}+d,\qquad (\mathrm{sh}_d S)_{1,j}=S_{1,j}.
```

<a id="t-nextR_shift_iff"></a>
#### 定理 $`\mathrm{nextR}`$ の平行移動不変性 (T.nextR_shift_iff)

**主張** $`b<\lvert S\rvert`$ ならば
```math
a\to^{\mathrm{sh}_d S}_i b \iff a\to^{S}_i b .
```

**証明** [(D.nextR)](Def.md#d-nextR) は $`i=0`$ か否かの場合分けである。
$`i=0`$ のときは両辺が $`\mathrm{nextrel0}`$ であり
[(T.nextrel0_shift_iff)](Nrmstep.md#t-nextrel0_shift_iff)、
$`i\ne 0`$ のときは両辺が $`\mathrm{nextrel1}`$ であり
[(T.nextrel1_shift_iff)](Nrmstep.md#t-nextrel1_shift_iff) が主張そのものである。∎

<a id="t-hasParent_shift"></a>
#### 定理 $`\mathrm{hasParent}`$ の平行移動不変性 (T.hasParent_shift)

**主張** $`b<\lvert S\rvert`$ ならば
$`\mathrm{hasParent}(\mathrm{sh}_d S,i,b) \iff \mathrm{hasParent}(S,i,b)`$。

**証明** [(D.hasParent)](Def.md#d-hasParent) より両辺は $`\exists!\,j_0,\ j_0\to^{\cdot}_i b`$ の形である。

$`(\Rightarrow)`$ $`j_0`$ を証人とし、$`j_0\to^{\mathrm{sh}_d S}_i b`$ と一意性
$`\forall y,\ (y\to^{\mathrm{sh}_d S}_i b)\to y=j_0`$ を仮定する。
[(T.nextR_shift_iff)](#t-nextR_shift_iff) より $`j_0\to^{S}_i b`$。また $`y\to^{S}_i b`$ なる $`y`$ に対しては
同じ同値の逆向きで $`y\to^{\mathrm{sh}_d S}_i b`$ となり、一意性から $`y=j_0`$。よって $`j_0`$ は $`S`$ 側でも一意の親である。

$`(\Leftarrow)`$ 同じ議論で [(T.nextR_shift_iff)](#t-nextR_shift_iff) の適用方向を入れ替えればよい。
すなわち $`j_0\to^{S}_i b`$ から $`j_0\to^{\mathrm{sh}_d S}_i b`$ を得、
$`y\to^{\mathrm{sh}_d S}_i b`$ から $`y\to^{S}_i b`$、よって $`y=j_0`$ を得る。∎

<a id="t-parent_shift"></a>
#### 定理 $`\mathrm{par}`$ の平行移動不変性 (T.parent_shift)

**主張** $`b<\lvert S\rvert`$ ならば $`\mathrm{par}^{\mathrm{sh}_d S}_i(b)=\mathrm{par}^{S}_i(b)`$。

**証明** [(D.parent)](Def.md#d-parent) より両辺は
$`\varepsilon j_0.\,(j_0\to^{\mathrm{sh}_d S}_i b)`$ と $`\varepsilon j_0.\,(j_0\to^{S}_i b)`$ である。
[(T.nextR_shift_iff)](#t-nextR_shift_iff) より、各 $`j_0`$ について 2 つの述語の値は同値であり、
命題の外延性によりそれらは等しい命題である。よって関数の外延性により 2 つの述語は同一の関数であり、
$`\varepsilon`$ を同一の関数に適用した値どうしであるから等しい。∎

<a id="t-oper_shift"></a>
#### 定理 $`M[n]`$ の平行移動同変性 (T.oper_shift)

**主張** $`(\mathrm{sh}_d M)[n] = \mathrm{sh}_d\,(M[n])`$。

**証明** $`\ell_M=\lvert M\rvert-1`$ が $`0`$ か否かで場合分けする。

**場合 1：$`\ell_M=0`$.** $`\lvert\mathrm{sh}_d M\rvert=\lvert M\rvert`$ より $`\ell_{\mathrm{sh}_d M}=0`$ でもある。
[(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) を両辺に適用すると
左辺 $`=\mathrm{sh}_d M`$、右辺 $`=\mathrm{sh}_d M`$。

**場合 2：$`\ell_M\ne 0`$.** このとき $`\ell_M<\lvert M\rvert`$ である。
[(T.idx1_shift)](Nrmstep.md#t-idx1_shift) より
$`\mathrm{idx}_1(\mathrm{sh}_d M,\ell_M)=\mathrm{idx}_1(M,\ell_M)=:i_1`$。
$`\mathrm{hasParent}(M,i_1,\ell_M)`$ が成り立つか否かで再び場合分けする。

**場合 2a：$`\mathrm{hasParent}(M,i_1,\ell_M)`$ が成り立つ.**

- $`0<M_{0,\ell_M}`$：もし $`M_{0,\ell_M}=0`$ ならば
  [(T.no_hasParent_of_row0_zero)](Nrm.md#t-no_hasParent_of_row0_zero) により
  $`\mathrm{hasParent}(M,i_1,\ell_M)`$ から矛盾が導かれる。
- よって $`\neg(M_{0,\ell_M}=0\wedge M_{1,\ell_M}=0)`$。
- 平行移動側でも $`\mathrm{hasParent}(\mathrm{sh}_d M,i_1,\ell_M)`$ が成り立つ（[(T.hasParent_shift)](#t-hasParent_shift)）。
- $`(\mathrm{sh}_d M)_{0,\ell_M}=M_{0,\ell_M}+d>0`$ であるから、平行移動側でも
  $`\neg\bigl((\mathrm{sh}_d M)_{0,\ell_M}=0\wedge(\mathrm{sh}_d M)_{1,\ell_M}=0\bigr)`$。

以上より両辺に [(T.oper_bad_unfold)](Mechanized.md#t-oper_bad_unfold) が適用できる。
[(T.parent_shift)](#t-parent_shift) より 2 つの親添字は一致するから、これを $`j_0`$ とおく。
また [(T.parent_nextR)](Mechanized.md#t-parent_nextR) と
[(T.nextR_index_lt)](Mechanized.md#t-nextR_index_lt) より $`j_0<\ell_M`$、とくに $`j_0<\lvert M\rvert`$。
コピー差分は
```math
(\mathrm{sh}_d M)_{0,\ell_M}-(\mathrm{sh}_d M)_{0,j_0}
=(M_{0,\ell_M}+d)-(M_{0,j_0}+d)=M_{0,\ell_M}-M_{0,j_0}
```
であり（被減数と減数の双方に同じ $`d`$ を加えても差は変わらない）、$`i_1`$ も一致するから、
[(T.oper_bad_unfold)](Mechanized.md#t-oper_bad_unfold) の展開に現れる係数
```math
\delta=\begin{cases}M_{0,\ell_M}-M_{0,j_0} & (0<i_1)\\ 0 & (\text{それ以外})\end{cases}
```
は両辺で同一である。よって示すべきは
```math
\mathrm{take}\,j_0\,(\mathrm{sh}_d M)\mathbin{+\!\!+}
\mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}\,(\lambda j.\,((\mathrm{sh}_d M)_{0,j}+k\delta,\ (\mathrm{sh}_d M)_{1,j}))\,\mathrm{range}'(j_0,\ell_M-j_0)\bigr)\,\mathrm{range}(n)
```
が
```math
\mathrm{sh}_d\Bigl(\mathrm{take}\,j_0\,M\mathbin{+\!\!+}
\mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}\,(\lambda j.\,(M_{0,j}+k\delta,\ M_{1,j}))\,\mathrm{range}'(j_0,\ell_M-j_0)\bigr)\,\mathrm{range}(n)\Bigr)
```
に等しいことである。右辺は `List.map_append`, `List.map_take`, `List.map_flatMap` により
```math
\mathrm{take}\,j_0\,(\mathrm{sh}_d M)\mathbin{+\!\!+}
\mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}\,(\lambda j.\,(M_{0,j}+k\delta+d,\ M_{1,j}))\,\mathrm{range}'(j_0,\ell_M-j_0)\bigr)\,\mathrm{range}(n)
```
に等しい。各 $`k`$、各 $`j\in\mathrm{range}'(j_0,\ell_M-j_0)`$ について $`j<\lvert M\rvert`$ であるから
[(T.entry_shift)](Nrmstep.md#t-entry_shift) が使え、左辺の被写像は
$`((M_{0,j}+d)+k\delta,\ M_{1,j})`$、右辺の被写像は $`((M_{0,j}+k\delta)+d,\ M_{1,j})`$ であり、
自然数の加法の交換・結合律により $`(M_{0,j}+d)+k\delta=(M_{0,j}+k\delta)+d`$。
`List.flatMap_congr` と `List.map_congr_left` によって全体が一致する。

**場合 2b：$`\mathrm{hasParent}(M,i_1,\ell_M)`$ が成り立たない.**
[(T.hasParent_shift)](#t-hasParent_shift) より平行移動側でも成り立たない。
$`M`$ 側では、$`M_{0,\ell_M}=0\wedge M_{1,\ell_M}=0`$ ならば
[(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero)、
そうでなければ [(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent) により
$`M[n]=\mathrm{Pred}\,M`$。平行移動側でも同じ 2 分岐により $`(\mathrm{sh}_d M)[n]=\mathrm{Pred}(\mathrm{sh}_d M)`$。
$`\ell_M\ne 0`$ より $`\lvert M\rvert\ge 2`$ かつ $`\lvert\mathrm{sh}_d M\rvert\ge 2`$ であるから、
[(D.Pred)](Def.md#d-Pred) はどちらも $`\mathrm{dropLast}`$ の分岐であり、
`List.map_dropLast` より $`\mathrm{dropLast}(\mathrm{sh}_d M)=\mathrm{sh}_d(\mathrm{dropLast}\,M)`$。∎

<a id="t-domT_shift"></a>
#### 定理 $`\mathrm{dom}=T_m`$ の平行移動不変性 (T.domT_shift)

**主張** $`\mathrm{dom}(\mathrm{sh}_d M)=T_m \iff \mathrm{dom}(M)=T_m`$。

**証明** $`M`$ の構成子で場合分けする。

- $`M=[]`$：$`\mathrm{sh}_d[]=[]`$ であるから両辺は同一の命題である。
- $`M=p\mathbin{::}\mathrm{rest}`$：$`\lvert\mathrm{sh}_d M\rvert=\lvert M\rvert`$ より $`\ell_{\mathrm{sh}_d M}=\ell_M`$ であり、
  $`M\ne[]`$ より $`\ell_M<\lvert M\rvert`$。よって [(T.entry_shift)](Nrmstep.md#t-entry_shift) の行 1 の等式から
  $`(\mathrm{sh}_d M)_{1,\ell_M}=M_{1,\ell_M}`$、また [(T.hasParent_shift)](#t-hasParent_shift) より
  $`\mathrm{hasParent}(\mathrm{sh}_d M,1,\ell_M)\iff\mathrm{hasParent}(M,1,\ell_M)`$。
  [(D.domT)](#d-domT) の 2 条件がそれぞれ同値であるから、全体も同値である。∎

<a id="t-natDom_shift"></a>
#### 定理 $`\mathrm{natDom}`$ の平行移動不変性 (T.natDom_shift)

**主張** $`\mathrm{natDom}(\mathrm{sh}_d M) \iff \mathrm{natDom}(M)`$。

**証明** [(D.natDom)](#d-natDom) より両辺は $`\forall m,\ \neg(\mathrm{dom}(\cdot)=T_m)`$ である。
$`(\Rightarrow)`$：$`\mathrm{dom}(M)=T_m`$ とすると [(T.domT_shift)](#t-domT_shift) より
$`\mathrm{dom}(\mathrm{sh}_d M)=T_m`$ となり仮定に反する。
$`(\Leftarrow)`$：$`\mathrm{dom}(\mathrm{sh}_d M)=T_m`$ とすると同じ同値の逆向きで $`\mathrm{dom}(M)=T_m`$ となり仮定に反する。∎

<a id="t-graft_shift"></a>
#### 定理 graft の平行移動同変性 (T.graft_shift)

**主張** $`M\ne[]`$ ならば $`\mathrm{gr}(\mathrm{sh}_d M,z)=\mathrm{sh}_d\bigl(\mathrm{gr}(M,z)\bigr)`$。

**証明** $`M\ne[]`$ より $`\ell_M<\lvert M\rvert`$。[(D.graft)](#d-graft) を両辺で展開する。
$`\lvert\mathrm{sh}_d M\rvert=\lvert M\rvert`$ と [(T.entry_shift)](Nrmstep.md#t-entry_shift) より
$`(\mathrm{sh}_d M)_{0,\ell_M}=M_{0,\ell_M}+d`$ であるから、
```math
\mathrm{gr}(\mathrm{sh}_d M,z)=\mathrm{dropLast}(\mathrm{sh}_d M)\mathbin{+\!\!+}
\mathrm{map}\,\bigl(\lambda p.\,(\pi_0 p+(M_{0,\ell_M}+d),\ \pi_1 p)\bigr)\,z .
```
他方、`List.map_append`, `List.map_dropLast`, `List.map_map` より
```math
\mathrm{sh}_d\bigl(\mathrm{gr}(M,z)\bigr)=\mathrm{dropLast}(\mathrm{sh}_d M)\mathbin{+\!\!+}
\mathrm{map}\,\bigl(\lambda p.\,((\pi_0 p+M_{0,\ell_M})+d,\ \pi_1 p)\bigr)\,z .
```
加法の結合律 $`\pi_0 p+(M_{0,\ell_M}+d)=(\pi_0 p+M_{0,\ell_M})+d`$ により
2 つの写像は各要素で一致し、`List.map_congr_left` により 2 つの列は等しい。∎

<a id="t-W_shift"></a>
#### 定理 $`M\in W_u \Rightarrow \mathrm{sh}_d M\in W_u`$ (T.W_shift)

**主張** $`M\in W_u`$ ならば $`\mathrm{sh}_d M\in W_u`$。

**証明** [(T.A2')](#t-A2') による $`W_u`$ の最小不動点帰納法。帰納法の述語は
```math
\Phi(N) :\equiv \mathrm{sh}_d N\in W_u
```
であり、示すべきことは $`\forall N,\ N\in A^{W}_u(\{N'\mid\mathrm{sh}_d N'\in W_u\})\to \mathrm{sh}_d N\in W_u`$。
[(T.A1_intro)](#t-A1_intro) により $`\mathrm{sh}_d N\in A^{W}_u(W_u)`$ を [(D.Aop)](#d-Aop) の枝ごとに示す。

- **枝 1**：$`\lvert N\rvert\le 1`$ かつ $`N_{1,0}=0`$ を仮定する。$`\lvert\mathrm{sh}_d N\rvert=\lvert N\rvert\le 1`$。
  行 1 の値については、$`N=[]`$ ならば $`\mathrm{sh}_d[]=[]`$ で $`[]_{1,0}=0`$、
  $`N=p\mathbin{::}\mathrm{rest}`$ ならば $`(\mathrm{sh}_d N)_{1,0}=\pi_1 p=N_{1,0}=0`$。よって枝 1 が成立する。
- **枝 2**：$`\mathrm{natDom}(N)`$ と $`\forall n\ge 1,\ \mathrm{sh}_d(N[n])\in W_u`$ を仮定する。
  [(T.natDom_shift)](#t-natDom_shift) より $`\mathrm{natDom}(\mathrm{sh}_d N)`$。
  また [(T.oper_shift)](#t-oper_shift) より $`(\mathrm{sh}_d N)[n]=\mathrm{sh}_d(N[n])\in W_u`$。
- **枝 3**：$`m<u`$、$`\mathrm{dom}(N)=T_m`$、$`\forall z\in W_m,\ \mathrm{based}(z)\to\mathrm{sh}_d(\mathrm{gr}(N,z))\in W_u`$
  を仮定する。[(T.domT_shift)](#t-domT_shift) より $`\mathrm{dom}(\mathrm{sh}_d N)=T_m`$。
  $`\mathrm{dom}(N)=T_m`$ と [(T.not_domT_nil)](#t-not_domT_nil) より $`N\ne[]`$ であるから
  [(T.graft_shift)](#t-graft_shift) が使え、$`z\in W_m`$ で $`\mathrm{based}(z)`$ なるものについて
  $`\mathrm{gr}(\mathrm{sh}_d N,z)=\mathrm{sh}_d(\mathrm{gr}(N,z))\in W_u`$。∎

### 4b. 最小値による末尾分割

<a id="t-split_lastMin"></a>
#### 定理 最上位の最後の木への分割 (T.split_lastMin)

**主張** $`M\ne[]`$ ならば、次をみたす $`A,P`$ が存在する。
```math
M=A\mathbin{+\!\!+}P,\qquad P\ne[],\qquad \mathrm{rsum}(A,P),\qquad \forall p\in P.\mathrm{tail},\ P_{0,0}<\pi_0 p .
```

**証明** $`M`$ に関するリストの逆向き帰納法（`List.reverseRecOn`）。帰納法の述語は
```math
\Phi(M) :\equiv M\ne[] \to \exists A\,P,\ \bigl(M=A\mathbin{+\!\!+}P \wedge P\ne[] \wedge \mathrm{rsum}(A,P)
\wedge \forall p\in P.\mathrm{tail},\ P_{0,0}<\pi_0 p\bigr).
```

- **基底段 $`\Phi([])`$**：前提 $`[]\ne[]`$ が偽であるから成立する。
- **帰納段 $`\Phi(M')\to\Phi(M'\mathbin{+\!\!+}[q])`$**：帰納法の仮定を $`\Phi(M')`$ とし、$`M:=M'\mathbin{+\!\!+}[q]`$ とする。
  $`M\ne[]`$ は成り立っている。$`M'`$ が空か否かで場合分けする。
  - **$`M'=[]`$ の場合**：$`A:=[]`$、$`P:=[q]`$ とする。
    $`M=[]\mathbin{+\!\!+}[q]`$ は連結の定義により成り立ち、$`[q]\ne[]`$ も成り立つ。
    $`\mathrm{rsum}([],[q])`$：$`[q]_{0,0}=\pi_0 q`$ であり、$`p\in[]\mathbin{+\!\!+}[q]=[q]`$ なら $`p=q`$ で
    $`\pi_0 q\le\pi_0 q`$。末尾条件：$`[q].\mathrm{tail}=[]`$ であるから前提をみたす $`p`$ が存在せず成立する。
  - **$`M'\ne[]`$ の場合**：帰納法の仮定より $`A',P'`$ が取れて
    $`M'=A'\mathbin{+\!\!+}P'`$、$`P'\ne[]`$、$`\mathrm{rsum}(A',P')`$、$`\forall p\in P'.\mathrm{tail},\ P'_{0,0}<\pi_0 p`$。
    $`\pi_0 q\le P'_{0,0}`$ か否かで場合分けする。
    - **$`\pi_0 q\le P'_{0,0}`$ の場合**：$`A:=M'`$、$`P:=[q]`$ とする。$`M=M'\mathbin{+\!\!+}[q]`$、$`[q]\ne[]`$。
      $`\mathrm{rsum}(M',[q])`$：$`[q]_{0,0}=\pi_0 q`$。$`p\in M'\mathbin{+\!\!+}[q]`$ とすると、
      $`p\in M'=A'\mathbin{+\!\!+}P'`$ の場合は $`\mathrm{rsum}(A',P')`$ より $`P'_{0,0}\le\pi_0 p`$、
      場合分けの仮定と合わせて $`\pi_0 q\le P'_{0,0}\le\pi_0 p`$。$`p=q`$ の場合は $`\pi_0 q\le\pi_0 q`$。
      末尾条件は $`[q].\mathrm{tail}=[]`$ より成立する。
    - **$`P'_{0,0}<\pi_0 q`$ の場合**：$`A:=A'`$、$`P:=P'\mathbin{+\!\!+}[q]`$ とする。
      $`M=A'\mathbin{+\!\!+}(P'\mathbin{+\!\!+}[q])`$ は連結の結合律による。$`P'\ne[]`$ より $`P\ne[]`$。
      $`P'=p_0\mathbin{::}P''`$ と書けるから $`P=p_0\mathbin{::}(P''\mathbin{+\!\!+}[q])`$ であり、
      ```math
      P_{0,0}=\pi_0 p_0=P'_{0,0}.
      ```
      $`\mathrm{rsum}(A',P)`$：$`p\in A'\mathbin{+\!\!+}P'\mathbin{+\!\!+}[q]`$ とする。$`p\in A'`$ または $`p\in P'`$ なら
      $`\mathrm{rsum}(A',P')`$ より $`P'_{0,0}\le\pi_0 p`$。$`p=q`$ なら場合分けの仮定 $`P'_{0,0}<\pi_0 q`$ より
      $`P'_{0,0}\le\pi_0 q`$。
      末尾条件：$`P.\mathrm{tail}=P''\mathbin{+\!\!+}[q]`$ であり、$`p\in P''=P'.\mathrm{tail}`$ なら
      帰納法の仮定の末尾条件より $`P'_{0,0}<\pi_0 p`$、$`p=q`$ なら場合分けの仮定そのものである。∎

### 4c. 前置ブロックとの可換性

<a id="t-map_sub_add"></a>
#### 定理 減算と加算の相殺 (T.map_sub_add)

**主張** $`\forall p\in X,\ c\le\pi_0 p`$ ならば $`\mathrm{sh}_c(\mathrm{sh}^{-}_c X)=X`$。
ここで $`\mathrm{sh}^{-}_c X := \mathrm{map}\,(\lambda p.\,(\pi_0 p-c,\pi_1 p))\,X`$（切り捨て減法）。

**証明** `List.map_map` より左辺は $`\mathrm{map}\,(\lambda p.\,((\pi_0 p-c)+c,\ \pi_1 p))\,X`$ である。
$`q\in X`$ に対し仮定より $`c\le\pi_0 q`$ であるから、切り捨て減法でも $`(\pi_0 q-c)+c=\pi_0 q`$ が成り立ち、
$`((\pi_0 q-c)+c,\ \pi_1 q)=(\pi_0 q,\pi_1 q)=q`$。よって `List.map_congr_left` により
左辺は $`\mathrm{map}\,(\lambda q.\,q)\,X`$ に等しく、`List.map_id` より $`X`$ に等しい。∎

<a id="t-rsum_decomp"></a>
#### 定理 最上位分割の平行移動分解 (T.rsum_decomp)

**主張** $`c:=P_{0,0}`$ とおく。$`\mathrm{rsum}(A,P)`$ ならば
```math
\mathrm{sh}_c\bigl(\mathrm{sh}^{-}_c A\mathbin{+\!\!+}\mathrm{sh}^{-}_c P\bigr)=A\mathbin{+\!\!+}P .
```

**証明** `List.map_append` より左辺は $`\mathrm{sh}_c(\mathrm{sh}^{-}_c A)\mathbin{+\!\!+}\mathrm{sh}_c(\mathrm{sh}^{-}_c P)`$。
[(D.rsum)](#d-rsum) より $`p\in A`$ でも $`p\in P`$ でも $`c\le\pi_0 p`$ であるから、
[(T.map_sub_add)](#t-map_sub_add) を $`X:=A`$ と $`X:=P`$ に適用してそれぞれ $`A`$、$`P`$ を得る。∎

<a id="t-entry_sub_zero"></a>
#### 定理 減算後の先頭の行 0 の値は $`0`$ (T.entry_sub_zero)

**主張** $`P\ne[]`$、$`c:=P_{0,0}`$ ならば $`(\mathrm{sh}^{-}_c P)_{0,0}=0`$。

**証明** $`P\ne[]`$ より $`P=p_0\mathbin{::}P'`$ と書け、$`c=P_{0,0}=\pi_0 p_0`$。
$`\mathrm{sh}^{-}_c P`$ の先頭は $`(\pi_0 p_0-c,\ \pi_1 p_0)=(\pi_0 p_0-\pi_0 p_0,\ \pi_1 p_0)=(0,\pi_1 p_0)`$ であり、
その行 0 の値は $`0`$。∎

<a id="t-oper_append_gen"></a>
#### 定理 最上位分割に対する $`M[n]`$ の前置可換性 (T.oper_append_gen)

**主張** $`2\le\lvert P\rvert`$ かつ $`\mathrm{rsum}(A,P)`$ ならば $`(A\mathbin{+\!\!+}P)[n]=A\mathbin{+\!\!+}P[n]`$。

**証明** $`c:=P_{0,0}`$、$`A_0:=\mathrm{sh}^{-}_c A`$、$`P_0:=\mathrm{sh}^{-}_c P`$ とおく。
$`2\le\lvert P\rvert`$ より $`P\ne[]`$、よって [(T.entry_sub_zero)](#t-entry_sub_zero) から $`(P_0)_{0,0}=0`$、
また $`\lvert P_0\rvert=\lvert P\rvert\ge 2`$。
[(T.rsum_decomp)](#t-rsum_decomp) より $`\mathrm{sh}_c(A_0\mathbin{+\!\!+}P_0)=A\mathbin{+\!\!+}P`$、
[(T.map_sub_add)](#t-map_sub_add) より $`\mathrm{sh}_c P_0=P`$ および $`\mathrm{sh}_c A_0=A`$。次の 6 段で計算する。

```math
\begin{aligned}
(A\mathbin{+\!\!+}P)[n]
&\overset{(1)}{=} \bigl(\mathrm{sh}_c(A_0\mathbin{+\!\!+}P_0)\bigr)[n]
 \overset{(2)}{=} \mathrm{sh}_c\bigl((A_0\mathbin{+\!\!+}P_0)[n]\bigr)
 \overset{(3)}{=} \mathrm{sh}_c\bigl(A_0\mathbin{+\!\!+}P_0[n]\bigr)\\
&\overset{(4)}{=} \mathrm{sh}_c A_0 \mathbin{+\!\!+} \mathrm{sh}_c (P_0[n])
 \overset{(5)}{=} A \mathbin{+\!\!+} (\mathrm{sh}_c P_0)[n]
 \overset{(6)}{=} A \mathbin{+\!\!+} P[n].
\end{aligned}
```

段の根拠は次のとおり。(1) [(T.rsum_decomp)](#t-rsum_decomp)。
(2) [(T.oper_shift)](#t-oper_shift)。
(3) [(T.oper_append_right)](Nrm.md#t-oper_append_right)（前提 $`2\le\lvert P_0\rvert`$ と $`(P_0)_{0,0}=0`$ は上で確認済み）。
(4) `List.map_append`。
(5) $`\mathrm{sh}_c A_0=A`$ と、[(T.oper_shift)](#t-oper_shift) を逆向きに使って
$`\mathrm{sh}_c(P_0[n])=(\mathrm{sh}_c P_0)[n]`$。
(6) $`\mathrm{sh}_c P_0=P`$。∎

<a id="t-graft_append"></a>
#### 定理 graft の前置可換性 (T.graft_append)

**主張** $`P\ne[]`$ ならば $`\mathrm{gr}(A\mathbin{+\!\!+}P,z)=A\mathbin{+\!\!+}\mathrm{gr}(P,z)`$。

**証明** $`P\ne[]`$ より $`0<\lvert P\rvert`$ であるから
```math
\ell_{A+\!\!+P}=\lvert A\rvert+\lvert P\rvert-1=\lvert A\rvert+(\lvert P\rvert-1)=\lvert A\rvert+\ell_P .
```
よって [(T.entry_append_right)](Nrm.md#t-entry_append_right) より
$`(A\mathbin{+\!\!+}P)_{0,\ell_{A+\!\!+P}}=P_{0,\ell_P}`$、すなわち graft の平行移動量は両辺で一致する。
また `List.dropLast_append_of_ne_nil` より
$`\mathrm{dropLast}(A\mathbin{+\!\!+}P)=A\mathbin{+\!\!+}\mathrm{dropLast}\,P`$。
したがって [(D.graft)](#d-graft) より
```math
\mathrm{gr}(A\mathbin{+\!\!+}P,z)=\bigl(A\mathbin{+\!\!+}\mathrm{dropLast}\,P\bigr)\mathbin{+\!\!+}
\mathrm{map}\,(\lambda p.\,(\pi_0 p+P_{0,\ell_P},\pi_1 p))\,z
```
であり、連結の結合律によりこれは $`A\mathbin{+\!\!+}\mathrm{gr}(P,z)`$ に等しい。∎

<a id="t-hasParent_append_gen"></a>
#### 定理 $`\mathrm{hasParent}`$ の前置不変性 (T.hasParent_append_gen)

**主張** $`j<\lvert P\rvert`$ かつ $`\mathrm{rsum}(A,P)`$ ならば
```math
\mathrm{hasParent}(A\mathbin{+\!\!+}P,\ i,\ \lvert A\rvert+j) \iff \mathrm{hasParent}(P,i,j).
```

**証明** $`j<\lvert P\rvert`$ より $`P\ne[]`$。$`c:=P_{0,0}`$、$`A_0:=\mathrm{sh}^{-}_c A`$、$`P_0:=\mathrm{sh}^{-}_c P`$ とおくと、
$`\lvert A_0\rvert=\lvert A\rvert`$、$`\lvert P_0\rvert=\lvert P\rvert`$、
$`(P_0)_{0,0}=0`$（[(T.entry_sub_zero)](#t-entry_sub_zero)）、
$`\mathrm{sh}_c(A_0\mathbin{+\!\!+}P_0)=A\mathbin{+\!\!+}P`$、$`\mathrm{sh}_c P_0=P`$ である。3 段の同値を合成する。

**第 1 段**
```math
\mathrm{hasParent}(A\mathbin{+\!\!+}P,i,\lvert A\rvert+j)
\iff\mathrm{hasParent}(A_0\mathbin{+\!\!+}P_0,i,\lvert A_0\rvert+j).
```
$`A\mathbin{+\!\!+}P=\mathrm{sh}_c(A_0\mathbin{+\!\!+}P_0)`$ であり、
$`\lvert A\rvert+j=\lvert A_0\rvert+j<\lvert A_0\mathbin{+\!\!+}P_0\rvert`$ であるから
[(T.hasParent_shift)](#t-hasParent_shift) が適用できる。

**第 2 段** $`\mathrm{hasParent}(A_0\mathbin{+\!\!+}P_0,i,\lvert A_0\rvert+j)\iff\mathrm{hasParent}(P_0,i,j)`$：
$`(P_0)_{0,j}=0`$ か否かで場合分けする。
- $`(P_0)_{0,j}=0`$ のとき：[(T.entry_append_right)](Nrm.md#t-entry_append_right) より
  $`(A_0\mathbin{+\!\!+}P_0)_{0,\lvert A_0\rvert+j}=(P_0)_{0,j}=0`$。
  [(T.no_hasParent_of_row0_zero)](Nrm.md#t-no_hasParent_of_row0_zero) により両辺とも偽であるから同値である。
- $`(P_0)_{0,j}\ne 0`$ のとき：$`0<(A_0\mathbin{+\!\!+}P_0)_{0,\lvert A_0\rvert+j}`$ であり、
  $`(P_0)_{0,0}=0`$ と合わせて [(T.hasParent_append_right)](Nrm.md#t-hasParent_append_right) が適用できる。

**第 3 段** $`\mathrm{hasParent}(P_0,i,j)\iff\mathrm{hasParent}(P,i,j)`$：
$`P=\mathrm{sh}_c P_0`$ かつ $`j<\lvert P_0\rvert`$ であるから
[(T.hasParent_shift)](#t-hasParent_shift) による。∎

<a id="t-domT_append"></a>
#### 定理 $`\mathrm{dom}=T_m`$ の前置不変性 (T.domT_append)

**主張** $`P\ne[]`$ かつ $`\mathrm{rsum}(A,P)`$ ならば
$`\mathrm{dom}(A\mathbin{+\!\!+}P)=T_m \iff \mathrm{dom}(P)=T_m`$。

**証明** $`P\ne[]`$ より $`0<\lvert P\rvert`$、よって $`\ell_{A+\!\!+P}=\lvert A\rvert+\ell_P`$ かつ $`\ell_P<\lvert P\rvert`$。
[(D.domT)](#d-domT) の 2 条件をそれぞれ移す。
第 1 条件は [(T.entry_append_right)](Nrm.md#t-entry_append_right) より
$`(A\mathbin{+\!\!+}P)_{1,\lvert A\rvert+\ell_P}=P_{1,\ell_P}`$、
第 2 条件は [(T.hasParent_append_gen)](#t-hasParent_append_gen)（$`j:=\ell_P<\lvert P\rvert`$）より
$`\mathrm{hasParent}(A\mathbin{+\!\!+}P,1,\lvert A\rvert+\ell_P)\iff\mathrm{hasParent}(P,1,\ell_P)`$。∎

<a id="t-natDom_append"></a>
#### 定理 $`\mathrm{natDom}`$ の前置不変性 (T.natDom_append)

**主張** $`P\ne[]`$ かつ $`\mathrm{rsum}(A,P)`$ ならば
$`\mathrm{natDom}(A\mathbin{+\!\!+}P)\iff\mathrm{natDom}(P)`$。

**証明** [(D.natDom)](#d-natDom) より両辺は $`\forall m,\ \neg(\mathrm{dom}(\cdot)=T_m)`$ である。
$`(\Rightarrow)`$：$`\mathrm{dom}(P)=T_m`$ とすると [(T.domT_append)](#t-domT_append) より
$`\mathrm{dom}(A\mathbin{+\!\!+}P)=T_m`$ となり仮定に反する。
$`(\Leftarrow)`$：$`\mathrm{dom}(A\mathbin{+\!\!+}P)=T_m`$ とすると同じ同値の逆向きで $`\mathrm{dom}(P)=T_m`$ となり仮定に反する。∎

---

## 5. Buchholz 2.4 — 連結 $`A\mathbin{+\!\!+}B`$ の所属

<a id="d-XA"></a>
#### 定義 前置ブロックによる引き戻し (D.XA)

```math
X^{(A)} := \{\,B \mid \mathrm{rsum}(A,B)\to A\mathbin{+\!\!+}B\in X\,\}
```
（[(D.rsum)](#d-rsum)）。

### 行 0 の値の記録：$`M[n]`$ と graft は行 0 の値の下界を保つ

<a id="t-entry_zero_headD"></a>
#### 定理 先頭の行 0 の値 (T.entry_zero_headD)

**主張** $`X_{0,0}=\pi_0\bigl(X.\mathrm{headD}(0,0)\bigr)`$。

**証明** $`X`$ の構成子で場合分けする。$`X=[]`$ のとき、[(D.entry)](Def.md#d-entry) より
$`[]_{0,0}=\pi_0(0,0)=0`$ であり、$`[].\mathrm{headD}(0,0)=(0,0)`$ よりその第 0 成分も $`0`$。
$`X=p\mathbin{::}L`$ のとき、$`X_{0,0}=\pi_0 p`$ であり $`X.\mathrm{headD}(0,0)=p`$。∎

<a id="t-oper_head_eq"></a>
#### 定理 $`M[n]`$ は先頭の行 0 の値を保つ (T.oper_head_eq)

**主張** $`1\le n`$ ならば $`(B[n])_{0,0}=B_{0,0}`$。

**証明** $`1<\lvert B\rvert`$ か否かで場合分けする。

- $`1<\lvert B\rvert`$ の場合：[(T.entry_zero_headD)](#t-entry_zero_headD) を両辺に適用すると、示すべきは
  $`\pi_0\bigl((B[n]).\mathrm{headD}(0,0)\bigr)=\pi_0\bigl(B.\mathrm{headD}(0,0)\bigr)`$ であり、
  [(T.oper_headD)](Nrm.md#t-oper_headD) より $`(B[n]).\mathrm{headD}(0,0)=B.\mathrm{headD}(0,0)`$。
- $`\lvert B\rvert\le 1`$ の場合：$`\ell_B=0`$ であるから
  [(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) より $`B[n]=B`$。∎

<a id="t-entry_pair_mem"></a>
#### 定理 第 $`j`$ 列は $`B`$ の要素 (T.entry_pair_mem)

**主張** $`j<\lvert B\rvert`$ ならば $`(B_{0,j},\,B_{1,j})\in B`$。

**証明** [(D.entry)](Def.md#d-entry) より $`B_{0,j}=\pi_0(B\langle j\rangle)`$、$`B_{1,j}=\pi_1(B\langle j\rangle)`$ であるから
$`(B_{0,j},B_{1,j})=B\langle j\rangle`$。$`j<\lvert B\rvert`$ より $`B\langle j\rangle`$ は既定値ではなく
$`B`$ の第 $`j`$ 要素であり、リストの要素はリストに属する。∎

<a id="t-oper_mem_ge"></a>
#### 定理 $`M[n]`$ は行 0 の値の下界を保つ (T.oper_mem_ge)

**主張** $`\forall p\in B,\ c\le\pi_0 p`$ ならば $`\forall p\in B[n],\ c\le\pi_0 p`$。

**証明** $`\ell_B=0`$ か否かで場合分けする。

- $`\ell_B=0`$ の場合：[(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) より $`B[n]=B`$ であり、仮定そのもの。
- $`\ell_B\ne 0`$ の場合：$`\mathrm{hasParent}(B,\mathrm{idx}_1(B,\ell_B),\ell_B)`$ が成り立つか否かで場合分けする。
  - 成り立つ場合：まず $`0<B_{0,\ell_B}`$ である（$`B_{0,\ell_B}=0`$ ならば
    [(T.no_hasParent_of_row0_zero)](Nrm.md#t-no_hasParent_of_row0_zero) により矛盾）。
    よって $`\neg(B_{0,\ell_B}=0\wedge B_{1,\ell_B}=0)`$ であり、
    [(T.oper_bad_unfold)](Mechanized.md#t-oper_bad_unfold) が適用でき
    ```math
    B[n]=\mathrm{take}\,j_0\,B\mathbin{+\!\!+}
    \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}\,(\lambda j.\,(B_{0,j}+k\delta,\ B_{1,j}))\,\mathrm{range}'(j_0,\ell_B-j_0)\bigr)\,\mathrm{range}(n)
    ```
    （$`j_0`$ は親、$`\delta`$ は係数）。$`p\in B[n]`$ を取り、連結のどちらに属するかで場合分けする。
    - $`p\in\mathrm{take}\,j_0\,B`$：前部の要素は $`B`$ の要素であるから仮定より $`c\le\pi_0 p`$。
    - $`p`$ が `flatMap` 側：ある $`k`$ と $`j\in\mathrm{range}'(j_0,\ell_B-j_0)`$ について
      $`p=(B_{0,j}+k\delta,\ B_{1,j})`$ である。$`j<\ell_B<\lvert B\rvert`$ であるから
      [(T.entry_pair_mem)](#t-entry_pair_mem) より $`(B_{0,j},B_{1,j})\in B`$、仮定より $`c\le B_{0,j}`$。
      よって $`c\le B_{0,j}\le B_{0,j}+k\delta=\pi_0 p`$。
  - 成り立たない場合：$`B_{0,\ell_B}=0\wedge B_{1,\ell_B}=0`$ なら
    [(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero)、
    そうでなければ [(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent) により
    $`B[n]=\mathrm{Pred}\,B`$。[(D.Pred)](Def.md#d-Pred) より $`\mathrm{Pred}\,B`$ は $`B`$ か
    $`\mathrm{dropLast}\,B`$ であり、どちらの要素も $`B`$ の要素であるから仮定が使える
    （`List.dropLast_subset`）。∎

<a id="t-graft_mem_ge"></a>
#### 定理 graft は行 0 の値の下界を保つ (T.graft_mem_ge)

**主張** $`B\ne[]`$ かつ $`\forall p\in B,\ c\le\pi_0 p`$ ならば $`\forall p\in\mathrm{gr}(B,z),\ c\le\pi_0 p`$。

**証明** $`B\ne[]`$ より $`\ell_B<\lvert B\rvert`$ であるから、[(T.entry_pair_mem)](#t-entry_pair_mem) より
$`(B_{0,\ell_B},B_{1,\ell_B})\in B`$、よって仮定より $`c\le B_{0,\ell_B}`$。
$`p\in\mathrm{gr}(B,z)`$ を取り、[(D.graft)](#d-graft) の連結のどちらに属するかで場合分けする。

- $`p\in\mathrm{dropLast}\,B`$：`List.dropLast_subset` より $`p\in B`$、仮定より $`c\le\pi_0 p`$。
- $`p=(\pi_0 q+B_{0,\ell_B},\ \pi_1 q)`$（$`q\in z`$）：$`c\le B_{0,\ell_B}\le \pi_0 q+B_{0,\ell_B}=\pi_0 p`$。∎

<a id="t-graft_head_eq"></a>
#### 定理 graft は先頭の行 0 の値を保つ (T.graft_head_eq)

**主張** $`B\ne[]`$、$`\mathrm{based}(z)`$、$`\mathrm{gr}(B,z)\ne[]`$ ならば
$`\bigl(\mathrm{gr}(B,z)\bigr)_{0,0}=B_{0,0}`$。

**証明** $`B`$ の形で場合分けする。$`B\ne[]`$ より $`B=b_0\mathbin{::}B'`$ と書ける。

- $`B'=[]`$ すなわち $`B=[b_0]`$ の場合：$`\mathrm{dropLast}[b_0]=[]`$、$`\ell_B=0`$、$`B_{0,0}=\pi_0 b_0`$ であるから
  ```math
  \mathrm{gr}([b_0],z)=\mathrm{map}\,(\lambda p.\,(\pi_0 p+\pi_0 b_0,\ \pi_1 p))\,z .
  ```
  仮定 $`\mathrm{gr}(B,z)\ne[]`$ よりこの列は空でなく、$`z=z_0\mathbin{::}z'`$ と書ける。
  $`\mathrm{based}(z)`$ は $`z_{0,0}=\pi_0 z_0=0`$ であるから、$`\mathrm{gr}(B,z)`$ の先頭は
  $`(\pi_0 z_0+\pi_0 b_0,\ \pi_1 z_0)=(\pi_0 b_0,\ \pi_1 z_0)`$ であり、その行 0 の値は
  $`\pi_0 b_0=B_{0,0}`$。
- $`B'=b_1\mathbin{::}B''`$ の場合：$`\mathrm{dropLast}\,B=b_0\mathbin{::}\mathrm{dropLast}(b_1\mathbin{::}B'')`$ は
  先頭 $`b_0`$ をもつ空でない列である。[(D.graft)](#d-graft) の連結の先頭はこの $`b_0`$ であるから、
  $`\bigl(\mathrm{gr}(B,z)\bigr)_{0,0}=\pi_0 b_0=B_{0,0}`$。∎

<a id="t-XA_closed"></a>
#### 定理 2.4(a) $`X`$ が前不動点なら $`X^{(A)}`$ も前不動点 (T.XA_closed)

**主張** $`\bigl(\forall M,\ M\in A^W_u(X)\to M\in X\bigr)`$ かつ $`A\in X`$ ならば
```math
\forall M,\ M\in A^W_u\bigl(X^{(A)}\bigr)\to M\in X^{(A)} .
```

**証明** $`B`$ を取り、$`B\in A^W_u(X^{(A)})`$ と $`\mathrm{rsum}(A,B)`$ を仮定して $`A\mathbin{+\!\!+}B\in X`$ を示す。

$`B=[]`$ の場合、$`A\mathbin{+\!\!+}[]=A\in X`$ である。以下 $`B\ne[]`$、すなわち $`0<\lvert B\rvert`$ とする。
[(D.rsum)](#d-rsum) より
```math
\forall p\in B,\ B_{0,0}\le\pi_0 p \qquad\text{および}\qquad \forall p\in A,\ B_{0,0}\le\pi_0 p
```
が成り立つ。[(D.Aop)](#d-Aop) の 3 つの枝で場合分けする。

**枝 1**：$`\lvert B\rvert\le 1`$ かつ $`B_{1,0}=0`$。$`0<\lvert B\rvert`$ と合わせて $`\lvert B\rvert=1`$。

- $`A=[]`$ の場合：$`A\mathbin{+\!\!+}B=B`$ であり、$`B`$ 自身が枝 1 をみたすから仮定より $`B\in X`$。
- $`A\ne[]`$ の場合：$`\lvert A\mathbin{+\!\!+}B\rvert=\lvert A\rvert+1\ge 2`$ であり
  $`\ell_{A+\!\!+B}=\lvert A\rvert+0`$。
  - 任意の $`i`$ について $`\neg\,\mathrm{hasParent}(A\mathbin{+\!\!+}B,i,\lvert A\rvert)`$：
    [(T.hasParent_append_gen)](#t-hasParent_append_gen)（$`j:=0<\lvert B\rvert`$）より
    これは $`\mathrm{hasParent}(B,i,0)`$ と同値であるが、その証人 $`j_0`$ は
    [(T.nextR_index_lt)](Mechanized.md#t-nextR_index_lt) より $`j_0<0`$ をみたすことになり、$`\mathbb{N}`$ では偽である。
  - $`(A\mathbin{+\!\!+}B)_{1,\lvert A\rvert}=B_{1,0}=0`$（[(T.entry_append_right)](Nrm.md#t-entry_append_right)）。
  - $`\mathrm{natDom}(B)`$：$`\ell_B=0`$ であり $`B_{1,\ell_B}=B_{1,0}=0`$ であるから
    [(T.natDom_iff)](#t-natDom_iff) の第 1 選言による。よって
    [(T.natDom_append)](#t-natDom_append) より $`\mathrm{natDom}(A\mathbin{+\!\!+}B)`$。

  $`A\mathbin{+\!\!+}B`$ について [(D.Aop)](#d-Aop) の枝 2 を用いる。各 $`n\ge 1`$ について、
  $`\ell_{A+\!\!+B}=\lvert A\rvert\ne 0`$ である。最終対が $`(0,0)`$ の場合は
  [(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero)、そうでない場合は
  上の 1 番目の事実（任意の $`i`$ について親が存在しない）を
  $`i:=\mathrm{idx}_1(A\mathbin{+\!\!+}B,\ell_{A+\!\!+B})`$ に用いて
  [(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent) が適用でき、いずれの場合も
  $`(A\mathbin{+\!\!+}B)[n]=\mathrm{Pred}(A\mathbin{+\!\!+}B)`$。
  $`\lvert A\mathbin{+\!\!+}B\rvert\ge 2`$ より [(D.Pred)](Def.md#d-Pred) は $`\mathrm{dropLast}`$ の分岐であり、
  `List.dropLast_append_of_ne_nil` と $`\lvert B\rvert=1`$（よって $`\mathrm{dropLast}\,B=[]`$）から
  ```math
  \mathrm{Pred}(A\mathbin{+\!\!+}B)=A\mathbin{+\!\!+}\mathrm{dropLast}\,B=A\mathbin{+\!\!+}[]=A\in X .
  ```
  よって枝 2 の条件がみたされ、仮定より $`A\mathbin{+\!\!+}B\in X`$。

**枝 2**：$`\mathrm{natDom}(B)`$ かつ $`\forall n\ge 1,\ B[n]\in X^{(A)}`$。

- $`2\le\lvert B\rvert`$ の場合：$`A\mathbin{+\!\!+}B`$ について枝 2 を用いる。
  $`\mathrm{natDom}(A\mathbin{+\!\!+}B)`$ は [(T.natDom_append)](#t-natDom_append) による。
  各 $`n\ge 1`$ について [(T.oper_append_gen)](#t-oper_append_gen) より
  $`(A\mathbin{+\!\!+}B)[n]=A\mathbin{+\!\!+}B[n]`$ であり、$`B[n]\in X^{(A)}`$ を用いるには
  $`\mathrm{rsum}(A,B[n])`$ が必要である。[(T.oper_head_eq)](#t-oper_head_eq) より
  $`(B[n])_{0,0}=B_{0,0}`$ であるから、$`p\in A\mathbin{+\!\!+}B[n]`$ に対し
  $`p\in A`$ なら $`B_{0,0}\le\pi_0 p`$、$`p\in B[n]`$ なら [(T.oper_mem_ge)](#t-oper_mem_ge)（$`c:=B_{0,0}`$）より
  $`B_{0,0}\le\pi_0 p`$。よって $`A\mathbin{+\!\!+}B[n]\in X`$。
  枝 2 の条件がみたされ、仮定より $`A\mathbin{+\!\!+}B\in X`$。
- $`\lvert B\rvert=1`$ の場合：$`\ell_B=0`$ であるから
  [(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) より $`B[1]=B`$。
  $`n:=1`$ として $`B\in X^{(A)}`$ を得、これに $`\mathrm{rsum}(A,B)`$ を適用して $`A\mathbin{+\!\!+}B\in X`$。

**枝 3**：$`m<u`$、$`\mathrm{dom}(B)=T_m`$、$`\forall z\in W_m,\ \mathrm{based}(z)\to\mathrm{gr}(B,z)\in X^{(A)}`$。
$`A\mathbin{+\!\!+}B`$ について枝 3 を同じ $`m`$ で用いる。
$`\mathrm{dom}(A\mathbin{+\!\!+}B)=T_m`$ は [(T.domT_append)](#t-domT_append) による。
$`z\in W_m`$ で $`\mathrm{based}(z)`$ なるものを取ると、[(T.graft_append)](#t-graft_append) より
$`\mathrm{gr}(A\mathbin{+\!\!+}B,z)=A\mathbin{+\!\!+}\mathrm{gr}(B,z)`$ であるから、
$`\mathrm{gr}(B,z)\in X^{(A)}`$ に $`\mathrm{rsum}(A,\mathrm{gr}(B,z))`$ を適用すればよい。
その $`\mathrm{rsum}`$ は次のように確かめる。
$`\mathrm{gr}(B,z)=[]`$ ならば $`(\mathrm{gr}(B,z))_{0,0}=0`$ でありすべての $`p`$ について $`0\le\pi_0 p`$。
$`\mathrm{gr}(B,z)\ne[]`$ ならば [(T.graft_head_eq)](#t-graft_head_eq) より
$`(\mathrm{gr}(B,z))_{0,0}=B_{0,0}`$ であり、$`p\in A`$ なら $`B_{0,0}\le\pi_0 p`$、
$`p\in\mathrm{gr}(B,z)`$ なら [(T.graft_mem_ge)](#t-graft_mem_ge)（$`c:=B_{0,0}`$）より $`B_{0,0}\le\pi_0 p`$。
よって枝 3 の条件がみたされ、仮定より $`A\mathbin{+\!\!+}B\in X`$。∎

<a id="t-W_add"></a>
#### 定理 2.4(b) $`A,B\in W_u \Rightarrow A\mathbin{+\!\!+}B\in W_u`$ (T.W_add)

**主張** $`A\in W_u`$、$`B\in W_u`$、$`\mathrm{rsum}(A,B)`$ ならば $`A\mathbin{+\!\!+}B\in W_u`$。

**証明** [(T.XA_closed)](#t-XA_closed) を $`X:=W_u`$ に適用する。その前提
「$`\forall M,\ M\in A^W_u(W_u)\to M\in W_u`$」は [(T.A1_intro)](#t-A1_intro) であり、$`A\in W_u`$ は仮定である。
得られる結論は $`\forall M,\ M\in A^W_u\bigl((W_u)^{(A)}\bigr)\to M\in (W_u)^{(A)}`$ であるから、
[(T.A2')](#t-A2') による $`W_u`$ の最小不動点帰納法（帰納法の述語は
$`\Phi(M):\equiv M\in (W_u)^{(A)}`$、すなわち
$`\mathrm{rsum}(A,M)\to A\mathbin{+\!\!+}M\in W_u`$）が使えて $`W_u\subseteq (W_u)^{(A)}`$。
これを $`B\in W_u`$ に適用し、さらに $`\mathrm{rsum}(A,B)`$ を適用して $`A\mathbin{+\!\!+}B\in W_u`$ を得る。∎

---

## 6. Buchholz 2.5/2.6 — 主要項のステップと塔

<a id="t-graft_Om"></a>
#### 定理 $`[(0,v)]`$ の graft は恒等 (T.graft_Om)

**主張** $`\mathrm{gr}([(0,v)],z)=z`$。

**証明** [(D.graft)](#d-graft) より $`\mathrm{dropLast}[(0,v)]=[]`$、$`\ell_{[(0,v)]}=1-1=0`$、
$`[(0,v)]_{0,0}=0`$ であるから
```math
\mathrm{gr}([(0,v)],z)=[]\mathbin{+\!\!+}\mathrm{map}\,(\lambda p.\,(\pi_0 p+0,\ \pi_1 p))\,z=z .
```
∎

<a id="t-domT_Om"></a>
#### 定理 $`[(0,m+1)]`$ は $`\mathrm{dom}=T_m`$ をみたす (T.domT_Om)

**主張** $`\mathrm{dom}([(0,m+1)])=T_m`$。

**証明** [(D.domT)](#d-domT) の第 1 条件は $`[(0,m+1)]_{1,0}=m+1`$ であり成立する。
第 2 条件：$`j_0\to^{[(0,m+1)]}_1 0`$ なる $`j_0`$ が存在したとすると、
[(D.nextR)](Def.md#d-nextR)（$`1\ne 0`$ より $`\mathrm{nextrel1}`$ の側）の条件 3 より $`j_0<0`$ となり、
$`\mathbb{N}`$ では偽である。よって $`\neg\,\mathrm{hasParent}([(0,m+1)],1,0)`$。∎

<a id="t-Om_mem_W"></a>
#### 定理 2.5 $`[(0,v)]\in W_v`$ (T.Om_mem_W)

**主張** $`[(0,v)]\in W_v`$。

**証明** $`v`$ の形で場合分けする。

- $`v=0`$：[(T.A1_intro)](#t-A1_intro) の枝 1 を用いる。$`\lvert[(0,0)]\rvert=1\le 1`$ であり
  $`[(0,0)]_{1,0}=0`$。
- $`v=w+1`$：[(T.A1_intro)](#t-A1_intro) の枝 3 を $`m:=w`$ で用いる。
  $`w<w+1`$ であり、$`\mathrm{dom}([(0,w+1)])=T_w`$ は [(T.domT_Om)](#t-domT_Om) である。
  $`z\in W_w`$ で $`\mathrm{based}(z)`$ なるものについて、[(T.graft_Om)](#t-graft_Om) より
  $`\mathrm{gr}([(0,w+1)],z)=z`$ であり、[(T.W_mono)](#t-W_mono)（$`w\le w+1`$）より $`z\in W_{w+1}`$。∎

<a id="d-Wstar"></a>
#### 定義 $`W^{*}`$ (D.Wstar)

```math
W^{*} := \{\,R \mid \mathrm{argOK}(R)\to\forall v\in\mathbb{N},\ (0,v)\mathbin{::}R\in W_v\,\}
```
（[(D.argOK)](#d-argOK)）。すなわち「引数ブロック $`R`$ に主要項の根 $`(0,v)`$ を付けたものが、
どの $`v`$ についてもその水準の $`W_v`$ に属する」。

<a id="d-tow"></a>
#### 定義 塔 (D.tow)

$`v\in\mathbb{N}`$、$`R\in\mathrm{PairSeq}`$ に対し、$`k`$ に関する再帰で
```math
t^{v,R}_0 := [],\qquad t^{v,R}_{k+1} := (0,v)\mathbin{::}\mathrm{gr}\bigl(R,\ t^{v,R}_k\bigr)
```
と定める（[(D.graft)](#d-graft)）。

<a id="t-graft_cons"></a>
#### 定理 主要項の graft (T.graft_cons)

**主張** $`R\ne[]`$ ならば $`\mathrm{gr}((0,v)\mathbin{::}R,\ z)=(0,v)\mathbin{::}\mathrm{gr}(R,z)`$。

**証明** [(T.graft_append)](#t-graft_append) を $`A:=[(0,v)]`$、$`P:=R`$ に適用すると
$`\mathrm{gr}([(0,v)]\mathbin{+\!\!+}R,\ z)=[(0,v)]\mathbin{+\!\!+}\mathrm{gr}(R,z)`$。
$`[(0,v)]\mathbin{+\!\!+}L=(0,v)\mathbin{::}L`$ であるから主張を得る。∎

<a id="t-entry_cons"></a>
#### 定理 成分の添字ずらし (T.entry_cons)

**主張** $`(p\mathbin{::}R)_{i,\,j+1}=R_{i,j}`$。

**証明** [(T.entry_append_right)](Nrm.md#t-entry_append_right) を $`A:=[p]`$、$`T:=R`$ に適用すると
$`([p]\mathbin{+\!\!+}R)_{i,\,1+j}=R_{i,j}`$。$`[p]\mathbin{+\!\!+}R=p\mathbin{::}R`$ であり
$`1+j=j+1`$ であるから主張を得る。∎

### $`\mathrm{oper}`$ を主要ブロックに適用したときの 4 つの場合

$`M=(0,v)\mathbin{::}R`$ で $`\mathrm{argOK}(R)`$ とする。$`x:=R_{0,\ell_R}`$、$`w:=R_{1,\ell_R}`$ と書くと、
$`M`$ の最終列の行 0 祖先鎖は $`R`$ 自身の鎖に根 $`(0,v)`$ を付け加えたものである
（$`\mathrm{argOK}(R)`$ よりこの根の行 0 の値 $`0`$ は $`R`$ のどの列の行 0 の値よりも真に小さい）。
したがって次の 4 つの場合に分かれる。以下、$`(0,v)\mathbin{::}R`$ の形の列を**主要ブロック**と呼ぶ。

| 場合 | 条件 | $`\mathrm{dom}`$ | $`M[n]`$ |
|---|---|---|---|
| (A′) | $`w=0`$ かつ $`R`$ 内に行 0 の親がない | 後続 | $`(0,v)\mathbin{::}\mathrm{dropLast}\,R`$ の $`n`$ 個の複製 |
| (B′)(C′) | $`R`$ の最終列が $`R`$ 内に親をもつ | $`\mathbb{N}`$ | $`(0,v)\mathbin{::}R[n]`$ |
| (D′) | $`\mathrm{dom}(R)=T_m`$ かつ $`v\le m`$ | $`\mathbb{N}`$ | 塔 $`t^{v,R}_n`$ |
| (E′) | $`\mathrm{dom}(R)=T_m`$ かつ $`m<v`$ | $`T_m`$ | 根を通した graft |

この表は Buchholz (1987) 2.6 の場合分けとの対応を示すものであり、正確な内容は以下の各補題の主張である。
以下の補題はすべて $`M[n]`$ と $`\mathrm{hasParent}`$ についての主張であり、
$`W`$、$`\prec`$、$`\mathrm{tr}`$ を含まない。

### 親の機構の cons への移送

<a id="t-nextR_cons"></a>
#### 定理 $`\mathrm{nextR}`$ の添字ずらし (T.nextR_cons)

**主張** $`(j_0+1)\to^{p\mathbin{::}R}_i(j_1+1) \iff j_0\to^{R}_i j_1`$。

**証明** [(T.nextR_append_right)](Nrm.md#t-nextR_append_right) を $`A:=[p]`$、$`T:=R`$ に適用すると
$`(1+j_0)\to^{[p]+\!\!+R}_i(1+j_1)\iff j_0\to^R_i j_1`$。
$`[p]\mathbin{+\!\!+}R=p\mathbin{::}R`$、$`1+j=j+1`$ による。∎

<a id="t-le0_cons"></a>
#### 定理 $`\mathrm{le0}`$ の添字ずらし (T.le0_cons)

**主張** $`(j_0+1)\le^{p\mathbin{::}R}_0(j_1+1) \iff j_0\le^{R}_0 j_1`$。

**証明** [(T.le0_append_right)](Nrm.md#t-le0_append_right) を $`A:=[p]`$、$`T:=R`$ に適用し、
$`[p]\mathbin{+\!\!+}R=p\mathbin{::}R`$ と $`1+j=j+1`$ で書き換える。∎

<a id="t-idx1_cons"></a>
#### 定理 $`\mathrm{idx}_1`$ の添字ずらし (T.idx1_cons)

**主張** $`\mathrm{idx}_1(p\mathbin{::}R,\ j+1)=\mathrm{idx}_1(R,j)`$。

**証明** [(T.idx1_append_right)](Nrm.md#t-idx1_append_right) を $`A:=[p]`$、$`T:=R`$ に適用し、
$`[p]\mathbin{+\!\!+}R=p\mathbin{::}R`$ と $`1+j=j+1`$ で書き換える。∎

<a id="t-hasParent_zero_iff"></a>
#### 定理 行 0 親の存在判定 (T.hasParent_zero_iff)

**主張** $`b<\lvert M\rvert`$ ならば
```math
\mathrm{hasParent}(M,0,b) \iff \exists k,\ \bigl(k<b \ \wedge\ M_{0,k}<M_{0,b}\bigr).
```

**証明** [(D.nextR)](Def.md#d-nextR) の場合分けで $`i=0`$ の側が選ばれるから、
$`k\to^M_0 b`$（$`\mathrm{nextR}`$ の意味）と $`k\to^M_0 b`$（$`\mathrm{nextrel0}`$ の意味）は同値であり、以下同一視する。

$`(\Rightarrow)`$ 親 $`k`$ を取ると、[(D.nextrel0)](Def.md#d-nextrel0) の条件 3, 4 より
$`k<b`$ と $`M_{0,k}<M_{0,b}`$。

$`(\Leftarrow)`$ 条件をみたす $`k`$ を取る。述語
```math
P(t):\equiv\ t<b \ \wedge\ M_{0,t}<M_{0,b}
```
に対し $`g:=\mathrm{fg}(P,b)`$ とおく。$`k<b`$ より $`k\le b`$、$`P(k)`$ が成り立つから
`Nat.findGreatest_spec` より $`P(g)`$、すなわち $`g<b`$ かつ $`M_{0,g}<M_{0,b}`$。
また $`P(t)`$ をみたす $`t`$ は $`t<b`$ すなわち $`t\le b`$ をみたすから、`Nat.le_findGreatest` より
```math
(\dagger)\qquad\forall t,\ P(t)\to t\le g .
```

$`g\to^M_0 b`$、すなわち [(D.nextrel0)](Def.md#d-nextrel0) の 5 条件を確かめる。

1. $`g<\lvert M\rvert`$：$`g<b`$ と $`b<\lvert M\rvert`$ の推移性。
2. $`b<\lvert M\rvert`$：仮定。
3. $`g<b`$：$`P(g)`$ の第 1 成分。
4. $`M_{0,g}<M_{0,b}`$：$`P(g)`$ の第 2 成分。
5. $`\forall l,\ (g<l\wedge l<b)\to M_{0,b}\le M_{0,l}`$：結論を否定して $`M_{0,l}<M_{0,b}`$ とすると、
   $`l<b`$ と合わせて $`P(l)`$ が成り立ち、$`(\dagger)`$ より $`l\le g`$ となって $`g<l`$ に矛盾する。

一意性：$`y\to^M_0 b`$ とすると条件 3, 4 より $`P(y)`$、$`(\dagger)`$ より $`y\le g`$。
$`y<g`$ と仮定すると、$`y`$ についての条件 5 を $`l:=g`$ に適用でき（$`y<g`$、$`g<b`$）、
$`M_{0,b}\le M_{0,g}`$ を得るが、これは $`P(g)`$ の第 2 成分 $`M_{0,g}<M_{0,b}`$ に矛盾する。よって $`y=g`$。∎

<a id="t-le0_cons_zero"></a>
#### 定理 主要ブロックの根はすべての列の行 0 祖先 (T.le0_cons_zero)

**主張** $`\mathrm{argOK}(R)`$ ならば、$`j<\lvert R\rvert`$ なる任意の $`j`$ について
$`0\le^{(0,v)::R}_0 (j+1)`$。

**証明** $`M:=(0,v)\mathbin{::}R`$ とおく。まず補助命題
```math
\mathrm{key}(N):\equiv\ \forall j,\ j\le N \to j<\lvert R\rvert \to 0\le^{M}_0 (j+1)
```
を $`N`$ に関する自然数の帰納法で示す。帰納法の述語は $`\mathrm{key}(N)`$ である。

- **基底段 $`N=0`$**：$`j\le 0`$ より $`j=0`$。$`j<\lvert R\rvert`$ より $`0<\lvert R\rvert`$、
  よって $`\lvert M\rvert=\lvert R\rvert+1\ge 2`$ であり $`0<\lvert M\rvert`$、$`1<\lvert M\rvert`$。
  [(D.le0)](Def.md#d-le0) の 3 条件のうち長さの 2 条件はこれで満たされる。
  残りは $`\mathrm{ReflTransGen}(\to^M_0)\ 0\ 1`$ であり、1 段の $`0\to^M_0 1`$ を示せばよい。
  [(D.nextrel0)](Def.md#d-nextrel0) の 5 条件は次のとおり。
  1. $`0<\lvert M\rvert`$、2. $`1<\lvert M\rvert`$、3. $`0<1`$。
  4. $`M_{0,0}<M_{0,1}`$：$`M_{0,0}=0`$ であり、[(T.entry_cons)](#t-entry_cons) より $`M_{0,1}=R_{0,0}`$。
     $`0<\lvert R\rvert`$ より [(T.entry_pair_mem)](#t-entry_pair_mem) から $`(R_{0,0},R_{1,0})\in R`$、
     $`\mathrm{argOK}(R)`$ より $`0<R_{0,0}`$。
  5. $`\forall l,\ (0<l\wedge l<1)\to\cdots`$：前提をみたす $`l`$ は存在しない。
- **帰納段 $`N\to N+1`$**：帰納法の仮定は $`\mathrm{key}(N)`$ である。$`j\le N+1`$、$`j<\lvert R\rvert`$ とする。
  $`j+1<\lvert M\rvert`$ である。[(T.entry_cons)](#t-entry_cons) と
  [(T.entry_pair_mem)](#t-entry_pair_mem)、$`\mathrm{argOK}(R)`$ より
  ```math
  M_{0,j+1}=R_{0,j}>0=M_{0,0},
  ```
  よって $`k:=0`$ が $`k<j+1`$ かつ $`M_{0,k}<M_{0,j+1}`$ をみたす。
  [(T.hasParent_zero_iff)](#t-hasParent_zero_iff) より $`\mathrm{hasParent}(M,0,j+1)`$ であり、
  その親を $`k`$ とすると $`k\to^M_0 (j+1)`$。
  - $`k=0`$ の場合：1 段の $`\mathrm{ReflTransGen}`$ で $`0\le^M_0 (j+1)`$。
  - $`k=k'+1`$（$`k>0`$）の場合：$`\mathrm{nextrel0}`$ の条件 3 より $`k'+1<j+1`$、すなわち $`k'<j`$。
    $`j\le N+1`$ より $`k'\le N`$ であり、$`k'<j<\lvert R\rvert`$ より $`k'<\lvert R\rvert`$。
    帰納法の仮定 $`\mathrm{key}(N)`$ を $`k'`$ に適用して $`0\le^M_0 (k'+1)`$、
    とくにその第 3 成分の鎖に 1 段 $` (k'+1)\to^M_0 (j+1)`$ を継ぎ足して
    $`\mathrm{ReflTransGen}(\to^M_0)\ 0\ (j+1)`$ を得る。長さの 2 条件も上で確認済みである。

最後に $`\mathrm{key}(j)`$ を $`N:=j`$、$`j:=j`$（$`j\le j`$）に適用して主張を得る。∎

<a id="t-len_succ"></a>
#### 定理 空でない列の長さ (T.len_succ)

**主張** $`R\ne[]`$ ならば $`\lvert R\rvert=(\lvert R\rvert-1)+1`$。

**証明** $`R\ne[]`$ より $`0<\lvert R\rvert`$。$`\lvert R\rvert\ge 1`$ の自然数については
切り捨て減法でも $`(\lvert R\rvert-1)+1=\lvert R\rvert`$ が成り立つ。∎

<a id="t-entry_cons_last"></a>
#### 定理 最終列の成分（cons） (T.entry_cons_last)

**主張** $`R\ne[]`$ ならば $`(p\mathbin{::}R)_{i,\lvert R\rvert}=R_{i,\lvert R\rvert-1}`$。

**証明** [(T.len_succ)](#t-len_succ) より左辺の添字を $`\lvert R\rvert=(\lvert R\rvert-1)+1`$ と書き換え、
[(T.entry_cons)](#t-entry_cons) を $`j:=\lvert R\rvert-1`$ に適用する。∎

<a id="t-le0_cons_last"></a>
#### 定理 最終列への $`\mathrm{le0}`$（cons） (T.le0_cons_last)

**主張** $`R\ne[]`$ ならば $`(j+1)\le^{p::R}_0\lvert R\rvert \iff j\le^{R}_0(\lvert R\rvert-1)`$。

**証明** [(T.len_succ)](#t-len_succ) で左辺の添字を $`(\lvert R\rvert-1)+1`$ と書き換え、
[(T.le0_cons)](#t-le0_cons) を $`j_1:=\lvert R\rvert-1`$ に適用する。∎

<a id="t-nextR_cons_last"></a>
#### 定理 最終列への $`\mathrm{nextR}`$（cons） (T.nextR_cons_last)

**主張** $`R\ne[]`$ ならば $`(j+1)\to^{p::R}_i\lvert R\rvert \iff j\to^{R}_i(\lvert R\rvert-1)`$。

**証明** [(T.len_succ)](#t-len_succ) で左辺の添字を $`(\lvert R\rvert-1)+1`$ と書き換え、
[(T.nextR_cons)](#t-nextR_cons) を $`j_1:=\lvert R\rvert-1`$ に適用する。∎

<a id="t-idx1_cons_last"></a>
#### 定理 最終列の $`\mathrm{idx}_1`$（cons） (T.idx1_cons_last)

**主張** $`R\ne[]`$ ならば $`\mathrm{idx}_1(p\mathbin{::}R,\lvert R\rvert)=\mathrm{idx}_1(R,\lvert R\rvert-1)`$。

**証明** [(T.len_succ)](#t-len_succ) で左辺の添字を $`(\lvert R\rvert-1)+1`$ と書き換え、
[(T.idx1_cons)](#t-idx1_cons) を $`j:=\lvert R\rvert-1`$ に適用する。∎

<a id="t-cons_len_lt"></a>
#### 定理 cons は長さを増やす (T.cons_len_lt)

**主張** $`\lvert R\rvert<\lvert p\mathbin{::}R\rvert`$。

**証明** $`\lvert p\mathbin{::}R\rvert=\lvert R\rvert+1`$ であり $`\lvert R\rvert<\lvert R\rvert+1`$。∎

<a id="t-hasParent_cons_one"></a>
#### 定理 (C′)(D′) 根が行 1 の親になる場合 (T.hasParent_cons_one)

**主張** $`\mathrm{argOK}(R)`$、$`R\ne[]`$、および
```math
\mathrm{hasParent}(R,1,\lvert R\rvert-1)\ \vee\ v<R_{1,\lvert R\rvert-1}
```
のいずれかが成り立つならば、$`\mathrm{hasParent}((0,v)\mathbin{::}R,\ 1,\ \lvert R\rvert)`$。

**証明** $`M:=(0,v)\mathbin{::}R`$ とおく。$`R\ne[]`$ より $`0<\lvert R\rvert`$、また
[(T.cons_len_lt)](#t-cons_len_lt) より $`\lvert R\rvert<\lvert M\rvert`$。
[(T.hasParent_one_iff)](#t-hasParent_one_iff) により、$`\mathrm{r1cand}(M,\lvert R\rvert,j_0)`$ なる $`j_0`$ の存在を示せばよい。
[(T.entry_cons_last)](#t-entry_cons_last) より $`M_{1,\lvert R\rvert}=R_{1,\lvert R\rvert-1}`$ である。
仮定の 2 つの選言で場合分けする。

- **$`\mathrm{hasParent}(R,1,\lvert R\rvert-1)`$ の場合**：$`\lvert R\rvert-1<\lvert R\rvert`$ であるから
  [(T.hasParent_one_iff)](#t-hasParent_one_iff) より $`j'`$ が取れて
  ```math
  j'<\lvert R\rvert-1,\qquad j'\le^R_0(\lvert R\rvert-1),\qquad R_{1,j'}<R_{1,\lvert R\rvert-1}.
  ```
  $`j_0:=j'+1`$ とする。$`j'<\lvert R\rvert-1`$ より $`j'+1<\lvert R\rvert`$。
  [(T.le0_cons_last)](#t-le0_cons_last) より $`(j'+1)\le^M_0\lvert R\rvert`$。
  [(T.entry_cons)](#t-entry_cons) より $`M_{1,j'+1}=R_{1,j'}`$ であり、
  $`M_{1,\lvert R\rvert}=R_{1,\lvert R\rvert-1}`$ と合わせて $`M_{1,j'+1}<M_{1,\lvert R\rvert}`$。
  よって $`\mathrm{r1cand}(M,\lvert R\rvert,j'+1)`$。
- **$`v<R_{1,\lvert R\rvert-1}`$ の場合**：$`j_0:=0`$ とする。$`0<\lvert R\rvert`$。
  [(T.le0_cons_zero)](#t-le0_cons_zero) を $`j:=\lvert R\rvert-1`$（$`<\lvert R\rvert`$）に適用すると
  $`0\le^M_0((\lvert R\rvert-1)+1)`$ であり、[(T.len_succ)](#t-len_succ) より
  $`(\lvert R\rvert-1)+1=\lvert R\rvert`$ であるから $`0\le^M_0\lvert R\rvert`$。
  また $`M_{1,0}=v<R_{1,\lvert R\rvert-1}=M_{1,\lvert R\rvert}`$。
  よって $`\mathrm{r1cand}(M,\lvert R\rvert,0)`$。∎

<a id="t-oper_root_tiling"></a>
#### 定理 親が根のときの展開形 (T.oper_root_tiling)

**主張** $`\ell_M\ne 0`$、$`\neg(M_{0,\ell_M}=0\wedge M_{1,\ell_M}=0)`$、
$`\mathrm{hasParent}(M,\mathrm{idx}_1(M,\ell_M),\ell_M)`$、かつ
$`\mathrm{par}^M_{\mathrm{idx}_1(M,\ell_M)}(\ell_M)=0`$ ならば
```math
M[n]=\mathrm{flatMap}\Bigl(\lambda k.\ \mathrm{map}\bigl(\lambda p.\,(\pi_0 p+k\delta,\ \pi_1 p)\bigr)(\mathrm{dropLast}\,M)\Bigr)\,\mathrm{range}(n),
```
```math
\delta := \begin{cases} M_{0,\ell_M}-M_{0,0} & (0<\mathrm{idx}_1(M,\ell_M))\\ 0 & (\text{それ以外}).\end{cases}
```

**証明** [(T.oper_bad_unfold)](Mechanized.md#t-oper_bad_unfold) を適用し、親を $`0`$ で置き換えると
$`\mathrm{take}\,0\,M=[]`$、$`\ell_M-0=\ell_M`$ であるから
```math
M[n]=\mathrm{flatMap}\Bigl(\lambda k.\ \mathrm{map}\bigl(\lambda j.\,(M_{0,j}+k\delta,\ M_{1,j})\bigr)\,\mathrm{range}'(0,\ell_M)\Bigr)\,\mathrm{range}(n).
```
他方 `List.dropLast_eq_take` より $`\mathrm{dropLast}\,M=\mathrm{take}\,\ell_M\,M`$ であり、
$`\ell_M\le\lvert M\rvert`$ であるから [(T.map_range_entry_eq_take)](Nrm.md#t-map_range_entry_eq_take) より
```math
\mathrm{dropLast}\,M=\mathrm{map}\,(\lambda j.\,(M_{0,j},M_{1,j}))\,\mathrm{range}(\ell_M).
```
これに $`\lambda p.(\pi_0 p+k\delta,\pi_1 p)`$ を写すと、`List.map_map` により
$`\mathrm{map}\,(\lambda j.\,(M_{0,j}+k\delta,\ M_{1,j}))\,\mathrm{range}(\ell_M)`$ である。
`List.range_eq_range'` より $`\mathrm{range}(\ell_M)=\mathrm{range}'(0,\ell_M)`$ であるから、
各 $`k`$ について 2 つの列は等しく、`List.flatMap_congr` により全体が等しい。∎

<a id="t-oper_cons_nat"></a>
#### 定理 (B′)(C′) 崩壊しない主要ステップ (T.oper_cons_nat)

**主張** $`\mathrm{argOK}(R)`$、$`R\ne[]`$、$`\mathrm{hasParent}(R,\mathrm{idx}_1(R,\ell_R),\ell_R)`$ ならば
```math
\bigl((0,v)\mathbin{::}R\bigr)[n]=(0,v)\mathbin{::}R[n].
```

**証明** $`M:=(0,v)\mathbin{::}R`$、$`i_1:=\mathrm{idx}_1(R,\ell_R)`$、
$`j_0:=\mathrm{par}^R_{i_1}(\ell_R)`$ とおく。$`R\ne[]`$ より $`0<\lvert R\rvert`$、
$`\lvert M\rvert=\lvert R\rvert+1`$、$`\ell_M=\lvert R\rvert`$ である。

**準備.** [(T.parent_nextR)](Mechanized.md#t-parent_nextR) より $`j_0\to^R_{i_1}\ell_R`$、
[(T.nextR_index_lt)](Mechanized.md#t-nextR_index_lt) より $`j_0<\ell_R`$、とくに $`\ell_R\ne 0`$。
$`\mathrm{argOK}(R)`$ と [(T.entry_pair_mem)](#t-entry_pair_mem) より $`0<R_{0,\ell_R}`$、
よって $`\neg(R_{0,\ell_R}=0\wedge R_{1,\ell_R}=0)`$。
[(T.entry_cons_last)](#t-entry_cons_last) より
```math
M_{0,\lvert R\rvert}=R_{0,\ell_R},\qquad M_{1,\lvert R\rvert}=R_{1,\ell_R},
```
したがって $`\ell_M=\lvert R\rvert\ne 0`$ かつ $`\neg(M_{0,\ell_M}=0\wedge M_{1,\ell_M}=0)`$。
[(T.idx1_cons_last)](#t-idx1_cons_last) より $`\mathrm{idx}_1(M,\ell_M)=i_1`$。

**根は $`M`$ の最終列の親ではない.** $`0\to^M_{i_1}\lvert R\rvert`$ を仮定して矛盾を導く。

- $`i_1=0`$ の場合：これは $`0\to^M_0\lvert R\rvert`$、すなわち $`\mathrm{nextrel0}`$ である。
  その条件 5 を $`j:=j_0+1`$ に適用する（$`0<j_0+1`$ であり、$`j_0<\ell_R=\lvert R\rvert-1`$ より $`j_0+1<\lvert R\rvert`$）。
  得られるのは $`M_{0,\lvert R\rvert}\le M_{0,j_0+1}`$、すなわち
  [(T.entry_cons)](#t-entry_cons) により $`R_{0,\ell_R}\le R_{0,j_0}`$。
  一方 $`j_0\to^R_0\ell_R`$（$`i_1=0`$ の場合の $`\mathrm{nextrel0}`$）の条件 4 は $`R_{0,j_0}<R_{0,\ell_R}`$ である。矛盾。
- $`i_1\ne 0`$ の場合：これは $`\mathrm{nextrel1}`$ である。
  $`j_0\to^R_1\ell_R`$ の条件 5 より $`j_0\le^R_0\ell_R`$、よって
  [(T.le0_cons_last)](#t-le0_cons_last) より $`(j_0+1)\le^M_0\lvert R\rvert`$。
  $`0\to^M_1\lvert R\rvert`$ の条件 6 を $`j:=j_0+1`$ に適用すると（$`0<j_0+1`$ と上の $`\le^M_0`$）
  $`M_{1,\lvert R\rvert}\le M_{1,j_0+1}`$、すなわち $`R_{1,\ell_R}\le R_{1,j_0}`$。
  一方 $`j_0\to^R_1\ell_R`$ の条件 4 は $`R_{1,j_0}<R_{1,\ell_R}`$ である。矛盾。

**$`M`$ の最終列の親は $`j_0+1`$ でありそれのみ.** $`y\to^M_{i_1}\lvert R\rvert`$ とする。
$`y=0`$ は上で否定した。$`y=y'+1`$ と書くと [(T.nextR_cons_last)](#t-nextR_cons_last) より
$`y'\to^R_{i_1}\ell_R`$ であり、$`\mathrm{hasParent}(R,i_1,\ell_R)`$ の一意性から $`y'=j_0`$、よって $`y=j_0+1`$。
また [(T.nextR_cons_last)](#t-nextR_cons_last) の逆向きにより $`(j_0+1)\to^M_{i_1}\lvert R\rvert`$ であるから、
$`\mathrm{hasParent}(M,i_1,\lvert R\rvert)`$ が成り立ち、
[(D.parent)](Def.md#d-parent) の性質と上の一意性より $`\mathrm{par}^M_{i_1}(\lvert R\rvert)=j_0+1`$。

**展開の比較.** 両辺に [(T.oper_bad_unfold)](Mechanized.md#t-oper_bad_unfold) を適用する。
係数は
```math
M\ \text{側}:\ \begin{cases}M_{0,\lvert R\rvert}-M_{0,j_0+1}=R_{0,\ell_R}-R_{0,j_0} & (0<i_1)\\ 0 & (\text{それ以外})\end{cases}
```
であり、$`R`$ 側の係数と一致する。これを $`\delta`$ とおく。また
```math
\lvert R\rvert-(j_0+1)=(\lvert R\rvert-1)-j_0=\ell_R-j_0 .
```
`List.take_succ_cons` より $`\mathrm{take}\,(j_0+1)\,M=(0,v)\mathbin{::}\mathrm{take}\,j_0\,R`$。
`List.range'_eq_map_range` を 2 回用いると
```math
\mathrm{range}'(j_0+1,\ \ell_R-j_0)=\mathrm{map}\,(\lambda j.\,j+1)\,\mathrm{range}'(j_0,\ \ell_R-j_0)
```
であり、これに $`\lambda j.\,(M_{0,j}+k\delta,\ M_{1,j})`$ を写すと、`List.map_map` と
[(T.entry_cons)](#t-entry_cons) により $`\lambda j.\,(R_{0,j}+k\delta,\ R_{1,j})`$ を
$`\mathrm{range}'(j_0,\ell_R-j_0)`$ に写したものに等しい。
`List.flatMap_congr` と `List.map_congr_left` により
```math
M[n]=(0,v)\mathbin{::}\Bigl(\mathrm{take}\,j_0\,R\mathbin{+\!\!+}
\mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda j.\,(R_{0,j}+k\delta,R_{1,j}))\,\mathrm{range}'(j_0,\ell_R-j_0)\bigr)\mathrm{range}(n)\Bigr)
```
であり、括弧の中は $`R[n]`$ そのものである。∎

<a id="t-oper_cons_succ"></a>
#### 定理 (A′) 後続の場合 (T.oper_cons_succ)

**主張** $`\mathrm{argOK}(R)`$、$`R\ne[]`$、$`R_{1,\ell_R}=0`$、$`\neg\,\mathrm{hasParent}(R,0,\ell_R)`$ ならば
```math
\bigl((0,v)\mathbin{::}R\bigr)[n]=\mathrm{flatMap}\bigl(\lambda \_.\ (0,v)\mathbin{::}\mathrm{dropLast}\,R\bigr)\,\mathrm{range}(n).
```

**証明** $`M:=(0,v)\mathbin{::}R`$ とおく。$`R\ne[]`$ より $`0<\lvert R\rvert`$、$`\ell_M=\lvert R\rvert`$。

**準備.** [(T.entry_cons_last)](#t-entry_cons_last) より $`M_{0,\lvert R\rvert}=R_{0,\ell_R}`$ であり、
$`\mathrm{argOK}(R)`$ と [(T.entry_pair_mem)](#t-entry_pair_mem) より $`0<R_{0,\ell_R}`$。
よって $`\ell_M=\lvert R\rvert\ne 0`$ かつ $`\neg(M_{0,\ell_M}=0\wedge M_{1,\ell_M}=0)`$。
[(T.idx1_cons_last)](#t-idx1_cons_last) と $`R_{1,\ell_R}=0`$、[(D.idx1)](Def.md#d-idx1) より
$`\mathrm{idx}_1(M,\ell_M)=\mathrm{idx}_1(R,\ell_R)=0`$。

**$`R`$ の最終列の行 0 の値は $`R`$ の中で最小.**
```math
(\ast)\qquad \forall k,\ k<\ell_R\to R_{0,\ell_R}\le R_{0,k}.
```
実際、ある $`k<\ell_R`$ で $`R_{0,k}<R_{0,\ell_R}`$ ならば
[(T.hasParent_zero_iff)](#t-hasParent_zero_iff) より $`\mathrm{hasParent}(R,0,\ell_R)`$ となり仮定に反する。

**根が最終列の行 0 の親であり、それのみ.** まず $`0\to^M_0\lvert R\rvert`$ を
[(D.nextrel0)](Def.md#d-nextrel0) の 5 条件で確かめる。
1. $`0<\lvert M\rvert`$、2. $`\lvert R\rvert<\lvert M\rvert`$、3. $`0<\lvert R\rvert`$。
4. $`M_{0,0}=0<R_{0,\ell_R}=M_{0,\lvert R\rvert}`$。
5. $`0<l<\lvert R\rvert`$ なる $`l`$ は $`l=l'+1`$ と書け、$`l'<\lvert R\rvert-1=\ell_R`$ であるから
   [(T.entry_cons)](#t-entry_cons) と $`(\ast)`$ より
   $`M_{0,\lvert R\rvert}=R_{0,\ell_R}\le R_{0,l'}=M_{0,l}`$。

一意性：$`y\to^M_0\lvert R\rvert`$ で $`y\ne 0`$ とすると $`y=y'+1`$ と書け、
[(T.nextR_cons_last)](#t-nextR_cons_last) より $`y'\to^R_0\ell_R`$。
その条件 3, 4 より $`y'<\ell_R`$ かつ $`R_{0,y'}<R_{0,\ell_R}`$ であるが、$`(\ast)`$ は $`R_{0,\ell_R}\le R_{0,y'}`$ を与える。矛盾。
よって $`\mathrm{hasParent}(M,0,\lvert R\rvert)`$ が成り立ち、$`\mathrm{par}^M_0(\lvert R\rvert)=0`$。

**展開形.** [(T.oper_root_tiling)](#t-oper_root_tiling) が適用でき、
$`\mathrm{idx}_1(M,\ell_M)=0`$ より係数は $`\delta=0`$、すなわち各 $`k`$ について
$`\lambda p.(\pi_0 p+k\cdot 0,\pi_1 p)`$ は恒等写像である。
$`R\ne[]`$ より $`\mathrm{dropLast}\,M=(0,v)\mathbin{::}\mathrm{dropLast}\,R`$ であるから、
```math
M[n]=\mathrm{flatMap}\bigl(\lambda\_. \ (0,v)\mathbin{::}\mathrm{dropLast}\,R\bigr)\,\mathrm{range}(n).
```
∎

<a id="t-oper_cons_tower"></a>
#### 定理 (D′) 塔の恒等式 (T.oper_cons_tower)

**主張** $`\mathrm{argOK}(R)`$、$`\mathrm{dom}(R)=T_m`$、$`v\le m`$ ならば
```math
\bigl((0,v)\mathbin{::}R\bigr)[n]=t^{v,R}_n .
```

**証明** $`M:=(0,v)\mathbin{::}R`$、$`x:=R_{0,\ell_R}`$ とおく。
[(T.not_domT_nil)](#t-not_domT_nil) より $`R\ne[]`$、よって $`0<\lvert R\rvert`$、$`\ell_M=\lvert R\rvert`$。

**準備.** [(T.entry_cons_last)](#t-entry_cons_last) より $`M_{0,\lvert R\rvert}=x`$、
$`M_{1,\lvert R\rvert}=R_{1,\ell_R}`$。[(D.domT)](#d-domT) より $`R_{1,\ell_R}=m+1`$。
$`\mathrm{argOK}(R)`$ と [(T.entry_pair_mem)](#t-entry_pair_mem) より $`0<x`$、
よって $`\ell_M\ne 0`$ かつ $`\neg(M_{0,\ell_M}=0\wedge M_{1,\ell_M}=0)`$。
[(T.idx1_cons_last)](#t-idx1_cons_last) と $`m+1>0`$、[(D.idx1)](Def.md#d-idx1) より
$`\mathrm{idx}_1(M,\ell_M)=\mathrm{idx}_1(R,\ell_R)=1`$。

**親は根 $`0`$ であり、それのみ.** $`v\le m<m+1=R_{1,\ell_R}`$ であるから
[(T.hasParent_cons_one)](#t-hasParent_cons_one) の第 2 選言が使え、
$`\mathrm{hasParent}(M,1,\lvert R\rvert)`$。
一意性のために $`y\to^M_1\lvert R\rvert`$ で $`y\ne 0`$ と仮定すると、$`y=y'+1`$ と書け
[(T.nextR_cons_last)](#t-nextR_cons_last) より $`y'\to^R_1\ell_R`$。
[(D.nextrel1)](Def.md#d-nextrel1) の条件 3, 5, 4 から $`\mathrm{r1cand}(R,\ell_R,y')`$ が成り立ち、
[(T.hasParent_one_iff)](#t-hasParent_one_iff) より $`\mathrm{hasParent}(R,1,\ell_R)`$ となるが、
これは $`\mathrm{dom}(R)=T_m`$ の第 2 条件に反する。よって親は $`0`$ のみであり
$`\mathrm{par}^M_1(\lvert R\rvert)=0`$。

**展開形.** $`M_{0,0}=0`$ であるから、[(T.oper_root_tiling)](#t-oper_root_tiling) の係数は
$`\delta=M_{0,\ell_M}-M_{0,0}=x-0=x`$（$`0<\mathrm{idx}_1(M,\ell_M)=1`$）。
$`R\ne[]`$ より $`\mathrm{dropLast}\,M=(0,v)\mathbin{::}\mathrm{dropLast}\,R=:D`$ であるから
```math
M[n]=\mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda p.\,(\pi_0 p+kx,\ \pi_1 p))\,D\bigr)\,\mathrm{range}(n).
```

**塔との一致.** 残るのは
```math
\Psi(n):\equiv\quad \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda p.\,(\pi_0 p+kx,\pi_1 p))\,D\bigr)\,\mathrm{range}(n)=t^{v,R}_n
```
を示すことである。$`n`$ に関する自然数の帰納法を用いる。帰納法の述語は $`\Psi(n)`$ である。

- **基底段 $`n=0`$**：$`\mathrm{range}(0)=[]`$ より左辺は $`[]`$、[(D.tow)](#d-tow) より $`t^{v,R}_0=[]`$。
- **帰納段 $`n\to n+1`$**：帰納法の仮定は $`\Psi(n)`$ である。
  `List.range_succ_eq_map` より
  $`\mathrm{range}(n+1)=0\mathbin{::}\mathrm{map}(\lambda j.\,j+1)\,\mathrm{range}(n)`$ であるから、
  左辺は「$`k=0`$ のブロック」と「$`k+1`$（$`k\in\mathrm{range}(n)`$）のブロックの連結」の連結である。
  $`k=0`$ のブロックは $`\mathrm{map}(\lambda p.(\pi_0 p+0,\pi_1 p))\,D=D`$。
  後半については、$`(k+1)x=kx+x`$ と加法の結合律により
  ```math
  \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda p.\,(\pi_0 p+(k+1)x,\pi_1 p))\,D\bigr)\,\mathrm{range}(n)
  =\mathrm{sh}_x\Bigl(\mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda p.\,(\pi_0 p+kx,\pi_1 p))\,D\bigr)\,\mathrm{range}(n)\Bigr)
  ```
  （`List.map_flatMap`, `List.map_map`, `List.map_congr_left`, `List.flatMap_congr` による）。
  帰納法の仮定 $`\Psi(n)`$ よりこれは $`\mathrm{sh}_x\bigl(t^{v,R}_n\bigr)`$ に等しい。よって左辺は
  ```math
  D\mathbin{+\!\!+}\mathrm{sh}_x\bigl(t^{v,R}_n\bigr)
  =(0,v)\mathbin{::}\Bigl(\mathrm{dropLast}\,R\mathbin{+\!\!+}\mathrm{sh}_x\bigl(t^{v,R}_n\bigr)\Bigr).
  ```
  他方 [(D.tow)](#d-tow) と [(D.graft)](#d-graft) より
  ```math
  t^{v,R}_{n+1}=(0,v)\mathbin{::}\mathrm{gr}\bigl(R,t^{v,R}_n\bigr)
  =(0,v)\mathbin{::}\Bigl(\mathrm{dropLast}\,R\mathbin{+\!\!+}
  \mathrm{map}(\lambda p.\,(\pi_0 p+R_{0,\ell_R},\pi_1 p))\,t^{v,R}_n\Bigr)
  ```
  であり、$`R_{0,\ell_R}=x`$ であるから両者は一致する。∎

<a id="t-domT_cons_of_lt"></a>
#### 定理 (E′) 連続の場合 (T.domT_cons_of_lt)

**主張** $`\mathrm{argOK}(R)`$、$`\mathrm{dom}(R)=T_m`$、$`m<v`$ ならば
$`\mathrm{dom}\bigl((0,v)\mathbin{::}R\bigr)=T_m`$。

**証明** $`M:=(0,v)\mathbin{::}R`$ とおく。[(T.not_domT_nil)](#t-not_domT_nil) より $`R\ne[]`$、
$`0<\lvert R\rvert`$、$`\ell_M=\lvert R\rvert`$。

第 1 条件：[(T.entry_cons_last)](#t-entry_cons_last) より
$`M_{1,\ell_M}=M_{1,\lvert R\rvert}=R_{1,\ell_R}=m+1`$（最後の等号は $`\mathrm{dom}(R)=T_m`$ の第 1 条件）。

第 2 条件：$`\lvert R\rvert<\lvert M\rvert`$（[(T.cons_len_lt)](#t-cons_len_lt)）より
[(T.hasParent_one_iff)](#t-hasParent_one_iff) が使える。
$`\mathrm{r1cand}(M,\lvert R\rvert,j_0)`$ なる $`j_0`$ が存在したとして矛盾を導く。
すなわち $`j_0<\lvert R\rvert`$、$`j_0\le^M_0\lvert R\rvert`$、$`M_{1,j_0}<M_{1,\lvert R\rvert}=m+1`$ とする。

- $`j_0=0`$ の場合：$`M_{1,0}=v`$ であるから $`v<m+1`$、すなわち $`v\le m`$。これは $`m<v`$ に矛盾する。
- $`j_0=j'+1`$ の場合：[(T.entry_cons)](#t-entry_cons) より $`M_{1,j'+1}=R_{1,j'}<m+1`$。
  $`j'+1<\lvert R\rvert`$ より $`j'<\lvert R\rvert-1=\ell_R`$。
  [(T.le0_cons_last)](#t-le0_cons_last) より $`j'\le^R_0\ell_R`$。
  $`R_{1,\ell_R}=m+1`$ であるから $`R_{1,j'}<R_{1,\ell_R}`$ であり、$`\mathrm{r1cand}(R,\ell_R,j')`$ が成り立つ。
  [(T.hasParent_one_iff)](#t-hasParent_one_iff) より $`\mathrm{hasParent}(R,1,\ell_R)`$ となるが、
  これは $`\mathrm{dom}(R)=T_m`$ の第 2 条件に矛盾する。∎

### 2.6 の組み立て

<a id="t-argOK_oper"></a>
#### 定理 $`\mathrm{argOK}`$ は $`M[n]`$ で保たれる (T.argOK_oper)

**主張** $`\mathrm{argOK}(R)`$ ならば $`\mathrm{argOK}(R[n])`$。

**証明** [(D.argOK)](#d-argOK) は「すべての対の行 0 の値が $`1`$ 以上」と同値である
（$`0<a`$ と $`1\le a`$ は自然数において同値）。よって
[(T.oper_mem_ge)](#t-oper_mem_ge) を $`c:=1`$、$`B:=R`$ に適用すればよい。∎

<a id="t-argOK_graft"></a>
#### 定理 $`\mathrm{argOK}`$ は graft で保たれる (T.argOK_graft)

**主張** $`R\ne[]`$ かつ $`\mathrm{argOK}(R)`$ ならば $`\mathrm{argOK}(\mathrm{gr}(R,z'))`$。

**証明** [(T.graft_mem_ge)](#t-graft_mem_ge) を $`c:=1`$、$`B:=R`$ に適用する（$`0<a\iff 1\le a`$）。∎

<a id="t-argOK_dropLast"></a>
#### 定理 $`\mathrm{argOK}`$ は末尾削除で保たれる (T.argOK_dropLast)

**主張** $`\mathrm{argOK}(R)`$ ならば $`\mathrm{argOK}(\mathrm{dropLast}\,R)`$。

**証明** `List.dropLast_subset` より $`\mathrm{dropLast}\,R`$ の要素は $`R`$ の要素であるから、
[(D.argOK)](#d-argOK) の条件がそのまま引き継がれる。∎

<a id="t-based_cons"></a>
#### 定理 主要ブロックは $`\mathrm{based}`$ (T.based_cons)

**主張** $`\mathrm{based}\bigl((0,v)\mathbin{::}R\bigr)`$。

**証明** [(D.based)](#d-based) より示すべきは $`((0,v)\mathbin{::}R)_{0,0}=0`$ であり、
先頭対は $`(0,v)`$ でその第 0 成分は $`0`$。∎

<a id="t-rsum_self_cons"></a>
#### 定理 主要ブロック自身の最小性 (T.rsum_self_cons)

**主張** $`\forall p\in (0,v)\mathbin{::}R,\ \bigl((0,v)\mathbin{::}R\bigr)_{0,0}\le\pi_0 p`$。

**証明** $`\bigl((0,v)\mathbin{::}R\bigr)_{0,0}=0`$ であり、自然数について $`0\le\pi_0 p`$ は常に成り立つ。∎

<a id="t-W_flatMap_copies"></a>
#### 定理 同一の木の $`n`$ 個の複製は $`W_u`$ に留まる (T.W_flatMap_copies)

**主張** $`Q\in W_u`$ かつ $`\forall p\in Q,\ Q_{0,0}\le\pi_0 p`$ ならば、任意の $`n`$ について
```math
\mathrm{flatMap}\,(\lambda\_. \ Q)\,\mathrm{range}(n)\in W_u .
```

**証明** $`n`$ に関する自然数の帰納法。帰納法の述語は
```math
\Phi(n):\equiv \mathrm{flatMap}\,(\lambda\_. \ Q)\,\mathrm{range}(n)\in W_u .
```

- **基底段 $`n=0`$**：$`\mathrm{range}(0)=[]`$ より列は $`[]`$ であり、[(T.W_nil)](#t-W_nil) より $`[]\in W_u`$。
- **帰納段 $`n\to n+1`$**：帰納法の仮定は $`\Phi(n)`$ である。
  `List.range_succ` より $`\mathrm{range}(n+1)=\mathrm{range}(n)\mathbin{+\!\!+}[n]`$ であるから
  ```math
  \mathrm{flatMap}\,(\lambda\_. Q)\,\mathrm{range}(n+1)
  =\bigl(\mathrm{flatMap}\,(\lambda\_. Q)\,\mathrm{range}(n)\bigr)\mathbin{+\!\!+}Q .
  ```
  [(T.W_add)](#t-W_add) を $`A:=\mathrm{flatMap}(\lambda\_.Q)\,\mathrm{range}(n)`$、$`B:=Q`$ に適用する。
  $`A\in W_u`$ は帰納法の仮定、$`Q\in W_u`$ は仮定である。
  $`\mathrm{rsum}(A,Q)`$：$`p\in A\mathbin{+\!\!+}Q`$ とすると、$`p\in A`$ の場合はある $`k`$ について $`p\in Q`$ であり、
  $`p\in Q`$ の場合はそのまま、いずれも仮定より $`Q_{0,0}\le\pi_0 p`$。∎

<a id="t-Wstar_closed"></a>
#### 定理 2.6 $`W^{*}`$ は各 $`A_u`$ の前不動点 (T.Wstar_closed)

**主張** 任意の $`u`$ と $`R`$ について、$`R\in A^{W}_u(W^{*})`$ ならば $`R\in W^{*}`$。

**証明** $`\mathrm{argOK}(R)`$ と $`v\in\mathbb{N}`$ を仮定して $`(0,v)\mathbin{::}R\in W_v`$ を示す。
$`M:=(0,v)\mathbin{::}R`$ とおく。

$`R=[]`$ の場合、$`M=[(0,v)]`$ であり [(T.Om_mem_W)](#t-Om_mem_W) より $`M\in W_v`$。
以下 $`R\ne[]`$、すなわち $`0<\lvert R\rvert`$ とする。このとき $`\ell_M=\lvert R\rvert`$ であり、
[(T.entry_cons_last)](#t-entry_cons_last) より $`M_{1,\ell_M}=R_{1,\ell_R}`$。
[(T.natDom_iff)](#t-natDom_iff) から次の 2 つを準備しておく。

- $`(\mathrm{n}_1)`$ $`\mathrm{hasParent}(M,1,\lvert R\rvert)`$ ならば $`\mathrm{natDom}(M)`$（第 2 選言）。
- $`(\mathrm{n}_2)`$ $`R_{1,\ell_R}=0`$ ならば $`\mathrm{natDom}(M)`$（第 1 選言、$`M_{1,\ell_M}=R_{1,\ell_R}`$ による）。

[(D.Aop)](#d-Aop) の 3 つの枝で場合分けする。

**枝 1**：$`\lvert R\rvert\le 1`$ かつ $`R_{1,0}=0`$。$`0<\lvert R\rvert`$ と合わせて $`\lvert R\rvert=1`$、
よって $`\ell_R=0`$ かつ $`R_{1,\ell_R}=0`$、また $`\mathrm{dropLast}\,R=[]`$。
$`\neg\,\mathrm{hasParent}(R,0,\ell_R)`$：親 $`j_0`$ が存在すれば
[(T.nextR_index_lt)](Mechanized.md#t-nextR_index_lt) より $`j_0<\ell_R=0`$ となり $`\mathbb{N}`$ では偽。
[(T.A1_intro)](#t-A1_intro) の枝 2 を用いる。$`\mathrm{natDom}(M)`$ は $`(\mathrm{n}_2)`$ による。
各 $`n\ge 1`$ について [(T.oper_cons_succ)](#t-oper_cons_succ) より
```math
M[n]=\mathrm{flatMap}\bigl(\lambda\_. \ (0,v)\mathbin{::}\mathrm{dropLast}\,R\bigr)\,\mathrm{range}(n)
=\mathrm{flatMap}\bigl(\lambda\_. \ [(0,v)]\bigr)\,\mathrm{range}(n),
```
これは [(T.W_flatMap_copies)](#t-W_flatMap_copies)（$`Q:=[(0,v)]`$、$`Q\in W_v`$ は
[(T.Om_mem_W)](#t-Om_mem_W)、最小性は [(T.rsum_self_cons)](#t-rsum_self_cons)）より $`W_v`$ に属する。

**枝 2**：$`\mathrm{natDom}(R)`$ かつ $`\forall n\ge 1,\ R[n]\in W^{*}`$。
$`\mathrm{hasParent}(R,\mathrm{idx}_1(R,\ell_R),\ell_R)`$ が成り立つか否かで場合分けする。

- **成り立つ場合 (B′)(C′)**：まず $`\mathrm{natDom}(M)`$ を示す。
  $`R_{1,\ell_R}=0`$ ならば $`(\mathrm{n}_2)`$。$`R_{1,\ell_R}\ne 0`$ ならば [(D.idx1)](Def.md#d-idx1) より
  $`\mathrm{idx}_1(R,\ell_R)=1`$ であるから仮定は $`\mathrm{hasParent}(R,1,\ell_R)`$ であり、
  [(T.hasParent_cons_one)](#t-hasParent_cons_one) の第 1 選言から
  $`\mathrm{hasParent}(M,1,\lvert R\rvert)`$、よって $`(\mathrm{n}_1)`$。
  [(T.A1_intro)](#t-A1_intro) の枝 2 を用いる。各 $`n\ge 1`$ について
  [(T.oper_cons_nat)](#t-oper_cons_nat) より $`M[n]=(0,v)\mathbin{::}R[n]`$ であり、
  $`R[n]\in W^{*}`$ に [(T.argOK_oper)](#t-argOK_oper) と $`v`$ を適用して
  $`(0,v)\mathbin{::}R[n]\in W_v`$。
- **成り立たない場合**：まず $`R_{1,\ell_R}=0`$ を示す。$`R_{1,\ell_R}\ne 0`$ とすると
  $`m:=R_{1,\ell_R}-1`$ について $`R_{1,\ell_R}=m+1`$ であり、[(D.idx1)](Def.md#d-idx1) より
  $`\mathrm{idx}_1(R,\ell_R)=1`$ であるから仮定は $`\neg\,\mathrm{hasParent}(R,1,\ell_R)`$、
  すなわち $`\mathrm{dom}(R)=T_m`$ となって $`\mathrm{natDom}(R)`$ に反する。
  よって $`R_{1,\ell_R}=0`$、したがって $`\mathrm{idx}_1(R,\ell_R)=0`$ であり
  $`\neg\,\mathrm{hasParent}(R,0,\ell_R)`$。
  [(T.A1_intro)](#t-A1_intro) の枝 2 を用いる。$`\mathrm{natDom}(M)`$ は $`(\mathrm{n}_2)`$。
  各 $`n\ge 1`$ について [(T.oper_cons_succ)](#t-oper_cons_succ) より
  $`M[n]=\mathrm{flatMap}(\lambda\_. \ (0,v)\mathbin{::}\mathrm{dropLast}\,R)\,\mathrm{range}(n)`$。
  [(T.W_flatMap_copies)](#t-W_flatMap_copies)（最小性は [(T.rsum_self_cons)](#t-rsum_self_cons)）により、
  $`(0,v)\mathbin{::}\mathrm{dropLast}\,R\in W_v`$ を示せばよい。
  - $`2\le\lvert R\rvert`$ の場合：$`\ell_R\ne 0`$ であり、仮定の否定形から
    [(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero) か
    [(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent) が適用でき
    $`R[1]=\mathrm{Pred}\,R=\mathrm{dropLast}\,R`$（$`\lvert R\rvert\ge 2`$）。
    $`n:=1`$ として $`R[1]\in W^{*}`$、すなわち $`\mathrm{dropLast}\,R\in W^{*}`$ を得、
    [(T.argOK_dropLast)](#t-argOK_dropLast) と $`v`$ を適用して
    $`(0,v)\mathbin{::}\mathrm{dropLast}\,R\in W_v`$。
  - $`\lvert R\rvert=1`$ の場合：$`\mathrm{dropLast}\,R=[]`$ であり
    $`(0,v)\mathbin{::}[]=[(0,v)]\in W_v`$（[(T.Om_mem_W)](#t-Om_mem_W)）。

**枝 3**：$`m<u`$、$`\mathrm{dom}(R)=T_m`$、$`\forall z\in W_m,\ \mathrm{based}(z)\to\mathrm{gr}(R,z)\in W^{*}`$。
$`v\le m`$ か否かで場合分けする。

- **$`v\le m`$ の場合 (D′)**：まず
  ```math
  (\mathrm{t})\qquad \forall k,\ t^{v,R}_k\in W_v
  ```
  を $`k`$ に関する自然数の帰納法で示す。帰納法の述語は $`\Theta(k):\equiv t^{v,R}_k\in W_v`$。
  - 基底段 $`k=0`$：[(D.tow)](#d-tow) より $`t^{v,R}_0=[]`$、[(T.W_nil)](#t-W_nil) より $`[]\in W_v`$。
  - 帰納段 $`k\to k+1`$：帰納法の仮定は $`\Theta(k)`$ である。
    $`\mathrm{based}(t^{v,R}_k)`$ を確かめる。$`k=0`$ なら $`t^{v,R}_0=[]`$ で
    [(T.based_nil)](#t-based_nil)、$`k=k'+1`$ なら
    $`t^{v,R}_k=(0,v)\mathbin{::}\mathrm{gr}(R,t^{v,R}_{k'})`$ で [(T.based_cons)](#t-based_cons)。
    $`\Theta(k)`$ と [(T.W_mono)](#t-W_mono)（$`v\le m`$）より $`t^{v,R}_k\in W_m`$。
    よって枝 3 の条件を $`z:=t^{v,R}_k`$ に適用して $`\mathrm{gr}(R,t^{v,R}_k)\in W^{*}`$、
    これに [(T.argOK_graft)](#t-argOK_graft) と $`v`$ を適用して
    $`(0,v)\mathbin{::}\mathrm{gr}(R,t^{v,R}_k)=t^{v,R}_{k+1}\in W_v`$。

  [(T.A1_intro)](#t-A1_intro) の枝 2 を用いる。$`\mathrm{natDom}(M)`$：
  $`\mathrm{dom}(R)=T_m`$ より $`R_{1,\ell_R}=m+1`$ であり $`v\le m<m+1`$ であるから
  [(T.hasParent_cons_one)](#t-hasParent_cons_one) の第 2 選言より
  $`\mathrm{hasParent}(M,1,\lvert R\rvert)`$、よって $`(\mathrm{n}_1)`$。
  各 $`n\ge 1`$ について [(T.oper_cons_tower)](#t-oper_cons_tower) より $`M[n]=t^{v,R}_n`$ であり、
  $`(\mathrm{t})`$ より $`W_v`$ に属する。
- **$`m<v`$ の場合 (E′)**：[(T.A1_intro)](#t-A1_intro) の枝 3 を同じ $`m`$ で用いる。
  $`m<v`$ であり、$`\mathrm{dom}(M)=T_m`$ は [(T.domT_cons_of_lt)](#t-domT_cons_of_lt) による。
  $`z\in W_m`$ で $`\mathrm{based}(z)`$ なるものについて、[(T.graft_cons)](#t-graft_cons) より
  $`\mathrm{gr}(M,z)=(0,v)\mathbin{::}\mathrm{gr}(R,z)`$ であり、
  枝 3 の条件より $`\mathrm{gr}(R,z)\in W^{*}`$、これに
  [(T.argOK_graft)](#t-argOK_graft) と $`v`$ を適用して $`(0,v)\mathbin{::}\mathrm{gr}(R,z)\in W_v`$。∎

---

## 7. Buchholz 2.7/2.8 — ブロック長に関する帰納法

<a id="t-tree_shift"></a>
#### 定理 単一の木の平行移動表示 (T.tree_shift)

**主張** $`\forall q\in R,\ \pi_0 p_0\le\pi_0 q`$ ならば
```math
\mathrm{sh}_{\pi_0 p_0}\Bigl((0,\pi_1 p_0)\mathbin{::}\mathrm{sh}^{-}_{\pi_0 p_0}R\Bigr)=p_0\mathbin{::}R .
```

**証明** `List.map_cons` により左辺は
```math
\bigl(0+\pi_0 p_0,\ \pi_1 p_0\bigr)\mathbin{::}\mathrm{sh}_{\pi_0 p_0}\bigl(\mathrm{sh}^{-}_{\pi_0 p_0}R\bigr)
```
である。先頭は $`(\pi_0 p_0,\pi_1 p_0)=p_0`$ であり、
残りは [(T.map_sub_add)](#t-map_sub_add)（$`c:=\pi_0 p_0`$、$`X:=R`$、仮定がその前提）より $`R`$ に等しい。∎

<a id="t-mem_of_Aclosed_aux"></a>
#### 定理 2.7 の補助（長さの上界つき） (T.mem_of_Aclosed_aux)

**主張** 任意の $`N`$ について、$`\lvert M\rvert\le N`$ なる任意の $`M`$ と、
```math
\bigl(\forall u,\ \forall M',\ M'\in A^{W}_u(X)\to M'\in X\bigr)
```
をみたす任意の $`X`$ に対し $`M\in X`$。

**証明** $`N`$ に関する自然数の帰納法。帰納法の述語は
```math
\Phi(N):\equiv\ \forall M,\ \lvert M\rvert\le N \to \forall X,\
\bigl(\forall u\,M',\ M'\in A^W_u(X)\to M'\in X\bigr)\to M\in X .
```

- **基底段 $`N=0`$**：$`\lvert M\rvert\le 0`$ より $`M=[]`$。仮定 $`\bigl(\forall u\,M',\ M'\in A^W_u(X)\to M'\in X\bigr)`$ を $`u:=0`$、$`M':=[]`$、
  [(D.Aop)](#d-Aop) の枝 1（$`\lvert[]\rvert=0\le 1`$、$`[]_{1,0}=0`$）に適用して $`[]\in X`$。
- **帰納段 $`N\to N+1`$**：帰納法の仮定は $`\Phi(N)`$ である。$`\lvert M\rvert\le N+1`$ とし、$`X`$ と仮定
  $`\bigl(\forall u\,M',\ M'\in A^W_u(X)\to M'\in X\bigr)`$ を取る。
  $`M=[]`$ ならば基底段と同じ議論で $`M\in X`$。以下 $`M\ne[]`$ とする。
  [(T.split_lastMin)](#t-split_lastMin) より $`M=A\mathbin{+\!\!+}P`$、$`P\ne[]`$、$`\mathrm{rsum}(A,P)`$、
  $`\forall p\in P.\mathrm{tail},\ P_{0,0}<\pi_0 p`$ なる $`A,P`$ を取る。
  $`0<\lvert P\rvert`$ であり、$`\lvert A\rvert+\lvert P\rvert=\lvert M\rvert\le N+1`$。
  $`A=[]`$ か否かで場合分けする。

  - **$`A=[]`$ の場合**：$`M=P`$ であり、$`P\ne[]`$ より $`P=p_0\mathbin{::}R`$ と書ける。
    - $`\forall q\in R,\ \pi_0 p_0<\pi_0 q`$：$`R=P.\mathrm{tail}`$ であり $`P_{0,0}=\pi_0 p_0`$ であるから、
      末尾条件そのものである。
    - $`\mathrm{argOK}\bigl(\mathrm{sh}^{-}_{\pi_0 p_0}R\bigr)`$：その要素は $`(\pi_0 q-\pi_0 p_0,\ \pi_1 q)`$
      （$`q\in R`$）の形であり、$`\pi_0 p_0<\pi_0 q`$ より $`0<\pi_0 q-\pi_0 p_0`$。
    - $`\lvert\mathrm{sh}^{-}_{\pi_0 p_0}R\rvert=\lvert R\rvert=\lvert P\rvert-1\le N`$
      （$`\lvert P\rvert\le N+1`$ による）。よって帰納法の仮定 $`\Phi(N)`$ を
      $`M:=\mathrm{sh}^{-}_{\pi_0 p_0}R`$、$`X:=W^{*}`$ とし、$`\forall u\,M',\ M'\in A^W_u(W^{*})\to M'\in W^{*}`$ として
      [(T.Wstar_closed)](#t-Wstar_closed) を与えると、
      $`\mathrm{sh}^{-}_{\pi_0 p_0}R\in W^{*}`$。
    - [(D.Wstar)](#d-Wstar) に $`\mathrm{argOK}`$ と $`v:=\pi_1 p_0`$ を適用して
      $`(0,\pi_1 p_0)\mathbin{::}\mathrm{sh}^{-}_{\pi_0 p_0}R\in W_{\pi_1 p_0}`$。
    - [(T.W_shift)](#t-W_shift)（$`d:=\pi_0 p_0`$）と [(T.tree_shift)](#t-tree_shift) より
      $`p_0\mathbin{::}R\in W_{\pi_1 p_0}`$。
    - 最後に [(T.A2')](#t-A2') による $`W_{\pi_1 p_0}`$ の最小不動点帰納法（帰納法の述語は
      $`\Phi'(M'):\equiv M'\in X`$、前提は上の仮定を $`u:=\pi_1 p_0`$ に固定したもの）から
      $`W_{\pi_1 p_0}\subseteq X`$、よって $`M=p_0\mathbin{::}R\in X`$。
  - **$`A\ne[]`$ の場合**：$`0<\lvert A\rvert`$ と $`0<\lvert P\rvert`$ と $`\lvert A\rvert+\lvert P\rvert\le N+1`$ より
    $`\lvert A\rvert\le N`$ かつ $`\lvert P\rvert\le N`$。
    - 帰納法の仮定 $`\Phi(N)`$ を $`M:=A`$、$`X:=X`$ に適用して $`A\in X`$。
    - 各 $`u`$ について、上の仮定を $`u`$ に固定したもの（$`\forall M',\ M'\in A^W_u(X)\to M'\in X`$）と
      $`A\in X`$ に [(T.XA_closed)](#t-XA_closed) を適用すると
      $`\forall M',\ M'\in A^W_u(X^{(A)})\to M'\in X^{(A)}`$ を得る。すなわち $`X^{(A)}`$ もまた
      $`\forall u\,M',\ M'\in A^W_u(X^{(A)})\to M'\in X^{(A)}`$ をみたす。
      よって帰納法の仮定 $`\Phi(N)`$ を $`M:=P`$、$`X:=X^{(A)}`$ に適用して $`P\in X^{(A)}`$。
    - [(D.XA)](#d-XA) に $`\mathrm{rsum}(A,P)`$ を適用して $`A\mathbin{+\!\!+}P=M\in X`$。∎

<a id="t-mem_of_Aclosed"></a>
#### 定理 2.7 すべてのブロックは各 $`A_u`$ の前不動点に属する (T.mem_of_Aclosed)

**主張** $`\bigl(\forall u\,M,\ M\in A^{W}_u(X)\to M\in X\bigr)`$ ならば $`\forall M,\ M\in X`$。

**証明** [(T.mem_of_Aclosed_aux)](#t-mem_of_Aclosed_aux) を $`N:=\lvert M\rvert`$ に適用する。
$`\lvert M\rvert\le\lvert M\rvert`$ であるから前提はみたされる。∎

<a id="t-mem_Wstar"></a>
#### 定理 2.8 すべての引数ブロックは $`W^{*}`$ に属する (T.mem_Wstar)

**主張** $`\forall R,\ R\in W^{*}`$。

**証明** [(T.mem_of_Aclosed)](#t-mem_of_Aclosed) を $`X:=W^{*}`$ に適用する。
その前提は [(T.Wstar_closed)](#t-Wstar_closed) である。∎

<a id="t-mem_W_of_bound_aux"></a>
#### 定理 水準の上界による所属（補助） (T.mem_W_of_bound_aux)

**主張** 任意の $`N`$ について、$`\lvert M\rvert\le N`$ かつ $`\forall p\in M,\ \pi_1 p\le u`$ ならば $`M\in W_u`$。

**証明** $`N`$ に関する自然数の帰納法。帰納法の述語は
```math
\Phi(N):\equiv\ \forall M,\ \lvert M\rvert\le N\to\forall u,\ \bigl(\forall p\in M,\ \pi_1 p\le u\bigr)\to M\in W_u .
```

- **基底段 $`N=0`$**：$`\lvert M\rvert\le 0`$ より $`M=[]`$ であり、[(T.W_nil)](#t-W_nil) より $`[]\in W_u`$。
- **帰納段 $`N\to N+1`$**：帰納法の仮定は $`\Phi(N)`$ である。$`\lvert M\rvert\le N+1`$、
  $`\forall p\in M,\ \pi_1 p\le u`$ とする。$`M=[]`$ なら [(T.W_nil)](#t-W_nil)。以下 $`M\ne[]`$ とする。
  [(T.split_lastMin)](#t-split_lastMin) より $`M=A\mathbin{+\!\!+}P`$、$`P\ne[]`$、$`\mathrm{rsum}(A,P)`$、
  $`\forall p\in P.\mathrm{tail},\ P_{0,0}<\pi_0 p`$ を得る。$`P=p_0\mathbin{::}R`$ と書く。

  - $`\forall q\in R,\ \pi_0 p_0<\pi_0 q`$：末尾条件と $`P_{0,0}=\pi_0 p_0`$ による。
  - $`\mathrm{argOK}\bigl(\mathrm{sh}^{-}_{\pi_0 p_0}R\bigr)`$：要素は $`(\pi_0 q-\pi_0 p_0,\pi_1 q)`$ の形であり
    $`\pi_0 p_0<\pi_0 q`$ より第 0 成分は $`0`$ より大きい。
  - [(T.mem_Wstar)](#t-mem_Wstar) より $`\mathrm{sh}^{-}_{\pi_0 p_0}R\in W^{*}`$、
    これに $`\mathrm{argOK}`$ と $`v:=\pi_1 p_0`$ を適用して
    $`(0,\pi_1 p_0)\mathbin{::}\mathrm{sh}^{-}_{\pi_0 p_0}R\in W_{\pi_1 p_0}`$。
  - [(T.tree_shift)](#t-tree_shift) と [(T.W_shift)](#t-W_shift) より $`p_0\mathbin{::}R\in W_{\pi_1 p_0}`$。
  - $`p_0\in A\mathbin{+\!\!+}P`$ であるから仮定より $`\pi_1 p_0\le u`$、
    [(T.W_mono)](#t-W_mono) より $`p_0\mathbin{::}R\in W_u`$。

  $`A=[]`$ か否かで場合分けする。
  - $`A=[]`$ の場合：$`M=P=p_0\mathbin{::}R\in W_u`$。
  - $`A\ne[]`$ の場合：$`0<\lvert A\rvert`$ と $`0<\lvert P\rvert`$、$`\lvert A\rvert+\lvert P\rvert\le N+1`$ より
    $`\lvert A\rvert\le N`$。$`p\in A`$ ならば $`p\in A\mathbin{+\!\!+}P`$ であるから $`\pi_1 p\le u`$ であり、
    帰納法の仮定 $`\Phi(N)`$ より $`A\in W_u`$。
    [(T.W_add)](#t-W_add) を $`A`$、$`P`$、$`\mathrm{rsum}(A,P)`$ に適用して $`M=A\mathbin{+\!\!+}P\in W_u`$。∎

<a id="t-mem_W_of_bound"></a>
#### 定理 水準の上界による所属 (T.mem_W_of_bound)

**主張** $`\forall p\in M,\ \pi_1 p\le u`$ ならば $`M\in W_u`$。

**証明** [(T.mem_W_of_bound_aux)](#t-mem_W_of_bound_aux) を $`N:=\lvert M\rvert`$ に適用する
（$`\lvert M\rvert\le\lvert M\rvert`$）。∎

<a id="t-le_maxr1"></a>
#### 定理 $`\mathrm{maxr1}`$ は行 1 の上界 (T.le_maxr1)

**主張** $`\forall p\in S,\ \pi_1 p\le\mathrm{maxr1}\,S`$。

（[(T.le_maxr1)](Nrmstep.md#t-le_maxr1) と同一の主張であり、本章の名前空間で再証明されている。）

**証明** $`S`$ の構造に関するリストの帰納法。帰納法の述語は
```math
\Phi(S):\equiv\ \forall p\in S,\ \pi_1 p\le\mathrm{maxr1}\,S .
```

- **基底段 $`S=[]`$**：$`p\in[]`$ をみたす $`p`$ は存在しないから成立する。
- **帰納段 $`S=q\mathbin{::}S'`$**：帰納法の仮定は $`\Phi(S')`$ である。
  [(T.maxr1_cons)](Nrmstep.md#t-maxr1_cons) より
  $`\mathrm{maxr1}(q\mathbin{::}S')=\max(\pi_1 q,\ \mathrm{maxr1}\,S')`$。
  $`p\in q\mathbin{::}S'`$ は $`p=q`$ または $`p\in S'`$ のいずれかである。
  - $`p=q`$：$`\pi_1 q\le\max(\pi_1 q,\mathrm{maxr1}\,S')`$。
  - $`p\in S'`$：$`\Phi(S')`$ より $`\pi_1 p\le\mathrm{maxr1}\,S'\le\max(\pi_1 q,\mathrm{maxr1}\,S')`$。∎

<a id="t-mem_W_maxr1"></a>
#### 定理 すべてのブロックは $`W_{\mathrm{maxr1}}`$ に属する (T.mem_W_maxr1)

**主張** $`M\in W_{\mathrm{maxr1}\,M}`$。

**証明** [(T.mem_W_of_bound)](#t-mem_W_of_bound) を $`u:=\mathrm{maxr1}\,M`$ に適用する。
その前提 $`\forall p\in M,\ \pi_1 p\le\mathrm{maxr1}\,M`$ は [(T.le_maxr1)](#t-le_maxr1) である。∎

---

## 8. 所属 — Buchholz (1987) 2.8 の PSS 版

<a id="t-W_membership"></a>
#### 定理 標準形の $`W`$ 所属 (T.W_membership)

**主張** $`M\in\mathrm{ST\_PS}`$ ならば $`\exists u,\ M\in W_u`$。

**証明** $`u:=\mathrm{maxr1}\,M`$ と取ればよい。$`M\in W_{\mathrm{maxr1}\,M}`$ は
[(T.mem_W_maxr1)](#t-mem_W_maxr1) である。
（[(T.mem_W_maxr1)](#t-mem_W_maxr1) はすべてのペア列について成り立つから、
仮定 $`M\in\mathrm{ST\_PS}`$ はこの証明では使われない。）∎

---

## 5. 組み立て（Assembly）

Lean 側では節番号 5 がここで再び用いられている。本節はこのファイルの結論を与える。

<a id="t-wf_of_cofinality_and_membership"></a>
#### 定理 2 本の柱から整礎性へ (T.wf_of_cofinality_and_membership)

**主張** $`\mathrm{hcof}`$（§3 の共終性仮定）と
```math
\mathrm{hmem}:\quad \forall M,\ M\in\mathrm{ST\_PS}\to\exists u,\ M\in W_u
```
を仮定すると、関係 $`R`$（[(D.Rst)](#d-Rst)）は整礎である。

**証明** `WellFounded.intro` により、各 $`M`$ について $`\mathrm{Acc}\,R\,M`$ を示せばよい。
$`M\in\mathrm{ST\_PS}`$ か否かで場合分けする。

- $`M\in\mathrm{ST\_PS}`$ の場合：$`\mathrm{hmem}`$ より $`M\in W_u`$ なる $`u`$ を取り、
  [(T.acc_of_W)](#t-acc_of_W) を適用して $`\mathrm{Acc}\,R\,M`$。
- $`M\notin\mathrm{ST\_PS}`$ の場合：`Acc.intro` を用いる。$`y\mathrel{R}M`$ なる $`y`$ が存在すれば
  [(D.Rst)](#d-Rst) の第 2 成分より $`M\in\mathrm{ST\_PS}`$ となり仮定に反する。
  よって $`M`$ は $`R`$ について前者をもたず、$`\mathrm{Acc}\,R\,M`$。∎

<a id="t-wf_olt_ST_PS_of_cofinality"></a>
#### 定理 共終性から $`\mathrm{ST\_PS}`$ 上の $`\prec`$ の整礎性へ (T.wf_olt_ST_PS_of_cofinality)

**主張** $`\mathrm{hcof}`$ を仮定すると、関係
```math
(a,b)\ \mapsto\ a\in\mathrm{ST\_PS}\ \wedge\ b\in\mathrm{ST\_PS}\ \wedge\ \mathrm{tr}\,a\prec\mathrm{tr}\,b
```
は整礎である。

**証明** この関係は [(D.Rst)](#d-Rst) を展開したものである。
[(T.wf_of_cofinality_and_membership)](#t-wf_of_cofinality_and_membership) に $`\mathrm{hcof}`$ と
$`\mathrm{hmem}:=`$ [(T.W_membership)](#t-W_membership) を与えればよい。∎

---

## 9. 記録

本節に宣言はない。Lean 側の同名の節に対応する記録である。

**設計上の 2 つの選択.**

1. $`\mathrm{dom}(M)=T_m`$ を PSS 自身の $`\neg\,\mathrm{hasParent}(M,1,\ell_M)`$ として読み
   （[(D.domT)](#d-domT)）、$`T_m`$ 添字の基本列を graft（[(D.graft)](#d-graft)）とした。
   この読み替えは仮定ではなく定理として検証されている：
   [(T.hasParent_one_iff)](#t-hasParent_one_iff) は「$`\mathrm{nextrel1}`$ は行 1 の値が真に小さい行 0 祖先のうち
   **最大**のものを選ぶ」ことを示し、その結果「行 1 の親が存在する $`\iff`$ そのような行 0 祖先が
   **1 つでも**存在する」が成り立つ。
2. [(D.Aop)](#d-Aop) の枝 2 には $`\mathrm{natDom}`$（[(D.natDom)](#d-natDom)）が付いている。
   これがないと、$`\mathrm{dom}(M)=T_m`$ をみたす $`M`$ に対して枝 2 も枝 3 も適用可能になる。
   枝 2 の側では [(T.oper_eq_graft_nil_of_domT)](#t-oper_eq_graft_nil_of_domT) により
   $`M[n]=\mathrm{gr}(M,[])`$ となり、[(T.Wstar_closed)](#t-Wstar_closed) の (D′) の場合で用いる塔
   [(D.tow)](#d-tow) を作ることができない。

**中核の補題.** [(T.oper_shift)](#t-oper_shift) は
[(T.oper_append_right)](Nrm.md#t-oper_append_right)（右側の列 $`T`$ に $`T_{0,0}=0`$ を要求する）を
[(T.oper_append_gen)](#t-oper_append_gen)（[(D.rsum)](#d-rsum) のみを要求する）へ一般化する。
[(T.split_lastMin)](#t-split_lastMin) が与える分割はこの一般形にそのまま適合する。

**加法についての注意.** Buchholz の 2.4(b) は原典では項の正規形条件を伴うが、
本章の [(T.W_add)](#t-W_add) が要求するのは位置についての条件 [(D.rsum)](#d-rsum) だけである。
これは $`\mathrm{tr}`$（[(D.translate)](Mechanized.md#d-translate)）の第 3 成分（後続和）に
正規形条件が課されていないことによる。実際、[(T.oper_cons_succ)](#t-oper_cons_succ)、
[(T.oper_cons_nat)](#t-oper_cons_nat)、[(T.oper_cons_tower)](#t-oper_cons_tower)、
[(T.domT_cons_of_lt)](#t-domT_cons_of_lt) の主張と証明には $`\mathrm{tr}`$ も $`\prec`$ も現れない。

**$`\mathrm{based}`$ と $`\mathrm{argOK}`$ の区別.**
$`\mathrm{based}(z)`$（[(D.based)](#d-based)、$`z_{0,0}=0`$）は [(T.oper_head_eq)](#t-oper_head_eq) が保つ性質、
$`\mathrm{argOK}(R)`$（[(D.argOK)](#d-argOK)、$`\forall p\in R,\ 0<\pi_0 p`$）は
[(T.le0_cons_zero)](#t-le0_cons_zero) で根が全列の行 0 祖先になるために使う性質であり、両者は異なる。
[(D.Aop)](#d-Aop) 枝 3 の $`\mathrm{based}(z)`$ が必要であることは §1c の計算例が示している。

**$`\mathrm{ST\_PS}`$ の使用箇所.** [(T.mem_W_of_bound)](#t-mem_W_of_bound) はすべてのペア列について
所属を与えるから、[(T.W_membership)](#t-W_membership) は $`\mathrm{ST\_PS}`$ を使わない。
$`\mathrm{ST\_PS}`$ が使われるのは [(T.acc_of_W)](#t-acc_of_W) の枝 1 と、
[(T.stps_ne_nil)](#t-stps_ne_nil)・[(T.stps_len_one)](#t-stps_len_one) の 2 つの小事実だけである。

**公理.** Lean 側では本章の主要な定理について `#print axioms` が実行されており、
いずれも `[propext, Classical.choice, Quot.sound]` のみに依存する（`sorryAx` を含まない）。

