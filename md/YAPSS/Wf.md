[← 目次](README.md)

# Wf — スパイン・最大添字・Cantor 標準形条件 $\mathrm{cnf}$ と展開によるその保存

本章は項の**最左引数スパイン** $\mathrm{sp}$、その最大値 $\mathrm{climb}$、項に現れる添字の最大値 $\mathrm{maxsub}$、
および添字列の辞書式広義順序 $\mathrm{slex}$ を定義し、$\mathrm{sp}(\mathrm{tr}\,M)$ と $\mathrm{maxsub}(\mathrm{tr}\,M)$ を
ペア列の言葉に書き直す。続いて Cantor 標準形条件 $\mathrm{cnf}$（先頭和に並ぶ主要項の添字優先順序 $\prec$ による非増加性）を定義し、
コピー・タイリング $\mathrm{sh}_d$, $\mathrm{cp}_d$ を用いて展開 $M[n]$ のすべての分岐で $\mathrm{cnf}$ が保たれること
[(T.cnf_oper)](#t-cnf_oper) を証明する。
本章の主結論は [(T.cnf_ST_PS)](#t-cnf_ST_PS)：$M\in\mathrm{ST\_PS}$ ならば $\mathrm{cnf}(\mathrm{tr}\,M)$ である。

## 記法

この章で導入する Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `spine t` | $\mathrm{sp}\,t$ | 最左引数スパイン（添字の有限列） |
| `cmax xs` | $\mathrm{cmax}\,xs$ | 自然数の有限列の最大値（空列では $0$） |
| `climb t` | $\mathrm{climb}\,t$ | スパイン最大値 $\mathrm{cmax}(\mathrm{sp}\,t)$ |
| `maxsub t` | $\mathrm{maxsub}\,t$ | 項 $t$ に現れる添字の最大値 |
| `slex xs ys` | $\mathrm{slex}(xs,ys)$ | 添字列の辞書式広義順序 |
| `incpref M` | $\mathrm{inc}\,M$ | 行 0 が狭義増加する極大な前部分列 |
| `cnf t` | $\mathrm{cnf}\,t$ | Cantor 標準形条件 |
| `shiftr0 d M` | $\mathrm{sh}_d M$ | $M$ の行 0 を一様に $d$ だけ増やした列 |
| `copies d blk n` | $\mathrm{cp}_d(B,n)$ | ブロック $B$ の昇順 $n$ コピー |
| `tops t` | $\mathrm{tops}\,t$ | 先頭和に並ぶ主要項の添字の列 |

他章から引き継ぐ記法（[`Def.md`](Def.md), [`Mechanized.md`](Mechanized.md) で定義済み）。

| Lean | 本文 | 意味 |
|---|---|---|
| `Three`, `Z`, `P a b c` | $\mathrm{Three}$, $\mathsf{Z}$, $\mathsf{P}(a,b,c)$ | 三分岐記法の型と構成子 |
| `x <o y`, `x ≤o y` | $x\prec y$, $x\preceq y$ | 添字優先辞書式順序とその広義版 |
| `translate M` | $\mathrm{tr}\,M$ | ペア列の翻訳 |
| `M.length` | $\lvert M\rvert$ | 長さ |
| `p.1`, `p.2` | $\pi_0 p$, $\pi_1 p$ | 対 $p$ の第 0・第 1 成分 |
| `M.getD j (0,0)` | $M\langle j\rangle$ | 第 $j$ 対（範囲外なら $(0,0)$） |
| `entry M i j` | $M_{i,j}$ | 第 $j$ 対の第 $i$ 成分 |
| `M⟦n⟧` | $M[n]$ | 展開（コピー数 $n$） |
| `diagSeq u v` | $\Delta_u^v$ | 対角列 $((j,j))_{j=u}^{v}$ |
| `sndSet M` | $\mathrm{sndSet}\,M$ | $M$ に現れる行 1 の値の集合 |
| `L.takeWhile (a < ·.1)` | $\mathrm{tw}_a L$ | 行 0 が $a$ より真に大きい極大な前部分列 |
| `L.dropWhile (a < ·.1)` | $\mathrm{dw}_a L$ | その残り |

リスト操作は [`Mechanized.md`](Mechanized.md) と同じ記号を用いる：
$\mathrm{map}\,f\,L$、$\mathrm{flatMap}\,f\,L$、$\mathrm{take}\,j\,L$、$\mathrm{dropLast}\,L$、
$\mathrm{getLast}\,L$、$\mathrm{headI}\,L$、$\mathrm{range}(n) = [0,\dots,n-1]$、
$\mathrm{range}'(a,m) = [a,\dots,a+m-1]$。さらに本章では

$$\mathrm{replicate}(n,x) := \underbrace{[x,\dots,x]}_{n\ \text{個}},\qquad
  \mathrm{flatten}\,[L_0,\dots,L_{k-1}] := L_0 \mathbin{+\!\!+}\cdots\mathbin{+\!\!+} L_{k-1}$$

を用いる（Lean の `List.replicate`, `List.flatten`）。
また $L[i]$ は $i<\lvert L\rvert$ のときの $L$ の第 $i$ 要素、$L.\mathrm{getD}\,i\,d$ は
$i<\lvert L\rvert$ なら第 $i$ 要素、そうでなければ $d$ を返す関数である。

**注（$\neg(x\prec y)$ の言い換え）.** 以下でくり返し使うので、ここで一度だけ示しておく。
任意の $x,y\in\mathrm{Three}$ について

$$\neg(x\prec y)\ \iff\ y\preceq x .$$

実際 $\neg(x\prec y)$ ならば [(T.olt_total)](Mechanized.md#t-olt_total) より $x=y$ か $y\prec x$ であり、
いずれの場合も [(D.ole)](Mechanized.md#d-ole) より $y\preceq x$。
逆に $y\preceq x$ かつ $x\prec y$ とすると、$y\prec x$ の場合は [(T.olt_trans)](Mechanized.md#t-olt_trans) より
$x\prec x$、$y=x$ の場合は $x\prec y=x$ となり、どちらも [(T.olt_irrefl)](Mechanized.md#t-olt_irrefl) に矛盾する。

## 最左引数スパイン・その最大値・最大添字

<a id="d-spine"></a>
### 定義 最左引数スパイン (D.spine)

$\mathrm{sp}:\mathrm{Three}\to\mathbb{N}^{<\omega}$ を項の構造帰納で定める。

$$\mathrm{sp}\,\mathsf{Z} := [],\qquad
  \mathrm{sp}\,\mathsf{P}(a,b,c) := a \mathbin{::} \mathrm{sp}\,b .$$

すなわち $\mathsf{P}(a_0,\mathsf{P}(a_1,\dots,\mathsf{P}(a_{k-1},\mathsf{Z},c_{k-1}),\dots),c_0)$ に対し
$\mathrm{sp}$ は $[a_0,a_1,\dots,a_{k-1}]$ を返す。第 3 引数（後続和）$c$ は読まれない。
再帰呼び出しの引数 $b$ は $\mathsf{P}(a,b,c)$ の真部分項であるから、この定義は構造帰納として整合的である。

<a id="t-spine_Z"></a>
### 定理 $\mathsf{Z}$ のスパイン (T.spine_Z)

**主張** $\mathrm{sp}\,\mathsf{Z} = []$。

**証明** [(D.spine)](#d-spine) の第 1 式であり、両辺は定義により同一である。∎

<a id="t-spine_P"></a>
### 定理 $\mathsf{P}$ のスパイン (T.spine_P)

**主張** 任意の $a\in\mathbb{N}$, $b,c\in\mathrm{Three}$ に対し
$\mathrm{sp}\,\mathsf{P}(a,b,c) = a\mathbin{::}\mathrm{sp}\,b$。

**証明** [(D.spine)](#d-spine) の第 2 式であり、両辺は定義により同一である。∎

<a id="d-cmax"></a>
### 定義 自然数列の最大値 (D.cmax)

$$\mathrm{cmax}\,xs := \mathrm{foldr}\ \max\ 0\ xs ,$$

すなわち

$$\mathrm{cmax}\,[] = 0,\qquad \mathrm{cmax}(x\mathbin{::}xs) = \max\bigl(x,\ \mathrm{cmax}\,xs\bigr).$$

空列に対する値は $0$ である。

<a id="d-climb"></a>
### 定義 スパイン最大値 (D.climb)

$$\mathrm{climb}\,t := \mathrm{cmax}(\mathrm{sp}\,t)$$

（[(D.cmax)](#d-cmax), [(D.spine)](#d-spine)）。

<a id="d-maxsub"></a>
### 定義 最大添字 (D.maxsub)

$\mathrm{maxsub}:\mathrm{Three}\to\mathbb{N}$ を項の構造帰納で定める。

$$\mathrm{maxsub}\,\mathsf{Z} := 0,\qquad
  \mathrm{maxsub}\,\mathsf{P}(a,b,c) := \max\bigl(a,\ \max(\mathrm{maxsub}\,b,\ \mathrm{maxsub}\,c)\bigr).$$

$\mathrm{sp}$ と異なり第 3 引数 $c$ も読む。再帰呼び出しの引数 $b$, $c$ はいずれも $\mathsf{P}(a,b,c)$ の
真部分項であるから、この定義は構造帰納として整合的である。

<a id="t-maxsub_Z"></a>
### 定理 $\mathsf{Z}$ の最大添字 (T.maxsub_Z)

**主張** $\mathrm{maxsub}\,\mathsf{Z} = 0$。

**証明** [(D.maxsub)](#d-maxsub) の第 1 式であり、両辺は定義により同一である。∎

<a id="t-maxsub_P"></a>
### 定理 $\mathsf{P}$ の最大添字 (T.maxsub_P)

**主張** 任意の $a\in\mathbb{N}$, $b,c\in\mathrm{Three}$ に対し
$$\mathrm{maxsub}\,\mathsf{P}(a,b,c) = \max\bigl(a,\ \max(\mathrm{maxsub}\,b,\ \mathrm{maxsub}\,c)\bigr).$$

**証明** [(D.maxsub)](#d-maxsub) の第 2 式であり、両辺は定義により同一である。∎

<a id="t-cmax_nil"></a>
### 定理 空列の $\mathrm{cmax}$ (T.cmax_nil)

**主張** $\mathrm{cmax}\,[] = 0$。

**証明** [(D.cmax)](#d-cmax) より $\mathrm{cmax}\,[] = \mathrm{foldr}\ \max\ 0\ [] = 0$ であり、
両辺は定義により同一である。∎

<a id="t-cmax_cons"></a>
### 定理 先頭付加の $\mathrm{cmax}$ (T.cmax_cons)

**主張** 任意の $x\in\mathbb{N}$、自然数列 $xs$ に対し
$\mathrm{cmax}(x\mathbin{::}xs) = \max\bigl(x,\ \mathrm{cmax}\,xs\bigr)$。

**証明** [(D.cmax)](#d-cmax) より
$\mathrm{foldr}\ \max\ 0\ (x\mathbin{::}xs) = \max(x,\ \mathrm{foldr}\ \max\ 0\ xs)$ であり、
両辺は定義により同一である。∎

<a id="t-cmax_ge"></a>
### 定理 $\mathrm{cmax}$ は上界 (T.cmax_ge)

**主張** $z\in xs$ ならば $z \le \mathrm{cmax}\,xs$。

**証明** $xs$ の構造に関する帰納法（$z$ は固定）。帰納法の述語は

$$\Phi(xs) :\equiv \forall z\in\mathbb{N},\ z\in xs \to z\le\mathrm{cmax}\,xs .$$

- 基底段 $xs=[]$：$z\in[]$ は偽であるから前件が偽であり、$\Phi([])$ が成り立つ。
- 帰納段 $xs = x\mathbin{::}xs'$：帰納法の仮定は $\Phi(xs')$、すなわち
  $\forall z,\ z\in xs' \to z\le\mathrm{cmax}\,xs'$ である。
  $z\in x\mathbin{::}xs'$ とすると、$z=x$ または $z\in xs'$ の 2 つの場合がある。
  - $z=x$ のとき：[(T.cmax_cons)](#t-cmax_cons) より
    $\mathrm{cmax}(x\mathbin{::}xs') = \max(x,\mathrm{cmax}\,xs') \ge x = z$。
  - $z\in xs'$ のとき：帰納法の仮定より $z\le\mathrm{cmax}\,xs'$。
    また $\max(x,\mathrm{cmax}\,xs') \ge \mathrm{cmax}\,xs'$ であるから、
    $z \le \mathrm{cmax}\,xs' \le \max(x,\mathrm{cmax}\,xs') = \mathrm{cmax}(x\mathbin{::}xs')$。

  いずれの場合も $z\le\mathrm{cmax}(x\mathbin{::}xs')$ であり、$\Phi(x\mathbin{::}xs')$ が成り立つ。∎

## 順序 $\prec$ と添字列の辞書式順序

<a id="d-slex"></a>
### 定義 添字列の辞書式広義順序 (D.slex)

$\mathrm{slex}\subseteq \mathbb{N}^{<\omega}\times\mathbb{N}^{<\omega}$ を第 1 引数に関する構造帰納で定める。

$$
\begin{aligned}
\mathrm{slex}([],\ ys) &:\iff \top,\\
\mathrm{slex}(x\mathbin{::}xs,\ []) &:\iff \bot,\\
\mathrm{slex}(x\mathbin{::}xs,\ y\mathbin{::}ys) &:\iff x<y \ \vee\ \bigl(x=y \wedge \mathrm{slex}(xs,ys)\bigr).
\end{aligned}
$$

空列は（スパインが尽きた状態として）すべての列以下であり、真の前部分列は小さい側になる。

<a id="t-slex_nil"></a>
### 定理 空列は最小 (T.slex_nil)

**主張** 任意の自然数列 $ys$ に対し $\mathrm{slex}([],ys)$。

**証明** [(D.slex)](#d-slex) の第 1 式により $\mathrm{slex}([],ys)$ は $\top$ と定義により等しい。∎

<a id="t-slex_cons_nil"></a>
### 定理 非空列は空列以下でない (T.slex_cons_nil)

**主張** 任意の $x\in\mathbb{N}$、自然数列 $xs$ に対し $\neg\,\mathrm{slex}(x\mathbin{::}xs,\ [])$。

**証明** [(D.slex)](#d-slex) の第 2 式により $\mathrm{slex}(x\mathbin{::}xs,[])$ は $\bot$ と定義により等しい。
よってその仮定からそのまま $\bot$ が得られる。∎

<a id="t-slex_cons_cons"></a>
### 定理 先頭付加どうしの比較 (T.slex_cons_cons)

**主張**
$$\mathrm{slex}(x\mathbin{::}xs,\ y\mathbin{::}ys)\ \iff\ x<y \ \vee\ \bigl(x=y \wedge \mathrm{slex}(xs,ys)\bigr).$$

**証明** [(D.slex)](#d-slex) の第 3 式そのものであり、両辺は定義により同一の命題である。∎

<a id="t-slex_refl"></a>
### 定理 反射性 (T.slex_refl)

**主張** 任意の自然数列 $xs$ に対し $\mathrm{slex}(xs,xs)$。

**証明** $xs$ の構造に関する帰納法。帰納法の述語は

$$\Phi(xs) :\equiv \mathrm{slex}(xs,xs).$$

- 基底段 $xs=[]$：[(T.slex_nil)](#t-slex_nil) より $\mathrm{slex}([],[])$、すなわち $\Phi([])$。
- 帰納段 $xs = x\mathbin{::}xs'$：帰納法の仮定は $\Phi(xs')$、すなわち $\mathrm{slex}(xs',xs')$ である。
  [(T.slex_cons_cons)](#t-slex_cons_cons) より $\mathrm{slex}(x\mathbin{::}xs',x\mathbin{::}xs')$ は
  $x<x \vee (x=x \wedge \mathrm{slex}(xs',xs'))$ と同値であり、第 2 選言は
  $x=x$（等号の反射性）と帰納法の仮定によりみたされる。よって $\Phi(x\mathbin{::}xs')$。∎

## スパインと行 0 が狭義増加する極大前部分列

Lean 側ではここに次の節見出しが置かれている：
「`slex` と正規形不変量から添字単調性へ」。この見出しの下に宣言はない。

以下では、$\mathrm{tr}\,M$ の最左引数スパインが、
「$M$ の先頭から行 0 の値が狭義に増加する極大な前部分列」の行 1 の値を読み出したものであることを示す。

<a id="t-getD_eq_getElem'"></a>
### 定理 $\mathrm{getD}$ と添字アクセスの一致 (T.getD_eq_getElem')

**主張** 任意の型 $\alpha$、リスト $l : \alpha^{<\omega}$、既定値 $d:\alpha$、$i\in\mathbb{N}$ について
$i<\lvert l\rvert$ ならば $l.\mathrm{getD}\,i\,d = l[i]$。

**証明** 標準ライブラリの `List.getD_eq_getElem?_getD` より
$l.\mathrm{getD}\,i\,d = (l[i]?).\mathrm{getD}\,d$ である。
$i<\lvert l\rvert$ のとき `List.getElem?_eq_getElem` より $l[i]? = \mathrm{some}\,l[i]$ であり、
$(\mathrm{some}\,a).\mathrm{getD}\,d = a$ は `Option.getD` の定義そのものであるから
$l.\mathrm{getD}\,i\,d = l[i]$。∎

<a id="d-incpref"></a>
### 定義 行 0 狭義増加前部分列 (D.incpref)

$\mathrm{inc}:\mathrm{PairSeq}\to\mathrm{PairSeq}$ を次で定める。

$$
\mathrm{inc}\,[] := [],\qquad
\mathrm{inc}\,[p] := [p],\qquad
\mathrm{inc}(p\mathbin{::}q\mathbin{::}L) := \begin{cases}
 p\mathbin{::}\mathrm{inc}(q\mathbin{::}L) & (\pi_0 p<\pi_0 q)\\
 [p] & (\neg(\pi_0 p<\pi_0 q)).
\end{cases}
$$

再帰呼び出しの引数 $q\mathbin{::}L$ は $p\mathbin{::}q\mathbin{::}L$ より長さが 1 小さいので、
この定義は長さに関する整礎再帰として整合的である。

**注（$\mathrm{inc}$ の再帰に伴う帰納法原理）.** ペア列の述語 $\Phi$ が

1. $\Phi([])$
2. 任意の対 $p$ について $\Phi([p])$
3. 任意の対 $p,q$、ペア列 $L$ について、$\pi_0 p<\pi_0 q$ かつ $\Phi(q\mathbin{::}L)$ ならば $\Phi(p\mathbin{::}q\mathbin{::}L)$
4. 任意の対 $p,q$、ペア列 $L$ について、$\neg(\pi_0 p<\pi_0 q)$ ならば $\Phi(p\mathbin{::}q\mathbin{::}L)$

をみたすなら、任意のペア列 $M$ について $\Phi(M)$ が成り立つ。これは $\lvert M\rvert$ に関する強帰納法である。
Lean ではこの原理は `incpref.induct` として自動生成される。
以下で「$\mathrm{inc}$ の再帰に沿う帰納法」と書いたときはこの原理を指す。

<a id="t-incpref_nil"></a>
### 定理 空列の $\mathrm{inc}$ (T.incpref_nil)

**主張** $\mathrm{inc}\,[] = []$。

**証明** [(D.incpref)](#d-incpref) の第 1 式であり、両辺は定義により同一である。∎

<a id="t-incpref_single"></a>
### 定理 単元列の $\mathrm{inc}$ (T.incpref_single)

**主張** 任意の対 $p$ に対し $\mathrm{inc}\,[p] = [p]$。

**証明** [(D.incpref)](#d-incpref) の第 2 式であり、両辺は定義により同一である。∎

<a id="t-incpref_cons_cons"></a>
### 定理 2 個以上の列の $\mathrm{inc}$ (T.incpref_cons_cons)

**主張** 任意の対 $p,q$、ペア列 $L$ に対し
$$\mathrm{inc}(p\mathbin{::}q\mathbin{::}L) = \begin{cases}
 p\mathbin{::}\mathrm{inc}(q\mathbin{::}L) & (\pi_0 p<\pi_0 q)\\
 [p] & (\neg(\pi_0 p<\pi_0 q)).\end{cases}$$

**証明** [(D.incpref)](#d-incpref) の第 3 式であり、両辺は定義により同一である。∎

<a id="t-takeWhile_fst_nest"></a>
### 定理 $\mathrm{tw}$ の入れ子 (T.takeWhile_fst_nest)

**主張** $a<b$ ならば、任意のペア列 $xs$ に対し
$\mathrm{tw}_b(\mathrm{tw}_a xs) = \mathrm{tw}_b\,xs$。

**証明** $a<b$ を固定し、$xs$ の構造に関する帰納法。帰納法の述語は

$$\Phi(xs) :\equiv \mathrm{tw}_b(\mathrm{tw}_a xs) = \mathrm{tw}_b\,xs .$$

- 基底段 $xs=[]$：$\mathrm{tw}_a[]=[]$、$\mathrm{tw}_b[]=[]$ であり、両辺とも $[]$。
- 帰納段 $xs = x\mathbin{::}xs'$：帰納法の仮定は $\Phi(xs')$ である。3 つの場合に分ける。
  - $a<\pi_0 x$ かつ $b<\pi_0 x$：`List.takeWhile` の定義より
    $\mathrm{tw}_a(x\mathbin{::}xs') = x\mathbin{::}\mathrm{tw}_a xs'$、
    さらに $\mathrm{tw}_b(x\mathbin{::}\mathrm{tw}_a xs') = x\mathbin{::}\mathrm{tw}_b(\mathrm{tw}_a xs')$。
    帰納法の仮定より $\mathrm{tw}_b(\mathrm{tw}_a xs') = \mathrm{tw}_b xs'$ だから左辺は
    $x\mathbin{::}\mathrm{tw}_b xs'$。右辺も $\mathrm{tw}_b(x\mathbin{::}xs') = x\mathbin{::}\mathrm{tw}_b xs'$。
  - $a<\pi_0 x$ かつ $\neg(b<\pi_0 x)$：左辺は
    $\mathrm{tw}_b(x\mathbin{::}\mathrm{tw}_a xs') = []$（先頭 $x$ が述語 $b<\pi_0(\cdot)$ をみたさない）。
    右辺も $\mathrm{tw}_b(x\mathbin{::}xs') = []$。
  - $\neg(a<\pi_0 x)$：このとき $\neg(b<\pi_0 x)$ である。実際 $b<\pi_0 x$ なら
    $a<b<\pi_0 x$ より $a<\pi_0 x$ となり仮定に反する。
    左辺は $\mathrm{tw}_a(x\mathbin{::}xs')=[]$ ゆえ $\mathrm{tw}_b[]=[]$、右辺も $\mathrm{tw}_b(x\mathbin{::}xs')=[]$。

  3 つの場合はすべてを尽くしており、いずれでも $\Phi(x\mathbin{::}xs')$ が成り立つ。∎

<a id="t-spine_translate_eq"></a>
### 定理 翻訳のスパイン (T.spine_translate_eq)

**主張** 任意のペア列 $M$ に対し
$$\mathrm{sp}(\mathrm{tr}\,M) = \mathrm{map}\ \pi_1\ (\mathrm{inc}\,M).$$

**証明** $\mathrm{inc}$ の再帰に沿う帰納法（[(D.incpref)](#d-incpref) の注）。帰納法の述語は

$$\Phi(M) :\equiv \mathrm{sp}(\mathrm{tr}\,M) = \mathrm{map}\ \pi_1\ (\mathrm{inc}\,M).$$

- **場合 1** $M=[]$：[(D.translate)](Mechanized.md#d-translate) より $\mathrm{tr}\,[]=\mathsf{Z}$、
  [(T.spine_Z)](#t-spine_Z) より左辺は $[]$。
  [(T.incpref_nil)](#t-incpref_nil) より $\mathrm{inc}\,[]=[]$ だから右辺も $[]$。
- **場合 2** $M=[p]$：[(D.translate)](Mechanized.md#d-translate) より
  $\mathrm{tr}[p] = \mathsf{P}(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p}[]),\ \mathrm{tr}(\mathrm{dw}_{\pi_0 p}[])) = \mathsf{P}(\pi_1 p,\mathsf{Z},\mathsf{Z})$。
  [(T.spine_P)](#t-spine_P) と [(T.spine_Z)](#t-spine_Z) より左辺は $[\pi_1 p]$。
  [(T.incpref_single)](#t-incpref_single) より $\mathrm{inc}[p]=[p]$ だから右辺も $[\pi_1 p]$。
- **場合 3** $M = p\mathbin{::}q\mathbin{::}L$ かつ $\pi_0 p<\pi_0 q$：帰納法の仮定は $\Phi(q\mathbin{::}L)$、すなわち
  $\mathrm{sp}(\mathrm{tr}(q\mathbin{::}L)) = \mathrm{map}\ \pi_1\ (\mathrm{inc}(q\mathbin{::}L))$ である。

  まず $\pi_0 p<\pi_0 q$ より、`List.takeWhile` の定義から
  $$\mathrm{tw}_{\pi_0 p}(q\mathbin{::}L) = q\mathbin{::}\mathrm{tw}_{\pi_0 p}L. \tag{tw}$$
  [(D.translate)](Mechanized.md#d-translate) より
  $$\mathrm{tr}(p\mathbin{::}q\mathbin{::}L)
   = \mathsf{P}\bigl(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p}(q\mathbin{::}L)),\
     \mathrm{tr}(\mathrm{dw}_{\pi_0 p}(q\mathbin{::}L))\bigr)$$
  であり、(tw) を代入して再び [(D.translate)](Mechanized.md#d-translate) を使うと
  $$\mathrm{tr}(q\mathbin{::}\mathrm{tw}_{\pi_0 p}L)
   = \mathsf{P}\bigl(\pi_1 q,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 q}(\mathrm{tw}_{\pi_0 p}L)),\
     \mathrm{tr}(\mathrm{dw}_{\pi_0 q}(\mathrm{tw}_{\pi_0 p}L))\bigr).$$
  ここで [(T.takeWhile_fst_nest)](#t-takeWhile_fst_nest)（$a:=\pi_0 p$, $b:=\pi_0 q$, $xs:=L$）より
  $\mathrm{tw}_{\pi_0 q}(\mathrm{tw}_{\pi_0 p}L) = \mathrm{tw}_{\pi_0 q}L$ である。
  したがって [(T.spine_P)](#t-spine_P) を 2 回使って
  $$\mathrm{sp}(\mathrm{tr}(p\mathbin{::}q\mathbin{::}L))
   = \pi_1 p \mathbin{::} \pi_1 q \mathbin{::} \mathrm{sp}\bigl(\mathrm{tr}(\mathrm{tw}_{\pi_0 q}L)\bigr).$$
  一方 [(D.translate)](Mechanized.md#d-translate) より
  $\mathrm{tr}(q\mathbin{::}L) = \mathsf{P}(\pi_1 q,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 q}L),\ \mathrm{tr}(\mathrm{dw}_{\pi_0 q}L))$
  だから、[(T.spine_P)](#t-spine_P) より
  $\mathrm{sp}(\mathrm{tr}(q\mathbin{::}L)) = \pi_1 q\mathbin{::}\mathrm{sp}(\mathrm{tr}(\mathrm{tw}_{\pi_0 q}L))$。
  よって
  $$\mathrm{sp}(\mathrm{tr}(p\mathbin{::}q\mathbin{::}L)) = \pi_1 p \mathbin{::} \mathrm{sp}(\mathrm{tr}(q\mathbin{::}L))
   = \pi_1 p \mathbin{::} \mathrm{map}\ \pi_1\ (\mathrm{inc}(q\mathbin{::}L))$$
  （最後の等号は帰納法の仮定）。
  他方 [(T.incpref_cons_cons)](#t-incpref_cons_cons) と $\pi_0 p<\pi_0 q$ より
  $\mathrm{inc}(p\mathbin{::}q\mathbin{::}L) = p\mathbin{::}\mathrm{inc}(q\mathbin{::}L)$ であり、
  $\mathrm{map}$ は先頭付加と交換するから
  $\mathrm{map}\ \pi_1\ (\mathrm{inc}(p\mathbin{::}q\mathbin{::}L)) = \pi_1 p\mathbin{::}\mathrm{map}\ \pi_1\ (\mathrm{inc}(q\mathbin{::}L))$。
  両辺が一致したので $\Phi(p\mathbin{::}q\mathbin{::}L)$。
- **場合 4** $M = p\mathbin{::}q\mathbin{::}L$ かつ $\neg(\pi_0 p<\pi_0 q)$：
  先頭 $q$ が述語 $\pi_0 p<\pi_0(\cdot)$ をみたさないので $\mathrm{tw}_{\pi_0 p}(q\mathbin{::}L)=[]$。
  よって [(D.translate)](Mechanized.md#d-translate) より
  $$\mathrm{tr}(p\mathbin{::}q\mathbin{::}L)
   = \mathsf{P}\bigl(\pi_1 p,\ \mathsf{Z},\ \mathrm{tr}(\mathrm{dw}_{\pi_0 p}(q\mathbin{::}L))\bigr)$$
  であり、[(T.spine_P)](#t-spine_P) と [(T.spine_Z)](#t-spine_Z) から左辺は $[\pi_1 p]$。
  [(T.incpref_cons_cons)](#t-incpref_cons_cons) より $\mathrm{inc}(p\mathbin{::}q\mathbin{::}L)=[p]$ だから
  右辺も $[\pi_1 p]$。

4 つの場合は $\mathrm{inc}$ の再帰の全分岐を尽くしている。∎

## 最大添字は行 1 の最大値

<a id="t-cmax_append"></a>
### 定理 連結の $\mathrm{cmax}$ (T.cmax_append)

**主張** 任意の自然数列 $xs,ys$ に対し
$\mathrm{cmax}(xs\mathbin{+\!\!+}ys) = \max(\mathrm{cmax}\,xs,\ \mathrm{cmax}\,ys)$。

**証明** $ys$ を固定し、$xs$ の構造に関する帰納法。帰納法の述語は

$$\Phi(xs) :\equiv \mathrm{cmax}(xs\mathbin{+\!\!+}ys) = \max(\mathrm{cmax}\,xs,\ \mathrm{cmax}\,ys).$$

- 基底段 $xs=[]$：左辺は $\mathrm{cmax}\,ys$。右辺は [(T.cmax_nil)](#t-cmax_nil) より
  $\max(0,\mathrm{cmax}\,ys) = \mathrm{cmax}\,ys$。
- 帰納段 $xs=x\mathbin{::}xs'$：帰納法の仮定は $\Phi(xs')$ である。
  $(x\mathbin{::}xs')\mathbin{+\!\!+}ys = x\mathbin{::}(xs'\mathbin{+\!\!+}ys)$ であるから、
  [(T.cmax_cons)](#t-cmax_cons) と帰納法の仮定より
  $$\mathrm{cmax}\bigl((x\mathbin{::}xs')\mathbin{+\!\!+}ys\bigr)
   = \max\bigl(x,\ \mathrm{cmax}(xs'\mathbin{+\!\!+}ys)\bigr)
   = \max\bigl(x,\ \max(\mathrm{cmax}\,xs',\ \mathrm{cmax}\,ys)\bigr).$$
  他方
  $$\max\bigl(\mathrm{cmax}(x\mathbin{::}xs'),\ \mathrm{cmax}\,ys\bigr)
   = \max\bigl(\max(x,\mathrm{cmax}\,xs'),\ \mathrm{cmax}\,ys\bigr).$$
  自然数の $\max$ は結合的である（$\max(u,\max(v,w))$ も $\max(\max(u,v),w)$ も
  $u,v,w$ のうち最大のものに等しい）から、両辺は一致し $\Phi(x\mathbin{::}xs')$ が成り立つ。∎

<a id="t-maxsub_translate"></a>
### 定理 翻訳の最大添字 (T.maxsub_translate)

**主張** 任意のペア列 $M$ に対し
$$\mathrm{maxsub}(\mathrm{tr}\,M) = \mathrm{cmax}\bigl(\mathrm{map}\ \pi_1\ M\bigr).$$

**証明** $\mathrm{tr}$ の再帰に沿う帰納法（[(D.translate)](Mechanized.md#d-translate) の注）。帰納法の述語は

$$\Phi(M) :\equiv \mathrm{maxsub}(\mathrm{tr}\,M) = \mathrm{cmax}(\mathrm{map}\ \pi_1\ M).$$

- 基底段 $M=[]$：$\mathrm{tr}\,[]=\mathsf{Z}$ と [(T.maxsub_Z)](#t-maxsub_Z) より左辺は $0$。
  $\mathrm{map}\,\pi_1\,[]=[]$ と [(T.cmax_nil)](#t-cmax_nil) より右辺も $0$。
- 帰納段 $M=p\mathbin{::}L$：帰納法の仮定は
  $\Phi(\mathrm{tw}_{\pi_0 p}L)$ と $\Phi(\mathrm{dw}_{\pi_0 p}L)$ である。

  まず標準ライブラリの `List.takeWhile_append_dropWhile` より
  $L = (\mathrm{tw}_{\pi_0 p}L)\mathbin{+\!\!+}(\mathrm{dw}_{\pi_0 p}L)$ であり、
  $\mathrm{map}$ は連結に分配するから
  $\mathrm{map}\,\pi_1\,L = \mathrm{map}\,\pi_1(\mathrm{tw}_{\pi_0 p}L)\mathbin{+\!\!+}\mathrm{map}\,\pi_1(\mathrm{dw}_{\pi_0 p}L)$。
  [(T.cmax_append)](#t-cmax_append) より
  $$\mathrm{cmax}(\mathrm{map}\,\pi_1\,L)
   = \max\Bigl(\mathrm{cmax}\bigl(\mathrm{map}\,\pi_1(\mathrm{tw}_{\pi_0 p}L)\bigr),\
     \mathrm{cmax}\bigl(\mathrm{map}\,\pi_1(\mathrm{dw}_{\pi_0 p}L)\bigr)\Bigr). \tag{key}$$

  一方 [(D.translate)](Mechanized.md#d-translate) と [(T.maxsub_P)](#t-maxsub_P) より
  $$\mathrm{maxsub}(\mathrm{tr}(p\mathbin{::}L))
   = \max\Bigl(\pi_1 p,\ \max\bigl(\mathrm{maxsub}(\mathrm{tr}(\mathrm{tw}_{\pi_0 p}L)),\
      \mathrm{maxsub}(\mathrm{tr}(\mathrm{dw}_{\pi_0 p}L))\bigr)\Bigr)$$
  であり、2 つの帰納法の仮定を代入すると
  $$= \max\Bigl(\pi_1 p,\ \max\bigl(\mathrm{cmax}(\mathrm{map}\,\pi_1(\mathrm{tw}_{\pi_0 p}L)),\
      \mathrm{cmax}(\mathrm{map}\,\pi_1(\mathrm{dw}_{\pi_0 p}L))\bigr)\Bigr)
    = \max\bigl(\pi_1 p,\ \mathrm{cmax}(\mathrm{map}\,\pi_1\,L)\bigr)$$
  （最後の等号は (key)）。
  [(T.cmax_cons)](#t-cmax_cons) よりこれは
  $\mathrm{cmax}(\pi_1 p\mathbin{::}\mathrm{map}\,\pi_1\,L) = \mathrm{cmax}(\mathrm{map}\,\pi_1(p\mathbin{::}L))$ に等しい。
  よって $\Phi(p\mathbin{::}L)$。∎

<a id="t-maxsub_eq_climb_iff"></a>
### 定理 $\mathrm{maxsub}=\mathrm{climb}$ のペア列による言い換え (T.maxsub_eq_climb_iff)

**主張** 任意のペア列 $M$ に対し
$$\mathrm{maxsub}(\mathrm{tr}\,M) = \mathrm{climb}(\mathrm{tr}\,M)
 \ \iff\ \mathrm{cmax}(\mathrm{map}\ \pi_1\ M) = \mathrm{cmax}\bigl(\mathrm{map}\ \pi_1\ (\mathrm{inc}\,M)\bigr).$$

**証明** [(T.maxsub_translate)](#t-maxsub_translate) より左辺の左項は $\mathrm{cmax}(\mathrm{map}\,\pi_1\,M)$ に等しい。
また [(D.climb)](#d-climb) より $\mathrm{climb}(\mathrm{tr}\,M) = \mathrm{cmax}(\mathrm{sp}(\mathrm{tr}\,M))$ であり、
[(T.spine_translate_eq)](#t-spine_translate_eq) より $\mathrm{sp}(\mathrm{tr}\,M) = \mathrm{map}\,\pi_1\,(\mathrm{inc}\,M)$
だから、左辺の右項は $\mathrm{cmax}(\mathrm{map}\,\pi_1\,(\mathrm{inc}\,M))$ に等しい。
2 つの書き換えにより両辺は同一の等式になる。∎

すなわち $\mathrm{maxsub}=\mathrm{climb}$ という項の側の条件は、
「$M$ に現れる行 1 の値の最大値が、行 0 が狭義増加する極大な前部分列 $\mathrm{inc}\,M$ の中ですでに達成される」
というペア列の側の条件と同値である。

## 悪い分岐の展開は $\mathrm{dropLast}\,M$ と行 1 の値を増やさないブロックの連結

Lean 側ではここに次の節見出しが置かれている：
「ペア列の正規形不変量とその保存」。この見出しの下に宣言はない。

以下で**悪い分岐**とは、[`Mechanized.md`](Mechanized.md) の
[(T.oper_bad_unfold)](Mechanized.md#t-oper_bad_unfold) が扱う場合、すなわち
$j_1:=\lvert M\rvert-1$、$i_1:=\mathrm{idx1}\,M\,j_1$ として
$$j_1\ne0 \ \wedge\ \neg\bigl(M_{0,j_1}=0\wedge M_{1,j_1}=0\bigr)\ \wedge\ \mathrm{hasParent}\,M\,i_1\,j_1$$
が成り立つ場合を指す（[(D.hasParent)](Def.md#d-hasParent)）。

<a id="t-oper_eq_dropLast_append"></a>
### 定理 展開は $\mathrm{dropLast}$ への追記 (T.oper_eq_dropLast_append)

**主張** $1<\lvert M\rvert$ かつ $1\le n$ ならば、あるペア列 $R$ が存在して
$$M[n] = \mathrm{dropLast}\,M \mathbin{+\!\!+} R
\qquad\text{かつ}\qquad
\mathrm{sndSet}\,R \subseteq \mathrm{sndSet}(\mathrm{dropLast}\,M)$$
（[(D.oper)](Def.md#d-oper), [(D.sndSet)](Mechanized.md#d-sndSet)）。

**証明** $1<\lvert M\rvert$ より $\neg(\lvert M\rvert\le 1)$ であるから、[(D.Pred)](Def.md#d-Pred) より
$\mathrm{Pred}\,M = \mathrm{dropLast}\,M$ である。$j_1 := \lvert M\rvert-1$ とおき、
[(D.oper)](Def.md#d-oper) の分岐で場合分けする（$1<\lvert M\rvert$ より $j_1\ne 0$）。

- **$M_{0,j_1}=0 \wedge M_{1,j_1}=0$ のとき。** $R:=[]$ とおく。
  [(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero) より
  $M[n]=\mathrm{Pred}\,M=\mathrm{dropLast}\,M = \mathrm{dropLast}\,M\mathbin{+\!\!+}[]$。
  [(T.sndSet_nil)](Mechanized.md#t-sndSet_nil) より $\mathrm{sndSet}\,[]=\emptyset$ であり、
  空集合は任意の集合の部分集合である。
- **$\neg(M_{0,j_1}=0\wedge M_{1,j_1}=0)$ かつ $\neg\,\mathrm{hasParent}\,M\,i_1\,j_1$ のとき**
  （$i_1:=\mathrm{idx1}\,M\,j_1$）。$R:=[]$ とおく。
  [(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent) より
  $M[n]=\mathrm{Pred}\,M=\mathrm{dropLast}\,M$ であり、あとは前項と同じである。
- **$\neg(M_{0,j_1}=0\wedge M_{1,j_1}=0)$ かつ $\mathrm{hasParent}\,M\,i_1\,j_1$ のとき。**
  [(T.oper_bad_blocks)](Mechanized.md#t-oper_bad_blocks) を適用して
  ペア列 $G,R_0$、自然数 $v_0,w_0,d_0$、対 $lp$ を取る。とくに条件 1, 2 より
  $$M = G\mathbin{+\!\!+}\bigl((v_0,w_0)\mathbin{::}R_0\bigr)\mathbin{+\!\!+}[lp],$$
  $$M[n] = G \mathbin{+\!\!+} \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}\,(\lambda p.\ (\pi_0 p+k\,d_0,\ \pi_1 p))\ ((v_0,w_0)\mathbin{::}R_0)\bigr)\ \mathrm{range}(n).$$

  まず条件 1 と `List.dropLast_concat`（末尾 1 個を付けてから落とすと元に戻る）より
  $$\mathrm{dropLast}\,M = G\mathbin{+\!\!+}\bigl((v_0,w_0)\mathbin{::}R_0\bigr). \tag{drop}$$

  次に $1\le n$ より $n=m+1$ と書ける。`List.range_eq_range'` より
  $\mathrm{range}(n) = \mathrm{range}'(0,n)$ であり、`List.range'_succ` より
  $\mathrm{range}'(0,m+1) = 0\mathbin{::}\mathrm{range}'(1,m)$、すなわち
  $$\mathrm{range}(n) = 0\mathbin{::}\mathrm{range}'(1,\ n-1). \tag{range}$$
  $k=0$ に対する被 $\mathrm{flatMap}$ 値は
  $\mathrm{map}\,(\lambda p.\ (\pi_0 p+0\cdot d_0,\ \pi_1 p))\ ((v_0,w_0)\mathbin{::}R_0) = (v_0,w_0)\mathbin{::}R_0$
  である（$\pi_0 p+0\cdot d_0=\pi_0 p$ であり、対 $p$ は $(\pi_0 p,\pi_1 p)$ に等しい）。
  よって (range) と $\mathrm{flatMap}$ の先頭分解より
  $$M[n] = G\mathbin{+\!\!+}\bigl((v_0,w_0)\mathbin{::}R_0\bigr)\mathbin{+\!\!+}R,\qquad
    R := \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}\,(\lambda p.\ (\pi_0 p+k\,d_0,\ \pi_1 p))\ ((v_0,w_0)\mathbin{::}R_0)\bigr)\ \mathrm{range}'(1,\ n-1)$$
  であり、連結の結合性と (drop) から $M[n] = \mathrm{dropLast}\,M\mathbin{+\!\!+}R$。

  最後に $\mathrm{sndSet}\,R\subseteq\mathrm{sndSet}(\mathrm{dropLast}\,M)$ を示す。
  $y\in\mathrm{sndSet}\,R$ とすると [(T.mem_sndSet)](Mechanized.md#t-mem_sndSet) より
  $p\in R$ で $\pi_1 p = y$ なるものが取れる。$R$ は $\mathrm{flatMap}$ であるから
  ある $k\in\mathrm{range}'(1,n-1)$ について
  $p\in\mathrm{map}\,(\lambda q.\ (\pi_0 q+k\,d_0,\ \pi_1 q))\ ((v_0,w_0)\mathbin{::}R_0)$、
  すなわちある $q\in(v_0,w_0)\mathbin{::}R_0$ について $p = (\pi_0 q+k\,d_0,\ \pi_1 q)$ である。
  このとき $y = \pi_1 p = \pi_1 q$ であり、(drop) より
  $q\in(v_0,w_0)\mathbin{::}R_0 \subseteq G\mathbin{+\!\!+}((v_0,w_0)\mathbin{::}R_0) = \mathrm{dropLast}\,M$。
  再び [(T.mem_sndSet)](Mechanized.md#t-mem_sndSet) より $y\in\mathrm{sndSet}(\mathrm{dropLast}\,M)$。

3 つの場合は [(D.oper)](Def.md#d-oper) の（$j_1\ne0$ の下での）全分岐を尽くしている。∎

## 対角列（基底段）

<a id="t-diagSeq_cons"></a>
### 定理 対角列の先頭分解 (T.diagSeq_cons)

**主張** $u\le v$ ならば $\Delta_u^v = (u,u)\mathbin{::}\Delta_{u+1}^{v}$
（[(D.diagSeq)](Def.md#d-diagSeq)）。

**証明** [(D.diagSeq)](Def.md#d-diagSeq) より
$\Delta_u^v = \mathrm{map}\ (\lambda j.\ (j,j))\ \mathrm{range}'(u,\ v+1-u)$ である。
$u\le v$ より $v+1-u\ge1$ であり、切り捨て減法について
$$v+1-u = \bigl(v+1-(u+1)\bigr)+1$$
が成り立つ（$u\le v$ ゆえ $v+1-u = v-u+1$、$v+1-(u+1)=v-u$）。
`List.range'_succ`（$\mathrm{range}'(a,m+1)=a\mathbin{::}\mathrm{range}'(a+1,m)$）より
$$\mathrm{range}'(u,\ v+1-u) = u\mathbin{::}\mathrm{range}'\bigl(u+1,\ v+1-(u+1)\bigr)$$
であり、$\mathrm{map}$ は先頭付加と交換するから
$$\Delta_u^v = (u,u)\mathbin{::}\mathrm{map}\ (\lambda j.\ (j,j))\ \mathrm{range}'\bigl(u+1,\ v+1-(u+1)\bigr)
 = (u,u)\mathbin{::}\Delta_{u+1}^v .$$
∎

<a id="t-fst_in_diagSeq"></a>
### 定理 対角列の行 0 の下界 (T.fst_in_diagSeq)

**主張** $q\in\Delta_a^b$ ならば $a\le\pi_0 q$。

**証明** [(D.diagSeq)](Def.md#d-diagSeq) より
$\Delta_a^b = \mathrm{map}\ (\lambda j.\ (j,j))\ \mathrm{range}'(a,\ b+1-a)$ であるから、
`List.mem_map` によりある $j\in\mathrm{range}'(a,b+1-a)$ について $q=(j,j)$ である。
`List.mem_range'` によりある $i<b+1-a$ について $j = a+i$ である。
よって $\pi_0 q = j = a+i \ge a$。∎

<a id="t-translate_diagSeq"></a>
### 定理 対角列の翻訳 (T.translate_diagSeq)

**主張** $u\le v$ ならば
$$\mathrm{tr}(\Delta_u^v) = \mathsf{P}\bigl(u,\ \mathrm{tr}(\Delta_{u+1}^v),\ \mathsf{Z}\bigr).$$

**証明** [(T.diagSeq_cons)](#t-diagSeq_cons) より $\Delta_u^v = (u,u)\mathbin{::}\Delta_{u+1}^v$ である。
$\Delta_{u+1}^v$ の任意の要素 $q$ について、[(T.fst_in_diagSeq)](#t-fst_in_diagSeq)（$a:=u+1$）より
$u+1\le\pi_0 q$、したがって $\pi_0 (u,u) = u < \pi_0 q$ である。
よって [(T.translate_single_tree)](Mechanized.md#t-translate_single_tree) を $p:=(u,u)$, $R:=\Delta_{u+1}^v$ に適用して
$$\mathrm{tr}\bigl((u,u)\mathbin{::}\Delta_{u+1}^v\bigr)
 = \mathsf{P}\bigl(\pi_1(u,u),\ \mathrm{tr}(\Delta_{u+1}^v),\ \mathsf{Z}\bigr)
 = \mathsf{P}\bigl(u,\ \mathrm{tr}(\Delta_{u+1}^v),\ \mathsf{Z}\bigr).$$
∎

## Cantor 標準形：先頭和の主要項は非増加

Lean 側ではここに次の 2 つの節見出しが置かれている：
「正規形不変量はすべての標準形で成り立つ」「$\mathrm{NF}=\mathrm{tr}[\mathrm{ST\_PS}]$ 上の降下の添字単調性」。
いずれの見出しの下にも宣言はない。

条件 $\mathrm{cnf}$ は、項を主要項の和 $p_{a_0}(b_0)+p_{a_1}(b_1)+\cdots$ と読んだとき、
各主要項 $p_{a_i}(b_i)$ が $\prec$ について非増加に並んでいることを要求する。

<a id="d-cnf"></a>
### 定義 Cantor 標準形条件 (D.cnf)

述語 $\mathrm{cnf}:\mathrm{Three}\to\mathrm{Prop}$ を項の構造帰納で定める。

$$
\begin{aligned}
\mathrm{cnf}\,\mathsf{Z} &:\iff \top,\\
\mathrm{cnf}\,\mathsf{P}(a,b,\mathsf{Z}) &:\iff \mathrm{cnf}\,b,\\
\mathrm{cnf}\,\mathsf{P}\bigl(a,b,\mathsf{P}(e,f,g)\bigr) &:\iff
 \mathrm{cnf}\,b \ \wedge\ \neg\bigl(\mathsf{P}(a,b,\mathsf{Z}) \prec \mathsf{P}(e,f,\mathsf{Z})\bigr)
 \ \wedge\ \mathrm{cnf}\,\mathsf{P}(e,f,g).
\end{aligned}
$$

再帰呼び出しの引数 $b$、$\mathsf{P}(e,f,g)$ はいずれも被定義項の真部分項であるから、
この定義は構造帰納として整合的である。

第 3 式の中央の条件は、記法の節の注により
$\mathsf{P}(e,f,\mathsf{Z}) \preceq \mathsf{P}(a,b,\mathsf{Z})$ と同値である。
すなわち「先頭の主要項 $p_a(b)$ は、次の主要項 $p_e(f)$ 以上である」という要求である。

<a id="t-cnf_Z"></a>
### 定理 $\mathsf{Z}$ は $\mathrm{cnf}$ (T.cnf_Z)

**主張** $\mathrm{cnf}\,\mathsf{Z}$。

**証明** [(D.cnf)](#d-cnf) の第 1 式により $\mathrm{cnf}\,\mathsf{Z}$ は $\top$ と定義により等しい。∎

<a id="t-cnf_P_Z"></a>
### 定理 後続和が $\mathsf{Z}$ の場合 (T.cnf_P_Z)

**主張** $\mathrm{cnf}\,\mathsf{P}(a,b,\mathsf{Z}) \iff \mathrm{cnf}\,b$。

**証明** [(D.cnf)](#d-cnf) の第 2 式そのものであり、両辺は定義により同一の命題である。∎

<a id="t-cnf_P_P"></a>
### 定理 後続和が主要項の場合 (T.cnf_P_P)

**主張**
$$\mathrm{cnf}\,\mathsf{P}\bigl(a,b,\mathsf{P}(e,f,g)\bigr) \iff
 \mathrm{cnf}\,b \ \wedge\ \neg\bigl(\mathsf{P}(a,b,\mathsf{Z})\prec\mathsf{P}(e,f,\mathsf{Z})\bigr)
 \ \wedge\ \mathrm{cnf}\,\mathsf{P}(e,f,g).$$

**証明** [(D.cnf)](#d-cnf) の第 3 式そのものであり、両辺は定義により同一の命題である。∎

<a id="t-cnf_translate_diagSeq_aux"></a>
### 定理 対角列の $\mathrm{cnf}$（一般の始点） (T.cnf_translate_diagSeq_aux)

**主張** 任意の $n,u\in\mathbb{N}$ に対し $\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_u^{u+n})\bigr)$。

**証明** $n$ に関する自然数の帰納法（$u$ は全称量化したまま動かす）。帰納法の述語は

$$\Phi(n) :\equiv \forall u\in\mathbb{N},\ \mathrm{cnf}\bigl(\mathrm{tr}(\Delta_u^{u+n})\bigr).$$

- 基底段 $n=0$：$u+0=u$ である。$u\le u$ だから
  [(T.translate_diagSeq)](#t-translate_diagSeq) より
  $\mathrm{tr}(\Delta_u^u) = \mathsf{P}(u,\ \mathrm{tr}(\Delta_{u+1}^{u}),\ \mathsf{Z})$。
  ここで [(D.diagSeq)](Def.md#d-diagSeq) より
  $\Delta_{u+1}^{u} = \mathrm{map}\ (\lambda j.\ (j,j))\ \mathrm{range}'(u+1,\ u+1-(u+1)) = \mathrm{map}\ (\lambda j.\ (j,j))\ \mathrm{range}'(u+1,0) = []$
  であり、[(D.translate)](Mechanized.md#d-translate) より $\mathrm{tr}\,[]=\mathsf{Z}$。
  よって $\mathrm{tr}(\Delta_u^u) = \mathsf{P}(u,\mathsf{Z},\mathsf{Z})$ であり、
  [(T.cnf_P_Z)](#t-cnf_P_Z) と [(T.cnf_Z)](#t-cnf_Z) より $\mathrm{cnf}\,\mathsf{P}(u,\mathsf{Z},\mathsf{Z})$。
  $u$ は任意だったので $\Phi(0)$。
- 帰納段 $n+1$：帰納法の仮定は $\Phi(n)$、すなわち
  $\forall u,\ \mathrm{cnf}(\mathrm{tr}(\Delta_u^{u+n}))$ である。$u$ を任意に取る。
  $u\le u+(n+1)$ であるから [(T.translate_diagSeq)](#t-translate_diagSeq) より
  $$\mathrm{tr}\bigl(\Delta_u^{u+(n+1)}\bigr)
   = \mathsf{P}\bigl(u,\ \mathrm{tr}(\Delta_{u+1}^{u+(n+1)}),\ \mathsf{Z}\bigr).$$
  $u+(n+1) = (u+1)+n$ であるから $\Delta_{u+1}^{u+(n+1)} = \Delta_{u+1}^{(u+1)+n}$ であり、
  帰納法の仮定 $\Phi(n)$ を $u:=u+1$ に適用して
  $\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_{u+1}^{(u+1)+n})\bigr)$ を得る。
  [(T.cnf_P_Z)](#t-cnf_P_Z) より $\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_u^{u+(n+1)})\bigr)$。
  $u$ は任意だったので $\Phi(n+1)$。∎

<a id="t-cnf_diag"></a>
### 定理 対角列の $\mathrm{cnf}$ (T.cnf_diag)

**主張** 任意の $v\in\mathbb{N}$ に対し $\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_0^v)\bigr)$。

**証明** [(T.cnf_translate_diagSeq_aux)](#t-cnf_translate_diagSeq_aux) を $n:=v$, $u:=0$ に適用すると
$\mathrm{cnf}(\mathrm{tr}(\Delta_0^{0+v}))$ を得る。$0+v=v$ である。∎

<a id="t-cnf_snoc"></a>
### 定理 末尾対の削除は $\mathrm{cnf}$ を保つ (T.cnf_snoc)

**主張** ペア列 $D$ と対 $m$ について
$\mathrm{cnf}\bigl(\mathrm{tr}(D\mathbin{+\!\!+}[m])\bigr)$ ならば $\mathrm{cnf}(\mathrm{tr}\,D)$。

**証明** $m$ を固定し、$\mathrm{tr}$ の再帰に沿う帰納法（[(D.translate)](Mechanized.md#d-translate) の注）。
帰納法の述語は

$$\Phi(D) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(D\mathbin{+\!\!+}[m])\bigr) \to \mathrm{cnf}(\mathrm{tr}\,D).$$

- 基底段 $D=[]$：$\mathrm{tr}\,[]=\mathsf{Z}$ であり、[(T.cnf_Z)](#t-cnf_Z) より結論 $\mathrm{cnf}\,\mathsf{Z}$ は
  仮定なしに成り立つ。よって $\Phi([])$。
- 帰納段 $D = p\mathbin{::}L$：帰納法の仮定は
  $\Phi(\mathrm{tw}_{\pi_0 p}L)$ と $\Phi(\mathrm{dw}_{\pi_0 p}L)$ である。
  $h : \mathrm{cnf}\bigl(\mathrm{tr}((p\mathbin{::}L)\mathbin{+\!\!+}[m])\bigr)$ を仮定する。
  $(p\mathbin{::}L)\mathbin{+\!\!+}[m] = p\mathbin{::}(L\mathbin{+\!\!+}[m])$ に注意して 3 つの場合に分ける。

  **場合 A1** $\forall x\in L,\ \pi_0 p<\pi_0 x$ かつ $\pi_0 p<\pi_0 m$。
  `List.takeWhile_eq_self_iff` より $\mathrm{tw}_{\pi_0 p}L=L$、
  `List.dropWhile_eq_nil_iff` より $\mathrm{dw}_{\pi_0 p}L=[]$ であるから
  [(D.translate)](Mechanized.md#d-translate) より
  $$\mathrm{tr}(p\mathbin{::}L) = \mathsf{P}\bigl(\pi_1 p,\ \mathrm{tr}\,L,\ \mathsf{Z}\bigr). \tag{A1-1}$$
  また $L\mathbin{+\!\!+}[m]$ の全要素 $x$ が $\pi_0 p<\pi_0 x$ をみたす（$x\in L$ なら仮定、$x=m$ なら $\pi_0 p<\pi_0 m$）ので、
  同様に $\mathrm{tw}_{\pi_0 p}(L\mathbin{+\!\!+}[m]) = L\mathbin{+\!\!+}[m]$、$\mathrm{dw}_{\pi_0 p}(L\mathbin{+\!\!+}[m])=[]$ であり
  $$\mathrm{tr}\bigl(p\mathbin{::}(L\mathbin{+\!\!+}[m])\bigr)
   = \mathsf{P}\bigl(\pi_1 p,\ \mathrm{tr}(L\mathbin{+\!\!+}[m]),\ \mathsf{Z}\bigr).$$
  $h$ に [(T.cnf_P_Z)](#t-cnf_P_Z) を適用して $\mathrm{cnf}\bigl(\mathrm{tr}(L\mathbin{+\!\!+}[m])\bigr)$ を得る。
  帰納法の仮定 $\Phi(\mathrm{tw}_{\pi_0 p}L)$ は $\mathrm{tw}_{\pi_0 p}L=L$ により
  $\mathrm{cnf}(\mathrm{tr}(L\mathbin{+\!\!+}[m]))\to\mathrm{cnf}(\mathrm{tr}\,L)$ と同じ命題であるから、
  $\mathrm{cnf}(\mathrm{tr}\,L)$ を得る。(A1-1) と [(T.cnf_P_Z)](#t-cnf_P_Z) より $\mathrm{cnf}(\mathrm{tr}(p\mathbin{::}L))$。

  **場合 A2** $\forall x\in L,\ \pi_0 p<\pi_0 x$ かつ $\neg(\pi_0 p<\pi_0 m)$。
  (A1-1) は場合 A1 と同じ理由で成り立つ。
  [(T.takeWhile_append_all)](Mechanized.md#t-takeWhile_append_all)（$xs:=L$, $ys:=[m]$）より
  $\mathrm{tw}_{\pi_0 p}(L\mathbin{+\!\!+}[m]) = L\mathbin{+\!\!+}\mathrm{tw}_{\pi_0 p}[m] = L\mathbin{+\!\!+}[] = L$
  （$\neg(\pi_0 p<\pi_0 m)$ ゆえ $\mathrm{tw}_{\pi_0 p}[m]=[]$）、
  [(T.dropWhile_append_all)](Mechanized.md#t-dropWhile_append_all) より
  $\mathrm{dw}_{\pi_0 p}(L\mathbin{+\!\!+}[m]) = \mathrm{dw}_{\pi_0 p}[m] = [m]$。よって
  $$\mathrm{tr}\bigl(p\mathbin{::}(L\mathbin{+\!\!+}[m])\bigr)
   = \mathsf{P}\bigl(\pi_1 p,\ \mathrm{tr}\,L,\ \mathrm{tr}[m]\bigr),\qquad
    \mathrm{tr}[m] = \mathsf{P}(\pi_1 m,\mathsf{Z},\mathsf{Z})$$
  （後者は [(D.translate)](Mechanized.md#d-translate) を $[m]=m\mathbin{::}[]$ に適用したもの）。
  $h$ に [(T.cnf_P_P)](#t-cnf_P_P) を適用するとその第 1 成分が $\mathrm{cnf}(\mathrm{tr}\,L)$ である。
  (A1-1) と [(T.cnf_P_Z)](#t-cnf_P_Z) より $\mathrm{cnf}(\mathrm{tr}(p\mathbin{::}L))$。

  **場合 B** $\neg(\forall x\in L,\ \pi_0 p<\pi_0 x)$。
  $x\in L$ で $\neg(\pi_0 p<\pi_0 x)$ なるものを取る。
  [(T.takeWhile_append_not)](Mechanized.md#t-takeWhile_append_not) と
  [(T.dropWhile_append_not)](Mechanized.md#t-dropWhile_append_not) より
  $$\mathrm{tw}_{\pi_0 p}(L\mathbin{+\!\!+}[m]) = \mathrm{tw}_{\pi_0 p}L,\qquad
    \mathrm{dw}_{\pi_0 p}(L\mathbin{+\!\!+}[m]) = (\mathrm{dw}_{\pi_0 p}L)\mathbin{+\!\!+}[m].$$
  また $\mathrm{dw}_{\pi_0 p}L\ne[]$ である。実際 $\mathrm{dw}_{\pi_0 p}L=[]$ なら
  `List.dropWhile_eq_nil_iff` より $L$ の全要素が述語 $\pi_0 p<\pi_0(\cdot)$ をみたし、
  $x$ に適用して $\pi_0 p<\pi_0 x$ となり仮定に反する。
  そこで $\mathrm{dw}_{\pi_0 p}L = q\mathbin{::}L_2$ と書く。[(D.translate)](Mechanized.md#d-translate) より
  $$\mathrm{tr}(\mathrm{dw}_{\pi_0 p}L)
   = \mathsf{P}\bigl(\pi_1 q,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 q}L_2),\ \mathrm{tr}(\mathrm{dw}_{\pi_0 q}L_2)\bigr), \tag{td}$$
  $$\mathrm{tr}\bigl((\mathrm{dw}_{\pi_0 p}L)\mathbin{+\!\!+}[m]\bigr)
   = \mathsf{P}\bigl(\pi_1 q,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 q}(L_2\mathbin{+\!\!+}[m])),\
      \mathrm{tr}(\mathrm{dw}_{\pi_0 q}(L_2\mathbin{+\!\!+}[m]))\bigr) \tag{td'}$$
  （後者は $(q\mathbin{::}L_2)\mathbin{+\!\!+}[m] = q\mathbin{::}(L_2\mathbin{+\!\!+}[m])$ による）。
  さらに [(D.translate)](Mechanized.md#d-translate) より
  $$\mathrm{tr}\bigl(p\mathbin{::}(L\mathbin{+\!\!+}[m])\bigr)
   = \mathsf{P}\Bigl(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p}L),\
      \mathrm{tr}\bigl((\mathrm{dw}_{\pi_0 p}L)\mathbin{+\!\!+}[m]\bigr)\Bigr)$$
  であり、(td') を代入した形に [(T.cnf_P_P)](#t-cnf_P_P) を $h$ に適用して次の 3 つを得る。

  - $c_b : \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{tw}_{\pi_0 p}L)\bigr)$
  - $s' : \neg\Bigl(\mathsf{P}\bigl(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p}L),\ \mathsf{Z}\bigr) \prec \mathsf{P}\bigl(\pi_1 q,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 q}(L_2\mathbin{+\!\!+}[m])),\ \mathsf{Z}\bigr)\Bigr)$
  - $c' : \mathrm{cnf}\bigl(\mathrm{tr}((\mathrm{dw}_{\pi_0 p}L)\mathbin{+\!\!+}[m])\bigr)$（(td') により書き換えたもの）

  $c'$ に帰納法の仮定 $\Phi(\mathrm{dw}_{\pi_0 p}L)$ を適用して
  $c_{dw} : \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dw}_{\pi_0 p}L)\bigr)$ を得る。

  次に [(T.translate_takeWhile_snoc_le)](Mechanized.md#t-translate_takeWhile_snoc_le)（$a:=\pi_0 q$, $C:=L_2$）より
  $\mathrm{tr}(\mathrm{tw}_{\pi_0 q}L_2) \preceq \mathrm{tr}(\mathrm{tw}_{\pi_0 q}(L_2\mathbin{+\!\!+}[m]))$。
  これから
  $$\mathsf{P}\bigl(\pi_1 q,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 q}L_2),\ \mathsf{Z}\bigr)
   \preceq \mathsf{P}\bigl(\pi_1 q,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 q}(L_2\mathbin{+\!\!+}[m])),\ \mathsf{Z}\bigr)$$
  が従う。実際 [(D.ole)](Mechanized.md#d-ole) により前者が狭義 $\prec$ なら
  [(T.olt_P_b)](Mechanized.md#t-olt_P_b) で狭義の $\prec$ が、等号なら両辺が同一である。
  そこで
  $$s : \neg\Bigl(\mathsf{P}\bigl(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p}L),\ \mathsf{Z}\bigr)
   \prec \mathsf{P}\bigl(\pi_1 q,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 q}L_2),\ \mathsf{Z}\bigr)\Bigr)$$
  が成り立つ。実際、左の $\prec$ が成り立つとすると、直前の $\preceq$ と
  [(T.olt_ole_trans)](Mechanized.md#t-olt_ole_trans) により $s'$ の否定する $\prec$ が得られ、矛盾する。

  最後に [(D.translate)](Mechanized.md#d-translate) より
  $\mathrm{tr}(p\mathbin{::}L) = \mathsf{P}\bigl(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p}L),\ \mathrm{tr}(\mathrm{dw}_{\pi_0 p}L)\bigr)$
  であり、(td) によりその第 3 引数は $\mathsf{P}(\pi_1 q,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 q}L_2),\ \mathrm{tr}(\mathrm{dw}_{\pi_0 q}L_2))$ の形である。
  [(T.cnf_P_P)](#t-cnf_P_P) に $c_b$, $s$, $c_{dw}$ を与えて $\mathrm{cnf}(\mathrm{tr}(p\mathbin{::}L))$ を得る。

  3 つの場合はすべてを尽くしており、いずれでも $\Phi(p\mathbin{::}L)$ が示された。∎

<a id="t-cnf_dropLast"></a>
### 定理 $\mathrm{dropLast}$ は $\mathrm{cnf}$ を保つ (T.cnf_dropLast)

**主張** $C\ne[]$ かつ $\mathrm{cnf}(\mathrm{tr}\,C)$ ならば $\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,C)\bigr)$。

**証明** $C\ne[]$ より標準ライブラリの `List.dropLast_append_getLast` により
$C = \mathrm{dropLast}\,C \mathbin{+\!\!+} [\,\mathrm{getLast}\,C\,]$ である。
[(T.cnf_snoc)](#t-cnf_snoc) を $D:=\mathrm{dropLast}\,C$, $m:=\mathrm{getLast}\,C$ に適用すればよい。∎

<a id="t-cnf_take"></a>
### 定理 前部分列は $\mathrm{cnf}$ (T.cnf_take)

**主張** $\mathrm{cnf}(\mathrm{tr}\,M)$ ならば、任意の $k\in\mathbb{N}$ に対し
$\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}\,k\,M)\bigr)$。

**証明** $M$ と仮定 $\mathrm{cnf}(\mathrm{tr}\,M)$ を固定し、次の補助命題を $d$ に関する自然数の帰納法で示す。

$$\Psi(d) :\equiv \forall k\in\mathbb{N},\ \lvert M\rvert-k = d \to \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}\,k\,M)\bigr)$$

（減法は切り捨て減法）。これが示されれば、与えられた $k$ に対し $d:=\lvert M\rvert-k$ として
$\Psi(\lvert M\rvert-k)$ を適用すれば主張が得られる。

- 基底段 $d=0$：$k$ を取り $\lvert M\rvert-k=0$ とする。切り捨て減法より $\lvert M\rvert\le k$ であり、
  `List.take_of_length_le` より $\mathrm{take}\,k\,M = M$。よって結論は仮定 $\mathrm{cnf}(\mathrm{tr}\,M)$ そのものである。
- 帰納段 $d+1$：帰納法の仮定は $\Psi(d)$ である。$k$ を取り $\lvert M\rvert-k=d+1$ とする。
  切り捨て減法より $\lvert M\rvert-k\ge1$、すなわち $k<\lvert M\rvert$ である。
  また $\lvert M\rvert-(k+1) = (\lvert M\rvert-k)-1 = d$ であるから、帰納法の仮定 $\Psi(d)$ を $k+1$ に適用して
  $$\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}\,(k+1)\,M)\bigr)$$
  を得る。ここで $k<\lvert M\rvert$ すなわち $k+1\le\lvert M\rvert$ より
  $\lvert\mathrm{take}\,(k+1)\,M\rvert = \min(k+1,\lvert M\rvert) = k+1 > 0$ であるから
  $\mathrm{take}\,(k+1)\,M \ne []$。
  さらに `List.dropLast_eq_take`（$l$ の $\mathrm{dropLast}$ は $\mathrm{take}\,(\lvert l\rvert-1)\,l$）と
  `List.take_take`（$\mathrm{take}\,m\,(\mathrm{take}\,n\,l) = \mathrm{take}\,(\min(m,n))\,l$）より
  $$\mathrm{dropLast}\bigl(\mathrm{take}\,(k+1)\,M\bigr)
   = \mathrm{take}\,\bigl((k+1)-1\bigr)\,\bigl(\mathrm{take}\,(k+1)\,M\bigr)
   = \mathrm{take}\,\bigl(\min(k,\ k+1)\bigr)\,M = \mathrm{take}\,k\,M$$
  （$\min(k,k+1)=k$）。よって [(T.cnf_dropLast)](#t-cnf_dropLast) を
  $C:=\mathrm{take}\,(k+1)\,M$ に適用して $\mathrm{cnf}(\mathrm{tr}(\mathrm{take}\,k\,M))$ を得る。∎

<a id="t-cnf_replicate_block"></a>
### 定理 完全コピーの $\mathrm{cnf}$ (T.cnf_replicate_block)

**主張** $v_0,w_0\in\mathbb{N}$、ペア列 $R$ が
$\forall x\in R,\ v_0<\pi_0 x$ と $\mathrm{cnf}(\mathrm{tr}\,R)$ をみたすならば、任意の $n\in\mathbb{N}$ に対し
$$\mathrm{cnf}\Bigl(\mathrm{tr}\bigl(\mathrm{flatten}\ \mathrm{replicate}(n,\ (v_0,w_0)\mathbin{::}R)\bigr)\Bigr).$$

**証明** $B := (v_0,w_0)\mathbin{::}R$ とおき、$n$ に関する自然数の帰納法。帰納法の述語は

$$\Phi(n) :\equiv \mathrm{cnf}\Bigl(\mathrm{tr}\bigl(\mathrm{flatten}\ \mathrm{replicate}(n,B)\bigr)\Bigr).$$

補助的に、任意の $m\in\mathbb{N}$ について次が成り立つことに注意する。

$$T_m := \mathrm{flatten}\ \mathrm{replicate}(m,B),\qquad
  T_{m+1} = B\mathbin{+\!\!+}T_m \tag{rep}$$

（`List.replicate_succ` と `List.flatten_cons`）。さらに

$$T_m = [] \ \vee\ \neg\bigl(v_0 < \pi_0(\mathrm{headI}\,T_m)\bigr) \tag{cond}$$

が成り立つ。実際 $m=0$ なら $T_0 = []$（左の選言）。$m=m'+1$ なら (rep) より
$T_m = B\mathbin{+\!\!+}T_{m'}$ であり $B$ の先頭は $(v_0,w_0)$ だから
$\mathrm{headI}\,T_m = (v_0,w_0)$、$\pi_0(\mathrm{headI}\,T_m)=v_0$ であり
$\neg(v_0<v_0)$（$<$ の非反射性）。

- 基底段 $n=0$：$T_0=[]$ であり $\mathrm{tr}\,[]=\mathsf{Z}$、[(T.cnf_Z)](#t-cnf_Z) より $\Phi(0)$。
- 帰納段 $n=m+1$：帰納法の仮定は $\Phi(m)$、すなわち $\mathrm{cnf}(\mathrm{tr}\,T_m)$ である。
  (rep) と (cond) により [(T.translate_block_append)](Mechanized.md#t-translate_block_append)
  （仮定 $\forall x\in R,\ v_0<\pi_0 x$ と (cond) を用いる）を $T:=T_m$ に適用して
  $$\mathrm{tr}\,T_{m+1} = \mathrm{tr}(B\mathbin{+\!\!+}T_m)
   = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T_m\bigr). \tag{tb}$$
  $m$ の形で分ける。
  - $m=0$：$T_0=[]$、$\mathrm{tr}\,T_0=\mathsf{Z}$ であるから (tb) より
    $\mathrm{tr}\,T_1 = \mathsf{P}(w_0,\ \mathrm{tr}\,R,\ \mathsf{Z})$。
    仮定 $\mathrm{cnf}(\mathrm{tr}\,R)$ と [(T.cnf_P_Z)](#t-cnf_P_Z) より $\Phi(1)$。
  - $m=m'+1$：(rep) と (cond)（$m$ を $m'$ として）より、同じく
    [(T.translate_block_append)](Mechanized.md#t-translate_block_append) を $T:=T_{m'}$ に適用して
    $$\mathrm{tr}\,T_m = \mathrm{tr}(B\mathbin{+\!\!+}T_{m'}) = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T_{m'}\bigr). \tag{tT}$$
    よって (tb) と (tT) より
    $$\mathrm{tr}\,T_{m+1} = \mathsf{P}\Bigl(w_0,\ \mathrm{tr}\,R,\ \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T_{m'}\bigr)\Bigr).$$
    [(T.cnf_P_P)](#t-cnf_P_P) を用いるために 3 条件を確かめる。
    第 1 条件 $\mathrm{cnf}(\mathrm{tr}\,R)$ は仮定。
    第 2 条件は $\neg\bigl(\mathsf{P}(w_0,\mathrm{tr}\,R,\mathsf{Z}) \prec \mathsf{P}(w_0,\mathrm{tr}\,R,\mathsf{Z})\bigr)$ であり、
    両辺が同一の項だから [(T.olt_irrefl)](Mechanized.md#t-olt_irrefl) による。
    第 3 条件は $\mathrm{cnf}\bigl(\mathsf{P}(w_0,\mathrm{tr}\,R,\mathrm{tr}\,T_{m'})\bigr)$ であり、
    (tT) によりこれは $\mathrm{cnf}(\mathrm{tr}\,T_m)$、すなわち帰納法の仮定 $\Phi(m)$ である。
    よって $\Phi(m+1)$。∎

<a id="t-cnf_ctx_cong"></a>
### 定理 $\mathrm{cnf}$ の文脈合同 (T.cnf_ctx_cong)

**主張** 対 $z_1,z_2$、ペア列 $T_1,T_2$ が次の 5 条件をみたすとする。

- $cZ_1 : \mathrm{cnf}\bigl(\mathrm{tr}(z_1\mathbin{::}T_1)\bigr)$
- $\text{decr} : \mathrm{tr}(z_1\mathbin{::}T_1) \prec \mathrm{tr}(z_2\mathbin{::}T_2)$
- $\text{root} : \pi_0 z_1 = \pi_0 z_2$
- $\text{leadle} : \exists a_1,b_1,c_1,a_2,b_2,c_2,\ \mathrm{tr}(z_1\mathbin{::}T_1)=\mathsf{P}(a_1,b_1,c_1)\ \wedge\ \mathrm{tr}(z_2\mathbin{::}T_2)=\mathsf{P}(a_2,b_2,c_2)\ \wedge\ \mathsf{P}(a_1,b_1,\mathsf{Z})\preceq\mathsf{P}(a_2,b_2,\mathsf{Z})$
- $r_1 : \forall x\in T_1,\ \pi_0 z_1\le\pi_0 x$、$r_2 : \forall x\in T_2,\ \pi_0 z_2\le\pi_0 x$

このとき、任意のペア列 $G$ について
$$\mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}z_2\mathbin{::}T_2)\bigr)
 \ \Longrightarrow\ \mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}z_1\mathbin{::}T_1)\bigr).$$

**証明** $z_1,z_2,T_1,T_2$ と 5 条件を固定する。leadle の証人を
$a_1,b_1,c_1,a_2,b_2,c_2$ とし、その 3 つの成分を
$$lZ_1 : \mathrm{tr}(z_1\mathbin{::}T_1)=\mathsf{P}(a_1,b_1,c_1),\quad
  lZ_2 : \mathrm{tr}(z_2\mathbin{::}T_2)=\mathsf{P}(a_2,b_2,c_2),\quad
  lle : \mathsf{P}(a_1,b_1,\mathsf{Z})\preceq\mathsf{P}(a_2,b_2,\mathsf{Z})$$
と書く。$\lvert G\rvert$ に関する強帰納法を行う。帰納法の述語は

$$\Phi(G) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}z_2\mathbin{::}T_2)\bigr)
 \to \mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}z_1\mathbin{::}T_1)\bigr)$$

であり、$\lvert G'\rvert<\lvert G\rvert$ なるすべての $G'$ について $\Phi(G')$ を仮定して $\Phi(G)$ を示す。
$G$ の形で分ける。

**$G=[]$ のとき。** $[]\mathbin{+\!\!+}z_i\mathbin{::}T_i = z_i\mathbin{::}T_i$ であるから、
結論は $cZ_1$ そのものであり、仮定を使わずに成り立つ。

**$G=g\mathbin{::}G'$ のとき。** $hG_2 : \mathrm{cnf}(\mathrm{tr}(G\mathbin{+\!\!+}z_2\mathbin{::}T_2))$ を仮定し、
$g\mathbin{::}G'\mathbin{+\!\!+}z_i\mathbin{::}T_i = g\mathbin{::}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i)$ に注意して 3 つの場合に分ける。

- **場合 (b)** $\forall x\in G',\ \pi_0 g<\pi_0 x$ かつ $\pi_0 g<\pi_0 z_1$。
  このとき $G'\mathbin{+\!\!+}z_1\mathbin{::}T_1$ の全要素 $x$ が $\pi_0 g<\pi_0 x$ をみたす。実際、
  $x\in G'$ なら仮定、$x=z_1$ なら $\pi_0 g<\pi_0 z_1$、$x\in T_1$ なら $r_1$ から
  $\pi_0 g<\pi_0 z_1\le\pi_0 x$ である。
  root より $\pi_0 z_2 = \pi_0 z_1 > \pi_0 g$ であるから、同じ論法（$r_2$ を用いる）で
  $G'\mathbin{+\!\!+}z_2\mathbin{::}T_2$ の全要素 $x$ も $\pi_0 g<\pi_0 x$ をみたす。
  よって [(T.translate_single_tree)](Mechanized.md#t-translate_single_tree) を $p:=g$ として 2 回用いて（$i=1,2$）
  $$\mathrm{tr}\bigl(g\mathbin{::}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i)\bigr)
   = \mathsf{P}\bigl(\pi_1 g,\ \mathrm{tr}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i),\ \mathsf{Z}\bigr).$$
  $hG_2$ に [(T.cnf_P_Z)](#t-cnf_P_Z) を適用して $\mathrm{cnf}(\mathrm{tr}(G'\mathbin{+\!\!+}z_2\mathbin{::}T_2))$、
  $\lvert G'\rvert<\lvert g\mathbin{::}G'\rvert$ より帰納法の仮定 $\Phi(G')$ を適用して
  $\mathrm{cnf}(\mathrm{tr}(G'\mathbin{+\!\!+}z_1\mathbin{::}T_1))$、
  再び [(T.cnf_P_Z)](#t-cnf_P_Z) より $\mathrm{cnf}(\mathrm{tr}(g\mathbin{::}(G'\mathbin{+\!\!+}z_1\mathbin{::}T_1)))$ を得る。
- **場合 (c)** $\forall x\in G',\ \pi_0 g<\pi_0 x$ かつ $\neg(\pi_0 g<\pi_0 z_1)$。
  root より $\neg(\pi_0 g<\pi_0 z_2)$ でもある。
  [(T.takeWhile_append_all)](Mechanized.md#t-takeWhile_append_all) より（$i=1,2$）
  $$\mathrm{tw}_{\pi_0 g}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i)
   = G'\mathbin{+\!\!+}\mathrm{tw}_{\pi_0 g}(z_i\mathbin{::}T_i) = G'\mathbin{+\!\!+}[] = G'$$
  （先頭 $z_i$ が述語をみたさないので $\mathrm{tw}_{\pi_0 g}(z_i\mathbin{::}T_i)=[]$）、
  [(T.dropWhile_append_all)](Mechanized.md#t-dropWhile_append_all) より
  $$\mathrm{dw}_{\pi_0 g}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i) = \mathrm{dw}_{\pi_0 g}(z_i\mathbin{::}T_i) = z_i\mathbin{::}T_i.$$
  よって [(D.translate)](Mechanized.md#d-translate) と $lZ_1$, $lZ_2$ より
  $$\mathrm{tr}\bigl(g\mathbin{::}(G'\mathbin{+\!\!+}z_1\mathbin{::}T_1)\bigr)
   = \mathsf{P}\bigl(\pi_1 g,\ \mathrm{tr}\,G',\ \mathsf{P}(a_1,b_1,c_1)\bigr),$$
  $$\mathrm{tr}\bigl(g\mathbin{::}(G'\mathbin{+\!\!+}z_2\mathbin{::}T_2)\bigr)
   = \mathsf{P}\bigl(\pi_1 g,\ \mathrm{tr}\,G',\ \mathsf{P}(a_2,b_2,c_2)\bigr).$$
  $hG_2$ に [(T.cnf_P_P)](#t-cnf_P_P) を適用して
  $c_{tg} : \mathrm{cnf}(\mathrm{tr}\,G')$ と
  $b_2^{\ast} : \neg\bigl(\mathsf{P}(\pi_1 g,\mathrm{tr}\,G',\mathsf{Z}) \prec \mathsf{P}(a_2,b_2,\mathsf{Z})\bigr)$ を得る。
  ここから
  $$b_1^{\ast} : \neg\bigl(\mathsf{P}(\pi_1 g,\mathrm{tr}\,G',\mathsf{Z}) \prec \mathsf{P}(a_1,b_1,\mathsf{Z})\bigr)$$
  が従う。実際、左の $\prec$ が成り立つとすると、$lle$ と
  [(T.olt_ole_trans)](Mechanized.md#t-olt_ole_trans) により
  $\mathsf{P}(\pi_1 g,\mathrm{tr}\,G',\mathsf{Z}) \prec \mathsf{P}(a_2,b_2,\mathsf{Z})$ となり $b_2^{\ast}$ に矛盾する。
  第 3 条件 $\mathrm{cnf}\,\mathsf{P}(a_1,b_1,c_1)$ は $lZ_1$ により $cZ_1$ と同じ命題である。
  よって [(T.cnf_P_P)](#t-cnf_P_P) に $c_{tg}$, $b_1^{\ast}$, $cZ_1$ を与えて結論を得る。
- **場合 (a)** $\neg(\forall x\in G',\ \pi_0 g<\pi_0 x)$。
  $x\in G'$ で $\neg(\pi_0 g<\pi_0 x)$ なるものを取る。
  [(T.takeWhile_append_not)](Mechanized.md#t-takeWhile_append_not) と
  [(T.dropWhile_append_not)](Mechanized.md#t-dropWhile_append_not) より（$i=1,2$）
  $$\mathrm{tw}_{\pi_0 g}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i) = \mathrm{tw}_{\pi_0 g}G',\qquad
    \mathrm{dw}_{\pi_0 g}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i) = (\mathrm{dw}_{\pi_0 g}G')\mathbin{+\!\!+}z_i\mathbin{::}T_i.$$
  また $\mathrm{dw}_{\pi_0 g}G'\ne[]$ である（$=[]$ なら `List.dropWhile_eq_nil_iff` より $G'$ の全要素が
  述語をみたし、$x$ に適用して仮定に反する）。そこで $\mathrm{dw}_{\pi_0 g}G' = d\mathbin{::}D'$ と書く。
  [(D.translate)](Mechanized.md#d-translate) より（$i=1,2$）
  $$\mathrm{tr}\bigl(g\mathbin{::}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i)\bigr)
   = \mathsf{P}\Bigl(\pi_1 g,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 g}G'),\
     \mathrm{tr}\bigl((d\mathbin{::}D')\mathbin{+\!\!+}z_i\mathbin{::}T_i\bigr)\Bigr),$$
  $$\mathrm{tr}\bigl((d\mathbin{::}D')\mathbin{+\!\!+}z_i\mathbin{::}T_i\bigr)
   = \mathsf{P}\Bigl(\pi_1 d,\ \mathrm{tr}\bigl(\mathrm{tw}_{\pi_0 d}(D'\mathbin{+\!\!+}z_i\mathbin{::}T_i)\bigr),\
      \mathrm{tr}\bigl(\mathrm{dw}_{\pi_0 d}(D'\mathbin{+\!\!+}z_i\mathbin{::}T_i)\bigr)\Bigr)$$
  （後者は $(d\mathbin{::}D')\mathbin{+\!\!+}Y = d\mathbin{::}(D'\mathbin{+\!\!+}Y)$ による）。
  以下 $\mathrm{arg}_i := \mathrm{tr}(\mathrm{tw}_{\pi_0 d}(D'\mathbin{+\!\!+}z_i\mathbin{::}T_i))$、
  $\mathrm{tl}_i := \mathrm{tr}(\mathrm{dw}_{\pi_0 d}(D'\mathbin{+\!\!+}z_i\mathbin{::}T_i))$ と書く。

  [(T.translate_ctx_cong)](Mechanized.md#t-translate_ctx_cong) を base $:=$ decr, root, $r_1$, $r_2$,
  $G:=d\mathbin{::}D'$ として適用すると
  $$\mathrm{tr}\bigl((d\mathbin{::}D')\mathbin{+\!\!+}z_1\mathbin{::}T_1\bigr)
   \prec \mathrm{tr}\bigl((d\mathbin{::}D')\mathbin{+\!\!+}z_2\mathbin{::}T_2\bigr)$$
  であり、上の $\mathsf{P}$ 表示と [(T.olt_P_P)](Mechanized.md#t-olt_P_P) より次の 3 つのいずれかが成り立つ。
  $\pi_1 d<\pi_1 d$（自然数の $<$ の非反射性により偽）、
  $(\pi_1 d=\pi_1 d \wedge \mathrm{arg}_1\prec\mathrm{arg}_2)$、
  $(\pi_1 d=\pi_1 d \wedge \mathrm{arg}_1=\mathrm{arg}_2 \wedge \mathrm{tl}_1\prec\mathrm{tl}_2)$。
  したがって
  $$\text{argle} : \mathrm{arg}_1\prec\mathrm{arg}_2 \ \vee\ \mathrm{arg}_1=\mathrm{arg}_2 . \tag{argle}$$

  $hG_2$ に [(T.cnf_P_P)](#t-cnf_P_P) を適用して
  $c_{tw} : \mathrm{cnf}(\mathrm{tr}(\mathrm{tw}_{\pi_0 g}G'))$、
  $b_2^{\ast} : \neg\bigl(\mathsf{P}(\pi_1 g,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 g}G'),\ \mathsf{Z}) \prec \mathsf{P}(\pi_1 d,\ \mathrm{arg}_2,\ \mathsf{Z})\bigr)$、
  $cD_2 : \mathrm{cnf}\bigl(\mathsf{P}(\pi_1 d,\mathrm{arg}_2,\mathrm{tl}_2)\bigr) = \mathrm{cnf}\bigl(\mathrm{tr}((d\mathbin{::}D')\mathbin{+\!\!+}z_2\mathbin{::}T_2)\bigr)$ を得る。
  $\lvert d\mathbin{::}D'\rvert = \lvert\mathrm{dw}_{\pi_0 g}G'\rvert \le \lvert G'\rvert < \lvert g\mathbin{::}G'\rvert$
  （`List.length_dropWhile_le`）だから帰納法の仮定 $\Phi(d\mathbin{::}D')$ が使え、$cD_2$ から
  $$cD_1 : \mathrm{cnf}\bigl(\mathrm{tr}((d\mathbin{::}D')\mathbin{+\!\!+}z_1\mathbin{::}T_1)\bigr)$$
  を得る。

  次に
  $$b_1^{\ast} : \neg\bigl(\mathsf{P}(\pi_1 g,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 g}G'),\ \mathsf{Z})
   \prec \mathsf{P}(\pi_1 d,\ \mathrm{arg}_1,\ \mathsf{Z})\bigr)$$
  を示す。左の $\prec$ が成り立つとして [(T.olt_P_P)](Mechanized.md#t-olt_P_P) で 3 つに分ける。
  - $\pi_1 g<\pi_1 d$：このとき [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 1 選言により
    $\mathsf{P}(\pi_1 g,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 g}G'),\ \mathsf{Z}) \prec \mathsf{P}(\pi_1 d,\mathrm{arg}_2,\mathsf{Z})$ となり
    $b_2^{\ast}$ に矛盾する。
  - $\pi_1 g=\pi_1 d$ かつ $\mathrm{tr}(\mathrm{tw}_{\pi_0 g}G')\prec\mathrm{arg}_1$：(argle) で分ける。
    $\mathrm{arg}_1\prec\mathrm{arg}_2$ なら [(T.olt_trans)](Mechanized.md#t-olt_trans) より
    $\mathrm{tr}(\mathrm{tw}_{\pi_0 g}G')\prec\mathrm{arg}_2$、
    $\mathrm{arg}_1=\mathrm{arg}_2$ ならそのまま $\mathrm{tr}(\mathrm{tw}_{\pi_0 g}G')\prec\mathrm{arg}_2$。
    いずれも [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 2 選言により $b_2^{\ast}$ に矛盾する。
  - $\pi_1 g=\pi_1 d$ かつ $\mathrm{tr}(\mathrm{tw}_{\pi_0 g}G')=\mathrm{arg}_1$ かつ $\mathsf{Z}\prec\mathsf{Z}$：
    [(T.not_olt_Z)](Mechanized.md#t-not_olt_Z) に矛盾する。

  よって [(T.cnf_P_P)](#t-cnf_P_P) に $c_{tw}$, $b_1^{\ast}$, $cD_1$ を与えて
  $\mathrm{cnf}(\mathrm{tr}(g\mathbin{::}(G'\mathbin{+\!\!+}z_1\mathbin{::}T_1)))$ を得る。

3 つの場合はすべてを尽くしている。帰納法で用いた $G'$（場合 (b)）と $d\mathbin{::}D'$（場合 (a)）の長さは
いずれも $\lvert g\mathbin{::}G'\rvert$ より真に小さいので、強帰納法は正当である。∎

<a id="t-cnf_tail"></a>
### 定理 末尾ブロック単独の $\mathrm{cnf}$ (T.cnf_tail)

**主張** 対 $t$、ペア列 $T'$ が $r_T : \forall x\in T',\ \pi_0 t\le\pi_0 x$ をみたすとする。
このとき任意のペア列 $G$ について
$$\mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}t\mathbin{::}T')\bigr)
 \ \Longrightarrow\ \mathrm{cnf}\bigl(\mathrm{tr}(t\mathbin{::}T')\bigr).$$

**証明** $t,T',r_T$ を固定し、$\lvert G\rvert$ に関する強帰納法。帰納法の述語は

$$\Phi(G) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}t\mathbin{::}T')\bigr)
 \to \mathrm{cnf}\bigl(\mathrm{tr}(t\mathbin{::}T')\bigr)$$

であり、$\lvert G'\rvert<\lvert G\rvert$ なるすべての $G'$ について $\Phi(G')$ を仮定して $\Phi(G)$ を示す。

**$G=[]$ のとき。** $[]\mathbin{+\!\!+}t\mathbin{::}T' = t\mathbin{::}T'$ であるから、仮定がそのまま結論である。

**$G=g\mathbin{::}G'$ のとき。** $hGT : \mathrm{cnf}(\mathrm{tr}(g\mathbin{::}(G'\mathbin{+\!\!+}t\mathbin{::}T')))$ を仮定し、
3 つの場合に分ける。

- **場合 (b)** $\forall x\in G',\ \pi_0 g<\pi_0 x$ かつ $\pi_0 g<\pi_0 t$。
  $G'\mathbin{+\!\!+}t\mathbin{::}T'$ の全要素 $x$ が $\pi_0 g<\pi_0 x$ をみたす（$x\in G'$ なら仮定、$x=t$ なら
  $\pi_0 g<\pi_0 t$、$x\in T'$ なら $r_T$ より $\pi_0 g<\pi_0 t\le\pi_0 x$）。
  よって [(T.translate_single_tree)](Mechanized.md#t-translate_single_tree) より
  $$\mathrm{tr}\bigl(g\mathbin{::}(G'\mathbin{+\!\!+}t\mathbin{::}T')\bigr)
   = \mathsf{P}\bigl(\pi_1 g,\ \mathrm{tr}(G'\mathbin{+\!\!+}t\mathbin{::}T'),\ \mathsf{Z}\bigr)$$
  であり、$hGT$ に [(T.cnf_P_Z)](#t-cnf_P_Z) を適用して $\mathrm{cnf}(\mathrm{tr}(G'\mathbin{+\!\!+}t\mathbin{::}T'))$ を得る。
  $\lvert G'\rvert<\lvert g\mathbin{::}G'\rvert$ より帰納法の仮定 $\Phi(G')$ を適用して結論を得る。
- **場合 (c)** $\forall x\in G',\ \pi_0 g<\pi_0 x$ かつ $\neg(\pi_0 g<\pi_0 t)$。
  [(T.takeWhile_append_all)](Mechanized.md#t-takeWhile_append_all) より
  $\mathrm{tw}_{\pi_0 g}(G'\mathbin{+\!\!+}t\mathbin{::}T') = G'\mathbin{+\!\!+}\mathrm{tw}_{\pi_0 g}(t\mathbin{::}T') = G'$
  （先頭 $t$ が述語をみたさない）、
  [(T.dropWhile_append_all)](Mechanized.md#t-dropWhile_append_all) より
  $\mathrm{dw}_{\pi_0 g}(G'\mathbin{+\!\!+}t\mathbin{::}T') = t\mathbin{::}T'$。よって
  [(D.translate)](Mechanized.md#d-translate) より
  $$\mathrm{tr}\bigl(g\mathbin{::}(G'\mathbin{+\!\!+}t\mathbin{::}T')\bigr)
   = \mathsf{P}\bigl(\pi_1 g,\ \mathrm{tr}\,G',\ \mathrm{tr}(t\mathbin{::}T')\bigr)$$
  であり、さらに [(D.translate)](Mechanized.md#d-translate) より
  $\mathrm{tr}(t\mathbin{::}T') = \mathsf{P}\bigl(\pi_1 t,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 t}T'),\ \mathrm{tr}(\mathrm{dw}_{\pi_0 t}T')\bigr)$
  である。これは第 3 引数が $\mathsf{P}$ の形であるから、$hGT$ に [(T.cnf_P_P)](#t-cnf_P_P) を適用でき、
  その第 3 成分がまさに $\mathrm{cnf}(\mathrm{tr}(t\mathbin{::}T'))$ である。
- **場合 (a)** $\neg(\forall x\in G',\ \pi_0 g<\pi_0 x)$。
  $x\in G'$ で $\neg(\pi_0 g<\pi_0 x)$ なるものを取る。
  [(T.takeWhile_append_not)](Mechanized.md#t-takeWhile_append_not) と
  [(T.dropWhile_append_not)](Mechanized.md#t-dropWhile_append_not) より
  $$\mathrm{tw}_{\pi_0 g}(G'\mathbin{+\!\!+}t\mathbin{::}T') = \mathrm{tw}_{\pi_0 g}G',\qquad
    \mathrm{dw}_{\pi_0 g}(G'\mathbin{+\!\!+}t\mathbin{::}T') = (\mathrm{dw}_{\pi_0 g}G')\mathbin{+\!\!+}t\mathbin{::}T' .$$
  $\mathrm{dw}_{\pi_0 g}G'\ne[]$ である（$=[]$ なら `List.dropWhile_eq_nil_iff` より $G'$ の全要素が述語をみたし、
  $x$ に適用して仮定に反する）。そこで $\mathrm{dw}_{\pi_0 g}G' = d\mathbin{::}D'$ と書くと、
  [(D.translate)](Mechanized.md#d-translate) より
  $$\mathrm{tr}\bigl(g\mathbin{::}(G'\mathbin{+\!\!+}t\mathbin{::}T')\bigr)
   = \mathsf{P}\Bigl(\pi_1 g,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 g}G'),\
      \mathrm{tr}\bigl((d\mathbin{::}D')\mathbin{+\!\!+}t\mathbin{::}T'\bigr)\Bigr),$$
  $$\mathrm{tr}\bigl((d\mathbin{::}D')\mathbin{+\!\!+}t\mathbin{::}T'\bigr)
   = \mathsf{P}\Bigl(\pi_1 d,\ \mathrm{tr}\bigl(\mathrm{tw}_{\pi_0 d}(D'\mathbin{+\!\!+}t\mathbin{::}T')\bigr),\
      \mathrm{tr}\bigl(\mathrm{dw}_{\pi_0 d}(D'\mathbin{+\!\!+}t\mathbin{::}T')\bigr)\Bigr).$$
  第 3 引数が $\mathsf{P}$ の形であるから $hGT$ に [(T.cnf_P_P)](#t-cnf_P_P) を適用でき、
  その第 3 成分は $\mathrm{cnf}\bigl(\mathrm{tr}((d\mathbin{::}D')\mathbin{+\!\!+}t\mathbin{::}T')\bigr)$ である。
  $\lvert d\mathbin{::}D'\rvert = \lvert\mathrm{dw}_{\pi_0 g}G'\rvert \le \lvert G'\rvert < \lvert g\mathbin{::}G'\rvert$
  （`List.length_dropWhile_le`）だから帰納法の仮定 $\Phi(d\mathbin{::}D')$ が使え、結論を得る。

3 つの場合はすべてを尽くしており、帰納法で用いた $G'$ と $d\mathbin{::}D'$ の長さは
いずれも $\lvert g\mathbin{::}G'\rvert$ より真に小さいので、強帰納法は正当である。∎

<a id="t-cnf_oper_i1eq0"></a>
### 定理 $\mathrm{cnf}$ の保存：完全コピー（$i_1=0$）の場合 (T.cnf_oper_i1eq0)

**主張** $v_0,w_0\in\mathbb{N}$、ペア列 $R,G$、対 $lp$、$n\in\mathbb{N}$ が
$$\forall x\in R,\ v_0<\pi_0 x,\qquad v_0<\pi_0 lp,\qquad 1\le n,\qquad
  \mathrm{cnf}\Bigl(\mathrm{tr}\bigl(G\mathbin{+\!\!+}((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}[lp]\bigr)\Bigr)$$
をみたすならば
$$\mathrm{cnf}\Bigl(\mathrm{tr}\bigl(G\mathbin{+\!\!+}\mathrm{flatten}\ \mathrm{replicate}(n,\ (v_0,w_0)\mathbin{::}R)\bigr)\Bigr).$$

**証明** $B := (v_0,w_0)\mathbin{::}R$、$T_m := \mathrm{flatten}\ \mathrm{replicate}(m,B)$ とおく。
$1\le n$ より $n=m+1$ と書ける。

**(1) 2 つの列の形.**
$R\mathbin{+\!\!+}[lp]$ の全要素 $x$ は $v_0<\pi_0 x$ をみたす（$x\in R$ なら第 1 の仮定、$x=lp$ なら第 2 の仮定）。
よって [(T.translate_single_tree)](Mechanized.md#t-translate_single_tree) より
$$\mathrm{tr}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp])\bigr)
 = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R\mathbin{+\!\!+}[lp]),\ \mathsf{Z}\bigr). \tag{tZ2}$$
また [(T.cnf_replicate_block)](#t-cnf_replicate_block) の証明中の (rep), (cond) と同じ計算により
$$T_{m+1} = (v_0,w_0)\mathbin{::}\bigl(R\mathbin{+\!\!+}T_m\bigr), \tag{e1n}$$
$$T_m=[]\ \vee\ \neg\bigl(v_0<\pi_0(\mathrm{headI}\,T_m)\bigr)$$
であり、[(T.translate_block_append)](Mechanized.md#t-translate_block_append) より
$$\mathrm{tr}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}T_m)\bigr)
 = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T_m\bigr). \tag{tZ1}$$

**(2) ブロック本体の $\mathrm{cnf}$.**
$r_T : \forall x\in R\mathbin{+\!\!+}[lp],\ v_0\le\pi_0 x$ は (1) の第 1 段から従う。
仮定の $\mathrm{cnf}$ は結合の付け替え
$G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp] = G\mathbin{+\!\!+}(v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp])$
により $cM' : \mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}(v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp]))\bigr)$ と書ける。
[(T.cnf_tail)](#t-cnf_tail)（$t:=(v_0,w_0)$, $T':=R\mathbin{+\!\!+}[lp]$）より
$\mathrm{cnf}\bigl(\mathrm{tr}((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp]))\bigr)$、
(tZ2) と [(T.cnf_P_Z)](#t-cnf_P_Z) より $\mathrm{cnf}\bigl(\mathrm{tr}(R\mathbin{+\!\!+}[lp])\bigr)$、
[(T.cnf_snoc)](#t-cnf_snoc) より
$$cR : \mathrm{cnf}(\mathrm{tr}\,R).$$
したがって [(T.cnf_replicate_block)](#t-cnf_replicate_block) より
$$cZ_1 : \mathrm{cnf}(\mathrm{tr}\,T_{m+1}).$$

**(3) 減少と先頭主要項の比較.**
[(T.translate_snoc_increase)](Mechanized.md#t-translate_snoc_increase) より
$\mathrm{tr}\,R \prec \mathrm{tr}(R\mathbin{+\!\!+}[lp])$。よって (tZ1), (tZ2) と
[(T.olt_P_b)](Mechanized.md#t-olt_P_b) より
$$\text{decr} : \mathrm{tr}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}T_m)\bigr)
 \prec \mathrm{tr}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp])\bigr),$$
$$\text{leadle} : \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathsf{Z}\bigr)
 \preceq \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R\mathbin{+\!\!+}[lp]),\ \mathsf{Z}\bigr)$$
（leadle の証人は $a_1=a_2=w_0$, $b_1=\mathrm{tr}\,R$, $c_1=\mathrm{tr}\,T_m$,
$b_2=\mathrm{tr}(R\mathbin{+\!\!+}[lp])$, $c_2=\mathsf{Z}$、および (tZ1), (tZ2)）。

**(4) 側条件 $r_1$.** $T_m$ の任意の要素は $B$ の要素である。実際 $T_m$ は
$\mathrm{replicate}(m,B)$ の要素をすべて連結したものであり、`List.eq_of_mem_replicate` より
その各要素は $B$ に等しいからである。したがって $x\in R\mathbin{+\!\!+}T_m$ ならば、
$x\in R$ の場合は第 1 の仮定より $v_0<\pi_0 x$、
$x\in T_m$ の場合は $x\in B=(v_0,w_0)\mathbin{::}R$ であり $x=(v_0,w_0)$ なら $\pi_0 x=v_0$、$x\in R$ なら $v_0<\pi_0 x$。
いずれにせよ
$$r_1 : \forall x\in R\mathbin{+\!\!+}T_m,\ v_0\le\pi_0 x .$$

**(5) 結論.** [(T.cnf_ctx_cong)](#t-cnf_ctx_cong) を
$z_1:=(v_0,w_0)$, $T_1:=R\mathbin{+\!\!+}T_m$, $z_2:=(v_0,w_0)$, $T_2:=R\mathbin{+\!\!+}[lp]$,
$cZ_1$ は (e1n) により (2) の $cZ_1$、decr は (3)、root は $\pi_0(v_0,w_0)=\pi_0(v_0,w_0)$、
leadle は (3)、$r_1$ は (4)、$r_2$ は $r_T$、$G:=G$、$hG_2 := cM'$ として適用すると
$$\mathrm{cnf}\Bigl(\mathrm{tr}\bigl(G\mathbin{+\!\!+}(v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}T_m)\bigr)\Bigr)$$
が得られる。(e1n) によりこれが求める $\mathrm{cnf}(\mathrm{tr}(G\mathbin{+\!\!+}T_{m+1}))$ である。∎

## $\mathrm{cnf}$ の保存：昇順コピー（$i_1=1$）の場合

$i_1=1$ の悪い分岐は、ブロック $B=(v_0,w_0)\mathbin{::}R$ とその後に落とされる対 $lp$ を、
$B$ の**昇順コピー** $n$ 個に置き換える：第 $k$ コピーは $B$ の行 0 の値をすべて $k\,d_0$ だけ増やしたものである
（$d_0>0$）。このコピー列を $\mathrm{cp}_{d_0}(B,n)$ と書く。

<a id="d-shiftr0"></a>
### 定義 行 0 の平行移動 (D.shiftr0)

$d\in\mathbb{N}$ に対し $\sigma_d(p) := (\pi_0 p + d,\ \pi_1 p)$ とおき

$$\mathrm{sh}_d M := \mathrm{map}\ \sigma_d\ M .$$

<a id="d-copies"></a>
### 定義 昇順コピー (D.copies)

$d\in\mathbb{N}$、ペア列 $B$、$n\in\mathbb{N}$ に対し

$$\mathrm{cp}_d(B,n) := \mathrm{flatMap}\ \bigl(\lambda k.\ \mathrm{sh}_{k\,d}B\bigr)\ \mathrm{range}(n)
 = \mathrm{sh}_{0}B \mathbin{+\!\!+} \mathrm{sh}_{d}B \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \mathrm{sh}_{(n-1)d}B .$$

<a id="t-shiftr0_zero"></a>
### 定理 $d=0$ の平行移動 (T.shiftr0_zero)

**主張** 任意のペア列 $M$ に対し $\mathrm{sh}_0 M = M$。

**証明** 任意の対 $p$ に対し $\sigma_0(p) = (\pi_0 p+0,\ \pi_1 p) = (\pi_0 p,\pi_1 p) = p$ であるから
$\sigma_0$ は恒等写像であり、`List.map_id` より $\mathrm{map}\ \sigma_0\ M = M$。∎

<a id="t-shiftr0_nil"></a>
### 定理 空列の平行移動 (T.shiftr0_nil)

**主張** 任意の $d\in\mathbb{N}$ に対し $\mathrm{sh}_d[] = []$。

**証明** $\mathrm{map}\ \sigma_d\ [] = []$ であり、両辺は定義により同一である。∎

<a id="t-shiftr0_eq_nil"></a>
### 定理 平行移動が空になる条件 (T.shiftr0_eq_nil)

**主張** $\mathrm{sh}_d M = [] \iff M = []$。

**証明** [(D.shiftr0)](#d-shiftr0) より $\mathrm{sh}_d M = \mathrm{map}\,\sigma_d\,M$ であり、
標準ライブラリの `List.map_eq_nil_iff`（$\mathrm{map}\,f\,l=[] \iff l=[]$）そのものである。∎

<a id="t-translate_shiftr0"></a>
### 定理 平行移動は翻訳を変えない (T.translate_shiftr0)

**主張** 任意の $d\in\mathbb{N}$、ペア列 $M$ に対し $\mathrm{tr}(\mathrm{sh}_d M) = \mathrm{tr}\,M$。

**証明** [(D.shiftr0)](#d-shiftr0) より $\mathrm{sh}_d M = \mathrm{map}\,\sigma_d\,M$ であるから、
[(T.translate_shift)](Mechanized.md#t-translate_shift) そのものである。∎

<a id="t-shiftr0_cons"></a>
### 定理 先頭付加の平行移動 (T.shiftr0_cons)

**主張** $\mathrm{sh}_d(p\mathbin{::}M) = (\pi_0 p+d,\ \pi_1 p)\mathbin{::}\mathrm{sh}_d M$。

**証明** $\mathrm{map}$ は先頭付加と交換し $\sigma_d(p) = (\pi_0 p+d,\pi_1 p)$ であるから、
両辺は定義により同一である。∎

<a id="t-mem_shiftr0"></a>
### 定理 平行移動の要素判定 (T.mem_shiftr0)

**主張** $x\in\mathrm{sh}_d M \iff \exists p\in M,\ (\pi_0 p+d,\ \pi_1 p) = x$。

**証明** [(D.shiftr0)](#d-shiftr0) より $\mathrm{sh}_d M = \mathrm{map}\,\sigma_d\,M$ であり、
標準ライブラリの `List.mem_map`（$x\in\mathrm{map}\,f\,l \iff \exists a\in l,\ f\,a=x$）を
$f:=\sigma_d$ に適用したものである。∎

<a id="t-copies_zero"></a>
### 定理 コピー数 $0$ (T.copies_zero)

**主張** $\mathrm{cp}_d(B,0) = []$。

**証明** $\mathrm{range}(0)=[]$ であり、空列の $\mathrm{flatMap}$ は $[]$ である。
両辺は定義により同一である。∎

<a id="t-copies_succ_front"></a>
### 定理 コピー列の先頭分解 (T.copies_succ_front)

**主張** $\mathrm{cp}_d(B,n+1) = B \mathbin{+\!\!+} \mathrm{sh}_d\bigl(\mathrm{cp}_d(B,n)\bigr)$。

**証明** `List.range_succ_eq_map`（$\mathrm{range}(n+1) = 0\mathbin{::}\mathrm{map}\ (\lambda k.\ k+1)\ \mathrm{range}(n)$）と
$\mathrm{flatMap}$ の先頭分解より
$$\mathrm{cp}_d(B,n+1)
 = \mathrm{sh}_{0\cdot d}B \mathbin{+\!\!+}
   \mathrm{flatMap}\ \bigl(\lambda k.\ \mathrm{sh}_{k\,d}B\bigr)\ \bigl(\mathrm{map}\ (\lambda k.\ k+1)\ \mathrm{range}(n)\bigr).$$
第 1 項は $0\cdot d = 0$ と [(T.shiftr0_zero)](#t-shiftr0_zero) より $B$ である。
第 2 項は `List.flatMap_map`（$\mathrm{flatMap}\ g\ (\mathrm{map}\ f\ l) = \mathrm{flatMap}\ (g\circ f)\ l$）より
$$\mathrm{flatMap}\ \bigl(\lambda k.\ \mathrm{sh}_{(k+1)d}B\bigr)\ \mathrm{range}(n).$$
他方、右辺の第 2 項は [(D.shiftr0)](#d-shiftr0) と
`List.map_flatMap`（$\mathrm{map}\ f\ (\mathrm{flatMap}\ g\ l) = \mathrm{flatMap}\ (\lambda a.\ \mathrm{map}\ f\ (g\,a))\ l$）より
$$\mathrm{sh}_d\bigl(\mathrm{cp}_d(B,n)\bigr)
 = \mathrm{flatMap}\ \bigl(\lambda k.\ \mathrm{map}\ \sigma_d\ (\mathrm{map}\ \sigma_{k\,d}\ B)\bigr)\ \mathrm{range}(n)$$
であり、`List.map_map` より $\mathrm{map}\ \sigma_d\ (\mathrm{map}\ \sigma_{k\,d}\ B) = \mathrm{map}\ (\sigma_d\circ\sigma_{k\,d})\ B$。
ここで任意の対 $p$ について
$$(\sigma_d\circ\sigma_{k\,d})(p) = \bigl((\pi_0 p + k\,d) + d,\ \pi_1 p\bigr)
 = \bigl(\pi_0 p + (k\,d + d),\ \pi_1 p\bigr) = \bigl(\pi_0 p + (k+1)d,\ \pi_1 p\bigr) = \sigma_{(k+1)d}(p)$$
である（加法の結合律と $(k+1)d = k\,d + d$）。よって両辺の第 2 項も一致する。∎

<a id="t-copies_one"></a>
### 定理 コピー数 $1$ (T.copies_one)

**主張** $\mathrm{cp}_d(B,1) = B$。

**証明** [(T.copies_succ_front)](#t-copies_succ_front) を $n:=0$ に適用して
$\mathrm{cp}_d(B,1) = B\mathbin{+\!\!+}\mathrm{sh}_d(\mathrm{cp}_d(B,0))$。
[(T.copies_zero)](#t-copies_zero) より $\mathrm{cp}_d(B,0)=[]$、
[(T.shiftr0_nil)](#t-shiftr0_nil) より $\mathrm{sh}_d[]=[]$、$B\mathbin{+\!\!+}[]=B$。∎

<a id="t-copies_nonempty"></a>
### 定理 コピー列は空でない (T.copies_nonempty)

**主張** $B\ne[]$ かつ $1\le n$ ならば $\mathrm{cp}_d(B,n)\ne[]$。

**証明** $1\le n$ より $n=m+1$ と書ける。[(T.copies_succ_front)](#t-copies_succ_front) より
$\mathrm{cp}_d(B,m+1) = B\mathbin{+\!\!+}\mathrm{sh}_d(\mathrm{cp}_d(B,m))$ である。
連結が空列であるのは両者がともに空列のときに限るから、$B\ne[]$ より $\mathrm{cp}_d(B,m+1)\ne[]$。∎

<a id="t-copies_succ_cons"></a>
### 定理 コピー列の先頭付加形 (T.copies_succ_cons)

**主張** $d,v_0,w_0\in\mathbb{N}$、ペア列 $R$、$n\in\mathbb{N}$ に対し
$$\mathrm{cp}_d\bigl((v_0,w_0)\mathbin{::}R,\ n+1\bigr)
 = (v_0,w_0)\mathbin{::}\Bigl(R\mathbin{+\!\!+}\mathrm{sh}_d\bigl(\mathrm{cp}_d((v_0,w_0)\mathbin{::}R,\ n)\bigr)\Bigr).$$

**証明** [(T.copies_succ_front)](#t-copies_succ_front) を $B:=(v_0,w_0)\mathbin{::}R$ に適用すると
左辺は $\bigl((v_0,w_0)\mathbin{::}R\bigr)\mathbin{+\!\!+}\mathrm{sh}_d(\mathrm{cp}_d(B,n))$ である。
$(p\mathbin{::}L)\mathbin{+\!\!+}Y = p\mathbin{::}(L\mathbin{+\!\!+}Y)$ よりこれは右辺に等しい。∎

<a id="t-copies_v0_le"></a>
### 定理 コピー列の行 0 の下界 (T.copies_v0_le)

**主張** $\forall x\in R,\ v_0\le\pi_0 x$ ならば、任意の $d,n\in\mathbb{N}$ に対し
$$\forall x\in\mathrm{cp}_d\bigl((v_0,w_0)\mathbin{::}R,\ n\bigr),\ v_0\le\pi_0 x .$$

**証明** $x\in\mathrm{cp}_d((v_0,w_0)\mathbin{::}R,\ n)$ とする。
[(D.copies)](#d-copies) は $\mathrm{flatMap}$ であるから、`List.mem_flatMap` により
ある $k\in\mathrm{range}(n)$ について $x\in\mathrm{sh}_{k\,d}\bigl((v_0,w_0)\mathbin{::}R\bigr)$、
[(T.mem_shiftr0)](#t-mem_shiftr0) によりある $p\in(v_0,w_0)\mathbin{::}R$ について
$x = (\pi_0 p + k\,d,\ \pi_1 p)$ である。
$p=(v_0,w_0)$ なら $\pi_0 p = v_0$、$p\in R$ なら仮定より $v_0\le\pi_0 p$。いずれにせよ $v_0\le\pi_0 p$ であり、
$$\pi_0 x = \pi_0 p + k\,d \ \ge\ \pi_0 p \ \ge\ v_0 .$$
∎

<a id="t-copies_tl_gt"></a>
### 定理 コピー列の尾部の行 0 の狭義下界 (T.copies_tl_gt)

**主張** $\forall x\in R,\ v_0<\pi_0 x$、$0<d$、$1\le n$ ならば
$$\forall x\in R\mathbin{+\!\!+}\mathrm{sh}_d\bigl(\mathrm{cp}_d((v_0,w_0)\mathbin{::}R,\ n-1)\bigr),\ v_0<\pi_0 x .$$

**証明** $x$ を取り、連結の 2 つの部分で分ける。

- $x\in R$ のとき：仮定より $v_0<\pi_0 x$。
- $x\in\mathrm{sh}_d\bigl(\mathrm{cp}_d((v_0,w_0)\mathbin{::}R,\ n-1)\bigr)$ のとき：
  [(T.mem_shiftr0)](#t-mem_shiftr0) によりある $p\in\mathrm{cp}_d((v_0,w_0)\mathbin{::}R,\ n-1)$ について
  $x = (\pi_0 p+d,\ \pi_1 p)$ である。仮定 $\forall x\in R,\ v_0<\pi_0 x$ から
  $\forall x\in R,\ v_0\le\pi_0 x$ が従うので、[(T.copies_v0_le)](#t-copies_v0_le) より $v_0\le\pi_0 p$。
  よって $0<d$ とあわせて $\pi_0 x = \pi_0 p + d \ge v_0 + d > v_0$。

（仮定 $1\le n$ はこの証明では使わない。Lean 側でも未使用引数として記されている。）∎

<a id="t-cnf_copies"></a>
### 定理 昇順コピー列の $\mathrm{cnf}$ (T.cnf_copies)

**主張** $v_0,w_0,d_0\in\mathbb{N}$、ペア列 $R$、対 $lp$ が
$$\forall x\in R,\ v_0<\pi_0 x,\qquad 0<d_0,\qquad w_0<\pi_1 lp,\qquad \pi_0 lp = v_0+d_0,$$
$$\mathrm{cnf}\Bigl(\mathrm{tr}\bigl(((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}[lp]\bigr)\Bigr)$$
をみたすならば、任意の $n\in\mathbb{N}$ に対し
$\mathrm{cnf}\Bigl(\mathrm{tr}\bigl(\mathrm{cp}_{d_0}((v_0,w_0)\mathbin{::}R,\ n)\bigr)\Bigr)$。

**証明** $B := (v_0,w_0)\mathbin{::}R$ とおき、$n$ に関する自然数の帰納法。帰納法の述語は

$$\Phi(n) :\equiv \mathrm{cnf}\Bigl(\mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B,n)\bigr)\Bigr).$$

- 基底段 $n=0$：[(T.copies_zero)](#t-copies_zero) より $\mathrm{cp}_{d_0}(B,0)=[]$、
  $\mathrm{tr}\,[]=\mathsf{Z}$、[(T.cnf_Z)](#t-cnf_Z) より $\Phi(0)$。
- 帰納段 $n+1$：帰納法の仮定は $\Phi(n)$ である。$n$ の形でさらに 2 つに分ける。
  - **$n=0$（すなわちコピー数 $1$）のとき。** [(T.copies_one)](#t-copies_one) より $\mathrm{cp}_{d_0}(B,1)=B$ である。
    $B = \mathrm{dropLast}(B\mathbin{+\!\!+}[lp])$（`List.dropLast_concat`）であり、$B\mathbin{+\!\!+}[lp]\ne[]$ だから、
    仮定 $\mathrm{cnf}(\mathrm{tr}(B\mathbin{+\!\!+}[lp]))$ に [(T.cnf_dropLast)](#t-cnf_dropLast) を適用して
    $\mathrm{cnf}(\mathrm{tr}\,B)$ を得る。よって $\Phi(1)$。
  - **$n=m+1$ のとき（示すのは $\Phi(m+2)$）。** 以下 $S_m := R\mathbin{+\!\!+}\mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(B,m))$ と書く。

    [(T.copies_succ_cons)](#t-copies_succ_cons) より
    $$\mathrm{cp}_{d_0}(B,m+1) = (v_0,w_0)\mathbin{::}S_m, \tag{cp}$$
    したがって [(T.shiftr0_cons)](#t-shiftr0_cons) より
    $$\mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(B,m+1)\bigr) = (v_0+d_0,\ w_0)\mathbin{::}\mathrm{sh}_{d_0}S_m . \tag{z1}$$
    [(T.copies_tl_gt)](#t-copies_tl_gt)（$n:=m+1$、その $n-1$ が $m$）より
    $$\forall x\in S_m,\ v_0<\pi_0 x . \tag{tlgt}$$
    (cp) と (tlgt) に [(T.translate_single_tree)](Mechanized.md#t-translate_single_tree) を適用して
    $$\mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B,m+1)\bigr) = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S_m,\ \mathsf{Z}\bigr), \tag{st1}$$
    (z1) と [(T.translate_shiftr0)](#t-translate_shiftr0) より
    $$\mathrm{tr}\bigl((v_0+d_0,w_0)\mathbin{::}\mathrm{sh}_{d_0}S_m\bigr)
     = \mathrm{tr}\bigl(\mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(B,m+1))\bigr)
     = \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B,m+1)\bigr)
     = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S_m,\ \mathsf{Z}\bigr). \tag{tZ1}$$
    また [(D.translate)](Mechanized.md#d-translate) より $\mathrm{tr}[lp] = \mathsf{P}(\pi_1 lp,\mathsf{Z},\mathsf{Z})$。

    [(T.cnf_ctx_cong)](#t-cnf_ctx_cong) を次のデータで適用する。

    - $z_1 := (v_0+d_0,\ w_0)$、$T_1 := \mathrm{sh}_{d_0}S_m$、$z_2 := lp$、$T_2 := []$、$G := B$。
    - $cZ_1$：(z1) と [(T.translate_shiftr0)](#t-translate_shiftr0) より
      $\mathrm{tr}(z_1\mathbin{::}T_1) = \mathrm{tr}(\mathrm{cp}_{d_0}(B,m+1))$ であり、
      これは帰納法の仮定 $\Phi(m+1)$ が $\mathrm{cnf}$ を主張する項である。
    - decr：(tZ1) と $\mathrm{tr}[lp]=\mathsf{P}(\pi_1 lp,\mathsf{Z},\mathsf{Z})$、および仮定 $w_0<\pi_1 lp$ に
      [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 1 選言を用いて
      $\mathrm{tr}(z_1\mathbin{::}T_1) \prec \mathrm{tr}(lp\mathbin{::}[])$。
    - root：$\pi_0 z_1 = v_0+d_0 = \pi_0 lp$（仮定 $\pi_0 lp = v_0+d_0$）。
    - leadle：証人を $a_1:=w_0$, $b_1:=\mathrm{tr}\,S_m$, $c_1:=\mathsf{Z}$,
      $a_2:=\pi_1 lp$, $b_2:=\mathsf{Z}$, $c_2:=\mathsf{Z}$ とすると、
      2 つの等式は (tZ1) と $\mathrm{tr}[lp]=\mathsf{P}(\pi_1 lp,\mathsf{Z},\mathsf{Z})$ であり、
      $\mathsf{P}(w_0,\mathrm{tr}\,S_m,\mathsf{Z}) \preceq \mathsf{P}(\pi_1 lp,\mathsf{Z},\mathsf{Z})$ は
      $w_0<\pi_1 lp$ と [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 1 選言による。
    - $r_1$：$x\in\mathrm{sh}_{d_0}S_m$ とすると [(T.mem_shiftr0)](#t-mem_shiftr0) よりある $p\in S_m$ について
      $x=(\pi_0 p+d_0,\ \pi_1 p)$ であり、(tlgt) より $v_0\le\pi_0 p$、したがって
      $\pi_0 z_1 = v_0+d_0 \le \pi_0 p+d_0 = \pi_0 x$。
    - $r_2$：$T_2=[]$ であるから前件が偽で成立する。
    - $hG_2$：仮定 $\mathrm{cnf}(\mathrm{tr}(B\mathbin{+\!\!+}[lp]))$ は $[lp]=lp\mathbin{::}[]$ により
      $\mathrm{cnf}(\mathrm{tr}(G\mathbin{+\!\!+}z_2\mathbin{::}T_2))$ そのものである。

    結論として
    $\mathrm{cnf}\bigl(\mathrm{tr}(B\mathbin{+\!\!+}(v_0+d_0,w_0)\mathbin{::}\mathrm{sh}_{d_0}S_m)\bigr)$ を得る。
    他方 [(T.copies_succ_front)](#t-copies_succ_front) と (z1) より
    $$\mathrm{cp}_{d_0}(B,m+2) = B\mathbin{+\!\!+}\mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(B,m+1)\bigr)
     = B\mathbin{+\!\!+}(v_0+d_0,w_0)\mathbin{::}\mathrm{sh}_{d_0}S_m$$
    であるから、これは $\Phi(m+2)$ にほかならない。∎

<a id="t-cnf_oper_i1eq1"></a>
### 定理 $\mathrm{cnf}$ の保存：昇順コピー（$i_1=1$）の場合 (T.cnf_oper_i1eq1)

**主張** $v_0,w_0,d_0\in\mathbb{N}$、ペア列 $R,G$、対 $lp$、$n\in\mathbb{N}$ が
$$\forall x\in R,\ v_0<\pi_0 x,\quad 0<d_0,\quad w_0<\pi_1 lp,\quad \pi_0 lp=v_0+d_0,\quad 1\le n,$$
$$\mathrm{cnf}\Bigl(\mathrm{tr}\bigl(G\mathbin{+\!\!+}((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}[lp]\bigr)\Bigr)$$
をみたすならば
$$\mathrm{cnf}\Bigl(\mathrm{tr}\bigl(G\mathbin{+\!\!+}\mathrm{cp}_{d_0}((v_0,w_0)\mathbin{::}R,\ n)\bigr)\Bigr).$$

**証明** $B:=(v_0,w_0)\mathbin{::}R$ とおく。$1\le n$ より $n=m+1$ と書ける。
$0<d_0$ と $\pi_0 lp = v_0+d_0$ より
$$lpv : v_0 < \pi_0 lp .$$
また $R\mathbin{+\!\!+}[lp]$ の全要素 $x$ は $v_0<\pi_0 x$ をみたす（$x\in R$ なら仮定、$x=lp$ なら $lpv$）。
以下 $S_m := R\mathbin{+\!\!+}\mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(B,m))$ と書く。

**(1) 悪い分岐の核による減少.** 次を示す。
$$\text{decr} : \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B,m+1)\bigr) \prec \mathrm{tr}\bigl(B\mathbin{+\!\!+}[lp]\bigr). \tag{decr}$$
$m$ の形で分ける。

- $m=0$：[(T.copies_one)](#t-copies_one) より $\mathrm{cp}_{d_0}(B,1)=B$ であり、
  [(T.translate_snoc_increase)](Mechanized.md#t-translate_snoc_increase) より
  $\mathrm{tr}\,B \prec \mathrm{tr}(B\mathbin{+\!\!+}[lp])$。
- $m=m'+1$：[(T.copies_succ_cons)](#t-copies_succ_cons) と [(T.shiftr0_cons)](#t-shiftr0_cons) より
  $$\mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(B,m'+1)\bigr) = (v_0+d_0,\ w_0)\mathbin{::}\mathrm{sh}_{d_0}S_{m'} ,$$
  したがって [(T.copies_succ_front)](#t-copies_succ_front) より
  $$\mathrm{cp}_{d_0}(B,m'+2) = B\mathbin{+\!\!+}\bigl((v_0+d_0,w_0)\mathbin{::}\mathrm{sh}_{d_0}S_{m'}\bigr). \tag{e}$$
  ここで [(T.core_i1)](Mechanized.md#t-core_i1) を
  $R:=R$, $c:=(v_0+d_0,\ w_0)$, $C':=\mathrm{sh}_{d_0}S_{m'}$, $lp:=lp$ として適用する。
  その 5 つの仮定は次のように満たされる。
  - $\forall x\in R,\ v_0<\pi_0 x$：本定理の仮定。
  - $\forall x\in C',\ \pi_0 c\le\pi_0 x$：$x\in\mathrm{sh}_{d_0}S_{m'}$ なら
    [(T.mem_shiftr0)](#t-mem_shiftr0) よりある $p\in S_{m'}$ について $x=(\pi_0 p+d_0,\pi_1 p)$ であり、
    [(T.copies_tl_gt)](#t-copies_tl_gt)（$n:=m'+1$）より $v_0<\pi_0 p$、
    したがって $\pi_0 c = v_0+d_0 \le \pi_0 p+d_0 = \pi_0 x$。
  - $\pi_0 c=\pi_0 lp$：$\pi_0 c = v_0+d_0 = \pi_0 lp$。
  - $v_0<\pi_0 lp$：$lpv$。
  - $\pi_1 c<\pi_1 lp$：$\pi_1 c = w_0$ と仮定 $w_0<\pi_1 lp$。

  結論は $\mathrm{tr}\bigl(B\mathbin{+\!\!+}(c\mathbin{::}C')\bigr) \prec \mathrm{tr}(B\mathbin{+\!\!+}[lp])$ であり、
  (e) によりこれが (decr) である。

**(2) 2 つの列の $\mathsf{P}$ 表示.**
[(T.copies_succ_cons)](#t-copies_succ_cons) より $\mathrm{cp}_{d_0}(B,m+1) = (v_0,w_0)\mathbin{::}S_m$ であり、
[(T.copies_tl_gt)](#t-copies_tl_gt)（$n:=m+1$）より $\forall x\in S_m,\ v_0<\pi_0 x$。
[(T.translate_single_tree)](Mechanized.md#t-translate_single_tree) より
$$\mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B,m+1)\bigr) = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S_m,\ \mathsf{Z}\bigr), \tag{st1}$$
$$\mathrm{tr}\bigl(B\mathbin{+\!\!+}[lp]\bigr) = \mathrm{tr}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp])\bigr)
 = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R\mathbin{+\!\!+}[lp]),\ \mathsf{Z}\bigr). \tag{st2}$$

**(3) ブロックの $\mathrm{cnf}$.**
$r_T : \forall x\in R\mathbin{+\!\!+}[lp],\ v_0\le\pi_0 x$ は上に示した狭義不等式から従う。
仮定の $\mathrm{cnf}$ は結合の付け替え
$G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp] = G\mathbin{+\!\!+}(v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp])$ により
$cM' : \mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}(v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp]))\bigr)$ と書ける。
[(T.cnf_tail)](#t-cnf_tail) より
$$cB_{lp} : \mathrm{cnf}\bigl(\mathrm{tr}(B\mathbin{+\!\!+}[lp])\bigr),$$
[(T.cnf_copies)](#t-cnf_copies) より
$$cC : \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{cp}_{d_0}(B,m+1))\bigr).$$

**(4) 引数どうしの比較.** (decr) を (st1), (st2) で書き換え、
[(T.olt_P_P)](Mechanized.md#t-olt_P_P) で 3 つに分ける。
第 1 の場合は $w_0<w_0$ で自然数の $<$ の非反射性により偽、
第 3 の場合は $\mathsf{Z}\prec\mathsf{Z}$ を含み [(T.not_olt_Z)](Mechanized.md#t-not_olt_Z) に反する。
よって第 2 の場合が成り立ち
$$\text{argA} : \mathrm{tr}\,S_m \prec \mathrm{tr}(R\mathbin{+\!\!+}[lp]).$$

**(5) 結論.** [(T.cnf_ctx_cong)](#t-cnf_ctx_cong) を次のデータで適用する。

- $z_1 := (v_0,w_0)$、$T_1 := S_m$、$z_2 := (v_0,w_0)$、$T_2 := R\mathbin{+\!\!+}[lp]$、$G := G$。
- $cZ_1$：$\mathrm{tr}((v_0,w_0)\mathbin{::}S_m) = \mathrm{tr}(\mathrm{cp}_{d_0}(B,m+1))$ であり $cC$。
- decr：(decr) を $\mathrm{cp}_{d_0}(B,m+1) = (v_0,w_0)\mathbin{::}S_m$ と
  $B\mathbin{+\!\!+}[lp] = (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp])$ で書き換えたもの。
- root：$\pi_0 z_1=\pi_0 z_2$（同一の対）。
- leadle：証人を $a_1=a_2:=w_0$, $b_1:=\mathrm{tr}\,S_m$, $b_2:=\mathrm{tr}(R\mathbin{+\!\!+}[lp])$,
  $c_1=c_2:=\mathsf{Z}$ とし、2 つの等式は (st1), (st2)、
  $\mathsf{P}(w_0,\mathrm{tr}\,S_m,\mathsf{Z}) \preceq \mathsf{P}(w_0,\mathrm{tr}(R\mathbin{+\!\!+}[lp]),\mathsf{Z})$ は
  argA と [(T.olt_P_b)](Mechanized.md#t-olt_P_b) による。
- $r_1$：$\forall x\in S_m,\ v_0\le\pi_0 x$（(2) の狭義不等式から）。
- $r_2$：$r_T$。
- $hG_2$：$cM'$。

結論として $\mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}(v_0,w_0)\mathbin{::}S_m)\bigr)$ を得る。
$(v_0,w_0)\mathbin{::}S_m = \mathrm{cp}_{d_0}(B,m+1)$ であるから、これが求める主張である。∎

<a id="t-copies_replicate"></a>
### 定理 $d=0$ のコピーは完全コピー (T.copies_replicate)

**主張** 任意のペア列 $B$、$n\in\mathbb{N}$ に対し
$$\mathrm{cp}_0(B,n) = \mathrm{flatten}\ \mathrm{replicate}(n,B).$$

**証明** 任意の $k\in\mathbb{N}$ について $k\cdot0=0$ であり、
[(T.shiftr0_zero)](#t-shiftr0_zero) より $\mathrm{sh}_{k\cdot0}B = B$ である。
よって [(D.copies)](#d-copies) の被 $\mathrm{flatMap}$ 関数は定数関数 $\lambda k.\ B$ であり
$$\mathrm{cp}_0(B,n) = \mathrm{flatMap}\ (\lambda k.\ B)\ \mathrm{range}(n).$$
`List.flatMap_def`（$\mathrm{flatMap}\ f\ l = \mathrm{flatten}(\mathrm{map}\ f\ l)$）、
`List.map_const'`（$\mathrm{map}\ (\lambda\_.\ b)\ l = \mathrm{replicate}(\lvert l\rvert,\ b)$）、
`List.length_range`（$\lvert\mathrm{range}(n)\rvert=n$）より、これは
$\mathrm{flatten}\ \mathrm{replicate}(n,B)$ に等しい。∎

<a id="t-cnf_oper"></a>
### 定理 展開一段は $\mathrm{cnf}$ を保つ (T.cnf_oper)

**主張** $1\le n$ かつ $\mathrm{cnf}(\mathrm{tr}\,M)$ ならば $\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)$。

**証明** $j_1:=\lvert M\rvert-1$、$i_1:=\mathrm{idx1}\,M\,j_1$（[(D.idx1)](Def.md#d-idx1)）とおく。

**$j_1=0$ のとき。** [(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) より $M[n]=M$ であり、
結論は仮定 $\mathrm{cnf}(\mathrm{tr}\,M)$ そのものである。

**$j_1\ne0$ のとき。** 切り捨て減法より $\lvert M\rvert-1\ne0$ は $1<\lvert M\rvert$ を意味する。
とくに $M\ne[]$ であり、[(D.Pred)](Def.md#d-Pred) より $\mathrm{Pred}\,M=\mathrm{dropLast}\,M$ である。
[(D.oper)](Def.md#d-oper) の残り 3 分岐で場合分けする。

- **$M_{0,j_1}=0\wedge M_{1,j_1}=0$ のとき。**
  [(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero) より $M[n]=\mathrm{dropLast}\,M$ であり、
  $M\ne[]$ と仮定 $\mathrm{cnf}(\mathrm{tr}\,M)$ に [(T.cnf_dropLast)](#t-cnf_dropLast) を適用すればよい。
- **$\neg(M_{0,j_1}=0\wedge M_{1,j_1}=0)$ かつ $\neg\,\mathrm{hasParent}\,M\,i_1\,j_1$ のとき。**
  [(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent) より $M[n]=\mathrm{dropLast}\,M$ であり、
  同じく [(T.cnf_dropLast)](#t-cnf_dropLast) を適用すればよい。
- **$\neg(M_{0,j_1}=0\wedge M_{1,j_1}=0)$ かつ $\mathrm{hasParent}\,M\,i_1\,j_1$ のとき。**
  [(T.oper_bad_blocks)](Mechanized.md#t-oper_bad_blocks) を適用して
  ペア列 $G,R$、自然数 $v_0,w_0,d_0$、対 $lp$ を取る。$B:=(v_0,w_0)\mathbin{::}R$ とおくと、条件 1, 2, 3, 4, 5 より

  1. $M = G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp]$
  2. $M[n] = G\mathbin{+\!\!+}\mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}\,(\lambda p.\ (\pi_0 p+k\,d_0,\ \pi_1 p))\ B\bigr)\ \mathrm{range}(n)$
  3. $\forall x\in R,\ v_0<\pi_0 x$
  4. $v_0<\pi_0 lp$
  5. $\bigl(d_0=0\wedge i_1=0\bigr)\ \vee\ \bigl(0<d_0\wedge w_0<\pi_1 lp\wedge \pi_0 lp=v_0+d_0\wedge\cdots\bigr)$

  である。ここで条件 2 の $\mathrm{flatMap}$ の被関数は
  $\lambda k.\ \mathrm{map}\ \sigma_{k\,d_0}\ B = \lambda k.\ \mathrm{sh}_{k\,d_0}B$ であるから、
  [(D.copies)](#d-copies) より条件 2 は
  $$M[n] = G\mathbin{+\!\!+}\mathrm{cp}_{d_0}(B,\ n)$$
  と書ける。条件 1 により仮定は
  $cM' : \mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}B\mathbin{+\!\!+}[lp])\bigr)$ である。
  条件 5 の 2 つの選言で分ける。
  - $d_0=0$（かつ $i_1=0$）のとき：[(T.copies_replicate)](#t-copies_replicate) より
    $\mathrm{cp}_0(B,n) = \mathrm{flatten}\ \mathrm{replicate}(n,B)$ であり、
    [(T.cnf_oper_i1eq0)](#t-cnf_oper_i1eq0) を条件 3、条件 4、$1\le n$、$cM'$ に適用して結論を得る。
  - $0<d_0$、$w_0<\pi_1 lp$、$\pi_0 lp=v_0+d_0$ のとき：
    [(T.cnf_oper_i1eq1)](#t-cnf_oper_i1eq1) を条件 3、これら 3 つ、$1\le n$、$cM'$ に適用して結論を得る。

3 つの場合は（$j_1\ne0$ の下で）[(D.oper)](Def.md#d-oper) の全分岐を尽くしている。∎

<a id="t-cnf_ST_PS"></a>
### 定理 標準形の翻訳は $\mathrm{cnf}$ (T.cnf_ST_PS)

**主張** $M\in\mathrm{ST\_PS}$ ならば $\mathrm{cnf}(\mathrm{tr}\,M)$。

**証明** $\mathrm{ST\_PS}$ の生成（[(D.ST_PS)](Def.md#d-ST_PS)）に関する帰納法。帰納法の述語は

$$\Phi(M) :\equiv \mathrm{cnf}(\mathrm{tr}\,M).$$

- 基底段（規則 (diag)）：$M=\Delta_0^v$ の形である。
  [(T.cnf_diag)](#t-cnf_diag) より $\mathrm{cnf}(\mathrm{tr}(\Delta_0^v))$、すなわち $\Phi(\Delta_0^v)$。
- 帰納段（規則 (oper)）：$M\in\mathrm{ST\_PS}$、$1\le n$ とし、帰納法の仮定として $\Phi(M)$、すなわち
  $\mathrm{cnf}(\mathrm{tr}\,M)$ を仮定する。[(T.cnf_oper)](#t-cnf_oper) を $1\le n$ とこの仮定に適用して
  $\mathrm{cnf}(\mathrm{tr}(M[n]))$、すなわち $\Phi(M[n])$ を得る。

[(D.ST_PS)](Def.md#d-ST_PS) の帰納法原理により、$\mathrm{ST\_PS}$ のすべての要素 $M$ について $\Phi(M)$。∎

<a id="d-tops"></a>
### 定義 先頭和の添字列 (D.tops)

$\mathrm{tops}:\mathrm{Three}\to\mathbb{N}^{<\omega}$ を項の構造帰納で定める。

$$\mathrm{tops}\,\mathsf{Z} := [],\qquad \mathrm{tops}\,\mathsf{P}(a,b,c) := a\mathbin{::}\mathrm{tops}\,c .$$

すなわち項を主要項の和と読んだときの、各主要項の添字を先頭から並べた列である。
$\mathrm{sp}$（[(D.spine)](#d-spine)）が第 2 引数（引数）をたどるのに対し、$\mathrm{tops}$ は第 3 引数（後続和）をたどる。

<a id="t-tops_Z"></a>
### 定理 $\mathsf{Z}$ の $\mathrm{tops}$ (T.tops_Z)

**主張** $\mathrm{tops}\,\mathsf{Z} = []$。

**証明** [(D.tops)](#d-tops) の第 1 式であり、両辺は定義により同一である。∎

<a id="t-tops_P"></a>
### 定理 $\mathsf{P}$ の $\mathrm{tops}$ (T.tops_P)

**主張** $\mathrm{tops}\,\mathsf{P}(a,b,c) = a\mathbin{::}\mathrm{tops}\,c$。

**証明** [(D.tops)](#d-tops) の第 2 式であり、両辺は定義により同一である。∎

<a id="t-cnf_tops_le"></a>
### 定理 $\mathrm{cnf}$ 項では先頭添字が全兄弟添字の上界 (T.cnf_tops_le)

**主張** $\mathrm{cnf}\,\mathsf{P}(a,b,c)$ ならば $\forall s\in\mathrm{tops}\,c,\ s\le a$。

**証明** $c$ の構造に関する帰納法（$a,b$ は全称量化したまま動かす）。帰納法の述語は

$$\Phi(c) :\equiv \forall a\in\mathbb{N},\ \forall b\in\mathrm{Three},\
 \mathrm{cnf}\,\mathsf{P}(a,b,c) \to \forall s\in\mathrm{tops}\,c,\ s\le a .$$

- 基底段 $c=\mathsf{Z}$：[(T.tops_Z)](#t-tops_Z) より $\mathrm{tops}\,\mathsf{Z}=[]$ であり、
  $s\in[]$ は偽であるから前件が偽で $\Phi(\mathsf{Z})$ が成り立つ。
- 帰納段 $c=\mathsf{P}(e,f,g)$：帰納法の仮定は $\Phi(f)$ と $\Phi(g)$ である（使うのは $\Phi(g)$ のみ）。
  $a,b$ を取り $\mathrm{cnf}\,\mathsf{P}(a,b,\mathsf{P}(e,f,g))$ を仮定する。
  [(T.cnf_P_P)](#t-cnf_P_P) よりその 3 成分
  $$\mathrm{cnf}\,b,\qquad
    \text{nlt} : \neg\bigl(\mathsf{P}(a,b,\mathsf{Z})\prec\mathsf{P}(e,f,\mathsf{Z})\bigr),\qquad
    cg : \mathrm{cnf}\,\mathsf{P}(e,f,g)$$
  が得られる。まず $e\le a$ を示す。$e\le a$ でないとすると $a<e$ であり、
  [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 1 選言により
  $\mathsf{P}(a,b,\mathsf{Z})\prec\mathsf{P}(e,f,\mathsf{Z})$ となって nlt に矛盾する。よって
  $$ea : e\le a .$$
  次に $s\in\mathrm{tops}\,\mathsf{P}(e,f,g)$ を取る。[(T.tops_P)](#t-tops_P) より
  $\mathrm{tops}\,\mathsf{P}(e,f,g) = e\mathbin{::}\mathrm{tops}\,g$ であるから、$s=e$ か $s\in\mathrm{tops}\,g$ である。
  - $s=e$ のとき：$ea$ より $s\le a$。
  - $s\in\mathrm{tops}\,g$ のとき：帰納法の仮定 $\Phi(g)$ を $a:=e$, $b:=f$ とし $cg$ に適用して $s\le e$、
    $ea$ とあわせて $s\le e\le a$。

  よって $\Phi(\mathsf{P}(e,f,g))$。∎

## 整礎性の最大添字レベル内への還元

Lean 側ではこの節見出しの下に宣言はない。置かれているのは、以降の章で行う議論の方針を述べたコメントのみである。
その内容は次の通りである。$\mathrm{Rnf}$（[(D.Rnf)](Proofs.md#d-Rnf)、$\mathrm{NF}$
（[(D.NF)](Proofs.md#d-NF)）上に制限した $\prec$）の整礎性を、
$\mathrm{maxsub}$（[(D.maxsub)](#d-maxsub)）を第 1 成分とする辞書式積に沿って
「$\mathrm{maxsub}$ が真に減る部分」と「$\mathrm{maxsub}$ が等しい部分」に分け、後者だけを残った課題とする、というものである。

<!-- 注意（本文の忠実性のため明記する）:
Lean のこのコメントは識別子 `maxsub_mono_NF'` を引いているが、
その名前の宣言はリポジトリ内のどの `.lean` ファイルにも存在しない（コメント中にのみ現れる）。
したがってここでは、そのコメントが述べる命題を本文の定理として掲げることはしない。
実際の停止性証明が取った経路は本章の下流の章（Cofinality, Wset, AscArg, Final）で与えられる。 -->

この見出しの下に宣言はないので、本章はここで終わる。
