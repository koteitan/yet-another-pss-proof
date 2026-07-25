[← 目次](README.md)

# Proofs — 停止性の還元：一段の減少 + 像側の整礎性 ⟹ 展開関係の整礎性

翻訳 $\mathrm{tr}$（[(D.translate)](Mechanized.md#d-translate)）による標準形の像 $\mathrm{NF}$、その上の順序
$\prec_{\mathrm{NF}}$、および標準形上の 1 ステップ関係 $\lhd$ を定義する。
そのうえで「(dec) 展開一段は $\mathrm{tr}$ を真に減少させる」と「(wfimg) $\prec_{\mathrm{NF}}$ が整礎である」の 2 つから
$\lhd$ の整礎性（＝標準形の無限展開列の非存在）が従うことを示し、
さらに (dec) を [(T.m_step_decreases)](Mechanized.md#t-m_step_decreases) で解消して、
停止性を (wfimg) ただ一つへ還元する。
本章の宣言は 8 個（定義 3、定理 5）である。

## 記法

この章で導入する Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `NF` | $\mathrm{NF}$ | 標準形の $\mathrm{tr}$ による像 |
| `Rnf v u` | $v \prec_{\mathrm{NF}} u$ | $\mathrm{NF}$ 上に制限した $\prec$ |
| `stepRel T M` | $T \lhd M$ | 標準形上の 1 ステップ関係 |

他章で定義済みの記号、および Lean の標準的な述語については次のように書く。

| Lean | 本文 | 意味 |
|---|---|---|
| `Three` | $\mathrm{Three}$ | 三分岐記法の項の型（[(D.Three)](Mechanized.md#d-Three)） |
| `x <o y` | $x \prec y$ | 添字優先辞書式順序（[(D.olt)](Mechanized.md#d-olt)） |
| `translate M` | $\mathrm{tr}\,M$ | 翻訳（[(D.translate)](Mechanized.md#d-translate)） |
| `M.length` | $\lvert M\rvert$ | 長さ |
| `M⟦n⟧` | $M[n]$ | 展開（[(D.oper)](Def.md#d-oper)） |
| `ST_PS M` | $M \in \mathrm{ST\_PS}$ | 標準形（[(D.ST_PS)](Def.md#d-ST_PS)） |
| `step M N` | $M \Rightarrow N$ | 1 ステップ展開（[(D.step)](Def.md#d-step)） |
| `diagSeq 0 v` | $\Delta_0^v$ | 対角列（[(D.diagSeq)](Def.md#d-diagSeq)） |
| `Acc r x` | $\mathrm{Acc}(r,x)$ | $x$ が $r$ について到達可能（下記 [(F.Acc)](#f-Acc)） |
| `WellFounded r` | $\mathrm{WF}(r)$ | $r$ が整礎（下記 [(F.WellFounded)](#f-WellFounded)） |
| `InvImage r f` | $r^{f}$ | 写像 $f$ による $r$ の逆像関係（下記 [(F.InvImage)](#f-InvImage)） |

**引数の向きの規約.** 本章に現れる関係 $r$ はすべて「$r\,y\,x$ は $y$ が $x$ の**下**にある」と読む。
Isabelle 版の $(y,x)\in r$ に対応する。したがって $\lhd$ と $\prec_{\mathrm{NF}}$ の第 1 引数が小さい側、
第 2 引数が大きい側である。

---

## 準備：到達可能性と整礎性についての標準事実

本章の証明はすべて、Lean の標準的な述語 `Acc` / `WellFounded` とその 3 つの補題
（`Acc.inv`, `InvImage.wf`, `Subrelation.wf`）の上に立つ。それらの内容と証明をここに固定しておく。
この節の 5 項目は本モジュールの宣言ではないので、ラベルには本章の他の項目と区別して `F.` を用いる。

<a id="f-Acc"></a>
### 事実 到達可能性とその帰納法原理 (F.Acc)

型 $\alpha$ 上の関係 $r : \alpha \to \alpha \to \mathrm{Prop}$ に対し、述語
$\mathrm{Acc}(r,\cdot) : \alpha \to \mathrm{Prop}$ を、次の 1 つの導入規則で生成される**最小の**述語と定める。

```math
\frac{\ \forall y,\ r\,y\,x \to \mathrm{Acc}(r,y)\ }{\ \mathrm{Acc}(r,x)\ }\ \text{(intro)}
```

最小性は次の形で使う（Lean の `Acc.rec`）。述語 $Q : \alpha \to \mathrm{Prop}$ が

```math
\forall x,\ \Bigl(\forall y,\ r\,y\,x \to \mathrm{Acc}(r,y)\Bigr) \to
\Bigl(\forall y,\ r\,y\,x \to Q(y)\Bigr) \to Q(x)
```

をみたすならば、$\forall x,\ \mathrm{Acc}(r,x) \to Q(x)$ が成り立つ。
以下で「$\mathrm{Acc}(r,x)$ の導出に関する帰納法」と書いたときはこの原理を指す。
帰納法の仮定は $\forall y,\ r\,y\,x \to Q(y)$ の部分であり、
それに加えて $\forall y,\ r\,y\,x \to \mathrm{Acc}(r,y)$ も使ってよい。

**基底段と帰納段の区別.** 導入規則が 1 つしかないため、この帰納法の場合分けも 1 つである。
その中で、$x$ が $r$ の極小元である場合、すなわち

```math
\neg\,\exists y,\ r\,y\,x
```

の場合を**基底段**と呼ぶ。このとき帰納法の仮定 $\forall y,\ r\,y\,x \to Q(y)$ は前件が常に偽であり、
内容を持たない。以下の各帰納法では、基底段が帰納段の特別な場合としてどう処理されるかを個別に書く。

<a id="f-WellFounded"></a>
### 事実 整礎性 (F.WellFounded)

```math
\mathrm{WF}(r) \ :\iff\ \forall x,\ \mathrm{Acc}(r,x).
```

Lean では `WellFounded` は構成子 `intro : (∀ a, Acc r a) → WellFounded r` をもつ構造であり、
逆向きの取り出しが `WellFounded.apply : WellFounded r → ∀ a, Acc r a` である。
本文ではこの往復を明示せず、$\mathrm{WF}(r)$ と $\forall x,\ \mathrm{Acc}(r,x)$ を同じ主張として扱う。

<a id="f-Acc_inv"></a>
### 事実 到達可能性の下方遺伝 (F.Acc_inv)

**主張** $\mathrm{Acc}(r,x)$ かつ $r\,y\,x$ ならば $\mathrm{Acc}(r,y)$。

**証明** $\mathrm{Acc}(r,x)$ の導出は [(F.Acc)](#f-Acc) の唯一の導入規則によるものだから、
ある $h : \forall z,\ r\,z\,x \to \mathrm{Acc}(r,z)$ が存在して導出は $\text{(intro)}$ の適用である。
この $h$ を $z := y$ と仮定 $r\,y\,x$ に適用して $\mathrm{Acc}(r,y)$ を得る。∎

<a id="f-InvImage"></a>
### 事実 逆像関係とその整礎性 (F.InvImage)

$f : \alpha \to \beta$ と $r : \beta\to\beta\to\mathrm{Prop}$ に対し、$\alpha$ 上の関係 $r^{f}$ を

```math
r^{f}\,a\,b \ :\iff\ r\,(f\,a)\,(f\,b)
```

で定める（Lean の `InvImage r f`）。

**主張** $\mathrm{WF}(r) \Longrightarrow \mathrm{WF}(r^{f})$。

**証明** 述語 $Q : \beta \to \mathrm{Prop}$ を

```math
Q(y) \ :\equiv\ \forall a \in \alpha,\ f\,a = y \to \mathrm{Acc}(r^{f}, a)
```

とおき、$\forall y,\ \mathrm{Acc}(r,y)\to Q(y)$ を $\mathrm{Acc}(r,y)$ の導出に関する帰納法
（[(F.Acc)](#f-Acc)）で示す。

帰納段は次の形である。$y \in \beta$ をとり、帰納法の仮定

```math
\mathrm{IH} :\ \forall z \in \beta,\ r\,z\,y \to Q(z)
```

を仮定して $Q(y)$ を示す。$a \in \alpha$ と $f\,a = y$ を仮定し、$\mathrm{Acc}(r^{f},a)$ を示す。
[(F.Acc)](#f-Acc) の導入規則により、$\forall a',\ r^{f}\,a'\,a \to \mathrm{Acc}(r^{f},a')$ を示せばよい。
そこで $a'$ が $r^{f}\,a'\,a$、すなわち定義により $r\,(f\,a')\,(f\,a)$ をみたすとする。
$f\,a = y$ だからこれは $r\,(f\,a')\,y$ である。$\mathrm{IH}$ を $z := f\,a'$ に適用して $Q(f\,a')$ を得、
さらに $Q$ の定義を $a := a'$、等式 $f\,a' = f\,a'$（反射性）に適用して $\mathrm{Acc}(r^{f},a')$ を得る。

基底段（$y$ が $r$ の極小元、すなわち $r\,z\,y$ なる $z$ が存在しない場合、[(F.Acc)](#f-Acc)）は
上の帰納段の特別な場合であり、そこでは $\mathrm{IH}$ が使われない形になる。実際その場合、
上で $a'$ について得た $r\,(f\,a')\,y$ は
$z := f\,a'$ の存在を与えて極小性に反するから、$r^{f}\,a'\,a$ をみたす $a'$ は存在せず、
$\mathrm{Acc}(r^{f},a)$ は [(F.Acc)](#f-Acc) の導入規則の前提が空虚に成り立つ形で得られる。

以上で $\forall y,\ \mathrm{Acc}(r,y)\to Q(y)$ が示された。
いま $\mathrm{WF}(r)$ を仮定すると、任意の $a\in\alpha$ について $\mathrm{Acc}(r, f\,a)$ が成り立つから
$Q(f\,a)$ が成り立ち、これを $a$ と $f\,a = f\,a$ に適用して $\mathrm{Acc}(r^{f},a)$ を得る。
$a$ は任意だったから $\mathrm{WF}(r^{f})$ である。∎

<a id="f-Subrelation"></a>
### 事実 部分関係の整礎性 (F.Subrelation)

**主張** $q, r$ を $\alpha$ 上の関係とする。
$\bigl(\forall x\,y,\ q\,x\,y \to r\,x\,y\bigr)$ かつ $\mathrm{WF}(r)$ ならば $\mathrm{WF}(q)$。

**証明** まず $\forall x,\ \mathrm{Acc}(r,x) \to \mathrm{Acc}(q,x)$ を、$\mathrm{Acc}(r,x)$ の導出に関する
帰納法（[(F.Acc)](#f-Acc)、$Q(x) :\equiv \mathrm{Acc}(q,x)$）で示す。
帰納段：$x$ をとり、帰納法の仮定

```math
\mathrm{IH} :\ \forall y,\ r\,y\,x \to \mathrm{Acc}(q,y)
```

を仮定して $\mathrm{Acc}(q,x)$ を示す。[(F.Acc)](#f-Acc) の導入規則により
$\forall y,\ q\,y\,x \to \mathrm{Acc}(q,y)$ を示せばよい。$y$ が $q\,y\,x$ をみたすとすると、
仮定 $\forall x\,y,\ q\,x\,y\to r\,x\,y$ より $r\,y\,x$ であり、$\mathrm{IH}$ から $\mathrm{Acc}(q,y)$ を得る。

基底段（$x$ が $r$ の極小元の場合、[(F.Acc)](#f-Acc)）は上の帰納段の特別な場合であり、
そこでは $\mathrm{IH}$ が使われない形になる。実際その場合、
$q\,y\,x$ をみたす $y$ があれば $r\,y\,x$ となって極小性に反するから、そのような $y$ は存在せず、
$\mathrm{Acc}(q,x)$ は導入規則の前提が空虚に成り立つ形で得られる。

$\mathrm{WF}(r)$ より任意の $x$ について $\mathrm{Acc}(r,x)$ だから、いま示したことから $\mathrm{Acc}(q,x)$。
$x$ は任意だったから $\mathrm{WF}(q)$ である。∎

---

## 標準形の像 $\mathrm{NF}$ と像上の順序 $\prec_{\mathrm{NF}}$

<a id="d-NF"></a>
### 定義 標準形の翻訳像 (D.NF)

$\mathrm{Three}$（[(D.Three)](Mechanized.md#d-Three)）の部分集合 $\mathrm{NF}$ を

```math
\mathrm{NF} := \bigl\{\, t \in \mathrm{Three} \ \bigm|\ \exists M \in \mathrm{PairSeq},\
 M \in \mathrm{ST\_PS} \ \wedge\ \mathrm{tr}\,M = t \,\bigr\}
```

で定める（[(D.PairSeq)](Def.md#d-PairSeq), [(D.ST_PS)](Def.md#d-ST_PS),
[(D.translate)](Mechanized.md#d-translate)）。すなわち $\mathrm{NF}$ は写像 $\mathrm{tr}$ による
$\mathrm{ST\_PS}$ の像である。

この定義から直ちに次の 2 つの使い方が得られる。

- （導入）$M \in \mathrm{ST\_PS}$ ならば $\mathrm{tr}\,M \in \mathrm{NF}$。
  実際、存在量化子の証拠として $M$ 自身を取り、等式は $\mathrm{tr}\,M = \mathrm{tr}\,M$（反射性）でよい。
- （除去）$t \in \mathrm{NF}$ ならば、ある $M$ が存在して $M \in \mathrm{ST\_PS}$ かつ $\mathrm{tr}\,M = t$。

<a id="d-Rnf"></a>
### 定義 像上の順序 (D.Rnf)

$v, u \in \mathrm{Three}$ に対し

```math
v \prec_{\mathrm{NF}} u \ :\iff\ v \prec u \ \wedge\ u \in \mathrm{NF} \ \wedge\ v \in \mathrm{NF}
```

（[(D.olt)](Mechanized.md#d-olt), [(D.NF)](#d-NF)）。すなわち $\prec$ を $\mathrm{NF}$ の内部へ制限した関係である。
第 1 引数 $v$ が小さい側であり、Isabelle 版の $(v,u)\in R_{\mathrm{NF}}$ に対応する。

**注（$\mathrm{NF}$ の外では前者が存在しない）.** $u \notin \mathrm{NF}$ ならば、
$v \prec_{\mathrm{NF}} u$ をみたす $v$ は存在しない。実際、$v \prec_{\mathrm{NF}} u$ は連言の第 2 項として
$u \in \mathrm{NF}$ を含むから、$u \notin \mathrm{NF}$ と矛盾する。
したがって [(F.Acc)](#f-Acc) の導入規則の前提
$\forall v,\ v \prec_{\mathrm{NF}} u \to \mathrm{Acc}(\prec_{\mathrm{NF}}, v)$ は前件が偽で成り立ち、
$\mathrm{Acc}(\prec_{\mathrm{NF}}, u)$ が成り立つ。

<a id="t-oper_eq_self_short"></a>
### 定理 長さ 1 以下の列は展開で動かない (T.oper_eq_self_short)

**主張** $M \in \mathrm{PairSeq}$、$n \in \mathbb{N}$ とする。
```math
\lvert M\rvert \le 1 \ \Longrightarrow\ M[n] = M .
```

**証明** [(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) は
$\lvert M\rvert - 1 = 0$（切り捨て減法）から $M[n] = M$ を与える。よって
$\lvert M\rvert \le 1 \Rightarrow \lvert M\rvert - 1 = 0$ を示せばよい。
$\lvert M\rvert \le 1$ なる自然数 $\lvert M\rvert$ は $0$ か $1$ である。
$\lvert M\rvert = 0$ のとき、切り捨て減法の規約（$a<b$ のとき $a-b=0$）により $0 - 1 = 0$。
$\lvert M\rvert = 1$ のとき $1 - 1 = 0$。いずれの場合も $\lvert M\rvert - 1 = 0$ である。∎

（Lean 側ではこの 2 通りの計算が `omega` に委ねられている。）

---

## $\mathrm{wfimg}$ の対角到達可能性への還元

Lean 原文はこの位置に節見出しコメントを置き、整礎性義務 $\mathrm{WF}(\prec_{\mathrm{NF}})$ が
対角列の到達可能性だけに帰着することを述べている。その内容を主張と証明の形で書いておく。
以下の**注**は本モジュールの宣言ではなく、この節の見通しを与えるものである。

**注（対角到達可能性 $\Rightarrow$ $\mathrm{wfimg}$）.**

```math
\Bigl(\forall v \in \mathbb{N},\ \mathrm{Acc}\bigl(\prec_{\mathrm{NF}},\ \mathrm{tr}\,\Delta_0^v\bigr)\Bigr)
\ \Longrightarrow\ \mathrm{WF}(\prec_{\mathrm{NF}}).
```

*証明.* 左辺を仮定する。

第 1 段：$\forall M,\ M\in\mathrm{ST\_PS} \to \mathrm{Acc}(\prec_{\mathrm{NF}}, \mathrm{tr}\,M)$ を、
[(D.ST_PS)](Def.md#d-ST_PS) の帰納法原理で示す。述語を
$P(M) :\equiv \mathrm{Acc}(\prec_{\mathrm{NF}}, \mathrm{tr}\,M)$ とおく。

- 基底段：$P(\Delta_0^v)$ は仮定そのものである。
- 帰納段：$M \in \mathrm{ST\_PS}$、$P(M)$、$1 \le n$ を仮定して $P(M[n])$ を示す。
  $\lvert M\rvert$ で場合分けする。
  - $\lvert M\rvert \le 1$ のとき。[(T.oper_eq_self_short)](#t-oper_eq_self_short) より $M[n] = M$ であるから
    $\mathrm{tr}(M[n]) = \mathrm{tr}\,M$ であり、$P(M[n])$ は $P(M)$ に他ならない。
  - $1 < \lvert M\rvert$ のとき。[(T.m_step_decreases)](Mechanized.md#t-m_step_decreases) より
    $\mathrm{tr}(M[n]) \prec \mathrm{tr}\,M$。また [(D.ST_PS)](Def.md#d-ST_PS) の規則 (oper) を
    $M \in \mathrm{ST\_PS}$ と $1\le n$ に適用して $M[n] \in \mathrm{ST\_PS}$ を得るから、
    [(D.NF)](#d-NF) の導入により $\mathrm{tr}\,M \in \mathrm{NF}$ かつ $\mathrm{tr}(M[n]) \in \mathrm{NF}$。
    よって [(D.Rnf)](#d-Rnf) の 3 条件がすべて成立し
    $\mathrm{tr}(M[n]) \prec_{\mathrm{NF}} \mathrm{tr}\,M$。
    これと $P(M)$ に [(F.Acc_inv)](#f-Acc_inv) を適用して $P(M[n])$ を得る。

第 2 段：任意の $u \in \mathrm{Three}$ について $\mathrm{Acc}(\prec_{\mathrm{NF}}, u)$ を示す。
$u \in \mathrm{NF}$ か否かで場合分けする。
$u \in \mathrm{NF}$ ならば [(D.NF)](#d-NF) の除去により $M \in \mathrm{ST\_PS}$ と $\mathrm{tr}\,M = u$ を
みたす $M$ が取れ、第 1 段から $\mathrm{Acc}(\prec_{\mathrm{NF}}, u)$。
$u \notin \mathrm{NF}$ ならば [(D.Rnf)](#d-Rnf) の注により $\mathrm{Acc}(\prec_{\mathrm{NF}}, u)$。
[(F.WellFounded)](#f-WellFounded) より $\mathrm{WF}(\prec_{\mathrm{NF}})$ である。$\square$

この注の第 1 段の帰納段が示しているのは、$\mathrm{ST\_PS}$ の 2 つの生成規則のうち展開規則
（$M \mapsto M[n]$）の側は、すでに証明済みの減少補題
[(T.m_step_decreases)](Mechanized.md#t-m_step_decreases) だけで処理できる、ということである。
残るのは基底規則、すなわち対角列 $\Delta_0^v$ の翻訳
$\mathrm{tr}\,\Delta_0^v$ の到達可能性のみである。

<a id="d-stepRel"></a>
### 定義 標準形上の 1 ステップ関係 (D.stepRel)

$T, M \in \mathrm{PairSeq}$ に対し

```math
T \lhd M \ :\iff\ M \in \mathrm{ST\_PS} \ \wedge\ M \Rightarrow T
```

（[(D.ST_PS)](Def.md#d-ST_PS), [(D.step)](Def.md#d-step)）。Isabelle 版の
$\{(T,M) \mid M\in\mathrm{ST\_PS} \wedge M \Rightarrow T\}$ に対応する。
第 1 引数 $T$ が展開後（小さい側）、第 2 引数 $M$ が展開前（大きい側）である。

$\mathrm{WF}(\lhd)$ が本証明全体の目標である。

<a id="t-step_terminates_cond"></a>
### 定理 条件付き停止性 (T.step_terminates_cond)

**主張** 次の 2 つを仮定する。

```math
\text{(dec)}\quad \forall M\,n,\ M\in\mathrm{ST\_PS} \to 1 < \lvert M\rvert \to 1 \le n \to
 \mathrm{tr}(M[n]) \prec \mathrm{tr}\,M ,
```

```math
\text{(wfimg)}\quad \mathrm{WF}(\prec_{\mathrm{NF}}).
```

このとき $\mathrm{WF}(\lhd)$ が成り立つ。

**証明** 逆像関係 $(\prec_{\mathrm{NF}})^{\mathrm{tr}}$（[(F.InvImage)](#f-InvImage)、$f := \mathrm{tr}$）を考える。
定義により

```math
(\prec_{\mathrm{NF}})^{\mathrm{tr}}\,T\,M \ \iff\ \mathrm{tr}\,T \prec_{\mathrm{NF}} \mathrm{tr}\,M .
```

**第 1 段（$\lhd$ は $(\prec_{\mathrm{NF}})^{\mathrm{tr}}$ の部分関係）.**
$T \lhd M$ を仮定して $\mathrm{tr}\,T \prec_{\mathrm{NF}} \mathrm{tr}\,M$ を示す。
[(D.stepRel)](#d-stepRel) より $M \in \mathrm{ST\_PS}$ と $M \Rightarrow T$ が得られる。
[(D.step)](Def.md#d-step) の導入規則は $\text{(step\_oper)}$ ただ一つであるから、
その場合分け原理により、ある $n$ が存在して

```math
1 < \lvert M\rvert,\qquad 1 \le n,\qquad T = M[n]
```

が成り立つ。以下 $T$ を $M[n]$ で置き換える。[(D.Rnf)](#d-Rnf) の 3 条件を順に確かめる。

1. $\mathrm{tr}(M[n]) \prec \mathrm{tr}\,M$：仮定 (dec) を $M$, $n$, $M\in\mathrm{ST\_PS}$,
   $1<\lvert M\rvert$, $1\le n$ に適用して得られる。
2. $\mathrm{tr}\,M \in \mathrm{NF}$：[(D.NF)](#d-NF) の導入を $M \in \mathrm{ST\_PS}$ に適用する。
3. $\mathrm{tr}(M[n]) \in \mathrm{NF}$：[(D.ST_PS)](Def.md#d-ST_PS) の規則 (oper) を
   $M\in\mathrm{ST\_PS}$ と $1\le n$ に適用して $M[n] \in \mathrm{ST\_PS}$ を得、
   これに [(D.NF)](#d-NF) の導入を適用する。

よって $\mathrm{tr}(M[n]) \prec_{\mathrm{NF}} \mathrm{tr}\,M$、すなわち
$(\prec_{\mathrm{NF}})^{\mathrm{tr}}\,T\,M$ である。

**第 2 段（整礎性の移送）.**
仮定 (wfimg) と [(F.InvImage)](#f-InvImage) から $\mathrm{WF}\bigl((\prec_{\mathrm{NF}})^{\mathrm{tr}}\bigr)$。
第 1 段は $\forall T\,M,\ T \lhd M \to (\prec_{\mathrm{NF}})^{\mathrm{tr}}\,T\,M$ であるから、
[(F.Subrelation)](#f-Subrelation) を $q := \lhd$、$r := (\prec_{\mathrm{NF}})^{\mathrm{tr}}$ として適用し
$\mathrm{WF}(\lhd)$ を得る。∎

<a id="t-no_infinite_expansion_cond"></a>
### 定理 条件付き無限展開列の非存在 (T.no_infinite_expansion_cond)

**主張** [(T.step_terminates_cond)](#t-step_terminates_cond) と同じ 2 つの仮定 (dec), (wfimg) の下で、

```math
\neg\ \exists S : \mathbb{N} \to \mathrm{PairSeq},\
 \bigl(\forall i,\ S_i \in \mathrm{ST\_PS}\bigr) \ \wedge\ \bigl(\forall i,\ S_i \Rightarrow S_{i+1}\bigr).
```

**証明** そのような $S$ が存在したとして矛盾を導く。すなわち

```math
h_{\mathrm{S}} : \forall i,\ S_i \in \mathrm{ST\_PS},
\qquad h_{\text{step}} : \forall i,\ S_i \Rightarrow S_{i+1}
```

を仮定する。

**第 1 段.** [(T.step_terminates_cond)](#t-step_terminates_cond) を仮定 (dec), (wfimg) に適用して
$\mathrm{WF}(\lhd)$ を得る。

**第 2 段.** 各 $i$ について $S_{i+1} \lhd S_i$。実際 [(D.stepRel)](#d-stepRel) の 2 条件は
$h_{\mathrm{S}}(i) : S_i \in \mathrm{ST\_PS}$ と $h_{\text{step}}(i) : S_i \Rightarrow S_{i+1}$ そのものである。

**第 3 段（本体）.** 次を示す。

```math
\text{(key)}\qquad \forall x \in \mathrm{PairSeq},\ \mathrm{Acc}(\lhd, x) \to
 \forall i \in \mathbb{N},\ S_i = x \to \bot .
```

$\mathrm{Acc}(\lhd,x)$ の導出に関する帰納法（[(F.Acc)](#f-Acc)）による。帰納法の述語は

```math
Q(x) \ :\equiv\ \forall i \in \mathbb{N},\ S_i = x \to \bot
```

である。帰納段：$x$ をとり、帰納法の仮定

```math
\mathrm{IH} :\ \forall y,\ y \lhd x \to Q(y),
\quad\text{すなわち}\quad \forall y,\ y \lhd x \to \bigl(\forall i,\ S_i = y \to \bot\bigr)
```

を仮定して $Q(x)$ を示す。$i \in \mathbb{N}$ と $S_i = x$ を仮定する。
第 2 段より $S_{i+1} \lhd S_i$ であり、$S_i = x$ で書き換えて $S_{i+1} \lhd x$。
$\mathrm{IH}$ を $y := S_{i+1}$ に適用して $\forall i',\ S_{i'} = S_{i+1} \to \bot$ を得、
これを $i' := i+1$ と等式 $S_{i+1} = S_{i+1}$（反射性）に適用して $\bot$ を得る。

基底段（$x$ が $\lhd$ の極小元、すなわち $y \lhd x$ なる $y$ が存在しない場合、[(F.Acc)](#f-Acc)）は
上の帰納段の特別な場合である。実際その場合、$i$ と $S_i = x$ を仮定すると、上と同じ計算で
$S_{i+1} \lhd x$ が導かれ、これが $y := S_{i+1}$ という証拠を与えて極小性に反するから、
やはり $\bot$ が得られる。これで (key) が示された。

**第 4 段.** 第 1 段の $\mathrm{WF}(\lhd)$ から $\mathrm{Acc}(\lhd, S_0)$（[(F.WellFounded)](#f-WellFounded)）。
(key) を $x := S_0$、この到達可能性、$i := 0$、等式 $S_0 = S_0$ に適用して $\bot$ を得る。
これは仮定した $S$ の存在との矛盾である。∎

---

## 減少条件 $\mathrm{dec}$ の解消

Lean 原文はこの位置に節見出しコメントを置き、証明済みの減少補題によって仮定 (dec) を落とせること、
その結果として停止性が (wfimg) ただ一つに帰着することを述べている。以下の 2 定理がその内容である。

<a id="t-step_terminates"></a>
### 定理 停止性（(wfimg) のみを仮定） (T.step_terminates)

**主張** $\mathrm{WF}(\prec_{\mathrm{NF}})$ ならば $\mathrm{WF}(\lhd)$。

**証明** [(T.step_terminates_cond)](#t-step_terminates_cond) を適用するために仮定 (dec)、すなわち

```math
\forall M\,n,\ M\in\mathrm{ST\_PS} \to 1 < \lvert M\rvert \to 1 \le n \to
 \mathrm{tr}(M[n]) \prec \mathrm{tr}\,M
```

を示す。$M$, $n$ をとり、$M\in\mathrm{ST\_PS}$、$1<\lvert M\rvert$、$1\le n$ を仮定する。
[(T.m_step_decreases)](Mechanized.md#t-m_step_decreases) は $1<\lvert M\rvert$ と $1\le n$ の 2 つのみから
$\mathrm{tr}(M[n]) \prec \mathrm{tr}\,M$ を与えるから、これを適用すればよい
（仮定 $M \in \mathrm{ST\_PS}$ は使わない。減少は標準形であることに依らない）。
こうして得た (dec) と仮定 $\mathrm{WF}(\prec_{\mathrm{NF}})$ を
[(T.step_terminates_cond)](#t-step_terminates_cond) に与えて $\mathrm{WF}(\lhd)$ を得る。∎

<a id="t-no_infinite_expansion"></a>
### 定理 無限展開列の非存在（(wfimg) のみを仮定） (T.no_infinite_expansion)

**主張** $\mathrm{WF}(\prec_{\mathrm{NF}})$ ならば

```math
\neg\ \exists S : \mathbb{N} \to \mathrm{PairSeq},\
 \bigl(\forall i,\ S_i \in \mathrm{ST\_PS}\bigr) \ \wedge\ \bigl(\forall i,\ S_i \Rightarrow S_{i+1}\bigr).
```

**証明** [(T.no_infinite_expansion_cond)](#t-no_infinite_expansion_cond) を適用するために仮定 (dec)、すなわち

```math
\forall M\,n,\ M\in\mathrm{ST\_PS} \to 1 < \lvert M\rvert \to 1 \le n \to
 \mathrm{tr}(M[n]) \prec \mathrm{tr}\,M
```

を示す。$M$, $n$ をとり、$M\in\mathrm{ST\_PS}$、$1<\lvert M\rvert$、$1\le n$ を仮定する。
[(T.m_step_decreases)](Mechanized.md#t-m_step_decreases) は $1<\lvert M\rvert$ と $1\le n$ の 2 つのみから
$\mathrm{tr}(M[n]) \prec \mathrm{tr}\,M$ を与えるから、これを適用すればよい
（仮定 $M \in \mathrm{ST\_PS}$ は使わない）。
こうして得た (dec) と仮定 $\mathrm{WF}(\prec_{\mathrm{NF}})$ を
[(T.no_infinite_expansion_cond)](#t-no_infinite_expansion_cond) に与えて主張を得る。∎

---

## 残余義務 $\mathrm{wfimg}$ の位置づけ

Lean 原文の最後の節見出しコメントは、上の 2 定理へ $\mathrm{WF}(\prec_{\mathrm{NF}})$ を供給すれば
停止性が無条件の主張になることを述べている。**この節に宣言はない。**

<!-- TODO: Lean 原文 (lean/YAPSS/Proofs.lean:110) のこの節見出しコメントは
     `wf_Rnf_from_diag` という名の補題を経由する計画を述べているが、現在の lean/YAPSS/ に
     その名の宣言は存在しない。実際に採られた経路は下記のとおりで、コメントの記述が古い。
     コメント本文の意図するところ以上の内容は md 側に書いていない。 -->

実際に $\mathrm{WF}(\prec_{\mathrm{NF}})$ を供給するのは
[(T.wf_Rnf_of_wf_PS)](OrdinalFree.md#t-wf_Rnf_of_wf_PS)（ペア列側の整礎性から像側の整礎性への移送）と
[(T.wf_Rnf_holds)](Final.md#t-wf_Rnf_holds)（その無条件化）であり、
本章の [(T.step_terminates)](#t-step_terminates) と
[(T.no_infinite_expansion)](#t-no_infinite_expansion) にそれらを与えて得られる無条件の主張が
[(T.PSS_terminates_unconditional)](Final.md#t-PSS_terminates_unconditional) と
[(T.no_infinite_expansion_holds)](Final.md#t-no_infinite_expansion_holds) である。
