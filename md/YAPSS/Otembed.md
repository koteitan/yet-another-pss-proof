[← 目次](README.md)

# Otembed — Buchholz 順序数への値写像 $`\mathrm{oV}`$ と OT 整合性述語 $`\mathrm{wf3}`$

三分岐記法 $`\mathrm{Three}`$（[(D.Three)](Mechanized.md#d-Three)）の項を Buchholz の崩壊関数
$`\psi_v`$（[(D.psi)](Psi.md#d-psi)）で順序数へ写す値写像 $`\mathrm{oV}`$ を定義し、その値の上界を与える
述語 $`\mathrm{allprinc}_{\lt d}`$、スパイン添字の上界 $`\mathrm{spinesub}_{\le m}`$、Buchholz の係数集合 $`G_u`$、
頭部比較 $`\sqsubseteq`$、および Buchholz OT の整合性述語 $`\mathrm{wf3}`$ を導入する。
本章の 29 個の宣言のうち 7 個は定義、22 個は定理である。定理のうち 4 個、すなわち
[(T.oV_lt_of_allprinc)](#t-oV_lt_of_allprinc)、[(T.spinesub_le_mono)](#t-spinesub_le_mono)、
[(T.wf3_spinesub_le)](#t-wf3_spinesub_le)、[(T.Gterm_tsize)](#t-Gterm_tsize)
は項の構造に関する帰納法で証明され、残る 18 個は定義の展開・有限個の場合分け・
順序数と自然数の初等的性質のみで証明される。
このうち後続の章で用いられるのは $`G_u`$ に関する宣言（[(D.Gterm)](#d-Gterm),
[(T.mem_Gterm_P)](#t-mem_Gterm_P), [(T.Gterm_tsize)](#t-Gterm_tsize)）のみであり、
$`\mathrm{oV}`$・$`\mathrm{wf3}`$ を経由する順序数埋め込みは本証明の最終経路では使われない
（[(T.PSS_terminates_unconditional)](Final.md#t-PSS_terminates_unconditional) の証明は $`\mathrm{oV}`$ にも
$`\mathrm{wf3}`$ にも依存しない）。

## 記法

この章で導入する Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `oV t` | $`\mathrm{oV}\,t`$ | 項 $`t`$ の順序数値 |
| `allprinc_lt d t` | $`\mathrm{allprinc}_{\lt d}(t)`$ | $`t`$ のスパイン上の主要項がすべて $`\lt d`$ |
| `spinesub_le m t` | $`\mathrm{spinesub}_{\le m}(t)`$ | $`t`$ のスパイン上の添字がすべて $`\le m`$ |
| `Gterm u t` | $`G_u(t)`$ | Buchholz の係数集合（項の集合） |
| `hdle x y` | $`x \sqsubseteq y`$ | $`x`$ の頭部主要項が $`y`$ の頭部主要項以下 |
| `wf3 t` | $`\mathrm{wf3}(t)`$ | $`t`$ は Buchholz OT の整合な項 |
| `headle_all bnd t` | $`\mathrm{headle}_{\mathrm{bnd}}(t)`$ | $`t`$ の各主要項が $`\mathrm{bnd}`$ の頭部以下 |

他の章で定義済みの記号については次のように書く。

| Lean | 本文 | 定義箇所 |
|---|---|---|
| `Three`, `Z`, `P a b c` | $`\mathrm{Three}`$, $`\mathsf{Z}`$, $`\mathsf{P}(a,b,c)`$ | [(D.Three)](Mechanized.md#d-Three) |
| `x <o y` | $`x \prec y`$ | [(D.olt)](Mechanized.md#d-olt) |
| `x ≤o y` | $`x \preceq y`$ | [(D.ole)](Mechanized.md#d-ole) |
| `lead t` | $`\mathrm{lead}\,t`$ | [(D.lead)](Mechanized.md#d-lead) |
| `tsize t` | $`\lVert t\rVert`$ | [(D.tsize)](Wfsum.md#d-tsize) |
| `psi α v` | $`\psi_v(\alpha)`$ | [(D.psi)](Psi.md#d-psi) |
| `addprinc δ` | $`\mathrm{addprinc}(\delta)`$ | [(D.addprinc)](Psi.md#d-addprinc) |
| `Ordinal` | $`\mathrm{Ord}`$ | Mathlib の順序数の型 |

順序数について本章で用いる性質は次の 3 つだけである。

- $`\alpha + \beta`$ は順序数の加法、$`0`$ は最小の順序数。
- $`\alpha \le \alpha + \beta`$（Mathlib の `le_self_add`）。
- $`\mathrm{addprinc}(\delta)`$ は $`0 \lt \delta`$ かつ
  $`\forall \beta\,\gamma,\ \beta\lt \delta \to \gamma\lt \delta \to \beta+\gamma\lt \delta`$ である
  （[(D.addprinc)](Psi.md#d-addprinc)）。

集合については、$`\mathrm{Three}`$ の部分集合を $`\mathrm{Set}\ \mathrm{Three}`$ と書き、
$`\emptyset`$ は空集合、$`X\cup Y`$ は和集合、$`\{b\}\cup X`$ は Lean の `insert b X` を表す。
和集合の要素判定 $`x\in X\cup Y \iff x\in X \vee x\in Y`$、
空集合の要素判定 $`\neg(x\in\emptyset)`$、
$`x\in\{b\}\cup X \iff x=b \vee x\in X`$ を随時用いる。

$`\mathrm{Three}`$ の項 $`t`$ に対し、$`t`$ の**スパイン**とは、$`t`$ を
```math
t = \mathsf{P}(a_1,b_1,\mathsf{P}(a_2,b_2,\dots \mathsf{P}(a_k,b_k,\mathsf{Z})\dots))
```
と（第 3 引数について $`\mathsf{Z}`$ に至るまで）分解したときの添字の列 $`(a_1,\dots,a_k)`$ を指す
（$`t=\mathsf{Z}`$ のときは $`k=0`$、空列）。この分解は [(D.Three)](Mechanized.md#d-Three) の
構成子の単射性により一意である。

## 値写像 $`\mathrm{oV}`$

<a id="d-oV"></a>
### 定義 値写像 (D.oV)

$`\mathrm{oV} : \mathrm{Three} \to \mathrm{Ord}`$ を項の構造に関する再帰で定める。

```math
\mathrm{oV}\,\mathsf{Z} := 0, \qquad
\mathrm{oV}\,\mathsf{P}(a,b,c) := \psi_a(\mathrm{oV}\,b) + \mathrm{oV}\,c .
```

右辺の再帰呼び出し $`\mathrm{oV}\,b`$, $`\mathrm{oV}\,c`$ の引数 $`b, c`$ は $`\mathsf{P}(a,b,c)`$ の真部分項
であるから、この定義は構造帰納として整合的である。
（この定義は、$`\mathsf{P}(a,b,c)`$ を Buchholz の記法 $`D_a(b)+c`$ に、$`\mathsf{Z}`$ を $`0`$ に
対応させる意図で置かれている。$`D_a`$ は本リポジトリでは定義されない外部の記法であり、
以下の主張・証明では用いない。）

Lean では `oV : Three → Ordinal.{u}` と宇宙多相に宣言されているが、宇宙変数 $`u`$ は
$`\psi`$ の宇宙変数と同一に取られるだけであり、以下の主張・証明には関与しない。

<a id="t-oV_Z"></a>
### 定理 $`\mathrm{oV}\,\mathsf{Z}=0`$ (T.oV_Z)

**主張** $`\mathrm{oV}\,\mathsf{Z} = 0`$。

**証明** [(D.oV)](#d-oV) の第 1 式そのものであり、両辺は定義により同一である。∎

<a id="t-oV_P"></a>
### 定理 主要項の値 (T.oV_P)

**主張** 任意の $`a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し
```math
\mathrm{oV}\,\mathsf{P}(a,b,c) = \psi_a(\mathrm{oV}\,b) + \mathrm{oV}\,c .
```

**証明** [(D.oV)](#d-oV) の第 2 式そのものであり、両辺は定義により同一である。∎

<a id="t-psi_le_oV"></a>
### 定理 主要項は値の下界 (T.psi_le_oV)

**主張** 任意の $`a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し
```math
\psi_a(\mathrm{oV}\,b) \ \le\ \mathrm{oV}\,\mathsf{P}(a,b,c) .
```

**証明** [(T.oV_P)](#t-oV_P) により右辺は $`\psi_a(\mathrm{oV}\,b) + \mathrm{oV}\,c`$ である。
順序数の加法は第 2 引数について広義単調であり、かつ $`\alpha + 0 = \alpha`$ であるから、
$`0 \le \beta`$ より $`\alpha = \alpha + 0 \le \alpha + \beta`$ が任意の順序数 $`\alpha,\beta`$ について成り立つ
（Mathlib の `le_self_add`）。これを $`\alpha := \psi_a(\mathrm{oV}\,b)`$, $`\beta := \mathrm{oV}\,c`$ に
適用すればよい。∎

## 加法主要な和と添字の上界

Lean 側の節見出し *Additive-principal sums and the subscript bound* に対応する。

<a id="d-allprinc_lt"></a>
### 定義 スパイン上の主要項の上界 (D.allprinc_lt)

$`d \in \mathrm{Ord}`$ に対し、述語 $`\mathrm{allprinc}_{\lt d} : \mathrm{Three}\to\mathrm{Prop}`$ を
項の構造に関する再帰で定める。

```math
\mathrm{allprinc}_{<d}(\mathsf{Z}) := \top, \qquad
\mathrm{allprinc}_{<d}(\mathsf{P}(a,b,c)) := \bigl(\psi_a(\mathrm{oV}\,b) < d\bigr) \ \wedge\ \mathrm{allprinc}_{<d}(c) .
```

再帰呼び出しは第 3 引数 $`c`$ についてのみであり、第 2 引数 $`b`$ の内部には立ち入らない。
したがって、$`t`$ のスパイン分解を
$`t = \mathsf{P}(a_1,b_1,\mathsf{P}(a_2,b_2,\dots\mathsf{P}(a_k,b_k,\mathsf{Z})\dots))`$ とすると、
定義を $`k`$ 回展開して

```math
\mathrm{allprinc}_{<d}(t) \iff \forall i\ (1\le i\le k),\ \psi_{a_i}(\mathrm{oV}\,b_i) < d
```

が成り立つ（$`k=0`$ すなわち $`t=\mathsf{Z}`$ のときは右辺は空の連言で $`\top`$）。

<a id="t-allprinc_lt_Z"></a>
### 定理 $`\mathsf{Z}`$ の場合 (T.allprinc_lt_Z)

**主張** 任意の $`d\in\mathrm{Ord}`$ に対し $`\mathrm{allprinc}_{\lt d}(\mathsf{Z})`$。

**証明** [(D.allprinc_lt)](#d-allprinc_lt) の第 1 式により
$`\mathrm{allprinc}_{\lt d}(\mathsf{Z})`$ は $`\top`$ と定義により同一であり、$`\top`$ は成り立つ。∎

<a id="t-allprinc_lt_P"></a>
### 定理 主要項の場合 (T.allprinc_lt_P)

**主張** 任意の $`d\in\mathrm{Ord}`$, $`a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し
```math
\mathrm{allprinc}_{<d}(\mathsf{P}(a,b,c)) \iff \bigl(\psi_a(\mathrm{oV}\,b)<d\bigr)\ \wedge\ \mathrm{allprinc}_{<d}(c) .
```

**証明** [(D.allprinc_lt)](#d-allprinc_lt) の第 2 式そのものであり、両辺は定義により同一の命題である。∎

<a id="t-oV_lt_of_allprinc"></a>
### 定理 加法主要な上界の下での値の上界 (T.oV_lt_of_allprinc)

**主張** $`d\in\mathrm{Ord}`$ が $`\mathrm{addprinc}(d)`$ をみたし、$`t\in\mathrm{Three}`$ が
$`\mathrm{allprinc}_{\lt d}(t)`$ をみたすならば $`\mathrm{oV}\,t \lt d`$。

**証明** $`d`$ と仮定 $`\mathrm{addprinc}(d)`$ を固定し、$`t`$ の構造に関する帰納法を行う。
帰納法の述語は

```math
\Phi(t) :\equiv \mathrm{allprinc}_{<d}(t) \to \mathrm{oV}\,t < d .
```

- **基底段** $`t=\mathsf{Z}`$：[(T.oV_Z)](#t-oV_Z) より $`\mathrm{oV}\,\mathsf{Z} = 0`$ である。
  $`\mathrm{addprinc}(d)`$（[(D.addprinc)](Psi.md#d-addprinc)）の第 1 連言子は $`0\lt d`$ であるから
  $`\mathrm{oV}\,\mathsf{Z} \lt d`$。よって前提によらず $`\Phi(\mathsf{Z})`$ が成り立つ。

- **帰納段** $`t=\mathsf{P}(a,b,c)`$：帰納法の仮定は $`\Phi(b)`$ と $`\Phi(c)`$ の 2 つである
  （以下で用いるのは $`\Phi(c)`$ のみ）。
  前提 $`\mathrm{allprinc}_{\lt d}(\mathsf{P}(a,b,c))`$ を仮定する。
  [(T.allprinc_lt_P)](#t-allprinc_lt_P) によりこれは
  $`h : \psi_a(\mathrm{oV}\,b)\lt d`$ と $`h' : \mathrm{allprinc}_{\lt d}(c)`$ の連言である。
  帰納法の仮定 $`\Phi(c)`$ を $`h'`$ に適用して $`\mathrm{oV}\,c \lt d`$ を得る。
  $`\mathrm{addprinc}(d)`$ の第 2 連言子
  $`\forall\beta\,\gamma,\ \beta\lt d\to\gamma\lt d\to\beta+\gamma\lt d`$ を
  $`\beta := \psi_a(\mathrm{oV}\,b)`$, $`\gamma := \mathrm{oV}\,c`$ に適用し、
  $`h`$ と $`\mathrm{oV}\,c\lt d`$ を渡すと
  ```math
  \psi_a(\mathrm{oV}\,b) + \mathrm{oV}\,c < d
  ```
  を得る。[(T.oV_P)](#t-oV_P) により左辺は $`\mathrm{oV}\,\mathsf{P}(a,b,c)`$ に等しい。
  よって $`\Phi(\mathsf{P}(a,b,c))`$。∎

<a id="d-spinesub_le"></a>
### 定義 スパイン添字の上界 (D.spinesub_le)

$`m\in\mathbb{N}`$ に対し、述語 $`\mathrm{spinesub}_{\le m} : \mathrm{Three}\to\mathrm{Prop}`$ を
項の構造に関する再帰で定める。

```math
\mathrm{spinesub}_{\le m}(\mathsf{Z}) := \top, \qquad
\mathrm{spinesub}_{\le m}(\mathsf{P}(a,b,c)) := (a\le m) \ \wedge\ \mathrm{spinesub}_{\le m}(c) .
```

[(D.allprinc_lt)](#d-allprinc_lt) と同じく再帰は第 3 引数についてのみであり、第 2 引数 $`b`$ は見ない。
$`t`$ のスパイン分解を $`t=\mathsf{P}(a_1,b_1,\dots\mathsf{P}(a_k,b_k,\mathsf{Z})\dots)`$ とすると、
定義を $`k`$ 回展開して

```math
\mathrm{spinesub}_{\le m}(t) \iff \forall i\ (1\le i\le k),\ a_i \le m
```

が成り立つ。

<a id="t-spinesub_le_Z"></a>
### 定理 $`\mathsf{Z}`$ の場合 (T.spinesub_le_Z)

**主張** 任意の $`m\in\mathbb{N}`$ に対し $`\mathrm{spinesub}_{\le m}(\mathsf{Z})`$。

**証明** [(D.spinesub_le)](#d-spinesub_le) の第 1 式により
$`\mathrm{spinesub}_{\le m}(\mathsf{Z})`$ は $`\top`$ と定義により同一であり、$`\top`$ は成り立つ。∎

<a id="t-spinesub_le_P"></a>
### 定理 主要項の場合 (T.spinesub_le_P)

**主張** 任意の $`m,a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し
```math
\mathrm{spinesub}_{\le m}(\mathsf{P}(a,b,c)) \iff (a\le m)\ \wedge\ \mathrm{spinesub}_{\le m}(c) .
```

**証明** [(D.spinesub_le)](#d-spinesub_le) の第 2 式そのものであり、両辺は定義により同一の命題である。∎

<a id="t-spinesub_le_mono"></a>
### 定理 上界の単調性 (T.spinesub_le_mono)

**主張** $`m,m'\in\mathbb{N}`$, $`t\in\mathrm{Three}`$ とする。
$`\mathrm{spinesub}_{\le m}(t)`$ かつ $`m\le m'`$ ならば $`\mathrm{spinesub}_{\le m'}(t)`$。

**証明** $`m`$, $`m'`$ と仮定 $`m\le m'`$ を固定し、$`t`$ の構造に関する帰納法を行う。
帰納法の述語は

```math
\Phi(t) :\equiv \mathrm{spinesub}_{\le m}(t) \to \mathrm{spinesub}_{\le m'}(t) .
```

- **基底段** $`t=\mathsf{Z}`$：結論 $`\mathrm{spinesub}_{\le m'}(\mathsf{Z})`$ は
  [(T.spinesub_le_Z)](#t-spinesub_le_Z) により成り立つ。よって前提によらず $`\Phi(\mathsf{Z})`$。

- **帰納段** $`t=\mathsf{P}(a,b,c)`$：帰納法の仮定は $`\Phi(b)`$ と $`\Phi(c)`$ の 2 つである
  （以下で用いるのは $`\Phi(c)`$ のみ）。
  前提 $`\mathrm{spinesub}_{\le m}(\mathsf{P}(a,b,c))`$ を仮定し、
  [(T.spinesub_le_P)](#t-spinesub_le_P) により
  $`h_1 : a\le m`$ と $`h_2 : \mathrm{spinesub}_{\le m}(c)`$ に分解する。
  結論はふたたび [(T.spinesub_le_P)](#t-spinesub_le_P) により
  $`a\le m'`$ と $`\mathrm{spinesub}_{\le m'}(c)`$ の連言である。
  - $`a\le m'`$：$`h_1`$ の $`a\le m`$ と仮定の $`m\le m'`$ から、$`\mathbb{N}`$ の $`\le`$ の推移律により
    $`a\le m'`$（Lean ではこの 1 行を `omega` が行う）。
  - $`\mathrm{spinesub}_{\le m'}(c)`$：帰納法の仮定 $`\Phi(c)`$ を $`h_2`$ に適用する。

  よって $`\Phi(\mathsf{P}(a,b,c))`$。∎

## Buchholz の係数集合 $`G_u`$ と OT 整合性述語

Lean 側の節見出し *Buchholz coefficient sets `G_u` and the OT well-formedness predicate* に対応する。

<a id="d-Gterm"></a>
### 定義 係数集合 (D.Gterm)

$`u\in\mathbb{N}`$ に対し、写像 $`G_u : \mathrm{Three}\to \mathrm{Set}\ \mathrm{Three}`$ を
項の構造に関する再帰で定める。

```math
G_u(\mathsf{Z}) := \emptyset, \qquad
G_u(\mathsf{P}(a,b,c)) := \Bigl(\text{if } u\le a \text{ then } \{b\}\cup G_u(b) \text{ else } \emptyset\Bigr)\ \cup\ G_u(c) .
```

すなわち

```math
G_u(\mathsf{P}(a,b,c)) = \begin{cases}
\{b\}\cup G_u(b)\cup G_u(c) & (u\le a) \cr
G_u(c) & (u>a)
\end{cases}
```

である（$`u\gt a`$ の場合は $`\emptyset\cup G_u(c)=G_u(c)`$ による）。
再帰呼び出しの引数 $`b`$, $`c`$ はいずれも $`\mathsf{P}(a,b,c)`$ の真部分項であるから、
この定義は構造帰納として整合的である。
条件式の中の再帰呼び出しの添字は $`u`$ のままであって $`a`$ ではないことに注意する
（$`a`$ に付け替えた版が現れるのは [(D.wf3)](#d-wf3) の中である）。

<a id="t-Gterm_Z"></a>
### 定理 $`\mathsf{Z}`$ の係数集合 (T.Gterm_Z)

**主張** 任意の $`u\in\mathbb{N}`$ に対し $`G_u(\mathsf{Z}) = \emptyset`$。

**証明** [(D.Gterm)](#d-Gterm) の第 1 式そのものであり、両辺は定義により同一である。∎

<a id="t-Gterm_P"></a>
### 定理 主要項の係数集合 (T.Gterm_P)

**主張** 任意の $`u,a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し
```math
G_u(\mathsf{P}(a,b,c)) = \Bigl(\text{if } u\le a \text{ then } \{b\}\cup G_u(b) \text{ else } \emptyset\Bigr)\ \cup\ G_u(c) .
```

**証明** [(D.Gterm)](#d-Gterm) の第 2 式そのものであり、両辺は定義により同一である。∎

<a id="t-mem_Gterm_P"></a>
### 定理 主要項の係数集合の要素判定 (T.mem_Gterm_P)

**主張** 任意の $`u,a\in\mathbb{N}`$, $`b,c,x\in\mathrm{Three}`$ に対し
```math
x\in G_u(\mathsf{P}(a,b,c)) \iff \bigl(u\le a \ \wedge\ (x=b \ \vee\ x\in G_u(b))\bigr)\ \vee\ x\in G_u(c) .
```

**証明** [(T.Gterm_P)](#t-Gterm_P) で左辺を書き換えたうえで、命題 $`u\le a`$ の真偽で場合分けする。

- $`u\le a`$ が真のとき。条件式は $`\{b\}\cup G_u(b)`$ に簡約され、左辺は
  $`x\in(\{b\}\cup G_u(b))\cup G_u(c)`$ である。和集合の要素判定を 2 回用いて、これは
  ```math
  (x=b \ \vee\ x\in G_u(b))\ \vee\ x\in G_u(c)
  ```
  と同値である。他方、右辺の第 1 選言子 $`u\le a \wedge (x=b\vee x\in G_u(b))`$ において
  $`u\le a`$ は真であるから、右辺は $`(x=b\vee x\in G_u(b))\vee x\in G_u(c)`$ と同値である。
  両者は同一の命題であるから同値。

- $`u\le a`$ が偽のとき。条件式は $`\emptyset`$ に簡約され、左辺は $`x\in\emptyset\cup G_u(c)`$ である。
  和集合の要素判定と $`\neg(x\in\emptyset)`$ より、これは $`x\in G_u(c)`$ と同値である。
  他方、右辺の第 1 選言子は $`u\le a`$ が偽であるから偽であり、右辺は $`x\in G_u(c)`$ と同値である。
  よって同値。∎

<a id="d-hdle"></a>
### 定義 頭部比較 (D.hdle)

関係 $`\sqsubseteq\ \subseteq \mathrm{Three}\times\mathrm{Three}`$ を、第 1 引数と第 2 引数の
構成子による場合分けで定める。

```math
\begin{aligned}
\mathsf{Z} &\sqsubseteq y &&:\iff \top &&(y\text{ は任意}),\cr
\mathsf{P}(a,b,c) &\sqsubseteq \mathsf{Z} &&:\iff \bot,\cr
\mathsf{P}(a,b,c) &\sqsubseteq \mathsf{P}(e,f,g) &&:\iff a<e \ \vee\ \bigl(a=e \ \wedge\ (b\prec f \ \vee\ b=f)\bigr).
\end{aligned}
```

ここで $`\prec`$ は [(D.olt)](Mechanized.md#d-olt) である。
第 3 式の右辺には第 3 引数 $`c`$, $`g`$ が現れない。すなわち $`\sqsubseteq`$ は
頭部主要項 $`\mathsf{P}(a,b,\cdot)`$ と $`\mathsf{P}(e,f,\cdot)`$ を、添字を第 1、引数を第 2 の
比較対象とする辞書式に比べる関係であり、後続和を無視する。
なお第 3 式の $`b\prec f\vee b=f`$ は [(D.ole)](Mechanized.md#d-ole) の $`b\preceq f`$ を
展開したものと同一の命題であるが、Lean の定義は $`\preceq`$ を用いずこの選言をそのまま書いている。

<a id="t-hdle_Z"></a>
### 定理 $`\mathsf{Z}`$ は任意の項の頭部以下 (T.hdle_Z)

**主張** 任意の $`y\in\mathrm{Three}`$ に対し $`\mathsf{Z}\sqsubseteq y`$。

**証明** [(D.hdle)](#d-hdle) の第 1 式により $`\mathsf{Z}\sqsubseteq y`$ は $`\top`$ と定義により同一であり、
$`\top`$ は成り立つ。∎

<a id="t-hdle_P_Z"></a>
### 定理 主要項は $`\mathsf{Z}`$ の頭部以下でない (T.hdle_P_Z)

**主張** 任意の $`a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し $`\neg\bigl(\mathsf{P}(a,b,c)\sqsubseteq\mathsf{Z}\bigr)`$。

**証明** [(D.hdle)](#d-hdle) の第 2 式により $`\mathsf{P}(a,b,c)\sqsubseteq\mathsf{Z}`$ は $`\bot`$ と
定義により同一の命題である。よってその仮定からそのまま $`\bot`$ が得られ、否定が示された
（Lean の証明項 `fun h => h` はこの恒等写像 $`\bot\to\bot`$ である）。∎

<a id="t-hdle_P_P"></a>
### 定理 主要項どうしの頭部比較 (T.hdle_P_P)

**主張** 任意の $`a,e\in\mathbb{N}`$, $`b,c,f,g\in\mathrm{Three}`$ に対し
```math
\mathsf{P}(a,b,c)\sqsubseteq\mathsf{P}(e,f,g) \iff a<e \ \vee\ \bigl(a=e\ \wedge\ (b\prec f \ \vee\ b=f)\bigr) .
```

**証明** [(D.hdle)](#d-hdle) の第 3 式そのものであり、両辺は定義により同一の命題である。∎

<a id="d-wf3"></a>
### 定義 OT 整合性 (D.wf3)

述語 $`\mathrm{wf3} : \mathrm{Three}\to\mathrm{Prop}`$ を項の構造に関する再帰で定める。

```math
\mathrm{wf3}(\mathsf{Z}) := \top,
```
```math
\mathrm{wf3}(\mathsf{P}(a,b,c)) := \mathrm{wf3}(b)\ \wedge\ \mathrm{wf3}(c)\ \wedge\
\bigl(\forall x\in G_a(b),\ x\prec b\bigr)\ \wedge\ \bigl(c\sqsubseteq\mathsf{P}(a,b,\mathsf{Z})\bigr) .
```

（[(D.Gterm)](#d-Gterm), [(D.olt)](Mechanized.md#d-olt), [(D.hdle)](#d-hdle)。）
4 つの連言子の役割は次の通りである。

1. $`\mathrm{wf3}(b)`$、2. $`\mathrm{wf3}(c)`$：部分項についての再帰的整合性。
3. $`\forall x\in G_a(b),\ x\prec b`$：Buchholz の条件 OT3。係数集合の添字が主要項の添字 $`a`$ である
   （[(D.Gterm)](#d-Gterm) の再帰内部の添字 $`u`$ とは異なり、ここで $`a`$ に付け替えられる）。
4. $`c\sqsubseteq\mathsf{P}(a,b,\mathsf{Z})`$：Buchholz の条件 OT2、すなわちスパインに沿って
   頭部主要項が非増加であること。$`\sqsubseteq`$ は第 3 引数を見ないから、
   右辺の第 3 引数を $`\mathsf{Z}`$ と書いても $`c`$ と書いても同じ命題である
   （[(T.hdle_head_ignores_tail)](#t-hdle_head_ignores_tail)）。

再帰呼び出しの引数 $`b`$, $`c`$ は $`\mathsf{P}(a,b,c)`$ の真部分項であるから、
この定義は構造帰納として整合的である。

<a id="t-wf3_Z"></a>
### 定理 $`\mathsf{Z}`$ は整合 (T.wf3_Z)

**主張** $`\mathrm{wf3}(\mathsf{Z})`$。

**証明** [(D.wf3)](#d-wf3) の第 1 式により $`\mathrm{wf3}(\mathsf{Z})`$ は $`\top`$ と定義により同一であり、
$`\top`$ は成り立つ。∎

<a id="t-wf3_P"></a>
### 定理 主要項の整合性 (T.wf3_P)

**主張** 任意の $`a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し
```math
\mathrm{wf3}(\mathsf{P}(a,b,c)) \iff
\mathrm{wf3}(b)\ \wedge\ \mathrm{wf3}(c)\ \wedge\ \bigl(\forall x\in G_a(b),\ x\prec b\bigr)\ \wedge\ \bigl(c\sqsubseteq\mathsf{P}(a,b,\mathsf{Z})\bigr) .
```

**証明** [(D.wf3)](#d-wf3) の第 2 式そのものであり、両辺は定義により同一の命題である。∎

<a id="t-wf3_spinesub_le"></a>
### 定理 整合な項のスパイン添字は先頭添字以下 (T.wf3_spinesub_le)

**主張** $`t\in\mathrm{Three}`$ が $`\mathrm{wf3}(t)`$ をみたすならば
$`\mathrm{spinesub}_{\le \mathrm{lead}\,t}(t)`$。

**証明** $`t`$ の構造に関する帰納法。帰納法の述語は

```math
\Phi(t) :\equiv \mathrm{wf3}(t) \to \mathrm{spinesub}_{\le \mathrm{lead}\,t}(t) .
```

- **基底段** $`t=\mathsf{Z}`$：$`\mathrm{lead}\,\mathsf{Z}=0`$ である
  （[(T.lead_Z)](Mechanized.md#t-lead_Z)）から結論は $`\mathrm{spinesub}_{\le 0}(\mathsf{Z})`$ であり、
  [(T.spinesub_le_Z)](#t-spinesub_le_Z) により成り立つ。よって前提によらず $`\Phi(\mathsf{Z})`$。

- **帰納段** $`t=\mathsf{P}(a,b,c)`$：帰納法の仮定は $`\Phi(b)`$ と $`\Phi(c)`$ の 2 つである
  （以下で用いるのは $`\Phi(c)`$ のみ）。前提 $`\mathrm{wf3}(\mathsf{P}(a,b,c))`$ を仮定し、
  [(T.wf3_P)](#t-wf3_P) により
  ```math
  \mathrm{wf3}(b),\quad \mathrm{wf3}(c),\quad \forall x\in G_a(b),\ x\prec b,\quad c\sqsubseteq\mathsf{P}(a,b,\mathsf{Z})
  ```
  の 4 つに分解する（第 3 のものは以下で使わない）。
  $`\mathrm{lead}\,\mathsf{P}(a,b,c)=a`$（[(T.lead_P)](Mechanized.md#t-lead_P)）であるから、
  示すべきは $`\mathrm{spinesub}_{\le a}(\mathsf{P}(a,b,c))`$ であり、
  [(T.spinesub_le_P)](#t-spinesub_le_P) によりこれは
  ```math
  a\le a \quad\text{かつ}\quad \mathrm{spinesub}_{\le a}(c)
  ```
  の連言である。

  第 1 の $`a\le a`$ は $`\mathbb{N}`$ の $`\le`$ の反射性による。

  第 2 の $`\mathrm{spinesub}_{\le a}(c)`$ を示すため、$`c`$ の構成子で場合分けする。

  - $`c=\mathsf{Z}`$ のとき：[(T.spinesub_le_Z)](#t-spinesub_le_Z) により
    $`\mathrm{spinesub}_{\le a}(\mathsf{Z})`$ が成り立つ。

  - $`c=\mathsf{P}(a',b',c')`$ のとき：分解して得た第 4 の連言子は
    $`\mathsf{P}(a',b',c')\sqsubseteq\mathsf{P}(a,b,\mathsf{Z})`$ である。
    [(T.hdle_P_P)](#t-hdle_P_P) によりこれは
    ```math
    a'<a \ \vee\ \bigl(a'=a \ \wedge\ (b'\prec b \ \vee\ b'=b)\bigr)
    ```
    である。第 1 選言のときは $`a'\lt a`$ から $`a'\le a`$、第 2 選言のときは $`a'=a`$ から $`a'\le a`$
    が従う（Lean ではこの 2 通りの初等的な導出を `omega` が行う）。いずれにせよ
    ```math
    a' \le a .
    ```
    一方、帰納法の仮定 $`\Phi(c)`$ を $`\mathrm{wf3}(c)`$ に適用して
    $`\mathrm{spinesub}_{\le \mathrm{lead}\,c}(c)`$ を得る。
    $`\mathrm{lead}\,c = \mathrm{lead}\,\mathsf{P}(a',b',c') = a'`$
    （[(T.lead_P)](Mechanized.md#t-lead_P)）であるから、これは
    $`\mathrm{spinesub}_{\le a'}(c)`$ である。
    ここで [(T.spinesub_le_mono)](#t-spinesub_le_mono) を $`m:=a'`$, $`m':=a`$, 項 $`c`$ に適用し、
    上で得た $`a'\le a`$ を渡すと $`\mathrm{spinesub}_{\le a}(c)`$ を得る。

  以上により $`\Phi(\mathsf{P}(a,b,c))`$。∎

<a id="d-headle_all"></a>
### 定義 スパイン上の主要項の頭部上界 (D.headle_all)

$`\mathrm{bnd}\in\mathrm{Three}`$ に対し、述語
$`\mathrm{headle}_{\mathrm{bnd}} : \mathrm{Three}\to\mathrm{Prop}`$ を項の構造に関する再帰で定める。

```math
\mathrm{headle}_{\mathrm{bnd}}(\mathsf{Z}) := \top, \qquad
\mathrm{headle}_{\mathrm{bnd}}(\mathsf{P}(a,b,c)) := \bigl(\mathsf{P}(a,b,\mathsf{Z})\sqsubseteq\mathrm{bnd}\bigr)\ \wedge\ \mathrm{headle}_{\mathrm{bnd}}(c) .
```

（[(D.hdle)](#d-hdle)。）再帰は第 3 引数についてのみである。
$`t`$ のスパイン分解を $`t=\mathsf{P}(a_1,b_1,\dots\mathsf{P}(a_k,b_k,\mathsf{Z})\dots)`$ とすると、
定義を $`k`$ 回展開して

```math
\mathrm{headle}_{\mathrm{bnd}}(t) \iff \forall i\ (1\le i\le k),\ \mathsf{P}(a_i,b_i,\mathsf{Z})\sqsubseteq\mathrm{bnd}
```

が成り立つ。

<a id="t-headle_all_Z"></a>
### 定理 $`\mathsf{Z}`$ の場合 (T.headle_all_Z)

**主張** 任意の $`\mathrm{bnd}\in\mathrm{Three}`$ に対し $`\mathrm{headle}_{\mathrm{bnd}}(\mathsf{Z})`$。

**証明** [(D.headle_all)](#d-headle_all) の第 1 式により
$`\mathrm{headle}_{\mathrm{bnd}}(\mathsf{Z})`$ は $`\top`$ と定義により同一であり、$`\top`$ は成り立つ。∎

<a id="t-headle_all_P"></a>
### 定理 主要項の場合 (T.headle_all_P)

**主張** 任意の $`\mathrm{bnd}\in\mathrm{Three}`$, $`a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し
```math
\mathrm{headle}_{\mathrm{bnd}}(\mathsf{P}(a,b,c)) \iff
\bigl(\mathsf{P}(a,b,\mathsf{Z})\sqsubseteq\mathrm{bnd}\bigr)\ \wedge\ \mathrm{headle}_{\mathrm{bnd}}(c) .
```

**証明** [(D.headle_all)](#d-headle_all) の第 2 式そのものであり、両辺は定義により同一の命題である。∎

<a id="t-hdle_head_ignores_tail"></a>
### 定理 頭部比較は後続和を見ない (T.hdle_head_ignores_tail)

**主張** 任意の $`a\in\mathbb{N}`$, $`b,c,z\in\mathrm{Three}`$ に対し
```math
\mathsf{P}(a,b,c)\sqsubseteq z \iff \mathsf{P}(a,b,\mathsf{Z})\sqsubseteq z .
```

**証明** $`z`$ の構成子で場合分けする。

- $`z=\mathsf{Z}`$ のとき：[(D.hdle)](#d-hdle) の第 2 式により、左辺 $`\mathsf{P}(a,b,c)\sqsubseteq\mathsf{Z}`$ も
  右辺 $`\mathsf{P}(a,b,\mathsf{Z})\sqsubseteq\mathsf{Z}`$ もともに $`\bot`$ と定義により同一である。
  よって両辺は同一の命題であり、同値。

- $`z=\mathsf{P}(e,f,g)`$ のとき：[(D.hdle)](#d-hdle) の第 3 式により、左辺は
  ```math
  a<e \ \vee\ \bigl(a=e\ \wedge\ (b\prec f\ \vee\ b=f)\bigr)
  ```
  と定義により同一であり、右辺もまったく同じ式と定義により同一である
  （第 3 式の右辺には第 1 引数の第 3 成分が現れないので、$`c`$ を $`\mathsf{Z}`$ に替えても式は変わらない）。
  よって両辺は同一の命題であり、同値。∎

## Buchholz クラス上の順序保存（Buchholz 補題 2.2(c)）

Lean 側の節見出し *Order preservation on the Buchholz class (Buchholz Lemma 2.2(c))* に対応する。
この見出しの下に宣言は 1 つも置かれていない。順序保存
（$`\mathrm{wf3}`$ をみたす $`x,y`$ について $`x\prec y \Rightarrow \mathrm{oV}\,x\lt \mathrm{oV}\,y`$）は
本モジュールでは述べられも証明されもしない。

## Buchholz 崩壊モジュール（値ルート）

Lean 側の節見出し *Buchholz collapsing module (value route)* に対応する。
この見出しには Lean のコメントとして、次の構想が記されている（証明された命題ではなく、
対応する宣言は本モジュールに存在しない。ここでは記録のためだけに引用する）。

> (M1) $`C_v(\alpha)`$ の加法主要な元でレベル $`v`$ の帯 $`[\Omega_v,\Omega_{v+1})`$ に属するものは、
> ある $`\xi\in C_v(\alpha)`$, $`\xi\lt \alpha`$ について $`\psi_v(\xi)`$ の形である。
> レベルが $`v`$ に定まるのは $`\psi_u(\xi)\in[\Omega_u,\Omega_{u+1})`$ であってこれらの帯が
> 互いに交わらないことによる。

ここで $`C_v(\alpha)`$ は [(D.Cset)](Psi.md#d-Cset)、$`\Omega_v`$ は [(D.Om)](Psi.md#d-Om) である。
この見出しの下に実際に置かれている宣言は次の 1 つである。

<a id="t-Gterm_tsize"></a>
### 定理 係数は構造サイズを真に減らす (T.Gterm_tsize)

**主張** $`t,x\in\mathrm{Three}`$, $`v\in\mathbb{N}`$ とする。
$`x\in G_v(t)`$ ならば $`\lVert x\rVert \lt \lVert t\rVert`$。

ここで $`\lVert\cdot\rVert`$ は [(D.tsize)](Wfsum.md#d-tsize) の構造サイズ、すなわち
$`\lVert\mathsf{Z}\rVert = 1`$、$`\lVert\mathsf{P}(a,b,c)\rVert = \lVert b\rVert+\lVert c\rVert+1`$ である。

**証明** $`x`$ と $`v`$ を固定し、$`t`$ の構造に関する帰納法を行う。帰納法の述語は

```math
\Phi(t) :\equiv x\in G_v(t) \to \lVert x\rVert < \lVert t\rVert .
```

- **基底段** $`t=\mathsf{Z}`$：[(T.Gterm_Z)](#t-Gterm_Z) より $`G_v(\mathsf{Z})=\emptyset`$ であり、
  $`\neg(x\in\emptyset)`$ であるから前提が偽である。よって $`\Phi(\mathsf{Z})`$ が成り立つ。

- **帰納段** $`t=\mathsf{P}(a,b,c)`$：帰納法の仮定は $`\Phi(b)`$ と $`\Phi(c)`$ の 2 つである。
  前提 $`x\in G_v(\mathsf{P}(a,b,c))`$ を仮定し、[(T.mem_Gterm_P)](#t-mem_Gterm_P) を適用して
  次の 3 つの場合に分ける。
  結論は $`\lVert x\rVert \lt \lVert \mathsf{P}(a,b,c)\rVert = \lVert b\rVert+\lVert c\rVert+1`$ である。

  1. $`v\le a`$ かつ $`x=b`$ のとき。示すべきは $`\lVert b\rVert \lt \lVert b\rVert+\lVert c\rVert+1`$ である。
     $`\lVert c\rVert \ge 0`$ であるから $`\lVert b\rVert+\lVert c\rVert+1 \ge \lVert b\rVert+1 \gt \lVert b\rVert`$。

  2. $`v\le a`$ かつ $`x\in G_v(b)`$ のとき。帰納法の仮定 $`\Phi(b)`$ を適用して
     $`\lVert x\rVert \lt \lVert b\rVert`$ を得る。
     また 1 と同じ計算で $`\lVert b\rVert \lt \lVert b\rVert+\lVert c\rVert+1`$ であるから、
     $`\mathbb{N}`$ の $`\lt `$ の推移律により $`\lVert x\rVert \lt \lVert b\rVert+\lVert c\rVert+1`$。

  3. $`x\in G_v(c)`$ のとき。帰納法の仮定 $`\Phi(c)`$ を適用して
     $`\lVert x\rVert \lt \lVert c\rVert`$ を得る。
     $`\lVert b\rVert\ge 0`$ より $`\lVert c\rVert \le \lVert b\rVert+\lVert c\rVert \lt \lVert b\rVert+\lVert c\rVert+1`$
     であるから、$`\lVert x\rVert \lt \lVert b\rVert+\lVert c\rVert+1`$。

  （1–3 の自然数の不等式計算を Lean では `omega` が行っている。）
  いずれの場合も結論が得られたので $`\Phi(\mathsf{P}(a,b,c))`$。∎

## Buchholz クラス $`\mathrm{wf3}`$ 上の $`\prec`$ の整礎性（補題 2.2）

Lean 側の節見出し *Well-foundedness of `olt` on the Buchholz class `wf3` (Lemma 2.2)* に対応する。
この見出しの下に宣言は 1 つも置かれておらず、ここでモジュールは終わる。
すなわち本モジュールは「値写像が $`(\mathrm{wf3},\prec)`$ を順序数へ埋め込む」という構想の
語彙（[(D.oV)](#d-oV), [(D.wf3)](#d-wf3), [(D.hdle)](#d-hdle), [(D.headle_all)](#d-headle_all),
[(D.allprinc_lt)](#d-allprinc_lt), [(D.spinesub_le)](#d-spinesub_le)）を定義するにとどまり、
$`\prec`$ の整礎性はここでは証明されない。

本証明で実際に用いられる $`\prec`$ の整礎性は
[(T.wf_olt_ST_PS_holds)](Final.md#t-wf_olt_ST_PS_holds) であって、その証明は
$`\mathrm{oV}`$ にも $`\mathrm{wf3}`$ にも $`\psi`$ にも依存しない。
後続の章（`Gterm0Olt` 以降）の証明本文が本章の宣言を名指しで引用する箇所は
[(D.Gterm)](#d-Gterm), [(T.mem_Gterm_P)](#t-mem_Gterm_P), [(T.Gterm_tsize)](#t-Gterm_tsize) の
3 つに限られる（`Nrm`, `Nrmstep` の 2 モジュールのみ）。
[(T.Gterm_Z)](#t-Gterm_Z) は Lean で `@[simp]` 補題として登録されているので、
後続の章の `simp` 呼び出しから暗黙に使われうる。
[(T.Gterm_P)](#t-Gterm_P) は `@[simp]` ではなく、本章の
[(T.mem_Gterm_P)](#t-mem_Gterm_P) の証明でのみ用いられる。
残りの宣言
（[(D.oV)](#d-oV), [(T.oV_Z)](#t-oV_Z), [(T.oV_P)](#t-oV_P), [(T.psi_le_oV)](#t-psi_le_oV),
[(D.allprinc_lt)](#d-allprinc_lt), [(T.allprinc_lt_Z)](#t-allprinc_lt_Z),
[(T.allprinc_lt_P)](#t-allprinc_lt_P), [(T.oV_lt_of_allprinc)](#t-oV_lt_of_allprinc),
[(D.spinesub_le)](#d-spinesub_le), [(T.spinesub_le_Z)](#t-spinesub_le_Z),
[(T.spinesub_le_P)](#t-spinesub_le_P), [(T.spinesub_le_mono)](#t-spinesub_le_mono),
[(D.hdle)](#d-hdle), [(T.hdle_Z)](#t-hdle_Z), [(T.hdle_P_Z)](#t-hdle_P_Z),
[(T.hdle_P_P)](#t-hdle_P_P), [(D.wf3)](#d-wf3), [(T.wf3_Z)](#t-wf3_Z), [(T.wf3_P)](#t-wf3_P),
[(T.wf3_spinesub_le)](#t-wf3_spinesub_le), [(D.headle_all)](#d-headle_all),
[(T.headle_all_Z)](#t-headle_all_Z), [(T.headle_all_P)](#t-headle_all_P),
[(T.hdle_head_ignores_tail)](#t-hdle_head_ignores_tail)）
は後続の章から引用されない。
