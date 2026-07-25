[← 目次](README.md)

# Nrm — 射影 $`\mathrm{proj}`$、正規化 $`\mathrm{nrm}`$、展開の接頭辞可換性

本章は 2 つの部分からなる。前半では、臨界項の集合 $`G_u`$ を列として計算する $`\mathrm{Glist}_u`$、
その列の $`\prec`$ に関する走査最大元 $`\mathrm{maxo}`$、条件 $`\forall g\in G_u(t),\ g\prec t`$ が
成り立つまで最大臨界項へ移る反復 $`\mathrm{proj}_u`$、吸収付き挿入 $`\mathrm{ins}`$、および正規化 $`\mathrm{nrm}`$ を定義する。
後半では、標準形の長さと先頭に関する 2 つの事実（$`0<\lvert M\rvert`$ と $`M`$ の先頭が $`(0,0)`$）と、
展開の接頭辞可換性 $`(A\mathbin{+\!\!+}T)[n] = A\mathbin{+\!\!+}T[n]`$（$`2\le\lvert T\rvert`$ かつ $`T_{0,0}=0`$ のとき）を証明する。
後者は、親子関係 $`\to_0`$, $`\to_1`$, $`\le_0`$, $`\mathrm{hasParent}`$, $`\mathrm{par}`$ のすべてが
接尾辞不変であること（接頭辞 $`A`$ を付けても添字をずらせば変わらないこと）に帰着する。

## 記法

この章で導入する Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `oltDecidable` | — | $`x\prec y`$ の決定手続き |
| `Glist u t` | $`\mathrm{Glist}_u(t)`$ | 臨界項を並べた列 |
| `maxo x L` | $`\mathrm{maxo}(x,L)`$ | $`x`$ を初期値とする $`\prec`$ 走査最大元 |
| `(Glist u b).filter (fun g => ¬ olt g b)` | $`\mathrm{bad}_u(b)`$ | $`\mathrm{Glist}_u(b)`$ のうち $`\neg(g\prec b)`$ なるものの列 |
| `proj u b` | $`\mathrm{proj}_u b`$ | 崩壊点における射影 |
| `ins a b t` | $`\mathrm{ins}(a,b,t)`$ | 吸収付き挿入 |
| `nrm t` | $`\mathrm{nrm}\,t`$ | 値の正規化 |

他の章で定義された記号は次のように書く。

| Lean | 本文 | 定義場所 |
|---|---|---|
| `Three` | $`\mathrm{Three}`$ | [(D.Three)](Mechanized.md#d-Three) |
| `Z`, `P a b c` | $`\mathsf{Z}`$, $`\mathsf{P}(a,b,c)`$ | [(D.Three)](Mechanized.md#d-Three) |
| `olt x y` | $`x \prec y`$ | [(D.olt)](Mechanized.md#d-olt) |
| `Gterm u t` | $`G_u(t)`$ | [(D.Gterm)](Otembed.md#d-Gterm) |
| `tsize t` | $`\mathrm{tsize}\,t`$ | [(D.tsize)](Wfsum.md#d-tsize) |
| `PairSeq` | $`\mathrm{PairSeq}`$ | [(D.PairSeq)](Def.md#d-PairSeq) |
| `M.length` | $`\lvert M\rvert`$ | — |
| `M.getD j (0,0)` | $`M\langle j\rangle`$ | [(D.entry)](Def.md#d-entry) の規約 |
| `entry M i j` | $`M_{i,j}`$ | [(D.entry)](Def.md#d-entry) |
| `nextrel0 M j0 j1` | $`j_0 \to^M_0 j_1`$ | [(D.nextrel0)](Def.md#d-nextrel0) |
| `le0 M j0 j1` | $`j_0 \le^M_0 j_1`$ | [(D.le0)](Def.md#d-le0) |
| `nextrel1 M j0 j1` | $`j_0 \to^M_1 j_1`$ | [(D.nextrel1)](Def.md#d-nextrel1) |
| `nextR M i j0 j1` | $`j_0 \to^M_i j_1`$ | [(D.nextR)](Def.md#d-nextR) |
| `idx1 M j` | $`\mathrm{idx}_1(M,j)`$ | [(D.idx1)](Def.md#d-idx1) |
| `hasParent M i j1` | $`\mathrm{hasParent}(M,i,j_1)`$ | [(D.hasParent)](Def.md#d-hasParent) |
| `parent M i j1` | $`\mathrm{par}^M_i(j_1)`$ | [(D.parent)](Def.md#d-parent) |
| `Pred M` | $`\mathrm{Pred}\,M`$ | [(D.Pred)](Def.md#d-Pred) |
| `M⟦n⟧` | $`M[n]`$ | [(D.oper)](Def.md#d-oper) |
| `diagSeq a b` | $`\Delta_a^b`$ | [(D.diagSeq)](Def.md#d-diagSeq) |
| `ST_PS M` | $`M \in \mathrm{ST\_PS}`$ | [(D.ST_PS)](Def.md#d-ST_PS) |

リストと対に関する記法は [`Mechanized.md`](Mechanized.md) の「記法」節に従う。すなわち
$`\pi_0 p`$, $`\pi_1 p`$ は対 $`p`$ の第 0・第 1 成分、
$`xs \mathbin{+\!\!+} ys`$ は連結、$`x \mathbin{::} xs`$ は先頭付加、
$`\mathrm{take}\,j\,L`$ は先頭 $`j`$ 個、$`\mathrm{dropLast}\,L`$ は末尾 1 個を除いた列、
$`\mathrm{map}\,f\,L`$ は各要素に $`f`$ を適用した列、$`\mathrm{flatMap}\,f\,L`$ は
$`f`$ の値（列）を $`L`$ の順に連結した列、$`\mathrm{range}(n) = [0,\dots,n-1]`$、
$`\mathrm{range}'(a,m) = [a,\dots,a+m-1]`$ である。さらに本章では次を用いる。

- $`\mathrm{headI}\,L`$ は $`L`$ の先頭要素、$`L = ()`$ のときは既定値。
  $`\mathrm{Three}`$ の既定値は構成子の第 1 のもの $`\mathsf{Z}`$ である（Lean の `deriving Inhabited`）。
- $`\mathrm{tail}\,L`$ は $`L`$ の先頭 1 個を除いた列、$`L = ()`$ のときは $`()`$。
- $`\mathrm{filter}\,p\,L`$ は $`L`$ のうち $`p`$ が真である要素を、$`L`$ における順序を保って並べた列。
  その要素判定は $`x \in \mathrm{filter}\,p\,L \iff x \in L \wedge p(x)`$ である。
- $`L[i]?`$ は位置 $`i`$ の要素をもつなら「その要素」、$`i \ge \lvert L\rvert`$ なら「無し」を返すオプション値。
  $`M\langle j\rangle`$ は $`M[j]?`$ が要素 $`p`$ をもつときは $`p`$、無しのときは $`(0,0)`$ に等しい。
- 自然数の減法はすべて切り捨て減法である（$`a<b`$ のとき $`a-b=0`$）。

---

## $`\prec`$ の決定可能性

<a id="d-oltDecidable"></a>
### 定義 $`\prec`$ の決定手続き (D.oltDecidable)

任意の $`x, y \in \mathrm{Three}`$ に対し、命題 $`x \prec y`$（[(D.olt)](Mechanized.md#d-olt)）の
決定手続き、すなわち $`x\prec y`$ の証明か $`\neg(x\prec y)`$ の証明のいずれかを与えるデータを、
$`x`$ と $`y`$ の構造に関する同時再帰で定義する。

- $`(x,y) = (\mathsf{Z},\mathsf{Z})`$：$`\neg(\mathsf{Z}\prec\mathsf{Z})`$ を返す。
  [(T.olt_Z_Z)](Mechanized.md#t-olt_Z_Z) により $`\mathsf{Z}\prec\mathsf{Z}`$ は定義により $`\bot`$ であるから、
  その仮定から $`\bot`$ が直ちに得られる（Lean の `isFalse (fun h => h)`）。
- $`(x,y) = (\mathsf{Z},\mathsf{P}(e,f,g))`$：$`\mathsf{Z}\prec\mathsf{P}(e,f,g)`$ を返す。
  [(T.olt_Z_P)](Mechanized.md#t-olt_Z_P) により定義から成り立つ。
- $`(x,y) = (\mathsf{P}(a,b,c),\mathsf{Z})`$：$`\neg(\mathsf{P}(a,b,c)\prec\mathsf{Z})`$ を返す。
  [(T.olt_P_Z)](Mechanized.md#t-olt_P_Z) による。
- $`(x,y) = (\mathsf{P}(a,b,c),\mathsf{P}(e,f,g))`$：再帰呼び出しにより $`b\prec f`$ の決定手続きと
  $`c\prec g`$ の決定手続きを得る。$`a<e`$ と $`a=e`$ は自然数上で決定可能である。
  [(T.olt_P_P)](Mechanized.md#t-olt_P_P) より
  ```math
  \mathsf{P}(a,b,c)\prec\mathsf{P}(e,f,g)\iff a<e \vee (a=e \wedge b\prec f) \vee (a=e\wedge b=f\wedge c\prec g)
  ```
  であり、右辺は決定可能な命題の連言・選言と $`b=f`$（$`\mathrm{Three}`$ は等号決定可能）で
  構成されているから決定可能である。同値な命題は決定可能性を移す。

再帰呼び出しの引数 $`(b,f)`$ と $`(c,g)`$ の第 1 成分 $`b`$, $`c`$ は $`\mathsf{P}(a,b,c)`$ の真部分項であるから、
この同時再帰は $`x`$ の構造に関する再帰として整合的である。

この決定手続きは、[(D.proj)](#d-proj) の定義に現れる $`\mathrm{filter}`$ が
述語 $`\lambda g.\ \neg(g\prec b)`$ を真偽値として評価できるために必要である。

---

## 臨界項の実行可能な収集

<a id="d-Glist"></a>
### 定義 臨界項の列 (D.Glist)

$`u \in \mathbb{N}`$ に対し、$`\mathrm{Three}`$ の項に $`\mathrm{Three}`$ の有限列を対応させる写像
$`\mathrm{Glist}_u`$ を、引数の構造に関する再帰で定める。

```math
\mathrm{Glist}_u(\mathsf{Z}) := (),\qquad
\mathrm{Glist}_u(\mathsf{P}(a,b,c)) :=
\Bigl(u\le a \text{ ならば } b \mathbin{::} \mathrm{Glist}_u(b),\ \text{さもなくば } ()\Bigr)
\mathbin{+\!\!+} \mathrm{Glist}_u(c).
```

再帰呼び出しの引数 $`b`$, $`c`$ は $`\mathsf{P}(a,b,c)`$ の真部分項であるから、この定義は整合的である。
これは集合値の $`G_u`$（[(D.Gterm)](Otembed.md#d-Gterm)）を列として計算するものであり、
両者が同じ要素をもつことは [(T.mem_Glist)](#t-mem_Glist) で示す。

<a id="t-Glist_Z"></a>
### 定理 $`\mathrm{Glist}`$ の $`\mathsf{Z}`$ での値 (T.Glist_Z)

**主張** $`\mathrm{Glist}_u(\mathsf{Z}) = ()`$。

**証明** [(D.Glist)](#d-Glist) の第 1 式そのものであり、両辺は定義により同一である。∎

<a id="t-Glist_P"></a>
### 定理 $`\mathrm{Glist}`$ の $`\mathsf{P}`$ での値 (T.Glist_P)

**主張** $`u, a \in \mathbb{N}`$、$`b, c \in \mathrm{Three}`$ に対し
```math
\mathrm{Glist}_u(\mathsf{P}(a,b,c)) =
\Bigl(u\le a \text{ ならば } b \mathbin{::} \mathrm{Glist}_u(b),\ \text{さもなくば } ()\Bigr)
\mathbin{+\!\!+} \mathrm{Glist}_u(c).
```

**証明** [(D.Glist)](#d-Glist) の第 2 式そのものであり、両辺は定義により同一である。∎

<a id="t-mem_Glist"></a>
### 定理 $`\mathrm{Glist}`$ と $`G_u`$ の要素の一致 (T.mem_Glist)

**主張** $`u \in \mathbb{N}`$、$`t, x \in \mathrm{Three}`$ に対し
```math
x \in \mathrm{Glist}_u(t) \iff x \in G_u(t).
```

**証明** $`x`$ と $`u`$ を固定し、$`t`$ の構造に関する帰納法を行う。帰納法の述語は
```math
\Phi(t) :\equiv \bigl(x \in \mathrm{Glist}_u(t) \iff x \in G_u(t)\bigr).
```

- 基底段 $`t=\mathsf{Z}`$：[(T.Glist_Z)](#t-Glist_Z) より $`\mathrm{Glist}_u(\mathsf{Z}) = ()`$ であり、
  空列は要素をもたないから左辺は偽。[(T.Gterm_Z)](Otembed.md#t-Gterm_Z) より $`G_u(\mathsf{Z}) = \emptyset`$ であり、
  右辺も偽。偽どうしは同値であるから $`\Phi(\mathsf{Z})`$。
- 帰納段 $`t=\mathsf{P}(a,b,c)`$：帰納法の仮定は
  ```math
  \Phi(b) :\equiv \bigl(x \in \mathrm{Glist}_u(b) \iff x \in G_u(b)\bigr),\qquad
    \Phi(c) :\equiv \bigl(x \in \mathrm{Glist}_u(c) \iff x \in G_u(c)\bigr)
  ```
  である。[(T.Glist_P)](#t-Glist_P) と [(T.mem_Gterm_P)](Otembed.md#t-mem_Gterm_P)
  ```math
  x \in G_u(\mathsf{P}(a,b,c)) \iff \bigl(u\le a \wedge (x=b \vee x\in G_u(b))\bigr) \vee x \in G_u(c)
  ```
  を用いて、$`u \le a`$ か否かで場合分けする。

  - $`u\le a`$ のとき：左辺は $`x \in (b \mathbin{::} \mathrm{Glist}_u(b)) \mathbin{+\!\!+} \mathrm{Glist}_u(c)`$、
    すなわち連結と先頭付加の要素判定より
    ```math
    x = b \ \vee\ x \in \mathrm{Glist}_u(b) \ \vee\ x \in \mathrm{Glist}_u(c)
    ```
    と同値。右辺は $`u\le a`$ が真だから
    ```math
    \bigl(x=b \vee x\in G_u(b)\bigr) \vee x \in G_u(c)
    ```
    と同値。$`\Phi(b)`$, $`\Phi(c)`$ で第 2・第 3 の選言肢を書き換え、$`\vee`$ の結合律で括りを直すと両者は一致する。
  - $`\neg(u\le a)`$ のとき：左辺は $`x \in () \mathbin{+\!\!+} \mathrm{Glist}_u(c) = \mathrm{Glist}_u(c)`$
    と同値。右辺の第 1 選言肢は $`u\le a`$ が偽だから偽であり、右辺は $`x \in G_u(c)`$ と同値。
    $`\Phi(c)`$ より両者は一致する。

  いずれの場合も $`\Phi(\mathsf{P}(a,b,c))`$ が成り立つ。∎

<a id="d-maxo"></a>
### 定義 走査最大元 (D.maxo)

$`x \in \mathrm{Three}`$ と $`\mathrm{Three}`$ の有限列 $`L`$ に対し、$`\mathrm{maxo}(x,L)`$ を
$`L`$ の構造に関する再帰で定める。

```math
\mathrm{maxo}(x, ()) := x,\qquad
  \mathrm{maxo}(x, y \mathbin{::} ys) := \mathrm{maxo}\bigl(x\prec y \text{ ならば } y \text{、さもなくば } x,\ ys\bigr).
```

すなわち $`x`$ を初期値として $`L`$ を左から走査し、現在値 $`z`$ に対し $`z \prec y`$ が成り立つときのみ
$`z`$ を $`y`$ に置き換える。条件 $`x \prec y`$ の判定には [(D.oltDecidable)](#d-oltDecidable) を用いる。
本章で用いる性質は [(T.maxo_in)](#t-maxo_in) の要素性のみである。

<a id="t-maxo_nil"></a>
### 定理 空列に対する $`\mathrm{maxo}`$ (T.maxo_nil)

**主張** $`\mathrm{maxo}(x, ()) = x`$。

**証明** [(D.maxo)](#d-maxo) の第 1 式そのものである。∎

<a id="t-maxo_cons"></a>
### 定理 先頭付加に対する $`\mathrm{maxo}`$ (T.maxo_cons)

**主張** $`\mathrm{maxo}(x, y\mathbin{::}ys) = \mathrm{maxo}\bigl(x\prec y \text{ ならば } y \text{、さもなくば } x,\ ys\bigr)`$。

**証明** [(D.maxo)](#d-maxo) の第 2 式そのものである。∎

<a id="t-maxo_in"></a>
### 定理 $`\mathrm{maxo}`$ の値は元の列に属する (T.maxo_in)

**主張** 任意の $`x\in\mathrm{Three}`$ と有限列 $`ys`$ に対し $`\mathrm{maxo}(x,ys) \in x \mathbin{::} ys`$。

**証明** $`ys`$ の構造に関する帰納法（$`x`$ は全称量化したまま動かす）。帰納法の述語は
```math
\Phi(ys) :\equiv \forall x \in \mathrm{Three},\ \mathrm{maxo}(x,ys) \in x \mathbin{::} ys.
```

- 基底段 $`ys=()`$：[(T.maxo_nil)](#t-maxo_nil) より $`\mathrm{maxo}(x,())=x`$ であり、
  $`x \in (x)`$ が成り立つ。よって $`\Phi(())`$。
- 帰納段 $`ys = y \mathbin{::} ys'`$：帰納法の仮定は
  ```math
  \Phi(ys') :\equiv \forall x\in\mathrm{Three},\ \mathrm{maxo}(x,ys') \in x \mathbin{::} ys'
  ```
  である。$`x`$ を任意に取る。[(T.maxo_cons)](#t-maxo_cons) より
  $`\mathrm{maxo}(x,y\mathbin{::}ys') = \mathrm{maxo}(z,ys')`$、ここで $`z`$ は $`x\prec y`$ ならば $`y`$、
  さもなくば $`x`$ である。$`x \prec y`$ の真偽で場合分けする。

  - $`x\prec y`$ のとき：$`z=y`$。帰納法の仮定 $`\Phi(ys')`$ を $`x:=y`$ に適用して
    $`\mathrm{maxo}(y,ys') \in y\mathbin{::}ys'`$、すなわち
    $`\mathrm{maxo}(y,ys')=y`$ または $`\mathrm{maxo}(y,ys')\in ys'`$。
    前者なら $`\mathrm{maxo}(x,y\mathbin{::}ys') = y \in x\mathbin{::}y\mathbin{::}ys'`$。
    後者なら $`ys'`$ の要素はすべて $`x\mathbin{::}y\mathbin{::}ys'`$ の要素であるから、やはり属する。
  - $`\neg(x\prec y)`$ のとき：$`z=x`$。帰納法の仮定 $`\Phi(ys')`$ を $`x:=x`$ に適用して
    $`\mathrm{maxo}(x,ys') \in x\mathbin{::}ys'`$、すなわち
    $`\mathrm{maxo}(x,ys')=x`$ または $`\mathrm{maxo}(x,ys')\in ys'`$。
    いずれの場合も $`x\mathbin{::}y\mathbin{::}ys'`$ の要素である。

  よって $`\Phi(y\mathbin{::}ys')`$。∎

<a id="t-maxo_hdtl_in"></a>
### 定理 先頭と残りに対する $`\mathrm{maxo}`$ の要素性 (T.maxo_hdtl_in)

**主張** 有限列 $`gs`$ が $`gs \ne ()`$ を満たすならば
$`\mathrm{maxo}(\mathrm{headI}\,gs,\ \mathrm{tail}\,gs) \in gs`$。

**証明** $`gs`$ の構成子で場合分けする。

- $`gs=()`$：仮定 $`gs\ne()`$ に反するので、この場合は起こらない。
- $`gs = g \mathbin{::} gs'`$：$`\mathrm{headI}\,gs = g`$、$`\mathrm{tail}\,gs = gs'`$ であるから、
  主張は $`\mathrm{maxo}(g,gs') \in g\mathbin{::}gs'`$ となり、
  これは [(T.maxo_in)](#t-maxo_in) を $`x:=g`$, $`ys:=gs'`$ に適用したものである。∎

---

## 崩壊点における射影

以下、$`u\in\mathbb{N}`$ と $`b\in\mathrm{Three}`$ に対して
```math
\mathrm{bad}_u(b) := \mathrm{filter}\,\bigl(\lambda g.\ \neg(g\prec b)\bigr)\ \mathrm{Glist}_u(b)
```
と書く（$`\mathrm{filter}`$ の述語判定は [(D.oltDecidable)](#d-oltDecidable) による）。
$`\mathrm{filter}`$ の要素判定より
```math
g \in \mathrm{bad}_u(b) \iff \bigl(g \in \mathrm{Glist}_u(b) \ \wedge\ \neg(g\prec b)\bigr) \tag{$\ast$}
```
が成り立つ。特に $`\mathrm{bad}_u(b) = ()`$ は
「$`\forall g\in\mathrm{Glist}_u(b),\ g\prec b`$」と同値である。

<a id="d-proj"></a>
### 定義 崩壊点における射影 (D.proj)

$`u\in\mathbb{N}`$ に対し $`\mathrm{proj}_u : \mathrm{Three}\to\mathrm{Three}`$ を
$`\mathrm{tsize}\,b`$（[(D.tsize)](Wfsum.md#d-tsize)）に関する整礎再帰で定める。

```math
\mathrm{proj}_u b := \begin{cases}
b & \bigl(\mathrm{bad}_u(b) = ()\bigr) \\[2pt]
\mathrm{proj}_u\bigl(\mathrm{maxo}(\mathrm{headI}\,\mathrm{bad}_u(b),\ \mathrm{tail}\,\mathrm{bad}_u(b))\bigr)
 & \bigl(\mathrm{bad}_u(b) \ne ()\bigr)
\end{cases}
```

**再帰の整合性（減少性）.** 第 2 の場合、
$`m := \mathrm{maxo}(\mathrm{headI}\,\mathrm{bad}_u(b),\ \mathrm{tail}\,\mathrm{bad}_u(b))`$ とおくと、
[(T.maxo_hdtl_in)](#t-maxo_hdtl_in)（$`\mathrm{bad}_u(b)\ne()`$ による）より $`m \in \mathrm{bad}_u(b)`$。
$`(\ast)`$ より $`m \in \mathrm{Glist}_u(b)`$、[(T.mem_Glist)](#t-mem_Glist) より $`m \in G_u(b)`$、
よって [(T.Gterm_tsize)](Otembed.md#t-Gterm_tsize) より
```math
\mathrm{tsize}\,m < \mathrm{tsize}\,b .
```
したがって再帰は $`\mathrm{tsize}`$ を真に減少させ、$`\mathbb{N}`$ の $`<`$ が整礎であるからこの定義は整合的である。

<a id="t-proj_id"></a>
### 定理 $`\mathrm{proj}`$ の停止条件 (T.proj_id)

**主張** $`\mathrm{bad}_u(b) = ()`$ ならば $`\mathrm{proj}_u b = b`$。

**証明** [(D.proj)](#d-proj) の定義方程式で条件 $`\mathrm{bad}_u(b)=()`$ が成り立つ場合であり、
第 1 の場合の値 $`b`$ がそのまま結果である。∎

<a id="t-proj_rec"></a>
### 定理 $`\mathrm{proj}`$ の再帰段 (T.proj_rec)

**主張** $`\mathrm{bad}_u(b) \ne ()`$ ならば
```math
\mathrm{proj}_u b = \mathrm{proj}_u\bigl(\mathrm{maxo}(\mathrm{headI}\,\mathrm{bad}_u(b),\ \mathrm{tail}\,\mathrm{bad}_u(b))\bigr).
```

**証明** [(D.proj)](#d-proj) の定義方程式で条件 $`\mathrm{bad}_u(b)=()`$ が成り立たない場合であり、
第 2 の場合の値がそのまま結果である。∎

<a id="t-proj_G"></a>
### 定理 射影は OT3 条件を満たす (T.proj_G)

**主張** 任意の $`u\in\mathbb{N}`$、$`b\in\mathrm{Three}`$ に対し
```math
\forall g \in G_u(\mathrm{proj}_u b),\ g \prec \mathrm{proj}_u b .
```

**証明** $`u`$ を固定し、$`n := \mathrm{tsize}\,b`$ に関する $`\mathbb{N}`$ 上の強帰納法を行う。帰納法の述語は
```math
\Psi(n) :\equiv \forall b\in\mathrm{Three},\ \bigl(\mathrm{tsize}\,b = n \to
  \forall g \in G_u(\mathrm{proj}_u b),\ g \prec \mathrm{proj}_u b\bigr),
```
帰納法の仮定は $`\forall m<n,\ \Psi(m)`$ である（強帰納法であるから基底段は $`n=0`$ の特別扱いを要さず、
$`n`$ より真に小さいすべての $`m`$ について $`\Psi(m)`$ を仮定して $`\Psi(n)`$ を示す）。

$`b`$ を $`\mathrm{tsize}\,b = n`$ なるものとし、$`\mathrm{bad}_u(b)`$ が空か否かで場合分けする。

- $`\mathrm{bad}_u(b) = ()`$ のとき：[(T.proj_id)](#t-proj_id) より $`\mathrm{proj}_u b = b`$ であるから、
  示すべきは $`\forall g\in G_u(b),\ g\prec b`$ である。
  $`g \in G_u(b)`$ を任意に取る。[(T.mem_Glist)](#t-mem_Glist) より $`g \in \mathrm{Glist}_u(b)`$。
  ここで $`\neg(g\prec b)`$ と仮定すると、$`(\ast)`$ より $`g \in \mathrm{bad}_u(b) = ()`$ となるが、
  空列は要素をもたないから矛盾である。よって $`g \prec b`$。
- $`\mathrm{bad}_u(b) \ne ()`$ のとき：
  $`m := \mathrm{maxo}(\mathrm{headI}\,\mathrm{bad}_u(b),\ \mathrm{tail}\,\mathrm{bad}_u(b))`$ とおくと、
  [(T.proj_rec)](#t-proj_rec) より $`\mathrm{proj}_u b = \mathrm{proj}_u m`$ である。
  [(T.maxo_hdtl_in)](#t-maxo_hdtl_in) より $`m \in \mathrm{bad}_u(b)`$、$`(\ast)`$ より
  $`m \in \mathrm{Glist}_u(b)`$、[(T.mem_Glist)](#t-mem_Glist) より $`m \in G_u(b)`$、
  [(T.Gterm_tsize)](Otembed.md#t-Gterm_tsize) より $`\mathrm{tsize}\,m < \mathrm{tsize}\,b = n`$。
  $`\mathrm{tsize}\,m < n`$ であるから帰納法の仮定を自然数 $`\mathrm{tsize}\,m`$ に適用でき、
  得られた $`\Psi(\mathrm{tsize}\,m)`$ を項 $`m`$（$`\mathrm{tsize}\,m = \mathrm{tsize}\,m`$ による）に用いて
  ```math
  \forall g \in G_u(\mathrm{proj}_u m),\ g \prec \mathrm{proj}_u m
  ```
  を得る。$`\mathrm{proj}_u b = \mathrm{proj}_u m`$ でこれを書き換えれば求める主張である。

以上で $`\Psi(n)`$ が示され、すべての $`n`$ について $`\Psi(n)`$、すなわち主張が成り立つ。∎

---

## 吸収付きの和への挿入と $`\mathrm{nrm}`$

<a id="d-ins"></a>
### 定義 吸収付き挿入 (D.ins)

$`a\in\mathbb{N}`$、$`b\in\mathrm{Three}`$ に対し $`\mathrm{ins}(a,b,\cdot) : \mathrm{Three}\to\mathrm{Three}`$ を
第 3 引数の構成子で場合分けして定める。

```math
\mathrm{ins}(a,b,\mathsf{Z}) := \mathsf{P}(a,b,\mathsf{Z}),\qquad
\mathrm{ins}(a,b,\mathsf{P}(e,f,g)) := \begin{cases}
\mathsf{P}(e,f,g) & \bigl(a<e \ \vee\ (a=e \wedge b\prec f)\bigr) \\
\mathsf{P}(a,b,\mathsf{P}(e,f,g)) & \text{その他}
\end{cases}
```

条件 $`a<e \vee (a=e\wedge b\prec f)`$ は、[(T.olt_P_P)](Mechanized.md#t-olt_P_P) の右辺の
第 1・第 2 選言肢であり、主要項どうしの比較 $`\mathsf{P}(a,b,\mathsf{Z}) \prec \mathsf{P}(e,f,g)`$ を
先頭添字と引数だけで判定したものである。この条件が成り立つとき挿入すべき主要項は
先頭の主要項に吸収され、$`\mathrm{ins}`$ は第 3 引数をそのまま返す。

<a id="t-ins_Z"></a>
### 定理 $`\mathrm{ins}`$ の $`\mathsf{Z}`$ での値 (T.ins_Z)

**主張** $`\mathrm{ins}(a,b,\mathsf{Z}) = \mathsf{P}(a,b,\mathsf{Z})`$。

**証明** [(D.ins)](#d-ins) の第 1 式そのものである。∎

<a id="t-ins_P"></a>
### 定理 $`\mathrm{ins}`$ の $`\mathsf{P}`$ での値 (T.ins_P)

**主張** $`a,e\in\mathbb{N}`$、$`b,f,g\in\mathrm{Three}`$ に対し
```math
\mathrm{ins}(a,b,\mathsf{P}(e,f,g)) = \begin{cases}
\mathsf{P}(e,f,g) & \bigl(a<e \vee (a=e \wedge b\prec f)\bigr) \\
\mathsf{P}(a,b,\mathsf{P}(e,f,g)) & \text{その他.}
\end{cases}
```

**証明** [(D.ins)](#d-ins) の第 2 式そのものである。∎

<a id="d-nrm"></a>
### 定義 値の正規化 (D.nrm)

$`\mathrm{nrm} : \mathrm{Three}\to\mathrm{Three}`$ を構造に関する再帰で定める。

```math
\mathrm{nrm}\,\mathsf{Z} := \mathsf{Z},\qquad
  \mathrm{nrm}\,\mathsf{P}(a,b,c) := \mathrm{ins}\bigl(a,\ \mathrm{proj}_a(\mathrm{nrm}\,b),\ \mathrm{nrm}\,c\bigr)
```

（[(D.ins)](#d-ins), [(D.proj)](#d-proj)）。再帰呼び出しの引数 $`b`$, $`c`$ は
$`\mathsf{P}(a,b,c)`$ の真部分項であるから、この定義は整合的である。
主要項 $`\mathsf{P}(a,b,c)`$ に対しては、引数 $`b`$ を正規化したうえでその添字 $`a`$ における射影を取り
（[(T.proj_G)](#t-proj_G) により $`\forall g\in G_a(\mathrm{proj}_a(\mathrm{nrm}\,b)),\ g\prec\mathrm{proj}_a(\mathrm{nrm}\,b)`$ が成り立つ）、
それを正規化した後続和 $`\mathrm{nrm}\,c`$ へ吸収付きで挿入する。

<a id="t-nrm_Z"></a>
### 定理 $`\mathrm{nrm}`$ の $`\mathsf{Z}`$ での値 (T.nrm_Z)

**主張** $`\mathrm{nrm}\,\mathsf{Z} = \mathsf{Z}`$。

**証明** [(D.nrm)](#d-nrm) の第 1 式そのものである。∎

<a id="t-nrm_P"></a>
### 定理 $`\mathrm{nrm}`$ の $`\mathsf{P}`$ での値 (T.nrm_P)

**主張** $`a\in\mathbb{N}`$、$`b,c\in\mathrm{Three}`$ に対し
$`\mathrm{nrm}\,\mathsf{P}(a,b,c) = \mathrm{ins}(a,\ \mathrm{proj}_a(\mathrm{nrm}\,b),\ \mathrm{nrm}\,c)`$。

**証明** [(D.nrm)](#d-nrm) の第 2 式そのものである。∎

---

## 宣言を含まない注記節

Lean 側のソースには、この位置に 5 つの注記ブロック
（`## Value preservation of ins`、`## The remaining core: order preservation on NF`、
`### Reduction of oV_nf_order_pres …`、`### The argument-branch head …`、
`### Why the argument head needs proj …`）が置かれている。
これらはいずれもコメントのみであり、宣言（定義・定理）を 1 つも含まない。
記述内容は、本停止性証明では採用されなかった経路（順序数値 $`\mathrm{oV}`$ を経由する
順序保存 `nrm_order_pres`）に関する設計上の記録である。
[`requirement.md`](../requirement.md) §3.3 により、停止性証明に使われない命題は本文の対象外であるから、
ここでは節の存在のみを記録する。

---

## 標準形の長さと先頭

次の 2 つの定理は、上記の注記ブロックの直後に置かれた宣言である。
いずれも [(D.ST_PS)](Def.md#d-ST_PS) の導出に関する帰納法で証明される。

<a id="t-stps_len_pos"></a>
### 定理 標準形は空でない (T.stps_len_pos)

**主張** $`M \in \mathrm{ST\_PS}`$ ならば $`0 < \lvert M\rvert`$。

**証明** [(D.ST_PS)](Def.md#d-ST_PS) の導出に関する帰納法。帰納法の述語は
```math
P(M) :\equiv 0 < \lvert M\rvert .
```

- 基底段（規則 (diag)）：$`M = \Delta_0^v`$。$`0\le v`$ であるから
  [(T.diagSeq_cons)](Wf.md#t-diagSeq_cons) より $`\Delta_0^v = (0,0)\mathbin{::}\Delta_1^v`$ であり、
  ```math
  \lvert \Delta_0^v\rvert = 1 + \lvert\Delta_1^v\rvert \ge 1 > 0 .
  ```
  よって $`P(\Delta_0^v)`$。
- 帰納段（規則 (oper)）：$`N\in\mathrm{ST\_PS}`$、$`1\le n`$ とし、帰納法の仮定
  $`P(N) :\equiv 0<\lvert N\rvert`$ の下で $`P(N[n]) :\equiv 0<\lvert N[n]\rvert`$ を示す。
  $`1<\lvert N\rvert`$ か否かで場合分けする。

  - $`1 < \lvert N\rvert`$ のとき：[(T.oper_eq_dropLast_append)](Wf.md#t-oper_eq_dropLast_append) より、
    ある $`R`$ が存在して $`N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R`$。よって
    ```math
    \lvert N[n]\rvert = \lvert \mathrm{dropLast}\,N\rvert + \lvert R\rvert
      = (\lvert N\rvert - 1) + \lvert R\rvert .
    ```
    $`1<\lvert N\rvert`$ すなわち $`\lvert N\rvert \ge 2`$ より $`\lvert N\rvert - 1 \ge 1`$ であるから
    $`\lvert N[n]\rvert \ge 1 > 0`$。
  - $`\neg(1<\lvert N\rvert)`$ のとき：$`\lvert N\rvert \le 1`$ であるから
    [(T.oper_eq_self_short)](Proofs.md#t-oper_eq_self_short) より $`N[n] = N`$ であり、
    帰納法の仮定 $`0<\lvert N\rvert`$ がそのまま $`0<\lvert N[n]\rvert`$ を与える。

  よって $`P(N[n])`$。∎

<a id="t-stps_head"></a>
### 定理 標準形の先頭は $`(0,0)`$ (T.stps_head)

**主張** $`M \in \mathrm{ST\_PS}`$ ならば $`M`$ の先頭要素（$`M=()`$ のときの既定値を $`(0,0)`$ とする）は $`(0,0)`$ である。
Lean では `M.headD (0,0) = (0,0)`。

**証明** [(D.ST_PS)](Def.md#d-ST_PS) の導出に関する帰納法。帰納法の述語は
```math
Q(M) :\equiv \bigl(M \text{ の先頭要素（既定値 }(0,0)\text{）} = (0,0)\bigr).
```

- 基底段（規則 (diag)）：$`M=\Delta_0^v`$。$`0\le v`$ より
  [(T.diagSeq_cons)](Wf.md#t-diagSeq_cons) から $`\Delta_0^v = (0,0)\mathbin{::}\Delta_1^v`$ であり、
  先頭付加された列の先頭要素は付加された要素そのものであるから $`(0,0)`$ である。よって $`Q(\Delta_0^v)`$。
- 帰納段（規則 (oper)）：$`N\in\mathrm{ST\_PS}`$、$`1\le n`$、帰納法の仮定 $`Q(N)`$ の下で $`Q(N[n])`$ を示す。
  $`1<\lvert N\rvert`$ か否かで場合分けする。

  - $`1<\lvert N\rvert`$ のとき：[(T.oper_eq_dropLast_append)](Wf.md#t-oper_eq_dropLast_append) より
    ある $`R`$ が存在して $`N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R`$。
    $`\lvert N\rvert \ge 2`$ であるから $`N`$ は $`N = p \mathbin{::} q \mathbin{::} u`$ の形に書ける。
    $`\mathrm{dropLast}`$ の定義（要素 2 個以上の列では
    $`\mathrm{dropLast}(p\mathbin{::}q\mathbin{::}u) = p \mathbin{::} \mathrm{dropLast}(q\mathbin{::}u)`$）より
    ```math
    N[n] = \bigl(p \mathbin{::} \mathrm{dropLast}(q\mathbin{::}u)\bigr) \mathbin{+\!\!+} R
           = p \mathbin{::} \bigl(\mathrm{dropLast}(q\mathbin{::}u) \mathbin{+\!\!+} R\bigr)
    ```
    であり、先頭要素は $`p`$。帰納法の仮定 $`Q(N)`$ は $`N`$ の先頭要素が $`(0,0)`$、すなわち $`p=(0,0)`$ を与える。
  - $`\neg(1<\lvert N\rvert)`$ のとき：$`\lvert N\rvert\le 1`$ より
    [(T.oper_eq_self_short)](Proofs.md#t-oper_eq_self_short) から $`N[n]=N`$ であり、
    帰納法の仮定 $`Q(N)`$ がそのまま $`Q(N[n])`$ を与える。

  よって $`Q(N[n])`$。∎

---

## $`\mathrm{oper}`$ の接頭辞可換性：親子関係の接尾辞不変性

本節の目標は [(T.oper_append_right)](#t-oper_append_right)、すなわち
$`2\le\lvert T\rvert`$ かつ $`T_{0,0}=0`$ のとき
```math
(A\mathbin{+\!\!+}T)[n] = A \mathbin{+\!\!+} T[n]
```
である。[(D.oper)](Def.md#d-oper) は末尾の添字 $`j_1`$ とその親の探索、および
$`\mathrm{take}`$・コピーブロックの構成から成るから、そこに現れる
$`M_{i,j}`$, $`\to^M_0`$, $`\le^M_0`$, $`\to^M_1`$, $`\to^M_i`$, $`\mathrm{idx}_1`$,
$`\mathrm{hasParent}`$, $`\mathrm{par}`$ のすべてについて、添字を $`\lvert A\rvert`$ だけずらせば
$`A\mathbin{+\!\!+}T`$ における値が $`T`$ における値と一致することを示せばよい。以下その準備を順に行う。

<a id="t-getD_app_right"></a>
### 定理 連結の右側の読み出し (T.getD_app_right)

**主張** $`A, T \in \mathrm{PairSeq}`$、$`i\in\mathbb{N}`$ が $`\lvert A\rvert \le i`$ を満たすならば
```math
(A\mathbin{+\!\!+}T)\langle i\rangle = T\langle i - \lvert A\rvert\rangle .
```

**証明** $`M\langle j\rangle`$ は、オプション値 $`M[j]?`$ が要素 $`p`$ をもつとき $`p`$、無しのとき $`(0,0)`$ に等しい。
連結の要素検索は、$`\lvert A\rvert \le i`$ のとき
```math
(A\mathbin{+\!\!+}T)[i]? = T[i-\lvert A\rvert]?
```
を満たす（$`A\mathbin{+\!\!+}T`$ の第 $`i`$ 位置は $`A`$ の範囲外であり、$`T`$ の第 $`i-\lvert A\rvert`$ 位置にあたる）。
両辺のオプション値が一致するから、既定値 $`(0,0)`$ による読み出しも一致する。∎

<a id="t-entry_append_right"></a>
### 定理 成分の接尾辞不変性 (T.entry_append_right)

**主張** $`A,T\in\mathrm{PairSeq}`$、$`i,j\in\mathbb{N}`$ に対し
```math
(A\mathbin{+\!\!+}T)_{i,\ \lvert A\rvert + j} = T_{i,j} .
```

**証明** [(D.entry)](Def.md#d-entry) より、左辺は $`i=0`$ のとき
$`\pi_0\bigl((A\mathbin{+\!\!+}T)\langle \lvert A\rvert+j\rangle\bigr)`$、$`i\ne0`$ のとき
$`\pi_1\bigl((A\mathbin{+\!\!+}T)\langle \lvert A\rvert+j\rangle\bigr)`$ である。
$`\lvert A\rvert \le \lvert A\rvert + j`$ であるから [(T.getD_app_right)](#t-getD_app_right) より
```math
(A\mathbin{+\!\!+}T)\langle \lvert A\rvert+j\rangle
 = T\langle (\lvert A\rvert+j) - \lvert A\rvert\rangle = T\langle j\rangle
```
（最後の等号は $`(\lvert A\rvert+j)-\lvert A\rvert = j`$）。よって $`i=0`$, $`i\ne0`$ の
どちらの分岐でも右辺 $`T_{i,j}`$ と一致する。∎

<a id="t-nextrel0_append_right"></a>
### 定理 行 0 直接親子関係の接尾辞不変性 (T.nextrel0_append_right)

**主張** $`A,T\in\mathrm{PairSeq}`$、$`j_0,j_1\in\mathbb{N}`$ に対し
```math
\lvert A\rvert+j_0 \to^{A+\!\!+T}_0 \lvert A\rvert+j_1 \iff j_0 \to^T_0 j_1 .
```

**証明** [(D.nextrel0)](Def.md#d-nextrel0) の 5 条件を両側で比較する。
$`\lvert A\mathbin{+\!\!+}T\rvert = \lvert A\rvert + \lvert T\rvert`$ である。

$`(\Rightarrow)`$ 左辺の 5 条件を $`h_1,\dots,h_5`$ とする。

1. $`h_1 : \lvert A\rvert+j_0 < \lvert A\rvert+\lvert T\rvert`$ の両辺から $`\lvert A\rvert`$ を消去して $`j_0<\lvert T\rvert`$。
2. $`h_2 : \lvert A\rvert+j_1 < \lvert A\rvert+\lvert T\rvert`$ の両辺から $`\lvert A\rvert`$ を消去して $`j_1<\lvert T\rvert`$。
3. $`h_3 : \lvert A\rvert+j_0 < \lvert A\rvert+j_1`$ から $`j_0<j_1`$。
4. $`h_4 : (A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_0} < (A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}`$ を
   [(T.entry_append_right)](#t-entry_append_right) で書き換えて $`T_{0,j_0}<T_{0,j_1}`$。
5. $`j`$ を $`j_0<j<j_1`$ なる任意の自然数とする。すると
   $`\lvert A\rvert+j_0 < \lvert A\rvert+j < \lvert A\rvert+j_1`$ であるから、$`h_5`$ を
   添字 $`\lvert A\rvert+j`$ に適用して
   $`(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1} \le (A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j}`$、
   [(T.entry_append_right)](#t-entry_append_right) で書き換えて $`T_{0,j_1}\le T_{0,j}`$。

$`(\Leftarrow)`$ 右辺の 5 条件を $`h_1,\dots,h_5`$ とする。

1. $`j_0<\lvert T\rvert`$ の両辺に $`\lvert A\rvert`$ を加えて
   $`\lvert A\rvert+j_0 < \lvert A\rvert+\lvert T\rvert = \lvert A\mathbin{+\!\!+}T\rvert`$。
2. $`j_1<\lvert T\rvert`$ の両辺に $`\lvert A\rvert`$ を加えて
   $`\lvert A\rvert+j_1 < \lvert A\rvert+\lvert T\rvert = \lvert A\mathbin{+\!\!+}T\rvert`$。
3. $`j_0<j_1`$ から $`\lvert A\rvert+j_0<\lvert A\rvert+j_1`$。
4. $`T_{0,j_0}<T_{0,j_1}`$ を [(T.entry_append_right)](#t-entry_append_right) で
   $`(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_0} < (A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}`$ に書き換える。
5. $`j`$ を $`\lvert A\rvert+j_0 < j < \lvert A\rvert+j_1`$ なる任意の自然数とする。
   $`j > \lvert A\rvert+j_0 \ge \lvert A\rvert`$ であるから $`j' := j-\lvert A\rvert`$ とおけば
   $`j = \lvert A\rvert+j'`$ と書け、$`j_0<j'<j_1`$ が成り立つ。$`h_5`$ を $`j'`$ に適用して
   $`T_{0,j_1}\le T_{0,j'}`$、[(T.entry_append_right)](#t-entry_append_right) で書き換えて
   $`(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1} \le (A\mathbin{+\!\!+}T)_{0,j}`$。∎

<a id="t-rtg_nextrel0_lift"></a>
### 定理 行 0 到達性の持ち上げ (T.rtg_nextrel0_lift)

**主張** $`\mathrm{ReflTransGen}(\to^T_0)\,j_0\,c`$ ならば
$`\mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,(\lvert A\rvert+j_0)\,(\lvert A\rvert+c)`$。

**証明** 反射推移閉包の導出に関する帰納法。$`j_0`$ を固定し、帰納法の述語を
```math
\Phi(c) :\equiv \mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,(\lvert A\rvert+j_0)\,(\lvert A\rvert+c)
```
とする。$`\mathrm{ReflTransGen}`$ の構成子は反射 (refl) と末尾追加 (tail) の 2 つである。

- 基底段 (refl)：$`c=j_0`$。$`\Phi(j_0)`$ は
  $`\mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,(\lvert A\rvert+j_0)\,(\lvert A\rvert+j_0)`$ であり、
  反射性そのものである。
- 帰納段 (tail)：$`\mathrm{ReflTransGen}(\to^T_0)\,j_0\,b`$ と $`b \to^T_0 c`$ が与えられ、
  帰納法の仮定は $`\Phi(b)`$、すなわち
  $`\mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,(\lvert A\rvert+j_0)\,(\lvert A\rvert+b)`$ である。
  [(T.nextrel0_append_right)](#t-nextrel0_append_right) の $`(\Leftarrow)`$ を $`b\to^T_0 c`$ に適用して
  $`\lvert A\rvert+b \to^{A+\!\!+T}_0 \lvert A\rvert+c`$ を得る。
  これを $`\Phi(b)`$ の末尾に追加すれば $`\Phi(c)`$ が得られる。∎

<a id="t-le0_append_right_of"></a>
### 定理 行 0 祖先関係の持ち上げ (T.le0_append_right_of)

**主張** $`j_0 \le^T_0 j_1`$ ならば $`\lvert A\rvert+j_0 \le^{A+\!\!+T}_0 \lvert A\rvert+j_1`$。

**証明** [(D.le0)](Def.md#d-le0) より仮定は 3 条件
$`j_0<\lvert T\rvert`$、$`j_1<\lvert T\rvert`$、$`\mathrm{ReflTransGen}(\to^T_0)\,j_0\,j_1`$ の連言である。
$`\lvert A\mathbin{+\!\!+}T\rvert = \lvert A\rvert+\lvert T\rvert`$ であるから、
第 1・第 2 条件の両辺に $`\lvert A\rvert`$ を加えて
$`\lvert A\rvert+j_0 < \lvert A\mathbin{+\!\!+}T\rvert`$、$`\lvert A\rvert+j_1 < \lvert A\mathbin{+\!\!+}T\rvert`$ を得る。
第 3 条件からは [(T.rtg_nextrel0_lift)](#t-rtg_nextrel0_lift) により
$`\mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,(\lvert A\rvert+j_0)\,(\lvert A\rvert+j_1)`$ を得る。
3 条件がそろったので [(D.le0)](Def.md#d-le0) の結論が成り立つ。∎

<a id="t-nextrel0_lt"></a>
### 定理 行 0 の辺は添字を増やす (T.nextrel0_lt)

**主張** $`a \to^M_0 b`$ ならば $`a<b`$。

**証明** [(D.nextrel0)](Def.md#d-nextrel0) の第 3 条件そのものである。∎

<a id="t-rtg_nextrel0_unlift"></a>
### 定理 行 0 到達性の引き戻し (T.rtg_nextrel0_unlift)

**主張** $`\mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,(\lvert A\rvert+a)\,c`$ ならば、ある $`c'`$ が存在して
```math
c = \lvert A\rvert + c' \quad\text{かつ}\quad \mathrm{ReflTransGen}(\to^T_0)\,a\,c' .
```

**証明** 反射推移閉包の導出に関する帰納法。$`a`$ を固定し、帰納法の述語を
```math
\Phi(c) :\equiv \exists c',\ \bigl(c=\lvert A\rvert+c' \ \wedge\ \mathrm{ReflTransGen}(\to^T_0)\,a\,c'\bigr)
```
とする。

- 基底段 (refl)：$`c=\lvert A\rvert+a`$。$`c' := a`$ と取れば $`c=\lvert A\rvert+a`$ であり、
  $`\mathrm{ReflTransGen}(\to^T_0)\,a\,a`$ は反射性から成り立つ。よって $`\Phi(\lvert A\rvert+a)`$。
- 帰納段 (tail)：$`\mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,(\lvert A\rvert+a)\,d`$ と
  $`d \to^{A+\!\!+T}_0 e`$ が与えられ、帰納法の仮定は $`\Phi(d)`$ である。
  $`\Phi(d)`$ から $`d' `$ を取り $`d=\lvert A\rvert+d'`$ かつ $`\mathrm{ReflTransGen}(\to^T_0)\,a\,d'`$ とする。
  [(T.nextrel0_lt)](#t-nextrel0_lt) を $`d \to^{A+\!\!+T}_0 e`$ に適用して $`d<e`$、
  $`\lvert A\rvert \le \lvert A\rvert+d' = d < e`$ より $`\lvert A\rvert \le e`$ であるから、
  $`e' := e-\lvert A\rvert`$ とおけば $`e = \lvert A\rvert+e'`$ と書ける。
  [(T.nextrel0_append_right)](#t-nextrel0_append_right) の $`(\Rightarrow)`$ を
  $`\lvert A\rvert+d' \to^{A+\!\!+T}_0 \lvert A\rvert+e'`$ に適用して $`d'\to^T_0 e'`$ を得る。
  これを $`\mathrm{ReflTransGen}(\to^T_0)\,a\,d'`$ の末尾に追加すれば
  $`\mathrm{ReflTransGen}(\to^T_0)\,a\,e'`$ であり、$`e=\lvert A\rvert+e'`$ と合わせて $`\Phi(e)`$。∎

<a id="t-le0_append_right"></a>
### 定理 行 0 祖先関係の接尾辞不変性 (T.le0_append_right)

**主張** $`A,T\in\mathrm{PairSeq}`$、$`j_0,j_1\in\mathbb{N}`$ に対し
```math
\lvert A\rvert+j_0 \le^{A+\!\!+T}_0 \lvert A\rvert+j_1 \iff j_0 \le^T_0 j_1 .
```

**証明**
$`(\Rightarrow)`$ [(D.le0)](Def.md#d-le0) より仮定は
$`\lvert A\rvert+j_0 < \lvert A\rvert+\lvert T\rvert`$、$`\lvert A\rvert+j_1 < \lvert A\rvert+\lvert T\rvert`$、
$`\mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,(\lvert A\rvert+j_0)\,(\lvert A\rvert+j_1)`$ の連言である。
前 2 者から $`j_0<\lvert T\rvert`$、$`j_1<\lvert T\rvert`$。
第 3 者に [(T.rtg_nextrel0_unlift)](#t-rtg_nextrel0_unlift) を適用して $`c'`$ を取ると、
$`\lvert A\rvert+j_1 = \lvert A\rvert+c'`$ すなわち $`j_1=c'`$ であり、
$`\mathrm{ReflTransGen}(\to^T_0)\,j_0\,c' = \mathrm{ReflTransGen}(\to^T_0)\,j_0\,j_1`$ を得る。
3 条件がそろうので $`j_0\le^T_0 j_1`$。

$`(\Leftarrow)`$ [(T.le0_append_right_of)](#t-le0_append_right_of) そのものである。∎

<a id="t-nextrel0_no_cross"></a>
### 定理 行 0 の辺は境界を越えない (T.nextrel0_no_cross)

**主張** $`A,T\in\mathrm{PairSeq}`$ が $`T_{0,0}=0`$ を満たすとする。
$`k<\lvert A\rvert`$、$`\lvert A\rvert \le j`$、$`0<(A\mathbin{+\!\!+}T)_{0,j}`$ のとき
$`k \to^{A+\!\!+T}_0 j`$ は成り立たない。

**証明** $`k \to^{A+\!\!+T}_0 j`$ を仮定して矛盾を導く。
[(D.nextrel0)](Def.md#d-nextrel0) の 5 条件を $`h_1,\dots,h_5`$ とする。
まず境界の値を計算する。[(T.entry_append_right)](#t-entry_append_right) の行番号 $`0`$、
ずらし幅 $`0`$ の場合を用いると
$`(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+0} = T_{0,0}`$ であり、$`\lvert A\rvert+0=\lvert A\rvert`$ と仮定 $`T_{0,0}=0`$ から
```math
(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert} = 0 . \tag{1}
```

次に $`\lvert A\rvert < j`$ を示す。$`\lvert A\rvert \ge j`$ と仮定すると、$`\lvert A\rvert \le j`$ と合わせて $`j=\lvert A\rvert`$ となり、
$`(1)`$ より $`(A\mathbin{+\!\!+}T)_{0,j}=0`$ であるが、これは仮定 $`0<(A\mathbin{+\!\!+}T)_{0,j}`$ に矛盾する。
よって $`\lvert A\rvert<j`$。

$`k<\lvert A\rvert`$ と $`\lvert A\rvert<j`$ より、添字 $`\lvert A\rvert`$ は $`h_5`$ の前提 $`k<\lvert A\rvert \wedge \lvert A\rvert<j`$ を満たす。
$`h_5`$ を適用して
```math
(A\mathbin{+\!\!+}T)_{0,j} \le (A\mathbin{+\!\!+}T)_{0,\lvert A\rvert} = 0
```
（最後の等号は $`(1)`$）。$`\mathbb{N}`$ において $`x\le 0`$ は $`x=0`$ を意味するから $`(A\mathbin{+\!\!+}T)_{0,j}=0`$ となり、
仮定 $`0<(A\mathbin{+\!\!+}T)_{0,j}`$ に矛盾する。∎

<a id="t-nextrel0_no_pred_zero"></a>
### 定理 行 0 の値 $`0`$ の列には行 0 の親がない (T.nextrel0_no_pred_zero)

**主張** $`M_{0,b}=0`$ ならば、いかなる $`a`$ についても $`a\to^M_0 b`$ は成り立たない。

**証明** $`a\to^M_0 b`$ を仮定する。[(D.nextrel0)](Def.md#d-nextrel0) の第 4 条件は
$`M_{0,a}<M_{0,b}`$ である。仮定 $`M_{0,b}=0`$ を代入すると $`M_{0,a}<0`$ となるが、
$`\mathbb{N}`$ には $`0`$ より小さい元がないから矛盾である。∎

<a id="t-rtg_to_root"></a>
### 定理 行 0 の値 $`0`$ の列へ到達する鎖は自明 (T.rtg_to_root)

**主張** $`M_{0,b}=0`$ かつ $`\mathrm{ReflTransGen}(\to^M_0)\,k\,b`$ ならば $`k=b`$。

**証明** 反射推移閉包の導出の構成子で場合分けする（帰納法ではなく最後の構成子のみを見る）。

- 反射 (refl)：$`k=b`$ であり、これが結論そのものである。
- 末尾追加 (tail)：ある $`x`$ について $`\mathrm{ReflTransGen}(\to^M_0)\,k\,x`$ と $`x\to^M_0 b`$ が
  成り立つ。しかし $`M_{0,b}=0`$ の下で
  [(T.nextrel0_no_pred_zero)](#t-nextrel0_no_pred_zero) より $`x\to^M_0 b`$ は成り立たない。
  よってこの場合は起こらない。∎

<a id="t-le0_no_cross"></a>
### 定理 行 0 祖先の鎖は境界を越えない (T.le0_no_cross)

**主張** $`A,T\in\mathrm{PairSeq}`$ が $`T_{0,0}=0`$ を満たすとする。
$`k<\lvert A\rvert`$ かつ $`0<(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}`$ のとき
$`k \le^{A+\!\!+T}_0 \lvert A\rvert+j_1`$ は成り立たない。

**証明** $`k\le^{A+\!\!+T}_0 \lvert A\rvert+j_1`$ を仮定すると、[(D.le0)](Def.md#d-le0) の第 3 条件から
```math
h : \mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,k\,(\lvert A\rvert+j_1)
```
が得られる。次の補助命題を示す。

```math
H :\equiv \forall e,\ \Bigl(\mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,k\,e \ \to\
   \lvert A\rvert\le e \ \to\ 0<(A\mathbin{+\!\!+}T)_{0,e} \ \to\ \lvert A\rvert\le k\Bigr).
```

$`H`$ を、$`k`$ を固定した反射推移閉包の導出に関する帰納法で示す。帰納法の述語は
```math
\Phi(e) :\equiv \bigl(\lvert A\rvert\le e \ \wedge\ 0<(A\mathbin{+\!\!+}T)_{0,e}\bigr) \to \lvert A\rvert\le k .
```

- 基底段 (refl)：$`e=k`$。前提として $`\lvert A\rvert\le e=k`$ が与えられるから、結論 $`\lvert A\rvert\le k`$ が直ちに従う。
- 帰納段 (tail)：$`\mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,k\,c`$ と $`c\to^{A+\!\!+T}_0 d`$ が与えられ、
  帰納法の仮定は $`\Phi(c)`$ である。$`\lvert A\rvert\le d`$ と $`0<(A\mathbin{+\!\!+}T)_{0,d}`$ を仮定して
  $`\lvert A\rvert\le k`$ を示す。

  まず $`\lvert A\rvert\le c`$ を示す。$`c<\lvert A\rvert`$ と仮定すると、
  [(T.nextrel0_no_cross)](#t-nextrel0_no_cross) を
  $`k:=c`$, $`j:=d`$（前提は $`c<\lvert A\rvert`$、$`\lvert A\rvert\le d`$、$`0<(A\mathbin{+\!\!+}T)_{0,d}`$、
  および辺 $`c\to^{A+\!\!+T}_0 d`$）に適用して矛盾を得る。よって $`\lvert A\rvert\le c`$。

  次に $`(A\mathbin{+\!\!+}T)_{0,c}`$ が正か否かで場合分けする。
  - $`0<(A\mathbin{+\!\!+}T)_{0,c}`$ のとき：帰納法の仮定 $`\Phi(c)`$ に $`\lvert A\rvert\le c`$ と
    この正値性を与えて $`\lvert A\rvert\le k`$ を得る。
  - $`\neg\bigl(0<(A\mathbin{+\!\!+}T)_{0,c}\bigr)`$ のとき：$`\mathbb{N}`$ ではこれは
    $`(A\mathbin{+\!\!+}T)_{0,c}=0`$ を意味する。
    [(T.rtg_to_root)](#t-rtg_to_root) を鎖 $`\mathrm{ReflTransGen}(\to^{A+\!\!+T}_0)\,k\,c`$ に
    適用して $`k=c`$ を得る。$`\lvert A\rvert\le c=k`$ である。

  いずれの場合も $`\lvert A\rvert\le k`$ であり、$`\Phi(d)`$ が示された。

$`H`$ を $`e:=\lvert A\rvert+j_1`$、鎖 $`h`$、$`\lvert A\rvert\le\lvert A\rvert+j_1`$、
仮定 $`0<(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}`$ に適用すると $`\lvert A\rvert\le k`$ を得るが、
これは仮定 $`k<\lvert A\rvert`$ に矛盾する。∎

<a id="t-nextrel1_append_right"></a>
### 定理 行 1 直接親子関係の接尾辞不変性 (T.nextrel1_append_right)

**主張** $`A,T\in\mathrm{PairSeq}`$、$`j_0,j_1\in\mathbb{N}`$ に対し
```math
\lvert A\rvert+j_0 \to^{A+\!\!+T}_1 \lvert A\rvert+j_1 \iff j_0 \to^T_1 j_1 .
```

**証明** [(D.nextrel1)](Def.md#d-nextrel1) の 6 条件を両側で比較する。
$`\lvert A\mathbin{+\!\!+}T\rvert = \lvert A\rvert+\lvert T\rvert`$ を用いる。

$`(\Rightarrow)`$ 左辺の 6 条件を $`h_1,\dots,h_6`$ とする。

1. $`h_1 : \lvert A\rvert+j_0 < \lvert A\rvert+\lvert T\rvert`$ の両辺から $`\lvert A\rvert`$ を消去して $`j_0<\lvert T\rvert`$。
2. $`h_2 : \lvert A\rvert+j_1 < \lvert A\rvert+\lvert T\rvert`$ の両辺から $`\lvert A\rvert`$ を消去して $`j_1<\lvert T\rvert`$。
3. $`h_3 : \lvert A\rvert+j_0 < \lvert A\rvert+j_1`$ から $`j_0<j_1`$。
4. $`h_4 : (A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_0} < (A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_1}`$ を
   [(T.entry_append_right)](#t-entry_append_right) で書き換えて $`T_{1,j_0}<T_{1,j_1}`$。
5. $`h_5 : \lvert A\rvert+j_0 \le^{A+\!\!+T}_0 \lvert A\rvert+j_1`$ に
   [(T.le0_append_right)](#t-le0_append_right) の $`(\Rightarrow)`$ を適用して $`j_0\le^T_0 j_1`$。
6. $`j`$ を $`j_0<j`$ かつ $`j\le^T_0 j_1`$ なる任意の自然数とする。
   $`\lvert A\rvert+j_0<\lvert A\rvert+j`$ であり、[(T.le0_append_right)](#t-le0_append_right) の
   $`(\Leftarrow)`$ より $`\lvert A\rvert+j \le^{A+\!\!+T}_0 \lvert A\rvert+j_1`$ であるから、
   $`h_6`$ を添字 $`\lvert A\rvert+j`$ に適用して
   $`(A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_1} \le (A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j}`$、
   [(T.entry_append_right)](#t-entry_append_right) で書き換えて $`T_{1,j_1}\le T_{1,j}`$。

$`(\Leftarrow)`$ 右辺の 6 条件を $`h_1,\dots,h_6`$ とする。

1. $`j_0<\lvert T\rvert`$ の両辺に $`\lvert A\rvert`$ を加えて $`\lvert A\rvert+j_0<\lvert A\rvert+\lvert T\rvert=\lvert A\mathbin{+\!\!+}T\rvert`$。
2. $`j_1<\lvert T\rvert`$ の両辺に $`\lvert A\rvert`$ を加えて $`\lvert A\rvert+j_1<\lvert A\rvert+\lvert T\rvert=\lvert A\mathbin{+\!\!+}T\rvert`$。
3. $`j_0<j_1`$ から $`\lvert A\rvert+j_0<\lvert A\rvert+j_1`$。
4. $`T_{1,j_0}<T_{1,j_1}`$ を [(T.entry_append_right)](#t-entry_append_right) で
   $`(A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_0} < (A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_1}`$ に書き換える。
5. $`j_0\le^T_0 j_1`$ に [(T.le0_append_right)](#t-le0_append_right) の $`(\Leftarrow)`$ を適用する。
6. $`j`$ を $`\lvert A\rvert+j_0<j`$ かつ $`j\le^{A+\!\!+T}_0 \lvert A\rvert+j_1`$ なる任意の自然数とする。
   $`j>\lvert A\rvert+j_0\ge\lvert A\rvert`$ であるから $`j'=j-\lvert A\rvert`$ とおいて $`j=\lvert A\rvert+j'`$ と書ける。
   [(T.le0_append_right)](#t-le0_append_right) の $`(\Rightarrow)`$ より $`j'\le^T_0 j_1`$、
   また $`\lvert A\rvert+j_0<\lvert A\rvert+j'`$ から $`j_0<j'`$。
   $`h_6`$ を $`j'`$ に適用して $`T_{1,j_1}\le T_{1,j'}`$、
   [(T.entry_append_right)](#t-entry_append_right) で書き換えて
   $`(A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_1} \le (A\mathbin{+\!\!+}T)_{1,j}`$。∎

<a id="t-nextR_append_right"></a>
### 定理 行付き直接親子関係の接尾辞不変性 (T.nextR_append_right)

**主張** $`A,T\in\mathrm{PairSeq}`$、$`i,j_0,j_1\in\mathbb{N}`$ に対し
```math
\lvert A\rvert+j_0 \to^{A+\!\!+T}_i \lvert A\rvert+j_1 \iff j_0 \to^T_i j_1 .
```

**証明** [(D.nextR)](Def.md#d-nextR) の場合分けは $`i=0`$ か否かである。

- $`i=0`$ のとき：両辺はそれぞれ
  $`\lvert A\rvert+j_0 \to^{A+\!\!+T}_0 \lvert A\rvert+j_1`$ と $`j_0\to^T_0 j_1`$ に等しく、
  同値性は [(T.nextrel0_append_right)](#t-nextrel0_append_right) である。
- $`i\ne0`$ のとき：両辺はそれぞれ
  $`\lvert A\rvert+j_0 \to^{A+\!\!+T}_1 \lvert A\rvert+j_1`$ と $`j_0\to^T_1 j_1`$ に等しく、
  同値性は [(T.nextrel1_append_right)](#t-nextrel1_append_right) である。∎

<a id="t-idx1_append_right"></a>
### 定理 $`\mathrm{idx}_1`$ の接尾辞不変性 (T.idx1_append_right)

**主張** $`\mathrm{idx}_1(A\mathbin{+\!\!+}T,\ \lvert A\rvert+j) = \mathrm{idx}_1(T,j)`$。

**証明** [(D.idx1)](Def.md#d-idx1) より
$`\mathrm{idx}_1(M,j)`$ は $`0<M_{1,j}`$ ならば $`1`$、さもなくば $`0`$ である。
[(T.entry_append_right)](#t-entry_append_right) より
$`(A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j} = T_{1,j}`$ であるから、条件 $`0<(A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j}`$ と
条件 $`0<T_{1,j}`$ は同一の命題であり、両辺の値は一致する。∎

<a id="t-nextR_le0"></a>
### 定理 行付きの辺は行 0 の祖先関係を与える (T.nextR_le0)

**主張** $`k \to^M_i b`$ ならば $`k \le^M_0 b`$。

**証明** [(D.nextR)](Def.md#d-nextR) の場合分けによる。

- $`i=0`$ のとき：仮定は $`k\to^M_0 b`$ である。[(D.nextrel0)](Def.md#d-nextrel0) の第 1・第 2 条件から
  $`k<\lvert M\rvert`$ と $`b<\lvert M\rvert`$、また 1 歩の辺から
  $`\mathrm{ReflTransGen}(\to^M_0)\,k\,b`$（長さ 1 の鎖）が得られる。
  3 条件がそろうので [(D.le0)](Def.md#d-le0) より $`k\le^M_0 b`$。
- $`i\ne0`$ のとき：仮定は $`k\to^M_1 b`$ である。[(D.nextrel1)](Def.md#d-nextrel1) の第 5 条件が
  まさに $`k\le^M_0 b`$ である。∎

<a id="t-nextR_src_in_T"></a>
### 定理 親の位置は $`T`$ の側にある (T.nextR_src_in_T)

**主張** $`A,T\in\mathrm{PairSeq}`$ が $`T_{0,0}=0`$ を満たすとする。
$`0<(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}`$ かつ $`k \to^{A+\!\!+T}_i \lvert A\rvert+j_1`$ ならば
$`\lvert A\rvert \le k`$。

**証明** $`\lvert A\rvert\le k`$ を否定して $`k<\lvert A\rvert`$ と仮定する。
[(T.nextR_le0)](#t-nextR_le0) より $`k \le^{A+\!\!+T}_0 \lvert A\rvert+j_1`$ が成り立つ。
これは [(T.le0_no_cross)](#t-le0_no_cross)（前提 $`T_{0,0}=0`$、$`k<\lvert A\rvert`$、
$`0<(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}`$）に矛盾する。∎

<a id="t-hasParent_append_right"></a>
### 定理 親の一意存在の接尾辞不変性 (T.hasParent_append_right)

**主張** $`A,T\in\mathrm{PairSeq}`$ が $`T_{0,0}=0`$ を満たし、
$`0<(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}`$ とする。このとき
```math
\mathrm{hasParent}(A\mathbin{+\!\!+}T,\ i,\ \lvert A\rvert+j_1) \iff \mathrm{hasParent}(T,i,j_1).
```

**証明** [(D.hasParent)](Def.md#d-hasParent) より、両辺はそれぞれ
$`\exists! j_0,\ j_0\to^{A+\!\!+T}_i \lvert A\rvert+j_1`$ と $`\exists! j_0,\ j_0\to^T_i j_1`$ である。

$`(\Rightarrow)`$ $`j_0`$ を、$`j_0\to^{A+\!\!+T}_i \lvert A\rvert+j_1`$ を満たし、かつ
「$`y\to^{A+\!\!+T}_i \lvert A\rvert+j_1`$ なる任意の $`y`$ について $`y=j_0`$」を満たすものとする。
[(T.nextR_src_in_T)](#t-nextR_src_in_T) より $`\lvert A\rvert\le j_0`$ であるから、
$`j_0' := j_0-\lvert A\rvert`$ とおいて $`j_0=\lvert A\rvert+j_0'`$ と書ける。
[(T.nextR_append_right)](#t-nextR_append_right) の $`(\Rightarrow)`$ より $`j_0'\to^T_i j_1`$。
一意性を示す。$`y\to^T_i j_1`$ とすると、[(T.nextR_append_right)](#t-nextR_append_right) の
$`(\Leftarrow)`$ より $`\lvert A\rvert+y \to^{A+\!\!+T}_i \lvert A\rvert+j_1`$ であるから、
左辺の一意性により $`\lvert A\rvert+y = \lvert A\rvert+j_0'`$、両辺から $`\lvert A\rvert`$ を消去して $`y=j_0'`$。

$`(\Leftarrow)`$ $`j_0'`$ を、$`j_0'\to^T_i j_1`$ を満たし、かつ
「$`y\to^T_i j_1`$ なる任意の $`y`$ について $`y=j_0'`$」を満たすものとする。
[(T.nextR_append_right)](#t-nextR_append_right) の $`(\Leftarrow)`$ より
$`\lvert A\rvert+j_0' \to^{A+\!\!+T}_i \lvert A\rvert+j_1`$。
一意性を示す。$`y\to^{A+\!\!+T}_i \lvert A\rvert+j_1`$ とすると、
[(T.nextR_src_in_T)](#t-nextR_src_in_T) より $`\lvert A\rvert\le y`$ であるから
$`y' := y-\lvert A\rvert`$ とおいて $`y=\lvert A\rvert+y'`$ と書ける。
[(T.nextR_append_right)](#t-nextR_append_right) の $`(\Rightarrow)`$ より $`y'\to^T_i j_1`$、
右辺の一意性により $`y'=j_0'`$、よって $`y=\lvert A\rvert+j_0'`$。∎

<a id="t-parent_append_right"></a>
### 定理 親の位置のずれ (T.parent_append_right)

**主張** $`A,T\in\mathrm{PairSeq}`$ が $`T_{0,0}=0`$ を満たし、
$`0<(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}`$ かつ $`\mathrm{hasParent}(T,i,j_1)`$ とする。このとき
```math
\mathrm{par}^{A+\!\!+T}_i(\lvert A\rvert+j_1) = \lvert A\rvert + \mathrm{par}^T_i(j_1).
```

**証明** [(T.hasParent_append_right)](#t-hasParent_append_right) の $`(\Leftarrow)`$ より
$`\mathrm{hasParent}(A\mathbin{+\!\!+}T,\ i,\ \lvert A\rvert+j_1)`$ が成り立つ。以下これを $`h_M`$ とおく。
$`h_M`$ は一意性の条項をもつから、$`\lvert A\rvert+j_1`$ の行 $`i`$ における親を与える添字は
たかだか 1 つである。そこで次の 2 つがともにその条件を満たすことを示せばよい。

1. $`\mathrm{par}^{A+\!\!+T}_i(\lvert A\rvert+j_1) \to^{A+\!\!+T}_i \lvert A\rvert+j_1`$。
   これは [(T.parent_nextR)](Mechanized.md#t-parent_nextR) を $`h_M`$ に適用したものである。
2. $`\lvert A\rvert + \mathrm{par}^T_i(j_1) \to^{A+\!\!+T}_i \lvert A\rvert+j_1`$。
   仮定 $`\mathrm{hasParent}(T,i,j_1)`$ に [(T.parent_nextR)](Mechanized.md#t-parent_nextR) を適用して
   $`\mathrm{par}^T_i(j_1)\to^T_i j_1`$ を得、[(T.nextR_append_right)](#t-nextR_append_right) の
   $`(\Leftarrow)`$ で $`A\mathbin{+\!\!+}T`$ 側へ移す。

$`h_M`$ の一意性により両者は等しい。∎

<a id="t-take_append_right"></a>
### 定理 連結に対する $`\mathrm{take}`$ の分解 (T.take_append_right)

**主張** $`\mathrm{take}\,(\lvert A\rvert+j)\,(A\mathbin{+\!\!+}T) = A \mathbin{+\!\!+} \mathrm{take}\,j\,T`$。

**証明** 連結に対する $`\mathrm{take}`$ の一般則
```math
\mathrm{take}\,m\,(A\mathbin{+\!\!+}T) = \mathrm{take}\,m\,A \mathbin{+\!\!+} \mathrm{take}\,(m-\lvert A\rvert)\,T
```
（前半 $`m`$ 個のうち $`A`$ から取れるのは先頭 $`\min(m,\lvert A\rvert)`$ 個、残りは $`T`$ の先頭 $`m-\lvert A\rvert`$ 個）を
$`m := \lvert A\rvert+j`$ に適用する。$`\lvert A\rvert \le \lvert A\rvert+j`$ であるから
$`\mathrm{take}\,(\lvert A\rvert+j)\,A = A`$ であり、また $`(\lvert A\rvert+j)-\lvert A\rvert = j`$ である。
よって右辺は $`A \mathbin{+\!\!+} \mathrm{take}\,j\,T`$ となる。∎

<a id="t-copyblock_append"></a>
### 定理 コピーブロックの接尾辞不変性 (T.copyblock_append)

**主張** $`A,T\in\mathrm{PairSeq}`$、$`a,m,k,d_0,d_1\in\mathbb{N}`$ に対し
```math
\mathrm{map}\,\bigl(\lambda j.\ ((A\mathbin{+\!\!+}T)_{0,j}+k\,d_0,\ (A\mathbin{+\!\!+}T)_{1,j}+k\,d_1)\bigr)\,
   \mathrm{range}'(\lvert A\rvert+a,\ m)
 = \mathrm{map}\,\bigl(\lambda j.\ (T_{0,j}+k\,d_0,\ T_{1,j}+k\,d_1)\bigr)\,\mathrm{range}'(a,m).
```

**証明** まず添字列について
```math
\mathrm{range}'(\lvert A\rvert+a,\ m) = \mathrm{map}\,(\lambda x.\ \lvert A\rvert+x)\,\mathrm{range}'(a,m)
 \tag{2}
```
を示す。$`\mathrm{range}'(s,m) = \mathrm{map}\,(\lambda x.\ s+x)\,\mathrm{range}(m)`$ であるから、
$`(2)`$ の左辺は $`\mathrm{map}\,(\lambda x.\ (\lvert A\rvert+a)+x)\,\mathrm{range}(m)`$、
右辺は $`\mathrm{map}\,(\lambda x.\ \lvert A\rvert+(a+x))\,\mathrm{range}(m)`$ である
（$`\mathrm{map}`$ の合成則 $`\mathrm{map}\,f\,(\mathrm{map}\,g\,L) = \mathrm{map}\,(f\circ g)\,L`$ による）。
加法の結合律 $`(\lvert A\rvert+a)+x = \lvert A\rvert+(a+x)`$ により 2 つの写像は各点で等しく、$`(2)`$ が従う。

$`(2)`$ と $`\mathrm{map}`$ の合成則より、主張の左辺は
```math
\mathrm{map}\,\bigl(\lambda j.\ ((A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j}+k\,d_0,\
  (A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j}+k\,d_1)\bigr)\,\mathrm{range}'(a,m)
```
に等しい。[(T.entry_append_right)](#t-entry_append_right) より各 $`j`$ について
$`(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j} = T_{0,j}`$ かつ $`(A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j} = T_{1,j}`$
であるから、写される関数は右辺のものと各点で等しい。よって両辺は等しい。∎

<a id="t-Pred_append_right"></a>
### 定理 $`\mathrm{Pred}`$ の分解 (T.Pred_append_right)

**主張** $`2\le\lvert T\rvert`$ ならば $`\mathrm{Pred}(A\mathbin{+\!\!+}T) = A \mathbin{+\!\!+} \mathrm{Pred}\,T`$。

**証明** [(D.Pred)](Def.md#d-Pred) は $`\lvert M\rvert\le1`$ ならば $`M`$、さもなくば $`\mathrm{dropLast}\,M`$ である。
$`\lvert A\mathbin{+\!\!+}T\rvert = \lvert A\rvert+\lvert T\rvert \ge \lvert T\rvert \ge 2`$ であるから
$`\neg(\lvert A\mathbin{+\!\!+}T\rvert\le1)`$、また仮定より $`\neg(\lvert T\rvert\le1)`$。
よって両辺はそれぞれ $`\mathrm{dropLast}(A\mathbin{+\!\!+}T)`$ と $`A\mathbin{+\!\!+}\mathrm{dropLast}\,T`$ である。
$`\lvert T\rvert\ge2>0`$ より $`T\ne()`$ であり、$`T\ne()`$ のとき連結の末尾要素は $`T`$ の末尾要素であるから
```math
\mathrm{dropLast}(A\mathbin{+\!\!+}T) = A \mathbin{+\!\!+} \mathrm{dropLast}\,T
```
が成り立つ。∎

<a id="t-no_hasParent_of_row0_zero"></a>
### 定理 行 0 の値 $`0`$ の列には親がない (T.no_hasParent_of_row0_zero)

**主張** $`M_{0,j_1}=0`$ ならば、いかなる $`i`$ についても $`\mathrm{hasParent}(M,i,j_1)`$ は成り立たない。

**証明** $`\mathrm{hasParent}(M,i,j_1)`$ を仮定する。[(D.hasParent)](Def.md#d-hasParent) より
ある $`j_0`$ について $`j_0 \to^M_i j_1`$ が成り立つ。
[(T.nextR_le0)](#t-nextR_le0) より $`j_0\le^M_0 j_1`$、その第 3 条件から
$`\mathrm{ReflTransGen}(\to^M_0)\,j_0\,j_1`$ が得られる。
仮定 $`M_{0,j_1}=0`$ の下で [(T.rtg_to_root)](#t-rtg_to_root) を適用すると $`j_0=j_1`$。
一方 [(T.nextR_index_lt)](Mechanized.md#t-nextR_index_lt) より $`j_0<j_1`$ であり、
$`j_0=j_1`$ と $`j_0<j_1`$ は両立しない。矛盾である。∎

<a id="t-oper_append_right"></a>
### 定理 展開の接頭辞可換性 (T.oper_append_right)

**主張** $`A,T\in\mathrm{PairSeq}`$、$`n\in\mathbb{N}`$ とし、$`2\le\lvert T\rvert`$ かつ $`T_{0,0}=0`$ とする。このとき
```math
(A\mathbin{+\!\!+}T)[n] = A \mathbin{+\!\!+} T[n].
```

**証明** $`j_1 := \lvert T\rvert-1`$ とおく。$`2\le\lvert T\rvert`$ より $`j_1\ge1`$、特に $`j_1\ne0`$ である。また
```math
\lvert A\mathbin{+\!\!+}T\rvert - 1 = (\lvert A\rvert+\lvert T\rvert)-1 = \lvert A\rvert + (\lvert T\rvert-1)
  = \lvert A\rvert+j_1 \tag{3}
```
（$`\lvert T\rvert\ge2\ge1`$ であるから切り捨て減法の繰り上がりは起こらない）。
すなわち $`A\mathbin{+\!\!+}T`$ の末尾添字は $`\lvert A\rvert+j_1`$ である。
[(D.oper)](Def.md#d-oper) の分岐を両辺で順に照合する。

**分岐 (a) の判定.** $`A\mathbin{+\!\!+}T`$ 側の条件は $`\lvert A\rvert+j_1=0`$、$`T`$ 側の条件は $`j_1=0`$ である。
$`j_1\ge1`$ よりどちらも偽であるから、両辺とも分岐 (a) には入らない。

**末尾の成分.** [(T.entry_append_right)](#t-entry_append_right) より
```math
(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1} = T_{0,j_1},\qquad
  (A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_1} = T_{1,j_1}. \tag{4}
```

**分岐 (b) の判定.** $`A\mathbin{+\!\!+}T`$ 側の条件
$`(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}=0 \wedge (A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_1}=0`$ は、
$`(4)`$ により $`T`$ 側の条件 $`T_{0,j_1}=0 \wedge T_{1,j_1}=0`$ と同一の命題である。

- この条件が成り立つとき：両辺はそれぞれ $`\mathrm{Pred}(A\mathbin{+\!\!+}T)`$ と $`A\mathbin{+\!\!+}\mathrm{Pred}\,T`$ であり、
  仮定 $`2\le\lvert T\rvert`$ の下で [(T.Pred_append_right)](#t-Pred_append_right) により等しい。
- 成り立たないとき：以下へ進む。

**行番号.** [(T.idx1_append_right)](#t-idx1_append_right) より
$`\mathrm{idx}_1(A\mathbin{+\!\!+}T,\ \lvert A\rvert+j_1) = \mathrm{idx}_1(T,j_1)`$。これを $`i_1`$ と書く。

**分岐 (c)/(d) の判定.** $`\mathrm{hasParent}(T,i_1,j_1)`$ の真偽で場合分けする。

**(i) $`\mathrm{hasParent}(T,i_1,j_1)`$ が成り立つ場合.**
まず $`0<T_{0,j_1}`$ を示す。$`T_{0,j_1}=0`$ と仮定すると
[(T.no_hasParent_of_row0_zero)](#t-no_hasParent_of_row0_zero)（$`M:=T`$）により
$`\mathrm{hasParent}(T,i_1,j_1)`$ が成り立たず、仮定に矛盾する。よって $`0<T_{0,j_1}`$、
$`(4)`$ により
```math
0 < (A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}. \tag{5}
```
$`(5)`$ と $`T_{0,0}=0`$ の下で [(T.hasParent_append_right)](#t-hasParent_append_right) の $`(\Leftarrow)`$ より
$`\mathrm{hasParent}(A\mathbin{+\!\!+}T,\ i_1,\ \lvert A\rvert+j_1)`$ が成り立つ。
したがって両辺とも分岐 (c) には入らず、分岐 (d) に入る。

$`j_0 := \mathrm{par}^T_{i_1}(j_1)`$ とおく。$`(5)`$ と [(T.parent_append_right)](#t-parent_append_right) より
```math
\mathrm{par}^{A+\!\!+T}_{i_1}(\lvert A\rvert+j_1) = \lvert A\rvert+j_0 . \tag{6}
```

分岐 (d) の 4 つの構成要素を照合する。

1. **増分 $`d_0`$.** $`A\mathbin{+\!\!+}T`$ 側の $`d_0`$ は、$`0<i_1`$ のとき
   $`(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1} - (A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_0}`$、
   $`i_1=0`$ のとき $`0`$ である（$`(6)`$ により親の添字は $`\lvert A\rvert+j_0`$）。
   $`(4)`$ と [(T.entry_append_right)](#t-entry_append_right) より
   $`(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_0} = T_{0,j_0}`$ であるから、この値は
   $`0<i_1`$ のとき $`T_{0,j_1}-T_{0,j_0}`$、$`i_1=0`$ のとき $`0`$ であり、$`T`$ 側の $`d_0`$ と一致する。
2. **増分 $`d_1`$.** $`A\mathbin{+\!\!+}T`$ 側の $`d_1`$ は、$`1<i_1`$ のとき
   $`(A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_1} - (A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_0}`$、
   $`i_1\le1`$ のとき $`0`$ である。$`(4)`$ と [(T.entry_append_right)](#t-entry_append_right) より
   $`(A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_1} = T_{1,j_1}`$、
   $`(A\mathbin{+\!\!+}T)_{1,\lvert A\rvert+j_0} = T_{1,j_0}`$ であるから、この値は
   $`1<i_1`$ のとき $`T_{1,j_1}-T_{1,j_0}`$、$`i_1\le1`$ のとき $`0`$ であり、$`T`$ 側の $`d_1`$ と一致する。
3. **接頭部.** [(T.take_append_right)](#t-take_append_right) より
   $`\mathrm{take}\,(\lvert A\rvert+j_0)\,(A\mathbin{+\!\!+}T) = A\mathbin{+\!\!+}\mathrm{take}\,j_0\,T`$。
4. **コピーブロック.** 項目 1, 2 により両側の増分は同じ値であるから、以下ではその共通の値を
   $`d_0`$, $`d_1`$ と書く。添字区間の長さは
   $`(\lvert A\rvert+j_1)-(\lvert A\rvert+j_0) = j_1-j_0`$ である。各 $`k\in\mathrm{range}(n)`$ について
   [(T.copyblock_append)](#t-copyblock_append) を $`a:=j_0`$, $`m:=j_1-j_0`$ に適用すると
   ```math
   \mathrm{map}\,\bigl(\lambda j.\ ((A\mathbin{+\!\!+}T)_{0,j}+k\,d_0,\ (A\mathbin{+\!\!+}T)_{1,j}+k\,d_1)\bigr)\,
     \mathrm{range}'(\lvert A\rvert+j_0,\ j_1-j_0)
   ```
   ```math
   = \mathrm{map}\,\bigl(\lambda j.\ (T_{0,j}+k\,d_0,\ T_{1,j}+k\,d_1)\bigr)\,\mathrm{range}'(j_0,\ j_1-j_0)
   ```
   である。$`\mathrm{flatMap}`$ は各 $`k`$ の像を連結するだけであるから、
   $`\mathrm{range}(n)`$ 上の $`\mathrm{flatMap}`$ どうしも等しい。

以上より、$`X := \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda j.\ (T_{0,j}+k\,d_0,\ T_{1,j}+k\,d_1))\, \mathrm{range}'(j_0,j_1-j_0)\bigr)\,\mathrm{range}(n)`$ とおくと
```math
(A\mathbin{+\!\!+}T)[n] = \bigl(A\mathbin{+\!\!+}\mathrm{take}\,j_0\,T\bigr)\mathbin{+\!\!+}X
 = A\mathbin{+\!\!+}\bigl(\mathrm{take}\,j_0\,T\mathbin{+\!\!+}X\bigr) = A\mathbin{+\!\!+}T[n]
```
（第 2 の等号は連結の結合律）。

**(ii) $`\mathrm{hasParent}(T,i_1,j_1)`$ が成り立たない場合.**
$`\mathrm{hasParent}(A\mathbin{+\!\!+}T,\ i_1,\ \lvert A\rvert+j_1)`$ も成り立たないことを示す。
これが成り立つと仮定し、$`(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}`$ が正か否かで場合分けする。

- $`0<(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}`$ のとき：
  [(T.hasParent_append_right)](#t-hasParent_append_right) の $`(\Rightarrow)`$ より
  $`\mathrm{hasParent}(T,i_1,j_1)`$ となり、この場合の仮定に矛盾する。
- $`\neg\bigl(0<(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}\bigr)`$ のとき：
  $`\mathbb{N}`$ ではこれは $`(A\mathbin{+\!\!+}T)_{0,\lvert A\rvert+j_1}=0`$ を意味する。
  [(T.no_hasParent_of_row0_zero)](#t-no_hasParent_of_row0_zero)（$`M := A\mathbin{+\!\!+}T`$）より
  $`\mathrm{hasParent}(A\mathbin{+\!\!+}T,\ i_1,\ \lvert A\rvert+j_1)`$ は成り立たず、矛盾する。

よって両辺とも分岐 (c) に入り、それぞれ $`\mathrm{Pred}(A\mathbin{+\!\!+}T)`$ と $`A\mathbin{+\!\!+}\mathrm{Pred}\,T`$ である。
[(T.Pred_append_right)](#t-Pred_append_right) によりこれらは等しい。∎

---

## `oper_tail_cases` のための補助

<a id="t-map_range_entry_eq_take"></a>
### 定理 成分列は接頭部に等しい (T.map_range_entry_eq_take)

**主張** $`N\in\mathrm{PairSeq}`$、$`j_1\le\lvert N\rvert`$ のとき
```math
\mathrm{map}\,\bigl(\lambda j.\ (N_{0,j},\ N_{1,j})\bigr)\,\mathrm{range}(j_1) = \mathrm{take}\,j_1\,N .
```

**証明** 2 つの列が等しいことを、長さの一致と各位置の要素の一致で示す。

**長さ.** 左辺の長さは $`\lvert\mathrm{range}(j_1)\rvert = j_1`$。
右辺の長さは $`\min(j_1,\lvert N\rvert)`$ であり、仮定 $`j_1\le\lvert N\rvert`$ より $`j_1`$ である。

**各位置.** $`i<j_1`$ とする。$`\mathrm{range}(j_1)`$ の第 $`i`$ 要素は $`i`$ であるから、左辺の第 $`i`$ 要素は
$`(N_{0,i},\ N_{1,i})`$ である。また $`i<j_1\le\lvert N\rvert`$ より $`i<\lvert N\rvert`$ であるから
$`N\langle i\rangle`$ は $`N`$ の第 $`i`$ 要素そのものであり、
[(D.entry)](Def.md#d-entry) より
```math
N_{0,i} = \pi_0(N\langle i\rangle),\qquad N_{1,i} = \pi_1(N\langle i\rangle)
```
である。対 $`p`$ について $`(\pi_0 p,\ \pi_1 p) = p`$ であるから、左辺の第 $`i`$ 要素は $`N`$ の第 $`i`$ 要素に等しい。
一方 $`\mathrm{take}\,j_1\,N`$ の第 $`i`$ 要素（$`i<j_1`$）も $`N`$ の第 $`i`$ 要素である。よって一致する。

長さと全位置の要素が一致するから両辺は等しい。∎

<a id="t-oper_headD"></a>
### 定理 展開は先頭を保つ (T.oper_headD)

**主張** $`N\in\mathrm{PairSeq}`$、$`1<\lvert N\rvert`$、$`1\le n`$ のとき、$`N[n]`$ の先頭要素と $`N`$ の先頭要素は
等しい（いずれも既定値 $`(0,0)`$ の下で読む）。

**証明** [(T.oper_eq_dropLast_append)](Wf.md#t-oper_eq_dropLast_append) より、ある $`R`$ が存在して
```math
N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R .
```
$`1<\lvert N\rvert`$ すなわち $`\lvert N\rvert\ge2`$ であるから $`N`$ は $`N = p\mathbin{::}q\mathbin{::}u`$ の形に書ける。
要素 2 個以上の列に対する $`\mathrm{dropLast}`$ の計算則
$`\mathrm{dropLast}(p\mathbin{::}q\mathbin{::}u) = p\mathbin{::}\mathrm{dropLast}(q\mathbin{::}u)`$ と、
先頭付加と連結の関係 $`(p\mathbin{::}L)\mathbin{+\!\!+}R = p\mathbin{::}(L\mathbin{+\!\!+}R)`$ より
```math
N[n] = p \mathbin{::} \bigl(\mathrm{dropLast}(q\mathbin{::}u)\mathbin{+\!\!+}R\bigr).
```
先頭付加された列の先頭要素は付加された要素であるから、$`N[n]`$ の先頭要素は $`p`$ であり、
$`N = p\mathbin{::}q\mathbin{::}u`$ の先頭要素も $`p`$ である。∎

---

## 末尾の注記節（宣言なし）

Lean 側のソースの末尾には、さらに 3 つの注記ブロック
（`ST_PS`-descendant-closure に関する注、
`## Well-foundedness of <o on NF, and PSS termination`、
`## Step decrease: the weaker (live) obligation`）が置かれている。
いずれもコメントのみであり、宣言（定義・定理）を含まない。したがって本文で扱う命題はない。
