[← 目次](README.md)

# Seqlex — 列辞書式順序と翻訳による順序同型

ペア列そのものの上の**列辞書式順序** $`\prec_{\mathrm{lex}}`$（先頭の対から順に、行 0 を優先し次に行 1 を比べる辞書式順序）を定義する。
行 0 の値が先頭でちょうど深さ $`d`$ に等しく、以降つねに $`d`$ 以上で、かつ隣接する 2 対の間で高々 1 しか増えない列
（ブロック条件 $`\mathrm{blockok}(d,\cdot)`$）に制限すると、翻訳 $`\mathrm{tr}`$（[(D.translate)](Mechanized.md#d-translate)）は
$`\prec_{\mathrm{lex}}`$ を [(D.olt)](Mechanized.md#d-olt) の $`\prec`$ へ写す順序同型になる。
最後に標準形 [(D.ST_PS)](Def.md#d-ST_PS) の元がすべて $`\mathrm{blockok}(0,\cdot)`$ をみたすことを示し、
結論 [(T.olt_ST_iff_seqlex)](#t-olt_ST_iff_seqlex)：$`M,N\in\mathrm{ST\_PS}`$ かつ $`M\ne N`$ ならば
$`\mathrm{tr}\,M\prec\mathrm{tr}\,N \iff M\prec_{\mathrm{lex}}N`$ を得る。

## 記法

この章で導入する Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `pairlt p q` | $`p \lt _{\mathrm p} q`$ | 対の辞書式順序（行 0 優先） |
| `seqlex M N` | $`M \prec_{\mathrm{lex}} N`$ | 列辞書式順序 |
| `steps1 B` | $`\mathrm{steps}_1(B)`$ | 行 0 が隣接段で高々 1 しか増えない |
| `blockok d B` | $`\mathrm{blockok}(d,B)`$ | $`B`$ は深さ $`d`$ のブロックである |

他章で定義済みの記号については次のように書く（[`Def.md`](Def.md), [`Mechanized.md`](Mechanized.md), [`Wf.md`](Wf.md)）。

| Lean | 本文 | 意味 |
|---|---|---|
| `M.length` | $`\lvert M\rvert`$ | 長さ |
| `p.1`, `p.2` | $`\pi_0 p`$, $`\pi_1 p`$ | 対 $`p`$ の第 0・第 1 成分 |
| `l.getD i d` | $`\mathrm{getD}(l,i,d)`$ | 第 $`i`$ 要素（範囲外なら $`d`$） |
| `M.getD j (0,0)` | $`M\langle j\rangle`$ | $`\mathrm{getD}(M,j,(0,0))`$ の略記 |
| `l.getLastD d` | $`\mathrm{lastD}(l,d)`$ | 末尾要素（空列なら $`d`$） |
| `l.headI` | $`\mathrm{headI}\,l`$ | 先頭要素（空列なら既定値） |
| `entry M i j` | $`M_{i,j}`$ | 第 $`j`$ 対の第 $`i`$ 成分 |
| `translate M` | $`\mathrm{tr}\,M`$ | ペア列の翻訳 |
| `x <o y` | $`x\prec y`$ | 添字優先辞書式順序 |
| `M⟦n⟧` | $`M[n]`$ | 展開（コピー数 $`n`$） |
| `xs ++ ys` | $`xs\mathbin{+\!\!+}ys`$ | 連結 |
| `x :: xs` | $`x\mathbin{::}xs`$ | 先頭付加 |
| `L.take j` | $`\mathrm{take}\,j\,L`$ | 前 $`j`$ 個 |
| `L.dropLast` | $`\mathrm{dropLast}\,L`$ | 末尾 1 個を除いた列 |
| `L.map f` | $`\mathrm{map}\,f\,L`$ | 各要素に $`f`$ を適用 |
| `L.flatMap f` | $`\mathrm{flatMap}\,f\,L`$ | 各要素に $`f`$ を適用して連結 |
| `List.range n` | $`\mathrm{range}(n)`$ | $`[0,1,\dots,n-1]`$ |
| `List.range' a m` | $`\mathrm{range}'(a,m)`$ | $`[a,a+1,\dots,a+m-1]`$ |

[`Mechanized.md`](Mechanized.md) と同じく、行 0 の値 $`a`$ を基準とする `takeWhile` / `dropWhile` を

```math
\mathrm{tw}_a L := L.\mathrm{takeWhile}\,(\lambda q.\ a<\pi_0 q),\qquad
  \mathrm{dw}_a L := L.\mathrm{dropWhile}\,(\lambda q.\ a<\pi_0 q)
```

と略記する。$`\mathrm{tw}_a L`$ は $`L`$ の先頭から「行 0 の値が $`a`$ より真に大きい」対が続く極大な前部分列、
$`\mathrm{dw}_a L`$ はその残りであり、$`\mathrm{tw}_a L \mathbin{+\!\!+} \mathrm{dw}_a L = L`$ が成り立つ。

ペア列の型は [(D.PairSeq)](Def.md#d-PairSeq)、成分 $`M_{i,j}`$ は [(D.entry)](Def.md#d-entry)、
展開 $`M[n]`$ は [(D.oper)](Def.md#d-oper) である。[(D.entry)](Def.md#d-entry) より
$`M_{0,j}=\pi_0(M\langle j\rangle)`$、$`M_{1,j}=\pi_1(M\langle j\rangle)`$ であり、以下ではこの 2 つの表示を
同じものとして行き来する。

### 標準ライブラリの補助事実

本章で用いる標準ライブラリの事実を挙げておく（$`p`$ は要素上の述語、$`l,l_1,l_2`$ はリスト、$`d`$ は既定値）。

- `List.getLastD_nil`：$`\mathrm{lastD}([],d) = d`$
- `List.getLastD_cons`：$`\mathrm{lastD}(b\mathbin{::}l,\ d) = \mathrm{lastD}(l,\ b)`$（既定値が先頭要素に置き換わる）
- `List.getLastD_eq_getLast?`：$`\mathrm{lastD}(l,d) = (l.\mathrm{getLast?}).\mathrm{getD}\,d`$
- `List.getLast?_eq_getElem?`：$`l.\mathrm{getLast?} = l[\lvert l\rvert-1]?`$
- `List.getD_eq_getElem?_getD`：$`\mathrm{getD}(l,i,d) = (l[i]?).\mathrm{getD}\,d`$
- `List.mem_takeWhile_imp`：$`x\in l.\mathrm{takeWhile}\,p \Rightarrow p\,x`$
- `List.head?_dropWhile_not`：$`l.\mathrm{dropWhile}\,p`$ が空でなければ、その先頭要素は $`p`$ をみたさない
- `List.takeWhile_sublist`：$`l.\mathrm{takeWhile}\,p`$ は $`l`$ の部分列である
- `List.dropWhile_sublist`：$`l.\mathrm{dropWhile}\,p`$ は $`l`$ の部分列である
- `List.length_dropWhile_le`：$`\lvert l.\mathrm{dropWhile}\,p\rvert\le\lvert l\rvert`$
- `List.takeWhile_append_dropWhile`：$`l.\mathrm{takeWhile}\,p \mathbin{+\!\!+} l.\mathrm{dropWhile}\,p = l`$
- `List.takeWhile_cons_of_pos` / `_of_neg`：$`p\,a`$ なら $`(a\mathbin{::}l).\mathrm{takeWhile}\,p = a\mathbin{::}l.\mathrm{takeWhile}\,p`$、
  $`\neg p\,a`$ なら $`(a\mathbin{::}l).\mathrm{takeWhile}\,p = []`$
- `List.dropWhile_cons_of_pos` / `_of_neg`：$`p\,a`$ なら $`(a\mathbin{::}l).\mathrm{dropWhile}\,p = l.\mathrm{dropWhile}\,p`$、
  $`\neg p\,a`$ なら $`(a\mathbin{::}l).\mathrm{dropWhile}\,p = a\mathbin{::}l`$
- `List.dropLast_subset`：$`\mathrm{dropLast}\,l`$ の要素は $`l`$ の要素である
- `List.dropLast_append_getLast`：$`l\ne[]`$ ならば $`\mathrm{dropLast}\,l \mathbin{+\!\!+} [\mathrm{getLast}\,l] = l`$
- `List.length_take`：$`\lvert\mathrm{take}\,k\,l\rvert = \min(k,\lvert l\rvert)`$
- `List.getElem_take`：$`i\lt \lvert\mathrm{take}\,k\,l\rvert`$ のとき $`(\mathrm{take}\,k\,l)[i] = l[i]`$
- `List.range_succ`：$`\mathrm{range}(m+1) = \mathrm{range}(m)\mathbin{+\!\!+}[m]`$
- `List.range'_succ`：$`\mathrm{range}'(a,m+1) = a\mathbin{::}\mathrm{range}'(a+1,m)`$
- `List.getElem_range'`：$`i\lt m`$ のとき $`\mathrm{range}'(a,m)[i] = a+i`$
- `List.flatMap_append`：$`\mathrm{flatMap}\,f\,(l_1\mathbin{+\!\!+}l_2) = \mathrm{flatMap}\,f\,l_1 \mathbin{+\!\!+} \mathrm{flatMap}\,f\,l_2`$
- `List.append_eq_nil_iff`：$`l_1\mathbin{+\!\!+}l_2 = [] \iff l_1=[] \wedge l_2=[]`$

---

## 列辞書式順序

<a id="d-pairlt"></a>
### 定義 対の辞書式順序 (D.pairlt)

$`p,q\in\mathbb{N}\times\mathbb{N}`$ に対し

```math
p <_{\mathrm p} q \ :\iff\ \pi_0 p<\pi_0 q \ \vee\ \bigl(\pi_0 p=\pi_0 q \wedge \pi_1 p<\pi_1 q\bigr).
```

行 0 の成分を優先し、それが等しいときに行 1 の成分を比べる辞書式順序である。

<a id="d-seqlex"></a>
### 定義 列辞書式順序 (D.seqlex)

ペア列 $`M,N`$ に対し $`M\prec_{\mathrm{lex}}N`$ を、$`M`$ の構造に関する再帰で定める。

```math
\begin{aligned}
{}[\,] \prec_{\mathrm{lex}} N &\ :\iff\ N\ne[\,],\cr
(p\mathbin{::}M) \prec_{\mathrm{lex}} [\,] &\ :\iff\ \bot,\cr
(p\mathbin{::}M) \prec_{\mathrm{lex}} (q\mathbin{::}N) &\ :\iff\ p<_{\mathrm p}q \ \vee\ \bigl(p=q \wedge M\prec_{\mathrm{lex}}N\bigr).
\end{aligned}
```

（[(D.pairlt)](#d-pairlt)。）第 3 式の再帰呼び出し $`M\prec_{\mathrm{lex}}N`$ の第 1 引数 $`M`$ は
$`p\mathbin{::}M`$ の尾部、すなわち構成子 $`\mathbin{::}`$ の直下の引数であるから、
この定義は第 1 引数に関する構造帰納として整合的である。
先頭から順に対を比べ、最初に相違した位置の $`\lt _{\mathrm p}`$ で大小を決める順序であり、
$`v\ne[\,]`$ のとき $`u\prec_{\mathrm{lex}}(u\mathbin{+\!\!+}v)`$ が成り立つ（[(T.seqlex_prefix)](#t-seqlex_prefix)）。

<a id="t-seqlex_nil_iff"></a>
### 定理 空列との比較 (T.seqlex_nil_iff)

**主張** $`[\,]\prec_{\mathrm{lex}}N \iff N\ne[\,]`$。

**証明** [(D.seqlex)](#d-seqlex) の第 1 式により、両辺は定義により同一の命題である。∎

<a id="t-not_seqlex_nil"></a>
### 定理 空列より小さい列はない (T.not_seqlex_nil)

**主張** 任意の対 $`p`$ とペア列 $`M`$ に対し $`\neg\bigl((p\mathbin{::}M)\prec_{\mathrm{lex}}[\,]\bigr)`$。

**証明** [(D.seqlex)](#d-seqlex) の第 2 式により $`(p\mathbin{::}M)\prec_{\mathrm{lex}}[\,]`$ は $`\bot`$ と定義により等しい。
よってこの仮定からそのまま $`\bot`$ が得られる。∎

<a id="t-seqlex_cons_cons"></a>
### 定理 先頭付加どうしの比較 (T.seqlex_cons_cons)

**主張**
```math
(p\mathbin{::}M)\prec_{\mathrm{lex}}(q\mathbin{::}N) \iff p<_{\mathrm p}q \ \vee\ \bigl(p=q \wedge M\prec_{\mathrm{lex}}N\bigr).
```

**証明** [(D.seqlex)](#d-seqlex) の第 3 式そのものであり、両辺は定義により同一の命題である。∎

<a id="t-seqlex_append_cancel"></a>
### 定理 共通前部の消去 (T.seqlex_append_cancel)

**主張** 任意のペア列 $`A,u,v`$ に対し
```math
(A\mathbin{+\!\!+}u)\prec_{\mathrm{lex}}(A\mathbin{+\!\!+}v) \iff u\prec_{\mathrm{lex}}v.
```

**証明** $`u,v`$ を固定し、$`A`$ の構造に関する帰納法。帰納法の述語は
```math
\Phi(A) :\equiv \Bigl((A\mathbin{+\!\!+}u)\prec_{\mathrm{lex}}(A\mathbin{+\!\!+}v) \iff u\prec_{\mathrm{lex}}v\Bigr).
```

- 基底段 $`A=[\,]`$：$`[\,]\mathbin{+\!\!+}u = u`$、$`[\,]\mathbin{+\!\!+}v = v`$ であるから、両辺は同一の命題である。
- 帰納段 $`A=a\mathbin{::}A'`$：帰納法の仮定は $`\Phi(A')`$ である。
  $`(a\mathbin{::}A')\mathbin{+\!\!+}u = a\mathbin{::}(A'\mathbin{+\!\!+}u)`$、$`(a\mathbin{::}A')\mathbin{+\!\!+}v = a\mathbin{::}(A'\mathbin{+\!\!+}v)`$ であるから、
  [(T.seqlex_cons_cons)](#t-seqlex_cons_cons) より左辺は
  ```math
  a<_{\mathrm p}a \ \vee\ \bigl(a=a \wedge (A'\mathbin{+\!\!+}u)\prec_{\mathrm{lex}}(A'\mathbin{+\!\!+}v)\bigr)
  ```
  と同値である。
  - ($`\Rightarrow`$) 第 1 選言 $`a\lt _{\mathrm p}a`$ は、[(D.pairlt)](#d-pairlt) より
    $`\pi_0 a\lt \pi_0 a`$ または $`(\pi_0 a=\pi_0 a \wedge \pi_1 a\lt \pi_1 a)`$ であるが、
    $`\mathbb{N}`$ の $`\lt `$ の非反射性によりどちらも偽である。よって第 2 選言が成り立ち、
    その第 2 成分に帰納法の仮定 $`\Phi(A')`$ の $`(\Rightarrow)`$ 方向を適用して $`u\prec_{\mathrm{lex}}v`$ を得る。
  - ($`\Leftarrow`$) $`u\prec_{\mathrm{lex}}v`$ から帰納法の仮定 $`\Phi(A')`$ の $`(\Leftarrow)`$ 方向で
    $`(A'\mathbin{+\!\!+}u)\prec_{\mathrm{lex}}(A'\mathbin{+\!\!+}v)`$ を得、$`a=a`$ とあわせて第 2 選言が成り立つ。∎

<a id="t-seqlex_prefix"></a>
### 定理 真の前部分列は小さい (T.seqlex_prefix)

**主張** $`v\ne[\,]`$ ならば、任意のペア列 $`u`$ に対し $`u\prec_{\mathrm{lex}}(u\mathbin{+\!\!+}v)`$。

**証明** $`v`$ とその仮定 $`v\ne[\,]`$ を固定し、$`u`$ の構造に関する帰納法。帰納法の述語は
```math
\Phi(u) :\equiv u\prec_{\mathrm{lex}}(u\mathbin{+\!\!+}v).
```

- 基底段 $`u=[\,]`$：$`[\,]\mathbin{+\!\!+}v = v`$ であり、[(T.seqlex_nil_iff)](#t-seqlex_nil_iff) より
  $`[\,]\prec_{\mathrm{lex}}v`$ は $`v\ne[\,]`$ と同値、これは仮定である。
- 帰納段 $`u=a\mathbin{::}u'`$：帰納法の仮定は $`\Phi(u')`$、すなわち $`u'\prec_{\mathrm{lex}}(u'\mathbin{+\!\!+}v)`$ である。
  $`(a\mathbin{::}u')\mathbin{+\!\!+}v = a\mathbin{::}(u'\mathbin{+\!\!+}v)`$ であるから、
  [(T.seqlex_cons_cons)](#t-seqlex_cons_cons) の右辺第 2 選言 $`a=a \wedge \Phi(u')`$ が成立し、$`\Phi(a\mathbin{::}u')`$ を得る。∎

---

## ブロック規律

<a id="d-steps1"></a>
### 定義 隣接段の増分制限 (D.steps1)

ペア列 $`B`$ に対し $`\mathrm{steps}_1(B)`$ を、$`B`$ の構造に関する再帰で定める。

```math
\mathrm{steps}_1([\,]) := \top,\qquad
  \mathrm{steps}_1([p]) := \top,\qquad
  \mathrm{steps}_1(p\mathbin{::}q\mathbin{::}r) := \bigl(\pi_0 q\le\pi_0 p+1\bigr) \wedge \mathrm{steps}_1(q\mathbin{::}r).
```

すなわち、隣り合う 2 対のあいだで行 0 の値が高々 1 しか増えないという条件である
（減る分には制限がない）。

<a id="t-steps1_nil"></a>
### 定理 空列は条件をみたす (T.steps1_nil)

**主張** $`\mathrm{steps}_1([\,])`$。

**証明** [(D.steps1)](#d-steps1) の第 1 式により $`\mathrm{steps}_1([\,])`$ は $`\top`$ と定義により等しい。∎

<a id="t-steps1_single"></a>
### 定理 1 元列は条件をみたす (T.steps1_single)

**主張** 任意の対 $`p`$ に対し $`\mathrm{steps}_1([p])`$。

**証明** [(D.steps1)](#d-steps1) の第 2 式により $`\mathrm{steps}_1([p])`$ は $`\top`$ と定義により等しい。∎

<a id="t-steps1_cons_cons"></a>
### 定理 2 元以上の場合の展開 (T.steps1_cons_cons)

**主張**
```math
\mathrm{steps}_1(p\mathbin{::}q\mathbin{::}r) \iff \bigl(\pi_0 q\le\pi_0 p+1\bigr) \wedge \mathrm{steps}_1(q\mathbin{::}r).
```

**証明** [(D.steps1)](#d-steps1) の第 3 式そのものであり、両辺は定義により同一の命題である。∎

<a id="d-blockok"></a>
### 定義 深さ $`d`$ のブロック (D.blockok)

$`d\in\mathbb{N}`$、ペア列 $`B`$ に対し

```math
\mathrm{blockok}(d,B) \ :\iff\
\bigl(B\ne[\,] \to \pi_0(\mathrm{headI}\,B)=d\bigr)
\ \wedge\ \bigl(\forall p\in B,\ d\le\pi_0 p\bigr)
\ \wedge\ \mathrm{steps}_1(B).
```

すなわち、$`B`$ が空でなければ先頭対の行 0 の値はちょうど $`d`$、$`B`$ のすべての対の行 0 の値は $`d`$ 以上、
かつ隣接段の増分は高々 1（[(D.steps1)](#d-steps1)）である。
以下、$`\mathrm{blockok}(d,B)`$ の 3 つの連言成分を順に**先頭条件**・**下界条件**・**増分条件**と呼ぶ。

<a id="t-steps1_iff"></a>
### 定理 添字による特徴づけ (T.steps1_iff)

**主張** 任意のペア列 $`B`$ に対し
```math
\mathrm{steps}_1(B) \iff \forall j,\ j+1<\lvert B\rvert \to \pi_0(B\langle j+1\rangle)\le\pi_0(B\langle j\rangle)+1.
```

**証明** $`B`$ の構造に関する帰納法。帰納法の述語は
```math
\Phi(B) :\equiv \Bigl(\mathrm{steps}_1(B) \iff \forall j,\ j+1<\lvert B\rvert \to \pi_0(B\langle j+1\rangle)\le\pi_0(B\langle j\rangle)+1\Bigr).
```

- 基底段 $`B=[\,]`$：左辺は [(T.steps1_nil)](#t-steps1_nil) より真。
  右辺は、$`\lvert[\,]\rvert=0`$ より前件 $`j+1\lt 0`$ がすべての $`j`$ で偽だから空虚に真。よって両辺とも真であり $`\Phi([\,])`$。
- 帰納段 $`B=p\mathbin{::}B'`$：帰納法の仮定は $`\Phi(B')`$ である。$`B'`$ の形で 2 つに分ける。
  - $`B'=[\,]`$、すなわち $`B=[p]`$：左辺は [(T.steps1_single)](#t-steps1_single) より真。
    右辺は $`\lvert[p]\rvert=1`$ より前件 $`j+1\lt 1`$ がすべての $`j`$ で偽（$`j+1\ge1`$）だから空虚に真。
  - $`B'=q\mathbin{::}r`$、すなわち $`B=p\mathbin{::}q\mathbin{::}r`$：このとき帰納法の仮定 $`\Phi(q\mathbin{::}r)`$ は
    ```math
    \mathrm{steps}_1(q\mathbin{::}r) \iff \forall j,\ j+1<\lvert r\rvert+1 \to \pi_0((q\mathbin{::}r)\langle j+1\rangle)\le\pi_0((q\mathbin{::}r)\langle j\rangle)+1
    ```
    である。[(T.steps1_cons_cons)](#t-steps1_cons_cons) と $`\Phi(q\mathbin{::}r)`$ により、示すべきは
    ```math
    \Bigl(\pi_0 q\le\pi_0 p+1 \ \wedge\ \forall j,\ j+1<\lvert r\rvert+1 \to \pi_0((q\mathbin{::}r)\langle j+1\rangle)\le\pi_0((q\mathbin{::}r)\langle j\rangle)+1\Bigr)
    ```
    と
    ```math
    \Bigl(\forall j,\ j+1<\lvert r\rvert+2 \to \pi_0((p\mathbin{::}q\mathbin{::}r)\langle j+1\rangle)\le\pi_0((p\mathbin{::}q\mathbin{::}r)\langle j\rangle)+1\Bigr)
    ```
    の同値である。ここで添字の対応 $`(p\mathbin{::}L)\langle k+1\rangle = L\langle k\rangle`$ および
    $`(p\mathbin{::}L)\langle 0\rangle = p`$ を用いる。
    - ($`\Rightarrow`$) 前者を $`\langle h,\ h_{\mathrm{s}}\rangle`$ とし、$`j+1\lt \lvert r\rvert+2`$ なる $`j`$ を取る。
      - $`j=0`$ のとき：示すべきは $`\pi_0((p\mathbin{::}q\mathbin{::}r)\langle 1\rangle)\le\pi_0((p\mathbin{::}q\mathbin{::}r)\langle 0\rangle)+1`$、
        すなわち $`\pi_0 q\le\pi_0 p+1`$ であり、これは $`h`$ である。
      - $`j=j'+1`$ のとき：$`j'+2\lt \lvert r\rvert+2`$ より $`j'+1\lt \lvert r\rvert+1`$ であるから
        $`h_{\mathrm{s}}\,j'`$ が使え、
        $`\pi_0((q\mathbin{::}r)\langle j'+1\rangle)\le\pi_0((q\mathbin{::}r)\langle j'\rangle)+1`$ を得る。
        添字の対応により、これは
        $`\pi_0((p\mathbin{::}q\mathbin{::}r)\langle j'+2\rangle)\le\pi_0((p\mathbin{::}q\mathbin{::}r)\langle j'+1\rangle)+1`$ に等しい。
    - ($`\Leftarrow`$) 後者を $`h`$ とする。
      - 第 1 成分：$`h\,0`$ を $`0+1\lt \lvert r\rvert+2`$（$`1\lt \lvert r\rvert+2`$ は $`\lvert r\rvert\ge0`$ より成立）に適用すると
        $`\pi_0((p\mathbin{::}q\mathbin{::}r)\langle 1\rangle)\le\pi_0((p\mathbin{::}q\mathbin{::}r)\langle 0\rangle)+1`$、すなわち $`\pi_0 q\le\pi_0 p+1`$。
      - 第 2 成分：$`j+1\lt \lvert r\rvert+1`$ なる $`j`$ に対し $`j+2\lt \lvert r\rvert+2`$ であるから $`h\,(j+1)`$ が使え、
        $`\pi_0((p\mathbin{::}q\mathbin{::}r)\langle j+2\rangle)\le\pi_0((p\mathbin{::}q\mathbin{::}r)\langle j+1\rangle)+1`$、
        すなわち $`\pi_0((q\mathbin{::}r)\langle j+1\rangle)\le\pi_0((q\mathbin{::}r)\langle j\rangle)+1`$ を得る。∎

<a id="t-steps1_tail"></a>
### 定理 尾部への遺伝 (T.steps1_tail)

**主張** $`\mathrm{steps}_1(p\mathbin{::}r)`$ ならば $`\mathrm{steps}_1(r)`$。

**証明** $`r`$ の形で場合分けする。

- $`r=[\,]`$：[(T.steps1_nil)](#t-steps1_nil) より $`\mathrm{steps}_1([\,])`$。
- $`r=q\mathbin{::}r'`$：[(T.steps1_cons_cons)](#t-steps1_cons_cons) より仮定は
  $`\pi_0 q\le\pi_0 p+1`$ と $`\mathrm{steps}_1(q\mathbin{::}r')`$ の連言であるから、その第 2 成分を取ればよい。∎

<a id="t-steps1_append"></a>
### 定理 連結の分解 (T.steps1_append)

**主張** 任意のペア列 $`A,B`$ に対し
```math
\mathrm{steps}_1(A\mathbin{+\!\!+}B) \iff
 \mathrm{steps}_1(A) \wedge \mathrm{steps}_1(B) \wedge
 \Bigl(A=[\,] \ \vee\ B=[\,] \ \vee\ \pi_0(\mathrm{headI}\,B)\le\pi_0(\mathrm{lastD}(A,(0,0)))+1\Bigr).
```

すなわち、連結が増分条件をみたすことは、各片が増分条件をみたし、かつ両者が空でないときに**継ぎ目**
（$`A`$ の末尾と $`B`$ の先頭）でも増分が高々 1 であることと同値である。

**証明** $`B`$ を固定し、$`A`$ の構造に関する帰納法。帰納法の述語は
```math
\Phi(A) :\equiv \Bigl(\mathrm{steps}_1(A\mathbin{+\!\!+}B) \iff \mathrm{steps}_1(A)\wedge\mathrm{steps}_1(B)\wedge(A=[\,]\vee B=[\,]\vee \pi_0(\mathrm{headI}\,B)\le\pi_0(\mathrm{lastD}(A,(0,0)))+1)\Bigr).
```

- 基底段 $`A=[\,]`$：左辺は $`\mathrm{steps}_1([\,]\mathbin{+\!\!+}B)=\mathrm{steps}_1(B)`$。
  右辺は、$`\mathrm{steps}_1([\,])`$ が [(T.steps1_nil)](#t-steps1_nil) より真、第 3 成分も第 1 選言 $`[\,]=[\,]`$ により真だから、
  $`\mathrm{steps}_1(B)`$ と同値。よって両辺は同値であり $`\Phi([\,])`$。
- 帰納段 $`A=p\mathbin{::}A_1`$：帰納法の仮定は $`\Phi(A_1)`$ である。$`A_1`$ の形で 2 つに分ける。
  - $`A_1=[\,]`$、すなわち $`A=[p]`$：$`[p]\mathbin{+\!\!+}B = p\mathbin{::}B`$ である。$`B`$ の形でさらに分ける。
    - $`B=[\,]`$：左辺は $`\mathrm{steps}_1([p])`$ で [(T.steps1_single)](#t-steps1_single) より真。
      右辺も $`\mathrm{steps}_1([p])`$、$`\mathrm{steps}_1([\,])`$ が真で、第 3 成分は第 2 選言 $`B=[\,]`$ により真。両辺とも真。
    - $`B=q\mathbin{::}B'`$：左辺は [(T.steps1_cons_cons)](#t-steps1_cons_cons) より
      $`\pi_0 q\le\pi_0 p+1 \wedge \mathrm{steps}_1(q\mathbin{::}B')`$。
      右辺は、$`\mathrm{steps}_1([p])`$ が真、$`\mathrm{headI}(q\mathbin{::}B')=q`$、
      $`\mathrm{lastD}([p],(0,0)) = \mathrm{lastD}([\,],p) = p`$（`List.getLastD_cons` と `List.getLastD_nil`）であり、
      第 3 成分の第 1 選言 $`[p]=[\,]`$ と第 2 選言 $`q\mathbin{::}B'=[\,]`$ はいずれも偽だから、
      $`\mathrm{steps}_1(q\mathbin{::}B') \wedge \pi_0 q\le\pi_0 p+1`$ と同値。連言の順序を除いて両辺は同じである。
  - $`A_1=p'\mathbin{::}A_2`$、すなわち $`A=p\mathbin{::}p'\mathbin{::}A_2`$：
    $`A\mathbin{+\!\!+}B = p\mathbin{::}p'\mathbin{::}(A_2\mathbin{+\!\!+}B)`$ であるから、
    [(T.steps1_cons_cons)](#t-steps1_cons_cons) より左辺は
    ```math
    \pi_0 p'\le\pi_0 p+1 \ \wedge\ \mathrm{steps}_1\bigl(p'\mathbin{::}(A_2\mathbin{+\!\!+}B)\bigr)
    ```
    と同値である。ここで $`p'\mathbin{::}(A_2\mathbin{+\!\!+}B) = (p'\mathbin{::}A_2)\mathbin{+\!\!+}B = A_1\mathbin{+\!\!+}B`$ である。
    また `List.getLastD_cons` を 2 回用いると
    ```math
    \mathrm{lastD}(p\mathbin{::}p'\mathbin{::}A_2,\ (0,0)) = \mathrm{lastD}(p'\mathbin{::}A_2,\ p) = \mathrm{lastD}(A_2,\ p'),\qquad
      \mathrm{lastD}(p'\mathbin{::}A_2,\ (0,0)) = \mathrm{lastD}(A_2,\ p')
    ```
    であるから、$`A`$ と $`A_1`$ の $`\mathrm{lastD}`$ は一致する。これを $`(\ast)`$ とおく。
    - ($`\Rightarrow`$) 左辺から $`h_1 : \pi_0 p'\le\pi_0 p+1`$ と $`h_2 : \mathrm{steps}_1(A_1\mathbin{+\!\!+}B)`$ を得る。
      $`\Phi(A_1)`$ の $`(\Rightarrow)`$ 方向を $`h_2`$ に適用して
      $`h_A : \mathrm{steps}_1(A_1)`$、$`h_B : \mathrm{steps}_1(B)`$、
      $`h_j : A_1=[\,] \vee B=[\,] \vee \pi_0(\mathrm{headI}\,B)\le\pi_0(\mathrm{lastD}(A_1,(0,0)))+1`$ を得る。
      示すべき右辺の第 1 成分 $`\mathrm{steps}_1(p\mathbin{::}p'\mathbin{::}A_2)`$ は
      [(T.steps1_cons_cons)](#t-steps1_cons_cons) より $`\langle h_1, h_A\rangle`$。第 2 成分は $`h_B`$。
      第 3 成分は $`h_j`$ から得る：$`h_j`$ の第 1 選言 $`A_1 = p'\mathbin{::}A_2=[\,]`$ は偽、
      第 2 選言 $`B=[\,]`$ はそのまま第 2 選言、第 3 選言は $`(\ast)`$ により $`A`$ についての第 3 選言に等しい。
    - ($`\Leftarrow`$) 右辺から $`\mathrm{steps}_1(p\mathbin{::}p'\mathbin{::}A_2)`$、すなわち
      [(T.steps1_cons_cons)](#t-steps1_cons_cons) より $`h_1 : \pi_0 p'\le\pi_0 p+1`$ と $`h_A : \mathrm{steps}_1(A_1)`$、
      および $`h_B : \mathrm{steps}_1(B)`$ と第 3 成分 $`h_j`$ を得る。
      $`h_j`$ の第 1 選言 $`p\mathbin{::}p'\mathbin{::}A_2=[\,]`$ は偽、第 2 選言 $`B=[\,]`$ はそのまま、
      第 3 選言は $`(\ast)`$ により $`A_1`$ についての第 3 選言に等しい。
      よって $`\Phi(A_1)`$ の $`(\Leftarrow)`$ 方向が使え $`\mathrm{steps}_1(A_1\mathbin{+\!\!+}B)`$ を得る。
      $`h_1`$ とあわせて [(T.steps1_cons_cons)](#t-steps1_cons_cons) より左辺を得る。∎

<a id="t-steps1_dropLast"></a>
### 定理 末尾削除への遺伝 (T.steps1_dropLast)

**主張** $`\mathrm{steps}_1(B)`$ ならば $`\mathrm{steps}_1(\mathrm{dropLast}\,B)`$。

**証明** $`B=[\,]`$ かどうかで場合分けする。

- $`B=[\,]`$：$`\mathrm{dropLast}\,[\,]=[\,]`$ であり [(T.steps1_nil)](#t-steps1_nil) による。
- $`B\ne[\,]`$：`List.dropLast_append_getLast` より
  $`\mathrm{dropLast}\,B \mathbin{+\!\!+} [\mathrm{getLast}\,B] = B`$ である。
  仮定 $`\mathrm{steps}_1(B)`$ をこの等式で書き換えると
  $`\mathrm{steps}_1(\mathrm{dropLast}\,B\mathbin{+\!\!+}[\mathrm{getLast}\,B])`$ であり、
  [(T.steps1_append)](#t-steps1_append) の $`(\Rightarrow)`$ 方向の第 1 成分が $`\mathrm{steps}_1(\mathrm{dropLast}\,B)`$ を与える。∎

<a id="t-blockok_dropLast"></a>
### 定理 末尾削除はブロック条件を保つ (T.blockok_dropLast)

**主張** $`\mathrm{blockok}(d,B)`$ ならば $`\mathrm{blockok}(d,\mathrm{dropLast}\,B)`$。

**証明** 仮定を [(D.blockok)](#d-blockok) の 3 成分 $`h_{\mathrm{hd}}`$（先頭条件）、$`h_{\mathrm{set}}`$（下界条件）、
$`h_{\mathrm{s}}`$（増分条件）に分ける。

- 下界条件：$`p\in\mathrm{dropLast}\,B`$ ならば `List.dropLast_subset` より $`p\in B`$、よって $`h_{\mathrm{set}}\,p`$ から $`d\le\pi_0 p`$。
- 増分条件：[(T.steps1_dropLast)](#t-steps1_dropLast) を $`h_{\mathrm{s}}`$ に適用する。
- 先頭条件：$`\mathrm{dropLast}\,B\ne[\,]`$ と仮定する。まず $`B\ne[\,]`$ である（$`B=[\,]`$ なら $`\mathrm{dropLast}\,B=[\,]`$）。
  よって $`B=x\mathbin{::}xs`$ と書ける。さらに $`xs\ne[\,]`$ である。実際 $`xs=[\,]`$ なら
  $`\mathrm{dropLast}\,[x]=[\,]`$ となり仮定に反する。そこで $`xs=y\mathbin{::}ys`$ と書けば、
  $`\mathrm{dropLast}`$ の定義より
  ```math
  \mathrm{dropLast}(x\mathbin{::}y\mathbin{::}ys) = x\mathbin{::}\mathrm{dropLast}(y\mathbin{::}ys)
  ```
  であるから $`\mathrm{headI}(\mathrm{dropLast}\,B) = x = \mathrm{headI}\,B`$。
  $`B\ne[\,]`$ に $`h_{\mathrm{hd}}`$ を適用して $`\pi_0 x=d`$ を得る。∎

---

## ブロックを先頭で分割する

深さ $`d`$ のブロック $`B=(d,y)\mathbin{::}r`$ を、$`\mathrm{tw}_d r`$（**引数部**）と $`\mathrm{dw}_d r`$（**後続部**）に分ける。
[(D.translate)](Mechanized.md#d-translate) の再帰がまさにこの分割であるから、
この 2 つが再びブロックになることが、次節の順序同型の帰納段を可能にする。

<a id="t-blockok_arg"></a>
### 定理 引数部は深さ $`d+1`$ のブロック (T.blockok_arg)

**主張** $`\mathrm{blockok}(d,(d,y)\mathbin{::}r)`$ ならば $`\mathrm{blockok}(d+1,\ \mathrm{tw}_d r)`$。

**証明** 仮定を [(D.blockok)](#d-blockok) の成分 $`h_{\mathrm{set}}`$（下界条件）、$`h_{\mathrm{s}}`$（増分条件）に分ける
（先頭条件は使わない）。3 成分を確かめる。

- **先頭条件**：$`\mathrm{tw}_d r\ne[\,]`$ と仮定し、$`\pi_0(\mathrm{headI}(\mathrm{tw}_d r))=d+1`$ を示す。
  $`\mathrm{tw}_d r = a\mathbin{::}as`$ と書く。$`r=[\,]`$ なら $`\mathrm{tw}_d[\,]=[\,]`$ となり矛盾するので、$`r=p'\mathbin{::}r'`$ と書ける。
  ここで $`d\lt \pi_0 p'`$ である。実際 $`\neg(d\lt \pi_0 p')`$ ならば `List.takeWhile_cons_of_neg` より
  $`\mathrm{tw}_d(p'\mathbin{::}r')=[\,]`$ となり $`a\mathbin{::}as`$ と等しくなり得ない。
  すると `List.takeWhile_cons_of_pos` より $`\mathrm{tw}_d(p'\mathbin{::}r') = p'\mathbin{::}\mathrm{tw}_d r'`$ であり、
  $`a\mathbin{::}as`$ との比較（先頭付加の単射性）から $`a=p'`$。
  一方 $`h_{\mathrm{s}}`$ は $`\mathrm{steps}_1((d,y)\mathbin{::}p'\mathbin{::}r')`$ であるから、
  [(T.steps1_cons_cons)](#t-steps1_cons_cons) の第 1 成分より
  $`\pi_0 p'\le\pi_0(d,y)+1 = d+1`$。
  $`d\lt \pi_0 p'`$ と $`\pi_0 p'\le d+1`$ から、$`\mathbb{N}`$ において $`d+1\le\pi_0 p'\le d+1`$、すなわち $`\pi_0 p'=d+1`$。
  $`\mathrm{headI}(\mathrm{tw}_d r)=a=p'`$ だから、$`\pi_0(\mathrm{headI}(\mathrm{tw}_d r))=d+1`$。
- **下界条件**：$`q\in\mathrm{tw}_d r`$ とする。`List.mem_takeWhile_imp` より、$`\mathrm{tw}_d`$ の定義に現れる述語
  $`\lambda q.\ d\lt \pi_0 q`$ が $`q`$ で成り立つ、すなわち $`d\lt \pi_0 q`$。
  $`\mathbb{N}`$ では $`d\lt \pi_0 q`$ と $`d+1\le\pi_0 q`$ は同値だから $`d+1\le\pi_0 q`$。
- **増分条件**：`List.takeWhile_append_dropWhile` より $`\mathrm{tw}_d r\mathbin{+\!\!+}\mathrm{dw}_d r = r`$ であり、
  [(T.steps1_tail)](#t-steps1_tail) を $`h_{\mathrm{s}}`$ に適用して $`\mathrm{steps}_1(r)`$ を得る。
  よって $`\mathrm{steps}_1(\mathrm{tw}_d r\mathbin{+\!\!+}\mathrm{dw}_d r)`$ が成り立ち、
  [(T.steps1_append)](#t-steps1_append) の $`(\Rightarrow)`$ 方向の第 1 成分より $`\mathrm{steps}_1(\mathrm{tw}_d r)`$。∎

<a id="t-blockok_tail"></a>
### 定理 後続部は深さ $`d`$ のブロック (T.blockok_tail)

**主張** $`\mathrm{blockok}(d,(d,y)\mathbin{::}r)`$ ならば $`\mathrm{blockok}(d,\ \mathrm{dw}_d r)`$。

**証明** 仮定を成分 $`h_{\mathrm{set}}`$（下界条件）、$`h_{\mathrm{s}}`$（増分条件）に分ける。

- **先頭条件**：$`\mathrm{dw}_d r\ne[\,]`$ と仮定し、$`\mathrm{dw}_d r = a\mathbin{::}as`$ と書く。
  `List.head?_dropWhile_not` より、$`\mathrm{dw}_d r`$ の先頭要素は述語をみたさない、すなわち $`\neg(d\lt \pi_0 a)`$。
  他方 `List.dropWhile_sublist` より $`a\in r`$、よって $`a\in(d,y)\mathbin{::}r`$ であり
  $`h_{\mathrm{set}}\,a`$ から $`d\le\pi_0 a`$。
  $`\mathbb{N}`$ において $`\neg(d\lt \pi_0 a)`$ は $`\pi_0 a\le d`$ と同値だから、$`d\le\pi_0 a\le d`$、すなわち $`\pi_0 a=d`$。
  $`\mathrm{headI}(\mathrm{dw}_d r)=a`$ だから先頭条件が成り立つ。
- **下界条件**：$`q\in\mathrm{dw}_d r`$ ならば `List.dropWhile_sublist` より $`q\in r`$、
  よって $`q\in(d,y)\mathbin{::}r`$ であり $`h_{\mathrm{set}}\,q`$ から $`d\le\pi_0 q`$。
- **増分条件**：`List.takeWhile_append_dropWhile` より $`\mathrm{tw}_d r\mathbin{+\!\!+}\mathrm{dw}_d r = r`$ であり、
  [(T.steps1_tail)](#t-steps1_tail) を $`h_{\mathrm{s}}`$ に適用して $`\mathrm{steps}_1(r)`$ を得る。
  よって $`\mathrm{steps}_1(\mathrm{tw}_d r\mathbin{+\!\!+}\mathrm{dw}_d r)`$ が成り立ち、
  [(T.steps1_append)](#t-steps1_append) の $`(\Rightarrow)`$ 方向の第 2 成分より $`\mathrm{steps}_1(\mathrm{dw}_d r)`$。∎

---

## 最初の相違は引数部か後続部のどちらかに現れる

<a id="t-seqlex_arg_or_tail"></a>
### 定理 相違位置の二分 (T.seqlex_arg_or_tail)

**主張** $`d\in\mathbb{N}`$、ペア列 $`r,r'`$ とし $`r\prec_{\mathrm{lex}}r'`$ とする。このとき

```math
\bigl(\mathrm{tw}_d r = \mathrm{tw}_d r' \ \wedge\ \mathrm{dw}_d r \prec_{\mathrm{lex}} \mathrm{dw}_d r'\bigr)
\ \ \vee\ \
\bigl(\mathrm{tw}_d r \ne \mathrm{tw}_d r' \ \wedge\ \mathrm{tw}_d r \prec_{\mathrm{lex}} \mathrm{tw}_d r'\bigr).
```

すなわち、$`r\prec_{\mathrm{lex}}r'`$ からは、$`\mathrm{tw}_d r=\mathrm{tw}_d r'`$ の場合には
$`\mathrm{dw}_d r\prec_{\mathrm{lex}}\mathrm{dw}_d r'`$ が、$`\mathrm{tw}_d r\ne\mathrm{tw}_d r'`$ の場合には
$`\mathrm{tw}_d r\prec_{\mathrm{lex}}\mathrm{tw}_d r'`$ が得られる。

**証明** $`r'`$ を全称量化したまま動かし、$`r`$ の構造に関する帰納法。帰納法の述語は

```math
\Phi(r) :\equiv \forall r',\ r\prec_{\mathrm{lex}}r' \to
\bigl(\mathrm{tw}_d r=\mathrm{tw}_d r' \wedge \mathrm{dw}_d r\prec_{\mathrm{lex}}\mathrm{dw}_d r'\bigr)
\vee \bigl(\mathrm{tw}_d r\ne\mathrm{tw}_d r' \wedge \mathrm{tw}_d r\prec_{\mathrm{lex}}\mathrm{tw}_d r'\bigr).
```

- **基底段 $`r=[\,]`$**：仮定 $`[\,]\prec_{\mathrm{lex}}r'`$ は [(T.seqlex_nil_iff)](#t-seqlex_nil_iff) より $`r'\ne[\,]`$ である。
  なお $`\mathrm{tw}_d[\,]=[\,]`$、$`\mathrm{dw}_d[\,]=[\,]`$ である。$`\mathrm{tw}_d r'`$ が空かどうかで分ける。
  - $`\mathrm{tw}_d r'=[\,]`$ のとき：第 1 選言を示す。第 1 成分は $`\mathrm{tw}_d[\,]=[\,]=\mathrm{tw}_d r'`$。
    第 2 成分のために $`\mathrm{dw}_d r'=r'`$ を示す。$`r'\ne[\,]`$ より $`r'=q\mathbin{::}t`$ と書ける。
    もし $`d\lt \pi_0 q`$ ならば `List.takeWhile_cons_of_pos` より $`\mathrm{tw}_d r' = q\mathbin{::}\mathrm{tw}_d t \ne[\,]`$ となり
    仮定に反するから $`\neg(d\lt \pi_0 q)`$。よって `List.dropWhile_cons_of_neg` より $`\mathrm{dw}_d r' = q\mathbin{::}t = r'`$。
    したがって $`\mathrm{dw}_d r' = r' \ne[\,]`$ であり、[(T.seqlex_nil_iff)](#t-seqlex_nil_iff) より
    $`[\,]\prec_{\mathrm{lex}}\mathrm{dw}_d r'`$、すなわち $`\mathrm{dw}_d[\,]\prec_{\mathrm{lex}}\mathrm{dw}_d r'`$。
  - $`\mathrm{tw}_d r'\ne[\,]`$ のとき：第 2 選言を示す。第 1 成分は $`[\,]\ne\mathrm{tw}_d r'`$（仮定の左右反転）。
    第 2 成分は [(T.seqlex_nil_iff)](#t-seqlex_nil_iff) より $`\mathrm{tw}_d r'\ne[\,]`$ と同値であり、これは仮定である。
- **帰納段 $`r=p\mathbin{::}rr`$**：帰納法の仮定は $`\Phi(rr)`$ である。
  $`r'=[\,]`$ ならば $`(p\mathbin{::}rr)\prec_{\mathrm{lex}}[\,]`$ は [(T.not_seqlex_nil)](#t-not_seqlex_nil) に反するから、
  $`r'=q\mathbin{::}rr'`$ と書ける。$`p=q`$ かどうかで分ける。
  - **$`p=q`$ のとき**：[(T.seqlex_cons_cons)](#t-seqlex_cons_cons) より仮定は
    $`p\lt _{\mathrm p}p`$ または $`(p=p \wedge rr\prec_{\mathrm{lex}}rr')`$ である。
    前者は [(D.pairlt)](#d-pairlt) より $`\pi_0 p\lt \pi_0 p`$ または $`(\pi_0 p=\pi_0 p \wedge \pi_1 p\lt \pi_1 p)`$ であり、
    $`\mathbb{N}`$ の $`\lt `$ の非反射性によりどちらも偽。よって $`rr\prec_{\mathrm{lex}}rr'`$ が成り立つ。これを $`sl_r`$ とおく。
    - $`d\lt \pi_0 p`$ のとき：`List.takeWhile_cons_of_pos` と `List.dropWhile_cons_of_pos` より
      ```math
      \mathrm{tw}_d(p\mathbin{::}rr)=p\mathbin{::}\mathrm{tw}_d rr,\quad \mathrm{dw}_d(p\mathbin{::}rr)=\mathrm{dw}_d rr,\quad
        \mathrm{tw}_d(p\mathbin{::}rr')=p\mathbin{::}\mathrm{tw}_d rr',\quad \mathrm{dw}_d(p\mathbin{::}rr')=\mathrm{dw}_d rr'.
      ```
      帰納法の仮定 $`\Phi(rr)`$ を $`rr'`$ と $`sl_r`$ に適用して 2 つに分ける。
      - $`\mathrm{tw}_d rr=\mathrm{tw}_d rr'`$ かつ $`\mathrm{dw}_d rr\prec_{\mathrm{lex}}\mathrm{dw}_d rr'`$ のとき：
        第 1 選言を示す。第 1 成分は $`p\mathbin{::}\mathrm{tw}_d rr = p\mathbin{::}\mathrm{tw}_d rr'`$、
        第 2 成分は $`\mathrm{dw}_d rr\prec_{\mathrm{lex}}\mathrm{dw}_d rr'`$ そのもの。
      - $`\mathrm{tw}_d rr\ne\mathrm{tw}_d rr'`$ かつ $`\mathrm{tw}_d rr\prec_{\mathrm{lex}}\mathrm{tw}_d rr'`$ のとき：
        第 2 選言を示す。第 1 成分は、$`p\mathbin{::}\mathrm{tw}_d rr = p\mathbin{::}\mathrm{tw}_d rr'`$ とすると
        先頭付加の単射性から $`\mathrm{tw}_d rr=\mathrm{tw}_d rr'`$ となり仮定に反する、から従う。
        第 2 成分は [(T.seqlex_cons_cons)](#t-seqlex_cons_cons) の右辺第 2 選言
        $`p=p \wedge \mathrm{tw}_d rr\prec_{\mathrm{lex}}\mathrm{tw}_d rr'`$ による。
    - $`\neg(d\lt \pi_0 p)`$ のとき：`List.takeWhile_cons_of_neg` と `List.dropWhile_cons_of_neg` より
      ```math
      \mathrm{tw}_d(p\mathbin{::}rr)=[\,],\quad \mathrm{tw}_d(p\mathbin{::}rr')=[\,],\quad
        \mathrm{dw}_d(p\mathbin{::}rr)=p\mathbin{::}rr,\quad \mathrm{dw}_d(p\mathbin{::}rr')=p\mathbin{::}rr'.
      ```
      第 1 選言を示す。第 1 成分は $`[\,]=[\,]`$、第 2 成分は仮定
      $`(p\mathbin{::}rr)\prec_{\mathrm{lex}}(p\mathbin{::}rr')`$ そのものである。
  - **$`p\ne q`$ のとき**：[(T.seqlex_cons_cons)](#t-seqlex_cons_cons) より仮定は
    $`p\lt _{\mathrm p}q`$ または $`(p=q \wedge \cdots)`$ であり、後者は $`p\ne q`$ に反する。よって $`p\lt _{\mathrm p}q`$。
    - $`d\lt \pi_0 p`$ のとき：[(D.pairlt)](#d-pairlt) より $`\pi_0 p\lt \pi_0 q`$ か $`\pi_0 p=\pi_0 q`$ であるから、
      いずれにせよ $`\pi_0 p\le\pi_0 q`$、よって $`d\lt \pi_0 p\le\pi_0 q`$ より $`d\lt \pi_0 q`$。
      `List.takeWhile_cons_of_pos` を両側に適用して
      $`\mathrm{tw}_d(p\mathbin{::}rr)=p\mathbin{::}\mathrm{tw}_d rr`$、$`\mathrm{tw}_d(q\mathbin{::}rr')=q\mathbin{::}\mathrm{tw}_d rr'`$。
      第 2 選言を示す。第 1 成分は、$`p\mathbin{::}\mathrm{tw}_d rr = q\mathbin{::}\mathrm{tw}_d rr'`$ とすると
      先頭付加の単射性から $`p=q`$ となり仮定に反する、から従う。
      第 2 成分は [(T.seqlex_cons_cons)](#t-seqlex_cons_cons) の右辺第 1 選言 $`p\lt _{\mathrm p}q`$ による。
    - $`\neg(d\lt \pi_0 p)`$ かつ $`d\lt \pi_0 q`$ のとき：
      $`\mathrm{tw}_d(p\mathbin{::}rr)=[\,]`$、$`\mathrm{tw}_d(q\mathbin{::}rr')=q\mathbin{::}\mathrm{tw}_d rr'`$。
      第 2 選言を示す。第 1 成分は $`[\,]\ne q\mathbin{::}\mathrm{tw}_d rr'`$（空列と先頭付加は異なる）。
      第 2 成分は [(T.seqlex_nil_iff)](#t-seqlex_nil_iff) より $`q\mathbin{::}\mathrm{tw}_d rr'\ne[\,]`$ と同値で、これは真。
    - $`\neg(d\lt \pi_0 p)`$ かつ $`\neg(d\lt \pi_0 q)`$ のとき：
      $`\mathrm{tw}_d(p\mathbin{::}rr)=[\,]`$、$`\mathrm{tw}_d(q\mathbin{::}rr')=[\,]`$、
      $`\mathrm{dw}_d(p\mathbin{::}rr)=p\mathbin{::}rr`$、$`\mathrm{dw}_d(q\mathbin{::}rr')=q\mathbin{::}rr'`$。
      第 1 選言を示す。第 1 成分は $`[\,]=[\,]`$、第 2 成分は仮定
      $`(p\mathbin{::}rr)\prec_{\mathrm{lex}}(q\mathbin{::}rr')`$ そのものである。∎

---

## 順序同型

<a id="t-seqlex_imp_olt"></a>
### 定理 列辞書式順序は翻訳の順序を導く (T.seqlex_imp_olt)

**主張** $`d\in\mathbb{N}`$、ペア列 $`M,N`$ が
$`\mathrm{blockok}(d,M)`$、$`\mathrm{blockok}(d,N)`$、$`M\prec_{\mathrm{lex}}N`$ をみたすならば
```math
\mathrm{tr}\,M \prec \mathrm{tr}\,N.
```

**証明** $`\lvert M\rvert+\lvert N\rvert`$ に関する整礎帰納法。帰納法の仮定は

```math
\mathrm{IH} :\equiv \forall d',M',N',\
 \lvert M'\rvert+\lvert N'\rvert<\lvert M\rvert+\lvert N\rvert \to
 \mathrm{blockok}(d',M') \to \mathrm{blockok}(d',N') \to M'\prec_{\mathrm{lex}}N' \to \mathrm{tr}\,M'\prec\mathrm{tr}\,N'
```

である（$`d`$ も動かすことに注意する。実際、下の引数部の再帰では深さが $`d`$ から $`d+1`$ に変わる）。
$`M,N`$ の形で 4 つに分ける。

- $`M=[\,]`$, $`N=[\,]`$：仮定 $`[\,]\prec_{\mathrm{lex}}[\,]`$ は [(T.seqlex_nil_iff)](#t-seqlex_nil_iff) より $`[\,]\ne[\,]`$ であり偽。
  よって前件が偽で任意の結論が従う。
- $`M=[\,]`$, $`N=q\mathbin{::}N'`$：[(D.translate)](Mechanized.md#d-translate) より $`\mathrm{tr}\,[\,]=\mathsf{Z}`$、
  $`\mathrm{tr}(q\mathbin{::}N')=\mathsf{P}(\pi_1 q,\cdot,\cdot)`$ であるから、
  [(T.olt_Z_P)](Mechanized.md#t-olt_Z_P) より $`\mathrm{tr}\,M\prec\mathrm{tr}\,N`$。
- $`M=p\mathbin{::}r`$, $`N=[\,]`$：[(T.not_seqlex_nil)](#t-not_seqlex_nil) より仮定が偽。
- $`M=p\mathbin{::}r`$, $`N=q\mathbin{::}r'`$：
  $`\mathrm{blockok}(d,M)`$ の先頭条件を $`M=p\mathbin{::}r\ne[\,]`$ に適用すると
  $`\pi_0(\mathrm{headI}\,M)=\pi_0 p=d`$、
  $`\mathrm{blockok}(d,N)`$ の先頭条件を $`N=q\mathbin{::}r'\ne[\,]`$ に適用すると
  $`\pi_0(\mathrm{headI}\,N)=\pi_0 q=d`$。
  よって $`y:=\pi_1 p`$, $`y':=\pi_1 q`$ とおけば $`p=(d,y)`$, $`q=(d,y')`$ である。$`y=y'`$ かどうかで分ける。
  - **$`y=y'`$ のとき**（すなわち $`p=q=(d,y)`$）：
    [(T.seqlex_cons_cons)](#t-seqlex_cons_cons) より仮定は $`(d,y)\lt _{\mathrm p}(d,y)`$ または
    $`((d,y)=(d,y) \wedge r\prec_{\mathrm{lex}}r')`$ である。前者は [(D.pairlt)](#d-pairlt) より
    $`d\lt d`$ または $`(d=d \wedge y\lt y)`$ であり、$`\mathbb{N}`$ の $`\lt `$ の非反射性によりどちらも偽。
    よって $`r\prec_{\mathrm{lex}}r'`$（これを $`sl_r`$ とおく）。
    [(D.translate)](Mechanized.md#d-translate) より
    ```math
    \mathrm{tr}((d,y)\mathbin{::}r) = \mathsf{P}\bigl(y,\ \mathrm{tr}(\mathrm{tw}_d r),\ \mathrm{tr}(\mathrm{dw}_d r)\bigr),\qquad
      \mathrm{tr}((d,y)\mathbin{::}r') = \mathsf{P}\bigl(y,\ \mathrm{tr}(\mathrm{tw}_d r'),\ \mathrm{tr}(\mathrm{dw}_d r')\bigr).
    ```
    [(T.seqlex_arg_or_tail)](#t-seqlex_arg_or_tail) を $`d`$, $`sl_r`$ に適用して 2 つに分ける。
    - **後続部の場合**（第 1 選言）$`\mathrm{tw}_d r=\mathrm{tw}_d r'`$ かつ $`\mathrm{dw}_d r\prec_{\mathrm{lex}}\mathrm{dw}_d r'`$：
      [(T.blockok_tail)](#t-blockok_tail) より $`\mathrm{blockok}(d,\mathrm{dw}_d r)`$、$`\mathrm{blockok}(d,\mathrm{dw}_d r')`$。
      さらに `List.length_dropWhile_le` より
      $`\lvert\mathrm{dw}_d r\rvert\le\lvert r\rvert`$、$`\lvert\mathrm{dw}_d r'\rvert\le\lvert r'\rvert`$ であるから
      ```math
      \lvert\mathrm{dw}_d r\rvert+\lvert\mathrm{dw}_d r'\rvert \le \lvert r\rvert+\lvert r'\rvert
        < (\lvert r\rvert+1)+(\lvert r'\rvert+1) = \lvert M\rvert+\lvert N\rvert
      ```
      であり、$`\mathrm{IH}`$ が $`d':=d`$, $`M':=\mathrm{dw}_d r`$, $`N':=\mathrm{dw}_d r'`$ に適用できて
      $`\mathrm{tr}(\mathrm{dw}_d r)\prec\mathrm{tr}(\mathrm{dw}_d r')`$ を得る。
      [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の右辺第 3 選言（添字は両辺とも $`y`$、
      引数は $`\mathrm{tw}_d r=\mathrm{tw}_d r'`$ より一致）が成り立つので $`\mathrm{tr}\,M\prec\mathrm{tr}\,N`$。
    - **引数部の場合**（第 2 選言）$`\mathrm{tw}_d r\ne\mathrm{tw}_d r'`$ かつ
      $`\mathrm{tw}_d r\prec_{\mathrm{lex}}\mathrm{tw}_d r'`$（以下では後半のみを使う）：
      [(T.blockok_arg)](#t-blockok_arg) より $`\mathrm{blockok}(d+1,\mathrm{tw}_d r)`$、$`\mathrm{blockok}(d+1,\mathrm{tw}_d r')`$。
      `List.takeWhile_sublist` より $`\lvert\mathrm{tw}_d r\rvert\le\lvert r\rvert`$、$`\lvert\mathrm{tw}_d r'\rvert\le\lvert r'\rvert`$ であるから
      ```math
      \lvert\mathrm{tw}_d r\rvert+\lvert\mathrm{tw}_d r'\rvert \le \lvert r\rvert+\lvert r'\rvert
        < \lvert M\rvert+\lvert N\rvert
      ```
      であり、$`\mathrm{IH}`$ が $`d':=d+1`$, $`M':=\mathrm{tw}_d r`$, $`N':=\mathrm{tw}_d r'`$ に適用できて
      $`\mathrm{tr}(\mathrm{tw}_d r)\prec\mathrm{tr}(\mathrm{tw}_d r')`$ を得る。
      [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の右辺第 2 選言（添字は両辺とも $`y`$）が成り立つので
      $`\mathrm{tr}\,M\prec\mathrm{tr}\,N`$。
  - **$`y\ne y'`$ のとき**：[(T.seqlex_cons_cons)](#t-seqlex_cons_cons) より仮定は
    $`(d,y)\lt _{\mathrm p}(d,y')`$ または $`(d,y)=(d,y')`$ である。
    後者は第 2 成分を比べて $`y=y'`$ を与え、仮定に反する。よって前者であり、
    [(D.pairlt)](#d-pairlt) より $`d\lt d`$（$`\mathbb{N}`$ の $`\lt `$ の非反射性により偽）または
    $`(d=d \wedge y\lt y')`$ であるから $`y\lt y'`$。
    [(D.translate)](Mechanized.md#d-translate) より
    $`\mathrm{tr}\,M = \mathsf{P}(y,\cdot,\cdot)`$、$`\mathrm{tr}\,N = \mathsf{P}(y',\cdot,\cdot)`$ であり、
    [(T.olt_P_P)](Mechanized.md#t-olt_P_P) の右辺第 1 選言 $`y\lt y'`$ が成り立つので $`\mathrm{tr}\,M\prec\mathrm{tr}\,N`$。∎

<a id="t-seqlex_total"></a>
### 定理 列辞書式順序の三分律 (T.seqlex_total)

**主張** 任意のペア列 $`M,N`$ に対し
```math
M=N \ \vee\ M\prec_{\mathrm{lex}}N \ \vee\ N\prec_{\mathrm{lex}}M.
```

**証明** $`N`$ を全称量化したまま動かし、$`M`$ の構造に関する帰納法。帰納法の述語は
```math
\Psi(M) :\equiv \forall N,\ M=N \vee M\prec_{\mathrm{lex}}N \vee N\prec_{\mathrm{lex}}M.
```

- 基底段 $`M=[\,]`$：$`N=[\,]`$ なら第 1 選言 $`M=N`$。
  $`N=q\mathbin{::}N'`$ なら [(T.seqlex_nil_iff)](#t-seqlex_nil_iff) より
  $`[\,]\prec_{\mathrm{lex}}(q\mathbin{::}N')`$ は $`q\mathbin{::}N'\ne[\,]`$ と同値で真、よって第 2 選言。
- 帰納段 $`M=p\mathbin{::}M_1`$：帰納法の仮定は $`\Psi(M_1)`$ である。
  - $`N=[\,]`$：[(T.seqlex_nil_iff)](#t-seqlex_nil_iff) より $`[\,]\prec_{\mathrm{lex}}(p\mathbin{::}M_1)`$ は
    $`p\mathbin{::}M_1\ne[\,]`$ と同値で真、よって第 3 選言。
  - $`N=q\mathbin{::}N'`$：$`p=q`$ かどうかで分ける。
    - $`p=q`$：帰納法の仮定 $`\Psi(M_1)`$ を $`N'`$ に適用して 3 つに分ける。
      - $`M_1=N'`$：$`p\mathbin{::}M_1 = p\mathbin{::}N' = N`$ で第 1 選言。
      - $`M_1\prec_{\mathrm{lex}}N'`$：[(T.seqlex_cons_cons)](#t-seqlex_cons_cons) の右辺第 2 選言
        $`p=p \wedge M_1\prec_{\mathrm{lex}}N'`$ より $`M\prec_{\mathrm{lex}}N`$、第 2 選言。
      - $`N'\prec_{\mathrm{lex}}M_1`$：[(T.seqlex_cons_cons)](#t-seqlex_cons_cons) の右辺第 2 選言
        $`q=q \wedge N'\prec_{\mathrm{lex}}M_1`$（$`p=q`$ より $`M=q\mathbin{::}M_1`$）より
        $`N\prec_{\mathrm{lex}}M`$、第 3 選言。
    - $`p\ne q`$：まず $`p\lt _{\mathrm p}q \vee q\lt _{\mathrm p}p`$ を示す。
      $`\mathbb{N}`$ の三分律で $`\pi_0 p`$ と $`\pi_0 q`$ を比べる。
      - $`\pi_0 p\lt \pi_0 q`$：[(D.pairlt)](#d-pairlt) の第 1 選言より $`p\lt _{\mathrm p}q`$。
      - $`\pi_0 p=\pi_0 q`$：$`\mathbb{N}`$ の三分律で $`\pi_1 p`$ と $`\pi_1 q`$ を比べる。
        - $`\pi_1 p\lt \pi_1 q`$：[(D.pairlt)](#d-pairlt) の第 2 選言より $`p\lt _{\mathrm p}q`$。
        - $`\pi_1 p=\pi_1 q`$：両成分が等しいから対として $`p=q`$ となり、仮定 $`p\ne q`$ に反する。
        - $`\pi_1 q\lt \pi_1 p`$：$`\pi_0 q=\pi_0 p`$ とあわせて [(D.pairlt)](#d-pairlt) の第 2 選言より $`q\lt _{\mathrm p}p`$。
      - $`\pi_0 q\lt \pi_0 p`$：[(D.pairlt)](#d-pairlt) の第 1 選言より $`q\lt _{\mathrm p}p`$。

      $`p\lt _{\mathrm p}q`$ の場合は [(T.seqlex_cons_cons)](#t-seqlex_cons_cons) の右辺第 1 選言より
      $`(p\mathbin{::}M_1)\prec_{\mathrm{lex}}(q\mathbin{::}N')`$、すなわち $`M\prec_{\mathrm{lex}}N`$（第 2 選言）。
      $`q\lt _{\mathrm p}p`$ の場合は [(T.seqlex_cons_cons)](#t-seqlex_cons_cons) の右辺第 1 選言より
      $`(q\mathbin{::}N')\prec_{\mathrm{lex}}(p\mathbin{::}M_1)`$、すなわち $`N\prec_{\mathrm{lex}}M`$（第 3 選言）。∎

<a id="t-olt_iff_seqlex"></a>
### 定理 ブロック上の順序同型 (T.olt_iff_seqlex)

**主張** $`\mathrm{blockok}(d,M)`$、$`\mathrm{blockok}(d,N)`$、$`M\ne N`$ ならば
```math
\mathrm{tr}\,M\prec\mathrm{tr}\,N \iff M\prec_{\mathrm{lex}}N.
```

**証明** 両方向を示す。

- ($`\Leftarrow`$) [(T.seqlex_imp_olt)](#t-seqlex_imp_olt) そのものである。
- ($`\Rightarrow`$) $`\mathrm{tr}\,M\prec\mathrm{tr}\,N`$ を仮定し、背理法で $`\neg(M\prec_{\mathrm{lex}}N)`$ と仮定する。
  [(T.seqlex_total)](#t-seqlex_total) より $`M=N`$、$`M\prec_{\mathrm{lex}}N`$、$`N\prec_{\mathrm{lex}}M`$ のいずれかが成り立つが、
  第 1 は $`M\ne N`$ に、第 2 は背理法の仮定に反するから $`N\prec_{\mathrm{lex}}M`$ である。
  [(T.seqlex_imp_olt)](#t-seqlex_imp_olt) を $`d`$, $`N`$, $`M`$ に適用して $`\mathrm{tr}\,N\prec\mathrm{tr}\,M`$ を得る。
  [(T.olt_trans)](Mechanized.md#t-olt_trans) より $`\mathrm{tr}\,M\prec\mathrm{tr}\,M`$ となり、
  [(T.olt_irrefl)](Mechanized.md#t-olt_irrefl) に矛盾する。∎

---

## ブロックの扇に沿う隣接段の合成

この節では、ブロックを連結したときに増分条件が保たれるための道具を用意する。
まず末尾要素についての補助補題を 4 つ示す。

<a id="t-getLastD_eq_getD"></a>
### 定理 末尾要素は添字 $`\lvert l\rvert-1`$ の要素 (T.getLastD_eq_getD)

**主張** 任意の型 $`\alpha`$、リスト $`l : \mathrm{List}\,\alpha`$、既定値 $`d:\alpha`$ に対し
```math
\mathrm{lastD}(l,d) = \mathrm{getD}(l,\ \lvert l\rvert-1,\ d)
```
（$`\lvert l\rvert-1`$ は切り捨て減法。$`l=[\,]`$ のときは $`0-1=0`$）。

**証明** 両辺をともに $`\bigl(l[\lvert l\rvert-1]?\bigr).\mathrm{getD}\,d`$ に等しいことを示す。
左辺は `List.getLastD_eq_getLast?` より $`(l.\mathrm{getLast?}).\mathrm{getD}\,d`$ であり、
`List.getLast?_eq_getElem?` より $`l.\mathrm{getLast?} = l[\lvert l\rvert-1]?`$ である。
右辺は `List.getD_eq_getElem?_getD` よりそのまま $`\bigl(l[\lvert l\rvert-1]?\bigr).\mathrm{getD}\,d`$ である。∎

<a id="t-getLastD_ne_nil_indep"></a>
### 定理 空でなければ既定値によらない (T.getLastD_ne_nil_indep)

**主張** $`B\ne[\,]`$ ならば、任意の既定値 $`d,d'`$ に対し $`\mathrm{lastD}(B,d)=\mathrm{lastD}(B,d')`$。

**証明** $`B`$ の形で場合分けする。$`B=[\,]`$ は仮定に反する。
$`B=b\mathbin{::}bs`$ のとき、`List.getLastD_cons` より
$`\mathrm{lastD}(b\mathbin{::}bs,\ d) = \mathrm{lastD}(bs,\ b)`$ かつ
$`\mathrm{lastD}(b\mathbin{::}bs,\ d') = \mathrm{lastD}(bs,\ b)`$ であり、両辺は同一の項である。∎

<a id="t-headI_append_left"></a>
### 定理 連結の先頭は左片の先頭 (T.headI_append_left)

**主張** $`A\ne[\,]`$ ならば $`\mathrm{headI}(A\mathbin{+\!\!+}B) = \mathrm{headI}\,A`$。

**証明** $`A`$ の形で場合分けする。$`A=[\,]`$ は仮定に反する。
$`A=a\mathbin{::}as`$ のとき $`(a\mathbin{::}as)\mathbin{+\!\!+}B = a\mathbin{::}(as\mathbin{+\!\!+}B)`$ であり、
両辺の $`\mathrm{headI}`$ はともに $`a`$ である。∎

<a id="t-getLastD_append_right"></a>
### 定理 連結の末尾は右片の末尾 (T.getLastD_append_right)

**主張** $`B\ne[\,]`$ ならば、任意の既定値 $`d`$ に対し $`\mathrm{lastD}(A\mathbin{+\!\!+}B,\ d) = \mathrm{lastD}(B,\ d)`$。

**証明** $`B`$ とその仮定 $`B\ne[\,]`$ を固定し、$`d`$ を全称量化したまま動かして $`A`$ の構造に関する帰納法。
帰納法の述語は
```math
\Phi(A) :\equiv \forall d,\ \mathrm{lastD}(A\mathbin{+\!\!+}B,\ d) = \mathrm{lastD}(B,\ d).
```

- 基底段 $`A=[\,]`$：$`[\,]\mathbin{+\!\!+}B=B`$ であるから両辺は同一の項である。
- 帰納段 $`A=a\mathbin{::}A'`$：帰納法の仮定は $`\Phi(A')`$ である。$`d`$ を取る。
  $`(a\mathbin{::}A')\mathbin{+\!\!+}B = a\mathbin{::}(A'\mathbin{+\!\!+}B)`$ であるから、`List.getLastD_cons` より
  ```math
  \mathrm{lastD}(A\mathbin{+\!\!+}B,\ d) = \mathrm{lastD}(A'\mathbin{+\!\!+}B,\ a).
  ```
  $`\Phi(A')`$ を既定値 $`a`$ に適用して $`\mathrm{lastD}(A'\mathbin{+\!\!+}B,\ a) = \mathrm{lastD}(B,\ a)`$。
  最後に $`B\ne[\,]`$ と [(T.getLastD_ne_nil_indep)](#t-getLastD_ne_nil_indep) より
  $`\mathrm{lastD}(B,\ a)=\mathrm{lastD}(B,\ d)`$。∎

<a id="t-steps1_flatMap"></a>
### 定理 ブロックの扇の連結 (T.steps1_flatMap)

**主張** ブロックの族 $`F:\mathbb{N}\to\mathrm{PairSeq}`$ と $`n\in\mathbb{N}`$ が

1. $`\forall k\lt n,\ \mathrm{steps}_1(F_k)`$
2. $`\forall k\lt n,\ F_k\ne[\,]`$
3. $`\forall k,\ k+1\lt n \to \pi_0(\mathrm{headI}\,F_{k+1}) \le \pi_0(\mathrm{lastD}(F_k,(0,0)))+1`$

をみたすとする。$`C_n := \mathrm{flatMap}\,F\,\mathrm{range}(n)`$ とおくと

```math
\mathrm{steps}_1(C_n)
\quad\wedge\quad
\Bigl(0<n \to C_n\ne[\,] \ \wedge\ \mathrm{headI}\,C_n = \mathrm{headI}\,F_0 \ \wedge\
 \mathrm{lastD}(C_n,(0,0)) = \mathrm{lastD}(F_{n-1},(0,0))\Bigr).
```

**証明** $`n`$ に関する自然数の帰納法。仮定 1–3 は $`n`$ に依存するので、帰納法の述語は仮定込みで

```math
\begin{aligned}
\Phi(m) :\equiv\ &\bigl(\forall k<m,\ \mathrm{steps}_1(F_k)\bigr)
 \to \bigl(\forall k<m,\ F_k\ne[\,]\bigr)\cr
 &\to \bigl(\forall k,\ k+1<m \to \pi_0(\mathrm{headI}\,F_{k+1})\le\pi_0(\mathrm{lastD}(F_k,(0,0)))+1\bigr)\cr
 &\to\ \mathrm{steps}_1(C_m) \wedge \bigl(0<m \to C_m\ne[\,] \wedge \mathrm{headI}\,C_m=\mathrm{headI}\,F_0
 \wedge \mathrm{lastD}(C_m,(0,0))=\mathrm{lastD}(F_{m-1},(0,0))\bigr)
\end{aligned}
```

とする（$`F`$ は固定）。

- **基底段 $`m=0`$**：$`\mathrm{range}(0)=[\,]`$ より $`C_0=[\,]`$。
  [(T.steps1_nil)](#t-steps1_nil) より第 1 成分が成り立ち、第 2 成分は前件 $`0\lt 0`$ が偽だから空虚に成り立つ。
- **帰納段 $`m+1`$**：帰納法の仮定は $`\Phi(m)`$ である。まず分解式
  ```math
  (\ast)\qquad C_{m+1} = C_m \mathbin{+\!\!+} F_m
  ```
  を得る。実際 `List.range_succ` より $`\mathrm{range}(m+1)=\mathrm{range}(m)\mathbin{+\!\!+}[m]`$ であり、
  `List.flatMap_append` より
  $`C_{m+1} = C_m \mathbin{+\!\!+} \mathrm{flatMap}\,F\,[m] = C_m\mathbin{+\!\!+}(F_m\mathbin{+\!\!+}[\,]) = C_m\mathbin{+\!\!+}F_m`$。
  $`m=0`$ かどうかで分ける。
  - **$`m=0`$ のとき**：$`C_1 = C_0\mathbin{+\!\!+}F_0 = [\,]\mathbin{+\!\!+}F_0 = F_0`$。
    第 1 成分は仮定 1 を $`k:=0\lt 1`$ に適用して $`\mathrm{steps}_1(F_0)`$。
    第 2 成分は、$`C_1\ne[\,]`$ が仮定 2 を $`k:=0\lt 1`$ に適用して得られ、
    $`\mathrm{headI}\,C_1=\mathrm{headI}\,F_0`$ と $`\mathrm{lastD}(C_1,(0,0))=\mathrm{lastD}(F_{1-1},(0,0))=\mathrm{lastD}(F_0,(0,0))`$ は
    $`C_1=F_0`$ と $`1-1=0`$ から同一の項である。
  - **$`m\ne0`$（すなわち $`1\le m`$）のとき**：
    $`k\lt m`$ ならば $`k\lt m+1`$、また $`k+1\lt m`$ ならば $`k+1\lt m+1`$ であるから、
    仮定 1–3 は $`m`$ に対する仮定 1–3 を含意する。$`\Phi(m)`$ を適用して
    $`h_{\mathrm{s}} : \mathrm{steps}_1(C_m)`$ と第 2 成分を得、$`0\lt m`$ より
    ```math
    c_{\ne} : C_m\ne[\,],\qquad c_{\mathrm{hd}} : \mathrm{headI}\,C_m=\mathrm{headI}\,F_0,\qquad
      c_{\mathrm{last}} : \mathrm{lastD}(C_m,(0,0))=\mathrm{lastD}(F_{m-1},(0,0))
    ```
    を得る。次に**継ぎ目**の評価
    ```math
    \pi_0(\mathrm{headI}\,F_m) \le \pi_0(\mathrm{lastD}(C_m,(0,0)))+1
    ```
    を示す。$`c_{\mathrm{last}}`$ により右辺は $`\pi_0(\mathrm{lastD}(F_{m-1},(0,0)))+1`$ に等しい。
    仮定 3 を $`k:=m-1`$ に適用する。前件は $`(m-1)+1\lt m+1`$ であり、$`1\le m`$ より $`(m-1)+1=m`$ だから $`m\lt m+1`$ で成立する。
    結論は $`\pi_0(\mathrm{headI}\,F_{(m-1)+1})\le\pi_0(\mathrm{lastD}(F_{m-1},(0,0)))+1`$ であり、
    $`(m-1)+1=m`$ よりこれが求める評価である。
    また仮定 2 を $`k:=m\lt m+1`$ に適用して $`F_m\ne[\,]`$ を得る。以上から 4 つの結論を示す。
    - $`\mathrm{steps}_1(C_{m+1})`$：$`(\ast)`$ と [(T.steps1_append)](#t-steps1_append) の $`(\Leftarrow)`$ 方向による。
      第 1 成分は $`h_{\mathrm{s}}`$、第 2 成分は仮定 1 を $`k:=m\lt m+1`$ に適用した $`\mathrm{steps}_1(F_m)`$、
      第 3 成分は継ぎ目の評価（第 3 選言）である。
    - $`C_{m+1}\ne[\,]`$：$`(\ast)`$ より $`C_{m+1}=[\,]`$ とすると `List.append_eq_nil_iff` から $`C_m=[\,]`$ となり
      $`c_{\ne}`$ に反する。
    - $`\mathrm{headI}\,C_{m+1}=\mathrm{headI}\,F_0`$：$`(\ast)`$ と
      [(T.headI_append_left)](#t-headI_append_left)（$`c_{\ne}`$ を用いる）より
      $`\mathrm{headI}\,C_{m+1}=\mathrm{headI}\,C_m`$、これに $`c_{\mathrm{hd}}`$ を適用する。
    - $`\mathrm{lastD}(C_{m+1},(0,0))=\mathrm{lastD}(F_{(m+1)-1},(0,0))`$：$`(\ast)`$ と
      [(T.getLastD_append_right)](#t-getLastD_append_right)（$`F_m\ne[\,]`$ を用いる）より
      $`\mathrm{lastD}(C_{m+1},(0,0))=\mathrm{lastD}(F_m,(0,0))`$ であり、$`(m+1)-1=m`$ である。∎

---

## 標準形はブロック規律をみたす

<a id="t-steps1_diag_range"></a>
### 定理 対角ブロックの増分条件 (T.steps1_diag_range)

**主張** 任意の $`m,s\in\mathbb{N}`$ に対し
```math
\mathrm{steps}_1\bigl(\mathrm{map}\,(\lambda j.\ (j,j))\ \mathrm{range}'(s,m)\bigr).
```

**証明** $`s`$ を全称量化したまま動かし、$`m`$ に関する自然数の帰納法。帰納法の述語は
```math
\Phi(m) :\equiv \forall s,\ \mathrm{steps}_1\bigl(\mathrm{map}\,(\lambda j.\ (j,j))\ \mathrm{range}'(s,m)\bigr).
```

- 基底段 $`m=0`$：$`\mathrm{range}'(s,0)=[\,]`$ より対象は空列であり、[(T.steps1_nil)](#t-steps1_nil) による。
- 帰納段 $`m+1`$：帰納法の仮定は $`\Phi(m)`$ である。$`s`$ を取る。
  `List.range'_succ` より $`\mathrm{range}'(s,m+1) = s\mathbin{::}\mathrm{range}'(s+1,m)`$ であるから、
  ```math
  \mathrm{map}\,(\lambda j.\ (j,j))\ \mathrm{range}'(s,m+1)
   = (s,s)\mathbin{::}\mathrm{map}\,(\lambda j.\ (j,j))\ \mathrm{range}'(s+1,m).
  ```
  $`m`$ の形でさらに分ける。
  - $`m=0`$：$`\mathrm{range}'(s+1,0)=[\,]`$ より対象は $`[(s,s)]`$ であり、[(T.steps1_single)](#t-steps1_single) による。
  - $`m=m'+1`$：再び `List.range'_succ` より
    $`\mathrm{range}'(s+1,m'+1) = (s+1)\mathbin{::}\mathrm{range}'(s+2,m')`$ であるから、対象は
    ```math
    (s,s)\mathbin{::}(s+1,s+1)\mathbin{::}\mathrm{map}\,(\lambda j.\ (j,j))\ \mathrm{range}'(s+2,m')
    ```
    である。[(T.steps1_cons_cons)](#t-steps1_cons_cons) より示すべきは
    $`\pi_0(s+1,s+1)\le\pi_0(s,s)+1`$、すなわち $`s+1\le s+1`$（$`\le`$ の反射性）と、
    ```math
    \mathrm{steps}_1\bigl((s+1,s+1)\mathbin{::}\mathrm{map}\,(\lambda j.\ (j,j))\ \mathrm{range}'(s+2,m')\bigr)
    ```
    である。後者は、帰納法の仮定 $`\Phi(m)`$ を $`s:=s+1`$ に適用して得られる
    $`\mathrm{steps}_1\bigl(\mathrm{map}\,(\lambda j.\ (j,j))\ \mathrm{range}'(s+1,m'+1)\bigr)`$ を
    `List.range'_succ` で書き換えたものにほかならない。∎

<a id="t-blockok_diagSeq"></a>
### 定理 対角列は深さ 0 のブロック (T.blockok_diagSeq)

**主張** 任意の $`v\in\mathbb{N}`$ に対し $`\mathrm{blockok}\bigl(0,\ \Delta_0^v\bigr)`$
（[(D.diagSeq)](Def.md#d-diagSeq)）。

**証明** [(D.blockok)](#d-blockok) の 3 成分を確かめる。

- 先頭条件：$`0\le v`$ であるから [(T.diagSeq_cons)](Wf.md#t-diagSeq_cons) より
  $`\Delta_0^v = (0,0)\mathbin{::}\Delta_1^v`$。よって $`\mathrm{headI}\,\Delta_0^v = (0,0)`$ であり
  $`\pi_0(0,0)=0`$。
- 下界条件：任意の対 $`p`$ について $`0\le\pi_0 p`$ は $`\mathbb{N}`$ の最小元性から成り立つ。
- 増分条件：[(D.diagSeq)](Def.md#d-diagSeq) より
  $`\Delta_0^v = \mathrm{map}\,(\lambda j.\ (j,j))\ \mathrm{range}'(0,\ v+1-0)`$ であるから、
  [(T.steps1_diag_range)](#t-steps1_diag_range) を $`m:=v+1-0`$, $`s:=0`$ に適用すればよい。∎

<a id="t-blockok_oper"></a>
### 定理 展開はブロック条件を保つ (T.blockok_oper)

**主張** $`\mathrm{blockok}(0,M)`$ かつ $`1\le n`$ ならば $`\mathrm{blockok}\bigl(0,\ M[n]\bigr)`$
（[(D.oper)](Def.md#d-oper)）。

**証明** 仮定 $`\mathrm{blockok}(0,M)`$ を $`b`$ とおく。$`\lvert M\rvert-1=0`$ かどうかで分ける。

**(I) $`\lvert M\rvert-1=0`$ のとき**：[(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) より
$`M[n]=M`$ であるから、$`b`$ そのものが結論である。

**(II) $`\lvert M\rvert-1\ne0`$ のとき**：このとき $`1\lt \lvert M\rvert`$ である（$`\lvert M\rvert\le1`$ なら切り捨て減法で $`\lvert M\rvert-1=0`$）。
とくに $`M\ne[\,]`$。また $`\lvert M\rvert\le1`$ が偽だから [(D.Pred)](Def.md#d-Pred) より
$`\mathrm{Pred}\,M=\mathrm{dropLast}\,M`$。以下 $`j_1:=\lvert M\rvert-1`$、$`i_1:=\mathrm{idx}_1(M,j_1)`$
（[(D.idx1)](Def.md#d-idx1)）と書く。3 つの場合に分ける。

- **(II-a) $`M_{0,j_1}=0 \wedge M_{1,j_1}=0`$ のとき**：
  [(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero) より
  $`M[n]=\mathrm{Pred}\,M=\mathrm{dropLast}\,M`$ であり、
  [(T.blockok_dropLast)](#t-blockok_dropLast) を $`b`$ に適用すればよい。
- **(II-b) $`\neg(M_{0,j_1}=0 \wedge M_{1,j_1}=0)`$ かつ $`\neg\,\mathrm{hasParent}(M,i_1,j_1)`$ のとき**
  （[(D.hasParent)](Def.md#d-hasParent)）：
  [(T.oper_eq_pred_of_noParent)](Mechanized.md#t-oper_eq_pred_of_noParent) より
  $`M[n]=\mathrm{Pred}\,M=\mathrm{dropLast}\,M`$ であり、
  [(T.blockok_dropLast)](#t-blockok_dropLast) を $`b`$ に適用すればよい。
- **(II-c) $`\neg(M_{0,j_1}=0 \wedge M_{1,j_1}=0)`$ かつ $`\mathrm{hasParent}(M,i_1,j_1)`$ のとき**：
  これが本補題の主要部である。$`j_0:=\mathrm{par}^M_{i_1}(j_1)`$（[(D.parent)](Def.md#d-parent)）とおく。
  [(T.parent_nextR)](Mechanized.md#t-parent_nextR) より $`j_0\to^M_{i_1}j_1`$（[(D.nextR)](Def.md#d-nextR)）、
  よって [(T.nextR_index_lt)](Mechanized.md#t-nextR_index_lt) より $`j_0\lt j_1`$ である。さらに
  ```math
  D := \begin{cases} M_{0,j_1}-M_{0,j_0} & (0<i_1)\cr 0 & (i_1=0)\end{cases}
  ```
  とおく。

  **(1) $`M`$ の行 0 の隣接段.** $`b`$ の増分条件 $`\mathrm{steps}_1(M)`$ に
  [(T.steps1_iff)](#t-steps1_iff) の $`(\Rightarrow)`$ 方向を適用して
  ```math
  (\mathrm{e}0)\qquad \forall j,\ j+1<\lvert M\rvert \to M_{0,j+1}\le M_{0,j}+1
  ```
  を得る（[(D.entry)](Def.md#d-entry) より $`M_{0,j}=\pi_0(M\langle j\rangle)`$）。

  **(2) 継ぎ目の評価** $`M_{0,j_0}+D \le M_{0,j_1-1}+1`$。
  まず $`1\lt \lvert M\rvert`$ より $`j_1=\lvert M\rvert-1\lt \lvert M\rvert`$、また $`j_0\lt j_1`$ より $`1\le j_1`$ である。
  よって $`(j_1-1)+1=j_1\lt \lvert M\rvert`$ であり、
  $`(\mathrm{e}0)`$ を $`j:=j_1-1`$ に適用して
  ```math
  (\mathrm{e}0')\qquad M_{0,j_1}\le M_{0,j_1-1}+1.
  ```
  $`0\lt i_1`$ かどうかで分ける。
  - $`0\lt i_1`$ のとき：$`i_1\ne0`$ だから [(D.nextR)](Def.md#d-nextR) より $`j_0\to^M_{i_1}j_1`$ は
    $`j_0\to^M_1 j_1`$（[(D.nextrel1)](Def.md#d-nextrel1)）である。その第 5 成分は $`j_0\le^M_0 j_1`$
    （[(D.le0)](Def.md#d-le0)）であるから、[(T.le0_entry0_mono)](Mechanized.md#t-le0_entry0_mono) より
    $`M_{0,j_0}\le M_{0,j_1}`$。このとき $`D=M_{0,j_1}-M_{0,j_0}`$ であり、切り捨て減法は
    $`M_{0,j_0}\le M_{0,j_1}`$ の下で
    $`M_{0,j_0}+D = M_{0,j_0}+(M_{0,j_1}-M_{0,j_0}) = M_{0,j_1}`$ を与える。
    $`(\mathrm{e}0')`$ とあわせて $`M_{0,j_0}+D\le M_{0,j_1-1}+1`$。
  - $`i_1=0`$ のとき：[(D.nextR)](Def.md#d-nextR) より $`j_0\to^M_0 j_1`$（[(D.nextrel0)](Def.md#d-nextrel0)）であり、
    [(T.nextrel0_entry0_less)](Mechanized.md#t-nextrel0_entry0_less) より $`M_{0,j_0}\lt M_{0,j_1}`$。
    このとき $`D=0`$ だから $`M_{0,j_0}+D = M_{0,j_0} \lt M_{0,j_1} \le M_{0,j_1-1}+1`$。

  **(3) 展開形.** [(T.oper_bad_unfold)](Mechanized.md#t-oper_bad_unfold) より
  ```math
  M[n] = \mathrm{take}\,j_0\,M \mathbin{+\!\!+} C_n,\qquad
    C_n := \mathrm{flatMap}\,F\,\mathrm{range}(n),\qquad
    F_k := \mathrm{map}\bigl(\lambda j.\ (M_{0,j}+kD,\ M_{1,j})\bigr)\ \mathrm{range}'(j_0,\ j_1-j_0).
  ```

  **(4) 各ブロック $`F_k`$ の性質.** $`j_0\lt j_1`$ より $`j_1-j_0\ge1`$ であるから、`List.range'_succ` により
  ```math
  (\mathrm{sp})\qquad \mathrm{range}'(j_0,\ j_1-j_0) = j_0\mathbin{::}\mathrm{range}'(j_0+1,\ j_1-j_0-1).
  ```
  $`(\mathrm{sp})`$ に $`\mathrm{map}`$ を分配すると
  ```math
  F_k = (M_{0,j_0}+kD,\ M_{1,j_0})\mathbin{::}\mathrm{map}\bigl(\lambda j.\ (M_{0,j}+kD,\ M_{1,j})\bigr)\ \mathrm{range}'(j_0+1,\ j_1-j_0-1)
  ```
  であるから、次が従う。
  - $`F_k\ne[\,]`$：右辺は先頭付加の形であり、空列ではない。
  - $`\mathrm{headI}\,F_k = (M_{0,j_0}+kD,\ M_{1,j_0})`$：右辺の先頭要素である。
  - $`\lvert F_k\rvert = j_1-j_0`$：$`\mathrm{map}`$ は長さを変えず、$`\lvert\mathrm{range}'(j_0,j_1-j_0)\rvert = j_1-j_0`$。
  - $`j\lt j_1-j_0`$ のとき $`F_k\langle j\rangle = (M_{0,j_0+j}+kD,\ M_{1,j_0+j})`$：
    [(T.getD_eq_getElem')](Wf.md#t-getD_eq_getElem') で $`\mathrm{getD}`$ を $`[\,\cdot\,]`$ に直し、
    `List.getElem_map` と `List.getElem_range'`（$`\mathrm{range}'(j_0,m)[j]=j_0+j`$）による。
  - $`\mathrm{lastD}(F_k,(0,0)) = (M_{0,j_1-1}+kD,\ M_{1,j_1-1})`$：
    [(T.getLastD_eq_getD)](#t-getLastD_eq_getD) より
    $`\mathrm{lastD}(F_k,(0,0)) = F_k\langle \lvert F_k\rvert-1\rangle = F_k\langle j_1-j_0-1\rangle`$
    であり、$`j_1-j_0-1\lt j_1-j_0`$ だから直前の等式が使えて
    $`(M_{0,j_0+(j_1-j_0-1)}+kD,\ M_{1,j_0+(j_1-j_0-1)})`$、
    ここで $`j_0\lt j_1`$ より $`j_0+(j_1-j_0-1)=j_1-1`$。
  - $`\mathrm{steps}_1(F_k)`$：[(T.steps1_iff)](#t-steps1_iff) の $`(\Leftarrow)`$ 方向を使う。
    $`j+1\lt \lvert F_k\rvert = j_1-j_0`$ なる $`j`$ を取る。上の等式より
    $`\pi_0(F_k\langle j+1\rangle) = M_{0,j_0+(j+1)}+kD`$、$`\pi_0(F_k\langle j\rangle) = M_{0,j_0+j}+kD`$ である。
    $`j_0+j+1 \lt j_0+(j_1-j_0) = j_1 \lt \lvert M\rvert`$ であるから $`(\mathrm{e}0)`$ を $`j:=j_0+j`$ に適用でき、
    $`M_{0,j_0+(j+1)}\le M_{0,j_0+j}+1`$。両辺に $`kD`$ を加えて求める不等式を得る。
  - $`k+1\lt n`$ のとき $`\pi_0(\mathrm{headI}\,F_{k+1}) \le \pi_0(\mathrm{lastD}(F_k,(0,0)))+1`$：
    左辺は $`M_{0,j_0}+(k+1)D`$、右辺は $`M_{0,j_1-1}+kD+1`$ である。
    $`(k+1)D = kD+D`$ であるから、示すべきは $`M_{0,j_0}+D+kD \le M_{0,j_1-1}+1+kD`$、
    すなわち (2) の継ぎ目の評価に $`kD`$ を加えたものである。

  **(5) 連結部 $`C_n`$.** (4) で示した $`\mathrm{steps}_1(F_k)`$、$`F_k\ne[\,]`$ はすべての $`k`$ について、
  継ぎ目の評価は $`k+1\lt n`$ なるすべての $`k`$ について成り立つので、
  [(T.steps1_flatMap)](#t-steps1_flatMap) の仮定 1–3 がみたされる。これを適用して
  $`\mathrm{steps}_1(C_n)`$ を得る。また $`1\le n`$ より $`0\lt n`$ であるから、
  $`C_n\ne[\,]`$ と $`\mathrm{headI}\,C_n=\mathrm{headI}\,F_0`$ も得る。
  $`\mathrm{headI}\,F_0 = (M_{0,j_0}+0\cdot D,\ M_{1,j_0}) = (M_{0,j_0},\ M_{1,j_0})`$ だから
  ```math
  (\mathrm{hd})\qquad \mathrm{headI}\,C_n = (M_{0,j_0},\ M_{1,j_0}).
  ```

  **(6) 前部 $`\mathrm{take}\,j_0\,M`$ の増分条件.**
  [(T.steps1_iff)](#t-steps1_iff) の $`(\Leftarrow)`$ 方向を使う。
  $`j+1\lt \lvert\mathrm{take}\,j_0\,M\rvert`$ なる $`j`$ を取る。`List.length_take` より
  $`\lvert\mathrm{take}\,j_0\,M\rvert=\min(j_0,\lvert M\rvert)`$ であるから、$`j+1\lt \lvert M\rvert`$ かつ $`j+1\lt j_0`$、
  とくに $`j\lt j_0`$ かつ $`j\lt \lvert M\rvert`$ である。
  よって [(T.getD_eq_getElem')](Wf.md#t-getD_eq_getElem') で両辺の $`\mathrm{getD}`$ を $`[\,\cdot\,]`$ に直したうえで
  `List.getElem_take` を用いると
  $`(\mathrm{take}\,j_0\,M)\langle j\rangle = M\langle j\rangle`$、
  $`(\mathrm{take}\,j_0\,M)\langle j+1\rangle = M\langle j+1\rangle`$ であり、
  求める不等式は $`(\mathrm{e}0)`$ を $`j`$ に適用したものに一致する。

  **(7) 前部と連結部の継ぎ目.** 次を示す。
  ```math
  \mathrm{take}\,j_0\,M=[\,] \ \vee\ C_n=[\,] \ \vee\
    \pi_0(\mathrm{headI}\,C_n)\le\pi_0(\mathrm{lastD}(\mathrm{take}\,j_0\,M,(0,0)))+1.
  ```
  - $`j_0=0`$ のとき：$`\mathrm{take}\,0\,M=[\,]`$ より第 1 選言。
  - $`j_0\ne0`$ のとき：第 3 選言を示す。$`j_0\lt j_1\lt \lvert M\rvert`$ より
    $`\lvert\mathrm{take}\,j_0\,M\rvert = \min(j_0,\lvert M\rvert) = j_0`$ であるから、
    [(T.getLastD_eq_getD)](#t-getLastD_eq_getD) より
    $`\mathrm{lastD}(\mathrm{take}\,j_0\,M,(0,0)) = (\mathrm{take}\,j_0\,M)\langle j_0-1\rangle`$ であり、
    $`j_0-1\lt j_0`$ かつ $`j_0-1\lt \lvert M\rvert`$ だから、
    [(T.getD_eq_getElem')](Wf.md#t-getD_eq_getElem') と `List.getElem_take` により
    これは $`M\langle j_0-1\rangle`$ に等しい。
    他方 $`(\mathrm{hd})`$ より $`\pi_0(\mathrm{headI}\,C_n)=M_{0,j_0}`$ である。
    $`1\le j_0`$ より $`(j_0-1)+1=j_0\lt \lvert M\rvert`$ であるから $`(\mathrm{e}0)`$ を $`j:=j_0-1`$ に適用して
    $`M_{0,j_0}\le M_{0,j_0-1}+1`$、これが求める不等式である。

  **(8) 結論.** $`M[n]=\mathrm{take}\,j_0\,M\mathbin{+\!\!+}C_n`$ について
  [(D.blockok)](#d-blockok) の 3 成分を確かめる。
  - 下界条件：示すべきは $`\forall p\in M[n],\ 0\le\pi_0 p`$ であり、
    任意の対 $`p`$ について $`0\le\pi_0 p`$ が $`\mathbb{N}`$ の最小元性から成り立つ。
  - 増分条件：[(T.steps1_append)](#t-steps1_append) の $`(\Leftarrow)`$ 方向に、
    第 1 成分として (6) の $`\mathrm{steps}_1(\mathrm{take}\,j_0\,M)`$、
    第 2 成分として (5) の $`\mathrm{steps}_1(C_n)`$、第 3 成分として (7) を渡す。
  - 先頭条件：$`M[n]\ne[\,]`$ と仮定して $`\pi_0(\mathrm{headI}(M[n]))=0`$ を示す。$`j_0=0`$ かどうかで分ける。
    - $`j_0=0`$：$`\mathrm{take}\,0\,M=[\,]`$ だから $`M[n]=C_n`$ であり、$`(\mathrm{hd})`$ より
      $`\pi_0(\mathrm{headI}(M[n]))=M_{0,j_0}=M_{0,0}`$。
      $`M\ne[\,]`$ に $`b`$ の先頭条件を適用すると $`\pi_0(\mathrm{headI}\,M)=0`$ であり、
      $`M=x\mathbin{::}xs`$ と書けば $`\mathrm{headI}\,M = x = M\langle0\rangle`$ だから $`M_{0,0}=\pi_0 x=0`$。
    - $`j_0\ne0`$：$`\lvert\mathrm{take}\,j_0\,M\rvert=j_0\ge1`$ より $`\mathrm{take}\,j_0\,M\ne[\,]`$ であるから、
      [(T.headI_append_left)](#t-headI_append_left) より
      $`\mathrm{headI}(M[n]) = \mathrm{headI}(\mathrm{take}\,j_0\,M)`$。
      さらに $`M=x\mathbin{::}xs`$、$`j_0=m+1`$ と書けば
      $`\mathrm{take}\,(m+1)\,(x\mathbin{::}xs) = x\mathbin{::}\mathrm{take}\,m\,xs`$ だから
      $`\mathrm{headI}(\mathrm{take}\,j_0\,M)=x=\mathrm{headI}\,M`$。
      $`b`$ の先頭条件を $`M\ne[\,]`$ に適用して $`\pi_0(\mathrm{headI}\,M)=0`$。∎

<a id="t-blockok_ST_PS"></a>
### 定理 標準形は深さ 0 のブロック (T.blockok_ST_PS)

**主張** $`M\in\mathrm{ST\_PS}`$（[(D.ST_PS)](Def.md#d-ST_PS)）ならば $`\mathrm{blockok}(0,M)`$。

**証明** $`\mathrm{ST\_PS}`$ の導出に関する帰納法（[(D.ST_PS)](Def.md#d-ST_PS) の帰納法原理）。
帰納法の述語は
```math
P(M) :\equiv \mathrm{blockok}(0,M).
```

- 基底段（規則 diag）：$`M=\Delta_0^v`$ の形。[(T.blockok_diagSeq)](#t-blockok_diagSeq) より $`P(\Delta_0^v)`$。
- 帰納段（規則 oper）：$`M\in\mathrm{ST\_PS}`$、$`1\le n`$ とし、帰納法の仮定 $`P(M)`$、すなわち $`\mathrm{blockok}(0,M)`$ を仮定する。
  [(T.blockok_oper)](#t-blockok_oper) をこの仮定と $`1\le n`$ に適用して $`\mathrm{blockok}(0,M[n])`$、すなわち $`P(M[n])`$ を得る。∎

<a id="t-olt_ST_iff_seqlex"></a>
### 定理 標準形上の順序同型 (T.olt_ST_iff_seqlex)

**主張** $`M,N\in\mathrm{ST\_PS}`$ かつ $`M\ne N`$ ならば
```math
\mathrm{tr}\,M\prec\mathrm{tr}\,N \iff M\prec_{\mathrm{lex}}N.
```

**証明** [(T.blockok_ST_PS)](#t-blockok_ST_PS) より $`\mathrm{blockok}(0,M)`$ かつ $`\mathrm{blockok}(0,N)`$ である。
これと $`M\ne N`$ に [(T.olt_iff_seqlex)](#t-olt_iff_seqlex) を $`d:=0`$ として適用すればよい。∎

すなわち、標準形の集合の上では、翻訳 $`\mathrm{tr}`$ は列辞書式順序 $`\prec_{\mathrm{lex}}`$ を
[(D.olt)](Mechanized.md#d-olt) の $`\prec`$ へ写す順序同型である。
