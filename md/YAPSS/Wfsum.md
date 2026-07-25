[← 目次](README.md)

# Wfsum — 和としての項の分解（引数列・和項列・項サイズ）

項 $`x\in\mathrm{Three}`$ を和 $`p_{a_1}(b_1)+\dots+p_{a_k}(b_k)`$ と読んだときの、引数の列 $`\mathrm{sargs}\,x=[b_1,\dots,b_k]`$、
その多重集合 $`\mathrm{margs}\,x`$、和項の列 $`\mathrm{summands}\,x=[\mathsf{P}(a_1,b_1,\mathsf{Z}),\dots,\mathsf{P}(a_k,b_k,\mathsf{Z})]`$、
および項の構造的サイズ $`\mathrm{tsize}\,x`$ を定義する。
宣言は全部で 10 個（定義 4 個、定理 6 個）であり、6 個の定理のうち 4 個は定義式そのものである。
内容のある主張は 2 つ、$`\preceq`$ の推移律 [(T.ole_trans)](#t-ole_trans) と、$`\mathrm{summands}\,x`$ の要素が必ず
$`\mathsf{P}(e,f,\mathsf{Z})`$ の形であること [(T.summands_shape)](#t-summands_shape) である。

## 記法

この章で導入する Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `sargs x` | $`\mathrm{sargs}\,x`$ | 和鎖に沿う引数のリスト |
| `margs x` | $`\mathrm{margs}\,x`$ | 和鎖に沿う引数の多重集合 |
| `summands x` | $`\mathrm{summands}\,x`$ | 和項のリスト |
| `tsize x` | $`\mathrm{tsize}\,x`$ | 項の構造的サイズ（自然数） |

既出の記号（[`Mechanized.md`](Mechanized.md) で定義済み）は次のように書く。

| Lean | 本文 | 定義 |
|---|---|---|
| `Three` | $`\mathrm{Three}`$ | [(D.Three)](Mechanized.md#d-Three) |
| `Z` | $`\mathsf{Z}`$ | [(D.Three)](Mechanized.md#d-Three) の第 1 構成子（項 $`0`$） |
| `P a b c` | $`\mathsf{P}(a,b,c)`$ | [(D.Three)](Mechanized.md#d-Three) の第 2 構成子（項 $`p_a(b)+c`$） |
| `x <o y` | $`x\prec y`$ | [(D.olt)](Mechanized.md#d-olt) |
| `x ≤o y` | $`x\preceq y`$ | [(D.ole)](Mechanized.md#d-ole)（$`x\prec y\ \vee\ x=y`$） |

リストと多重集合については次の記号を用いる。

- `[]` は空リスト、`b :: L` は $`b\mathbin{::}L`$（先頭付加）、`[b₁, …, b_k]` は $`[b_1,\dots,b_k]`$。
  $`s\in L`$ は「$`s`$ がリスト $`L`$ の要素である」（Lean の `List.Mem`）を表す。特に $`s\in[]`$ は偽である。
- `Multiset α` は $`\mathrm{Multiset}(\alpha)`$ と書く。これは `List α` を「並べ替えで移り合う」という同値関係で割った商型であり、
  リスト `L : List α` の同値類（Lean の型強制 `↑L`）を $`\mathrm{ms}(L)`$ と書く。
  すなわち $`\mathrm{ms}(L)=\mathrm{ms}(L')`$ は $`L`$ と $`L'`$ が互いの並べ替えであることと同値であり、
  多重集合は各要素の出現回数のみを保持し、順序を保持しない。

Lean ファイル冒頭のモジュール注釈が述べるとおり、本モジュールはもともと "Sum-layer reduction"、
すなわち「同一準位内の $`\prec`$ の整礎性を、Dershowitz–Manna 多重集合拡大を経由して
引数の上の $`\prec`$ の整礎性へ帰着させる」経路のために書かれたものである。
その経路は放棄され（[`../requirement.md`](../requirement.md) §3.3 により、停止性証明に使われない宣言は Lean 側から削除される）、
現在の `lean/YAPSS/Wfsum.lean` に残っているのは以下の 10 宣言のみである。
このうち他モジュールから参照されるのは $`\mathrm{tsize}`$（[(T.Gterm_tsize)](Gterm.md#t-Gterm_tsize) と
[(D.proj)](Nrm.md#d-proj) の再帰の停止測度）と [(T.ole_trans)](#t-ole_trans)（[`Nrmstep.md`](Nrmstep.md) の複数箇所）であり、
$`\mathrm{sargs}`$, $`\mathrm{margs}`$, $`\mathrm{summands}`$, [(T.summands_shape)](#t-summands_shape) を参照する宣言は
`lean/YAPSS/` の他のどのファイルにも存在しない。

以下の `##` 見出しは、Lean ファイル中の節注釈 `/-! ## … -/` に 1 対 1 で対応する。
宣言を 1 つも含まない節が残っているのは、上に述べた削除の結果である。

## パラメータ付き Dershowitz–Manna 順序（A parametric Dershowitz–Manna order）

この節に属する宣言は、現在の `lean/YAPSS/Wfsum.lean` には存在しない。
ファイル冒頭の `import Mathlib.Data.Multiset.DershowitzManna` はこの節のために置かれたものであるが、
本ファイル中の 10 宣言のいずれもこの import が提供する多重集合順序を用いていない。

## 和の引数と和項（Sum arguments and summands）

<a id="d-sargs"></a>
### 定義 和鎖に沿う引数のリスト (D.sargs)

関数 $`\mathrm{sargs}:\mathrm{Three}\to\mathrm{List}(\mathrm{Three})`$ を、定義域の項の構造に関する再帰で定める。

```math
\mathrm{sargs}\,\mathsf{Z} := [],\qquad
  \mathrm{sargs}\,\mathsf{P}(a,b,c) := b\mathbin{::}\mathrm{sargs}\,c .
```

第 2 式の右辺に現れる再帰呼び出しの引数 $`c`$ は $`\mathsf{P}(a,b,c)`$ の真部分項であるから、
この定義は構造帰納として整合的である。第 2 式の右辺は添字 $`a`$ を用いていない（Lean のパターンも `| P _ b c` である）。
したがって $`\mathrm{sargs}\,\mathsf{P}(a,b,c)`$ の値は $`a`$ に依存しない。

**補足（和鎖表示と、その上での $`\mathrm{sargs}`$ の値）.**
$`k\in\mathbb{N}`$、$`a_1,\dots,a_k\in\mathbb{N}`$、$`b_1,\dots,b_k\in\mathrm{Three}`$ に対し、項の列
$`S_k,S_{k-1},\dots,S_0`$ を添字の降順に

```math
S_k := \mathsf{Z},\qquad S_i := \mathsf{P}(a_{i+1},b_{i+1},S_{i+1})\quad(0\le i<k)
```

で定める。すなわち

```math
S_0 = \mathsf{P}\bigl(a_1,b_1,\mathsf{P}(a_2,b_2,\cdots\mathsf{P}(a_k,b_k,\mathsf{Z})\cdots)\bigr)
```

であり、$`k=0`$ のときは $`S_0=\mathsf{Z}`$ である。[(D.Three)](Mechanized.md#d-Three) の読み方に従えば
$`S_0`$ は和 $`p_{a_1}(b_1)+p_{a_2}(b_2)+\dots+p_{a_k}(b_k)`$ を表す。これを $`S_0`$ の**和鎖表示**と呼ぶ。

*主張 A.* 任意の $`x\in\mathrm{Three}`$ に対し、ある $`k\in\mathbb{N}`$ と $`a_1,\dots,a_k\in\mathbb{N}`$、
$`b_1,\dots,b_k\in\mathrm{Three}`$ が存在して $`x=S_0`$ となる。ここで $`S_0`$ は、その $`k`$ と $`a_1,\dots,a_k`$、
$`b_1,\dots,b_k`$ から上の再帰で定まる項である（以下の $`\Phi`$ の中の $`S_0`$ も同じ意味である）。

*証明.* $`x`$ の構造に関する帰納法。帰納法の述語は
```math
\Phi(x):\equiv \exists k\in\mathbb{N},\ \exists a_1,\dots,a_k\in\mathbb{N},\ \exists b_1,\dots,b_k\in\mathrm{Three},\ x=S_0 .
```

- 基底段 $`x=\mathsf{Z}`$：$`k=0`$ と取れば $`S_0=S_k=\mathsf{Z}=x`$ であり $`\Phi(\mathsf{Z})`$。
- 帰納段 $`x=\mathsf{P}(a,b,c)`$：帰納法の仮定は $`\Phi(b)`$ と $`\Phi(c)`$ である。ここでは $`\Phi(c)`$ のみを用いる。
  $`\Phi(c)`$ により、ある $`k`$ と $`a_1,\dots,a_k`$, $`b_1,\dots,b_k`$ があって $`c=S_0`$ と書ける。
  そこで $`k':=k+1`$、$`a'_1:=a`$, $`b'_1:=b`$、$`a'_{i+1}:=a_i`$, $`b'_{i+1}:=b_i`$（$`1\le i\le k`$）と置くと、
  対応する列 $`S'_{k'},\dots,S'_0`$ は $`S'_{i+1}=S_i`$（$`0\le i\le k`$）をみたし、
  $`S'_0=\mathsf{P}(a'_1,b'_1,S'_1)=\mathsf{P}(a,b,S_0)=\mathsf{P}(a,b,c)=x`$ である。よって $`\Phi(\mathsf{P}(a,b,c))`$。$`\square`$

*主張 B.* 上の記号のもとで、$`0\le i\le k`$ なるすべての $`i`$ について
$`\mathrm{sargs}\,S_i=[b_{i+1},b_{i+2},\dots,b_k]`$。特に $`\mathrm{sargs}\,S_0=[b_1,\dots,b_k]`$。

*証明.* $`k-i`$ に関する帰納法（$`i`$ の降順の帰納法）。帰納法の述語は
```math
\Psi(m):\equiv \mathrm{sargs}\,S_{k-m}=[b_{k-m+1},\dots,b_k]\qquad(0\le m\le k).
```

- 基底段 $`m=0`$：$`S_k=\mathsf{Z}`$ であり、$`\mathrm{sargs}\,\mathsf{Z}=[]`$（[(T.sargs_Z)](#t-sargs_Z)）。
  右辺 $`[b_{k+1},\dots,b_k]`$ は要素を 1 つも持たない列、すなわち $`[]`$ である。よって $`\Psi(0)`$。
- 帰納段 $`m+1\le k`$：帰納法の仮定は $`\Psi(m)`$、すなわち $`\mathrm{sargs}\,S_{k-m}=[b_{k-m+1},\dots,b_k]`$。
  $`i:=k-(m+1)`$ と置くと $`0\le i\lt k`$ かつ $`i+1=k-m`$ だから、定義より $`S_i=\mathsf{P}(a_{i+1},b_{i+1},S_{i+1})`$ であり、
  [(T.sargs_P)](#t-sargs_P) より
  ```math
  \mathrm{sargs}\,S_i=b_{i+1}\mathbin{::}\mathrm{sargs}\,S_{i+1}
   =b_{i+1}\mathbin{::}[b_{i+2},\dots,b_k]=[b_{i+1},b_{i+2},\dots,b_k].
  ```
  よって $`\Psi(m+1)`$。$`\square`$

<a id="t-sargs_Z"></a>
### 定理 $`\mathrm{sargs}\,\mathsf{Z}=[]`$ (T.sargs_Z)

**主張** $`\mathrm{sargs}\,\mathsf{Z}=[]`$。

**証明** [(D.sargs)](#d-sargs) の第 1 式そのものであり、両辺は定義により同一の項である。∎

<a id="t-sargs_P"></a>
### 定理 $`\mathrm{sargs}`$ の展開 (T.sargs_P)

**主張** 任意の $`a\in\mathbb{N}`$、$`b,c\in\mathrm{Three}`$ に対し
$`\mathrm{sargs}\,\mathsf{P}(a,b,c)=b\mathbin{::}\mathrm{sargs}\,c`$。

**証明** [(D.sargs)](#d-sargs) の第 2 式そのものであり、両辺は定義により同一の項である。
右辺は $`a`$ を含まないから、この等式は $`a`$ の値によらず成り立つ。∎

<a id="d-margs"></a>
### 定義 引数の多重集合 (D.margs)

```math
\mathrm{margs}\,x := \mathrm{ms}(\mathrm{sargs}\,x)\ \in\ \mathrm{Multiset}(\mathrm{Three})
```

（[(D.sargs)](#d-sargs)）。すなわち $`\mathrm{sargs}\,x`$ の要素を、出現回数を保ったまま、順序を忘れて集めた多重集合である。
[(D.sargs)](#d-sargs) の補足の記号で $`x=S_0`$ と和鎖表示すれば、$`\mathrm{margs}\,x`$ は $`b_1,\dots,b_k`$ を
（重複を許して）並べた多重集合である。

<a id="t-ole_trans"></a>
### 定理 $`\preceq`$ の推移律 (T.ole_trans)

**主張** $`x,y,z\in\mathrm{Three}`$ とする。$`x\preceq y`$ かつ $`y\preceq z`$ ならば $`x\preceq z`$。

**証明** [(D.ole)](Mechanized.md#d-ole) より、仮定 $`x\preceq y`$ は $`x\prec y`$ または $`x=y`$ である。この 2 つで場合分けする。

- $`x\prec y`$ のとき。もう一方の仮定 $`y\preceq z`$ と合わせて
  [(T.olt_ole_trans)](Mechanized.md#t-olt_ole_trans)（$`x\prec y`$ かつ $`y\preceq z`$ ならば $`x\prec z`$）を適用すると
  $`x\prec z`$ を得る。[(D.ole)](Mechanized.md#d-ole) の第 1 選言により $`x\preceq z`$。
- $`x=y`$ のとき。仮定 $`y\preceq z`$ の $`y`$ を $`x`$ で置き換えると、それ自体が $`x\preceq z`$ である。

いずれの場合も $`x\preceq z`$ が得られた。∎

## `NF` 項は添字 0 の和である（`NF` terms are zero-top sums）

この節に属する宣言は、現在の `lean/YAPSS/Wfsum.lean` には存在しない。
節見出しの `NF` は [(D.NF)](Proofs.md#d-NF) である。

## 一般の和の剥がし（The general sum peel）

Lean の節注釈によれば、この節は「（添字が $`0`$ であるという条件を課さずに）
[(D.cnf)](Wf.md#d-cnf) をみたす和どうしの $`\prec`$ を、和項どうしの順序の多重集合拡大
（多重集合の上の Dershowitz–Manna 順序）へ埋め込む」ことを意図した節である。
その埋め込みを述べる宣言は現在残っておらず、この節に残っているのは、和項のリスト $`\mathrm{summands}`$ と、
その要素の形状に関する補題 [(T.summands_shape)](#t-summands_shape) のみである。

<a id="d-summands"></a>
### 定義 和項のリスト (D.summands)

関数 $`\mathrm{summands}:\mathrm{Three}\to\mathrm{List}(\mathrm{Three})`$ を、定義域の項の構造に関する再帰で定める。

```math
\mathrm{summands}\,\mathsf{Z} := [],\qquad
  \mathrm{summands}\,\mathsf{P}(a,b,c) := \mathsf{P}(a,b,\mathsf{Z})\mathbin{::}\mathrm{summands}\,c .
```

第 2 式の右辺の再帰呼び出しの引数 $`c`$ は $`\mathsf{P}(a,b,c)`$ の真部分項であるから、この定義は構造帰納として整合的である。
[(D.Three)](Mechanized.md#d-Three) の読み方では $`\mathsf{P}(a,b,\mathsf{Z})`$ は $`p_a(b)+0`$、すなわち単項の和 $`p_a(b)`$ を表す。

**補足（和鎖表示の上での $`\mathrm{summands}`$ の値）.**
[(D.sargs)](#d-sargs) の補足で定めた和鎖表示 $`S_k=\mathsf{Z}`$、$`S_i=\mathsf{P}(a_{i+1},b_{i+1},S_{i+1})`$（$`0\le i\lt k`$）
のもとで、$`0\le i\le k`$ なるすべての $`i`$ について

```math
\mathrm{summands}\,S_i=[\ \mathsf{P}(a_{i+1},b_{i+1},\mathsf{Z}),\ \mathsf{P}(a_{i+2},b_{i+2},\mathsf{Z}),\ \dots,\ \mathsf{P}(a_k,b_k,\mathsf{Z})\ ].
```

*証明.* $`k-i`$ に関する帰納法（$`i`$ の降順の帰納法）。帰納法の述語は
```math
\Xi(m):\equiv \mathrm{summands}\,S_{k-m}=[\mathsf{P}(a_{k-m+1},b_{k-m+1},\mathsf{Z}),\dots,\mathsf{P}(a_k,b_k,\mathsf{Z})]
\qquad(0\le m\le k).
```

- 基底段 $`m=0`$：$`S_k=\mathsf{Z}`$ であり $`\mathrm{summands}\,\mathsf{Z}=[]`$（[(T.summands_Z)](#t-summands_Z)）。
  右辺は要素を 1 つも持たない列 $`[]`$ である。よって $`\Xi(0)`$。
- 帰納段 $`m+1\le k`$：帰納法の仮定は $`\Xi(m)`$。$`i:=k-(m+1)`$ と置くと $`0\le i\lt k`$ かつ $`i+1=k-m`$ であるから、
  $`S_i=\mathsf{P}(a_{i+1},b_{i+1},S_{i+1})`$ であり、[(T.summands_P)](#t-summands_P) より
  ```math
  \mathrm{summands}\,S_i=\mathsf{P}(a_{i+1},b_{i+1},\mathsf{Z})\mathbin{::}\mathrm{summands}\,S_{i+1}
   =[\mathsf{P}(a_{i+1},b_{i+1},\mathsf{Z}),\dots,\mathsf{P}(a_k,b_k,\mathsf{Z})].
  ```
  よって $`\Xi(m+1)`$。$`\square`$

$`i=0`$ と [(D.sargs)](#d-sargs) の主張 A を合わせると、任意の $`x\in\mathrm{Three}`$ について
$`\mathrm{summands}\,x`$ は和鎖表示の各和項 $`p_{a_j}(b_j)`$ を $`\mathsf{P}(a_j,b_j,\mathsf{Z})`$ の形で並べたリストであり、
$`\mathrm{sargs}\,x`$ と長さが等しい。

<a id="t-summands_Z"></a>
### 定理 $`\mathrm{summands}\,\mathsf{Z}=[]`$ (T.summands_Z)

**主張** $`\mathrm{summands}\,\mathsf{Z}=[]`$。

**証明** [(D.summands)](#d-summands) の第 1 式そのものであり、両辺は定義により同一の項である。∎

<a id="t-summands_P"></a>
### 定理 $`\mathrm{summands}`$ の展開 (T.summands_P)

**主張** 任意の $`a\in\mathbb{N}`$、$`b,c\in\mathrm{Three}`$ に対し
$`\mathrm{summands}\,\mathsf{P}(a,b,c)=\mathsf{P}(a,b,\mathsf{Z})\mathbin{::}\mathrm{summands}\,c`$。

**証明** [(D.summands)](#d-summands) の第 2 式そのものであり、両辺は定義により同一の項である。∎

<a id="t-summands_shape"></a>
### 定理 和項の形 (T.summands_shape)

**主張** $`x,s\in\mathrm{Three}`$ とする。$`s\in\mathrm{summands}\,x`$ ならば、ある $`e\in\mathbb{N}`$ と $`f\in\mathrm{Three}`$ が存在して
$`s=\mathsf{P}(e,f,\mathsf{Z})`$。

（Lean での束縛変数名は `a`, `c` であるが、和項 $`\mathsf{P}(a,b,c)`$ の $`a`$, $`c`$ と紛れないよう
本文では $`e`$, $`f`$ と書く。主張の内容は同じである。）

**証明** $`s`$ を固定し、$`x`$ の構造に関する帰納法。帰納法の述語は

```math
\Theta(x):\equiv \bigl(s\in\mathrm{summands}\,x\bigr)\ \to\ \exists e\in\mathbb{N},\ \exists f\in\mathrm{Three},\ s=\mathsf{P}(e,f,\mathsf{Z}).
```

- 基底段 $`x=\mathsf{Z}`$：[(T.summands_Z)](#t-summands_Z) より $`\mathrm{summands}\,\mathsf{Z}=[]`$ であるから、
  前件は $`s\in[]`$ である。空リストは要素を持たないから $`s\in[]`$ は偽であり、含意 $`\Theta(\mathsf{Z})`$ は成り立つ。
  （Lean 側の `simp at hs` はこの `List.not_mem_nil` による矛盾の導出である。）
- 帰納段 $`x=\mathsf{P}(a,b,c)`$：帰納法の仮定は $`\Theta(b)`$ と $`\Theta(c)`$ である。以下では $`\Theta(c)`$ のみを用いる。
  前件 $`s\in\mathrm{summands}\,\mathsf{P}(a,b,c)`$ を仮定する。[(T.summands_P)](#t-summands_P) により、これは
  ```math
  s\in \mathsf{P}(a,b,\mathsf{Z})\mathbin{::}\mathrm{summands}\,c
  ```
  と同じ命題である。先頭付加されたリストへの所属は
  ```math
  s\in (u\mathbin{::}L)\ \iff\ s=u\ \vee\ s\in L
  ```
  （Lean の `List.mem_cons`）であるから、次の 2 つの場合に分かれる。
  - $`s=\mathsf{P}(a,b,\mathsf{Z})`$ の場合：$`e:=a`$、$`f:=b`$ と取れば $`s=\mathsf{P}(e,f,\mathsf{Z})`$ であり、結論が成り立つ。
  - $`s\in\mathrm{summands}\,c`$ の場合：帰納法の仮定 $`\Theta(c)`$ をこの所属に適用して、
    $`s=\mathsf{P}(e,f,\mathsf{Z})`$ をみたす $`e,f`$ を得る。

  いずれの場合も結論が得られたので $`\Theta(\mathsf{P}(a,b,c))`$。∎

## 準位 $`m`$ の引数クラスと残余核の下降（The level-`m` argument classes and the descent of the residual core）

この節に属する宣言は、現在の `lean/YAPSS/Wfsum.lean` には存在しない。

## 準位 0：梯子の基底（Level 0: the base of the ladder）

Lean の節注釈によれば、この節は準位（level）$`0`$、すなわち
[(D.cnf)](Wf.md#d-cnf) をみたし [(D.maxsub)](Wf.md#d-maxsub) の値が $`0`$ である項のクラスの上で
$`\prec`$ が整礎であることを扱う節である。その主張を述べる宣言は現在残っておらず、
この節に残るのは次の項サイズの定義のみである。

<a id="d-tsize"></a>
### 定義 項の構造的サイズ (D.tsize)

関数 $`\mathrm{tsize}:\mathrm{Three}\to\mathbb{N}`$ を、定義域の項の構造に関する再帰で定める。

```math
\mathrm{tsize}\,\mathsf{Z} := 1,\qquad
  \mathrm{tsize}\,\mathsf{P}(a,b,c) := \mathrm{tsize}\,b+\mathrm{tsize}\,c+1 .
```

第 2 式の右辺の再帰呼び出しの引数 $`b`$, $`c`$ はいずれも $`\mathsf{P}(a,b,c)`$ の真部分項であるから、
この定義は構造帰納として整合的である。右辺は添字 $`a`$ を用いていない（Lean のパターンも `| P _ b c` である）から、
$`\mathrm{tsize}\,\mathsf{P}(a,b,c)`$ の値は $`a`$ に依存しない。

**補足（正値性）.** 任意の $`x\in\mathrm{Three}`$ に対し $`1\le\mathrm{tsize}\,x`$。

*証明.* $`x`$ の構造に関する帰納法。帰納法の述語は $`\Lambda(x):\equiv 1\le\mathrm{tsize}\,x`$。

- 基底段 $`x=\mathsf{Z}`$：$`\mathrm{tsize}\,\mathsf{Z}=1`$ であり $`1\le 1`$。
- 帰納段 $`x=\mathsf{P}(a,b,c)`$：帰納法の仮定は $`\Lambda(b)`$ と $`\Lambda(c)`$ であるが、ここでは用いない。
  $`\mathrm{tsize}\,\mathsf{P}(a,b,c)=\mathrm{tsize}\,b+\mathrm{tsize}\,c+1`$ であり、
  自然数の加法について $`0\le \mathrm{tsize}\,b+\mathrm{tsize}\,c`$ だから $`1\le \mathrm{tsize}\,b+\mathrm{tsize}\,c+1`$。$`\square`$

$`\mathrm{tsize}`$ は本章では他に用いられないが、後続の章で再帰の停止を保証する測度として使われる。すなわち
[(T.Gterm_tsize)](Gterm.md#t-Gterm_tsize) が、[(D.Gterm)](Gterm.md#d-Gterm) について
$`x\in\mathrm{Gterm}\,v\,t\ \Rightarrow\ \mathrm{tsize}\,x\lt \mathrm{tsize}\,t`$
という真の減少を与え、これにより [(D.proj)](Nrm.md#d-proj) の再帰が停止する（Lean の `termination_by tsize b`）。

## 残余核（2 段目）（The residual core, two levels in）

この節に属する宣言は、現在の `lean/YAPSS/Wfsum.lean` には存在しない。
Lean の節注釈によれば、この節には準位 $`m`$ の和の引数（添字は任意）の上の $`\prec`$ の整礎性が置かれる予定であり、
その帰納段（準位 $`m`$ の場合を準位 $`\lt m`$ の場合から得る段）は注釈中で "the Buchholz-collapse core" と呼ばれ、
`sorry` のまま残されていた。本証明はこの経路を採らず、値の正規化
[(D.nrm)](Nrm.md#d-nrm) を経由する経路（[`Nrm.md`](Nrm.md) 以降）を採る。

## 最上位：引数核を法とした PSS 停止性（Top-level: PSS termination, modulo the argument core）

この節に属する宣言は、現在の `lean/YAPSS/Wfsum.lean` には存在しない。
PSS の停止性は、仮定を置かない形で [(T.PSS_terminates_unconditional)](Final.md#t-PSS_terminates_unconditional) として
[`Final.md`](Final.md) で示される。
