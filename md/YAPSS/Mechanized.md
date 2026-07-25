[← 目次](README.md)

# Mechanized — 三分岐記法 $`p_a(b)+c`$、その順序 $`\prec`$、展開一段の減少

ペア列を項へ写す翻訳 $`\mathrm{tr}`$ と、その値域である三分岐記法 $`\mathrm{Three}`$ 上の添字優先辞書式順序 $`\prec`$ を定義する。
$`\prec`$ が非反射的・推移的・三分律をみたすことを示し、$`\mathrm{tr}`$ の形状補題（単一木・ブロック分解・行 0 平行移動不変性・文脈合同）を用意する。
これらを組み合わせ、$`1\lt \lvert M\rvert`$ のとき [(D.oper)](Def.md#d-oper) が取りうる 3 つの枝すべてについて
$`\mathrm{tr}`$ の減少を証明する。
結論は [(T.m_step_decreases)](#t-m_step_decreases)：$`1 \lt \lvert M\rvert`$ かつ $`1 \le n`$ ならば $`\mathrm{tr}(M[n]) \prec \mathrm{tr}(M)`$、すなわち展開一段は $`\prec`$ を必ず真に減少させる。

## 記法

この章で用いる Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `Three` | $`\mathrm{Three}`$ | 三分岐記法の項の型 |
| `Z` | $`\mathsf{Z}`$ | 項 $`0`$ |
| `P a b c` | $`\mathsf{P}(a,b,c)`$ | 項 $`p_a(b)+c`$ |
| `x <o y` | $`x \prec y`$ | 添字優先辞書式順序 |
| `x ≤o y` | $`x \preceq y`$ | $`x \prec y \vee x = y`$ |
| `lead t` | $`\mathrm{lead}\,t`$ | 先頭主要項の添字 |
| `translate M` | $`\mathrm{tr}\,M`$ | ペア列 $`M`$ の翻訳 |
| `sndSet M` | $`\mathrm{sndSet}\,M`$ | $`M`$ に現れる行 1 の値の集合 |

ペア列とその周辺（[`Def.md`](Def.md) で定義済み）については次のように書く。

| Lean | 本文 | 意味 |
|---|---|---|
| `M.length` | $`\lvert M\rvert`$ | 長さ（記事の $`\mathrm{Lng}\,M`$） |
| `p.1`, `p.2` | $`\pi_0 p`$, $`\pi_1 p`$ | 対 $`p`$ の第 0・第 1 成分 |
| `M.getD j (0,0)` | $`M\langle j\rangle`$ | 第 $`j`$ 対（範囲外なら $`(0,0)`$） |
| `entry M i j` | $`M_{i,j}`$ | 第 $`j`$ 対の第 $`i`$ 成分 |
| `M⟦n⟧` | $`M[n]`$ | 展開（コピー数 $`n`$） |
| `xs ++ ys` | $`xs \mathbin{+\!\!+} ys`$ | 連結 |
| `x :: xs` | $`x \mathbin{::} xs`$ | 先頭付加 |
| `L.take j`, `L.drop j` | $`\mathrm{take}\,j\,L`$, $`\mathrm{drop}\,j\,L`$ | 前 $`j`$ 個、前 $`j`$ 個を除いた残り |
| `L.dropLast` | $`\mathrm{dropLast}\,L`$ | 末尾 1 個を除いた列 |
| `L.getLast h` | $`\mathrm{getLast}\,L`$ | 末尾要素（$`L\ne[]`$ のとき） |
| `Relation.ReflTransGen r` | $`\mathrm{ReflTransGen}(r)`$ | 関係 $`r`$ の反射推移閉包 |
| `L.headI` | $`\mathrm{headI}\,L`$ | 先頭要素（空列なら $`(0,0)`$） |
| `List.range n` | $`\mathrm{range}(n)`$ | $`[0,1,\dots,n-1]`$ |
| `List.range' a m` | $`\mathrm{range}'(a,m)`$ | $`[a,a+1,\dots,a+m-1]`$ |
| `L.map f` | $`\mathrm{map}\,f\,L`$ | 各要素に $`f`$ を適用 |
| `L.flatMap f` | $`\mathrm{flatMap}\,f\,L`$ | 各要素に $`f`$ を適用して連結 |

ペア列の型は [(D.PairSeq)](Def.md#d-PairSeq)、成分 $`M_{i,j}`$ は [(D.entry)](Def.md#d-entry)、
展開 $`M[n]`$ は [(D.oper)](Def.md#d-oper) で定義されている。

さらに、行 0 の値 $`a`$ を基準とする `takeWhile` / `dropWhile` を次の記号で略記する
（$`L`$ はペア列）。

```math
\mathrm{tw}_a L := L.\mathrm{takeWhile}\,(\lambda q.\ a < \pi_0 q),\qquad
  \mathrm{dw}_a L := L.\mathrm{dropWhile}\,(\lambda q.\ a < \pi_0 q).
```

すなわち $`\mathrm{tw}_a L`$ は $`L`$ の先頭から「行 0 の値が $`a`$ より真に大きい」要素が続く極大な前部分列、
$`\mathrm{dw}_a L`$ はその残りであり、$`\mathrm{tw}_a L \mathbin{+\!\!+} \mathrm{dw}_a L = L`$ が成り立つ。

## 添字優先辞書式順序

<a id="d-Three"></a>
### 定義 三分岐記法 (D.Three)

$`\mathrm{Three}`$ を、次の 2 つの構成子をもつ帰納型として定義する。

```math
\mathsf{Z} : \mathrm{Three},\qquad
  \mathsf{P} : \mathbb{N} \to \mathrm{Three} \to \mathrm{Three} \to \mathrm{Three}.
```

$`\mathsf{Z}`$ は項 $`0`$ を、$`\mathsf{P}(a,b,c)`$ は項 $`p_a(b)+c`$ を表す。
$`a`$ を主要項 $`p_a(b)`$ の**添字**、$`b`$ を**引数**、$`c`$ を**後続和**と呼ぶ。
帰納型であるから、$`\mathsf{Z} \ne \mathsf{P}(a,b,c)`$ であり、
$`\mathsf{P}(a,b,c) = \mathsf{P}(a',b',c')`$ は $`a=a' \wedge b=b' \wedge c=c'`$ と同値である。

<a id="d-olt"></a>
### 定義 添字優先辞書式順序 (D.olt)

関係 $`\prec\ \subseteq \mathrm{Three}\times\mathrm{Three}`$ を、第 1 引数に関する構造帰納で定義する。

```math
\begin{aligned}
\mathsf{Z} &\prec \mathsf{Z} &&:\iff \bot,\cr
\mathsf{Z} &\prec \mathsf{P}(e,f,g) &&:\iff \top,\cr
\mathsf{P}(a,b,c) &\prec \mathsf{Z} &&:\iff \bot,\cr
\mathsf{P}(a,b,c) &\prec \mathsf{P}(e,f,g) &&:\iff
 a<e \ \vee\ (a=e \wedge b \prec f)\ \vee\ (a=e \wedge b=f \wedge c \prec g).
\end{aligned}
```

第 4 式の右辺に現れる再帰呼び出し $`b \prec f`$、$`c \prec g`$ の第 1 引数 $`b`$, $`c`$ は
$`\mathsf{P}(a,b,c)`$ の真部分項であるから、この定義は第 1 引数に関する構造帰納として整合的である。
添字 $`a`$ を第 1 の、引数 $`b`$ を第 2 の、後続和 $`c`$ を第 3 の比較対象とする辞書式順序であり、
これを**添字優先**と呼ぶ。

<a id="d-ole"></a>
### 定義 広義順序 (D.ole)

```math
x \preceq y \ :\iff\ x \prec y \ \vee\ x = y.
```

<a id="t-olt_Z_Z"></a>
### 定理 $`\mathsf{Z}\not\prec\mathsf{Z}`$ (T.olt_Z_Z)

**主張** $`\neg(\mathsf{Z} \prec \mathsf{Z})`$。

**証明** [(D.olt)](#d-olt) の第 1 式により $`\mathsf{Z}\prec\mathsf{Z}`$ は $`\bot`$ と定義により等しい。
よって $`\mathsf{Z}\prec\mathsf{Z}`$ の仮定からそのまま $`\bot`$ が得られる。∎

<a id="t-olt_Z_P"></a>
### 定理 $`\mathsf{Z}`$ は主要項より小さい (T.olt_Z_P)

**主張** 任意の $`a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し $`\mathsf{Z}\prec\mathsf{P}(a,b,c)`$。

**証明** [(D.olt)](#d-olt) の第 2 式により $`\mathsf{Z}\prec\mathsf{P}(a,b,c)`$ は $`\top`$ と定義により等しい。∎

<a id="t-olt_P_Z"></a>
### 定理 主要項は $`\mathsf{Z}`$ より小さくない (T.olt_P_Z)

**主張** 任意の $`a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し $`\neg(\mathsf{P}(a,b,c)\prec\mathsf{Z})`$。

**証明** [(D.olt)](#d-olt) の第 3 式により $`\mathsf{P}(a,b,c)\prec\mathsf{Z}`$ は $`\bot`$ と定義により等しい。∎

<a id="t-olt_P_P"></a>
### 定理 主要項どうしの比較 (T.olt_P_P)

**主張**
```math
\mathsf{P}(a,b,c)\prec\mathsf{P}(e,f,g)\ \iff\
 a<e \ \vee\ (a=e \wedge b \prec f)\ \vee\ (a=e \wedge b=f \wedge c \prec g).
```

**証明** [(D.olt)](#d-olt) の第 4 式そのものであり、両辺は定義により同一の命題である。∎

<a id="d-lead"></a>
### 定義 先頭添字 (D.lead)

```math
\mathrm{lead}\,\mathsf{Z} := 0,\qquad \mathrm{lead}\,\mathsf{P}(a,b,c) := a.
```

<a id="t-lead_Z"></a>
### 定理 $`\mathrm{lead}\,\mathsf{Z}=0`$ (T.lead_Z)

**主張** $`\mathrm{lead}\,\mathsf{Z} = 0`$。

**証明** [(D.lead)](#d-lead) の第 1 式である。∎

<a id="t-lead_P"></a>
### 定理 $`\mathrm{lead}\,\mathsf{P}(a,b,c)=a`$ (T.lead_P)

**主張** $`\mathrm{lead}\,\mathsf{P}(a,b,c) = a`$。

**証明** [(D.lead)](#d-lead) の第 2 式である。∎

<a id="t-olt_P_of_lead_lt"></a>
### 定理 添字優先支配 (T.olt_P_of_lead_lt)

**主張** $`t\in\mathrm{Three}`$, $`w\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ とする。
```math
t = \mathsf{Z}\ \vee\ \mathrm{lead}\,t < w \ \Longrightarrow\ t \prec \mathsf{P}(w,b,c).
```

**証明** $`t`$ の構成子で場合分けする。

- $`t = \mathsf{Z}`$ のとき。[(T.olt_Z_P)](#t-olt_Z_P) より $`\mathsf{Z}\prec\mathsf{P}(w,b,c)`$。
- $`t = \mathsf{P}(a,b',c')`$ のとき。仮定の第 1 選言 $`\mathsf{P}(a,b',c')=\mathsf{Z}`$ は
  [(D.Three)](#d-Three) の構成子相異により成立しない。よって第 2 選言が成立し、
  [(T.lead_P)](#t-lead_P) より $`\mathrm{lead}\,t = a`$ であるから $`a \lt w`$。
  [(T.olt_P_P)](#t-olt_P_P) の右辺第 1 選言がみたされるので
  $`\mathsf{P}(a,b',c') \prec \mathsf{P}(w,b,c)`$。∎

この補題は [(T.core_i1)](#t-core_i1) で使う。そこでは、コピー列の翻訳の先頭添字が
落とされる最終対の行 1 の値より真に小さいことから、コピー列全体がその最終対 1 個に支配される。

<a id="t-olt_irrefl"></a>
### 定理 非反射性 (T.olt_irrefl)

**主張** 任意の $`x\in\mathrm{Three}`$ に対し $`\neg(x \prec x)`$。

**証明** $`x`$ の構造に関する帰納法。帰納法の述語は
```math
\Phi(x) :\equiv \neg(x\prec x).
```

- 基底段 $`x=\mathsf{Z}`$：[(T.olt_Z_Z)](#t-olt_Z_Z) より $`\neg(\mathsf{Z}\prec\mathsf{Z})`$、すなわち $`\Phi(\mathsf{Z})`$。
- 帰納段 $`x=\mathsf{P}(a,b,c)`$：帰納法の仮定は $`\Phi(b)`$（$`\neg(b\prec b)`$）と $`\Phi(c)`$（$`\neg(c\prec c)`$）である。
  [(T.olt_P_P)](#t-olt_P_P) より $`\mathsf{P}(a,b,c)\prec\mathsf{P}(a,b,c)`$ は
  ```math
  a<a \ \vee\ (a=a \wedge b\prec b)\ \vee\ (a=a\wedge b=b\wedge c\prec c)
  ```
  と同値である。第 1 選言は $`\mathbb{N}`$ の $`\lt `$ の非反射性により偽、
  第 2 選言は $`\Phi(b)`$ により偽、第 3 選言は $`\Phi(c)`$ により偽。
  よって 3 つの選言すべてが偽であり $`\Phi(\mathsf{P}(a,b,c))`$。∎

<a id="t-not_olt_Z"></a>
### 定理 $`\mathsf{Z}`$ は最小 (T.not_olt_Z)

**主張** 任意の $`x\in\mathrm{Three}`$ に対し $`\neg(x\prec\mathsf{Z})`$。

**証明** $`x`$ の構成子で場合分けする。$`x=\mathsf{Z}`$ のときは [(T.olt_Z_Z)](#t-olt_Z_Z)、
$`x=\mathsf{P}(a,b,c)`$ のときは [(T.olt_P_Z)](#t-olt_P_Z) である。∎

<a id="t-olt_Z_iff"></a>
### 定理 上界は $`\mathsf{Z}`$ でない (T.olt_Z_iff)

**主張** $`x\prec y`$ ならば $`y \ne \mathsf{Z}`$。

**証明** $`y=\mathsf{Z}`$ と仮定すると $`x\prec\mathsf{Z}`$ となり、[(T.not_olt_Z)](#t-not_olt_Z) に矛盾する。∎

<a id="t-olt_trans"></a>
### 定理 推移律 (T.olt_trans)

**主張** $`x\prec y`$ かつ $`y\prec z`$ ならば $`x\prec z`$。

**証明** $`z`$ の構造に関する帰納法（$`x,y`$ は全称量化したまま動かす）。帰納法の述語は
```math
\Phi(z) :\equiv \forall x\,y\in\mathrm{Three},\ (x\prec y \wedge y\prec z) \to x\prec z.
```

- 基底段 $`z=\mathsf{Z}`$：仮定 $`y\prec\mathsf{Z}`$ は [(T.not_olt_Z)](#t-not_olt_Z) に反するので、
  前件が偽であり $`\Phi(\mathsf{Z})`$ が成り立つ。
- 帰納段 $`z=\mathsf{P}(c_1,c_2,c_3)`$：帰納法の仮定は $`\Phi(c_2)`$ と $`\Phi(c_3)`$ である。
  $`x,y`$ を取り $`x\prec y`$, $`y\prec\mathsf{P}(c_1,c_2,c_3)`$ とする。

  $`x=\mathsf{Z}`$ のときは [(T.olt_Z_P)](#t-olt_Z_P) より $`x\prec\mathsf{P}(c_1,c_2,c_3)`$ である。
  以下 $`x=\mathsf{P}(a_1,a_2,a_3)`$ とする。$`x\prec y`$ と [(T.olt_Z_iff)](#t-olt_Z_iff) より $`y\ne\mathsf{Z}`$、
  よって $`y=\mathsf{P}(e_1,e_2,e_3)`$ と書ける。[(T.olt_P_P)](#t-olt_P_P) により、
  $`x\prec y`$ は次の 3 つのいずれかである。

  - (1) $`a_1\lt e_1`$
  - (2) $`a_1=e_1 \wedge a_2\prec e_2`$
  - (3) $`a_1=e_1 \wedge a_2=e_2 \wedge a_3\prec e_3`$

  また [(T.olt_P_P)](#t-olt_P_P) により、$`y\prec z`$ は次の 3 つのいずれかである。

  - (I) $`e_1\lt c_1`$
  - (II) $`e_1=c_1 \wedge e_2\prec c_2`$
  - (III) $`e_1=c_1 \wedge e_2=c_2 \wedge e_3\prec c_3`$

  9 通りすべてを列挙する。各欄には $`x\prec z`$ を与える
  [(T.olt_P_P)](#t-olt_P_P) 右辺の選言を書く。

  | | (I) $`e_1\lt c_1`$ | (II) $`e_1=c_1,\ e_2\prec c_2`$ | (III) $`e_1=c_1,\ e_2=c_2,\ e_3\prec c_3`$ |
  |---|---|---|---|
  | (1) | $`a_1\lt e_1\lt c_1`$ より $`a_1\lt c_1`$（第 1 選言） | $`a_1\lt e_1=c_1`$（第 1 選言） | $`a_1\lt e_1=c_1`$（第 1 選言） |
  | (2) | $`a_1=e_1\lt c_1`$（第 1 選言） | $`a_1=c_1`$ かつ $`a_2\prec e_2\prec c_2`$、$`\Phi(c_2)`$ より $`a_2\prec c_2`$（第 2 選言） | $`a_1=c_1`$ かつ $`a_2\prec e_2=c_2`$（第 2 選言） |
  | (3) | $`a_1=e_1\lt c_1`$（第 1 選言） | $`a_1=c_1`$ かつ $`a_2=e_2\prec c_2`$（第 2 選言） | $`a_1=c_1`$, $`a_2=c_2`$ かつ $`a_3\prec e_3\prec c_3`$、$`\Phi(c_3)`$ より $`a_3\prec c_3`$（第 3 選言） |

  (1)(I) では $`\mathbb{N}`$ の $`\lt `$ の推移律を用いた。
  (2)(II) では帰納法の仮定 $`\Phi(c_2)`$ を $`x:=a_2`$, $`y:=e_2`$ に適用した。
  (3)(III) では帰納法の仮定 $`\Phi(c_3)`$ を $`x:=a_3`$, $`y:=e_3`$ に適用した。
  いずれの場合も $`x\prec z`$ が得られたので $`\Phi(\mathsf{P}(c_1,c_2,c_3))`$。∎

<a id="t-olt_total"></a>
### 定理 三分律 (T.olt_total)

**主張** 任意の $`x,y\in\mathrm{Three}`$ に対し $`x\prec y \ \vee\ x=y \ \vee\ y\prec x`$。

**証明** $`x`$ の構造に関する帰納法（$`y`$ は全称量化したまま動かす）。帰納法の述語は
```math
\Psi(x) :\equiv \forall y\in\mathrm{Three},\ x\prec y \vee x=y \vee y\prec x.
```

- 基底段 $`x=\mathsf{Z}`$：$`y=\mathsf{Z}`$ なら $`x=y`$（第 2 選言）、
  $`y=\mathsf{P}(e_1,e_2,e_3)`$ なら [(T.olt_Z_P)](#t-olt_Z_P) より $`x\prec y`$（第 1 選言）。
- 帰納段 $`x=\mathsf{P}(a_1,a_2,a_3)`$：帰納法の仮定は $`\Psi(a_2)`$ と $`\Psi(a_3)`$ である。
  $`y=\mathsf{Z}`$ なら [(T.olt_Z_P)](#t-olt_Z_P) より $`y\prec x`$（第 3 選言）。
  $`y=\mathsf{P}(e_1,e_2,e_3)`$ とし、$`\mathbb{N}`$ の三分律で $`a_1`$ と $`e_1`$ を比較する。
  - $`a_1\lt e_1`$：[(T.olt_P_P)](#t-olt_P_P) 第 1 選言より $`x\prec y`$。
  - $`e_1\lt a_1`$：[(T.olt_P_P)](#t-olt_P_P) 第 1 選言より $`y\prec x`$。
  - $`a_1=e_1`$：帰納法の仮定 $`\Psi(a_2)`$ を $`y:=e_2`$ に適用して 3 つに分ける。
    - $`a_2\prec e_2`$：[(T.olt_P_P)](#t-olt_P_P) 第 2 選言より $`x\prec y`$。
    - $`e_2\prec a_2`$：[(T.olt_P_P)](#t-olt_P_P) 第 2 選言より $`y\prec x`$。
    - $`a_2=e_2`$：帰納法の仮定 $`\Psi(a_3)`$ を $`y:=e_3`$ に適用して 3 つに分ける。
      - $`a_3\prec e_3`$：[(T.olt_P_P)](#t-olt_P_P) 第 3 選言より $`x\prec y`$。
      - $`e_3\prec a_3`$：[(T.olt_P_P)](#t-olt_P_P) 第 3 選言より $`y\prec x`$。
      - $`a_3=e_3`$：$`a_1=e_1`$, $`a_2=e_2`$, $`a_3=e_3`$ より [(D.Three)](#d-Three) の構成子の単射性から $`x=y`$。

  よって $`\Psi(\mathsf{P}(a_1,a_2,a_3))`$。∎

<a id="t-olt_ole_trans"></a>
### 定理 $`\prec`$ と $`\preceq`$ の合成 (T.olt_ole_trans)

**主張** $`x\prec y`$ かつ $`y\preceq z`$ ならば $`x\prec z`$。

**証明** [(D.ole)](#d-ole) より $`y\preceq z`$ は $`y\prec z`$ または $`y=z`$ である。
前者なら [(T.olt_trans)](#t-olt_trans) より $`x\prec z`$。後者なら $`x\prec y = z`$。∎

<a id="t-olt_P_b"></a>
### 定理 引数についての狭義単調性 (T.olt_P_b)

**主張** $`b_1\prec b_2`$ ならば、任意の $`a\in\mathbb{N}`$, $`c_1,c_2\in\mathrm{Three}`$ に対し
$`\mathsf{P}(a,b_1,c_1)\prec\mathsf{P}(a,b_2,c_2)`$。

**証明** [(T.olt_P_P)](#t-olt_P_P) の右辺第 2 選言 $`a=a \wedge b_1\prec b_2`$ が成立する。∎

<a id="t-olt_P_c"></a>
### 定理 後続和についての狭義単調性 (T.olt_P_c)

**主張** $`c_1\prec c_2`$ ならば、任意の $`a\in\mathbb{N}`$, $`b\in\mathrm{Three}`$ に対し
$`\mathsf{P}(a,b,c_1)\prec\mathsf{P}(a,b,c_2)`$。

**証明** [(T.olt_P_P)](#t-olt_P_P) の右辺第 3 選言 $`a=a \wedge b=b \wedge c_1\prec c_2`$ が成立する。∎

## 翻訳 $`\mathrm{tr} : \mathrm{PairSeq}\to\mathrm{Three}`$

<a id="d-translate"></a>
### 定義 翻訳 (D.translate)

ペア列を項へ写す写像 $`\mathrm{tr}`$ を次式で定義する。空列は $`\mathsf{Z}`$ に、
先頭対 $`p`$ をもつ列 $`p\mathbin{::}L`$ は添字 $`\pi_1 p`$ の主要項に写り、
その引数は $`\mathrm{tw}_{\pi_0 p}L`$（$`L`$ の先頭から行 0 の値が $`\pi_0 p`$ より真に大きい対が続く極大な前部分列）の翻訳、
後続和は $`\mathrm{dw}_{\pi_0 p}L`$（その残り）の翻訳である。

```math
\mathrm{tr}([]) := \mathsf{Z},\qquad
\mathrm{tr}(p \mathbin{::} L) := \mathsf{P}\bigl(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p} L),\ \mathrm{tr}(\mathrm{dw}_{\pi_0 p} L)\bigr).
```

この再帰は $`\lvert M\rvert`$ に関して整礎である。実際
$`\mathrm{tw}_{\pi_0 p} L`$ は $`L`$ の部分列だから $`\lvert \mathrm{tw}_{\pi_0 p} L\rvert \le \lvert L\rvert \lt \lvert p\mathbin{::}L\rvert`$ であり、
また $`\lvert \mathrm{dw}_{\pi_0 p} L\rvert \le \lvert L\rvert \lt \lvert p\mathbin{::}L\rvert`$ である
（標準ライブラリの `List.takeWhile_sublist`, `List.length_dropWhile_le`）。

**注（$`\mathrm{tr}`$ の再帰に伴う帰納法原理）**
ペア列の述語 $`\Phi`$ が次の 2 条件をみたすとする。

1. $`\Phi([])`$。
2. 任意の対 $`p`$ とペア列 $`L`$ について、$`\Phi(\mathrm{tw}_{\pi_0 p}L)`$ かつ $`\Phi(\mathrm{dw}_{\pi_0 p}L)`$ ならば $`\Phi(p\mathbin{::}L)`$。

このとき任意のペア列 $`M`$ について $`\Phi(M)`$ が成り立つ。
これは $`\lvert M\rvert`$ に関する強帰納法である：$`\lvert M\rvert=0`$ なら $`M=[]`$ で条件 1、
$`M=p\mathbin{::}L`$ なら $`\mathrm{tw}_{\pi_0 p}L`$ と $`\mathrm{dw}_{\pi_0 p}L`$ の長さは
上に見たとおり $`\lvert M\rvert`$ より真に小さいので強帰納法の仮定が使え、条件 2 が適用できる。
Lean ではこの原理は `translate.induct` として自動生成される。
以下で「$`\mathrm{tr}`$ の再帰に沿う帰納法」と書いたときはこの原理を指す。

<a id="t-lead_translate"></a>
### 定理 翻訳の先頭添字 (T.lead_translate)

**主張** 任意のペア列 $`M`$ に対し
```math
\mathrm{lead}(\mathrm{tr}\,M) = \begin{cases} 0 & (M=[])\cr \pi_1 p & (M = p\mathbin{::}L). \end{cases}
```

**証明** $`M`$ の構成子で場合分けする。
$`M=[]`$ のとき [(D.translate)](#d-translate) より $`\mathrm{tr}\,M=\mathsf{Z}`$ であり、
[(T.lead_Z)](#t-lead_Z) より $`\mathrm{lead}\,\mathsf{Z}=0`$。
$`M=p\mathbin{::}L`$ のとき [(D.translate)](#d-translate) より
$`\mathrm{tr}\,M = \mathsf{P}(\pi_1 p, \cdot, \cdot)`$ であり、[(T.lead_P)](#t-lead_P) よりその $`\mathrm{lead}`$ は $`\pi_1 p`$。∎

### 計算例

以下は Lean 側で無名の `example` として検証されている等式である
（いずれも [(D.translate)](#d-translate) の展開のみで計算できる）。

1. $`\mathrm{tr}[(0,0)] = \mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$。
   先頭対 $`p=(0,0)`$、残り $`L=[]`$。$`\mathrm{tw}_0[]=[]`$, $`\mathrm{dw}_0[]=[]`$、$`\mathrm{tr}[]=\mathsf{Z}`$、$`\pi_1 p=0`$。
2. $`\mathrm{tr}[(0,0),(1,0)] = \mathsf{P}(0,\mathsf{P}(0,\mathsf{Z},\mathsf{Z}),\mathsf{Z})`$、すなわち $`p_0(p_0(0))`$。
   $`p=(0,0)`$, $`L=[(1,0)]`$。$`0\lt 1`$ なので $`\mathrm{tw}_0 L=[(1,0)]`$, $`\mathrm{dw}_0 L=[]`$。
   1 より $`\mathrm{tr}[(1,0)]=\mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$。
3. $`\mathrm{tr}[(0,0),(1,1)] = \mathsf{P}(0,\mathsf{P}(1,\mathsf{Z},\mathsf{Z}),\mathsf{Z})`$、すなわち $`p_0(p_1(0))`$。
   $`p=(0,0)`$, $`L=[(1,1)]`$。$`0\lt 1`$ なので $`\mathrm{tw}_0L=[(1,1)]`$, $`\mathrm{dw}_0L=[]`$。
   $`\mathrm{tr}[(1,1)]`$ は先頭対 $`(1,1)`$、残り $`[]`$ より $`\mathsf{P}(1,\mathsf{Z},\mathsf{Z})`$。
4. $`\mathrm{tr}[(0,0),(1,0),(1,0)] = \mathsf{P}(0,\mathsf{P}(0,\mathsf{Z},\mathsf{P}(0,\mathsf{Z},\mathsf{Z})),\mathsf{Z})`$、すなわち $`p_0(p_0(0)+p_0(0))`$。
   $`p=(0,0)`$, $`L=[(1,0),(1,0)]`$：どちらも第 0 成分が $`1\gt 0`$ なので $`\mathrm{tw}_0L=L`$, $`\mathrm{dw}_0L=[]`$。
   次に $`\mathrm{tr}[(1,0),(1,0)]`$：先頭 $`(1,0)`$、残り $`[(1,0)]`$ の第 0 成分は $`1`$ で $`1\lt 1`$ は偽だから
   $`\mathrm{tw}_1[(1,0)]=[]`$, $`\mathrm{dw}_1[(1,0)]=[(1,0)]`$。よって $`\mathsf{P}(0,\mathsf{Z},\mathsf{P}(0,\mathsf{Z},\mathsf{Z}))`$。
5. $`\mathrm{tr}[(0,0),(1,1),(2,2),(3,3)] = \mathsf{P}(0,\mathsf{P}(1,\mathsf{P}(2,\mathsf{P}(3,\mathsf{Z},\mathsf{Z}),\mathsf{Z}),\mathsf{Z}),\mathsf{Z})`$、
   すなわち $`p_0(p_1(p_2(p_3(0))))`$。
   $`p=(0,0)`$, $`L=[(1,1),(2,2),(3,3)]`$：$`0\lt 1,0\lt 2,0\lt 3`$ より $`\mathrm{tw}_0L=L`$, $`\mathrm{dw}_0L=[]`$。
   $`\mathrm{tr}[(1,1),(2,2),(3,3)]`$：$`1\lt 2,1\lt 3`$ より $`\mathrm{tw}_1[(2,2),(3,3)]=[(2,2),(3,3)]`$, $`\mathrm{dw}_1=[]`$。
   $`\mathrm{tr}[(2,2),(3,3)]`$：$`2\lt 3`$ より $`\mathrm{tw}_2[(3,3)]=[(3,3)]`$, $`\mathrm{dw}_2=[]`$。
   $`\mathrm{tr}[(3,3)] = \mathsf{P}(3,\mathsf{Z},\mathsf{Z})`$。これらを内側から代入する。

### リスト操作の補助補題

ここで用いる標準ライブラリの事実を挙げる（$`p`$ は要素上の述語、$`l,l_1,l_2`$ はリスト）。

- `List.takeWhile_append`：
  $`(l_1\mathbin{+\!\!+}l_2).\mathrm{takeWhile}\,p = \begin{cases} l_1 \mathbin{+\!\!+} l_2.\mathrm{takeWhile}\,p & (\lvert l_1.\mathrm{takeWhile}\,p\rvert = \lvert l_1\rvert)\cr l_1.\mathrm{takeWhile}\,p & (\text{それ以外}) \end{cases}`$
- `List.dropWhile_append`：
  $`(l_1\mathbin{+\!\!+}l_2).\mathrm{dropWhile}\,p = \begin{cases} l_2.\mathrm{dropWhile}\,p & (l_1.\mathrm{dropWhile}\,p = [])\cr l_1.\mathrm{dropWhile}\,p \mathbin{+\!\!+} l_2 & (\text{それ以外}) \end{cases}`$
- `List.takeWhile_eq_self_iff`：$`l.\mathrm{takeWhile}\,p = l \iff \forall x\in l,\ p\,x`$
- `List.dropWhile_eq_nil_iff`：$`l.\mathrm{dropWhile}\,p = [] \iff \forall x\in l,\ p\,x`$
- `List.takeWhile_sublist`：$`l.\mathrm{takeWhile}\,p`$ は $`l`$ の部分列である
- `List.Sublist.eq_of_length`：部分列であって長さが等しいリストは元のリストに等しい
- `List.length_dropWhile_le`：$`\lvert l.\mathrm{dropWhile}\,p\rvert \le \lvert l\rvert`$
- `List.ext_getElem`：長さが等しくすべての添字で要素が等しい 2 つのリストは等しい
- `List.getElem_range'`：$`\mathrm{range}'(a,m)`$ の第 $`i`$ 要素は $`a+i`$ である（$`i\lt m`$）
- `List.range'_succ`：$`\mathrm{range}'(a,m+1) = a \mathbin{::} \mathrm{range}'(a+1,m)`$
- `List.range'_append`：$`\mathrm{range}'(a,m) \mathbin{+\!\!+} \mathrm{range}'(a+m,k) = \mathrm{range}'(a,m+k)`$

<a id="t-takeWhile_append_all"></a>
### 定理 全体が述語をみたす前部の takeWhile (T.takeWhile_append_all)

**主張** $`\forall x\in xs,\ p\,x`$ ならば
$`(xs\mathbin{+\!\!+}ys).\mathrm{takeWhile}\,p = xs \mathbin{+\!\!+} ys.\mathrm{takeWhile}\,p`$。

**証明** 仮定と `List.takeWhile_eq_self_iff` より $`xs.\mathrm{takeWhile}\,p = xs`$、
とくに $`\lvert xs.\mathrm{takeWhile}\,p\rvert = \lvert xs\rvert`$。
よって `List.takeWhile_append` の第 1 の場合が適用され、主張の等式を得る。∎

<a id="t-dropWhile_append_all"></a>
### 定理 全体が述語をみたす前部の dropWhile (T.dropWhile_append_all)

**主張** $`\forall x\in xs,\ p\,x`$ ならば
$`(xs\mathbin{+\!\!+}ys).\mathrm{dropWhile}\,p = ys.\mathrm{dropWhile}\,p`$。

**証明** 仮定と `List.dropWhile_eq_nil_iff` より $`xs.\mathrm{dropWhile}\,p = []`$。
よって `List.dropWhile_append` の第 1 の場合が適用され、主張の等式を得る。∎

<a id="t-takeWhile_append_not"></a>
### 定理 述語を破る要素を含む前部の takeWhile (T.takeWhile_append_not)

**主張** $`x\in xs`$ かつ $`\neg p\,x`$ ならば
$`(xs\mathbin{+\!\!+}ys).\mathrm{takeWhile}\,p = xs.\mathrm{takeWhile}\,p`$。

**証明** `List.takeWhile_append` の第 2 の場合、すなわち
$`\lvert xs.\mathrm{takeWhile}\,p\rvert \ne \lvert xs\rvert`$ であることを示せばよい。
もし $`\lvert xs.\mathrm{takeWhile}\,p\rvert = \lvert xs\rvert`$ なら、
`List.takeWhile_sublist` より $`xs.\mathrm{takeWhile}\,p`$ は $`xs`$ の部分列で長さが等しいから、
`List.Sublist.eq_of_length` により $`xs.\mathrm{takeWhile}\,p = xs`$。
すると `List.takeWhile_eq_self_iff` より $`\forall y\in xs,\ p\,y`$ となり、
$`x\in xs`$ に適用して $`p\,x`$ を得るが、これは $`\neg p\,x`$ に矛盾する。∎

<a id="t-dropWhile_append_not"></a>
### 定理 述語を破る要素を含む前部の dropWhile (T.dropWhile_append_not)

**主張** $`x\in xs`$ かつ $`\neg p\,x`$ ならば
$`(xs\mathbin{+\!\!+}ys).\mathrm{dropWhile}\,p = xs.\mathrm{dropWhile}\,p \mathbin{+\!\!+} ys`$。

**証明** `List.dropWhile_append` の第 2 の場合、すなわち $`xs.\mathrm{dropWhile}\,p \ne []`$ を示せばよい。
もし $`xs.\mathrm{dropWhile}\,p = []`$ なら `List.dropWhile_eq_nil_iff` より $`\forall y\in xs,\ p\,y`$ となり、
$`x\in xs`$ に適用して $`p\,x`$ を得るが、これは $`\neg p\,x`$ に矛盾する。∎

<a id="t-drop_eq_map_getD"></a>
### 定理 接尾列の添字表示 (T.drop_eq_map_getD)

**主張** 任意のリスト $`xs`$、$`a\in\mathbb{N}`$、既定値 $`d`$ に対し
```math
\mathrm{drop}\,a\,xs = \mathrm{map}\ (\lambda i.\ xs.\mathrm{getD}\,i\,d)\ \mathrm{range}'(a,\ \lvert xs\rvert - a).
```

**証明** `List.ext_getElem` により、長さの一致と各添字での要素の一致を示す。

- 長さ：左辺の長さは $`\lvert xs\rvert - a`$。右辺は $`\mathrm{range}'(a,\lvert xs\rvert-a)`$ の長さ、
  すなわち $`\lvert xs\rvert - a`$ である（$`\mathrm{map}`$ は長さを変えない）。
- 要素：$`i \lt \lvert xs\rvert - a`$ とする。左辺の第 $`i`$ 要素は $`xs`$ の第 $`a+i`$ 要素である。
  右辺の第 $`i`$ 要素は、`List.getElem_range'` より $`\mathrm{range}'(a,\lvert xs\rvert-a)`$ の第 $`i`$ 要素が $`a+i`$ であるから、
  $`xs.\mathrm{getD}\,(a+i)\,d`$ である。
  $`i\lt \lvert xs\rvert-a`$ より $`a+i\lt \lvert xs\rvert`$ なので、$`xs.\mathrm{getD}\,(a+i)\,d`$ は $`xs`$ の第 $`a+i`$ 要素に等しい。
  よって両辺の第 $`i`$ 要素は一致する。∎

## 親子関係の行 0 単調性

行 0 の祖先鎖に沿って行 0 の値は真に増加する。これは [(T.oper_bad_blocks)](#t-oper_bad_blocks) の
条件 3・条件 4、すなわちコピーされるブロックの根 $`(v_0,w_0)`$ の行 0 の値が、
ブロックの他のすべての要素および落とされる最終対の行 0 の値より真に小さいことの根拠である。

<a id="t-nextrel0_entry0_less"></a>
### 定理 nextrel0 は行 0 を真に増やす (T.nextrel0_entry0_less)

**主張** $`\mathrm{nextrel0}\,M\,j_0\,j_1`$（[(D.nextrel0)](Def.md#d-nextrel0)）ならば $`M_{0,j_0} \lt M_{0,j_1}`$。

**証明** [(D.nextrel0)](Def.md#d-nextrel0) は 5 つの連言
```math
j_0<\lvert M\rvert,\quad j_1<\lvert M\rvert,\quad j_0<j_1,\quad M_{0,j_0}<M_{0,j_1},\quad
 \forall j,\ (j_0<j<j_1 \to M_{0,j_1}\le M_{0,j})
```
であり、その第 4 成分が主張そのものである。∎

<a id="t-le0_entry0_mono"></a>
### 定理 le0 は行 0 を弱く増やす (T.le0_entry0_mono)

**主張** $`\mathrm{le0}\,M\,j_0\,j_1`$（[(D.le0)](Def.md#d-le0)）ならば $`M_{0,j_0} \le M_{0,j_1}`$。

**証明** [(D.le0)](Def.md#d-le0) の第 3 成分は反射推移閉包
$`\mathrm{ReflTransGen}(\mathrm{nextrel0}\,M)\,j_0\,j_1`$ である。この導出に関する帰納法を行う。
$`j_0`$ を固定し、帰納法の述語を
```math
\Phi(b) :\equiv M_{0,j_0} \le M_{0,b}
```
とする（$`b`$ は $`j_0`$ から到達可能な添字）。

- 基底段（`refl`、$`b=j_0`$）：$`M_{0,j_0}\le M_{0,j_0}`$ であり $`\Phi(j_0)`$。
- 帰納段（`tail`）：$`\mathrm{ReflTransGen}(\mathrm{nextrel0}\,M)\,j_0\,y`$ と $`\mathrm{nextrel0}\,M\,y\,z`$ が与えられ、
  帰納法の仮定は $`\Phi(y)`$、すなわち $`M_{0,j_0}\le M_{0,y}`$ である。
  [(T.nextrel0_entry0_less)](#t-nextrel0_entry0_less) より $`M_{0,y}\lt M_{0,z}`$ であるから
  $`M_{0,j_0}\le M_{0,y}\le M_{0,z}`$、すなわち $`\Phi(z)`$。∎

<a id="t-nextrel0_index_less"></a>
### 定理 nextrel0 は添字を真に増やす (T.nextrel0_index_less)

**主張** $`\mathrm{nextrel0}\,M\,a\,b`$ ならば $`a\lt b`$。

**証明** [(D.nextrel0)](Def.md#d-nextrel0) の第 3 成分が主張そのものである。∎

<a id="t-nextrel0_rtrancl_index_le"></a>
### 定理 行 0 鎖は添字を弱く増やす (T.nextrel0_rtrancl_index_le)

**主張** $`\mathrm{ReflTransGen}(\mathrm{nextrel0}\,M)\,a\,b`$ ならば $`a\le b`$。

**証明** 反射推移閉包の導出に関する帰納法。$`a`$ を固定し、帰納法の述語を
```math
\Phi(b) :\equiv a \le b
```
とする。

- 基底段（`refl`、$`b=a`$）：$`a\le a`$。
- 帰納段（`tail`）：$`\mathrm{ReflTransGen}(\mathrm{nextrel0}\,M)\,a\,y`$ と $`\mathrm{nextrel0}\,M\,y\,z`$ が与えられ、
  帰納法の仮定は $`\Phi(y)`$、すなわち $`a\le y`$。
  [(T.nextrel0_index_less)](#t-nextrel0_index_less) より $`y\lt z`$ だから $`a\le y\le z`$、すなわち $`\Phi(z)`$。∎

<a id="t-le0_interval_gt"></a>
### 定理 区間補題 (T.le0_interval_gt)

**主張** $`\mathrm{ReflTransGen}(\mathrm{nextrel0}\,M)\,j_0\,j_1`$ ならば
```math
\forall k,\ (j_0<k \wedge k\le j_1)\ \to\ M_{0,j_0} < M_{0,k}.
```

すなわち、鎖の通過点だけでなく区間 $`(j_0,j_1]`$ のすべての添字で行 0 の値は $`M_{0,j_0}`$ より真に大きい。

**証明** 反射推移閉包の導出に関する帰納法。$`j_0`$ を固定し、帰納法の述語を
```math
\Phi(b) :\equiv \forall k,\ (j_0<k \wedge k\le b)\ \to\ M_{0,j_0} < M_{0,k}
```
とする。

- 基底段（`refl`、$`b=j_0`$）：$`j_0\lt k`$ かつ $`k\le j_0`$ をみたす $`k`$ は存在しないので、前件が常に偽であり $`\Phi(j_0)`$ が成り立つ。
- 帰納段（`tail`）：$`h_1 : \mathrm{ReflTransGen}(\mathrm{nextrel0}\,M)\,j_0\,y`$ と
  $`h_2 : \mathrm{nextrel0}\,M\,y\,z`$ が与えられ、帰納法の仮定は $`\Phi(y)`$ である。$`\Phi(z)`$ を示す。

  まず次の 3 つを用意する。
  1. $`M_{0,y}\lt M_{0,z}`$（[(T.nextrel0_entry0_less)](#t-nextrel0_entry0_less) を $`h_2`$ に適用）。
  2. $`j_0\le y`$（[(T.nextrel0_rtrancl_index_le)](#t-nextrel0_rtrancl_index_le) を $`h_1`$ に適用）。
  3. $`M_{0,j_0}\le M_{0,y}`$。実際、$`j_0\lt y`$ なら $`\Phi(y)`$ を $`k:=y`$ に適用して $`M_{0,j_0}\lt M_{0,y}`$ を得る。
     $`j_0\lt y`$ でないなら 2 と合わせて $`j_0=y`$ であり、両辺は同じ値である。

  さて $`k`$ を $`j_0\lt k`$ かつ $`k\le z`$ をみたす任意の添字とする。$`y`$ と $`k`$ の大小で分ける。
  - $`k\le y`$ のとき：帰納法の仮定 $`\Phi(y)`$ を $`k`$ に適用して $`M_{0,j_0}\lt M_{0,k}`$。
  - $`y\lt k`$ かつ $`k=z`$ のとき：3 と 1 より $`M_{0,j_0}\le M_{0,y}\lt M_{0,z}=M_{0,k}`$。
  - $`y\lt k`$ かつ $`k\lt z`$ のとき：[(D.nextrel0)](Def.md#d-nextrel0) の第 5 成分を $`h_2`$ と $`k`$ に適用すると
    $`M_{0,z}\le M_{0,k}`$ を得る。3 と 1 と合わせて
    $`M_{0,j_0}\le M_{0,y} \lt M_{0,z} \le M_{0,k}`$。

  いずれの場合も $`M_{0,j_0}\lt M_{0,k}`$ であり、$`\Phi(z)`$ が成り立つ。∎

## $`\mathrm{tr}`$ の形状補題

<a id="t-translate_single_tree"></a>
### 定理 単一木 (T.translate_single_tree)

**主張** 対 $`p`$ とペア列 $`R`$ が $`\forall x\in R,\ \pi_0 p \lt \pi_0 x`$ をみたすならば
```math
\mathrm{tr}(p\mathbin{::}R) = \mathsf{P}(\pi_1 p,\ \mathrm{tr}\,R,\ \mathsf{Z}).
```

**証明** 仮定と `List.takeWhile_eq_self_iff` より $`\mathrm{tw}_{\pi_0 p}R = R`$、
仮定と `List.dropWhile_eq_nil_iff` より $`\mathrm{dw}_{\pi_0 p}R = []`$。
[(D.translate)](#d-translate) の第 2 式にこれらを代入し、さらに $`\mathrm{tr}([])=\mathsf{Z}`$ を用いると主張を得る。∎

<a id="t-translate_block_append"></a>
### 定理 ブロック連結の翻訳 (T.translate_block_append)

**主張** $`v_0,w_0\in\mathbb{N}`$、ペア列 $`R,T`$ が
```math
\forall x\in R,\ v_0<\pi_0 x, \qquad T=[]\ \vee\ \neg\bigl(v_0 < \pi_0(\mathrm{headI}\,T)\bigr)
```
をみたすならば
```math
\mathrm{tr}\bigl(((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}T\bigr) = \mathsf{P}(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T).
```

**証明** $`((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}T = (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}T)`$ であるから、
[(D.translate)](#d-translate) の第 2 式より
```math
\mathrm{tr}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}T)\bigr)
 = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(\mathrm{tw}_{v_0}(R\mathbin{+\!\!+}T)),\ \mathrm{tr}(\mathrm{dw}_{v_0}(R\mathbin{+\!\!+}T))\bigr).
```
よって $`\mathrm{tw}_{v_0}(R\mathbin{+\!\!+}T)=R`$ と $`\mathrm{dw}_{v_0}(R\mathbin{+\!\!+}T)=T`$ を示せばよい。$`T`$ の形で分ける。

- $`T=[]`$ のとき：$`R\mathbin{+\!\!+}[]=R`$ であり、第 1 の仮定と `List.takeWhile_eq_self_iff` から
  $`\mathrm{tw}_{v_0}R=R`$、`List.dropWhile_eq_nil_iff` から $`\mathrm{dw}_{v_0}R=[]=T`$。
- $`T=t\mathbin{::}ts`$ のとき：$`T\ne[]`$ だから第 2 の仮定の第 1 選言は成立せず、
  $`\neg(v_0\lt \pi_0(\mathrm{headI}\,T))`$、すなわち $`\neg(v_0\lt \pi_0 t)`$ が成り立つ。
  [(T.takeWhile_append_all)](#t-takeWhile_append_all) より
  $`\mathrm{tw}_{v_0}(R\mathbin{+\!\!+}T) = R \mathbin{+\!\!+} \mathrm{tw}_{v_0}T`$ であり、
  $`T`$ の先頭 $`t`$ が述語をみたさないので $`\mathrm{tw}_{v_0}T=[]`$、したがって $`\mathrm{tw}_{v_0}(R\mathbin{+\!\!+}T)=R`$。
  また [(T.dropWhile_append_all)](#t-dropWhile_append_all) より
  $`\mathrm{dw}_{v_0}(R\mathbin{+\!\!+}T) = \mathrm{dw}_{v_0}T`$ であり、先頭が述語をみたさないので
  $`\mathrm{dw}_{v_0}T = T`$。∎

<a id="t-translate_shift"></a>
### 定理 行 0 平行移動不変性 (T.translate_shift)

**主張** $`d\in\mathbb{N}`$ とし $`\sigma_d(p) := (\pi_0 p + d,\ \pi_1 p)`$ とおく。任意のペア列 $`M`$ に対し
```math
\mathrm{tr}(\mathrm{map}\,\sigma_d\,M) = \mathrm{tr}\,M.
```

**証明** $`\mathrm{tr}`$ の再帰に沿う帰納法（[(D.translate)](#d-translate) の注）。帰納法の述語は
```math
\Phi(M) :\equiv \mathrm{tr}(\mathrm{map}\,\sigma_d\,M) = \mathrm{tr}\,M.
```

- 基底段 $`M=[]`$：$`\mathrm{map}\,\sigma_d\,[] = []`$ であり、両辺とも $`\mathsf{Z}`$。
- 帰納段 $`M=p\mathbin{::}L`$：帰納法の仮定は
  $`\Phi(\mathrm{tw}_{\pi_0 p}L)`$ と $`\Phi(\mathrm{dw}_{\pi_0 p}L)`$ である。

  まず $`\mathrm{map}\,\sigma_d\,(p\mathbin{::}L) = \sigma_d p \mathbin{::} \mathrm{map}\,\sigma_d\,L`$ であり、
  $`\pi_0(\sigma_d p) = \pi_0 p + d`$、$`\pi_1(\sigma_d p) = \pi_1 p`$。よって [(D.translate)](#d-translate) より
  ```math
  \mathrm{tr}(\mathrm{map}\,\sigma_d\,(p\mathbin{::}L))
   = \mathsf{P}\bigl(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p+d}(\mathrm{map}\,\sigma_d L)),\
      \mathrm{tr}(\mathrm{dw}_{\pi_0 p+d}(\mathrm{map}\,\sigma_d L))\bigr).
  ```

  次に述語の対応を見る。任意の対 $`r`$ に対し
  ```math
  \bigl(\lambda q.\ \pi_0 p + d < \pi_0 q\bigr)(\sigma_d r)
   \ \iff\ \pi_0 p + d < \pi_0 r + d \ \iff\ \pi_0 p < \pi_0 r
  ```
  であるから、述語 $`(\lambda q.\ \pi_0 p+d\lt \pi_0 q)\circ\sigma_d`$ は $`(\lambda r.\ \pi_0 p\lt \pi_0 r)`$ に等しい。
  標準ライブラリの
  `List.takeWhile_map`（$`(\mathrm{map}\,f\,l).\mathrm{takeWhile}\,q = \mathrm{map}\,f\,(l.\mathrm{takeWhile}(q\circ f))`$）
  と `List.dropWhile_map`（$`(\mathrm{map}\,f\,l).\mathrm{dropWhile}\,q = \mathrm{map}\,f\,(l.\mathrm{dropWhile}(q\circ f))`$）より
  ```math
  \mathrm{tw}_{\pi_0 p+d}(\mathrm{map}\,\sigma_d L) = \mathrm{map}\,\sigma_d\,(\mathrm{tw}_{\pi_0 p}L),\qquad
    \mathrm{dw}_{\pi_0 p+d}(\mathrm{map}\,\sigma_d L) = \mathrm{map}\,\sigma_d\,(\mathrm{dw}_{\pi_0 p}L).
  ```
  ここで帰納法の仮定 $`\Phi(\mathrm{tw}_{\pi_0 p}L)`$、$`\Phi(\mathrm{dw}_{\pi_0 p}L)`$ を用いると
  ```math
  \mathrm{tr}(\mathrm{map}\,\sigma_d(\mathrm{tw}_{\pi_0 p}L)) = \mathrm{tr}(\mathrm{tw}_{\pi_0 p}L),\qquad
    \mathrm{tr}(\mathrm{map}\,\sigma_d(\mathrm{dw}_{\pi_0 p}L)) = \mathrm{tr}(\mathrm{dw}_{\pi_0 p}L).
  ```
  したがって
  $`\mathrm{tr}(\mathrm{map}\,\sigma_d(p\mathbin{::}L)) = \mathsf{P}(\pi_1 p, \mathrm{tr}(\mathrm{tw}_{\pi_0 p}L), \mathrm{tr}(\mathrm{dw}_{\pi_0 p}L)) = \mathrm{tr}(p\mathbin{::}L)`$、すなわち $`\Phi(p\mathbin{::}L)`$。∎

この不変性が成り立つのは、[(D.translate)](#d-translate) が行 0 の値を比較 $`\pi_0 p\lt \pi_0 q`$ の形でのみ用い
（$`\pi_0 p+d\lt \pi_0 q+d \iff \pi_0 p\lt \pi_0 q`$ ゆえ平行移動で不変）、行 1 の値 $`\pi_1 p`$ を
そのまま添字に用いるからである。$`M[n]`$ の第 3 分岐で作られる昇順コピーは基準ブロックと
行 0 の一様な平行移動だけ異なるので、すべて同一の項に翻訳される。

## 文脈合同 (BADCTX)

<a id="t-translate_ctx_cong"></a>
### 定理 文脈合同 (T.translate_ctx_cong)

**主張** 対 $`z_1,z_2`$ とペア列 $`T_1,T_2`$ が

- $`\text{base} : \mathrm{tr}(z_1\mathbin{::}T_1) \prec \mathrm{tr}(z_2\mathbin{::}T_2)`$
- $`\text{root} : \pi_0 z_1 = \pi_0 z_2`$
- $`r_1 : \forall x\in T_1,\ \pi_0 z_1 \le \pi_0 x`$
- $`r_2 : \forall x\in T_2,\ \pi_0 z_2 \le \pi_0 x`$

をみたすとする。このとき任意のペア列 $`G`$ に対し
```math
\mathrm{tr}(G\mathbin{+\!\!+}z_1\mathbin{::}T_1) \prec \mathrm{tr}(G\mathbin{+\!\!+}z_2\mathbin{::}T_2).
```

**証明** $`z_1,z_2,T_1,T_2`$ と 4 つの仮定を固定し、$`\lvert G\rvert`$ に関する強帰納法を行う。帰納法の述語は
```math
\Phi(G) :\equiv \mathrm{tr}(G\mathbin{+\!\!+}z_1\mathbin{::}T_1) \prec \mathrm{tr}(G\mathbin{+\!\!+}z_2\mathbin{::}T_2)
```
であり、$`\lvert G'\rvert\lt \lvert G\rvert`$ なるすべての $`G'`$ について $`\Phi(G')`$ を仮定して $`\Phi(G)`$ を示す。
$`G`$ の形で分ける。

**$`G=[]`$ のとき。** $`[]\mathbin{+\!\!+}z_i\mathbin{::}T_i = z_i\mathbin{::}T_i`$ なので、主張は base そのものである。

**$`G=g\mathbin{::}G'`$ のとき。** さらに 3 つの場合に分ける。

- **場合 (a)** $`\neg(\forall x\in G',\ \pi_0 g\lt \pi_0 x)`$：$`x\in G'`$ で $`\neg(\pi_0 g\lt \pi_0 x)`$ なるものを取る。
  [(T.takeWhile_append_not)](#t-takeWhile_append_not) と [(T.dropWhile_append_not)](#t-dropWhile_append_not) を
  $`xs:=G'`$, $`ys:=z_i\mathbin{::}T_i`$ に適用して（$`i=1,2`$）
  ```math
  \mathrm{tw}_{\pi_0 g}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i) = \mathrm{tw}_{\pi_0 g}G',\qquad
    \mathrm{dw}_{\pi_0 g}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i) = (\mathrm{dw}_{\pi_0 g}G')\mathbin{+\!\!+}z_i\mathbin{::}T_i.
  ```
  よって [(D.translate)](#d-translate) より
  ```math
  \mathrm{tr}(g\mathbin{::}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i))
   = \mathsf{P}\bigl(\pi_1 g,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 g}G'),\
     \mathrm{tr}((\mathrm{dw}_{\pi_0 g}G')\mathbin{+\!\!+}z_i\mathbin{::}T_i)\bigr)
  ```
  であり、$`i=1,2`$ で添字と引数が一致する。
  $`\lvert \mathrm{dw}_{\pi_0 g}G'\rvert \le \lvert G'\rvert \lt \lvert g\mathbin{::}G'\rvert`$ だから
  帰納法の仮定 $`\Phi(\mathrm{dw}_{\pi_0 g}G')`$ が使え、後続和どうしが
  ```math
  \mathrm{tr}((\mathrm{dw}_{\pi_0 g}G')\mathbin{+\!\!+}z_1\mathbin{::}T_1)
   \prec \mathrm{tr}((\mathrm{dw}_{\pi_0 g}G')\mathbin{+\!\!+}z_2\mathbin{::}T_2)
  ```
  をみたす。[(T.olt_P_c)](#t-olt_P_c) より $`\Phi(g\mathbin{::}G')`$ を得る。
- **場合 (b)** $`\forall x\in G',\ \pi_0 g\lt \pi_0 x`$ かつ $`\pi_0 g\lt \pi_0 z_1`$：
  このとき $`G'\mathbin{+\!\!+}z_1\mathbin{::}T_1`$ の全要素 $`x`$ が $`\pi_0 g\lt \pi_0 x`$ をみたす。実際、
  $`x\in G'`$ なら仮定より、$`x=z_1`$ なら $`\pi_0 g\lt \pi_0 z_1`$ より、$`x\in T_1`$ なら
  $`r_1`$ から $`\pi_0 g\lt \pi_0 z_1\le\pi_0 x`$ である。
  root より $`\pi_0 z_2=\pi_0 z_1`$ なので $`\pi_0 g\lt \pi_0 z_2`$ でもあり、
  $`G'\mathbin{+\!\!+}z_2\mathbin{::}T_2`$ の全要素 $`x`$ も $`\pi_0 g\lt \pi_0 x`$ をみたす：
  $`x\in G'`$ なら仮定より、$`x=z_2`$ なら $`\pi_0 g\lt \pi_0 z_2`$ より、$`x\in T_2`$ なら
  $`r_2`$ から $`\pi_0 g\lt \pi_0 z_2\le\pi_0 x`$ である。
  よって [(T.translate_single_tree)](#t-translate_single_tree) を $`p:=g`$ に適用して（$`i=1,2`$）
  ```math
  \mathrm{tr}(g\mathbin{::}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i))
   = \mathsf{P}\bigl(\pi_1 g,\ \mathrm{tr}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i),\ \mathsf{Z}\bigr).
  ```
  $`\lvert G'\rvert\lt \lvert g\mathbin{::}G'\rvert`$ だから帰納法の仮定 $`\Phi(G')`$ が使え、
  [(T.olt_P_b)](#t-olt_P_b) より $`\Phi(g\mathbin{::}G')`$ を得る。
- **場合 (c)** $`\forall x\in G',\ \pi_0 g\lt \pi_0 x`$ かつ $`\neg(\pi_0 g\lt \pi_0 z_1)`$：
  root より $`\neg(\pi_0 g\lt \pi_0 z_2)`$ でもある。
  [(T.takeWhile_append_all)](#t-takeWhile_append_all) より（$`i=1,2`$）
  ```math
  \mathrm{tw}_{\pi_0 g}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i)
   = G'\mathbin{+\!\!+}\mathrm{tw}_{\pi_0 g}(z_i\mathbin{::}T_i) = G'\mathbin{+\!\!+}[] = G'
  ```
  （先頭 $`z_i`$ が述語 $`\pi_0 g\lt \pi_0(\cdot)`$ をみたさないので $`\mathrm{tw}_{\pi_0 g}(z_i\mathbin{::}T_i)=[]`$）、
  [(T.dropWhile_append_all)](#t-dropWhile_append_all) より
  ```math
  \mathrm{dw}_{\pi_0 g}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i) = \mathrm{dw}_{\pi_0 g}(z_i\mathbin{::}T_i) = z_i\mathbin{::}T_i.
  ```
  よって [(D.translate)](#d-translate) より
  ```math
  \mathrm{tr}(g\mathbin{::}(G'\mathbin{+\!\!+}z_i\mathbin{::}T_i))
   = \mathsf{P}\bigl(\pi_1 g,\ \mathrm{tr}\,G',\ \mathrm{tr}(z_i\mathbin{::}T_i)\bigr)
  ```
  であり、添字と引数が $`i=1,2`$ で一致し、後続和どうしは base により
  $`\mathrm{tr}(z_1\mathbin{::}T_1)\prec\mathrm{tr}(z_2\mathbin{::}T_2)`$。
  [(T.olt_P_c)](#t-olt_P_c) より $`\Phi(g\mathbin{::}G')`$ を得る。

3 つの場合はすべてを尽くしており、いずれでも $`\Phi(g\mathbin{::}G')`$ が示された。
帰納法で用いた $`G'`$ と $`\mathrm{dw}_{\pi_0 g}G'`$ の長さはいずれも $`\lvert g\mathbin{::}G'\rvert`$ より真に小さいので、
強帰納法は正当である。∎

## 添字集合と $`M[n]`$ の分岐

<a id="d-sndSet"></a>
### 定義 行 1 の値の集合 (D.sndSet)

```math
\mathrm{sndSet}\,M := \pi_1[\,\{x \mid x\in M\}\,] \subseteq \mathbb{N},
```
すなわち $`M`$ に現れる対の第 1 成分全体のなす集合。

<a id="t-mem_sndSet"></a>
### 定理 $`\mathrm{sndSet}`$ の要素判定 (T.mem_sndSet)

**主張** $`y\in\mathrm{sndSet}\,M \iff \exists p\in M,\ \pi_1 p = y`$。

**証明** [(D.sndSet)](#d-sndSet) は写像 $`\pi_1`$ による集合 $`\{x\mid x\in M\}`$ の像であり、
像の要素であることの定義がそのまま右辺である。∎

<a id="t-sndSet_nil"></a>
### 定理 空列の $`\mathrm{sndSet}`$ (T.sndSet_nil)

**主張** $`\mathrm{sndSet}\,[] = \emptyset`$。

**証明** 任意の $`y`$ について、[(T.mem_sndSet)](#t-mem_sndSet) より
$`y\in\mathrm{sndSet}\,[]`$ は $`\exists p\in[],\ \pi_1 p=y`$ と同値であり、
空列は要素をもたないのでこれは偽。よって外延性より $`\mathrm{sndSet}\,[]=\emptyset`$。∎

<a id="t-sndSet_mono"></a>
### 定理 $`\mathrm{sndSet}`$ の単調性 (T.sndSet_mono)

**主張** $`\forall x\in M,\ x\in N`$ ならば $`\mathrm{sndSet}\,M \subseteq \mathrm{sndSet}\,N`$。

**証明** $`y\in\mathrm{sndSet}\,M`$ とする。[(T.mem_sndSet)](#t-mem_sndSet) より $`p\in M`$ で $`\pi_1 p=y`$ なるものが取れる。
仮定より $`p\in N`$ であり、再び [(T.mem_sndSet)](#t-mem_sndSet) より $`y\in\mathrm{sndSet}\,N`$。∎

<a id="t-idx1_le1"></a>
### 定理 $`\mathrm{idx1}\le 1`$ (T.idx1_le1)

**主張** 任意の $`M`$, $`j`$ に対し $`\mathrm{idx1}\,M\,j \le 1`$（[(D.idx1)](Def.md#d-idx1)）。

**証明** [(D.idx1)](Def.md#d-idx1) より $`\mathrm{idx1}\,M\,j`$ は $`0\lt M_{1,j}`$ のとき $`1`$、それ以外のとき $`0`$ である。
$`1\le 1`$ かつ $`0\le 1`$。∎

この補題により、[(D.oper)](Def.md#d-oper) の行 1 の増分 $`d_1`$（$`1\lt i_1`$ のときのみ非零）は常に $`0`$ である。

### $`M[n]`$ の分岐の展開

以下、$`j_1 := \lvert M\rvert-1`$（最終対の添字）、$`i_1 := \mathrm{idx1}\,M\,j_1`$ と書く。
$`\mathrm{Pred}`$ は [(D.Pred)](Def.md#d-Pred)、$`\mathrm{hasParent}`$ は [(D.hasParent)](Def.md#d-hasParent) である。
[(D.oper)](Def.md#d-oper) の 4 つの枝のうち、$`\mathrm{Pred}\,M`$ を返す 2 つの枝、すなわち
```math
\lvert M\rvert-1\ne0 \ \wedge\ \bigl(M_{0,j_1}=0\wedge M_{1,j_1}=0\bigr)
 \qquad\text{および}\qquad
 \lvert M\rvert-1\ne0 \ \wedge\ \neg\bigl(M_{0,j_1}=0\wedge M_{1,j_1}=0\bigr)\ \wedge\ \neg\,\mathrm{hasParent}\,M\,i_1\,j_1
```
の場合を**前者分岐**と呼び、最後の枝、すなわち
```math
\lvert M\rvert-1\ne0 \ \wedge\ \neg\bigl(M_{0,j_1}=0\wedge M_{1,j_1}=0\bigr)\ \wedge\ \mathrm{hasParent}\,M\,i_1\,j_1
```
の場合を**悪い分岐**と呼ぶ。

<a id="t-oper_eq_self_of_short"></a>
### 定理 長さ 1 以下では不動 (T.oper_eq_self_of_short)

**主張** $`\lvert M\rvert-1=0`$ ならば $`M[n]=M`$。

**証明** [(D.oper)](Def.md#d-oper) の最初の条件分岐 $`j_1=0`$ が真になり、その枝の値は $`M`$ である。∎

<a id="t-oper_eq_pred_of_zero"></a>
### 定理 前者分岐 1（最終対が $`(0,0)`$） (T.oper_eq_pred_of_zero)

**主張** $`\lvert M\rvert-1\ne 0`$ かつ $`M_{0,j_1}=0 \wedge M_{1,j_1}=0`$ ならば $`M[n]=\mathrm{Pred}\,M`$。

**証明** [(D.oper)](Def.md#d-oper) の最初の条件 $`j_1=0`$ は偽、次の条件
$`M_{0,j_1}=0\wedge M_{1,j_1}=0`$ は真であるから、その枝の値 $`\mathrm{Pred}\,M`$
（[(D.Pred)](Def.md#d-Pred)）が得られる。∎

<a id="t-oper_eq_pred_of_noParent"></a>
### 定理 前者分岐 2（親が一意に存在しない） (T.oper_eq_pred_of_noParent)

**主張** $`\lvert M\rvert-1\ne 0`$、$`\neg(M_{0,j_1}=0\wedge M_{1,j_1}=0)`$、
かつ $`\neg\,\mathrm{hasParent}\,M\,i_1\,j_1`$ ならば $`M[n]=\mathrm{Pred}\,M`$。

**証明** [(D.oper)](Def.md#d-oper) の最初の条件は偽、2 番目の条件も偽であり、
3 番目の条件 $`\neg\,\mathrm{hasParent}\,M\,i_1\,j_1`$
（[(D.hasParent)](Def.md#d-hasParent)）が真であるから、その枝の値 $`\mathrm{Pred}\,M`$ が得られる。∎

<a id="t-oper_bad_unfold"></a>
### 定理 悪い分岐の展開 (T.oper_bad_unfold)

**主張** $`\lvert M\rvert-1\ne 0`$、$`\neg(M_{0,j_1}=0\wedge M_{1,j_1}=0)`$、
かつ $`\mathrm{hasParent}\,M\,i_1\,j_1`$ ならば、$`j_0 := \mathrm{parent}\,M\,i_1\,j_1`$
（[(D.parent)](Def.md#d-parent)）、
$`d_0 := \bigl(0\lt i_1 \text{ ならば } M_{0,j_1}-M_{0,j_0},\ \text{さもなくば } 0\bigr)`$ として
```math
M[n] = \mathrm{take}\,j_0\,M \ \mathbin{+\!\!+}\
 \mathrm{flatMap}\Bigl(\lambda k.\ \mathrm{map}\bigl(\lambda j.\ (M_{0,j}+k\,d_0,\ M_{1,j})\bigr)\,\mathrm{range}'(j_0,\ j_1-j_0)\Bigr)\ \mathrm{range}(n).
```

**証明** [(D.oper)](Def.md#d-oper) の 3 つの条件分岐はそれぞれ偽・偽・偽（3 番目は
$`\neg\,\mathrm{hasParent}`$ が偽）であるから、最後の枝の値
```math
\mathrm{take}\,j_0\,M \mathbin{+\!\!+}
 \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda j.\ (M_{0,j}+k\,d_0,\ M_{1,j}+k\,d_1))\,\mathrm{range}'(j_0,j_1-j_0)\bigr)\,\mathrm{range}(n)
```
が得られる。ここで $`d_1 = (1\lt i_1 \text{ ならば } M_{1,j_1}-M_{1,j_0},\ \text{さもなくば } 0)`$ であるが、
[(T.idx1_le1)](#t-idx1_le1) より $`i_1\le 1`$ なので $`1\lt i_1`$ は偽、したがって $`d_1=0`$ であり、
各成分は $`M_{1,j}+k\cdot 0 = M_{1,j}`$ となる。∎

## 対の追加は測度を真に増やす

<a id="t-translate_snoc_increase"></a>
### 定理 末尾追加による増加 (T.translate_snoc_increase)

**主張** 任意のペア列 $`C`$ と対 $`m`$ に対し
```math
\mathrm{tr}\,C \prec \mathrm{tr}(C\mathbin{+\!\!+}[m]).
```

**証明** $`m`$ を固定し、$`\mathrm{tr}`$ の再帰に沿う帰納法（[(D.translate)](#d-translate) の注）を行う。帰納法の述語は
```math
\Phi(C) :\equiv \mathrm{tr}\,C \prec \mathrm{tr}(C\mathbin{+\!\!+}[m]).
```

- 基底段 $`C=[]`$：$`\mathrm{tr}\,[] = \mathsf{Z}`$、
  $`\mathrm{tr}([]\mathbin{+\!\!+}[m]) = \mathrm{tr}[m] = \mathsf{P}(\pi_1 m,\mathsf{Z},\mathsf{Z})`$ であり、
  [(T.olt_Z_P)](#t-olt_Z_P) より $`\mathsf{Z}\prec\mathsf{P}(\pi_1 m,\mathsf{Z},\mathsf{Z})`$。
- 帰納段 $`C=p\mathbin{::}L`$：帰納法の仮定は
  $`\Phi(\mathrm{tw}_{\pi_0 p}L)`$ と $`\Phi(\mathrm{dw}_{\pi_0 p}L)`$ である。
  $`(p\mathbin{::}L)\mathbin{+\!\!+}[m] = p\mathbin{::}(L\mathbin{+\!\!+}[m])`$ に注意して 3 つの場合に分ける。

  - **場合 A1** $`\forall x\in L,\ \pi_0 p\lt \pi_0 x`$ かつ $`\pi_0 p\lt \pi_0 m`$：
    `List.takeWhile_eq_self_iff` より $`\mathrm{tw}_{\pi_0 p}L=L`$ だから、帰納法の仮定
    $`\Phi(\mathrm{tw}_{\pi_0 p}L)`$ は $`\mathrm{tr}\,L \prec \mathrm{tr}(L\mathbin{+\!\!+}[m])`$ と同じ命題である。
    $`L\mathbin{+\!\!+}[m]`$ の全要素 $`x`$ は $`\pi_0 p\lt \pi_0 x`$ をみたす（$`x\in L`$ なら仮定、$`x=m`$ なら $`\pi_0 p\lt \pi_0 m`$）ので、
    [(T.translate_single_tree)](#t-translate_single_tree) を 2 回用いて
    ```math
    \mathrm{tr}(p\mathbin{::}L) = \mathsf{P}(\pi_1 p,\ \mathrm{tr}\,L,\ \mathsf{Z}),\qquad
      \mathrm{tr}(p\mathbin{::}(L\mathbin{+\!\!+}[m])) = \mathsf{P}(\pi_1 p,\ \mathrm{tr}(L\mathbin{+\!\!+}[m]),\ \mathsf{Z}).
    ```
    [(T.olt_P_b)](#t-olt_P_b) より $`\Phi(p\mathbin{::}L)`$。
  - **場合 A2** $`\forall x\in L,\ \pi_0 p\lt \pi_0 x`$ かつ $`\neg(\pi_0 p\lt \pi_0 m)`$：
    [(T.translate_single_tree)](#t-translate_single_tree) より
    $`\mathrm{tr}(p\mathbin{::}L)=\mathsf{P}(\pi_1 p,\mathrm{tr}\,L,\mathsf{Z})`$。
    一方 [(T.takeWhile_append_all)](#t-takeWhile_append_all) と
    [(T.dropWhile_append_all)](#t-dropWhile_append_all)（$`xs:=L`$, $`ys:=[m]`$）より
    ```math
    \mathrm{tw}_{\pi_0 p}(L\mathbin{+\!\!+}[m]) = L\mathbin{+\!\!+}\mathrm{tw}_{\pi_0 p}[m] = L,\qquad
      \mathrm{dw}_{\pi_0 p}(L\mathbin{+\!\!+}[m]) = \mathrm{dw}_{\pi_0 p}[m] = [m]
    ```
    （$`\neg(\pi_0 p\lt \pi_0 m)`$ による）。よって [(D.translate)](#d-translate) より
    $`\mathrm{tr}(p\mathbin{::}(L\mathbin{+\!\!+}[m])) = \mathsf{P}(\pi_1 p,\ \mathrm{tr}\,L,\ \mathrm{tr}[m])`$。
    $`\mathrm{tr}[m]=\mathsf{P}(\pi_1 m,\mathsf{Z},\mathsf{Z})`$ と [(T.olt_Z_P)](#t-olt_Z_P) より
    $`\mathsf{Z}\prec\mathrm{tr}[m]`$ だから、[(T.olt_P_c)](#t-olt_P_c) より $`\Phi(p\mathbin{::}L)`$。
  - **場合 B** $`\neg(\forall x\in L,\ \pi_0 p\lt \pi_0 x)`$：
    $`x\in L`$ で $`\neg(\pi_0 p\lt \pi_0 x)`$ なるものを取ると、
    [(T.takeWhile_append_not)](#t-takeWhile_append_not) と [(T.dropWhile_append_not)](#t-dropWhile_append_not) より
    ```math
    \mathrm{tw}_{\pi_0 p}(L\mathbin{+\!\!+}[m]) = \mathrm{tw}_{\pi_0 p}L,\qquad
      \mathrm{dw}_{\pi_0 p}(L\mathbin{+\!\!+}[m]) = (\mathrm{dw}_{\pi_0 p}L)\mathbin{+\!\!+}[m].
    ```
    よって [(D.translate)](#d-translate) より
    ```math
    \mathrm{tr}(p\mathbin{::}L) = \mathsf{P}(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p}L),\ \mathrm{tr}(\mathrm{dw}_{\pi_0 p}L)),
    ```
    ```math
    \mathrm{tr}(p\mathbin{::}(L\mathbin{+\!\!+}[m])) = \mathsf{P}(\pi_1 p,\ \mathrm{tr}(\mathrm{tw}_{\pi_0 p}L),\ \mathrm{tr}((\mathrm{dw}_{\pi_0 p}L)\mathbin{+\!\!+}[m]))
    ```
    となり、添字と引数が一致する。帰納法の仮定 $`\Phi(\mathrm{dw}_{\pi_0 p}L)`$ が後続和どうしの比較
    $`\mathrm{tr}(\mathrm{dw}_{\pi_0 p}L)\prec\mathrm{tr}((\mathrm{dw}_{\pi_0 p}L)\mathbin{+\!\!+}[m])`$ を与えるので、
    [(T.olt_P_c)](#t-olt_P_c) より $`\Phi(p\mathbin{::}L)`$。

  3 つの場合はすべてを尽くしている。∎

<a id="t-translate_dropLast_decrease"></a>
### 定理 末尾削除による減少 (T.translate_dropLast_decrease)

**主張** $`C\ne[]`$ ならば $`\mathrm{tr}(\mathrm{dropLast}\,C) \prec \mathrm{tr}\,C`$。

**証明** $`C\ne[]`$ より $`C = \mathrm{dropLast}\,C \mathbin{+\!\!+} [\,\mathrm{getLast}\,C\,]`$ である
（標準ライブラリの `List.dropLast_append_getLast`）。
右辺に [(T.translate_snoc_increase)](#t-translate_snoc_increase) を $`C:=\mathrm{dropLast}\,C`$,
$`m:=\mathrm{getLast}\,C`$ として適用すればよい。∎

<a id="t-translate_takeWhile_snoc_le"></a>
### 定理 先頭ブロックの弱増加 (T.translate_takeWhile_snoc_le)

**主張** 任意の $`a\in\mathbb{N}`$、ペア列 $`C`$、対 $`m`$ に対し
```math
\mathrm{tr}(\mathrm{tw}_a C) \preceq \mathrm{tr}(\mathrm{tw}_a (C\mathbin{+\!\!+}[m])).
```

**証明** 場合分けする。

- $`\forall x\in C,\ a\lt \pi_0 x`$ のとき：`List.takeWhile_eq_self_iff` より $`\mathrm{tw}_a C = C`$。
  - $`a\lt \pi_0 m`$ ならば $`C\mathbin{+\!\!+}[m]`$ の全要素が述語をみたすので
    $`\mathrm{tw}_a(C\mathbin{+\!\!+}[m]) = C\mathbin{+\!\!+}[m]`$ であり、
    [(T.translate_snoc_increase)](#t-translate_snoc_increase) より
    $`\mathrm{tr}\,C\prec\mathrm{tr}(C\mathbin{+\!\!+}[m])`$。[(D.ole)](#d-ole) の第 1 選言。
  - $`\neg(a\lt \pi_0 m)`$ ならば [(T.takeWhile_append_all)](#t-takeWhile_append_all) より
    $`\mathrm{tw}_a(C\mathbin{+\!\!+}[m]) = C\mathbin{+\!\!+}\mathrm{tw}_a[m] = C\mathbin{+\!\!+}[] = C`$。
    両辺は同一なので [(D.ole)](#d-ole) の第 2 選言。
- $`\neg(\forall x\in C,\ a\lt \pi_0 x)`$ のとき：$`x\in C`$ で $`\neg(a\lt \pi_0 x)`$ なるものを取ると
  [(T.takeWhile_append_not)](#t-takeWhile_append_not) より
  $`\mathrm{tw}_a(C\mathbin{+\!\!+}[m]) = \mathrm{tw}_a C`$。両辺は同一なので [(D.ole)](#d-ole) の第 2 選言。∎

## 悪い分岐の抽象核

次の 2 つの補題は、悪い分岐で生じる列の形だけを抽象化したものである
（$`i_1=0`$ なら完全コピー、$`i_1=1`$ なら昇順コピーになる）。

<a id="t-core_i0"></a>
### 定理 核 $`i_1=0`$（完全コピー） (T.core_i0)

**主張** $`v_0,w_0\in\mathbb{N}`$、ペア列 $`R,T`$、対 $`lp`$ が
```math
\forall x\in R,\ v_0<\pi_0 x,\qquad v_0<\pi_0 lp,\qquad
  T=[]\ \vee\ \neg\bigl(v_0<\pi_0(\mathrm{headI}\,T)\bigr)
```
をみたすならば
```math
\mathrm{tr}\bigl(((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}T\bigr)
 \prec \mathrm{tr}\bigl(((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}[lp]\bigr).
```

**証明** 左辺は [(T.translate_block_append)](#t-translate_block_append) より
```math
\mathrm{tr}\bigl(((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}T\bigr) = \mathsf{P}(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T).
```
右辺は $`((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}[lp] = (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp])`$ であり、
$`R\mathbin{+\!\!+}[lp]`$ の全要素 $`x`$ が $`v_0\lt \pi_0 x`$ をみたす（$`x\in R`$ なら第 1 の仮定、$`x=lp`$ なら第 2 の仮定）ので、
[(T.translate_single_tree)](#t-translate_single_tree) より
```math
\mathrm{tr}\bigl(((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}[lp]\bigr) = \mathsf{P}(w_0,\ \mathrm{tr}(R\mathbin{+\!\!+}[lp]),\ \mathsf{Z}).
```
[(T.translate_snoc_increase)](#t-translate_snoc_increase) より $`\mathrm{tr}\,R \prec \mathrm{tr}(R\mathbin{+\!\!+}[lp])`$ であるから、
[(T.olt_P_b)](#t-olt_P_b)（添字は両辺とも $`w_0`$）により主張を得る。
比較は引数の段で決まるので、後続和 $`\mathrm{tr}\,T`$（コピーの個数）は結論に影響しない。∎

<a id="t-core_i1"></a>
### 定理 核 $`i_1=1`$（昇順コピー） (T.core_i1)

**主張** $`v_0,w_0\in\mathbb{N}`$、ペア列 $`R,C'`$、対 $`c,lp`$ が
```math
\forall x\in R,\ v_0<\pi_0 x,\quad \forall x\in C',\ \pi_0 c\le\pi_0 x,\quad
  \pi_0 c=\pi_0 lp,\quad v_0<\pi_0 lp,\quad \pi_1 c<\pi_1 lp
```
をみたすならば
```math
\mathrm{tr}\bigl(((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}(c\mathbin{::}C')\bigr)
 \prec \mathrm{tr}\bigl(((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}[lp]\bigr).
```

**証明** 3 段に分ける。

1. **添字優先支配** $`\mathrm{tr}(c\mathbin{::}C') \prec \mathrm{tr}[lp]`$。
   [(T.lead_translate)](#t-lead_translate) より $`\mathrm{lead}(\mathrm{tr}(c\mathbin{::}C')) = \pi_1 c`$ であり、
   仮定 $`\pi_1 c\lt \pi_1 lp`$ とあわせて
   [(T.olt_P_of_lead_lt)](#t-olt_P_of_lead_lt)（$`t:=\mathrm{tr}(c\mathbin{::}C')`$, $`w:=\pi_1 lp`$）より
   $`\mathrm{tr}(c\mathbin{::}C') \prec \mathsf{P}(\pi_1 lp,\mathsf{Z},\mathsf{Z})`$。
   [(D.translate)](#d-translate) より $`\mathrm{tr}[lp] = \mathsf{P}(\pi_1 lp,\mathsf{Z},\mathsf{Z})`$ だから、これが 1 の主張である。
2. **文脈 $`R`$ への持ち上げ** $`\mathrm{tr}(R\mathbin{+\!\!+}c\mathbin{::}C') \prec \mathrm{tr}(R\mathbin{+\!\!+}lp\mathbin{::}[])`$。
   [(T.translate_ctx_cong)](#t-translate_ctx_cong) を
   $`z_1:=c`$, $`T_1:=C'`$, $`z_2:=lp`$, $`T_2:=[]`$, $`G:=R`$ として適用する。
   base は 1、root は仮定 $`\pi_0 c=\pi_0 lp`$、$`r_1`$ は仮定 $`\forall x\in C',\ \pi_0 c\le\pi_0 x`$、
   $`r_2`$ は $`T_2=[]`$ ゆえ前件が偽で成立する。
3. **根 $`(v_0,w_0)`$ への持ち上げ**。
   $`R\mathbin{+\!\!+}c\mathbin{::}C'`$ の全要素 $`x`$ は $`v_0\lt \pi_0 x`$ をみたす。実際、
   $`x\in R`$ なら第 1 の仮定、$`x=c`$ なら $`\pi_0 c=\pi_0 lp\gt v_0`$、
   $`x\in C'`$ なら $`v_0\lt \pi_0 lp=\pi_0 c\le\pi_0 x`$。
   また $`R\mathbin{+\!\!+}[lp]`$ の全要素 $`x`$ も $`v_0\lt \pi_0 x`$ をみたす：
   $`x\in R`$ なら第 1 の仮定、$`x=lp`$ なら仮定 $`v_0\lt \pi_0 lp`$ による。
   よって [(T.translate_single_tree)](#t-translate_single_tree) を 2 回用いて
   ```math
   \mathrm{tr}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}c\mathbin{::}C')\bigr)
     = \mathsf{P}(w_0,\ \mathrm{tr}(R\mathbin{+\!\!+}c\mathbin{::}C'),\ \mathsf{Z}),
   ```
   ```math
   \mathrm{tr}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp])\bigr)
     = \mathsf{P}(w_0,\ \mathrm{tr}(R\mathbin{+\!\!+}[lp]),\ \mathsf{Z}).
   ```
   2 と [(T.olt_P_b)](#t-olt_P_b) より主張を得る（$`((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}X = (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}X)`$ による）。∎

## 展開一段の減少：前者分岐

<a id="t-translate_oper_pred"></a>
### 定理 前者分岐の減少 (T.translate_oper_pred)

**主張** $`1\lt \lvert M\rvert`$ とし、$`j_1=\lvert M\rvert-1`$ について
```math
\bigl(M_{0,j_1}=0 \wedge M_{1,j_1}=0\bigr)\ \vee\ \neg\,\mathrm{hasParent}\,M\,(\mathrm{idx1}\,M\,j_1)\,j_1
```
が成り立つとする。このとき $`\mathrm{tr}(M[n]) \prec \mathrm{tr}\,M`$。

**証明** $`1\lt \lvert M\rvert`$ より $`\lvert M\rvert-1\ne 0`$ である。まず $`M[n]=\mathrm{Pred}\,M`$ を示す。
仮定の第 1 選言が成り立つなら [(T.oper_eq_pred_of_zero)](#t-oper_eq_pred_of_zero) による。
第 2 選言が成り立つ場合は、$`M_{0,j_1}=0\wedge M_{1,j_1}=0`$ が成り立つかどうかでさらに分け、
成り立つなら [(T.oper_eq_pred_of_zero)](#t-oper_eq_pred_of_zero)、
成り立たないなら [(T.oper_eq_pred_of_noParent)](#t-oper_eq_pred_of_noParent) による。

次に $`1\lt \lvert M\rvert`$ より $`\lvert M\rvert\le 1`$ は偽だから、[(D.Pred)](Def.md#d-Pred) より
$`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$。
また $`M=[]`$ とすると $`\lvert M\rvert=0`$ となり $`1\lt 0`$ に矛盾するので $`M\ne[]`$。
[(T.translate_dropLast_decrease)](#t-translate_dropLast_decrease) より
$`\mathrm{tr}(\mathrm{dropLast}\,M)\prec\mathrm{tr}\,M`$、すなわち $`\mathrm{tr}(M[n])\prec\mathrm{tr}\,M`$。∎

## 悪い分岐の分解

<a id="t-parent_nextR"></a>
### 定理 親は $`\mathrm{nextR}`$ をみたす (T.parent_nextR)

**主張** $`\mathrm{hasParent}\,M\,i\,j_1`$ ならば
$`\mathrm{nextR}\,M\,i\,(\mathrm{parent}\,M\,i\,j_1)\,j_1`$（[(D.nextR)](Def.md#d-nextR)）。

**証明** [(D.hasParent)](Def.md#d-hasParent) は
$`\exists!\,j_0,\ \mathrm{nextR}\,M\,i\,j_0\,j_1`$ であり、とくに
$`\exists\,j_0,\ \mathrm{nextR}\,M\,i\,j_0\,j_1`$ が成り立つ。
[(D.parent)](Def.md#d-parent) は述語 $`\lambda j_0.\ \mathrm{nextR}\,M\,i\,j_0\,j_1`$ に対する Hilbert の
$`\varepsilon`$ 項であるから、存在からその仕様（`Classical.epsilon_spec`）が得られ、
$`\mathrm{nextR}\,M\,i\,(\mathrm{parent}\,M\,i\,j_1)\,j_1`$ が従う。∎

<a id="t-nextR_index_lt"></a>
### 定理 $`\mathrm{nextR}`$ は添字を真に増やす (T.nextR_index_lt)

**主張** $`\mathrm{nextR}\,M\,i\,j_0\,j_1`$ ならば $`j_0\lt j_1`$。

**証明** [(D.nextR)](Def.md#d-nextR) は $`i=0`$ のとき $`\mathrm{nextrel0}\,M\,j_0\,j_1`$
（[(D.nextrel0)](Def.md#d-nextrel0)）、$`i\ne 0`$ のとき $`\mathrm{nextrel1}\,M\,j_0\,j_1`$
（[(D.nextrel1)](Def.md#d-nextrel1)）である。どちらも第 3 成分として $`j_0\lt j_1`$ をもつ。∎

<a id="t-nextR_chain0"></a>
### 定理 $`\mathrm{nextR}`$ から行 0 鎖へ (T.nextR_chain0)

**主張** $`\mathrm{nextR}\,M\,i\,j_0\,j_1`$ ならば
$`\mathrm{ReflTransGen}(\mathrm{nextrel0}\,M)\,j_0\,j_1`$。

**証明** [(D.nextR)](Def.md#d-nextR) で場合分けする。
$`i=0`$ のときは $`\mathrm{nextrel0}\,M\,j_0\,j_1`$ であり、1 歩の鎖として反射推移閉包に属する。
$`i\ne 0`$ のときは $`\mathrm{nextrel1}\,M\,j_0\,j_1`$ であり、
[(D.nextrel1)](Def.md#d-nextrel1) の第 5 成分が $`\mathrm{le0}\,M\,j_0\,j_1`$、
その [(D.le0)](Def.md#d-le0) の第 3 成分が $`\mathrm{ReflTransGen}(\mathrm{nextrel0}\,M)\,j_0\,j_1`$ である。∎

<a id="t-oper_bad_blocks"></a>
### 定理 悪い分岐のブロック分解 (T.oper_bad_blocks)

**主張** $`j_1:=\lvert M\rvert-1`$、$`i_1:=\mathrm{idx1}\,M\,j_1`$ とし、
```math
1<\lvert M\rvert,\qquad \neg\bigl(M_{0,j_1}=0\wedge M_{1,j_1}=0\bigr),\qquad
  \mathrm{hasParent}\,M\,i_1\,j_1,\qquad 1\le n
```
を仮定する。このときペア列 $`G,R`$、自然数 $`v_0,w_0,d_0`$、対 $`lp`$ が存在して次の 6 条件をみたす。

1. $`M = G \mathbin{+\!\!+} ((v_0,w_0)\mathbin{::}R) \mathbin{+\!\!+} [lp]`$
2. $`M[n] = G \mathbin{+\!\!+} \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda p.\ (\pi_0 p + k\,d_0,\ \pi_1 p))\,((v_0,w_0)\mathbin{::}R)\bigr)\,\mathrm{range}(n)`$
3. $`\forall x\in R,\ v_0\lt \pi_0 x`$
4. $`v_0\lt \pi_0 lp`$
5. $`\bigl(d_0=0 \wedge i_1=0\bigr)\ \vee\ \bigl(0\lt d_0 \wedge w_0\lt \pi_1 lp \wedge \pi_0 lp=v_0+d_0 \wedge \mathrm{nextrel1}\,M\,\lvert G\rvert\,j_1\bigr)`$
6. $`\mathrm{nextR}\,M\,i_1\,\lvert G\rvert\,j_1`$

（仮定 $`1\le n`$ は以下の証明では使わない。Lean 側でも未使用引数として記されている。）

**証明** $`j_0 := \mathrm{parent}\,M\,i_1\,j_1`$ とおき、次を証人とする。
```math
G := \mathrm{take}\,j_0\,M,\quad v_0 := M_{0,j_0},\quad w_0 := M_{1,j_0},\quad
  R := \mathrm{map}\bigl(\lambda j.\ (M_{0,j},M_{1,j})\bigr)\,\mathrm{range}'(j_0+1,\ j_1-(j_0+1)),
```
```math
d_0 := \begin{cases} M_{0,j_1}-M_{0,j_0} & (0<i_1)\cr 0 & (\text{それ以外})\end{cases},\qquad
  lp := M\langle j_1\rangle .
```

準備として次を用意する。

- (P1) $`\mathrm{nextR}\,M\,i_1\,j_0\,j_1`$：仮定 $`\mathrm{hasParent}\,M\,i_1\,j_1`$ に
  [(T.parent_nextR)](#t-parent_nextR) を適用。
- (P2) $`j_0\lt j_1`$：(P1) に [(T.nextR_index_lt)](#t-nextR_index_lt) を適用。
- (P3) $`\mathrm{ReflTransGen}(\mathrm{nextrel0}\,M)\,j_0\,j_1`$：(P1) に
  [(T.nextR_chain0)](#t-nextR_chain0) を適用。
- (P4) $`\forall k,\ (j_0\lt k \wedge k\le j_1)\to M_{0,j_0}\lt M_{0,k}`$：(P3) に
  [(T.le0_interval_gt)](#t-le0_interval_gt) を適用。
- (P5) $`\mathrm{range}'(j_0,\ j_1-j_0) = j_0 \mathbin{::} \mathrm{range}'(j_0+1,\ j_1-(j_0+1))`$：
  (P2) より $`j_1-j_0 = \bigl(j_1-(j_0+1)\bigr)+1`$ であり、`List.range'_succ` を適用する。
- (P6) $`\lvert G\rvert = j_0`$：$`\lvert \mathrm{take}\,j_0\,M\rvert = \min(j_0,\lvert M\rvert)`$ であり、
  (P2) と $`j_1=\lvert M\rvert-1\lt \lvert M\rvert`$ から $`j_0\lt \lvert M\rvert`$ なので $`\min(j_0,\lvert M\rvert)=j_0`$。
- (P7) 任意の $`j`$ に対し $`M\langle j\rangle = (M_{0,j},\ M_{1,j})`$：
  [(D.entry)](Def.md#d-entry) より $`M_{0,j}=\pi_0(M\langle j\rangle)`$、$`M_{1,j}=\pi_1(M\langle j\rangle)`$ であり、
  対 $`u`$ は $`(\pi_0 u,\pi_1 u)`$ に等しい。

**条件 1 の証明。** $`M = \mathrm{take}\,j_0\,M \mathbin{+\!\!+} \mathrm{drop}\,j_0\,M`$ であるから、
```math
\mathrm{drop}\,j_0\,M = \bigl((v_0,w_0)\mathbin{::}R\bigr)\mathbin{+\!\!+}[lp]
```
を示せばよい。[(T.drop_eq_map_getD)](#t-drop_eq_map_getD) より
```math
\mathrm{drop}\,j_0\,M = \mathrm{map}\,(\lambda i.\ M\langle i\rangle)\ \mathrm{range}'(j_0,\ \lvert M\rvert-j_0).
```
$`1\lt \lvert M\rvert`$ より $`\lvert M\rvert=j_1+1`$ であり、(P2) より $`j_0\le j_1`$ だから
$`\lvert M\rvert-j_0 = (j_1-j_0)+1`$。また `List.range'_append`（$`a:=j_0`$, $`m:=j_1-j_0`$, $`k:=1`$）より
```math
\mathrm{range}'(j_0,\ j_1-j_0)\mathbin{+\!\!+}\mathrm{range}'\bigl(j_0+(j_1-j_0),\ 1\bigr)
 = \mathrm{range}'\bigl(j_0,\ (j_1-j_0)+1\bigr)
```
であり、$`j_0\le j_1`$ より $`j_0+(j_1-j_0)=j_1`$、かつ $`\mathrm{range}'(j_1,1)=[j_1]`$ であるから
```math
\mathrm{range}'\bigl(j_0,\ (j_1-j_0)+1\bigr) = \mathrm{range}'(j_0,\ j_1-j_0)\mathbin{+\!\!+}[j_1].
```
$`\mathrm{map}`$ を連結に分配し、(P5) を使うと
```math
\mathrm{drop}\,j_0\,M
 = \Bigl(M\langle j_0\rangle \mathbin{::} \mathrm{map}\,(\lambda i.\ M\langle i\rangle)\,\mathrm{range}'(j_0+1,\ j_1-(j_0+1))\Bigr)
   \mathbin{+\!\!+}[\,M\langle j_1\rangle\,].
```
(P7) より $`M\langle j_0\rangle=(v_0,w_0)`$、
$`\mathrm{map}\,(\lambda i.\ M\langle i\rangle)\,\mathrm{range}'(j_0+1,\cdot) = R`$、
$`M\langle j_1\rangle = lp`$ であるから、条件 1 を得る。

**条件 2 の証明。** [(T.oper_bad_unfold)](#t-oper_bad_unfold) より
```math
M[n] = \mathrm{take}\,j_0\,M \mathbin{+\!\!+}
 \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda j.\ (M_{0,j}+k\,d_0,\ M_{1,j}))\,\mathrm{range}'(j_0,\ j_1-j_0)\bigr)\,\mathrm{range}(n).
```
各 $`k`$ について、(P5) と $`\mathrm{map}`$ の $`\mathbin{::}`$ への分配より
```math
\mathrm{map}(\lambda j.\ (M_{0,j}+k\,d_0,\ M_{1,j}))\,\mathrm{range}'(j_0,\ j_1-j_0)
 = (v_0+k\,d_0,\ w_0)\mathbin{::}\mathrm{map}(\lambda j.\ (M_{0,j}+k\,d_0,\ M_{1,j}))\,\mathrm{range}'(j_0+1,\ j_1-(j_0+1)).
```
一方、$`R`$ の定義と $`\mathrm{map}\,f\,(\mathrm{map}\,g\,l) = \mathrm{map}\,(f\circ g)\,l`$ より
```math
\mathrm{map}(\lambda p.\ (\pi_0 p + k\,d_0,\ \pi_1 p))\,\bigl((v_0,w_0)\mathbin{::}R\bigr)
 = (v_0+k\,d_0,\ w_0)\mathbin{::}\mathrm{map}(\lambda j.\ (M_{0,j}+k\,d_0,\ M_{1,j}))\,\mathrm{range}'(j_0+1,\ j_1-(j_0+1)).
```
両者は一致するので、$`\mathrm{flatMap}`$ の中身を置き換えて条件 2 を得る。

**条件 3 の証明。** $`x\in R`$ とする。$`R`$ の定義より $`j\in\mathrm{range}'(j_0+1,\ j_1-(j_0+1))`$ が存在して
$`x=(M_{0,j},M_{1,j})`$、すなわち $`\pi_0 x = M_{0,j}`$。
$`j\in\mathrm{range}'(j_0+1,\ j_1-(j_0+1))`$ は $`j=j_0+1+i`$ かつ $`i\lt j_1-(j_0+1)`$ なる $`i`$ の存在を意味する。
このとき $`j_0\lt j`$ である。また自然数の切り捨て減算のもとで $`i\lt j_1-(j_0+1)`$ が成り立つのは
$`j_0+1\lt j_1`$ のときに限り、そのとき $`j_0+1+\bigl(j_1-(j_0+1)\bigr)=j_1`$ だから
$`j = j_0+1+i \lt j_1`$、とくに $`j\le j_1`$。
(P4) を $`k:=j`$ に適用して $`v_0 = M_{0,j_0} \lt M_{0,j} = \pi_0 x`$。

**条件 4 の証明。** (P7) より $`\pi_0 lp = M_{0,j_1}`$。(P4) を $`k:=j_1`$ に適用する
（(P2) より $`j_0\lt j_1`$、また $`j_1\le j_1`$）と $`v_0\lt M_{0,j_1}=\pi_0 lp`$。

**条件 5 の証明。** $`0\lt i_1`$ かどうかで分ける。

- $`0\lt i_1`$ のとき（右の選言を示す）。$`i_1\ne0`$ だから [(D.nextR)](Def.md#d-nextR) と (P1) より
  $`\mathrm{nextrel1}\,M\,j_0\,j_1`$ が成り立つ。これを $`\mathrm{nl}_1`$ とおく。
  - $`0\lt d_0`$：$`d_0 = M_{0,j_1}-M_{0,j_0}`$ であり、条件 4 の証明で見た $`M_{0,j_0}\lt M_{0,j_1}`$ より差は正。
  - $`w_0\lt \pi_1 lp`$：[(D.nextrel1)](Def.md#d-nextrel1) の第 4 成分は $`M_{1,j_0}\lt M_{1,j_1}`$ であり、
    (P7) より $`w_0=M_{1,j_0}`$、$`\pi_1 lp = M_{1,j_1}`$。
  - $`\pi_0 lp = v_0+d_0`$：$`M_{0,j_0}\le M_{0,j_1}`$ より
    $`M_{0,j_0} + (M_{0,j_1}-M_{0,j_0}) = M_{0,j_1}`$、すなわち $`v_0+d_0 = M_{0,j_1} = \pi_0 lp`$。
  - $`\mathrm{nextrel1}\,M\,\lvert G\rvert\,j_1`$：(P6) より $`\lvert G\rvert=j_0`$ なので $`\mathrm{nl}_1`$ そのもの。
- $`\neg(0\lt i_1)`$ のとき（左の選言を示す）。$`d_0`$ の定義の第 2 の場合が選ばれるので $`d_0=0`$。
  また $`i_1`$ は自然数で $`0\lt i_1`$ でないから $`i_1=0`$。

**条件 6 の証明。** (P6) より $`\lvert G\rvert=j_0`$ であり、(P1) がそのまま主張である。∎

## 展開一段の減少：悪い分岐

<a id="t-translate_oper_bad"></a>
### 定理 悪い分岐の減少 (T.translate_oper_bad)

**主張** $`j_1=\lvert M\rvert-1`$、$`i_1=\mathrm{idx1}\,M\,j_1`$ とし、
```math
1<\lvert M\rvert,\qquad \neg\bigl(M_{0,j_1}=0\wedge M_{1,j_1}=0\bigr),\qquad
  \mathrm{hasParent}\,M\,i_1\,j_1,\qquad 1\le n
```
を仮定する。このとき $`\mathrm{tr}(M[n]) \prec \mathrm{tr}\,M`$。

**証明** [(T.oper_bad_blocks)](#t-oper_bad_blocks) により
$`G,v_0,w_0,R,d_0,lp`$ を取り、その条件 1〜5 を使う（条件 6 はここでは使わない）。

**分解の整形。** $`1\le n`$ より $`n=m+1`$ と書ける。`List.range_eq_range'` と `List.range'_succ` より
```math
\mathrm{range}(n) = \mathrm{range}'(0,n) = 0\mathbin{::}\mathrm{range}'(1,\ n-1).
```
また $`k=0`$ の項は
$`\mathrm{map}(\lambda p.\ (\pi_0 p+0\cdot d_0,\ \pi_1 p))\,((v_0,w_0)\mathbin{::}R) = (v_0,w_0)\mathbin{::}R`$
である（$`0\cdot d_0=0`$ かつ $`(\pi_0 p+0,\pi_1 p)=p`$）。そこで
```math
C := \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda p.\ (\pi_0 p+k\,d_0,\ \pi_1 p))\,((v_0,w_0)\mathbin{::}R)\bigr)\,\mathrm{range}'(1,\ n-1)
```
とおくと、条件 2 は
```math
M[n] = G\mathbin{+\!\!+}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}C)\bigr)
```
となり、条件 1 は
```math
M = G\mathbin{+\!\!+}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp])\bigr)
```
となる。

**$`C`$ の要素の下界 (LB)。** $`\forall x\in C,\ v_0\le\pi_0 x`$。実際 $`x\in C`$ なら
$`k\in\mathrm{range}'(1,n-1)`$ と $`p\in(v_0,w_0)\mathbin{::}R`$ が存在して $`x=(\pi_0 p+k\,d_0,\ \pi_1 p)`$ である。
$`p=(v_0,w_0)`$ なら $`\pi_0 p=v_0`$、$`p\in R`$ なら条件 3 より $`v_0\lt \pi_0 p`$。いずれにせよ $`v_0\le\pi_0 p`$ であり、
$`\pi_0 p \le \pi_0 p + k\,d_0 = \pi_0 x`$。

**核の適用**
```math
\text{(core)}\qquad \mathrm{tr}\bigl(((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}C\bigr)
 \prec \mathrm{tr}\bigl(((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}[lp]\bigr).
```
$`n`$ の大きさで分ける。

- $`n\lt 2`$ のとき。$`1\le n`$ とあわせて $`n=1`$ であり、$`\mathrm{range}'(1,0)=[]`$ だから $`C=[]`$。
  [(T.core_i0)](#t-core_i0) を $`T:=C=[]`$（第 3 仮定の第 1 選言）、
  第 1 仮定に条件 3、第 2 仮定に条件 4 を与えて適用する。
- $`2\le n`$ のとき。$`n-1=(n-2)+1`$ と `List.range'_succ` より
  $`\mathrm{range}'(1,\ n-1) = 1\mathbin{::}\mathrm{range}'(2,\ n-2)`$ であり、$`C`$ の先頭を取り出すと
  ```math
  C = (v_0+1\cdot d_0,\ w_0)\mathbin{::}\Bigl(\mathrm{map}(\lambda p.\ (\pi_0 p+1\cdot d_0,\ \pi_1 p))\,R
      \mathbin{+\!\!+} \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}(\lambda p.\ (\pi_0 p+k\,d_0,\ \pi_1 p))\,((v_0,w_0)\mathbin{::}R)\bigr)\,\mathrm{range}'(2,\ n-2)\Bigr).
  ```
  条件 5 の 2 つの選言で分ける。
  - **$`d_0=0`$ の場合（完全コピー）。** 上の表示より $`C`$ の先頭は $`(v_0+1\cdot 0,\ w_0)=(v_0,w_0)`$ であり、
    $`\pi_0(\mathrm{headI}\,C)=v_0`$、したがって $`\neg(v_0\lt \pi_0(\mathrm{headI}\,C))`$。
    [(T.core_i0)](#t-core_i0) を $`T:=C`$（第 3 仮定の第 2 選言）として適用する。
  - **$`0\lt d_0`$ の場合（昇順コピー）。** 条件 5 の右の選言より
    $`w_0\lt \pi_1 lp`$ かつ $`\pi_0 lp = v_0+d_0`$ である。
    $`c := (v_0+1\cdot d_0,\ w_0)`$、$`C'`$ を上の表示の第 2 成分（$`\mathbin{::}`$ の右）として
    [(T.core_i1)](#t-core_i1) を適用する。仮定の検証は次の通り。
    - $`\forall x\in R,\ v_0\lt \pi_0 x`$：条件 3。
    - $`\forall x\in C',\ \pi_0 c\le\pi_0 x`$：$`C'`$ は 2 つの部分の連結である。
      前半の要素は $`p\in R`$ に対する $`(\pi_0 p+1\cdot d_0,\ \pi_1 p)`$ であり、条件 3 の $`v_0\lt \pi_0 p`$ から
      $`v_0+d_0\le\pi_0 p+d_0`$。
      後半の要素は $`k\in\mathrm{range}'(2,n-2)`$（したがって $`2\le k`$）と $`p\in(v_0,w_0)\mathbin{::}R`$ に対する
      $`(\pi_0 p+k\,d_0,\ \pi_1 p)`$ であり、$`v_0\le\pi_0 p`$（$`p=(v_0,w_0)`$ なら等号、$`p\in R`$ なら条件 3）と
      $`1\cdot d_0\le k\,d_0`$（$`1\le k`$ による）から $`v_0+1\cdot d_0\le\pi_0 p+k\,d_0`$。
    - $`\pi_0 c=\pi_0 lp`$：$`\pi_0 c = v_0+1\cdot d_0 = v_0+d_0 = \pi_0 lp`$。
    - $`v_0\lt \pi_0 lp`$：条件 4。
    - $`\pi_1 c\lt \pi_1 lp`$：$`\pi_1 c = w_0`$ であり $`w_0\lt \pi_1 lp`$。

**前半部 $`G`$ への持ち上げ。** [(T.translate_ctx_cong)](#t-translate_ctx_cong) を
$`z_1:=(v_0,w_0)`$, $`T_1:=R\mathbin{+\!\!+}C`$, $`z_2:=(v_0,w_0)`$, $`T_2:=R\mathbin{+\!\!+}[lp]`$, $`G:=G`$ として適用する。

- base：$`((v_0,w_0)\mathbin{::}R)\mathbin{+\!\!+}X = (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}X)`$ により (core) を書き換えたもの。
- root：$`z_1=z_2`$ ゆえ $`\pi_0 z_1=\pi_0 z_2`$。
- $`r_1`$：$`x\in R\mathbin{+\!\!+}C`$ なら、$`x\in R`$ のとき条件 3 より $`v_0\lt \pi_0 x`$、
  $`x\in C`$ のとき (LB) より $`v_0\le\pi_0 x`$。
- $`r_2`$：$`x\in R\mathbin{+\!\!+}[lp]`$ なら、$`x\in R`$ のとき条件 3、$`x=lp`$ のとき条件 4 より $`v_0\le\pi_0 x`$。

したがって
```math
\mathrm{tr}\bigl(G\mathbin{+\!\!+}((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}C))\bigr)
 \prec \mathrm{tr}\bigl(G\mathbin{+\!\!+}((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}[lp]))\bigr)
```
であり、整形した条件 2・条件 1 によりこれは $`\mathrm{tr}(M[n])\prec\mathrm{tr}\,M`$ に他ならない。∎

## 減少補題

<a id="t-m_step_decreases"></a>
### 定理 展開一段の減少 (T.m_step_decreases)

**主張** $`1\lt \lvert M\rvert`$ かつ $`1\le n`$ ならば $`\mathrm{tr}(M[n]) \prec \mathrm{tr}\,M`$。

**証明** $`j_1=\lvert M\rvert-1`$、$`i_1=\mathrm{idx1}\,M\,j_1`$ とし、[(D.oper)](Def.md#d-oper) の分岐条件で場合分けする。

- $`M_{0,j_1}=0 \wedge M_{1,j_1}=0`$ のとき：
  [(T.translate_oper_pred)](#t-translate_oper_pred) を第 1 選言で適用する。
- $`\neg(M_{0,j_1}=0\wedge M_{1,j_1}=0)`$ かつ $`\mathrm{hasParent}\,M\,i_1\,j_1`$ のとき：
  [(T.translate_oper_bad)](#t-translate_oper_bad) を適用する（ここでのみ $`1\le n`$ を使う）。
- $`\neg(M_{0,j_1}=0\wedge M_{1,j_1}=0)`$ かつ $`\neg\,\mathrm{hasParent}\,M\,i_1\,j_1`$ のとき：
  [(T.translate_oper_pred)](#t-translate_oper_pred) を第 2 選言で適用する。

3 つの場合はすべてを尽くしており、いずれでも $`\mathrm{tr}(M[n])\prec\mathrm{tr}\,M`$ が示された。
この主張は、コピー数 $`n`$（$`1\le n`$ をみたす限り）の値にも、$`M`$ が標準形
[(D.ST_PS)](Def.md#d-ST_PS) であるかどうかにもよらない。∎
