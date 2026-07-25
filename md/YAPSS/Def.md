[← 目次](README.md)

# Def — ペア数列・親子関係・基本列・標準形の定義

本章は以降のすべての章が用いる語彙を定める。ペア数列 $M$、その成分 $M_{i,j}$、行 $0$ / 行 $1$ の親子関係、
前者関数 $\mathrm{Pred}$、基本列（展開）$M[n]$、対角列 $\Delta_a^b$、標準形の集合 $\mathrm{ST\_PS}$、
1 ステップ関係 $\mathrm{step}$ を導入する。
本章の宣言は 14 個すべてが定義であり、定理は含まれない。うち 2 個（$\mathrm{ST\_PS}$, $\mathrm{step}$）は
帰納的述語であるから、導入規則と帰納法原理（場合分け原理）を明示する。

## 記法

| Lean | 本文 | 意味 |
|---|---|---|
| `PairSeq` | $\mathrm{PairSeq}$ | 自然数のペアの有限列全体 |
| `M.length` | $\mathrm{Lng}\,M$ | 列 $M$ の長さ |
| `M.getD j (0, 0)` | $M_j$ | $M$ の第 $j$ 要素（$j \ge \mathrm{Lng}\,M$ のときは $(0,0)$） |
| `entry M i j` | $M_{i,j}$ | 第 $j$ 要素の第 $i$ 成分 |
| `nextrel0 M j0 j1` | $j_0 \to^M_0 j_1$ | 行 $0$ の直接親子関係 |
| `le0 M j0 j1` | $j_0 \le^M_0 j_1$ | 行 $0$ の祖先関係（$\to^M_0$ の反射推移閉包） |
| `nextrel1 M j0 j1` | $j_0 \to^M_1 j_1$ | 行 $1$ の直接親子関係 |
| `nextR M i j0 j1` | $j_0 \to^M_i j_1$ | 行 $i$ の直接親子関係 |
| `Pred M` | $\mathrm{Pred}\,M$ | 末尾 1 要素を除いた列（長さ $\le 1$ なら $M$ 自身） |
| `idx1 M j1` | $\mathrm{idx}_1(M, j_1)$ | 末尾の親を探す行番号 |
| `hasParent M i j1` | $\mathrm{hasParent}(M, i, j_1)$ | 行 $i$ における $j_1$ の親が一意に存在する |
| `parent M i j1` | $\mathrm{par}^M_i(j_1)$ | 行 $i$ における $j_1$ の親 |
| `oper M n`, `M⟦n⟧` | $M[n]$ | 基本列（コピー数 $n$ の展開） |
| `diagSeq a b` | $\Delta_a^b$ | 対角列 $((j,j))_{j=a}^{b}$ |
| `ST_PS M` | $M \in \mathrm{ST\_PS}$ | $M$ は標準形 |
| `step M N` | $M \Rightarrow N$ | 1 ステップ展開 |

補助的な Lean の関数について、本文で用いる意味を固定しておく。

- `List.range' a m` $= [a,\ a+1,\ \dots,\ a+m-1]$（長さ $m$ の列。$m = 0$ なら空列）。
- `List.range n` $= [0, 1, \dots, n-1]$。
- `List.take k M` $= (M_0, \dots, M_{\min(k,\,\mathrm{Lng}\,M)-1})$、本文では $M \upharpoonright k$ と書く。
- `List.dropLast M` は $M$ の末尾 1 要素を除いた列。
- `(L.map f)` は各要素に $f$ を適用した列、`(L.flatMap f)` は $f$ の値（列）を $L$ の順に連結した列。
- `Relation.ReflTransGen r` は関係 $r$ の反射推移閉包。すなわち $\mathrm{ReflTransGen}\ r\ a\ b$ とは、
  ある $m \ge 0$ と列 $a = k_0, k_1, \dots, k_m = b$ が存在して $\forall t < m,\ r\ k_t\ k_{t+1}$ が成り立つこと。
- 自然数の減法 $a - b$ はすべて切り捨て減法である。すなわち $a < b$ のとき $a - b = 0$。
- $\exists! x,\ P(x)$ は $\exists x,\ \bigl(P(x) \wedge \forall y,\ P(y) \to y = x\bigr)$ の略記。
- $\varepsilon x.\,P(x)$ は `Classical.epsilon (fun x => P x)` を表す。その唯一の性質は
  $(\exists x,\ P(x)) \to P(\varepsilon x.\,P(x))$ である（`Classical.epsilon_spec`）。

---

## §4 記法 (Notation)

Lean 移植では原論文の $\mathrm{Lng}\,M$ を `M.length` として直接用いる。本文では $\mathrm{Lng}\,M$ と書く。
この節に宣言はない。

---

## §5 定式化 (Formulation)

<a id="d-PairSeq"></a>
#### 定義 ペア数列 (D.PairSeq)

```math
\mathrm{PairSeq} := (\mathbb{N} \times \mathbb{N})^{<\omega}
```

すなわち自然数のペアの有限列全体。Lean では `abbrev PairSeq := List (ℕ × ℕ)` であり、
`List (ℕ × ℕ)` の略記にすぎない（新しい型を作らない）。

長さ $X = \mathrm{Lng}\,M$ の $M \in \mathrm{PairSeq}$ を $M = (M_0, \dots, M_{X-1})$ と書き、
$M_j \in \mathbb{N}\times\mathbb{N}$ を $M$ の第 $j$ 要素（$0$ 起算）と呼ぶ。
添字 $j$ が $j \ge X$ を満たすときは、下の [(D.entry)](#d-entry) の規約により $M_j = (0,0)$ と定める。

<a id="d-entry"></a>
#### 定義 成分 (D.entry)

$M \in \mathrm{PairSeq}$、$i, j \in \mathbb{N}$ に対し

```math
M_{i,j} := \begin{cases}
\pi_1(M_j) & (i = 0) \\
\pi_2(M_j) & (i \ne 0)
\end{cases}
\qquad
M_j := \begin{cases}
M \text{ の第 } j \text{ 要素} & (j < \mathrm{Lng}\,M) \\
(0,0) & (j \ge \mathrm{Lng}\,M)
\end{cases}
```

ここで $\pi_1, \pi_2$ はペアの第 1・第 2 成分である。Lean の定義

```lean
def entry (M : PairSeq) (i j : ℕ) : ℕ :=
  if i = 0 then (M.getD j (0, 0)).1 else (M.getD j (0, 0)).2
```

は場合分けが `i = 0` か否かであるから、$i \ge 1$ のすべての $i$ について $M_{i,j} = \pi_2(M_j)$ である。
本文で用いるのは $i \in \{0, 1\}$ の場合のみだが、定義自体はこの通りである。

この規約から直ちに次が従う。

```math
j \ge \mathrm{Lng}\,M \ \Longrightarrow\ M_{0,j} = 0 \ \wedge\ M_{1,j} = 0 .
```

実際、$j \ge \mathrm{Lng}\,M$ のとき $M_j = (0,0)$ であり、$\pi_1(0,0) = \pi_2(0,0) = 0$ である。
以降、$M_{i,j}$ を用いる箇所では常に $j < \mathrm{Lng}\,M$ が保証されるので、この既定値が読まれることはない。

---

### §5.1 親子関係 (Parent-child relations)

<a id="d-nextrel0"></a>
#### 定義 行 0 の直接親子関係 (D.nextrel0)

$M \in \mathrm{PairSeq}$、$j_0, j_1 \in \mathbb{N}$ に対し、$j_0 \to^M_0 j_1$ を次の 5 条件の連言と定める。

1. $j_0 < \mathrm{Lng}\,M$
2. $j_1 < \mathrm{Lng}\,M$
3. $j_0 < j_1$
4. $M_{0,j_0} < M_{0,j_1}$
5. $\forall j,\ \bigl(j_0 < j \ \wedge\ j < j_1\bigr) \to M_{0,j_1} \le M_{0,j}$

（[(D.entry)](#d-entry) の $M_{0,\cdot}$ を用いている。）

**補足（条件 5 の意味）.** 条件 3, 4, 5 を合わせると

```math
M_{0,j_1} = \min\{\, M_{0,j} \mid j_0 < j \le j_1 \,\} \quad\text{かつ}\quad M_{0,j_0} < M_{0,j_1}
```

と同値である。実際、条件 3 より $j_1$ 自身が添字集合 $\{ j \mid j_0 < j \le j_1 \}$ に属する。
条件 5 は「$j_0 < j < j_1$ なるすべての $j$ で $M_{0,j_1} \le M_{0,j}$」であり、
$j = j_1$ については $\le$ の反射性から $M_{0,j_1} \le M_{0,j_1}$ が成り立つ。
よって $M_{0,j_1}$ は集合 $\{M_{0,j} \mid j_0 < j \le j_1\}$ の下界であり、かつ $j = j_1$ でその値を取るから、
最小値である。逆に、この最小性から条件 5（$j_0 < j < j_1$ の場合）が従う。
なお最小値を取る $j$ は $j_1$ 以外にも存在しうる（条件 5 は等号を許す）。

<a id="d-le0"></a>
#### 定義 行 0 の祖先関係 (D.le0)

```math
j_0 \le^M_0 j_1 \ :\Longleftrightarrow\
j_0 < \mathrm{Lng}\,M \ \wedge\ j_1 < \mathrm{Lng}\,M \ \wedge\ \mathrm{ReflTransGen}\,(\to^M_0)\ j_0\ j_1 .
```

すなわち、$j_0$ と $j_1$ がともに $M$ の添字範囲にあり、かつある $m \ge 0$ と列
$j_0 = k_0, k_1, \dots, k_m = j_1$ が存在して $\forall t < m,\ k_t \to^M_0 k_{t+1}$
（[(D.nextrel0)](#d-nextrel0)）が成り立つこと。

長さの条件 1, 2 は反射推移閉包とは独立に課されている。したがって $m = 0$（$j_0 = j_1$）の場合でも
$j_0 \le^M_0 j_0$ が成り立つのは $j_0 < \mathrm{Lng}\,M$ のときに限る。

<a id="d-nextrel1"></a>
#### 定義 行 1 の直接親子関係 (D.nextrel1)

$M \in \mathrm{PairSeq}$、$j_0, j_1 \in \mathbb{N}$ に対し、$j_0 \to^M_1 j_1$ を次の 6 条件の連言と定める。

1. $j_0 < \mathrm{Lng}\,M$
2. $j_1 < \mathrm{Lng}\,M$
3. $j_0 < j_1$
4. $M_{1,j_0} < M_{1,j_1}$
5. $j_0 \le^M_0 j_1$（[(D.le0)](#d-le0)）
6. $\forall j,\ \bigl(j_0 < j \ \wedge\ j \le^M_0 j_1\bigr) \to M_{1,j_1} \le M_{1,j}$

条件 5 により、行 $1$ の親は必ず行 $0$ の祖先である。
条件 6 で $j$ が動く範囲は「$j_0 < j$ かつ $j$ が $j_1$ の行 $0$ 祖先」であり、
[(D.nextrel0)](#d-nextrel0) の条件 5（区間 $(j_0,j_1)$ 全体）とは範囲が異なる。
$j = j_1$ は条件 6 の前提を満たす（$j_0 < j_1$ は条件 3、$j_1 \le^M_0 j_1$ は条件 2 と
$\mathrm{ReflTransGen}$ の反射性から従う）が、そのときの結論 $M_{1,j_1} \le M_{1,j_1}$ は
$\le$ の反射性から成り立つので、条件 6 の内容は $j \ne j_1$ の場合に尽きる。

<a id="d-nextR"></a>
#### 定義 行付き直接親子関係 (D.nextR)

```math
j_0 \to^M_i j_1 \ :\Longleftrightarrow\
\begin{cases}
j_0 \to^M_0 j_1 & (i = 0) \\
j_0 \to^M_1 j_1 & (i \ne 0)
\end{cases}
```

（[(D.nextrel0)](#d-nextrel0), [(D.nextrel1)](#d-nextrel1)）。
[(D.entry)](#d-entry) と同じく、場合分けは `i = 0` か否かであるから、$i \ge 1$ のすべての $i$ で
$\to^M_i$ は $\to^M_1$ に一致する。[(D.oper)](#d-oper) がこの関係に渡す $i$ は
$\mathrm{idx}_1(M, j_1)$（[(D.idx1)](#d-idx1)）の値、すなわち $0$ か $1$ である。

どちらの場合も定義の条件 1–3 から

```math
j_0 \to^M_i j_1 \ \Longrightarrow\ j_0 < j_1 < \mathrm{Lng}\,M
```

が成り立つ。

---

### §5.2 前者関数 (Predecessor functions)

<a id="d-Pred"></a>
#### 定義 前者 (D.Pred)

```math
\mathrm{Pred}\,M := \begin{cases}
M & (\mathrm{Lng}\,M \le 1) \\
(M_0, \dots, M_{\mathrm{Lng}\,M - 2}) & (\mathrm{Lng}\,M \ge 2)
\end{cases}
```

第 2 の場合は `M.dropLast`、すなわち末尾 1 要素を除いた列である。長さは

```math
\mathrm{Lng}(\mathrm{Pred}\,M) = \begin{cases}
\mathrm{Lng}\,M & (\mathrm{Lng}\,M \le 1) \\
\mathrm{Lng}\,M - 1 & (\mathrm{Lng}\,M \ge 2)
\end{cases}
```

である。空列 $M = ()$ と長さ 1 の列に対しては $\mathrm{Pred}\,M = M$ であり、長さは減らない。

---

### §5.3 基本列 (Fundamental sequence, $M[n]$)

<a id="d-idx1"></a>
#### 定義 親を探す行番号 (D.idx1)

```math
\mathrm{idx}_1(M, j_1) := \begin{cases}
1 & (0 < M_{1,j_1}) \\
0 & (M_{1,j_1} = 0)
\end{cases}
```

（[(D.entry)](#d-entry)）。値域は $\{0, 1\}$ である。

<a id="d-hasParent"></a>
#### 定義 親の一意存在 (D.hasParent)

```math
\mathrm{hasParent}(M, i, j_1) \ :\Longleftrightarrow\ \exists!\, j_0,\ j_0 \to^M_i j_1 ,
```

すなわち

```math
\exists j_0,\ \Bigl( j_0 \to^M_i j_1 \ \wedge\ \forall j,\ (j \to^M_i j_1) \to j = j_0 \Bigr)
```

（[(D.nextR)](#d-nextR)）。

<a id="d-parent"></a>
#### 定義 親 (D.parent)

```math
\mathrm{par}^M_i(j_1) := \varepsilon\, j_0.\ \bigl(j_0 \to^M_i j_1\bigr)
```

（[(D.nextR)](#d-nextR)）。Hilbert の選択作用素 `Classical.epsilon` による定義であり、
関数としては全域だが計算可能ではない（Lean 側でも `noncomputable`）。

**性質（Isabelle の `THE` との一致）.**
$\mathrm{hasParent}(M, i, j_1)$（[(D.hasParent)](#d-hasParent)）が成り立つならば、

```math
\mathrm{par}^M_i(j_1) \to^M_i j_1
\qquad\text{かつ}\qquad
\forall j,\ (j \to^M_i j_1) \to j = \mathrm{par}^M_i(j_1) .
```

*証明.* $\mathrm{hasParent}(M,i,j_1)$ は、ある $a$ が存在して
$a \to^M_i j_1$ かつ $\forall j,\ (j \to^M_i j_1) \to j = a$ を満たすことである。
特に $\exists j_0,\ j_0 \to^M_i j_1$ が成り立つから、$\varepsilon$ の性質
$(\exists x, P(x)) \to P(\varepsilon x.\,P(x))$ を $P(x) :\equiv (x \to^M_i j_1)$ に適用して
$\mathrm{par}^M_i(j_1) \to^M_i j_1$ を得る。これに一意性の条項を適用すると
$\mathrm{par}^M_i(j_1) = a$ である。よって任意の $j$ について $j \to^M_i j_1$ ならば
$j = a = \mathrm{par}^M_i(j_1)$。$\square$

したがって $\mathrm{hasParent}$ の仮定の下で $\mathrm{par}^M_i(j_1)$ は $j_0 \to^M_i j_1$ を満たす唯一の $j_0$ である。
$\mathrm{hasParent}$ が成り立たない場合の $\mathrm{par}^M_i(j_1)$ の値は定義から決まらないが、
下の [(D.oper)](#d-oper) では $\mathrm{hasParent}$ が成り立つ分岐でしか $\mathrm{par}$ を使わない。

<a id="d-oper"></a>
#### 定義 基本列 (D.oper)

$M \in \mathrm{PairSeq}$、$n \in \mathbb{N}$ に対し $M[n]$ を次で定める。
$j_1 := \mathrm{Lng}\,M - 1$（切り捨て減法）とおく。

**(a) $j_1 = 0$ のとき**（すなわち $\mathrm{Lng}\,M \le 1$）:

```math
M[n] := M .
```

**(b) $j_1 \ne 0$ かつ $M_{0,j_1} = 0 \wedge M_{1,j_1} = 0$ のとき**（末尾のペアが $(0,0)$）:

```math
M[n] := \mathrm{Pred}\,M
```

（[(D.Pred)](#d-Pred)）。

**(c) $j_1 \ne 0$、$\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)$、かつ
$\neg\,\mathrm{hasParent}(M, i_1, j_1)$ のとき**（$i_1 := \mathrm{idx}_1(M, j_1)$、[(D.idx1)](#d-idx1)）:

```math
M[n] := \mathrm{Pred}\,M .
```

**(d) それ以外のとき**、すなわち $j_1 \ne 0$、$\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)$、
$\mathrm{hasParent}(M, i_1, j_1)$ のとき: $j_0 := \mathrm{par}^M_{i_1}(j_1)$（[(D.parent)](#d-parent)）、

```math
d_0 := \begin{cases} M_{0,j_1} - M_{0,j_0} & (0 < i_1) \\ 0 & (i_1 = 0) \end{cases}
\qquad
d_1 := \begin{cases} M_{1,j_1} - M_{1,j_0} & (1 < i_1) \\ 0 & (i_1 \le 1) \end{cases}
```

とおき、

```math
M[n] := (M \upharpoonright j_0) \ \mathbin{+\!\!+} \ B_0 \mathbin{+\!\!+} B_1 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
```

```math
B_k := \bigl(\ (\,M_{0,j} + k\,d_0,\ M_{1,j} + k\,d_1\,)\ \bigr)_{j = j_0}^{j_1 - 1}
\qquad (k = 0, 1, \dots, n-1) .
```

ここで $M \upharpoonright j_0 = (M_0, \dots, M_{j_0-1})$ は先頭 $j_0$ 要素であり、
$B_k$ は添字 $j = j_0, j_0+1, \dots, j_1-1$ を順に走る長さ $j_1 - j_0$ の列である
（Lean の `List.range' j0 (j1 - j0)` は $[j_0, \dots, j_1-1]$ であり、$j_1$ 自身は**含まない**）。
$n = 0$ のときは $B_k$ が 1 つも現れず $M[0] = M \upharpoonright j_0$ である。

Lean の記法 `M⟦n⟧` は `oper M n` の略記である。

**補足 1（$d_1$ は常に $0$）.**
[(D.idx1)](#d-idx1) より $i_1 = \mathrm{idx}_1(M, j_1) \in \{0, 1\}$ である。よって条件 $1 < i_1$ は
偽であり、分岐 (d) では常に $d_1 = 0$ である。したがって $B_k$ の第 2 成分は $M_{1,j}$ そのもの、
すなわちコピーによって増加するのは行 $0$ の値のみである。

**補足 2（$d_0$ の 2 つの場合）.**
$i_1 = 1$ のとき（すなわち $M_{1,j_1} > 0$ のとき）、[(D.nextR)](#d-nextR) より
$j_0 \to^M_{i_1} j_1$ は $j_0 \to^M_1 j_1$ であり、[(D.nextrel1)](#d-nextrel1) の条件 5 から
$j_0 \le^M_0 j_1$ が成り立つ。このとき $d_0 = M_{0,j_1} - M_{0,j_0}$ である。
$i_1 = 0$ のとき（すなわち $M_{1,j_1} = 0$ のとき）は $d_0 = 0$ であり、補足 1 と合わせて
$d_0 = d_1 = 0$ だから、すべての $k$ について

```math
B_k = \bigl(\,(M_{0,j},\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1} = (M_{j_0}, M_{j_0+1}, \dots, M_{j_1-1})
```

である（最後の等号は、$j < \mathrm{Lng}\,M$ のとき [(D.entry)](#d-entry) より
$(M_{0,j}, M_{1,j}) = (\pi_1(M_j), \pi_2(M_j)) = M_j$ であることによる。分岐 (d) では
$j_0 \le j < j_1 < \mathrm{Lng}\,M$）。すなわち $M[n]$ は
$M \upharpoonright j_0$ の後ろに区間 $[j_0, j_1)$ の要素をそのまま $n$ 回並べた列である。

**補足 3（長さ）.** 分岐 (d) において

```math
\mathrm{Lng}\,(M[n]) = j_0 + n\,(j_1 - j_0) .
```

*証明.* 分岐 (d) では $\mathrm{hasParent}(M, i_1, j_1)$ が成り立つから、[(D.parent)](#d-parent) の性質より
$j_0 \to^M_{i_1} j_1$、したがって [(D.nextR)](#d-nextR) の後の注意により $j_0 < j_1 < \mathrm{Lng}\,M$ である。
よって $\mathrm{Lng}(M \upharpoonright j_0) = \min(j_0, \mathrm{Lng}\,M) = j_0$。
各 $B_k$ は $[j_0, \dots, j_1-1]$ に写像を施した列だから $\mathrm{Lng}\,B_k = j_1 - j_0$。
連結の長さは長さの和だから、全体の長さは $j_0 + n(j_1-j_0)$ である。$\square$

分岐 (a) では $\mathrm{Lng}(M[n]) = \mathrm{Lng}\,M$、分岐 (b), (c) では
$j_1 \ne 0$ より $\mathrm{Lng}\,M \ge 2$ だから $\mathrm{Lng}(M[n]) = \mathrm{Lng}\,M - 1$ である
（[(D.Pred)](#d-Pred)）。

---

## §6.5 / §6.7 標準形 (Standard form)

<a id="d-diagSeq"></a>
#### 定義 対角列 (D.diagSeq)

$a, b \in \mathbb{N}$ に対し

```math
\Delta_a^b := \bigl(\,(j, j)\,\bigr)_{j=a}^{b}
= \bigl((a,a),\ (a+1,a+1),\ \dots,\ (b,b)\bigr) .
```

Lean では `(List.range' a (b + 1 - a)).map (fun j => (j, j))` であり、長さは切り捨て減法で
$b + 1 - a$ である。したがって

```math
\mathrm{Lng}\,\Delta_a^b = \begin{cases} b + 1 - a & (a \le b) \\ 0 & (a > b) \end{cases}
```

であり、$a > b$ のとき $\Delta_a^b$ は空列である。特に

```math
\Delta_0^v = \bigl((0,0), (1,1), \dots, (v,v)\bigr), \qquad \mathrm{Lng}\,\Delta_0^v = v + 1 .
```

成分は、$a \le j \le b$ のとき $(\Delta_a^b)_{0,\,j-a} = (\Delta_a^b)_{1,\,j-a} = j$ である
（[(D.entry)](#d-entry)）。

<a id="d-ST_PS"></a>
#### 定義 標準形 (D.ST_PS)

$\mathrm{ST\_PS} \subseteq \mathrm{PairSeq}$ を、次の 2 つの導入規則で生成される**最小の**集合と定める。

```math
\frac{\ }{\ \Delta_0^v \in \mathrm{ST\_PS}\ }\ \text{(diag)}\quad (v \in \mathbb{N})
\qquad\qquad
\frac{\ M \in \mathrm{ST\_PS} \qquad 1 \le n\ }{\ M[n] \in \mathrm{ST\_PS}\ }\ \text{(oper)}
```

（[(D.diagSeq)](#d-diagSeq), [(D.oper)](#d-oper)）。すなわち Lean の

```lean
inductive ST_PS : PairSeq → Prop where
  | diag (v : ℕ) : ST_PS (diagSeq 0 v)
  | oper {M : PairSeq} {n : ℕ} : ST_PS M → 1 ≤ n → ST_PS (M⟦n⟧)
```

に対応する。言い換えると、$M \in \mathrm{ST\_PS}$ とは、ある $v \in \mathbb{N}$、ある $m \ge 0$、
ある $n_1, \dots, n_m \ge 1$ が存在して

```math
M = \Delta_0^v[n_1][n_2]\cdots[n_m]
```

と書けることである。

**帰納法原理.** 「最小の集合」であることは、次の形で使われる。
任意の述語 $P : \mathrm{PairSeq} \to \mathrm{Prop}$ について、

1. （基底段）$\forall v \in \mathbb{N},\ P(\Delta_0^v)$
2. （帰納段）$\forall M, n,\ \bigl(M \in \mathrm{ST\_PS} \ \wedge\ P(M)\ \wedge\ 1 \le n\bigr) \to P(M[n])$

が成り立つならば $\forall M,\ M \in \mathrm{ST\_PS} \to P(M)$ が成り立つ。
これが Lean の `ST_PS.rec`（帰納的述語に対して自動生成される除去規則）である。
帰納段では帰納法の仮定として $P(M)$ に加えて $M \in \mathrm{ST\_PS}$ 自身も使ってよいことに注意する。

**基底を $\Delta_0^v$ に限ることについて.**
規則 (diag) の基底は $u = 0$ から始まる対角列 $\Delta_0^v$ のみであり、
一般の $\Delta_u^v$（$u > 0$）は基底に含めない。$\Delta_u^v$（$u > 0$）を基底に加えると、
第 $0$ 要素が $(u,u) \ne (0,0)$ である列も $\mathrm{ST\_PS}$ に属することになる。
ここでは、基底が $\Delta_0^v$ に限られているという定義上の事実のみを記録する。
この選択が後続の章の不変量にどう効くかは、それらの章で個別に示される。

<a id="d-step"></a>
#### 定義 1 ステップ展開 (D.step)

関係 $\Rightarrow\ \subseteq \mathrm{PairSeq} \times \mathrm{PairSeq}$ を、次の 1 つの導入規則で生成される
最小の関係と定める。

```math
\frac{\ 1 < \mathrm{Lng}\,M \qquad 1 \le n\ }{\ M \Rightarrow M[n]\ }\ \text{(step\_oper)}
```

（[(D.oper)](#d-oper)）。

**場合分け原理（逆向きの読み）.** 導入規則が 1 つしかないから、

```math
M \Rightarrow N \quad\Longleftrightarrow\quad \exists n,\ \bigl(1 < \mathrm{Lng}\,M \ \wedge\ 1 \le n \ \wedge\ N = M[n]\bigr) .
```

$(\Leftarrow)$ は規則 (step\_oper) そのもの。$(\Rightarrow)$ は Lean の `step.rec`（唯一の構成子に対する場合分け）である。

**補足（長さ制限 $1 < \mathrm{Lng}\,M$ の役割）.**
$\mathrm{Lng}\,M \le 1$ ならば $j_1 = \mathrm{Lng}\,M - 1 = 0$（切り捨て減法。$\mathrm{Lng}\,M = 0$ のときも
$0 - 1 = 0$）であるから、[(D.oper)](#d-oper) の分岐 (a) により、任意の $n$ について $M[n] = M$ である。
導入規則の前提 $1 < \mathrm{Lng}\,M$ は、この $M \Rightarrow M$ という形の対を $\Rightarrow$ から除いている。

この $\Rightarrow$ に無限前進列が存在しないことが、本証明全体の目標である
（[(T.no_infinite_expansion_holds)](Final.md#t-no_infinite_expansion_holds)、
[(T.PSS_terminates_unconditional)](Final.md#t-PSS_terminates_unconditional)）。
