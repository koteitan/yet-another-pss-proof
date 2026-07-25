[← README](README.md)

<a id="d-PairSeq"></a>
## 定義: ペア数列 (D.PairSeq)

自然数の対の有限列を**ペア数列**と呼び、その全体を $`\mathrm{PairSeq}`$ と書く。

```math
\mathrm{PairSeq} := (\mathbb{N} \times \mathbb{N})^{\lt \omega}
```

$`M \in \mathrm{PairSeq}`$ の長さを $`\lvert M\rvert`$、第 $`j`$ 要素（$`j`$ は $`0`$ から数える）を
$`M_j`$ と書く。$`M = (M_0, M_1, \dots, M_{\lvert M\rvert - 1})`$ である。

<a id="d-entry"></a>
## 定義: 成分 (D.entry)

$`M \in \mathrm{PairSeq}`$、$`i, j \in \mathbb{N}`$ に対し

```math
M_{i,j} := \begin{cases}
\pi_1\bigl(M\langle j\rangle\bigr) & (i = 0) \cr
\pi_2\bigl(M\langle j\rangle\bigr) & (i \ne 0)
\end{cases}
```

とおく。ここで $`\pi_1, \pi_2`$ は対の第 1・第 2 成分であり、$`M\langle j\rangle`$ は

```math
M\langle j\rangle := \begin{cases}
M_j & (j \lt \lvert M\rvert) \cr
(0,0) & (j \ge \lvert M\rvert)
\end{cases}
```

である。すなわち添字が範囲外のときは $`(0,0)`$ を読む。とくに

```math
j \ge \lvert M\rvert \ \Longrightarrow\ M_{0,j} = M_{1,j} = 0 .
```

$`M_{0,j}`$ を第 $`j`$ 列の**行 $`0`$ の値**、$`M_{1,j}`$ を**行 $`1`$ の値**と呼ぶ。
$`i \ne 0`$ のときは $`i`$ の値によらず第 2 成分を読むから、以下で $`M_{i,j}`$ を
$`i \in \{0,1\}`$ についてのみ用いる。

<a id="d-nextrel0"></a>
## 定義: 行 0 の親子関係 (D.nextrel0)

$`M \in \mathrm{PairSeq}`$、$`j_0, j_1 \in \mathbb{N}`$ に対し、$`j_0 \to^M_0 j_1`$ を
次の 5 条件の連言として定める。

```math
\begin{aligned}
&(1)\ j_0 \lt \lvert M\rvert, \cr
&(2)\ j_1 \lt \lvert M\rvert, \cr
&(3)\ j_0 \lt j_1, \cr
&(4)\ M_{0,j_0} \lt M_{0,j_1}, \cr
&(5)\ \forall j\ \bigl(j_0 \lt j \wedge j \lt j_1 \to M_{0,j_1} \le M_{0,j}\bigr).
\end{aligned}
```

条件 (5) は、区間 $`(j_0, j_1)`$ に $`M_{0,j_1}`$ より小さい行 $`0`$ の値が現れないことを言う。
$`j_0 \to^M_0 j_1`$ のとき $`j_0`$ を $`j_1`$ の**行 $`0`$ の親**と呼ぶ。

<a id="d-le0"></a>
## 定義: 行 0 の祖先関係 (D.le0)

$`j_0 \le^M_0 j_1`$ を次の 3 条件の連言として定める。

```math
\begin{aligned}
&(1)\ j_0 \lt \lvert M\rvert, \cr
&(2)\ j_1 \lt \lvert M\rvert, \cr
&(3)\ j_0 \mathbin{(\to^M_0)^{*}} j_1 .
\end{aligned}
```

ここで $`(\to^M_0)^{*}`$ は $`\to^M_0`$ の反射推移閉包、すなわち

```math
j_0 \mathbin{(\to^M_0)^{*}} j_1 \iff
\exists k \ge 0,\ \exists k_0, \dots, k_k,\
k_0 = j_0 \wedge k_k = j_1 \wedge \forall m \lt k,\ k_m \to^M_0 k_{m+1}
```

である（$`k = 0`$ のとき、すなわち $`j_0 = j_1`$ のときも含む）。

<a id="d-nextrel1"></a>
## 定義: 行 1 の親子関係 (D.nextrel1)

$`j_0 \to^M_1 j_1`$ を次の 6 条件の連言として定める。

```math
\begin{aligned}
&(1)\ j_0 \lt \lvert M\rvert, \cr
&(2)\ j_1 \lt \lvert M\rvert, \cr
&(3)\ j_0 \lt j_1, \cr
&(4)\ M_{1,j_0} \lt M_{1,j_1}, \cr
&(5)\ j_0 \le^M_0 j_1, \cr
&(6)\ \forall j\ \bigl(j_0 \lt j \wedge j \le^M_0 j_1 \to M_{1,j_1} \le M_{1,j}\bigr).
\end{aligned}
```

条件 (5) により行 $`1`$ の親子関係は行 $`0`$ の祖先関係を細分する。
条件 (6) の最小性は、条件 (5) の意味での祖先の鎖に沿ってのみ課される。

<a id="d-nextR"></a>
## 定義: 行つき親子関係 (D.nextR)

$`i \in \mathbb{N}`$ に対し

```math
j_0 \to^M_i j_1 :\iff \begin{cases}
j_0 \to^M_0 j_1 & (i = 0) \cr
j_0 \to^M_1 j_1 & (i \ne 0)
\end{cases}
```

とおく。

<a id="d-Pred"></a>
## 定義: 前者 (D.Pred)

```math
\mathrm{Pred}\,M := \begin{cases}
M & (\lvert M\rvert \le 1) \cr
(M_0, \dots, M_{\lvert M\rvert - 2}) & (\lvert M\rvert \ge 2)
\end{cases}
```

すなわち末尾の 1 列を落とす操作であり、長さ $`1`$ 以下の列の上では恒等である。

<a id="d-idx1"></a>
## 定義: 探索行 (D.idx1)

```math
\mathrm{idx}_1(M, j_1) := \begin{cases}
1 & (0 \lt M_{1,j_1}) \cr
0 & (M_{1,j_1} = 0)
\end{cases}
```

第 $`j_1`$ 列の親をどちらの行で探すかを与える。値は $`0`$ か $`1`$ のいずれかである。

<a id="d-hasParent"></a>
## 定義: 親の存在 (D.hasParent)

```math
\mathrm{hasParent}(M, i, j_1) :\iff \exists!\, j_0,\ j_0 \to^M_i j_1
```

すなわち $`j_0 \to^M_i j_1`$ をみたす $`j_0`$ が存在し、かつ一意である。

<a id="d-parent"></a>
## 定義: 親 (D.parent)

```math
\mathrm{par}^M_i(j_1) := \varepsilon j_0.\ \bigl(j_0 \to^M_i j_1\bigr)
```

ここで $`\varepsilon`$ は Hilbert の選択作用素である。
$`\mathrm{hasParent}(M, i, j_1)`$ が成り立つとき、$`\mathrm{par}^M_i(j_1)`$ は
$`j_0 \to^M_i j_1`$ をみたす一意の $`j_0`$ に等しい。実際、そのような $`j_0`$ は存在するから
$`\varepsilon`$ はそれをみたす値を返し、一意性よりその値は $`j_0`$ に限る。

<a id="d-oper"></a>
## 定義: 基本列 (D.oper)

$`M \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ に対し $`M[n]`$ を次で定める。
$`j_1 := \lvert M\rvert - 1`$ とおく（自然数の減法は切り捨て減法であり、
$`\lvert M\rvert = 0`$ のとき $`j_1 = 0`$）。

**(a) $`j_1 = 0`$ のとき**、すなわち $`\lvert M\rvert \le 1`$ のとき:

```math
M[n] := M .
```

**(b) $`j_1 \ne 0`$ かつ $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき**、すなわち末尾の列が $`(0,0)`$ のとき:

```math
M[n] := \mathrm{Pred}\,M .
```

**(c) $`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ のとき**（$`i_1 := \mathrm{idx}_1(M, j_1)`$）:

```math
M[n] := \mathrm{Pred}\,M .
```

**(d) それ以外のとき**、すなわち $`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、
$`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。$`j_0 := \mathrm{par}^M_{i_1}(j_1)`$ とおき、

```math
d_0 := \begin{cases} M_{0,j_1} - M_{0,j_0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
\qquad
d_1 := \begin{cases} M_{1,j_1} - M_{1,j_0} & (1 \lt i_1) \cr 0 & (i_1 \le 1) \end{cases}
```

と定めて

```math
M[n] := (M_0, \dots, M_{j_0 - 1}) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} B_1 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
```

```math
B_k := \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j} + k\,d_1)\,\bigr)_{j = j_0}^{j_1 - 1}
\qquad (k = 0, 1, \dots, n-1) .
```

$`B_k`$ は添字 $`j = j_0, j_0+1, \dots, j_1-1`$ を順に走る長さ $`j_1 - j_0`$ の列であり、
$`j_1`$ 自身は**含まない**。$`n = 0`$ のときは $`B_k`$ が 1 つも現れず
$`M[0] = (M_0, \dots, M_{j_0-1})`$ である。

<a id="d-diagSeq"></a>
## 定義: 対角列 (D.diagSeq)

$`a, b \in \mathbb{N}`$ に対し

```math
\Delta_a^b := \bigl((a,a),\ (a+1,a+1),\ \dots,\ (b,b)\bigr)
```

とおく。長さは $`b + 1 - a`$（切り捨て減法）であり、$`a \gt b`$ のときは空列である。

<a id="d-ST_PS"></a>
## 定義: 標準形 (D.ST_PS)

$`\mathrm{ST\_PS} \subseteq \mathrm{PairSeq}`$ を、次の 2 つの規則で閉じた**最小**の集合として定める。

```math
\begin{aligned}
&\text{(diag)}\quad \forall v \in \mathbb{N},\ \Delta_0^v \in \mathrm{ST\_PS}, \cr
&\text{(oper)}\quad \forall M,\ \forall n \ge 1,\ M \in \mathrm{ST\_PS} \to M[n] \in \mathrm{ST\_PS} .
\end{aligned}
```

最小性は次の帰納法の原理として使う。$`\mathrm{PairSeq}`$ 上の述語 $`\Phi`$ が

```math
\forall v,\ \Phi(\Delta_0^v)
\qquad\text{かつ}\qquad
\forall M,\ \forall n \ge 1,\ \bigl(M \in \mathrm{ST\_PS} \wedge \Phi(M)\bigr) \to \Phi(M[n])
```

をみたすならば、$`\forall M \in \mathrm{ST\_PS},\ \Phi(M)`$ が成り立つ。
以下ではこれを「$`\mathrm{ST\_PS}`$ の導出に関する帰納法」と呼ぶ。

<a id="d-step"></a>
## 定義: 展開 (D.step)

$`M \Rightarrow N`$ を、次の 1 つの規則で生成される最小の関係として定める。

```math
\text{(step\_oper)}\quad
1 \lt \lvert M\rvert \ \wedge\ 1 \le n
\ \Longrightarrow\ M \Rightarrow M[n] .
```

すなわち $`M \Rightarrow N`$ は、$`1 \lt \lvert M\rvert`$ であり、かつ $`N = M[n]`$ となる
$`n \ge 1`$ が存在することと同値である。
