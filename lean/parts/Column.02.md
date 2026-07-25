<a id="d-r1ok"></a>
## 定義: 行 1 の規律 (D.r1ok)

$`M \in \mathrm{PairSeq}`$ に対し、命題 $`\mathrm{r1ok}(M)`$ を次のものとして定める。

> 任意の $`j`$ について、$`j \lt \lvert M\rvert`$ かつ $`0 \lt M_{0,j}`$ ならば、
> 次の 4 条件をみたす $`k`$ が存在する。

```math
\begin{aligned}
&(1)\ k \lt j, \cr
&(2)\ M_{0,k} + 1 = M_{0,j}, \cr
&(3)\ \forall l\ \bigl(k \lt l \wedge l \lt j \to M_{0,j} \le M_{0,l}\bigr), \cr
&(4)\ M_{1,j} \le M_{1,k} + 1 .
\end{aligned}
```

条件 (1)〜(4) をみたす $`k`$ を、列 $`M`$ における第 $`j`$ 列の**証人**と呼ぶ。

<a id="t-diagSeq0_length"></a>
## 定理: 対角列の長さ (T.diagSeq0_length)

### 定理

任意の $`v \in \mathbb{N}`$ に対し $`\lvert \Delta_0^v\rvert = v + 1`$。

### 証明

$`\Delta_a^b`$ の定義（D.diagSeq）より
$`\Delta_0^v = ((0,0),(1,1),\dots,(v,v))`$ であり、その長さは $`v + 1 - 0`$、
すなわち $`v + 1`$ である。∎

<a id="t-diagSeq0_getD"></a>
## 定理: 対角列の成分 (T.diagSeq0_getD)

### 定理

任意の $`v, i \in \mathbb{N}`$ に対し、$`i \lt v + 1`$ ならば
$`\Delta_0^v\langle i\rangle = (i,i)`$。

### 証明

[T.diagSeq0_length](#t-diagSeq0_length) より $`\lvert \Delta_0^v\rvert = v+1`$ であり、
仮定 $`i \lt v+1`$ から添字 $`i`$ は範囲内である。よって $`M\langle i\rangle`$ の定義（D.entry）の
第 1 の場合が選ばれ、$`\Delta_0^v\langle i\rangle`$ は $`\Delta_0^v`$ の第 $`i`$ 要素である。
$`\Delta_a^b`$ の定義（D.diagSeq）より $`\Delta_0^v = ((0,0),(1,1),\dots,(v,v))`$ であるから、
その第 $`i`$ 要素は $`(i,i)`$ である。∎

<a id="t-r1ok_diagSeq"></a>
## 定理: 対角列は行 1 の規律をみたす (T.r1ok_diagSeq)

### 定理

任意の $`v \in \mathbb{N}`$ に対し $`\mathrm{r1ok}(\Delta_0^v)`$。

### 証明

$`j \lt \lvert \Delta_0^v\rvert`$ かつ $`0 \lt (\Delta_0^v)_{0,j}`$ とする。
[T.diagSeq0_length](#t-diagSeq0_length) より $`j \lt v+1`$ であり、
[T.diagSeq0_getD](#t-diagSeq0_getD) より $`\Delta_0^v\langle j\rangle = (j,j)`$、
したがって $`(\Delta_0^v)_{0,j} = j`$ である。仮定より $`0 \lt j`$。

証人として $`k := j - 1`$ を取る。$`0 \lt j`$ より $`j - 1 + 1 = j`$ であり、
$`j - 1 \lt j \lt v+1`$ であるから [T.diagSeq0_getD](#t-diagSeq0_getD) が $`j-1`$ にも使えて
$`\Delta_0^v\langle j-1\rangle = (j-1, j-1)`$ である。
$`\mathrm{r1ok}`$ の定義（D.r1ok）の 4 条件を確かめる。

**(1)** $`0 \lt j`$ より $`j - 1 \lt j`$。

**(2)** $`(\Delta_0^v)_{0,j-1} + 1 = (j-1) + 1 = j = (\Delta_0^v)_{0,j}`$。

**(3)** $`j - 1 \lt l`$ かつ $`l \lt j`$ をみたす $`l`$ を取ると、$`0 \lt j`$ より
$`j - 1 \lt l \lt j = (j-1) + 1`$ となり、そのような自然数 $`l`$ は存在しない。
よって前件が偽であり、条件は成り立つ。

**(4)** $`(\Delta_0^v)_{1,j} = j`$、$`(\Delta_0^v)_{1,j-1} + 1 = (j-1) + 1 = j`$ であるから
$`(\Delta_0^v)_{1,j} \le (\Delta_0^v)_{1,j-1} + 1`$。∎

<a id="t-getD_take"></a>
## 定理: 前部分列の成分 (T.getD_take)

### 定理

$`M \in \mathrm{PairSeq}`$、$`m, j \in \mathbb{N}`$ とし、$`\mathrm{take}_m M`$ を $`M`$ の先頭
$`m`$ 要素からなる列とする。$`j \lt m`$ ならば

```math
(\mathrm{take}_m M)\langle j\rangle = M\langle j\rangle .
```

### 証明

$`\mathrm{take}_m M`$ の第 $`j`$ 要素は、$`j \lt m`$ のとき $`M`$ の第 $`j`$ 要素であり、
$`M`$ の第 $`j`$ 要素が存在しないとき（$`j \ge \lvert M\rvert`$ のとき）は
$`\mathrm{take}_m M`$ の第 $`j`$ 要素も存在しない。すなわち $`j \lt m`$ のとき

```math
j \lt \lvert \mathrm{take}_m M\rvert \iff j \lt \lvert M\rvert
```

であり、そのとき両者の第 $`j`$ 要素は一致する。
$`M\langle j\rangle`$ の定義（D.entry）は、添字が範囲内なら第 $`j`$ 要素、範囲外なら
$`(0,0)`$ を返すものであったから、両辺は一致する。∎

<a id="t-r1ok_take"></a>
## 定理: 行 1 の規律は前部分列に遺伝する (T.r1ok_take)

### 定理

$`\mathrm{r1ok}(M)`$ ならば、任意の $`m \in \mathbb{N}`$ に対し
$`\mathrm{r1ok}(\mathrm{take}_m M)`$。

### 証明

$`j \lt \lvert \mathrm{take}_m M\rvert`$ かつ $`0 \lt (\mathrm{take}_m M)_{0,j}`$ とする。
$`\lvert \mathrm{take}_m M\rvert = \min(m, \lvert M\rvert)`$ であるから
$`j \lt m`$ かつ $`j \lt \lvert M\rvert`$ である。
[T.getD_take](#t-getD_take) より $`(\mathrm{take}_m M)\langle j\rangle = M\langle j\rangle`$ であり、
したがって $`0 \lt M_{0,j}`$ である。

仮定 $`\mathrm{r1ok}(M)`$ を $`j`$ に適用して、$`\mathrm{r1ok}`$ の定義（D.r1ok）の条件
(1)〜(4) をみたす $`k`$ を得る。この $`k`$ が $`\mathrm{take}_m M`$ における
第 $`j`$ 列の証人でもあることを示す。条件 (1) $`k \lt j`$ は共通である。
$`k \lt j \lt m`$ であるから [T.getD_take](#t-getD_take) が $`k`$ にも使えて
$`(\mathrm{take}_m M)\langle k\rangle = M\langle k\rangle`$ である。よって条件 (2) と (4) は
$`M`$ についての条件 (2), (4) そのものになる。
条件 (3) については、$`k \lt l`$ かつ $`l \lt j`$ をみたす $`l`$ に対し $`l \lt j \lt m`$
であるから [T.getD_take](#t-getD_take) より
$`(\mathrm{take}_m M)\langle l\rangle = M\langle l\rangle`$ であり、
$`M`$ についての条件 (3) がそのまま条件になる。∎

<a id="t-r1ok_dropLast"></a>
## 定理: 行 1 の規律は末尾除去に遺伝する (T.r1ok_dropLast)

### 定理

$`\mathrm{r1ok}(M)`$ ならば $`\mathrm{r1ok}(\mathrm{dropLast}\,M)`$。

### 証明

$`\mathrm{dropLast}\,M = \mathrm{take}_{\lvert M\rvert - 1} M`$ である
（どちらも $`M`$ の先頭 $`\lvert M\rvert - 1`$ 要素からなる列である）。
よって [T.r1ok_take](#t-r1ok_take) を $`m := \lvert M\rvert - 1`$ に適用すればよい。∎

<a id="t-getD_append_left"></a>
## 定理: 連結列の左側の成分 (T.getD_append_left)

### 定理

$`G, X \in \mathrm{PairSeq}`$、$`i \lt \lvert G\rvert`$ ならば
$`(G \mathbin{+\!\!+} X)\langle i\rangle = G\langle i\rangle`$。

### 証明

$`i \lt \lvert G\rvert`$ のとき、連結列 $`G \mathbin{+\!\!+} X`$ の第 $`i`$ 要素は
$`G`$ の第 $`i`$ 要素である。どちらの添字も範囲内であるから、
$`M\langle i\rangle`$ の定義（D.entry）の第 1 の場合が両辺で選ばれ、値は一致する。∎

<a id="t-getD_append_right"></a>
## 定理: 連結列の右側の成分 (T.getD_append_right)

### 定理

$`G, X \in \mathrm{PairSeq}`$、$`\lvert G\rvert \le i`$ ならば
$`(G \mathbin{+\!\!+} X)\langle i\rangle = X\langle i - \lvert G\rvert\rangle`$。

### 証明

$`\lvert G\rvert \le i`$ のとき、$`G \mathbin{+\!\!+} X`$ の第 $`i`$ 要素が存在することと
$`X`$ の第 $`i - \lvert G\rvert`$ 要素が存在することは同値であり
（$`i \lt \lvert G\rvert + \lvert X\rvert \iff i - \lvert G\rvert \lt \lvert X\rvert`$）、
存在するときは両者は同じ要素である。
よって $`M\langle i\rangle`$ の定義（D.entry）の場合分けが両辺で一致し、値も一致する。∎

<a id="t-index_decomp"></a>
## 定理: 添字の商剰余分解 (T.index_decomp)

### 定理

$`0 \lt L`$ かつ $`i \lt n L`$ ならば、$`k \lt n`$、$`q \lt L`$、$`i = k L + q`$ をみたす
$`k, q \in \mathbb{N}`$ が存在する。

### 証明

$`k := \lfloor i / L\rfloor`$、$`q := i \bmod L`$ と取る。

$`q \lt L`$：$`0 \lt L`$ であるから剰余は $`L`$ 未満である。

$`k \lt n`$：除法の等式 $`i = L\lfloor i/L\rfloor + (i \bmod L)`$ より
$`L\lfloor i/L\rfloor \le i`$ である。もし $`n \le \lfloor i/L\rfloor`$ ならば
$`nL \le L\lfloor i/L\rfloor \le i`$ となり、仮定 $`i \lt nL`$ に矛盾する。
よって $`\lfloor i/L\rfloor \lt n`$。

$`i = kL + q`$：除法の等式と乗法の可換性より

```math
i = L\lfloor i/L\rfloor + (i \bmod L) = \lfloor i/L\rfloor \cdot L + (i \bmod L) = kL + q . \qquad \blacksquare
```

<a id="t-copies_map_length"></a>
## 定理: 複製列の長さ (T.copies_map_length)

### 定理

以下、$`f : \mathbb{N} \to (\mathbb{N}\times\mathbb{N}) \to (\mathbb{N}\times\mathbb{N})`$、
$`B \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ に対し

```math
\mathrm{cp}(B, f, n) := \mathrm{map}(f_0, B) \mathbin{+\!\!+} \mathrm{map}(f_1, B)
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \mathrm{map}(f_{n-1}, B)
```

と書く。ここで $`f_k := f(k)`$ であり、$`\mathrm{map}(g, B)`$ は $`B`$ の各要素 $`x`$ を
$`g(x)`$ に置き換えた列である。$`n = 0`$ のとき $`\mathrm{cp}(B,f,0) = ()`$ である。
定義から直ちに

```math
\mathrm{cp}(B,f,n+1) = \mathrm{cp}(B,f,n) \mathbin{+\!\!+} \mathrm{map}(f_n, B)
```

が成り立つ。このとき

```math
\lvert \mathrm{cp}(B,f,n)\rvert = n\,\lvert B\rvert .
```

### 証明

$`n`$ に関する帰納法。帰納法の述語は

```math
\Phi(n) :\equiv \lvert \mathrm{cp}(B,f,n)\rvert = n\,\lvert B\rvert .
```

- **基底段** $`n = 0`$：$`\mathrm{cp}(B,f,0) = ()`$ であり
  $`\lvert ()\rvert = 0 = 0 \cdot \lvert B\rvert`$。

**帰納段** $`n \to n+1`$。帰納法の仮定は
$`\Phi(n)`$、すなわち $`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert`$ である。
上に述べた分解と、連結列の長さが長さの和であること、および
$`\lvert \mathrm{map}(f_n, B)\rvert = \lvert B\rvert`$ より

```math
\lvert \mathrm{cp}(B,f,n+1)\rvert = n\lvert B\rvert + \lvert B\rvert = (n+1)\lvert B\rvert
```

である。よって $`\Phi(n+1)`$。∎

<a id="t-copies_map_getD"></a>
## 定理: 複製列の成分 (T.copies_map_getD)

### 定理

$`k \lt n`$ かつ $`q \lt \lvert B\rvert`$ ならば

```math
\mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle = f_k\bigl(B\langle q\rangle\bigr).
```

### 証明

$`n`$ に関する帰納法。帰納法の述語は

```math
\Phi(n) :\equiv \forall k, q,\ \bigl(k \lt n \wedge q \lt \lvert B\rvert\bigr)
  \to \mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle = f_k\bigl(B\langle q\rangle\bigr).
```

- **基底段** $`n = 0`$：$`k \lt 0`$ をみたす自然数 $`k`$ は存在しないから前件が偽であり、
  $`\Phi(0)`$ が成り立つ。

**帰納段** $`n \to n+1`$。帰納法の仮定は $`\Phi(n)`$ である。
$`k \lt n+1`$、$`q \lt \lvert B\rvert`$ とし、[T.copies_map_length](#t-copies_map_length) の
分解 $`\mathrm{cp}(B,f,n+1) = \mathrm{cp}(B,f,n) \mathbin{+\!\!+} \mathrm{map}(f_n, B)`$ を使う。
[T.copies_map_length](#t-copies_map_length) より
$`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert`$ である。$`k`$ と $`n`$ の大小で場合分けする。

**(a) $`k \lt n`$ のとき。** $`q \lt \lvert B\rvert`$ より

```math
k\lvert B\rvert + q \lt k\lvert B\rvert + \lvert B\rvert = (k+1)\lvert B\rvert \le n\lvert B\rvert
```

である（最後の不等号は $`k + 1 \le n`$ による）。よって添字 $`k\lvert B\rvert + q`$ は
左側の $`\mathrm{cp}(B,f,n)`$ の範囲内にあり、[T.getD_append_left](#t-getD_append_left) より

```math
\mathrm{cp}(B,f,n+1)\bigl\langle k\lvert B\rvert + q\bigr\rangle
  = \mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle
```

である。これに帰納法の仮定 $`\Phi(n)`$ を適用して $`f_k(B\langle q\rangle)`$ を得る。

**(b) $`k = n`$ のとき。** 添字は $`n\lvert B\rvert + q`$ であり、
$`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert \le n\lvert B\rvert + q`$ であるから、
[T.getD_append_right](#t-getD_append_right) より

```math
\mathrm{cp}(B,f,n+1)\bigl\langle n\lvert B\rvert + q\bigr\rangle
  = \mathrm{map}(f_n, B)\bigl\langle (n\lvert B\rvert + q) - n\lvert B\rvert\bigr\rangle
  = \mathrm{map}(f_n, B)\langle q\rangle
```

である。$`q \lt \lvert B\rvert = \lvert \mathrm{map}(f_n,B)\rvert`$ であるから添字は範囲内であり、
$`\mathrm{map}(f_n,B)`$ の第 $`q`$ 要素は $`B`$ の第 $`q`$ 要素に $`f_n`$ を適用したもの、
すなわち $`f_n(B\langle q\rangle)`$ である。∎

<a id="d-copyExp"></a>
## 定義: 複製展開 (D.copyExp)

$`L \in \mathrm{PairSeq}`$、$`e \in \mathbb{N}`$ に対し、$`L`$ の各対の第 1 成分に
$`e`$ を足した列を $`L^{+e}`$ と書く。$`G, B \in \mathrm{PairSeq}`$、$`d_0, n \in \mathbb{N}`$ に対し

```math
\mathrm{copyExp}(G,B,d_0,n) := G \mathbin{+\!\!+} \mathrm{cp}(B, f, n),
\qquad f_k(p) := (p_1 + k\,d_0,\ p_2)
```

と定める。すなわち

```math
\mathrm{copyExp}(G,B,d_0,n)
  = G \mathbin{+\!\!+} B^{+0\cdot d_0} \mathbin{+\!\!+} B^{+1\cdot d_0}
    \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}
```

である。$`G`$ を**前置部**、
$`B^{+0\cdot d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}`$ を**複製部**と呼ぶ。

<a id="t-copyExp_length"></a>
## 定理: 複製展開の長さ (T.copyExp_length)

### 定理

```math
\lvert \mathrm{copyExp}(G,B,d_0,n)\rvert = \lvert G\rvert + n\,\lvert B\rvert .
```

### 証明

$`\mathrm{copyExp}`$ の定義（D.copyExp）より
$`\mathrm{copyExp}(G,B,d_0,n) = G \mathbin{+\!\!+} \mathrm{cp}(B,f,n)`$ であり、
連結列の長さは長さの和であるから、その長さは
$`\lvert G\rvert + \lvert \mathrm{cp}(B,f,n)\rvert`$ である。
[T.copies_map_length](#t-copies_map_length) より
$`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert`$。∎

<a id="t-copyExp_getD_pre"></a>
## 定理: 複製展開の前置部の成分 (T.copyExp_getD_pre)

### 定理

$`i \lt \lvert G\rvert`$ ならば
$`\mathrm{copyExp}(G,B,d_0,n)\langle i\rangle = G\langle i\rangle`$。

### 証明

$`\mathrm{copyExp}`$ の定義（D.copyExp）より左辺は
$`(G \mathbin{+\!\!+} \mathrm{cp}(B,f,n))\langle i\rangle`$ であり、
[T.getD_append_left](#t-getD_append_left) を適用すればよい。∎

<a id="t-copyExp_getD_copy"></a>
## 定理: 複製展開の複製部の成分 (T.copyExp_getD_copy)

### 定理

$`k \lt n`$ かつ $`q \lt \lvert B\rvert`$ ならば

```math
\mathrm{copyExp}(G,B,d_0,n)\bigl\langle \lvert G\rvert + (k\lvert B\rvert + q)\bigr\rangle
  = \bigl(B_{0,q} + k\,d_0,\ B_{1,q}\bigr).
```

### 証明

$`\mathrm{copyExp}`$ の定義（D.copyExp）より左辺は
$`(G \mathbin{+\!\!+} \mathrm{cp}(B,f,n))\langle \lvert G\rvert + (k\lvert B\rvert + q)\rangle`$ である。
$`\lvert G\rvert \le \lvert G\rvert + (k\lvert B\rvert + q)`$ であるから
[T.getD_append_right](#t-getD_append_right) が使えて、これは

```math
\mathrm{cp}(B,f,n)\bigl\langle \bigl(\lvert G\rvert + (k\lvert B\rvert + q)\bigr) - \lvert G\rvert\bigr\rangle
  = \mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle
```

に等しい。[T.copies_map_getD](#t-copies_map_getD) より、これは
$`f_k(B\langle q\rangle)`$、すなわち $`\mathrm{copyExp}`$ の定義（D.copyExp）の
$`f_k(p) = (p_1 + k d_0, p_2)`$ を $`p := B\langle q\rangle`$ に適用した
$`(B_{0,q} + k d_0,\ B_{1,q})`$ に等しい。∎

<a id="t-hostM_getD_pre"></a>
## 定理: 連結列 $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ の前置部の成分 (T.hostM_getD_pre)

### 定理

$`G, B \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ とする。
$`i \lt \lvert G\rvert`$ ならば

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)\langle i\rangle = G\langle i\rangle .
```

### 証明

$`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell) = (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$ であり、
$`i \lt \lvert G\rvert \le \lvert G\rvert + \lvert B\rvert = \lvert G \mathbin{+\!\!+} B\rvert`$ であるから、
[T.getD_append_left](#t-getD_append_left) より左辺は
$`(G \mathbin{+\!\!+} B)\langle i\rangle`$ に等しい。
ふたたび $`i \lt \lvert G\rvert`$ に [T.getD_append_left](#t-getD_append_left) を適用して
$`G\langle i\rangle`$ を得る。∎

<a id="t-hostM_getD_blk"></a>
## 定理: 連結列 $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ のブロック部の成分 (T.hostM_getD_blk)

### 定理

$`q \lt \lvert B\rvert`$ ならば

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)\langle \lvert G\rvert + q\rangle = B\langle q\rangle .
```

### 証明

$`q \lt \lvert B\rvert`$ より
$`\lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert = \lvert G \mathbin{+\!\!+} B\rvert`$ であるから、
[T.getD_append_left](#t-getD_append_left) より左辺は
$`(G \mathbin{+\!\!+} B)\langle \lvert G\rvert + q\rangle`$ に等しい。
$`\lvert G\rvert \le \lvert G\rvert + q`$ であるから
[T.getD_append_right](#t-getD_append_right) が使えて、これは
$`B\langle (\lvert G\rvert + q) - \lvert G\rvert\rangle = B\langle q\rangle`$ に等しい。∎

<a id="t-hostM_length"></a>
## 定理: 連結列 $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ の長さ (T.hostM_length)

### 定理

```math
\bigl\lvert G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr\rvert = \lvert G\rvert + \lvert B\rvert + 1 .
```

### 証明

連結列の長さは長さの和であり、$`\lvert (\ell)\rvert = 1`$ であるから

```math
\bigl\lvert (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)\bigr\rvert
  = \bigl(\lvert G\rvert + \lvert B\rvert\bigr) + 1 . \qquad \blacksquare
```

<a id="t-r1ok_copyExp"></a>
## 定理: 複製展開における行 1 の規律 (T.r1ok_copyExp)

### 定理

$`G, B \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、$`n, d_0 \in \mathbb{N}`$ とし、
$`E := \mathrm{copyExp}(G,B,d_0,n)`$ とおく。次の 2 つを仮定する。

```math
\text{(hr)}\quad \mathrm{r1ok}\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr),
```

```math
\begin{aligned}
\text{(hmin)}\quad &\forall k, q,\
  \Bigl(0 \lt k \wedge k \lt n \wedge q \lt \lvert B\rvert
  \wedge \bigl(\forall r \lt q,\ B_{0,q} \le B_{0,r}\bigr)
  \wedge 0 \lt B_{0,q} + k d_0\Bigr) \to \cr
  &\quad \exists p,\
  \Bigl(p \lt \lvert G\rvert + (k\lvert B\rvert + q)
  \ \wedge\ E_{0,p} + 1 = B_{0,q} + k d_0 \cr
  &\qquad \wedge\ \bigl(\forall l,\ p \lt l \wedge l \lt \lvert G\rvert + (k\lvert B\rvert + q)
     \to B_{0,q} + k d_0 \le E_{0,l}\bigr) \cr
  &\qquad \wedge\ B_{1,q} \le E_{1,p} + 1\Bigr).
\end{aligned}
```

このとき $`\mathrm{r1ok}(E)`$ が成り立つ。

### 証明

$`H := G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ とおく。
$`j \lt \lvert E\rvert`$ かつ $`0 \lt E_{0,j}`$ とする。
[T.copyExp_length](#t-copyExp_length) より
$`j \lt \lvert G\rvert + n\lvert B\rvert`$ である。$`j`$ の位置で場合分けする。

**(A) $`j \lt \lvert G\rvert + \lvert B\rvert`$ のとき。**
まず次を示す。

```math
(\ast)\qquad \forall i \le j,\ E\langle i\rangle = H\langle i\rangle .
```

$`i \le j`$ を取る。

**(A-1) $`i \lt \lvert G\rvert`$ のとき。**
[T.copyExp_getD_pre](#t-copyExp_getD_pre) より $`E\langle i\rangle = G\langle i\rangle`$、
[T.hostM_getD_pre](#t-hostM_getD_pre) より $`H\langle i\rangle = G\langle i\rangle`$ であり、
両辺は一致する。

**(A-2) $`\lvert G\rvert \le i`$ のとき。**
$`i \le j \lt \lvert G\rvert + \lvert B\rvert`$ より $`i - \lvert G\rvert \lt \lvert B\rvert`$ である。
また $`0 \lt n`$ である。実際、$`n = 0`$ とすると
$`j \lt \lvert G\rvert + 0 \cdot \lvert B\rvert = \lvert G\rvert`$ となるが、
$`\lvert G\rvert \le i \le j`$ に反する。
$`i = \lvert G\rvert + (0 \cdot \lvert B\rvert + (i - \lvert G\rvert))`$ であるから、
[T.copyExp_getD_copy](#t-copyExp_getD_copy) を $`k := 0`$、$`q := i - \lvert G\rvert`$ に適用して

```math
E\langle i\rangle
  = \bigl(B_{0,\,i - \lvert G\rvert} + 0 \cdot d_0,\ B_{1,\,i - \lvert G\rvert}\bigr)
  = B\langle i - \lvert G\rvert\rangle
```

を得る。他方 $`i = \lvert G\rvert + (i - \lvert G\rvert)`$ であるから
[T.hostM_getD_blk](#t-hostM_getD_blk) より
$`H\langle i\rangle = B\langle i - \lvert G\rvert\rangle`$ である。よって両辺は一致する。

これで $`(\ast)`$ が示された。[T.hostM_length](#t-hostM_length) より
$`\lvert H\rvert = \lvert G\rvert + \lvert B\rvert + 1`$ であり、
$`j \lt \lvert G\rvert + \lvert B\rvert \lt \lvert H\rvert`$ である。
$`(\ast)`$ を $`i := j`$ に用いると $`0 \lt H_{0,j}`$ である。
仮定 (hr) を $`j`$ に適用して、$`H`$ における第 $`j`$ 列の証人 $`p`$ を得る。
すなわち $`p \lt j`$、$`H_{0,p} + 1 = H_{0,j}`$、
$`\forall l\ (p \lt l \wedge l \lt j \to H_{0,j} \le H_{0,l})`$、
$`H_{1,j} \le H_{1,p} + 1`$ である。
この $`p`$ が $`E`$ における第 $`j`$ 列の証人でもあることを示す。

条件 (1) $`p \lt j`$ はそのままである。
$`p \lt j`$ より $`p \le j`$ であるから $`(\ast)`$ が $`p`$ に使え、
$`E\langle p\rangle = H\langle p\rangle`$、$`E\langle j\rangle = H\langle j\rangle`$ である。
よって条件 (2) $`E_{0,p} + 1 = E_{0,j}`$ と条件 (4) $`E_{1,j} \le E_{1,p} + 1`$ は
$`H`$ についての等式・不等式そのものになる。
条件 (3) については、$`p \lt l`$ かつ $`l \lt j`$ をみたす $`l`$ に対し $`l \le j`$ であるから
$`(\ast)`$ より $`E\langle l\rangle = H\langle l\rangle`$ であり、
$`H`$ についての条件がそのまま $`E_{0,j} \le E_{0,l}`$ を与える。

**(B) $`\lvert G\rvert + \lvert B\rvert \le j`$ のとき。**
まず $`0 \lt \lvert B\rvert`$ である。実際 $`\lvert B\rvert = 0`$ とすると
$`j \lt \lvert G\rvert + n \cdot 0 = \lvert G\rvert`$ となるが、
$`\lvert G\rvert \le \lvert G\rvert + \lvert B\rvert \le j`$ に反する。
$`j \lt \lvert G\rvert + n\lvert B\rvert`$ より $`j - \lvert G\rvert \lt n\lvert B\rvert`$ であるから、
[T.index_decomp](#t-index_decomp) より $`k \lt n`$、$`q \lt \lvert B\rvert`$、
$`j - \lvert G\rvert = k\lvert B\rvert + q`$ をみたす $`k, q`$ が存在する。
$`\lvert G\rvert \le j`$ であるから $`j = \lvert G\rvert + (k\lvert B\rvert + q)`$ である。
さらに $`0 \lt k`$ である。実際 $`k = 0`$ とすると
$`j = \lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert`$ となり、
場合 (B) の仮定に反する。
[T.copyExp_getD_copy](#t-copyExp_getD_copy) より

```math
E\langle j\rangle = \bigl(B_{0,q} + k d_0,\ B_{1,q}\bigr),
```

とくに $`0 \lt B_{0,q} + k d_0`$ である。$`q`$ より前の位置の行 $`0`$ の値との大小で場合分けする。

**(B-1) $`\forall r \lt q,\ B_{0,q} \le B_{0,r}`$ のとき。**
仮定 (hmin) を $`k, q`$ に適用すればよい。得られる $`p`$ が条件 (1)〜(4) を
みたすことは (hmin) の結論そのものである（$`E_{0,j} = B_{0,q} + k d_0`$、
$`E_{1,j} = B_{1,q}`$ による）。

**(B-2) ある $`r \lt q`$ が $`B_{0,r} \lt B_{0,q}`$ をみたすとき。**
$`0 \le B_{0,r} \lt B_{0,q}`$ より $`0 \lt B_{0,q}`$ である。
[T.hostM_length](#t-hostM_length) より
$`\lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$ であり、
[T.hostM_getD_blk](#t-hostM_getD_blk) より $`H\langle \lvert G\rvert + q\rangle = B\langle q\rangle`$、
とくに $`0 \lt H_{0,\lvert G\rvert + q}`$ である。
仮定 (hr) を添字 $`\lvert G\rvert + q`$ に適用して、$`H`$ における
第 $`\lvert G\rvert + q`$ 列の証人 $`p`$ を得る。すなわち

```math
\begin{aligned}
&p \lt \lvert G\rvert + q, \cr
&H_{0,p} + 1 = H_{0,\lvert G\rvert + q} = B_{0,q}, \cr
&\forall l\ \bigl(p \lt l \wedge l \lt \lvert G\rvert + q \to B_{0,q} \le H_{0,l}\bigr), \cr
&B_{1,q} = H_{1,\lvert G\rvert + q} \le H_{1,p} + 1 .
\end{aligned}
```

ここで $`\lvert G\rvert + r \le p`$ である。実際 $`p \lt \lvert G\rvert + r`$ とすると、
$`r \lt q`$ より $`\lvert G\rvert + r \lt \lvert G\rvert + q`$ であるから第 3 の条件を
$`l := \lvert G\rvert + r`$ に適用でき、[T.hostM_getD_blk](#t-hostM_getD_blk) より
$`B_{0,q} \le H_{0,\lvert G\rvert + r} = B_{0,r}`$ となって $`B_{0,r} \lt B_{0,q}`$ に矛盾する。

したがって $`r' := p - \lvert G\rvert`$ とおけば $`p = \lvert G\rvert + r'`$ であり、
$`p \lt \lvert G\rvert + q`$ より $`r' \lt q`$、よって $`r' \lt \lvert B\rvert`$ である。
[T.hostM_getD_blk](#t-hostM_getD_blk) より $`H\langle p\rangle = B\langle r'\rangle`$ であるから、
上の条件は

```math
B_{0,r'} + 1 = B_{0,q}, \qquad B_{1,q} \le B_{1,r'} + 1
```

と書き直せる。$`E`$ における第 $`j`$ 列の証人として
$`p^{*} := \lvert G\rvert + (k\lvert B\rvert + r')`$ を取る。
$`\mathrm{r1ok}`$ の定義（D.r1ok）の 4 条件を確かめる。

**(1)** $`r' \lt q`$ より
$`p^{*} = \lvert G\rvert + (k\lvert B\rvert + r') \lt \lvert G\rvert + (k\lvert B\rvert + q) = j`$。

**(2)** [T.copyExp_getD_copy](#t-copyExp_getD_copy) を $`k`$, $`r'`$ に適用して
$`E_{0,p^{*}} = B_{0,r'} + k d_0`$ である。よって

```math
E_{0,p^{*}} + 1 = B_{0,r'} + k d_0 + 1 = (B_{0,r'} + 1) + k d_0 = B_{0,q} + k d_0 = E_{0,j} .
```

**(3)** $`p^{*} \lt l`$ かつ $`l \lt j`$ をみたす $`l`$ を取る。
$`\lvert G\rvert + k\lvert B\rvert \le p^{*} \lt l \lt \lvert G\rvert + (k\lvert B\rvert + q)`$ であるから、
$`rr := l - \lvert G\rvert - k\lvert B\rvert`$ とおくと
$`l = \lvert G\rvert + (k\lvert B\rvert + rr)`$、$`r' \lt rr`$、$`rr \lt q`$ である。
とくに $`rr \lt \lvert B\rvert`$ であるから
[T.copyExp_getD_copy](#t-copyExp_getD_copy) より $`E_{0,l} = B_{0,rr} + k d_0`$ である。
他方 $`p = \lvert G\rvert + r' \lt \lvert G\rvert + rr \lt \lvert G\rvert + q`$ であるから、
$`H`$ についての第 3 の条件を $`l := \lvert G\rvert + rr`$ に適用し、
[T.hostM_getD_blk](#t-hostM_getD_blk) より $`B_{0,q} \le B_{0,rr}`$ を得る。よって

```math
E_{0,j} = B_{0,q} + k d_0 \le B_{0,rr} + k d_0 = E_{0,l} .
```

**(4)** [T.copyExp_getD_copy](#t-copyExp_getD_copy) より
$`E_{1,p^{*}} = B_{1,r'}`$ であり、$`E_{1,j} = B_{1,q} \le B_{1,r'} + 1 = E_{1,p^{*}} + 1`$。∎

<a id="t-getD_mem"></a>
## 定理: 範囲内の成分は要素である (T.getD_mem)

### 定理

$`L`$ を対の列、$`i \lt \lvert L\rvert`$ とすると $`L\langle i\rangle \in L`$。

### 証明

$`i \lt \lvert L\rvert`$ であるから $`L\langle i\rangle`$ の定義（D.entry）の第 1 の場合が選ばれ、
$`L\langle i\rangle`$ は $`L`$ の第 $`i`$ 要素である。列の第 $`i`$ 要素は
（$`i`$ が範囲内である限り）その列の要素である。∎

<a id="t-dominated_PM_zero"></a>
## 定理: 支配されたブロックで行 0 が最小になる位置は先頭に限る (T.dominated_PM_zero)

### 定理

$`v_0, w_0 \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$、$`q \in \mathbb{N}`$ とし、
$`B := (v_0,w_0) :: R`$ とおく。次の 3 つを仮定する。

```math
\begin{aligned}
&\text{(hdom)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hq)}\quad q \lt \lvert B\rvert, \cr
&\text{(hPM)}\quad \forall r \lt q,\ B_{0,q} \le B_{0,r} .
\end{aligned}
```

このとき $`q = 0`$。

### 証明

$`q \ne 0`$ と仮定して矛盾を導く。$`q \ne 0`$ より $`q = q' + 1`$ と書ける。
$`\lvert B\rvert = \lvert R\rvert + 1`$ であるから (hq) より $`q' \lt \lvert R\rvert`$ である。
[T.getD_mem](#t-getD_mem) より $`R\langle q'\rangle \in R`$ であり、(hdom) より

```math
v_0 \lt R_{0,q'} .
```

他方 (hPM) を $`r := 0`$ に適用すると（$`0 \lt q`$ である）$`B_{0,q} \le B_{0,0}`$ を得る。
$`B = (v_0,w_0) :: R`$ であるから $`B\langle 0\rangle = (v_0,w_0)`$、すなわち $`B_{0,0} = v_0`$ であり、
また $`B\langle q' + 1\rangle = R\langle q'\rangle`$ であるから $`B_{0,q} = R_{0,q'}`$ である。
よって $`R_{0,q'} \le v_0`$ となり、$`v_0 \lt R_{0,q'}`$ に矛盾する。∎

<a id="t-r1ok_min_d0zero"></a>
## 定理: 複製部の証人（$`d_0 = 0`$ の場合） (T.r1ok_min_d0zero)

### 定理

$`G, R \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、$`n, v_0, w_0 \in \mathbb{N}`$、
$`B := (v_0,w_0) :: R`$、$`E := \mathrm{copyExp}(G,B,0,n)`$ とおく。次を仮定する。

```math
\begin{aligned}
&\text{(hdom)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hr)}\quad \mathrm{r1ok}\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr), \cr
&\text{(hk1)}\quad 0 \lt k, \qquad
 \text{(hk)}\quad k \lt n, \qquad
 \text{(hq)}\quad q \lt \lvert B\rvert, \cr
&\text{(hPM)}\quad \forall r \lt q,\ B_{0,q} \le B_{0,r}, \cr
&\text{(hpos)}\quad 0 \lt B_{0,q} + k \cdot 0 .
\end{aligned}
```

このとき次をみたす $`p`$ が存在する。

```math
\begin{aligned}
&p \lt \lvert G\rvert + (k\lvert B\rvert + q), \cr
&E_{0,p} + 1 = B_{0,q} + k \cdot 0, \cr
&\forall l,\ \bigl(p \lt l \wedge l \lt \lvert G\rvert + (k\lvert B\rvert + q)\bigr)
   \to B_{0,q} + k \cdot 0 \le E_{0,l}, \cr
&B_{1,q} \le E_{1,p} + 1 .
\end{aligned}
```

### 証明

$`H := G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ とおく。
[T.dominated_PM_zero](#t-dominated_PM_zero) を (hdom), (hq), (hPM) に適用して $`q = 0`$ を得る。
以下 $`q = 0`$ とする。$`B\langle 0\rangle = (v_0,w_0)`$ であるから $`B_{0,0} = v_0`$、$`B_{1,0} = w_0`$ であり、
$`k \cdot 0 = 0`$ であるから (hpos) は $`0 \lt v_0`$ を与える。

$`0 \lt \lvert B\rvert`$ であるから [T.hostM_getD_blk](#t-hostM_getD_blk) を $`q := 0`$ に適用して
$`H\langle \lvert G\rvert\rangle = B\langle 0\rangle = (v_0,w_0)`$ を得る。
[T.hostM_length](#t-hostM_length) より
$`\lvert G\rvert \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$ であり、
$`H_{0,\lvert G\rvert} = v_0 \gt 0`$ である。
仮定 (hr) を添字 $`\lvert G\rvert`$ に適用して、$`H`$ における第 $`\lvert G\rvert`$ 列の証人 $`p`$ を得る。
すなわち

```math
\begin{aligned}
&p \lt \lvert G\rvert, \cr
&H_{0,p} + 1 = v_0, \cr
&\forall l\ \bigl(p \lt l \wedge l \lt \lvert G\rvert \to v_0 \le H_{0,l}\bigr), \cr
&w_0 \le H_{1,p} + 1 .
\end{aligned}
```

$`p \lt \lvert G\rvert`$ であるから [T.hostM_getD_pre](#t-hostM_getD_pre) より
$`H\langle p\rangle = G\langle p\rangle`$ であり、上の 2 番目と 4 番目は

```math
G_{0,p} + 1 = v_0, \qquad w_0 \le G_{1,p} + 1
```

となる。この $`p`$ が求めるものであることを示す。
[T.copyExp_getD_pre](#t-copyExp_getD_pre) より $`E\langle p\rangle = G\langle p\rangle`$ である。

**第 1 の条件。** $`p \lt \lvert G\rvert \le \lvert G\rvert + (k\lvert B\rvert + 0)`$。

**第 2 の条件。** $`E_{0,p} + 1 = G_{0,p} + 1 = v_0 = v_0 + k \cdot 0 = B_{0,0} + k \cdot 0`$。

**第 3 の条件。** $`p \lt l`$ かつ $`l \lt \lvert G\rvert + (k\lvert B\rvert + 0)`$ をみたす $`l`$ を取る。
示すべきは $`v_0 + k \cdot 0 \le E_{0,l}`$、すなわち $`v_0 \le E_{0,l}`$ である。$`l`$ の位置で場合分けする。

**(a) $`l \lt \lvert G\rvert`$ のとき。**
[T.copyExp_getD_pre](#t-copyExp_getD_pre) より $`E\langle l\rangle = G\langle l\rangle`$ であり、
上の 3 番目の条件と [T.hostM_getD_pre](#t-hostM_getD_pre) より
$`v_0 \le H_{0,l} = G_{0,l} = E_{0,l}`$。

**(b) $`\lvert G\rvert \le l`$ のとき。**
(hk) より $`k \le n`$ であるから $`k\lvert B\rvert \le n\lvert B\rvert`$ であり、
$`l \lt \lvert G\rvert + k\lvert B\rvert`$ から $`l - \lvert G\rvert \lt n\lvert B\rvert`$ である。
$`0 \lt \lvert B\rvert`$ であるから [T.index_decomp](#t-index_decomp) より
$`k' \lt n`$、$`r \lt \lvert B\rvert`$、$`l - \lvert G\rvert = k'\lvert B\rvert + r`$ をみたす $`k', r`$ が
存在し、$`l = \lvert G\rvert + (k'\lvert B\rvert + r)`$ である。
[T.copyExp_getD_copy](#t-copyExp_getD_copy) より
$`E_{0,l} = B_{0,r} + k' \cdot 0 = B_{0,r}`$ である。
$`v_0 \le B_{0,r}`$ を $`r`$ で場合分けして示す。

- $`r = 0`$ のとき。$`B_{0,0} = v_0`$ であるから $`v_0 \le v_0`$。
- $`r = r' + 1`$ のとき。$`B\langle r' + 1\rangle = R\langle r'\rangle`$ であり、
  $`r \lt \lvert B\rvert = \lvert R\rvert + 1`$ より $`r' \lt \lvert R\rvert`$ であるから
  [T.getD_mem](#t-getD_mem) より $`R\langle r'\rangle \in R`$、
  (hdom) より $`v_0 \lt R_{0,r'} = B_{0,r}`$。

**第 4 の条件。** $`B_{1,0} = w_0 \le G_{1,p} + 1 = E_{1,p} + 1`$。∎

<a id="t-r1ok_min_d0pos"></a>
## 定理: 複製部の証人（$`0 \lt d_0`$ の場合） (T.r1ok_min_d0pos)

### 定理

$`G, R \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、$`n, v_0, w_0, d_0 \in \mathbb{N}`$、
$`B := (v_0,w_0) :: R`$、$`E := \mathrm{copyExp}(G,B,d_0,n)`$ とおく。次を仮定する。

```math
\begin{aligned}
&\text{(hdom)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hd0)}\quad 0 \lt d_0, \cr
&\text{(hlp)}\quad \ell_1 = v_0 + d_0, \cr
&\text{(hstep)}\quad \forall r,\ r + 1 \lt \lvert B\rvert \to B_{0,r+1} \le B_{0,r} + 1, \cr
&\text{(hlpstep)}\quad \ell_1 \le B_{0,\lvert B\rvert - 1} + 1, \cr
&\text{(hclimb)}\quad \forall r' \lt \lvert B\rvert,\
   \Bigl(B_{0,r'} = v_0 + d_0 - 1
   \wedge \bigl(\forall rr,\ r' \lt rr \wedge rr \lt \lvert B\rvert \to v_0 + d_0 \le B_{0,rr}\bigr)\Bigr)
   \to w_0 \le B_{1,r'} + 1, \cr
&\text{(hk1)}\quad 0 \lt k, \qquad
 \text{(hk)}\quad k \lt n, \qquad
 \text{(hq)}\quad q \lt \lvert B\rvert, \cr
&\text{(hPM)}\quad \forall r \lt q,\ B_{0,q} \le B_{0,r}, \cr
&\text{(hpos)}\quad 0 \lt B_{0,q} + k d_0 .
\end{aligned}
```

このとき次をみたす $`p`$ が存在する。

```math
\begin{aligned}
&p \lt \lvert G\rvert + (k\lvert B\rvert + q), \cr
&E_{0,p} + 1 = B_{0,q} + k d_0, \cr
&\forall l,\ \bigl(p \lt l \wedge l \lt \lvert G\rvert + (k\lvert B\rvert + q)\bigr)
   \to B_{0,q} + k d_0 \le E_{0,l}, \cr
&B_{1,q} \le E_{1,p} + 1 .
\end{aligned}
```

### 証明

[T.dominated_PM_zero](#t-dominated_PM_zero) を (hdom), (hq), (hPM) に適用して $`q = 0`$ を得る。
以下 $`q = 0`$ とする。$`B = (v_0,w_0) :: R`$ であるから
$`0 \lt \lvert B\rvert`$ であり $`B\langle 0\rangle = (v_0,w_0)`$、すなわち
$`B_{0,0} = v_0`$、$`B_{1,0} = w_0`$ である。

**証人の候補。** 述語 $`P`$ を

```math
P(r) :\equiv B_{0,r} \le v_0 + d_0 - 1
```

で定める。(hd0) より $`d_0 \ge 1`$ であるから $`v_0 \le v_0 + d_0 - 1`$ であり、
$`B_{0,0} = v_0`$ であるから $`P(0)`$ が成り立つ。
集合 $`\{\, r \le \lvert B\rvert - 1 \mid P(r)\,\}`$ は $`0`$ を含むので空でなく、
$`\lvert B\rvert - 1`$ で上に有界であるから最大元をもつ。それを $`r'`$ とおく。すなわち

```math
P(r'), \qquad r' \le \lvert B\rvert - 1, \qquad
\forall rr,\ \bigl(r' \lt rr \wedge rr \le \lvert B\rvert - 1\bigr) \to \neg P(rr) .
```

$`0 \lt \lvert B\rvert`$ より $`r' \lt \lvert B\rvert`$ である。
また $`0 \lt \lvert B\rvert`$ より $`rr \lt \lvert B\rvert`$ と $`rr \le \lvert B\rvert - 1`$ は同値である。
$`\neg P(rr)`$ は $`v_0 + d_0 - 1 \lt B_{0,rr}`$ のことであり、$`d_0 \ge 1`$ より
$`(v_0 + d_0 - 1) + 1 = v_0 + d_0`$ であるから、これは $`v_0 + d_0 \le B_{0,rr}`$ と同値である。したがって

```math
(\dagger)\qquad \forall rr,\ \bigl(r' \lt rr \wedge rr \lt \lvert B\rvert\bigr)
  \to v_0 + d_0 \le B_{0,rr} .
```

**証人における行 0 の値。** $`B_{0,r'} = v_0 + d_0 - 1`$ を示す。
$`P(r')`$ より $`B_{0,r'} \le v_0 + d_0 - 1`$ である。逆向きを $`r'`$ と $`\lvert B\rvert - 1`$ の
大小で場合分けして示す。

**(a) $`r' \lt \lvert B\rvert - 1`$ のとき。**
$`r' \lt r' + 1 \le \lvert B\rvert - 1`$ であるから $`\neg P(r'+1)`$、すなわち
$`v_0 + d_0 - 1 \lt B_{0,r'+1}`$ である。また $`r' + 1 \lt \lvert B\rvert`$ であるから
(hstep) より $`B_{0,r'+1} \le B_{0,r'} + 1`$ である。よって

```math
v_0 + d_0 - 1 \lt B_{0,r'} + 1,
```

すなわち $`v_0 + d_0 - 1 \le B_{0,r'}`$。

**(b) $`r' = \lvert B\rvert - 1`$ のとき。**
(hlp) と (hlpstep) より $`v_0 + d_0 = \ell_1 \le B_{0,\lvert B\rvert - 1} + 1 = B_{0,r'} + 1`$ であり、
$`v_0 + d_0 - 1 \le B_{0,r'}`$。

いずれの場合も $`v_0 + d_0 - 1 \le B_{0,r'}`$ であり、上界と合わせて

```math
(\ddagger)\qquad B_{0,r'} = v_0 + d_0 - 1 .
```

**乗法の書き換え。** (hk1) より $`k \ge 1`$ であるから $`k = (k-1) + 1`$ と書け、

```math
k\lvert B\rvert = (k-1)\lvert B\rvert + \lvert B\rvert, \qquad
k d_0 = (k-1) d_0 + d_0
```

である。また (hk) より $`k - 1 \lt n`$ である。

**証人。** $`p^{*} := \lvert G\rvert + \bigl((k-1)\lvert B\rvert + r'\bigr)`$ を取る。
$`k - 1 \lt n`$ と $`r' \lt \lvert B\rvert`$ により
[T.copyExp_getD_copy](#t-copyExp_getD_copy) が使えて

```math
E\langle p^{*}\rangle = \bigl(B_{0,r'} + (k-1)d_0,\ B_{1,r'}\bigr)
```

である。4 つの条件を確かめる。

**第 1 の条件。** $`r' \lt \lvert B\rvert`$ より
$`(k-1)\lvert B\rvert + r' \lt (k-1)\lvert B\rvert + \lvert B\rvert = k\lvert B\rvert`$ であるから
$`p^{*} \lt \lvert G\rvert + (k\lvert B\rvert + 0)`$。

**第 2 の条件。** $`(\ddagger)`$ と $`d_0 \ge 1`$ より

```math
E_{0,p^{*}} + 1 = (v_0 + d_0 - 1) + (k-1)d_0 + 1 = v_0 + d_0 + (k-1)d_0 = v_0 + k d_0
  = B_{0,0} + k d_0 .
```

**第 3 の条件。** $`p^{*} \lt l`$ かつ $`l \lt \lvert G\rvert + (k\lvert B\rvert + 0)`$ をみたす $`l`$ を取る。
$`\lvert G\rvert \le p^{*} \lt l`$ である。(hk) より $`k\lvert B\rvert \le n\lvert B\rvert`$ であるから
$`l - \lvert G\rvert \lt k\lvert B\rvert \le n\lvert B\rvert`$ であり、
[T.index_decomp](#t-index_decomp) より $`k'' \lt n`$、$`rr \lt \lvert B\rvert`$、
$`l - \lvert G\rvert = k''\lvert B\rvert + rr`$ をみたす $`k'', rr`$ が存在する。
$`k'' = k - 1`$ であることを三分律で示す。

- $`k'' \lt k - 1`$ とすると $`k'' + 1 \le k - 1`$ であるから
  $`(k''+1)\lvert B\rvert \le (k-1)\lvert B\rvert`$、すなわち
  $`k''\lvert B\rvert + \lvert B\rvert \le (k-1)\lvert B\rvert`$ である。
  $`rr \lt \lvert B\rvert`$ より
  $`l - \lvert G\rvert = k''\lvert B\rvert + rr \lt (k-1)\lvert B\rvert \le (k-1)\lvert B\rvert + r'`$
  となり、$`p^{*} \lt l`$ に矛盾する。
- $`k - 1 \lt k''`$ とすると $`k \le k''`$ であるから $`k\lvert B\rvert \le k''\lvert B\rvert`$ であり、
  $`l - \lvert G\rvert = k''\lvert B\rvert + rr \ge k\lvert B\rvert`$ となって
  $`l - \lvert G\rvert \lt k\lvert B\rvert`$ に矛盾する。

よって $`k'' = k - 1`$ である。すると $`p^{*} \lt l`$ は
$`(k-1)\lvert B\rvert + r' \lt (k-1)\lvert B\rvert + rr`$、すなわち $`r' \lt rr`$ を与える。
[T.copyExp_getD_copy](#t-copyExp_getD_copy) より
$`E_{0,l} = B_{0,rr} + (k-1)d_0`$ であり、$`(\dagger)`$ より $`v_0 + d_0 \le B_{0,rr}`$ であるから

```math
B_{0,0} + k d_0 = v_0 + k d_0 = (v_0 + d_0) + (k-1)d_0 \le B_{0,rr} + (k-1)d_0 = E_{0,l} .
```

**第 4 の条件。** $`E_{1,p^{*}} = B_{1,r'}`$ であるから、示すべきは
$`B_{1,0} = w_0 \le B_{1,r'} + 1`$ である。これは (hclimb) を $`r'`$ に適用したものであり、
その前提は $`r' \lt \lvert B\rvert`$、$`(\ddagger)`$、$`(\dagger)`$ で与えられている。∎

<a id="t-hostM_getD_lp"></a>
## 定理: 連結列 $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ の末尾の成分 (T.hostM_getD_lp)

### 定理

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)
  \bigl\langle \lvert G\rvert + \lvert B\rvert\bigr\rangle = \ell .
```

### 証明

$`\lvert G \mathbin{+\!\!+} B\rvert = \lvert G\rvert + \lvert B\rvert`$ であるから
$`\lvert G \mathbin{+\!\!+} B\rvert \le \lvert G\rvert + \lvert B\rvert`$ であり、
[T.getD_append_right](#t-getD_append_right) を $`G := G \mathbin{+\!\!+} B`$、$`X := (\ell)`$ に適用して

```math
\bigl((G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)\bigr)\bigl\langle \lvert G\rvert + \lvert B\rvert\bigr\rangle
  = (\ell)\bigl\langle (\lvert G\rvert + \lvert B\rvert) - (\lvert G\rvert + \lvert B\rvert)\bigr\rangle
  = (\ell)\langle 0\rangle
```

を得る。$`0 \lt 1 = \lvert (\ell)\rvert`$ であるから $`(\ell)\langle 0\rangle = \ell`$ である。∎

<a id="t-r1ok_Pred"></a>
## 定理: 行 1 の規律は前者に遺伝する (T.r1ok_Pred)

### 定理

$`\mathrm{r1ok}(M)`$ ならば $`\mathrm{r1ok}(\mathrm{Pred}\,M)`$。

### 証明

$`\mathrm{Pred}`$ の定義（D.Pred）の場合分けによる。

- $`\lvert M\rvert \le 1`$ のとき。$`\mathrm{Pred}\,M = M`$ であり、仮定そのものである。
- $`\lvert M\rvert \ge 2`$ のとき。$`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$ であり、
  [T.r1ok_dropLast](#t-r1ok_dropLast) を適用すればよい。∎

<a id="t-climb_bound"></a>
## 定理: ブロック先頭の行 1 の値の上界 (T.climb_bound)

### 定理

$`M, G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ とし、
$`B := (v_0,w_0) :: R`$ とおく。次を仮定する。

```math
\begin{aligned}
&\text{(hM)}\quad M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell), \cr
&\text{(hd0)}\quad 0 \lt d_0, \cr
&\text{(hlp1)}\quad \ell_1 = v_0 + d_0, \cr
&\text{(hwlt)}\quad w_0 \lt \ell_2, \cr
&\text{(hnl1)}\quad \lvert G\rvert \to^M_1 (\lvert M\rvert - 1), \cr
&\text{(hr')}\quad r' \lt \lvert B\rvert, \cr
&\text{(hlev)}\quad B_{0,r'} = v_0 + d_0 - 1, \cr
&\text{(hafter)}\quad \forall rr,\ \bigl(r' \lt rr \wedge rr \lt \lvert B\rvert\bigr)
   \to v_0 + d_0 \le B_{0,rr} .
\end{aligned}
```

このとき $`w_0 \le B_{1,r'} + 1`$。

### 証明

$`r'`$ が $`0`$ かどうかで場合分けする。

**(a) $`r' = 0`$ のとき。** $`B = (v_0,w_0) :: R`$ より $`B\langle 0\rangle = (v_0,w_0)`$、
すなわち $`B_{1,0} = w_0`$ である。よって示すべきは $`w_0 \le w_0 + 1`$ であり、これは成り立つ。

**(b) $`0 \lt r'`$ のとき。**
以下 (hM) により $`M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ と書く。
[T.hostM_length](#t-hostM_length) より
$`\lvert M\rvert = \lvert G\rvert + \lvert B\rvert + 1`$ であり、したがって

```math
\lvert M\rvert - 1 = \lvert G\rvert + \lvert B\rvert .
```

まず 2 つの成分を計算する。$`M_{0,j}`$ の定義（D.entry）と
[T.hostM_getD_blk](#t-hostM_getD_blk)（$`r' \lt \lvert B\rvert`$）より

```math
M_{0,\lvert G\rvert + r'} = B_{0,r'} = v_0 + d_0 - 1 ,
```

[T.hostM_getD_lp](#t-hostM_getD_lp) と (hlp1) より

```math
M_{0,\lvert G\rvert + \lvert B\rvert} = \ell_1 = v_0 + d_0 .
```

**行 0 の親子関係。** $`\lvert G\rvert + r' \to^M_0 \lvert G\rvert + \lvert B\rvert`$ を示す。
$`\to^M_0`$ の定義（D.nextrel0）の 5 条件を確かめる。

**(1)** $`r' \lt \lvert B\rvert`$ より
$`\lvert G\rvert + r' \lt \lvert G\rvert + \lvert B\rvert \lt \lvert M\rvert`$。

**(2)** $`\lvert G\rvert + \lvert B\rvert \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert M\rvert`$。

**(3)** $`r' \lt \lvert B\rvert`$ より $`\lvert G\rvert + r' \lt \lvert G\rvert + \lvert B\rvert`$。

**(4)** (hd0) より $`d_0 \ge 1`$ であるから
$`M_{0,\lvert G\rvert + r'} = v_0 + d_0 - 1 \lt v_0 + d_0 = M_{0,\lvert G\rvert + \lvert B\rvert}`$。

**(5)** $`\lvert G\rvert + r' \lt j`$ かつ $`j \lt \lvert G\rvert + \lvert B\rvert`$ をみたす $`j`$ を取る。
$`rr := j - \lvert G\rvert`$ とおくと $`j = \lvert G\rvert + rr`$、$`r' \lt rr`$、$`rr \lt \lvert B\rvert`$ である。
[T.hostM_getD_blk](#t-hostM_getD_blk) より $`M_{0,j} = B_{0,rr}`$ であり、
(hafter) より $`v_0 + d_0 \le B_{0,rr}`$、すなわち
$`M_{0,\lvert G\rvert + \lvert B\rvert} \le M_{0,j}`$。

**行 0 の祖先関係。** $`\le^M_0`$ の定義（D.le0）の 3 条件のうち (1), (2) は上の (1), (2) であり、
(3) は 1 歩の $`\to^M_0`$ からなる鎖として得られる。よって

```math
\lvert G\rvert + r' \le^M_0 \lvert G\rvert + \lvert B\rvert = \lvert M\rvert - 1 .
```

**最大性の適用。** (hnl1) すなわち $`\lvert G\rvert \to^M_1 (\lvert M\rvert - 1)`$ の
$`\to^M_1`$ の定義（D.nextrel1）の条件 (6) を $`j := \lvert G\rvert + r'`$ に適用する。
その前提は $`\lvert G\rvert \lt \lvert G\rvert + r'`$（$`0 \lt r'`$ による）と、
いま示した $`\lvert G\rvert + r' \le^M_0 \lvert M\rvert - 1`$ である。よって

```math
M_{1,\lvert M\rvert - 1} \le M_{1,\lvert G\rvert + r'} .
```

$`M_{1,j}`$ の定義（D.entry）と [T.hostM_getD_lp](#t-hostM_getD_lp) より
$`M_{1,\lvert M\rvert - 1} = M_{1,\lvert G\rvert + \lvert B\rvert} = \ell_2`$ であり、
[T.hostM_getD_blk](#t-hostM_getD_blk) より $`M_{1,\lvert G\rvert + r'} = B_{1,r'}`$ である。
したがって $`\ell_2 \le B_{1,r'}`$ であり、(hwlt) の $`w_0 \lt \ell_2`$ と合わせて

```math
w_0 \lt \ell_2 \le B_{1,r'} \le B_{1,r'} + 1 . \qquad \blacksquare
```

<a id="t-r1ok_oper"></a>
## 定理: 行 1 の規律は展開で保たれる (T.r1ok_oper)

### 定理

$`1 \le n`$、$`\mathrm{r1ok}(M)`$、$`\mathrm{steps1}(M)`$ ならば
$`\mathrm{r1ok}(M[n])`$。

### 証明

$`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$ とおく。
$`M[n]`$ の定義（D.oper）の 4 つの分岐で場合分けする。

**(a) $`j_1 = 0`$ のとき。**
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より $`M[n] = M`$ であり、
結論は仮定 $`\mathrm{r1ok}(M)`$ そのものである。

**(b) $`j_1 \ne 0`$ かつ $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。**
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) より
$`M[n] = \mathrm{Pred}\,M`$ であり、
[T.r1ok_Pred](#t-r1ok_Pred) を仮定 $`\mathrm{r1ok}(M)`$ に適用すればよい。

**(c) $`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) より
$`M[n] = \mathrm{Pred}\,M`$ であり、[T.r1ok_Pred](#t-r1ok_Pred) を適用すればよい。

**(d) $`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
$`j_1 = \lvert M\rvert - 1 \ne 0`$ より $`1 \lt \lvert M\rvert`$ である。
[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) を適用して、
$`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$ で
次をみたすものを得る。$`B := (v_0,w_0) :: R`$ とおく。

```math
\begin{aligned}
&\text{(1)}\ M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell), \cr
&\text{(2)}\ M[n] = G \mathbin{+\!\!+} B^{+0 d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}, \cr
&\text{(3)}\ \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(5)}\ \bigl(d_0 = 0 \wedge i_1 = 0\bigr) \ \vee\
   \bigl(0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 j_1\bigr).
\end{aligned}
```

（[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) の 6 つの主張のうち、
以下で用いる 4 つを同じ番号で挙げた。また $`\mathrm{copyExp}`$ の定義（D.copyExp）により
(2) の右辺は $`\mathrm{copyExp}(G,B,d_0,n)`$ である。）
(1) より $`\mathrm{r1ok}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$ と
$`\mathrm{steps1}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$ が仮定から従う。

**段差条件。** $`r + 1 \lt \lvert B\rvert`$ をみたす $`r`$ に対し
$`B_{0,r+1} \le B_{0,r} + 1`$ を示す。
[T.hostM_length](#t-hostM_length) より
$`\lvert G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\rvert = \lvert G\rvert + \lvert B\rvert + 1`$ であり、
$`r + 1 \lt \lvert B\rvert`$ より
$`(\lvert G\rvert + r) + 1 \lt \lvert G\rvert + \lvert B\rvert + 1`$ である。
[T.steps1_iff](Seqlex.md#t-steps1_iff) を
$`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ の添字 $`\lvert G\rvert + r`$ に適用して

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + (r+1)}
  \le \bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + r} + 1
```

を得る。$`r + 1 \lt \lvert B\rvert`$ と $`r \lt \lvert B\rvert`$ に
[T.hostM_getD_blk](#t-hostM_getD_blk) を適用すると、これは
$`B_{0,r+1} \le B_{0,r} + 1`$ である。

**末尾の段差条件。** $`\ell_1 \le B_{0,\lvert B\rvert - 1} + 1`$ を示す。
$`0 \lt \lvert B\rvert`$ であるから

```math
\bigl(\lvert G\rvert + (\lvert B\rvert - 1)\bigr) + 1 = \lvert G\rvert + \lvert B\rvert
  \lt \lvert G\rvert + \lvert B\rvert + 1
```

である。
[T.steps1_iff](Seqlex.md#t-steps1_iff) を添字 $`\lvert G\rvert + (\lvert B\rvert - 1)`$ に適用して

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + \lvert B\rvert}
  \le \bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + (\lvert B\rvert - 1)} + 1
```

を得る。左辺は [T.hostM_getD_lp](#t-hostM_getD_lp) より $`\ell_1`$、
右辺は [T.hostM_getD_blk](#t-hostM_getD_blk)（$`\lvert B\rvert - 1 \lt \lvert B\rvert`$）より
$`B_{0,\lvert B\rvert - 1} + 1`$ である。

**組み立て。** [T.r1ok_copyExp](#t-r1ok_copyExp) を
$`G, B, \ell, n, d_0`$ に適用する。仮定 (hr) は
$`\mathrm{r1ok}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$ である。仮定 (hmin) を示すために
$`0 \lt k`$、$`k \lt n`$、$`q \lt \lvert B\rvert`$、$`\forall r \lt q,\ B_{0,q} \le B_{0,r}`$、
$`0 \lt B_{0,q} + k d_0`$ を取り、(5) の選言で場合分けする。

**第 1 の選言 $`d_0 = 0 \wedge i_1 = 0`$ のとき。**
[T.r1ok_min_d0zero](#t-r1ok_min_d0zero) を (3) と
$`\mathrm{r1ok}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$ に適用すればよい。

**第 2 の選言のとき。** すなわち

```math
0 \lt d_0 \ \wedge\ w_0 \lt \ell_2 \ \wedge\ \ell_1 = v_0 + d_0
  \ \wedge\ \lvert G\rvert \to^M_1 j_1
```

が成り立つとき。[T.r1ok_min_d0pos](#t-r1ok_min_d0pos) を適用する。その仮定 (hdom) は (3)、
(hd0), (hlp) はこの選言の第 1・第 3 成分、(hstep), (hlpstep) は上で示した
2 つの段差条件である。残る仮定 (hclimb) は、$`r' \lt \lvert B\rvert`$、
$`B_{0,r'} = v_0 + d_0 - 1`$、および

```math
\forall rr,\ \bigl(r' \lt rr \wedge rr \lt \lvert B\rvert\bigr) \to v_0 + d_0 \le B_{0,rr}
```

を仮定して $`w_0 \le B_{1,r'} + 1`$ を導くものであり、
[T.climb_bound](#t-climb_bound) を (1) と、この選言の第 1・第 2・第 3・第 4 成分に
適用して得られる。

以上より [T.r1ok_copyExp](#t-r1ok_copyExp) が使えて
$`\mathrm{r1ok}(\mathrm{copyExp}(G,B,d_0,n))`$ を得る。(2) よりこれは
$`\mathrm{r1ok}(M[n])`$ である。∎
