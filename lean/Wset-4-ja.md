[← README](README-ja.md) | [English](Wset-4.md) | [Japanese](Wset-4-ja.md) | Wset [1](Wset-ja.md) [2](Wset-2-ja.md) [3](Wset-3-ja.md) **4**

<a id="t-oper_cons_succ"></a>
## 定理: 後続子の主要ステップ (T.oper_cons_succ)

### 定理

$`v, n \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）とし、
$`k_1 := \lvert R\rvert - 1`$ とおく。
$`\mathrm{argOK}(R)`$（[D.argOK](Wset-ja.md#d-argOK)）、$`R \ne ()`$、
$`R_{1,k_1} = 0`$（[D.entry](Pss-ja.md#d-entry)）、
$`\neg\,\mathrm{hasParent}(R, 0, k_1)`$（[D.hasParent](Pss-ja.md#d-hasParent)）
を仮定すると

```math
\bigl((0,v) :: R\bigr)[n] = \bigl((0,v) :: \mathrm{dropLast}\,R\bigr)^{\frown n} .
```

（$`M[n]`$ [D.oper](Pss-ja.md#d-oper)）

ここで列 $`Q`$ に対し $`Q^{\frown n}`$ を $`Q`$ を $`n`$ 個連結した列とする。すなわち

```math
Q^{\frown 0} := (), \qquad Q^{\frown (n+1)} := Q^{\frown n} \mathbin{+\!\!+} Q .
```

### 証明

$`M := (0,v) :: R`$ と書く。$`R \ne ()`$ より $`0 \lt \lvert R\rvert`$ であり、
$`\lvert M\rvert - 1 = \lvert R\rvert`$ である。
[T.entry_cons_last](Wset-3-ja.md#t-entry_cons_last) より $`M_{0,\lvert R\rvert} = R_{0,k_1}`$ である。

**第 1 段：$`\mathrm{idx}_1(M, \lvert M\rvert - 1) = 0`$（[D.idx1](Pss-ja.md#d-idx1)）。**
[T.idx1_cons_last](Wset-3-ja.md#t-idx1_cons_last) より
$`\mathrm{idx}_1(M, \lvert R\rvert) = \mathrm{idx}_1(R, k_1)`$ であり、
仮定 $`R_{1,k_1} = 0`$ と $`\mathrm{idx}_1`$ の定義（D.idx1）の第 2 の場合により
$`\mathrm{idx}_1(R, k_1) = 0`$ である。

**第 2 段：$`\forall k \lt k_1,\ R_{0,k_1} \le R_{0,k}`$。**
$`k \lt k_1`$ かつ $`R_{0,k} \lt R_{0,k_1}`$ なる $`k`$ が存在したとすると、
$`k_1 \lt \lvert R\rvert`$ であるから [T.hasParent_zero_iff](Wset-3-ja.md#t-hasParent_zero_iff) より
$`\mathrm{hasParent}(R, 0, k_1)`$ となり、仮定に反する。

**第 3 段：$`0 \to^M_0 \lvert R\rvert`$（[D.nextrel0](Pss-ja.md#d-nextrel0)）。**
$`\to^M_0`$ の定義（D.nextrel0）の 5 条件を確かめる。

- (1) $`0 \lt \lvert M\rvert`$：$`\lvert M\rvert = \lvert R\rvert + 1 \ge 1`$。
- (2) $`\lvert R\rvert \lt \lvert M\rvert`$：同上。
- (3) $`0 \lt \lvert R\rvert`$：$`R \ne ()`$ による。
- (4) $`M_{0,0} \lt M_{0,\lvert R\rvert}`$：$`M`$ の第 $`0`$ 列は $`(0,v)`$ であるから
  $`M_{0,0} = 0`$ である。一方 $`k_1 \lt \lvert R\rvert`$ と
  [T.entry_pair_mem](Wset-2-ja.md#t-entry_pair_mem) より対 $`(R_{0,k_1}, R_{1,k_1})`$ は $`R`$ の要素だから、
  $`\mathrm{argOK}`$ の定義（D.argOK）より $`M_{0,\lvert R\rvert} = R_{0,k_1} \gt 0`$ である。
- (5) $`\forall l,\ (0 \lt l \wedge l \lt \lvert R\rvert) \to M_{0,\lvert R\rvert} \le M_{0,l}`$：
  $`l = l' + 1`$ と書けて $`l' \lt k_1`$ である。[T.entry_cons](Wset-3-ja.md#t-entry_cons) より
  $`M_{0,l'+1} = R_{0,l'}`$ であり、第 2 段が $`R_{0,k_1} \le R_{0,l'}`$ を与える。

**第 4 段：$`y \to^M_0 \lvert R\rvert`$ ならば $`y = 0`$。**
$`y \ne 0`$ とすると $`y = y' + 1`$ と書け、[T.nextR_cons_last](Wset-3-ja.md#t-nextR_cons_last) より
$`y' \to^R_0 k_1`$ である。その定義（D.nextrel0）の条件 (3) より $`y' \lt k_1`$、
条件 (4) より $`R_{0,y'} \lt R_{0,k_1}`$ である。ところが第 2 段は
$`R_{0,k_1} \le R_{0,y'}`$ を与えるから矛盾である。

**第 5 段：展開の適用。**
第 3 段と第 4 段より $`\mathrm{hasParent}(M, 0, \lvert R\rvert)`$ が成り立ち、
第 1 段と合わせて
$`\mathrm{hasParent}\bigl(M, \mathrm{idx}_1(M, \lvert M\rvert-1), \lvert M\rvert-1\bigr)`$ である。
また [T.parent_nextR](Decrease-ja.md#t-parent_nextR) と第 4 段より
$`\mathrm{par}^M_0(\lvert R\rvert) = 0`$（[D.parent](Pss-ja.md#d-parent)）である。
$`\lvert M\rvert - 1 = \lvert R\rvert \ne 0`$ であり、
$`M_{0,\lvert R\rvert} = R_{0,k_1} \gt 0`$ より
$`\neg(M_{0,\lvert M\rvert-1} = 0 \wedge M_{1,\lvert M\rvert-1} = 0)`$ である。
よって [T.oper_root_tiling](Wset-3-ja.md#t-oper_root_tiling) が適用できる。第 1 段により
$`\mathrm{idx}_1(M, \lvert M\rvert-1) = 0`$ であるから、そこに現れる $`e`$ は
$`0 \lt \mathrm{idx}_1(M,\lvert M\rvert-1)`$ が偽であることにより $`e = 0`$ であり、
各ブロックは $`(\mathrm{dropLast}\,M)^{+k\cdot 0} = \mathrm{dropLast}\,M`$（[D.shiftr0](Cnf-2-ja.md#d-shiftr0)）である。
したがって

```math
M[n] = \bigl(\mathrm{dropLast}\,M\bigr)^{\frown n} .
```

最後に $`R \ne ()`$ より、$`M = (0,v) :: R`$ の末尾要素は $`R`$ の末尾要素であるから

```math
\mathrm{dropLast}\,M = \mathrm{dropLast}\bigl((0,v) :: R\bigr) = (0,v) :: \mathrm{dropLast}\,R
```

である。∎

<a id="t-oper_cons_tower"></a>
## 定理: 塔の等式 (T.oper_cons_tower)

### 定理

$`v, m, n \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ とする。
$`\mathrm{argOK}(R)`$、$`\mathrm{domT}(R, m)`$（[D.domT](Wset-ja.md#d-domT)）、$`v \le m`$ ならば

```math
\bigl((0,v) :: R\bigr)[n] = \mathrm{tow}_v(R,n) .
```

（$`\mathrm{tow}_v(R,n)`$ [D.tow](Wset-3-ja.md#d-tow)）

### 証明

$`M := (0,v) :: R`$、$`k_1 := \lvert R\rvert - 1`$、$`x := R_{0,k_1}`$ と書く。

まず $`R \ne ()`$ である。実際 $`R = ()`$ とすると
[T.not_domT_nil](Wset-ja.md#t-not_domT_nil) が $`\mathrm{domT}(R,m)`$ に反する。
したがって $`0 \lt \lvert R\rvert`$ であり $`\lvert M\rvert - 1 = \lvert R\rvert`$ である。
[T.entry_cons_last](Wset-3-ja.md#t-entry_cons_last) より
$`M_{0,\lvert R\rvert} = R_{0,k_1} = x`$、$`M_{1,\lvert R\rvert} = R_{1,k_1}`$ である。
$`\mathrm{domT}`$ の定義（D.domT）の第 1 連言子より $`R_{1,k_1} = m + 1`$、
第 2 連言子より $`\neg\,\mathrm{hasParent}(R, 1, k_1)`$ である。
また $`k_1 \lt \lvert R\rvert`$ と [T.entry_pair_mem](Wset-2-ja.md#t-entry_pair_mem)、
$`\mathrm{argOK}`$ の定義（D.argOK）より $`0 \lt x`$ である。

**第 1 段：$`\mathrm{idx}_1(M, \lvert M\rvert - 1) = 1`$。**
[T.idx1_cons_last](Wset-3-ja.md#t-idx1_cons_last) より
$`\mathrm{idx}_1(M, \lvert R\rvert) = \mathrm{idx}_1(R, k_1)`$ であり、
$`R_{1,k_1} = m + 1 \gt 0`$ と $`\mathrm{idx}_1`$ の定義（D.idx1）の第 1 の場合により
その値は $`1`$ である。

**第 2 段：$`y \to^M_1 \lvert R\rvert`$（[D.nextrel1](Pss-ja.md#d-nextrel1)）ならば $`y = 0`$。**
$`y \ne 0`$ とすると $`y = y' + 1`$ と書け、[T.nextR_cons_last](Wset-3-ja.md#t-nextR_cons_last) より
$`y' \to^R_1 k_1`$ である。$`\to^R_1`$ の定義（D.nextrel1）の条件 (3)(4)(5) はそれぞれ
$`y' \lt k_1`$、$`R_{1,y'} \lt R_{1,k_1}`$、$`y' \le^R_0 k_1`$（[D.le0](Pss-ja.md#d-le0)）であり、これは
$`\mathrm{r1cand}(R, k_1, y')`$（[D.r1cand](Wset-ja.md#d-r1cand)）にほかならない。$`k_1 \lt \lvert R\rvert`$ であるから
[T.hasParent_one_iff](Wset-ja.md#t-hasParent_one_iff) より $`\mathrm{hasParent}(R, 1, k_1)`$ となり、
上で見た $`\neg\,\mathrm{hasParent}(R,1,k_1)`$ に矛盾する。

**第 3 段：$`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$ と $`\mathrm{par}^M_1(\lvert R\rvert) = 0`$。**
$`v \le m \lt m + 1 = R_{1,k_1}`$ であるから、
[T.hasParent_cons_one](Wset-3-ja.md#t-hasParent_cons_one) を第 2 選言で適用して
$`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$ を得る。
[T.parent_nextR](Decrease-ja.md#t-parent_nextR) より
$`\mathrm{par}^M_1(\lvert R\rvert) \to^M_1 \lvert R\rvert`$ であるから、第 2 段より
$`\mathrm{par}^M_1(\lvert R\rvert) = 0`$ である。

**第 4 段：敷き詰めの形。**
$`\lvert M\rvert - 1 = \lvert R\rvert \ne 0`$ であり、$`M_{0,\lvert R\rvert} = x \gt 0`$ より
$`\neg(M_{0,\lvert M\rvert-1} = 0 \wedge M_{1,\lvert M\rvert-1} = 0)`$ である。
第 1 段・第 3 段と合わせて [T.oper_root_tiling](Wset-3-ja.md#t-oper_root_tiling) が適用できる。
第 1 段より $`\mathrm{idx}_1(M,\lvert M\rvert-1) = 1 \gt 0`$ であるから、そこに現れる $`e`$ は

```math
e = M_{0,\lvert M\rvert-1} - M_{0,0} = x - 0 = x
```

である（$`M`$ の第 $`0`$ 列は $`(0,v)`$ だから $`M_{0,0} = 0`$）。また
$`R \ne ()`$ より $`\mathrm{dropLast}\,M = (0,v) :: \mathrm{dropLast}\,R`$ である。
$`D := (0,v) :: \mathrm{dropLast}\,R`$ とおくと

```math
M[n] = D^{+0\cdot x} \mathbin{+\!\!+} D^{+1\cdot x} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} D^{+(n-1)x} .
```

**第 5 段：右辺が $`\mathrm{tow}_v(R,n)`$ に等しいこと。**
$`n`$ に関する帰納法。帰納法の述語は

```math
\Phi(n) :\equiv D^{+0\cdot x} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} D^{+(n-1)x} = \mathrm{tow}_v(R,n) .
```

- **基底段** $`n = 0`$：左辺は空の連結すなわち $`()`$ であり、
  $`\mathrm{tow}`$ の定義（D.tow）の第 1 式より $`\mathrm{tow}_v(R,0) = ()`$ である。

- **帰納段** $`n \to n+1`$：$`\Phi(n)`$ を仮定する。
  左辺の先頭ブロックを切り出すと、$`D^{+0\cdot x} = D`$ であり、
  残りは各ブロックの添字を 1 ずつずらしたものだから

```math
D^{+0\cdot x} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} D^{+n x}
  = D \mathbin{+\!\!+} \Bigl(D^{+0\cdot x} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} D^{+(n-1)x}\Bigr)^{+x}
```

  である（$`(L^{+a})^{+b} = L^{+(a+b)}`$ と $`k\,x + x = (k+1)x`$ による）。
  帰納法の仮定 $`\Phi(n)`$ を右辺の括弧の中に適用すると

```math
D^{+0\cdot x} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} D^{+n x}
  = D \mathbin{+\!\!+} \bigl(\mathrm{tow}_v(R,n)\bigr)^{+x}
```

  を得る。一方 $`\mathrm{tow}`$ の定義（D.tow）の第 2 式と
  $`\mathrm{graft}`$ の定義（[D.graft](Wset-ja.md#d-graft)）より

```math
\begin{aligned}
\mathrm{tow}_v(R,n+1)
  &= (0,v) :: \mathrm{graft}\bigl(R, \mathrm{tow}_v(R,n)\bigr) \cr
  &= (0,v) :: \Bigl(\mathrm{dropLast}\,R
       \mathbin{+\!\!+} \bigl(\mathrm{tow}_v(R,n)\bigr)^{+R_{0,\lvert R\rvert-1}}\Bigr)
\end{aligned}
```

  であり、$`R_{0,\lvert R\rvert-1} = x`$、$`(0,v) :: \mathrm{dropLast}\,R = D`$ であるから
  右辺は $`D \mathbin{+\!\!+} (\mathrm{tow}_v(R,n))^{+x}`$ に等しい。よって $`\Phi(n+1)`$。∎

<a id="t-domT_cons_of_lt"></a>
## 定理: 連続の場合の $`\mathrm{dom}`$ の継承 (T.domT_cons_of_lt)

### 定理

$`v, m \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ とする。
$`\mathrm{argOK}(R)`$、$`\mathrm{domT}(R, m)`$、$`m \lt v`$ ならば
$`\mathrm{domT}\bigl((0,v) :: R,\ m\bigr)`$。

### 証明

$`M := (0,v) :: R`$、$`k_1 := \lvert R\rvert - 1`$ と書く。
[T.not_domT_nil](Wset-ja.md#t-not_domT_nil) より $`R \ne ()`$ であり、
$`0 \lt \lvert R\rvert`$、$`\lvert M\rvert - 1 = \lvert R\rvert`$ である。
[T.entry_cons_last](Wset-3-ja.md#t-entry_cons_last) より $`M_{1,\lvert R\rvert} = R_{1,k_1}`$ である。

$`\mathrm{domT}`$ の定義（D.domT）の 2 つの連言子を示す。

**第 1 連言子 $`M_{1,\lvert M\rvert - 1} = m + 1`$。**
$`M_{1,\lvert M\rvert-1} = M_{1,\lvert R\rvert} = R_{1,k_1}`$ であり、
仮定 $`\mathrm{domT}(R,m)`$ の第 1 連言子より $`R_{1,k_1} = m + 1`$ である。

**第 2 連言子 $`\neg\,\mathrm{hasParent}(M, 1, \lvert M\rvert - 1)`$。**
$`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$ を仮定して矛盾を導く。
[T.cons_len_lt](Wset-3-ja.md#t-cons_len_lt) より $`\lvert R\rvert \lt \lvert M\rvert`$ であるから
[T.hasParent_one_iff](Wset-ja.md#t-hasParent_one_iff) が使えて、

```math
j_0 \lt \lvert R\rvert, \qquad j_0 \le^M_0 \lvert R\rvert, \qquad M_{1,j_0} \lt M_{1,\lvert R\rvert} = m+1
```

をみたす $`j_0`$ が取れる。$`j_0`$ で場合分けする。

- **$`j_0 = 0`$ のとき。** $`M`$ の第 $`0`$ 列は $`(0,v)`$ であるから $`M_{1,0} = v`$ であり、
  $`v \lt m + 1`$ すなわち $`v \le m`$ となる。これは仮定 $`m \lt v`$ に矛盾する。

- **$`j_0 = j' + 1`$ のとき。** [T.entry_cons](Wset-3-ja.md#t-entry_cons) より
  $`M_{1,j'+1} = R_{1,j'}`$ であるから $`R_{1,j'} \lt m + 1 = R_{1,k_1}`$ である。
  また $`j' + 1 \lt \lvert R\rvert`$ より $`j' \lt \lvert R\rvert - 1 = k_1`$ であり、
  $`j' + 1 \le^M_0 \lvert R\rvert`$ と [T.le0_cons_last](Wset-3-ja.md#t-le0_cons_last) より
  $`j' \le^R_0 k_1`$ である。
  これら 3 つは $`\mathrm{r1cand}(R, k_1, j')`$ にほかならないから、
  $`k_1 \lt \lvert R\rvert`$ と [T.hasParent_one_iff](Wset-ja.md#t-hasParent_one_iff) より
  $`\mathrm{hasParent}(R, 1, k_1)`$ を得る。これは仮定 $`\mathrm{domT}(R,m)`$ の
  第 2 連言子に矛盾する。∎

<a id="t-argOK_oper"></a>
## 定理: 引数ブロックは展開で保たれる (T.argOK_oper)

### 定理

$`\mathrm{argOK}(R)`$ ならば、任意の $`n`$ に対し $`\mathrm{argOK}(R[n])`$。

### 証明

$`\mathrm{argOK}`$ の定義（D.argOK）より、仮定は $`\forall p \in R,\ 0 \lt p_1`$、
すなわち $`\forall p \in R,\ 1 \le p_1`$ である。
[T.oper_mem_ge](Wset-2-ja.md#t-oper_mem_ge) を $`c := 1`$、$`B := R`$ として適用すると
$`\forall p \in R[n],\ 1 \le p_1`$、すなわち $`\forall p \in R[n],\ 0 \lt p_1`$ を得る。∎

<a id="t-argOK_graft"></a>
## 定理: 引数ブロックは接ぎ木で保たれる (T.argOK_graft)

### 定理

$`R \ne ()`$ かつ $`\mathrm{argOK}(R)`$ ならば、任意の $`z' \in \mathrm{PairSeq}`$ に対し
$`\mathrm{argOK}\bigl(\mathrm{graft}(R, z')\bigr)`$。

### 証明

仮定は $`\forall p \in R,\ 1 \le p_1`$ と同値である。
[T.graft_mem_ge](Wset-2-ja.md#t-graft_mem_ge) を $`c := 1`$、$`B := R`$、$`z := z'`$ として適用すると
$`\forall p \in \mathrm{graft}(R,z'),\ 1 \le p_1`$、すなわち
$`\forall p \in \mathrm{graft}(R,z'),\ 0 \lt p_1`$ を得る。∎

<a id="t-argOK_dropLast"></a>
## 定理: 引数ブロックは末尾切りで保たれる (T.argOK_dropLast)

### 定理

$`\mathrm{argOK}(R)`$ ならば $`\mathrm{argOK}(\mathrm{dropLast}\,R)`$。

### 証明

$`p \in \mathrm{dropLast}\,R`$ とする。$`\mathrm{dropLast}\,R`$ は $`R`$ の前部分列であるから
$`p \in R`$ であり、$`\mathrm{argOK}`$ の定義（D.argOK）より $`0 \lt p_1`$。∎

<a id="t-based_cons"></a>
## 定理: 主要ブロックは正規化形 (T.based_cons)

### 定理

任意の $`v \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ に対し
$`\mathrm{based}\bigl((0,v) :: R\bigr)`$（[D.based](Wset-ja.md#d-based)）。

### 証明

$`\mathrm{based}`$ の定義（D.based）より示すべきことは
$`\bigl((0,v) :: R\bigr)_{0,0} = 0`$ である。
$`(0,v) :: R`$ の第 $`0`$ 列は $`(0,v)`$ であるから、
$`M_{i,j}`$ の定義（D.entry）よりその行 $`0`$ の値は $`0`$ である。∎

<a id="t-rsum_self_cons"></a>
## 定理: 主要ブロックの根は最小の深さをもつ (T.rsum_self_cons)

### 定理

任意の $`v \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ に対し

```math
\forall p \in (0,v) :: R,\ \bigl((0,v) :: R\bigr)_{0,0} \le p_1 .
```

### 証明

$`(0,v) :: R`$ の第 $`0`$ 列は $`(0,v)`$ であるから
$`\bigl((0,v) :: R\bigr)_{0,0} = 0`$ である（$`M_{i,j}`$ の定義 D.entry）。
$`p_1`$ は自然数であるから $`0 \le p_1`$ である。∎

<a id="t-W_flatMap_copies"></a>
## 定理: 同一の木の複製も $`W_u`$ に属する (T.W_flatMap_copies)

### 定理

$`Q \in W_u`$（[D.W](Wset-ja.md#d-W)）かつ $`\forall p \in Q,\ Q_{0,0} \le p_1`$ ならば、
任意の $`n \in \mathbb{N}`$ に対し
$`Q^{\frown n} \in W_u`$。

### 証明

$`n`$ に関する帰納法。帰納法の述語は

```math
\Phi(n) :\equiv Q^{\frown n} \in W_u .
```

- **基底段** $`n = 0`$：$`Q^{\frown 0} = ()`$ であり、
  [T.W_nil](Wset-ja.md#t-W_nil) より $`() \in W_u`$ である。

- **帰納段** $`n \to n+1`$：$`\Phi(n)`$、すなわち $`Q^{\frown n} \in W_u`$ を仮定する。
  $`Q^{\frown(n+1)} = Q^{\frown n} \mathbin{+\!\!+} Q`$ であるから、
  [T.W_add](Wset-3-ja.md#t-W_add) を $`A := Q^{\frown n}`$、$`B := Q`$ として適用すればよい。
  その仮定 $`\mathrm{rsum}(Q^{\frown n}, Q)`$（[D.rsum](Wset-ja.md#d-rsum)）、すなわち

```math
\forall p \in Q^{\frown n} \mathbin{+\!\!+} Q,\ Q_{0,0} \le p_1
```

  を確かめる。$`p \in Q^{\frown n} \mathbin{+\!\!+} Q`$ とすると、
  $`p \in Q^{\frown n}`$ か $`p \in Q`$ である。後者のときは仮定そのものである。
  前者のとき、$`Q^{\frown n}`$ は $`Q`$ を $`n`$ 個連結した列であるから $`p \in Q`$ であり、
  やはり仮定が $`Q_{0,0} \le p_1`$ を与える。よって $`\Phi(n+1)`$。∎

<a id="t-Wstar_closed"></a>
## 定理: $`A_u(W^{*}) \subseteq W^{*}`$ (T.Wstar_closed)

### 定理

任意の $`u \in \mathbb{N}`$、$`M \in \mathrm{PairSeq}`$ に対し、
$`M \in A_u(W^{*})`$（$`A_u`$ [D.Aop](Wset-ja.md#d-Aop)、$`W^{*}`$ [D.Wstar](Wset-3-ja.md#d-Wstar)）ならば
$`M \in W^{*}`$。

### 証明

定理の主張の $`M`$ を、以下 $`R`$ と書く。$`W^{*}`$ の定義（D.Wstar）より、示すべきことは

```math
\mathrm{argOK}(R) \ \longrightarrow\ \forall v \in \mathbb{N},\ (0,v) :: R \in W_v
```

である。そこで $`\mathrm{argOK}(R)`$ と $`v`$ を仮定する。
$`N := (0,v) :: R`$、$`k_1 := \lvert R\rvert - 1`$ と書く。

**$`R = ()`$ のとき。** $`N = (0,v) :: ()`$ であり、
[T.Om_mem_W](Wset-3-ja.md#t-Om_mem_W) より $`N \in W_v`$ である。

以下 $`R \ne ()`$ とする。$`0 \lt \lvert R\rvert`$、$`\lvert N\rvert - 1 = \lvert R\rvert`$ であり、
[T.entry_cons_last](Wset-3-ja.md#t-entry_cons_last) より
$`N_{1,\lvert N\rvert-1} = N_{1,\lvert R\rvert} = R_{1,k_1}`$ である。
次の 2 つを用意する。

- **(D1)** $`\mathrm{hasParent}(N, 1, \lvert R\rvert)`$ ならば
  $`\mathrm{natDom}(N)`$（[D.natDom](Wset-ja.md#d-natDom)）。
  [T.natDom_iff](Wset-ja.md#t-natDom_iff) の右辺の第 2 選言が
  $`\mathrm{hasParent}(N, 1, \lvert N\rvert - 1)`$ であり、
  $`\lvert N\rvert - 1 = \lvert R\rvert`$ だからである。
- **(D2)** $`R_{1,k_1} = 0`$ ならば $`\mathrm{natDom}(N)`$。
  [T.natDom_iff](Wset-ja.md#t-natDom_iff) の右辺の第 1 選言が $`N_{1,\lvert N\rvert-1} = 0`$ であり、
  これは $`R_{1,k_1} = 0`$ に等しいからである。

仮定 $`R \in A_u(W^{*})`$ について、$`A_u`$ の定義（D.Aop）の 3 分岐で場合分けする。

**分岐 (1)：$`\lvert R\rvert \le 1`$ かつ $`R_{1,0} = 0`$ のとき。**
$`R \ne ()`$ より $`\lvert R\rvert = 1`$、したがって $`k_1 = 0`$ であり $`R_{1,k_1} = 0`$ である。
また $`\neg\,\mathrm{hasParent}(R, 0, k_1)`$ である。実際
$`j_0 \to^R_0 0`$ なる $`j_0`$ があれば
[T.nextR_index_lt](Decrease-ja.md#t-nextR_index_lt) より $`j_0 \lt 0`$ となり、
自然数についてこれは不可能である。さらに $`\lvert R\rvert = 1`$ より
$`\mathrm{dropLast}\,R = ()`$ である。

[T.A1_intro](Wset-ja.md#t-A1_intro) により $`N \in A_v(W_v)`$ を示せばよい。
$`A_v`$ の定義（D.Aop）の分岐 (2) を取る。
$`\mathrm{natDom}(N)`$ は (D2) による。$`n \ge 1`$ に対する $`N[n] \in W_v`$ は、
[T.oper_cons_succ](#t-oper_cons_succ) より

```math
N[n] = \bigl((0,v) :: \mathrm{dropLast}\,R\bigr)^{\frown n} = \bigl((0,v) :: ()\bigr)^{\frown n}
```

であり、[T.Om_mem_W](Wset-3-ja.md#t-Om_mem_W) より $`(0,v) :: () \in W_v`$、
[T.rsum_self_cons](#t-rsum_self_cons) より
$`\forall p \in (0,v) :: (),\ \bigl((0,v) :: ()\bigr)_{0,0} \le p_1`$ であるから、
[T.W_flatMap_copies](#t-W_flatMap_copies) が $`N[n] \in W_v`$ を与える。

**分岐 (2)：$`\mathrm{natDom}(R)`$ かつ $`\forall n \ge 1,\ R[n] \in W^{*}`$ のとき。**
$`\mathrm{hasParent}\bigl(R, \mathrm{idx}_1(R,k_1), k_1\bigr)`$ が成り立つかどうかで場合分けする。

**(2a) $`\mathrm{hasParent}\bigl(R, \mathrm{idx}_1(R,k_1), k_1\bigr)`$ のとき。**
まず $`\mathrm{natDom}(N)`$ を示す。$`R_{1,k_1} = 0`$ ならば (D2) による。
$`R_{1,k_1} \ne 0`$ ならば、$`\mathrm{idx}_1`$ の定義（D.idx1）の第 1 の場合より
$`\mathrm{idx}_1(R,k_1) = 1`$ であるから、いまの仮定は $`\mathrm{hasParent}(R,1,k_1)`$ である。
[T.hasParent_cons_one](Wset-3-ja.md#t-hasParent_cons_one) を第 1 選言で適用して
$`\mathrm{hasParent}(N, 1, \lvert R\rvert)`$ を得、(D1) を使う。

[T.A1_intro](Wset-ja.md#t-A1_intro) により $`N \in A_v(W_v)`$ を、その分岐 (2) で示す。
$`n \ge 1`$ とすると [T.oper_cons_nat](Wset-3-ja.md#t-oper_cons_nat) より
$`N[n] = (0,v) :: R[n]`$ である。分岐 (2) の仮定より $`R[n] \in W^{*}`$ であり、
[T.argOK_oper](#t-argOK_oper) より $`\mathrm{argOK}(R[n])`$ であるから、
$`W^{*}`$ の定義（D.Wstar）を $`v`$ に適用して $`(0,v) :: R[n] \in W_v`$ を得る。

**(2b) $`\neg\,\mathrm{hasParent}\bigl(R, \mathrm{idx}_1(R,k_1), k_1\bigr)`$ のとき。**
まず $`R_{1,k_1} = 0`$ を示す。$`R_{1,k_1} \ne 0`$ とすると
$`R_{1,k_1} = m + 1`$ と書ける。$`\mathrm{natDom}(R)`$ の定義（D.natDom）より
$`\neg\,\mathrm{domT}(R,m)`$ であり、$`\mathrm{domT}`$ の定義（D.domT）の第 1 連言子は
いま成り立っているから、第 2 連言子が破れて $`\mathrm{hasParent}(R,1,k_1)`$ である。
ところが $`R_{1,k_1} \gt 0`$ より $`\mathrm{idx}_1(R,k_1) = 1`$ であるから、
これはいまの場合分けの仮定に矛盾する。

次に $`\neg\,\mathrm{hasParent}(R, 0, k_1)`$ を示す。$`\mathrm{hasParent}(R,0,k_1)`$ とすると、
$`R_{1,k_1} = 0`$ より $`\mathrm{idx}_1(R,k_1) = 0`$ であるから、
これもいまの場合分けの仮定に矛盾する。

[T.A1_intro](Wset-ja.md#t-A1_intro) により $`N \in A_v(W_v)`$ を、その分岐 (2) で示す。
$`\mathrm{natDom}(N)`$ は (D2) による。$`n \ge 1`$ に対しては
[T.oper_cons_succ](#t-oper_cons_succ) より

```math
N[n] = \bigl((0,v) :: \mathrm{dropLast}\,R\bigr)^{\frown n}
```

である。[T.rsum_self_cons](#t-rsum_self_cons) と
[T.W_flatMap_copies](#t-W_flatMap_copies) により、
$`(0,v) :: \mathrm{dropLast}\,R \in W_v`$ を示せば十分である。$`\lvert R\rvert`$ で場合分けする。

- **$`2 \le \lvert R\rvert`$ のとき。** $`k_1 = \lvert R\rvert - 1 \ne 0`$ である。
  いまの場合分けの仮定 $`\neg\,\mathrm{hasParent}\bigl(R,\mathrm{idx}_1(R,k_1),k_1\bigr)`$ により、
  $`R_{0,k_1} = 0 \wedge R_{1,k_1} = 0`$ が成り立つときは
  [T.oper_eq_pred_of_zero](Decrease-ja.md#t-oper_eq_pred_of_zero)、
  成り立たないときは
  [T.oper_eq_pred_of_noParent](Decrease-ja.md#t-oper_eq_pred_of_noParent) により
  $`R[1] = \mathrm{Pred}\,R`$（[D.Pred](Pss-ja.md#d-Pred)）である。
  さらに $`\neg(\lvert R\rvert \le 1)`$ であるから
  $`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合が選ばれ
  $`R[1] = \mathrm{dropLast}\,R`$ である。
  分岐 (2) の仮定を $`n := 1`$ に適用して $`\mathrm{dropLast}\,R \in W^{*}`$ を得る。
  [T.argOK_dropLast](#t-argOK_dropLast) より
  $`\mathrm{argOK}(\mathrm{dropLast}\,R)`$ であるから、
  $`W^{*}`$ の定義（D.Wstar）を $`v`$ に適用して
  $`(0,v) :: \mathrm{dropLast}\,R \in W_v`$ を得る。

- **$`\lvert R\rvert = 1`$ のとき。** $`\mathrm{dropLast}\,R = ()`$ であるから
  $`(0,v) :: \mathrm{dropLast}\,R = (0,v) :: ()`$ であり、
  [T.Om_mem_W](Wset-3-ja.md#t-Om_mem_W) より $`W_v`$ に属する。

**分岐 (3)：$`m \lt u`$、$`\mathrm{domT}(R,m)`$、かつ**
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(R,z) \in W^{*}`$ **のとき。**
$`v \le m`$ か否かで場合分けする。

**(3a) $`v \le m`$ のとき。**
まず $`\forall k \in \mathbb{N},\ \mathrm{tow}_v(R,k) \in W_v`$ を $`k`$ に関する帰納法で示す。
帰納法の述語は $`\Psi(k) :\equiv \mathrm{tow}_v(R,k) \in W_v`$ である。

- **基底段** $`k = 0`$：$`\mathrm{tow}`$ の定義（D.tow）の第 1 式より
  $`\mathrm{tow}_v(R,0) = ()`$ であり、[T.W_nil](Wset-ja.md#t-W_nil) より $`() \in W_v`$。

- **帰納段** $`k \to k+1`$：$`\Psi(k)`$ を仮定する。
  まず $`\mathrm{based}(\mathrm{tow}_v(R,k))`$ を示す。$`k = 0`$ のときは
  $`\mathrm{tow}_v(R,0) = ()`$ であり [T.based_nil](Wset-ja.md#t-based_nil) による。
  $`k = k' + 1`$ のときは $`\mathrm{tow}`$ の定義（D.tow）の第 2 式より
  $`\mathrm{tow}_v(R,k) = (0,v) :: \mathrm{graft}(R, \mathrm{tow}_v(R,k'))`$ であり、
  [T.based_cons](#t-based_cons) による。
  次に $`v \le m`$ と [T.W_mono](Wset-ja.md#t-W_mono) を $`\Psi(k)`$ に適用して
  $`\mathrm{tow}_v(R,k) \in W_m`$ を得る。分岐 (3) の仮定を
  $`z := \mathrm{tow}_v(R,k)`$ に適用すると
  $`\mathrm{graft}(R, \mathrm{tow}_v(R,k)) \in W^{*}`$ である。
  $`R \ne ()`$（[T.not_domT_nil](Wset-ja.md#t-not_domT_nil) と $`\mathrm{domT}(R,m)`$ による）と
  [T.argOK_graft](#t-argOK_graft) より
  $`\mathrm{argOK}\bigl(\mathrm{graft}(R,\mathrm{tow}_v(R,k))\bigr)`$ であるから、
  $`W^{*}`$ の定義（D.Wstar）を $`v`$ に適用して

```math
\mathrm{tow}_v(R,k+1) = (0,v) :: \mathrm{graft}\bigl(R, \mathrm{tow}_v(R,k)\bigr) \in W_v
```

  を得る。すなわち $`\Psi(k+1)`$。

[T.A1_intro](Wset-ja.md#t-A1_intro) により $`N \in A_v(W_v)`$ を、その分岐 (2) で示す。
$`\mathrm{natDom}(N)`$ は次のように得る。$`\mathrm{domT}(R,m)`$ の第 1 連言子より
$`R_{1,k_1} = m + 1`$ であり、$`v \le m \lt m+1`$ であるから
[T.hasParent_cons_one](Wset-3-ja.md#t-hasParent_cons_one) を第 2 選言で適用して
$`\mathrm{hasParent}(N,1,\lvert R\rvert)`$ を得、(D1) を使う。
$`n \ge 1`$ に対しては [T.oper_cons_tower](#t-oper_cons_tower) より
$`N[n] = \mathrm{tow}_v(R,n)`$ であり、いま示した $`\Psi(n)`$ よりこれは $`W_v`$ に属する。

**(3b) $`\neg(v \le m)`$ すなわち $`m \lt v`$ のとき。**
[T.A1_intro](Wset-ja.md#t-A1_intro) により $`N \in A_v(W_v)`$ を、その分岐 (3) で示す。
分岐 (3) の 3 つの成分を確かめる。

- $`m \lt v`$：いまの場合分けの仮定である。
- $`\mathrm{domT}(N, m)`$：[T.domT_cons_of_lt](#t-domT_cons_of_lt) による。
- $`z \in W_m`$ かつ $`\mathrm{based}(z)`$ ならば $`\mathrm{graft}(N,z) \in W_v`$：
  $`R \ne ()`$ であるから [T.graft_cons](Wset-3-ja.md#t-graft_cons) より
  $`\mathrm{graft}(N,z) = (0,v) :: \mathrm{graft}(R,z)`$ である。分岐 (3) の仮定より
  $`\mathrm{graft}(R,z) \in W^{*}`$ であり、[T.argOK_graft](#t-argOK_graft) より
  $`\mathrm{argOK}(\mathrm{graft}(R,z))`$ であるから、
  $`W^{*}`$ の定義（D.Wstar）を $`v`$ に適用して
  $`(0,v) :: \mathrm{graft}(R,z) \in W_v`$ を得る。∎

<a id="t-tree_shift"></a>
## 定理: 単一の木の平行移動 (T.tree_shift)

### 定理

$`(x,y) \in \mathbb{N}\times\mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ とし、
$`\forall r \in R,\ x \le r_1`$ を仮定する。このとき

```math
\Bigl((0,y) :: R^{-x}\Bigr)^{+x} = (x,y) :: R .
```

（$`R^{-x}`$ [D.shiftl0](ArgDom-2-ja.md#d-shiftl0)）

### 証明

平行移動 $`(\cdot)^{+x}`$ は各対の第 1 成分に $`x`$ を足す操作であるから、
先頭要素と残りに分けて

```math
\Bigl((0,y) :: R^{-x}\Bigr)^{+x} = (0 + x,\ y) :: \bigl(R^{-x}\bigr)^{+x}
```

である。$`0 + x = x`$ であり、仮定 $`\forall r \in R,\ x \le r_1`$ のもとで
[T.map_sub_add](Wset-2-ja.md#t-map_sub_add) が $`\bigl(R^{-x}\bigr)^{+x} = R`$ を与える。∎

<a id="t-mem_of_Aclosed_aux"></a>
## 定理: 長さに関する帰納法による所属（補題） (T.mem_of_Aclosed_aux)

### 定理

任意の $`N \in \mathbb{N}`$、$`M \in \mathrm{PairSeq}`$ に対し、
$`\lvert M\rvert \le N`$ ならば、条件

```math
\mathrm{(Acl)}\qquad \forall u \in \mathbb{N},\ \forall M' \in \mathrm{PairSeq},\
  M' \in A_u(X) \to M' \in X
```

をみたす任意の $`X \subseteq \mathrm{PairSeq}`$ について $`M \in X`$ である。

### 証明

$`N`$ に関する帰納法。帰納法の述語は

```math
\Phi(N) :\equiv \forall M,\ \lvert M\rvert \le N \to
  \forall X,\ \mathrm{(Acl)} \to M \in X .
```

- **基底段** $`N = 0`$：$`\lvert M\rvert \le 0`$ より $`M = ()`$ である。
  $`A_0`$ の定義（D.Aop）の分岐 (1) $`\lvert M\rvert \le 1 \wedge M_{1,0} = 0`$ は、
  $`\lvert ()\rvert = 0 \le 1`$ と、$`M_{i,j}`$ の定義（D.entry）により添字が範囲外の読みが
  $`(0,0)`$ であることから $`()_{1,0} = 0`$ であることにより成り立つ。
  よって $`() \in A_0(X)`$ であり、$`\mathrm{(Acl)}`$ を $`u := 0`$、$`M' := ()`$ に適用して
  $`() \in X`$ を得る。

**帰納段** $`N \to N+1`$：$`\Phi(N)`$ を仮定する。
$`\lvert M\rvert \le N+1`$ なる $`M`$ と $`\mathrm{(Acl)}`$ をみたす $`X`$ を取る。

$`M = ()`$ のときは、基底段で見たとおり $`() \in A_0(X)`$ であるから、
$`\mathrm{(Acl)}`$ を $`u := 0`$、$`M' := ()`$ に適用して $`M \in X`$ を得る。
以下 $`M \ne ()`$ とする。
[T.split_lastMin](Wset-2-ja.md#t-split_lastMin) により

```math
M = A \mathbin{+\!\!+} P, \qquad P \ne (), \qquad \mathrm{rsum}(A,P), \qquad
\forall p \in \mathrm{tail}\,P,\ P_{0,0} \lt p_1
```

なる $`A, P`$ を取る。$`0 \lt \lvert P\rvert`$ であり、
$`\lvert A\rvert + \lvert P\rvert = \lvert M\rvert \le N+1`$ である。$`A`$ で場合分けする。

**(a) $`A = ()`$ のとき。** $`M = P`$ である。$`P \ne ()`$ より
$`P = (x,y) :: R`$ と書ける。$`P_{0,0} = x`$ であり、$`\mathrm{tail}\,P = R`$ であるから、
上の第 4 の性質は

```math
\forall r \in R,\ x \lt r_1
```

である。ここから $`\mathrm{argOK}\bigl(R^{-x}\bigr)`$ が従う。実際
$`R^{-x}`$ の要素は $`r \in R`$ に対する $`(r_1 - x,\ r_2)`$ の形であり、
$`x \lt r_1`$ より $`0 \lt r_1 - x`$ である。

$`\lvert R^{-x}\rvert = \lvert R\rvert = \lvert P\rvert - 1 \le N`$ であるから、
帰納法の仮定 $`\Phi(N)`$ を $`M := R^{-x}`$、$`X := W^{*}`$ に適用できる。
$`W^{*}`$ が $`\mathrm{(Acl)}`$ をみたすことは [T.Wstar_closed](#t-Wstar_closed) である。
よって $`R^{-x} \in W^{*}`$ を得る。$`\mathrm{argOK}(R^{-x})`$ と合わせ、
$`W^{*}`$ の定義（D.Wstar）を $`y`$ に適用して

```math
(0,y) :: R^{-x} \in W_y
```

を得る。[T.W_shift](Wset-2-ja.md#t-W_shift) を $`d := x`$ として適用すると
$`\bigl((0,y) :: R^{-x}\bigr)^{+x} \in W_y`$ であり、
$`\forall r \in R,\ x \le r_1`$ のもとで [T.tree_shift](#t-tree_shift) より
この列は $`(x,y) :: R = P = M`$ に等しい。すなわち $`M \in W_y`$ である。

最後に [T.A2'](Wset-ja.md#t-A2') を $`u := y`$、$`Y := X`$ として適用する。その仮定
「$`\forall M',\ M' \in A_y(X) \to M' \in X`$」は $`\mathrm{(Acl)}`$ を $`u := y`$ に
特殊化したものである。よって $`W_y \subseteq X`$ であり $`M \in X`$。

**(b) $`A \ne ()`$ のとき。** $`0 \lt \lvert A\rvert`$ かつ $`0 \lt \lvert P\rvert`$ であり、
$`\lvert A\rvert + \lvert P\rvert \le N+1`$ であるから
$`\lvert A\rvert \le N`$ かつ $`\lvert P\rvert \le N`$ である。

帰納法の仮定 $`\Phi(N)`$ を $`M := A`$、$`X := X`$ に適用して $`A \in X`$ を得る。
次に [T.XA_closed](Wset-3-ja.md#t-XA_closed) を、$`\mathrm{(Acl)}`$ を $`u`$ に特殊化したものと
$`A \in X`$ に適用すると、任意の $`u`$ について

```math
\forall M',\ M' \in A_u\bigl(X^{(A)}\bigr) \to M' \in X^{(A)}
```

が成り立つ。すなわち $`X^{(A)}`$（[D.XA](Wset-2-ja.md#d-XA)）も $`\mathrm{(Acl)}`$ をみたす。
そこで帰納法の仮定 $`\Phi(N)`$ を $`M := P`$、$`X := X^{(A)}`$ に適用して
$`P \in X^{(A)}`$ を得る。$`X^{(A)}`$ の定義（D.XA）より
$`P \in X^{(A)}`$ は $`\mathrm{rsum}(A,P) \to A \mathbin{+\!\!+} P \in X`$ であり、
$`\mathrm{rsum}(A,P)`$ は上で取った通りであるから $`M = A \mathbin{+\!\!+} P \in X`$。∎

<a id="t-mem_of_Aclosed"></a>
## 定理: 条件 (Acl) をみたす集合はすべての列を含む (T.mem_of_Aclosed)

### 定理

$`X \subseteq \mathrm{PairSeq}`$ が

```math
\forall u \in \mathbb{N},\ \forall M \in \mathrm{PairSeq},\ M \in A_u(X) \to M \in X
```

をみたすならば、任意の $`M \in \mathrm{PairSeq}`$ に対し $`M \in X`$。

### 証明

[T.mem_of_Aclosed_aux](#t-mem_of_Aclosed_aux) を $`N := \lvert M\rvert`$ として適用する。
その仮定 $`\lvert M\rvert \le N`$ は $`\le`$ の反射性による。∎

<a id="t-mem_Wstar"></a>
## 定理: すべての列が $`W^{*}`$ に属する (T.mem_Wstar)

### 定理

任意の $`R \in \mathrm{PairSeq}`$ に対し $`R \in W^{*}`$。

### 証明

[T.mem_of_Aclosed](#t-mem_of_Aclosed) を $`X := W^{*}`$ として適用する。
その仮定は [T.Wstar_closed](#t-Wstar_closed) そのものである。∎

<a id="t-mem_W_of_bound_aux"></a>
## 定理: 行 1 の上界による所属（補題） (T.mem_W_of_bound_aux)

### 定理

任意の $`N \in \mathbb{N}`$、$`M \in \mathrm{PairSeq}`$、$`u \in \mathbb{N}`$ に対し、
$`\lvert M\rvert \le N`$ かつ $`\forall p \in M,\ p_2 \le u`$ ならば $`M \in W_u`$。

### 証明

$`N`$ に関する帰納法。帰納法の述語は

```math
\Phi(N) :\equiv \forall M,\ \lvert M\rvert \le N \to
  \forall u,\ \bigl(\forall p \in M,\ p_2 \le u\bigr) \to M \in W_u .
```

- **基底段** $`N = 0`$：$`\lvert M\rvert \le 0`$ より $`M = ()`$ であり、
  [T.W_nil](Wset-ja.md#t-W_nil) より $`() \in W_u`$。

**帰納段** $`N \to N+1`$：$`\Phi(N)`$ を仮定する。
$`\lvert M\rvert \le N+1`$ なる $`M`$、$`u`$、および
$`\forall p \in M,\ p_2 \le u`$ を取る。

$`M = ()`$ のときは [T.W_nil](Wset-ja.md#t-W_nil) による。以下 $`M \ne ()`$ とする。
[T.split_lastMin](Wset-2-ja.md#t-split_lastMin) により

```math
M = A \mathbin{+\!\!+} P, \qquad P \ne (), \qquad \mathrm{rsum}(A,P), \qquad
\forall p \in \mathrm{tail}\,P,\ P_{0,0} \lt p_1
```

なる $`A, P`$ を取る。$`0 \lt \lvert P\rvert`$ であり
$`\lvert A\rvert + \lvert P\rvert \le N+1`$ である。
$`P \ne ()`$ より $`P = (x,y) :: R`$ と書け、$`P_{0,0} = x`$、$`\mathrm{tail}\,P = R`$ であるから

```math
\forall r \in R,\ x \lt r_1
```

である。ここから $`\mathrm{argOK}\bigl(R^{-x}\bigr)`$ が従う。実際
$`R^{-x}`$ の要素は $`r \in R`$ に対する $`(r_1 - x,\ r_2)`$ の形であり、
$`x \lt r_1`$ より $`0 \lt r_1 - x`$ である。

[T.mem_Wstar](#t-mem_Wstar) より $`R^{-x} \in W^{*}`$ であるから、
$`W^{*}`$ の定義（D.Wstar）を $`\mathrm{argOK}(R^{-x})`$ と $`y`$ に適用して
$`(0,y) :: R^{-x} \in W_y`$ を得る。[T.W_shift](Wset-2-ja.md#t-W_shift) を $`d := x`$ として適用し、
$`\forall r \in R,\ x \le r_1`$ のもとで [T.tree_shift](#t-tree_shift) を使うと

```math
(x,y) :: R = \Bigl((0,y) :: R^{-x}\Bigr)^{+x} \in W_y
```

である。$`(x,y) \in A \mathbin{+\!\!+} P = M`$ であるから仮定より $`y \le u`$ であり、
[T.W_mono](Wset-ja.md#t-W_mono) より $`(x,y) :: R \in W_u`$、すなわち $`P \in W_u`$ である。

$`A`$ で場合分けする。

- **$`A = ()`$ のとき。** $`M = P \in W_u`$ である。

- **$`A \ne ()`$ のとき。** $`0 \lt \lvert A\rvert`$ かつ $`0 \lt \lvert P\rvert`$ であるから
  $`\lvert A\rvert \le N`$ である。$`A`$ の要素は $`M`$ の要素であるから
  $`\forall p \in A,\ p_2 \le u`$ であり、帰納法の仮定 $`\Phi(N)`$ を $`A`$ に適用して
  $`A \in W_u`$ を得る。$`\mathrm{rsum}(A,P)`$ と合わせて
  [T.W_add](Wset-3-ja.md#t-W_add) より $`M = A \mathbin{+\!\!+} P \in W_u`$。∎

<a id="t-mem_W_of_bound"></a>
## 定理: 行 1 の上界による所属 (T.mem_W_of_bound)

### 定理

$`M \in \mathrm{PairSeq}`$、$`u \in \mathbb{N}`$ とし
$`\forall p \in M,\ p_2 \le u`$ を仮定すると $`M \in W_u`$。

### 証明

[T.mem_W_of_bound_aux](#t-mem_W_of_bound_aux) を $`N := \lvert M\rvert`$ として適用する。
その仮定 $`\lvert M\rvert \le N`$ は $`\le`$ の反射性による。∎

<a id="t-le_maxr1"></a>
## 定理: 行 1 の値は最大値以下 (T.le_maxr1)

### 定理

任意の $`S \in \mathrm{PairSeq}`$ と $`p \in S`$ に対し $`p_2 \le \mathrm{maxr}_1(S)`$（[D.maxr1](Column-2-ja.md#d-maxr1)）。

### 証明

$`S`$ の構造に関する帰納法。帰納法の述語は

```math
\Phi(S) :\equiv \forall p \in S,\ p_2 \le \mathrm{maxr}_1(S) .
```

- **基底段** $`S = ()`$：空列は要素をもたないから前件が偽であり、$`\Phi(())`$ が成り立つ。

- **帰納段** $`S = q :: S'`$：$`\Phi(S')`$ を仮定する。
  [T.maxr1_cons](Column-2-ja.md#t-maxr1_cons) より
  $`\mathrm{maxr}_1(q :: S') = \max\bigl(q_2,\ \mathrm{maxr}_1(S')\bigr)`$ である。
  自然数の $`\max`$ については $`a \le \max(a,b)`$ かつ $`b \le \max(a,b)`$ が成り立つ。
  $`p \in q :: S'`$ とすると $`p = q`$ か $`p \in S'`$ である。
  - $`p = q`$ のとき。$`p_2 = q_2 \le \max\bigl(q_2, \mathrm{maxr}_1(S')\bigr)`$。
  - $`p \in S'`$ のとき。帰納法の仮定より $`p_2 \le \mathrm{maxr}_1(S')`$ であり、
    $`\mathrm{maxr}_1(S') \le \max\bigl(q_2, \mathrm{maxr}_1(S')\bigr)`$ と $`\le`$ の推移律により
    $`p_2 \le \max\bigl(q_2, \mathrm{maxr}_1(S')\bigr)`$。

  いずれの場合も $`p_2 \le \mathrm{maxr}_1(q :: S')`$ であるから $`\Phi(q :: S')`$。∎

<a id="t-mem_W_maxr1"></a>
## 定理: 行 1 の最大値の段での所属 (T.mem_W_maxr1)

### 定理

任意の $`M \in \mathrm{PairSeq}`$ に対し $`M \in W_{\mathrm{maxr}_1(M)}`$。

### 証明

[T.mem_W_of_bound](#t-mem_W_of_bound) を $`u := \mathrm{maxr}_1(M)`$ として適用する。
その仮定 $`\forall p \in M,\ p_2 \le \mathrm{maxr}_1(M)`$ は
[T.le_maxr1](#t-le_maxr1) である。∎

<a id="t-W_membership"></a>
## 定理: 標準形は或る段に属する (T.W_membership)

### 定理

任意の $`M \in \mathrm{PairSeq}`$ に対し、$`M \in \mathrm{ST\_PS}`$（[D.ST_PS](Pss-ja.md#d-ST_PS)）ならば
$`M \in W_u`$ なる $`u \in \mathbb{N}`$ が存在する。

### 証明

$`u := \mathrm{maxr}_1(M)`$ を取ればよい。
$`M \in W_{\mathrm{maxr}_1(M)}`$ は [T.mem_W_maxr1](#t-mem_W_maxr1) である。∎

<a id="t-wf_of_cofinality_and_membership"></a>
## 定理: 共終性と所属から整礎性へ (T.wf_of_cofinality_and_membership)

### 定理

次の 2 つを仮定する。

```math
\begin{aligned}
&\text{(cof)}\quad &&\forall M, N \in \mathrm{PairSeq},\
  M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,N \prec \mathrm{tr}\,M \cr
& &&\longrightarrow\ \exists n,\ 1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n]), \cr
&\text{(mem)}\quad &&\forall M \in \mathrm{PairSeq},\
  M \in \mathrm{ST\_PS} \to \exists u \in \mathbb{N},\ M \in W_u .
\end{aligned}
```

（$`\mathrm{tr}`$ [D.translate](Term-ja.md#d-translate)、$`\prec`$ [D.olt](Term-ja.md#d-olt)、$`\preceq`$ [D.ole](Term-ja.md#d-ole)）

このとき関係 $`R_{\mathrm{st}}`$（[D.Rst](Wset-ja.md#d-Rst)）は整礎である。

### 証明

$`R_{\mathrm{st}}`$ の定義（D.Rst）より

```math
a \mathbin{R_{\mathrm{st}}} b :\iff a \in \mathrm{ST\_PS} \wedge b \in \mathrm{ST\_PS}
  \wedge \mathrm{tr}\,a \prec \mathrm{tr}\,b
```

である。整礎性は $`\forall M,\ M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ と同値であるから、
$`M`$ を任意に取り $`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ を示す。
$`M \in \mathrm{ST\_PS}`$ か否かで場合分けする。

- **$`M \in \mathrm{ST\_PS}`$ のとき。** 仮定 (mem) により $`M \in W_u`$ なる $`u`$ を取る。
  [T.acc_of_W](Wset-ja.md#t-acc_of_W) を仮定 (cof) と $`u`$、$`M`$ に適用して
  $`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ を得る。

- **$`M \notin \mathrm{ST\_PS}`$ のとき。** [T.Acc.intro](Reduction-ja.md#t-Acc.intro)
  $`\bigl(\forall y,\ y \mathbin{R} a \to y \in \mathrm{Acc}_{R}\bigr) \to a \in \mathrm{Acc}_{R}`$ により、
  $`y \mathbin{R_{\mathrm{st}}} M`$ なるすべての $`y`$ について
  $`y \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ を示せばよい。ところが
  $`y \mathbin{R_{\mathrm{st}}} M`$ の第 2 連言子は $`M \in \mathrm{ST\_PS}`$ であり、
  いまの場合分けの仮定に矛盾する。よって前件をみたす $`y`$ は存在せず、
  $`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ が成り立つ。∎

<a id="t-wf_olt_ST_PS_of_cofinality"></a>
## 定理: 共終性から標準形上の順序の整礎性へ (T.wf_olt_ST_PS_of_cofinality)

### 定理

仮定 (cof)、すなわち

```math
\begin{aligned}
&\forall M, N \in \mathrm{PairSeq},\
  M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,N \prec \mathrm{tr}\,M \cr
&\qquad \longrightarrow\ \exists n,\ 1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])
\end{aligned}
```

のもとで、関係

```math
a \mathbin{\rho} b :\iff a \in \mathrm{ST\_PS} \wedge b \in \mathrm{ST\_PS}
  \wedge \mathrm{tr}\,a \prec \mathrm{tr}\,b
```

は整礎である。

### 証明

$`\rho`$ は $`R_{\mathrm{st}}`$ の定義（D.Rst）の右辺を書き下したものであり、
両者は定義により同一の関係である。
[T.wf_of_cofinality_and_membership](#t-wf_of_cofinality_and_membership) を、
仮定 (cof) と、(mem) として [T.W_membership](#t-W_membership) を取って適用すればよい。∎
