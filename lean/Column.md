[← README](README.md) ｜ Column **1** [2](Column-2.md) [3](Column-3.md) [4](Column-4.md)

<a id="t-stps_len_pos"></a>
## 定理: 標準形は空でない (T.stps_len_pos)

### 定理

$`M \in \mathrm{PairSeq}`$（[D.PairSeq](Pss.md#d-PairSeq)）が $`M \in \mathrm{ST\_PS}`$（[D.ST_PS](Pss.md#d-ST_PS)）
をみたすならば $`0 \lt \lvert M\rvert`$。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M) :\equiv 0 \lt \lvert M\rvert .
```

**基底段（規則 diag）$`M = \Delta_0^v`$（[D.diagSeq](Pss.md#d-diagSeq)）。**
[T.diagSeq_cons](Cnf.md#t-diagSeq_cons) を $`u := 0`$、$`v := v`$ とし、
仮定 $`0 \le v`$ のもとで適用すると
$`\Delta_0^v = (0,0) :: \Delta_1^v`$ である。
よって $`\lvert \Delta_0^v\rvert = 1 + \lvert \Delta_1^v\rvert`$ であり $`0 \lt \lvert \Delta_0^v\rvert`$。

**帰納段（規則 oper）$`M = N[n]`$（[D.oper](Pss.md#d-oper)、$`N \in \mathrm{ST\_PS}`$、$`1 \le n`$）。**
帰納法の仮定は $`\Phi(N)`$、すなわち $`0 \lt \lvert N\rvert`$ である。
$`\lvert N\rvert`$ で場合分けする。

**(a) $`1 \lt \lvert N\rvert`$ のとき。**
[T.oper_eq_dropLast_append](Cnf.md#t-oper_eq_dropLast_append) より、ある $`R \in \mathrm{PairSeq}`$ が存在して
$`N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R`$ である。ここで $`\mathrm{dropLast}\,N`$ は
$`N`$ の末尾 1 要素を落とした列であり $`\lvert \mathrm{dropLast}\,N\rvert = \lvert N\rvert - 1`$ である。よって

```math
\lvert N[n]\rvert = (\lvert N\rvert - 1) + \lvert R\rvert \ge \lvert N\rvert - 1 \ge 1
```

であり $`0 \lt \lvert N[n]\rvert`$。

**(b) $`\neg(1 \lt \lvert N\rvert)`$ のとき。**
$`\lvert N\rvert \le 1`$ であるから [T.oper_eq_self_short](Decrease.md#t-oper_eq_self_short) より
$`N[n] = N`$ である。$`\Phi(N[n])`$ は帰納法の仮定 $`\Phi(N)`$ そのものである。∎

<a id="t-stps_head"></a>
## 定理: 標準形の先頭は $`(0,0)`$ (T.stps_head)

### 定理

$`M \in \mathrm{ST\_PS}`$ ならば $`\mathrm{head}\,M = (0,0)`$。
ここで $`\mathrm{head}\,M`$ は $`M`$ の先頭要素であり、$`M = ()`$ のときは $`(0,0)`$ と読む。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M) :\equiv \mathrm{head}\,M = (0,0) .
```

**基底段（規則 diag）$`M = \Delta_0^v`$。**
[T.diagSeq_cons](Cnf.md#t-diagSeq_cons) を $`u := 0`$、$`v := v`$、仮定 $`0 \le v`$ に適用して
$`\Delta_0^v = (0,0) :: \Delta_1^v`$ を得る。先頭要素は $`(0,0)`$ である。

**帰納段（規則 oper）$`M = N[n]`$（$`N \in \mathrm{ST\_PS}`$、$`1 \le n`$）。**
帰納法の仮定は $`\Phi(N)`$、すなわち $`\mathrm{head}\,N = (0,0)`$ である。
$`\lvert N\rvert`$ で場合分けする。

**(a) $`1 \lt \lvert N\rvert`$ のとき。**
[T.oper_eq_dropLast_append](Cnf.md#t-oper_eq_dropLast_append) より、ある $`R`$ について
$`N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R`$ である。
$`1 \lt \lvert N\rvert`$ であるから $`N`$ は少なくとも 2 要素をもち、
$`N = a :: b :: u`$ と書ける。このとき

```math
\mathrm{dropLast}\,(a :: b :: u) = a :: \mathrm{dropLast}\,(b :: u)
```

であるから

```math
N[n] = a :: \bigl(\mathrm{dropLast}\,(b :: u) \mathbin{+\!\!+} R\bigr)
```

であり、$`\mathrm{head}\,(N[n]) = a = \mathrm{head}\,N`$ である。
帰納法の仮定より $`\mathrm{head}\,N = (0,0)`$。

**(b) $`\neg(1 \lt \lvert N\rvert)`$ のとき。**
$`\lvert N\rvert \le 1`$ であるから [T.oper_eq_self_short](Decrease.md#t-oper_eq_self_short) より
$`N[n] = N`$ であり、$`\Phi(N[n])`$ は帰納法の仮定そのものである。∎

<a id="t-getD_app_right"></a>
## 定理: 連結列の右側の読み出し (T.getD_app_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`i \in \mathbb{N}`$ とし $`\lvert A\rvert \le i`$ とする。このとき

```math
(A \mathbin{+\!\!+} T)\langle i\rangle = T\langle i - \lvert A\rvert\rangle
```

（$`M\langle j\rangle`$ [D.entry](Pss.md#d-entry)は範囲外で $`(0,0)`$ を返す読み出しである）。

### 証明

$`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$ である。$`i`$ の大きさで場合分けする。

**(a) $`i \lt \lvert A\rvert + \lvert T\rvert`$ のとき。**
$`i \lt \lvert A \mathbin{+\!\!+} T\rvert`$ であるから、$`M\langle j\rangle`$ の定義（D.entry）の第 1 の場合により
左辺は $`(A \mathbin{+\!\!+} T)_i`$ である。連結列の第 $`i`$ 要素は、$`\lvert A\rvert \le i`$ のとき
$`T_{i - \lvert A\rvert}`$ である。一方 $`i - \lvert A\rvert \lt \lvert T\rvert`$ であるから、
ふたたび D.entry の第 1 の場合により右辺も $`T_{i - \lvert A\rvert}`$ である。

**(b) $`\lvert A\rvert + \lvert T\rvert \le i`$ のとき。**
$`\lvert A \mathbin{+\!\!+} T\rvert \le i`$ であるから D.entry の第 2 の場合により左辺は $`(0,0)`$ である。
また $`\lvert A\rvert \le i`$ と $`\lvert A\rvert + \lvert T\rvert \le i`$ から $`\lvert T\rvert \le i - \lvert A\rvert`$
であり、右辺も $`(0,0)`$ である。∎

<a id="t-entry_append_right"></a>
## 定理: 成分は前置に不変 (T.entry_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`i, j \in \mathbb{N}`$ に対し

```math
(A \mathbin{+\!\!+} T)_{i,\,\lvert A\rvert + j} = T_{i,j}
```

### 証明

$`\lvert A\rvert \le \lvert A\rvert + j`$ であるから [T.getD_app_right](#t-getD_app_right) を
$`i := \lvert A\rvert + j`$ に適用して

```math
(A \mathbin{+\!\!+} T)\langle \lvert A\rvert + j\rangle
 = T\langle (\lvert A\rvert + j) - \lvert A\rvert\rangle = T\langle j\rangle
```

を得る。$`M_{i,j}`$ の定義（D.entry）により、$`i = 0`$ のとき両辺はそれぞれ
$`\pi_1\bigl((A \mathbin{+\!\!+} T)\langle \lvert A\rvert + j\rangle\bigr)`$ と $`\pi_1\bigl(T\langle j\rangle\bigr)`$、
$`i \ne 0`$ のとき $`\pi_2`$ をとったものである。いずれの場合も同じ対の同じ成分であるから等しい。∎

<a id="t-nextrel0_append_right"></a>
## 定理: 行 0 の親子関係は前置に不変 (T.nextrel0_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`j_0, j_1 \in \mathbb{N}`$ に対し

```math
\lvert A\rvert + j_0 \to^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1
\iff
j_0 \to^{T}_0 j_1
```

（$`\to^M_0`$ [D.nextrel0](Pss.md#d-nextrel0)）。

### 証明

$`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$ に注意し、
$`\to^M_0`$ の定義（D.nextrel0）の 5 条件を左右で対応させる。

**（$`\Rightarrow`$）** 左辺の 5 条件を (1)–(5) とする。

- (1) $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$ から $`j_0 \lt \lvert T\rvert`$。
- (2) $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$ から $`j_1 \lt \lvert T\rvert`$。
- (3) $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j_1`$ から $`j_0 \lt j_1`$。
- (4) [T.entry_append_right](#t-entry_append_right) より
  $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_0} = T_{0,j_0}`$ かつ
  $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = T_{0,j_1}`$ であるから、
  (4) は $`T_{0,j_0} \lt T_{0,j_1}`$ である。
- (5) $`j`$ を $`j_0 \lt j`$ かつ $`j \lt j_1`$ なる自然数とする。
  このとき $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j \lt \lvert A\rvert + j_1`$ であるから
  (5) を $`\lvert A\rvert + j`$ に適用でき、
  $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} \le (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j}`$ を得る。
  [T.entry_append_right](#t-entry_append_right) で両辺を書き換えて $`T_{0,j_1} \le T_{0,j}`$。

**（$`\Leftarrow`$）** 右辺の 5 条件を (1')–(5') とする。

- (1) (1') $`j_0 \lt \lvert T\rvert`$ に $`\lvert A\rvert`$ を足して
  $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$。
- (2) (2') $`j_1 \lt \lvert T\rvert`$ に $`\lvert A\rvert`$ を足して
  $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$。
- (3) (3') $`j_0 \lt j_1`$ から $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j_1`$。
- (4) [T.entry_append_right](#t-entry_append_right) で書き換えれば (4') そのものである。
- (5) $`j`$ を $`\lvert A\rvert + j_0 \lt j`$ かつ $`j \lt \lvert A\rvert + j_1`$ なる自然数とする。
  $`\lvert A\rvert \le \lvert A\rvert + j_0 \lt j`$ であるから $`j' := j - \lvert A\rvert`$ とおくと
  $`j = \lvert A\rvert + j'`$ であり、$`j_0 \lt j' \lt j_1`$ である。
  (5') を $`j'`$ に適用して $`T_{0,j_1} \le T_{0,j'}`$ を得、
  [T.entry_append_right](#t-entry_append_right) で書き換えれば
  $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} \le (A \mathbin{+\!\!+} T)_{0,j}`$。∎

<a id="t-rtg_nextrel0_lift"></a>
## 定理: 行 0 の鎖の持ち上げ (T.rtg_nextrel0_lift)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`j_0, c \in \mathbb{N}`$ とする。
$`j_0 \mathbin{(\to^{T}_0)^{*}} c`$（[D.le0](Pss.md#d-le0)）ならば

```math
\lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + c .
```

### 証明

鎖 $`j_0 \mathbin{(\to^{T}_0)^{*}} c`$ の構成に関する帰納法。$`A`$、$`T`$、$`j_0`$ は固定し、
帰納法の述語は

```math
\Phi(c) :\equiv \lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + c .
```

**基底段（長さ $`0`$ の鎖、$`c = j_0`$）。**
$`\lvert A\rvert + j_0`$ から $`\lvert A\rvert + j_0`$ への長さ $`0`$ の鎖が $`\Phi(j_0)`$ を与える。

**帰納段（長さ $`k+1`$ の鎖）。**
鎖は長さ $`k`$ の鎖 $`j_0 \mathbin{(\to^{T}_0)^{*}} b`$ と最後の 1 段 $`b \to^{T}_0 c`$ に分かれる。
帰納法の仮定は $`\Phi(b)`$、すなわち
$`\lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + b`$ である。
[T.nextrel0_append_right](#t-nextrel0_append_right) の（$`\Leftarrow`$）を
$`b \to^{T}_0 c`$ に適用して
$`\lvert A\rvert + b \to^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + c`$ を得る。
これを帰納法の仮定の鎖の末尾に継ぎ足せば $`\Phi(c)`$ を得る。∎

<a id="t-le0_append_right_of"></a>
## 定理: 行 0 の祖先関係の持ち上げ (T.le0_append_right_of)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`j_0, j_1 \in \mathbb{N}`$ とする。
$`j_0 \le^{T}_0 j_1`$ ならば
$`\lvert A\rvert + j_0 \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$。

### 証明

$`\le^M_0`$ の定義（D.le0）の 3 条件を示す。仮定の 3 条件を (1')(2')(3') とする。

- (1) $`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$ であり、(1') $`j_0 \lt \lvert T\rvert`$ から
  $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$。
- (2) $`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$ であり、(2') $`j_1 \lt \lvert T\rvert`$ から
  $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$。
- (3) (3') は $`j_0 \mathbin{(\to^{T}_0)^{*}} j_1`$ であり、
  [T.rtg_nextrel0_lift](#t-rtg_nextrel0_lift) を適用すれば
  $`\lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + j_1`$。∎

<a id="t-nextrel0_lt"></a>
## 定理: 行 0 の親子では添字が増える (T.nextrel0_lt)

### 定理

$`M \in \mathrm{PairSeq}`$、$`a, b \in \mathbb{N}`$ とする。$`a \to^{M}_0 b`$ ならば $`a \lt b`$。

### 証明

$`\to^M_0`$ の定義（D.nextrel0）の第 3 条件が $`a \lt b`$ そのものである。∎

<a id="t-rtg_nextrel0_unlift"></a>
## 定理: 行 0 の鎖の引き戻し (T.rtg_nextrel0_unlift)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`a, c \in \mathbb{N}`$ とする。
$`\lvert A\rvert + a \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} c`$ ならば、ある $`c'`$ が存在して

```math
c = \lvert A\rvert + c' \qquad\text{かつ}\qquad a \mathbin{(\to^{T}_0)^{*}} c' .
```

### 証明

鎖 $`\lvert A\rvert + a \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} c`$ の構成に関する帰納法。
$`A`$、$`T`$、$`a`$ は固定し、帰納法の述語は

```math
\Phi(c) :\equiv \exists c',\ c = \lvert A\rvert + c' \wedge a \mathbin{(\to^{T}_0)^{*}} c' .
```

**基底段（長さ $`0`$ の鎖、$`c = \lvert A\rvert + a`$）。**
$`c' := a`$ とおけば $`c = \lvert A\rvert + a`$ であり、$`a`$ から $`a`$ への長さ $`0`$ の鎖がある。

**帰納段（長さ $`k+1`$ の鎖）。**
鎖は長さ $`k`$ の鎖 $`\lvert A\rvert + a \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} d`$ と
最後の 1 段 $`d \to^{A \mathbin{+\!\!+} T}_0 e`$ に分かれる（$`c = e`$）。
帰納法の仮定は $`\Phi(d)`$ であり、$`d = \lvert A\rvert + d'`$ かつ
$`a \mathbin{(\to^{T}_0)^{*}} d'`$ なる $`d'`$ をとる。
[T.nextrel0_lt](#t-nextrel0_lt) を最後の 1 段に適用して $`d \lt e`$、すなわち
$`\lvert A\rvert + d' \lt e`$ を得る。とくに $`\lvert A\rvert \le e`$ であるから
$`e' := e - \lvert A\rvert`$ とおけば $`e = \lvert A\rvert + e'`$ である。
[T.nextrel0_append_right](#t-nextrel0_append_right) の（$`\Rightarrow`$）を
$`\lvert A\rvert + d' \to^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + e'`$ に適用して
$`d' \to^{T}_0 e'`$ を得る。これを帰納法の仮定の鎖の末尾に継ぎ足して
$`a \mathbin{(\to^{T}_0)^{*}} e'`$ を得る。$`c' := e'`$ が $`\Phi(e)`$ を与える。∎

<a id="t-le0_append_right"></a>
## 定理: 行 0 の祖先関係は前置に不変 (T.le0_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`j_0, j_1 \in \mathbb{N}`$ に対し

```math
\lvert A\rvert + j_0 \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1
\iff
j_0 \le^{T}_0 j_1 .
```

### 証明

**（$`\Rightarrow`$）** 左辺の 3 条件を (1)(2)(3) とする。
$`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$ であるから、
(1) から $`j_0 \lt \lvert T\rvert`$、(2) から $`j_1 \lt \lvert T\rvert`$ である。
(3) は $`\lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + j_1`$ であるから、
[T.rtg_nextrel0_unlift](#t-rtg_nextrel0_unlift) より $`c'`$ が存在して
$`\lvert A\rvert + j_1 = \lvert A\rvert + c'`$ かつ $`j_0 \mathbin{(\to^{T}_0)^{*}} c'`$ である。
第 1 の等式から $`j_1 = c'`$ であり、$`j_0 \mathbin{(\to^{T}_0)^{*}} j_1`$ を得る。
これで $`\le^M_0`$ の定義（D.le0）の 3 条件がそろった。

**（$`\Leftarrow`$）** [T.le0_append_right_of](#t-le0_append_right_of) そのものである。∎

<a id="t-nextrel0_no_cross"></a>
## 定理: 行 0 の親子は境界を越えない (T.nextrel0_no_cross)

### 定理

$`A, T \in \mathrm{PairSeq}`$ が $`T_{0,0} = 0`$ をみたすとする。
$`k, j \in \mathbb{N}`$ が

```math
k \lt \lvert A\rvert, \qquad
\lvert A\rvert \le j, \qquad
0 \lt (A \mathbin{+\!\!+} T)_{0,j}, \qquad
k \to^{A \mathbin{+\!\!+} T}_0 j
```

をみたすならば矛盾する。

### 証明

まず $`\lvert A\rvert \lt j`$ を示す。仮定 $`\lvert A\rvert \le j`$ より $`j = \lvert A\rvert`$ か
$`\lvert A\rvert \lt j`$ のいずれかである。$`j = \lvert A\rvert`$ とすると、
[T.entry_append_right](#t-entry_append_right) を $`i := 0`$、$`j := 0`$ に適用して

```math
(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert} = T_{0,0} = 0
```

であり、仮定 $`0 \lt (A \mathbin{+\!\!+} T)_{0,j}`$ に矛盾する。よって $`\lvert A\rvert \lt j`$ である。

次に $`k \to^{A \mathbin{+\!\!+} T}_0 j`$ の条件 (5)（D.nextrel0）を $`\lvert A\rvert`$ に適用する。
$`k \lt \lvert A\rvert`$ かつ $`\lvert A\rvert \lt j`$ であるから条件を満たし、

```math
(A \mathbin{+\!\!+} T)_{0,j} \le (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert} = 0
```

を得る。これは仮定 $`0 \lt (A \mathbin{+\!\!+} T)_{0,j}`$ に矛盾する。∎

<a id="t-nextrel0_no_pred_zero"></a>
## 定理: 行 0 の値が $`0`$ の列に親はない (T.nextrel0_no_pred_zero)

### 定理

$`M \in \mathrm{PairSeq}`$、$`a, b \in \mathbb{N}`$ とする。
$`M_{0,b} = 0`$ かつ $`a \to^{M}_0 b`$ ならば矛盾する。

### 証明

$`\to^M_0`$ の定義（D.nextrel0）の第 4 条件は $`M_{0,a} \lt M_{0,b}`$ である。
$`M_{0,b} = 0`$ を代入すると $`M_{0,a} \lt 0`$ となるが、自然数に $`0`$ より小さいものはない。∎

<a id="t-rtg_to_root"></a>
## 定理: 行 0 の値が $`0`$ の列で終わる鎖は自明 (T.rtg_to_root)

### 定理

$`M \in \mathrm{PairSeq}`$、$`k, b \in \mathbb{N}`$ とする。
$`M_{0,b} = 0`$ かつ $`k \mathbin{(\to^{M}_0)^{*}} b`$ ならば $`k = b`$。

### 証明

鎖の長さで場合分けする。

- **長さ $`0`$ のとき。** 鎖の両端は同一であり $`k = b`$ である。
- **長さが $`1`$ 以上のとき。** 鎖は $`k \mathbin{(\to^{M}_0)^{*}} c`$ と最後の 1 段
  $`c \to^{M}_0 b`$ に分かれる。$`M_{0,b} = 0`$ であるから
  [T.nextrel0_no_pred_zero](#t-nextrel0_no_pred_zero) により矛盾する。
  よってこの場合は起こらない。∎

<a id="t-le0_no_cross"></a>
## 定理: 行 0 の祖先関係は境界を越えない (T.le0_no_cross)

### 定理

$`A, T \in \mathrm{PairSeq}`$ が $`T_{0,0} = 0`$ をみたすとする。
$`k, j_1 \in \mathbb{N}`$ が

```math
k \lt \lvert A\rvert, \qquad
0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}, \qquad
k \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1
```

をみたすならば矛盾する。

### 証明

次の命題 (H) を示せば十分である。

```math
(H)\quad \forall e,\ \Bigl(k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} e
 \wedge \lvert A\rvert \le e \wedge 0 \lt (A \mathbin{+\!\!+} T)_{0,e}\Bigr)
 \to \lvert A\rvert \le k .
```

実際、仮定 $`k \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$ の第 3 条件（D.le0）は
$`k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + j_1`$ であり、
$`\lvert A\rvert \le \lvert A\rvert + j_1`$ と
$`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ が成り立つから、(H) を
$`e := \lvert A\rvert + j_1`$ に適用して $`\lvert A\rvert \le k`$ を得る。
これは仮定 $`k \lt \lvert A\rvert`$ に矛盾する。

(H) を鎖 $`k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} e`$ の構成に関する帰納法で示す。
$`A`$、$`T`$、$`k`$ は固定し、帰納法の述語は

```math
\Phi(e) :\equiv \bigl(\lvert A\rvert \le e \wedge 0 \lt (A \mathbin{+\!\!+} T)_{0,e}\bigr)
 \to \lvert A\rvert \le k .
```

**基底段（長さ $`0`$ の鎖、$`e = k`$）。**
前件の第 1 連言子が $`\lvert A\rvert \le k`$ そのものであるから結論が得られる。

**帰納段（長さ $`m+1`$ の鎖）。**
鎖は長さ $`m`$ の鎖 $`k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} c`$ と
最後の 1 段 $`c \to^{A \mathbin{+\!\!+} T}_0 d`$ に分かれる（$`e = d`$）。
帰納法の仮定は $`\Phi(c)`$ である。
前件 $`\lvert A\rvert \le d`$ と $`0 \lt (A \mathbin{+\!\!+} T)_{0,d}`$ を仮定する。

まず $`\lvert A\rvert \le c`$ を示す。$`c \lt \lvert A\rvert`$ とすると、
[T.nextrel0_no_cross](#t-nextrel0_no_cross) を $`k := c`$、$`j := d`$ として適用でき
（4 つの仮定はそれぞれ $`c \lt \lvert A\rvert`$、$`\lvert A\rvert \le d`$、
$`0 \lt (A \mathbin{+\!\!+} T)_{0,d}`$、$`c \to^{A \mathbin{+\!\!+} T}_0 d`$ である）、矛盾する。

次に $`(A \mathbin{+\!\!+} T)_{0,c}`$ で場合分けする。

- $`0 \lt (A \mathbin{+\!\!+} T)_{0,c}`$ のとき。
  帰納法の仮定 $`\Phi(c)`$ に $`\lvert A\rvert \le c`$ とこの不等式を与えて
  $`\lvert A\rvert \le k`$ を得る。
- $`(A \mathbin{+\!\!+} T)_{0,c} = 0`$ のとき。
  [T.rtg_to_root](#t-rtg_to_root) を $`M := A \mathbin{+\!\!+} T`$、$`b := c`$ とし、
  鎖 $`k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} c`$ に適用して $`k = c`$ を得る。
  すでに示した $`\lvert A\rvert \le c`$ と合わせて $`\lvert A\rvert \le k`$。∎

<a id="t-nextrel1_append_right"></a>
## 定理: 行 1 の親子関係は前置に不変 (T.nextrel1_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`j_0, j_1 \in \mathbb{N}`$ に対し

```math
\lvert A\rvert + j_0 \to^{A \mathbin{+\!\!+} T}_1 \lvert A\rvert + j_1
\iff
j_0 \to^{T}_1 j_1
```

（$`\to^M_1`$ [D.nextrel1](Pss.md#d-nextrel1)）。

### 証明

$`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$ に注意し、
$`\to^M_1`$ の定義（D.nextrel1）の 6 条件を左右で対応させる。

**（$`\Rightarrow`$）** 左辺の 6 条件を (1)–(6) とする。

- (1) $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$ から $`j_0 \lt \lvert T\rvert`$。
- (2) $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$ から $`j_1 \lt \lvert T\rvert`$。
- (3) $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j_1`$ から $`j_0 \lt j_1`$。
- (4) [T.entry_append_right](#t-entry_append_right) より
  $`(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_0} = T_{1,j_0}`$ かつ
  $`(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} = T_{1,j_1}`$ であるから、
  (4) は $`T_{1,j_0} \lt T_{1,j_1}`$ である。
- (5) [T.le0_append_right](#t-le0_append_right) の（$`\Rightarrow`$）を (5) に適用して
  $`j_0 \le^{T}_0 j_1`$。
- (6) $`j`$ を $`j_0 \lt j`$ かつ $`j \le^{T}_0 j_1`$ なる自然数とする。
  $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j`$ であり、
  [T.le0_append_right](#t-le0_append_right) の（$`\Leftarrow`$）より
  $`\lvert A\rvert + j \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$ である。
  よって (6) を $`\lvert A\rvert + j`$ に適用でき、
  $`(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} \le (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j}`$、
  すなわち [T.entry_append_right](#t-entry_append_right) による書き換えで
  $`T_{1,j_1} \le T_{1,j}`$ を得る。

**（$`\Leftarrow`$）** 右辺の 6 条件を (1')–(6') とする。

- (1) (1') $`j_0 \lt \lvert T\rvert`$ から $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$。
- (2) (2') $`j_1 \lt \lvert T\rvert`$ に $`\lvert A\rvert`$ を足して
  $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$。
- (3) (3') $`j_0 \lt j_1`$ から $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j_1`$。
- (4) [T.entry_append_right](#t-entry_append_right) で書き換えれば (4') そのものである。
- (5) [T.le0_append_right](#t-le0_append_right) の（$`\Leftarrow`$）を (5') に適用する。
- (6) $`j`$ を $`\lvert A\rvert + j_0 \lt j`$ かつ
  $`j \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$ なる自然数とする。
  $`\lvert A\rvert \le \lvert A\rvert + j_0 \lt j`$ であるから $`j' := j - \lvert A\rvert`$ とおくと
  $`j = \lvert A\rvert + j'`$ であり $`j_0 \lt j'`$ である。
  [T.le0_append_right](#t-le0_append_right) の（$`\Rightarrow`$）より $`j' \le^{T}_0 j_1`$ であるから、
  (6') を $`j'`$ に適用して $`T_{1,j_1} \le T_{1,j'}`$ を得る。
  [T.entry_append_right](#t-entry_append_right) で書き換えれば
  $`(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} \le (A \mathbin{+\!\!+} T)_{1,j}`$。∎

<a id="t-nextR_append_right"></a>
## 定理: 行つき親子関係は前置に不変 (T.nextR_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`i, j_0, j_1 \in \mathbb{N}`$ に対し

```math
\lvert A\rvert + j_0 \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1
\iff
j_0 \to^{T}_i j_1
```

（$`\to^M_i`$ [D.nextR](Pss.md#d-nextR)）。

### 証明

$`\to^M_i`$ の定義（D.nextR）の場合分けによる。

- $`i = 0`$ のとき。両辺はそれぞれ
  $`\lvert A\rvert + j_0 \to^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$ と $`j_0 \to^{T}_0 j_1`$ であり、
  [T.nextrel0_append_right](#t-nextrel0_append_right) が主張そのものである。
- $`i \ne 0`$ のとき。両辺はそれぞれ
  $`\lvert A\rvert + j_0 \to^{A \mathbin{+\!\!+} T}_1 \lvert A\rvert + j_1`$ と $`j_0 \to^{T}_1 j_1`$ であり、
  [T.nextrel1_append_right](#t-nextrel1_append_right) が主張そのものである。∎

<a id="t-idx1_append_right"></a>
## 定理: 探索行は前置に不変 (T.idx1_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`j \in \mathbb{N}`$ に対し

```math
\mathrm{idx}_1(A \mathbin{+\!\!+} T,\ \lvert A\rvert + j) = \mathrm{idx}_1(T, j)
```

（$`\mathrm{idx}_1`$ [D.idx1](Pss.md#d-idx1)）。

### 証明

$`\mathrm{idx}_1`$ の定義（D.idx1）は $`M_{1,j_1}`$ の正負のみによる場合分けである。
[T.entry_append_right](#t-entry_append_right) より
$`(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j} = T_{1,j}`$ であるから、
条件 $`0 \lt (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j}`$ と $`0 \lt T_{1,j}`$ は同一の命題であり、
どちらの場合が選ばれるかも一致する。∎

<a id="t-nextR_le0"></a>
## 定理: 親子関係は祖先関係を導く (T.nextR_le0)

### 定理

$`M \in \mathrm{PairSeq}`$、$`i, k, b \in \mathbb{N}`$ とする。
$`k \to^{M}_i b`$ ならば $`k \le^{M}_0 b`$。

### 証明

$`\to^M_i`$ の定義（D.nextR）の場合分けによる。

- $`i = 0`$ のとき。$`k \to^{M}_0 b`$ である。$`\le^M_0`$ の定義（D.le0）の 3 条件のうち、
  (1) $`k \lt \lvert M\rvert`$ と (2) $`b \lt \lvert M\rvert`$ は $`\to^M_0`$ の定義（D.nextrel0）の
  第 1・第 2 条件そのものであり、(3) は $`k \to^{M}_0 b`$ を 1 段だけもつ鎖である。
- $`i \ne 0`$ のとき。$`k \to^{M}_1 b`$ であり、$`\to^M_1`$ の定義（D.nextrel1）の
  第 5 条件が $`k \le^{M}_0 b`$ そのものである。∎

<a id="t-nextR_src_in_T"></a>
## 定理: 親は後半に属する (T.nextR_src_in_T)

### 定理

$`A, T \in \mathrm{PairSeq}`$ が $`T_{0,0} = 0`$ をみたすとする。
$`i, k, j_1 \in \mathbb{N}`$ が $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ かつ
$`k \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$ をみたすならば $`\lvert A\rvert \le k`$。

### 証明

$`\lvert A\rvert \le k`$ を否定して $`k \lt \lvert A\rvert`$ と仮定する。
[T.nextR_le0](#t-nextR_le0) より $`k \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$ である。
[T.le0_no_cross](#t-le0_no_cross) の 3 つの仮定
$`k \lt \lvert A\rvert`$、$`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$、
$`k \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$ がそろうから矛盾する。∎

<a id="t-hasParent_append_right"></a>
## 定理: 親の存在は前置に不変 (T.hasParent_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$ が $`T_{0,0} = 0`$ をみたし、
$`i, j_1 \in \mathbb{N}`$ が $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ をみたすとする。このとき

```math
\mathrm{hasParent}(A \mathbin{+\!\!+} T,\ i,\ \lvert A\rvert + j_1)
\iff
\mathrm{hasParent}(T,\ i,\ j_1)
```

（$`\mathrm{hasParent}`$ [D.hasParent](Pss.md#d-hasParent)）。

### 証明

$`\mathrm{hasParent}`$ の定義（D.hasParent）は、条件をみたす添字の存在と一意性である。

**（$`\Rightarrow`$）** $`j_0`$ を $`j_0 \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$ をみたす一意の添字とする。
[T.nextR_src_in_T](#t-nextR_src_in_T) より $`\lvert A\rvert \le j_0`$ であるから、
$`j_0' := j_0 - \lvert A\rvert`$ とおけば $`j_0 = \lvert A\rvert + j_0'`$ である。
[T.nextR_append_right](#t-nextR_append_right) の（$`\Rightarrow`$）より
$`j_0' \to^{T}_i j_1`$ を得る（存在）。
一意性を示す。$`y`$ が $`y \to^{T}_i j_1`$ をみたすとすると、
[T.nextR_append_right](#t-nextR_append_right) の（$`\Leftarrow`$）より
$`\lvert A\rvert + y \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$ であるから、
$`j_0`$ の一意性により $`\lvert A\rvert + y = \lvert A\rvert + j_0'`$、すなわち $`y = j_0'`$ である。

**（$`\Leftarrow`$）** $`j_0'`$ を $`j_0' \to^{T}_i j_1`$ をみたす一意の添字とする。
[T.nextR_append_right](#t-nextR_append_right) の（$`\Leftarrow`$）より
$`\lvert A\rvert + j_0' \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$ である（存在）。
一意性を示す。$`y`$ が $`y \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$ をみたすとすると、
[T.nextR_src_in_T](#t-nextR_src_in_T) より $`\lvert A\rvert \le y`$ であるから
$`y' := y - \lvert A\rvert`$ とおけば $`y = \lvert A\rvert + y'`$ である。
[T.nextR_append_right](#t-nextR_append_right) の（$`\Rightarrow`$）より $`y' \to^{T}_i j_1`$ であり、
$`j_0'`$ の一意性から $`y' = j_0'`$、すなわち $`y = \lvert A\rvert + j_0'`$ である。∎

<a id="t-parent_append_right"></a>
## 定理: 親は前置の長さだけずれる (T.parent_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$ が $`T_{0,0} = 0`$ をみたし、
$`i, j_1 \in \mathbb{N}`$ が $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ と
$`\mathrm{hasParent}(T, i, j_1)`$ をみたすとする。このとき

```math
\mathrm{par}^{A \mathbin{+\!\!+} T}_i(\lvert A\rvert + j_1) = \lvert A\rvert + \mathrm{par}^{T}_i(j_1)
```

（$`\mathrm{par}^M_i`$ [D.parent](Pss.md#d-parent)）。

### 証明

[T.hasParent_append_right](#t-hasParent_append_right) の（$`\Leftarrow`$）より
$`\mathrm{hasParent}(A \mathbin{+\!\!+} T, i, \lvert A\rvert + j_1)`$ が成り立つ。
すなわち $`x \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$ をみたす $`x`$ は一意である。
次の 2 つがともにこの条件をみたす。

- $`x := \mathrm{par}^{A \mathbin{+\!\!+} T}_i(\lvert A\rvert + j_1)`$。
  [T.parent_nextR](Decrease.md#t-parent_nextR) を
  $`\mathrm{hasParent}(A \mathbin{+\!\!+} T, i, \lvert A\rvert + j_1)`$ に適用すればよい。
- $`x := \lvert A\rvert + \mathrm{par}^{T}_i(j_1)`$。
  [T.parent_nextR](Decrease.md#t-parent_nextR) を $`\mathrm{hasParent}(T, i, j_1)`$ に適用すると
  $`\mathrm{par}^{T}_i(j_1) \to^{T}_i j_1`$ であり、
  [T.nextR_append_right](#t-nextR_append_right) の（$`\Leftarrow`$）を適用すればよい。

一意性より両者は等しい。∎

<a id="t-take_append_right"></a>
## 定理: 前部分列は連結を分ける (T.take_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`j \in \mathbb{N}`$ に対し

```math
\mathrm{take}_{\lvert A\rvert + j}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{take}_{j}\,T .
```

ここで $`\mathrm{take}_m M`$ は $`M`$ の先頭 $`m`$ 要素からなる列であり、
$`\lvert M\rvert \le m`$ のときは $`M`$ 自身である（長さは $`\min(m, \lvert M\rvert)`$）。

### 証明

連結列の前部分列は

```math
\mathrm{take}_{p}\,(A \mathbin{+\!\!+} T)
 = \mathrm{take}_{p}\,A \mathbin{+\!\!+} \mathrm{take}_{p - \lvert A\rvert}\,T
```

をみたす。$`p := \lvert A\rvert + j`$ とおくと $`\lvert A\rvert \le p`$ であるから
$`\mathrm{take}_{p}\,A = A`$ であり、また $`p - \lvert A\rvert = j`$ である。∎

<a id="t-copyblock_append"></a>
## 定理: コピーブロックは前置に不変 (T.copyblock_append)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`a, m, k, d_0, d_1 \in \mathbb{N}`$ に対し

```math
\Bigl(\bigl((A \mathbin{+\!\!+} T)_{0,j} + k\,d_0,\ (A \mathbin{+\!\!+} T)_{1,j} + k\,d_1\bigr)\Bigr)_{j = \lvert A\rvert + a}^{\lvert A\rvert + a + m - 1}
=
\Bigl(\bigl(T_{0,j} + k\,d_0,\ T_{1,j} + k\,d_1\bigr)\Bigr)_{j = a}^{a + m - 1} .
```

ここで $`\bigl(f(j)\bigr)_{j = b}^{b + m - 1}`$ は添字 $`j`$ を $`b`$ から 1 ずつ増やして走らせた
長さ $`m`$ の列であり、$`m = 0`$ のときは空列である。

### 証明

両辺はともに長さ $`m`$ の列であるから、$`p \lt m`$ なる各 $`p`$ について第 $`p`$ 要素が
一致することを示せばよい。左辺の第 $`p`$ 要素は $`j = \lvert A\rvert + a + p`$ に対する

```math
\bigl((A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + a + p} + k\,d_0,\ (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + a + p} + k\,d_1\bigr)
```

であり、右辺の第 $`p`$ 要素は $`j = a + p`$ に対する
$`\bigl(T_{0,a+p} + k\,d_0,\ T_{1,a+p} + k\,d_1\bigr)`$ である。
$`\lvert A\rvert + a + p = \lvert A\rvert + (a + p)`$ であるから、
[T.entry_append_right](#t-entry_append_right) を $`i := 0`$、$`j := a + p`$ および
$`i := 1`$、$`j := a + p`$ に適用して

```math
(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + a + p} = T_{0,a+p},
\qquad
(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + a + p} = T_{1,a+p}
```

を得る。よって両辺の第 $`p`$ 要素は一致する。∎

<a id="t-Pred_append_right"></a>
## 定理: 前者は連結を分ける (T.Pred_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$ が $`2 \le \lvert T\rvert`$ をみたすならば

```math
\mathrm{Pred}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{Pred}\,T
```

（$`\mathrm{Pred}`$ [D.Pred](Pss.md#d-Pred)）。

### 証明

$`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert \ge \lvert T\rvert \ge 2`$ であるから
$`\neg\bigl(\lvert A \mathbin{+\!\!+} T\rvert \le 1\bigr)`$ であり、$`\mathrm{Pred}`$ の定義（D.Pred）の
第 2 の場合により $`\mathrm{Pred}\,(A \mathbin{+\!\!+} T) = \mathrm{dropLast}\,(A \mathbin{+\!\!+} T)`$ である。
また仮定 $`2 \le \lvert T\rvert`$ から $`\neg\bigl(\lvert T\rvert \le 1\bigr)`$ であり、
$`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合により
$`\mathrm{Pred}\,T = \mathrm{dropLast}\,T`$ である。

$`2 \le \lvert T\rvert`$ より $`T \ne ()`$ であるから、$`A \mathbin{+\!\!+} T`$ の末尾要素は $`T`$ の末尾要素であり、
それを落とした列は $`A`$ に $`\mathrm{dropLast}\,T`$ を連結したものである。すなわち

```math
\mathrm{dropLast}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{dropLast}\,T . \qquad \blacksquare
```

<a id="t-no_hasParent_of_row0_zero"></a>
## 定理: 行 0 の値が $`0`$ の列は親をもたない (T.no_hasParent_of_row0_zero)

### 定理

$`M \in \mathrm{PairSeq}`$、$`i, j_1 \in \mathbb{N}`$ とする。
$`M_{0,j_1} = 0`$ かつ $`\mathrm{hasParent}(M, i, j_1)`$ ならば矛盾する。

### 証明

$`\mathrm{hasParent}`$ の定義（D.hasParent）より $`j_0 \to^{M}_i j_1`$ をみたす $`j_0`$ が存在する。
[T.nextR_le0](#t-nextR_le0) より $`j_0 \le^{M}_0 j_1`$ であり、その第 3 条件（D.le0）は
$`j_0 \mathbin{(\to^{M}_0)^{*}} j_1`$ である。
$`M_{0,j_1} = 0`$ であるから [T.rtg_to_root](#t-rtg_to_root) を適用して $`j_0 = j_1`$ を得る。
一方 [T.nextR_index_lt](Decrease.md#t-nextR_index_lt) より $`j_0 \lt j_1`$ であり、矛盾する。∎
