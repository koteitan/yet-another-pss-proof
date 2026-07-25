[← README](README.md)

<a id="t-stps_len_pos"></a>
## 定理: 標準形は空でない (T.stps_len_pos)

### 定理

[$`M \in \mathrm{PairSeq}`$](Pss.md#d-PairSeq) が [$`M \in \mathrm{ST\_PS}`$](Pss.md#d-ST_PS)
をみたすならば $`0 \lt \lvert M\rvert`$。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M) :\equiv 0 \lt \lvert M\rvert .
```

**基底段（規則 diag）$`M = \Delta_0^v`$。**
[T.diagSeq_cons](Cnf.md#t-diagSeq_cons) を $`u := 0`$、$`v := v`$ とし、
仮定 $`0 \le v`$ のもとで適用すると
[$`\Delta_0^v = (0,0) :: \Delta_1^v`$](Pss.md#d-diagSeq) である。
よって $`\lvert \Delta_0^v\rvert = 1 + \lvert \Delta_1^v\rvert`$ であり $`0 \lt \lvert \Delta_0^v\rvert`$。

**帰納段（規則 oper）$`M = N[n]`$（$`N \in \mathrm{ST\_PS}`$、$`1 \le n`$）。**
帰納法の仮定は $`\Phi(N)`$、すなわち $`0 \lt \lvert N\rvert`$ である。
$`\lvert N\rvert`$ で場合分けする。

**(a) $`1 \lt \lvert N\rvert`$ のとき。**
[T.oper_eq_dropLast_append](Cnf.md#t-oper_eq_dropLast_append) より、ある $`R \in \mathrm{PairSeq}`$ が存在して
[$`N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R`$](Pss.md#d-oper) である。ここで $`\mathrm{dropLast}\,N`$ は
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

（[$`M\langle j\rangle`$](Pss.md#d-entry) は範囲外で $`(0,0)`$ を返す読み出しである）。

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

（[$`M_{i,j}`$](Pss.md#d-entry)）。

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

（[$`\to^M_0`$](Pss.md#d-nextrel0)）。

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
- (2) (2') から同様に $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$。
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
[$`j_0 \mathbin{(\to^{T}_0)^{*}} c`$](Pss.md#d-le0) ならば

```math
\lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + c .
```

### 証明

鎖 $`j_0 \mathbin{(\to^{T}_0)^{*}} c`$ の長さに関する帰納法。$`A`$、$`T`$、$`j_0`$ は固定し、
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
[$`j_0 \le^{T}_0 j_1`$](Pss.md#d-le0) ならば
$`\lvert A\rvert + j_0 \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$。

### 証明

$`\le^M_0`$ の定義（D.le0）の 3 条件を示す。仮定の 3 条件を (1')(2')(3') とする。

- (1) $`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$ であり、(1') $`j_0 \lt \lvert T\rvert`$ から
  $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$。
- (2) 同様に (2') から $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$。
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

鎖 $`\lvert A\rvert + a \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} c`$ の長さに関する帰納法。
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

(H) を鎖 $`k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} e`$ の長さに関する帰納法で示す。
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

（[$`\to^M_1`$](Pss.md#d-nextrel1)）。

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
- (2) (2') から同様。
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

（[$`\to^M_i`$](Pss.md#d-nextR)）。

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

（[$`\mathrm{idx}_1`$](Pss.md#d-idx1)）。

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

（[$`\mathrm{hasParent}`$](Pss.md#d-hasParent)）。

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

（[$`\mathrm{par}^M_i`$](Pss.md#d-parent)）。

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

（[$`\mathrm{Pred}`$](Pss.md#d-Pred)）。

### 証明

$`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert \ge \lvert T\rvert \ge 2`$ であるから
$`\neg\bigl(\lvert A \mathbin{+\!\!+} T\rvert \le 1\bigr)`$ であり、$`\mathrm{Pred}`$ の定義（D.Pred）の
第 2 の場合により $`\mathrm{Pred}\,(A \mathbin{+\!\!+} T) = \mathrm{dropLast}\,(A \mathbin{+\!\!+} T)`$ である。
同様に $`\neg\bigl(\lvert T\rvert \le 1\bigr)`$ であるから
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

<a id="t-oper_append_right"></a>
## 定理: 展開は前置と可換 (T.oper_append_right)

### 定理

$`A, T \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とし、$`2 \le \lvert T\rvert`$ かつ $`T_{0,0} = 0`$ とする。
このとき

```math
(A \mathbin{+\!\!+} T)[n] = A \mathbin{+\!\!+} T[n] .
```

### 証明

$`j_1 := \lvert T\rvert - 1`$ とおく。$`2 \le \lvert T\rvert`$ より $`1 \le j_1`$、とくに $`j_1 \ne 0`$ である。
また

```math
\lvert A \mathbin{+\!\!+} T\rvert - 1 = (\lvert A\rvert + \lvert T\rvert) - 1 = \lvert A\rvert + j_1
```

であるから、$`A \mathbin{+\!\!+} T`$ に対する $`M[n]`$ の定義（D.oper）の末尾添字は $`\lvert A\rvert + j_1`$ である。
以下、D.oper の 4 分岐を左右で対応させる。

**分岐 (a)。** 条件は左辺では $`\lvert A\rvert + j_1 = 0`$、右辺では $`j_1 = 0`$ であり、
$`1 \le j_1`$ よりいずれも偽である。よって両辺とも分岐 (a) を選ばない。

**分岐 (b)。** 条件は左辺では
$`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = 0 \wedge (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} = 0`$、
右辺では $`T_{0,j_1} = 0 \wedge T_{1,j_1} = 0`$ である。
[T.entry_append_right](#t-entry_append_right) より

```math
(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = T_{0,j_1},
\qquad
(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} = T_{1,j_1}
```

であるから、2 つの条件は同一の命題である。これが成り立つ場合、両辺はそれぞれ
$`\mathrm{Pred}\,(A \mathbin{+\!\!+} T)`$ と $`\mathrm{Pred}\,T`$ であり、
[T.Pred_append_right](#t-Pred_append_right) により
$`\mathrm{Pred}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{Pred}\,T`$ である。
以下、この条件は成り立たないとする。

**探索行。** [T.idx1_append_right](#t-idx1_append_right) より
$`\mathrm{idx}_1(A \mathbin{+\!\!+} T, \lvert A\rvert + j_1) = \mathrm{idx}_1(T, j_1)`$ であるから、
両辺の $`i_1`$ は共通の値である。これを $`i_1 := \mathrm{idx}_1(T, j_1)`$ と書く。
$`\mathrm{hasParent}(T, i_1, j_1)`$ が成り立つかどうかで場合分けする。

**(A) $`\mathrm{hasParent}(T, i_1, j_1)`$ が成り立つとき。**
まず $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ を示す。
上の書き換えによりこれは $`0 \lt T_{0,j_1}`$ と同値である。
$`T_{0,j_1} = 0`$ とすると [T.no_hasParent_of_row0_zero](#t-no_hasParent_of_row0_zero) を
$`M := T`$、$`i := i_1`$、$`j_1 := j_1`$ に適用して矛盾する。
よって [T.hasParent_append_right](#t-hasParent_append_right) の（$`\Leftarrow`$）が適用でき、
$`\mathrm{hasParent}(A \mathbin{+\!\!+} T, i_1, \lvert A\rvert + j_1)`$ が成り立つ。
したがって分岐 (c) の条件は両辺で偽であり、両辺とも分岐 (d) を選ぶ。

分岐 (d) の各構成要素を比べる。$`j_0 := \mathrm{par}^{T}_{i_1}(j_1)`$ とおく。

**親。** [T.parent_append_right](#t-parent_append_right) より
$`\mathrm{par}^{A \mathbin{+\!\!+} T}_{i_1}(\lvert A\rvert + j_1) = \lvert A\rvert + j_0`$ である。

**増分。** 左辺の $`d_0`$ と $`d_1`$ は D.oper の式により

```math
d_0 = \begin{cases}
(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} - (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_0} & (0 \lt i_1) \cr
0 & (i_1 = 0)
\end{cases}
\qquad
d_1 = \begin{cases}
(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} - (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_0} & (1 \lt i_1) \cr
0 & (i_1 \le 1)
\end{cases}
```

である。[T.entry_append_right](#t-entry_append_right) を 4 つの成分に適用すると、
これらはそれぞれ $`0 \lt i_1`$ のとき $`T_{0,j_1} - T_{0,j_0}`$、$`1 \lt i_1`$ のとき
$`T_{1,j_1} - T_{1,j_0}`$ に等しく、条件の部分も共通であるから、右辺の $`d_0`$、$`d_1`$ と一致する。

**前部分列。** [T.take_append_right](#t-take_append_right) より
$`\mathrm{take}_{\lvert A\rvert + j_0}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{take}_{j_0}\,T`$ である。

**コピーブロック。** 左辺の第 $`k`$ ブロックは、添字 $`j`$ を $`\lvert A\rvert + j_0`$ から
$`(\lvert A\rvert + j_1) - 1`$ まで走らせた長さ
$`(\lvert A\rvert + j_1) - (\lvert A\rvert + j_0) = j_1 - j_0`$ の列

```math
\Bigl(\bigl((A \mathbin{+\!\!+} T)_{0,j} + k\,d_0,\ (A \mathbin{+\!\!+} T)_{1,j} + k\,d_1\bigr)\Bigr)_{j = \lvert A\rvert + j_0}^{\lvert A\rvert + j_1 - 1}
```

である。[T.copyblock_append](#t-copyblock_append) を $`a := j_0`$、$`m := j_1 - j_0`$ に適用すると、
これは右辺の第 $`k`$ ブロック

```math
\Bigl(\bigl(T_{0,j} + k\,d_0,\ T_{1,j} + k\,d_1\bigr)\Bigr)_{j = j_0}^{j_1 - 1}
```

に等しい。これが $`k = 0, 1, \dots, n-1`$ のすべてについて成り立つ。

以上より、共通のブロックを $`B_0, \dots, B_{n-1}`$ と書くと

```math
(A \mathbin{+\!\!+} T)[n]
 = \bigl(A \mathbin{+\!\!+} \mathrm{take}_{j_0}\,T\bigr) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1}
 = A \mathbin{+\!\!+} \bigl(\mathrm{take}_{j_0}\,T \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1}\bigr)
 = A \mathbin{+\!\!+} T[n]
```

である（中央の等号は連結の結合律）。

**(B) $`\neg\,\mathrm{hasParent}(T, i_1, j_1)`$ のとき。**
$`\neg\,\mathrm{hasParent}(A \mathbin{+\!\!+} T, i_1, \lvert A\rvert + j_1)`$ を示す。
$`\mathrm{hasParent}(A \mathbin{+\!\!+} T, i_1, \lvert A\rvert + j_1)`$ が成り立つと仮定して
$`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ で場合分けする。

- $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ のとき。
  [T.hasParent_append_right](#t-hasParent_append_right) の（$`\Rightarrow`$）より
  $`\mathrm{hasParent}(T, i_1, j_1)`$ となり、この場合の仮定に矛盾する。
- $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = 0`$ のとき。
  [T.no_hasParent_of_row0_zero](#t-no_hasParent_of_row0_zero) を
  $`M := A \mathbin{+\!\!+} T`$、$`j_1 := \lvert A\rvert + j_1`$ に適用して矛盾する。

よって両辺とも分岐 (c) を選び、それぞれ $`\mathrm{Pred}\,(A \mathbin{+\!\!+} T)`$ と $`\mathrm{Pred}\,T`$ である。
[T.Pred_append_right](#t-Pred_append_right) により両者は $`A`$ の連結で結ばれる。∎

<a id="t-map_range_entry_eq_take"></a>
## 定理: 成分の列挙は前部分列 (T.map_range_entry_eq_take)

### 定理

$`N \in \mathrm{PairSeq}`$、$`j_1 \in \mathbb{N}`$ とし $`j_1 \le \lvert N\rvert`$ とする。このとき

```math
\bigl((N_{0,j},\ N_{1,j})\bigr)_{j = 0}^{j_1 - 1} = \mathrm{take}_{j_1}\,N .
```

### 証明

両辺の長さと各要素を比べる。

**長さ。** 左辺は長さ $`j_1`$ の列である。右辺の長さは
$`\min(j_1, \lvert N\rvert)`$ であり、仮定 $`j_1 \le \lvert N\rvert`$ より $`j_1`$ である。

**第 $`i`$ 要素（$`i \lt j_1`$）。**
$`i \lt j_1 \le \lvert N\rvert`$ であるから、$`M\langle j\rangle`$ の定義（D.entry）の第 1 の場合により
$`N\langle i\rangle = N_i`$ である。よって左辺の第 $`i`$ 要素は

```math
(N_{0,i},\ N_{1,i}) = \bigl(\pi_1(N_i),\ \pi_2(N_i)\bigr) = N_i
```

である。右辺の第 $`i`$ 要素は、$`i \lt j_1`$ より $`N`$ の第 $`i`$ 要素 $`N_i`$ である。
よって両辺の第 $`i`$ 要素は一致する。∎

<a id="t-oper_headD"></a>
## 定理: 展開は先頭を変えない (T.oper_headD)

### 定理

$`N \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とし、$`1 \lt \lvert N\rvert`$ かつ $`1 \le n`$ とする。
このとき $`\mathrm{head}\,(N[n]) = \mathrm{head}\,N`$。

### 証明

[T.oper_eq_dropLast_append](Cnf.md#t-oper_eq_dropLast_append) より、ある $`R \in \mathrm{PairSeq}`$ について
$`N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R`$ である。
$`1 \lt \lvert N\rvert`$ より $`N`$ は少なくとも 2 要素をもち $`N = a :: b :: u`$ と書ける。
このとき

```math
\mathrm{dropLast}\,(a :: b :: u) = a :: \mathrm{dropLast}\,(b :: u)
```

であるから

```math
N[n] = a :: \bigl(\mathrm{dropLast}\,(b :: u) \mathbin{+\!\!+} R\bigr)
```

であり、$`\mathrm{head}\,(N[n]) = a = \mathrm{head}\,N`$ である。∎

<a id="t-translate_nil"></a>
## 定理: 空列の翻訳 (T.translate_nil)

### 定理

[$`\mathrm{tr}\,()`$](Term.md#d-translate) は [$`\mathsf{Z}`$](Term.md#d-Three) に等しい。

### 証明

$`\mathrm{tr}`$ の定義（D.translate）の第 1 式そのものである。∎

<a id="d-maxr1"></a>
## 定義: 行 1 の最大値 (D.maxr1)

$`S \in \mathrm{PairSeq}`$ に対し $`\mathrm{maxr}_1(S) \in \mathbb{N}`$ を、列の構成子に関する再帰で定める。

```math
\mathrm{maxr}_1(()) := 0,
\qquad
\mathrm{maxr}_1(c :: S) := \max\bigl(c_2,\ \mathrm{maxr}_1(S)\bigr) .
```

ここで $`c = (c_1, c_2)`$ である。再帰呼び出しの引数 $`S`$ は $`c :: S`$ の真の後部分列であり、
長さが真に小さいから、この定義は整合的である。

<a id="t-maxr1_cons"></a>
## 定理: 行 1 の最大値の再帰式 (T.maxr1_cons)

### 定理

$`c \in \mathbb{N} \times \mathbb{N}`$、$`S \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{maxr}_1(c :: S) = \max\bigl(c_2,\ \mathrm{maxr}_1(S)\bigr) .
```

### 証明

$`\mathrm{maxr}_1`$ の定義（D.maxr1）の第 2 式そのものであり、両辺は定義により同一の値である。∎

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

<a id="t-r1ok_ST_PS"></a>
## 定理: 標準形は $`\mathrm{r1ok}`$ をみたす (T.r1ok_ST_PS)

### 定理

$`M \in \mathrm{ST\_PS}`$ ならば $`\mathrm{r1ok}(M)`$。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M) :\equiv \mathrm{r1ok}(M).
```

- **基底段**（規則 (diag)）：$`M = \Delta_0^v`$ である。
  [T.r1ok_diagSeq](#t-r1ok_diagSeq) が $`\Phi(\Delta_0^v)`$ そのものである。

- **帰納段**（規則 (oper)）：$`N \in \mathrm{ST\_PS}`$、$`1 \le n`$ とする。帰納法の仮定は
  $`\Phi(N)`$、すなわち $`\mathrm{r1ok}(N)`$ であり、示すべきは $`\mathrm{r1ok}(N[n])`$ である。
  [T.blockok_ST_PS](Seqlex.md#t-blockok_ST_PS) を $`N \in \mathrm{ST\_PS}`$ に適用して
  $`\mathrm{blockok}(0, N)`$ を得る。$`\mathrm{blockok}`$ の定義（D.blockok）は 3 つの連言で
  あり、その第 3 連言子は $`\mathrm{steps1}(N)`$ である。
  [T.r1ok_oper](#t-r1ok_oper) を $`1 \le n`$、$`\mathrm{r1ok}(N)`$、$`\mathrm{steps1}(N)`$ に
  適用すれば $`\mathrm{r1ok}(N[n])`$ を得る。∎

<a id="t-nextrel0_bound"></a>
## 定理: 行 0 の親子の行き先は範囲内 (T.nextrel0_bound)

### 定理

$`a \to^M_0 b`$ ならば $`b \lt \lvert M\rvert`$。

### 証明

$`\to^M_0`$ の定義（D.nextrel0）の第 2 条件そのものである。∎

<a id="t-le0_le"></a>
## 定理: 行 0 の祖先関係は添字の大小を含む (T.le0_le)

### 定理

$`a \le^M_0 b`$ ならば $`a \le b`$。

### 証明

$`\le^M_0`$ の定義（D.le0）の第 3 条件により $`a \mathbin{(\to^M_0)^{*}} b`$ である。
この反射推移閉包の構成に関する帰納法を行う。帰納法の述語は

```math
\Phi(j) :\equiv a \le j .
```

- **基底段**（$`j = a`$、鎖の長さ $`0`$）：$`a \le a`$ は $`\le`$ の反射性による。

- **帰納段**（$`a \mathbin{(\to^M_0)^{*}} y`$ と $`y \to^M_0 z`$ から $`a \mathbin{(\to^M_0)^{*}} z`$）：
  帰納法の仮定は $`\Phi(y)`$、すなわち $`a \le y`$ である。
  [T.nextrel0_lt](#t-nextrel0_lt) より $`y \lt z`$ であるから $`a \le y \le z`$、
  すなわち $`\Phi(z)`$。∎

<a id="d-z0ok"></a>
## 定義: 行 0 が 0 の列の規律 (D.z0ok)

$`M \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{z0ok}(M) :\iff \forall j,\ j \lt \lvert M\rvert \to \bigl(M_{0,j} = 0 \to M_{1,j} = 0\bigr).
```

すなわち行 $`0`$ の値が $`0`$ である列は行 $`1`$ の値も $`0`$ である、と読む。

<a id="t-z0ok_diagSeq"></a>
## 定理: 対角列は $`\mathrm{z0ok}`$ をみたす (T.z0ok_diagSeq)

### 定理

任意の $`v \in \mathbb{N}`$ に対し $`\mathrm{z0ok}(\Delta_0^v)`$。

### 証明

$`j`$ を取り $`j \lt \lvert \Delta_0^v\rvert`$、$`(\Delta_0^v)_{0,j} = 0`$ とする。
[T.diagSeq0_length](#t-diagSeq0_length) より $`\lvert \Delta_0^v\rvert = v + 1`$ であるから
$`j \lt v + 1`$ であり、[T.diagSeq0_getD](#t-diagSeq0_getD) より
$`\Delta_0^v\langle j\rangle = (j, j)`$ である。$`M_{i,j}`$ の定義（D.entry）により

```math
(\Delta_0^v)_{0,j} = j, \qquad (\Delta_0^v)_{1,j} = j
```

である。仮定 $`(\Delta_0^v)_{0,j} = 0`$ は $`j = 0`$ を与えるから、
$`(\Delta_0^v)_{1,j} = j = 0`$ である。∎

<a id="t-z0ok_take"></a>
## 定理: 前部分列は $`\mathrm{z0ok}`$ をみたす (T.z0ok_take)

### 定理

$`\mathrm{z0ok}(M)`$ ならば、任意の $`m \in \mathbb{N}`$ に対し
$`\mathrm{z0ok}(\mathrm{take}_m M)`$。

### 証明

$`j`$ を取り $`j \lt \lvert \mathrm{take}_m M\rvert`$、$`(\mathrm{take}_m M)_{0,j} = 0`$ とする。
$`\lvert \mathrm{take}_m M\rvert = \min(m, \lvert M\rvert)`$ であるから
$`j \lt m`$ かつ $`j \lt \lvert M\rvert`$ である。

$`j \lt m`$ に [T.getD_take](#t-getD_take) を適用すると
$`(\mathrm{take}_m M)\langle j\rangle = M\langle j\rangle`$ であり、したがって

```math
(\mathrm{take}_m M)_{0,j} = M_{0,j}, \qquad (\mathrm{take}_m M)_{1,j} = M_{1,j}
```

である。仮定より $`M_{0,j} = 0`$ であるから、$`\mathrm{z0ok}(M)`$ の定義（D.z0ok）を
$`j \lt \lvert M\rvert`$ に適用して $`M_{1,j} = 0`$ を得る。
これは $`(\mathrm{take}_m M)_{1,j} = 0`$ に等しい。∎

<a id="t-z0ok_Pred"></a>
## 定理: 前者は $`\mathrm{z0ok}`$ をみたす (T.z0ok_Pred)

### 定理

$`\mathrm{z0ok}(M)`$ ならば $`\mathrm{z0ok}(\mathrm{Pred}\,M)`$。

### 証明

$`\mathrm{Pred}`$ の定義（D.Pred）の場合分けによる。

- $`\lvert M\rvert \le 1`$ のとき。$`\mathrm{Pred}\,M = M`$ であり、仮定そのものである。

- $`\lvert M\rvert \ge 2`$ のとき。
  $`\mathrm{Pred}\,M = \mathrm{dropLast}\,M = \mathrm{take}_{\lvert M\rvert - 1} M`$ である
  （どれも $`M`$ の先頭 $`\lvert M\rvert - 1`$ 要素からなる列である）。
  よって [T.z0ok_take](#t-z0ok_take) を $`m := \lvert M\rvert - 1`$ に適用すればよい。∎

<a id="t-z0ok_copyExp"></a>
## 定理: コピー展開は $`\mathrm{z0ok}`$ をみたす (T.z0ok_copyExp)

### 定理

$`G, B \in \mathrm{PairSeq}`$、$`\ell \in \mathbb{N}\times\mathbb{N}`$、$`d_0, n \in \mathbb{N}`$ とする。
$`\mathrm{z0ok}\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)`$ ならば
$`\mathrm{z0ok}\bigl(\mathrm{copyExp}(G, B, d_0, n)\bigr)`$。

### 証明

$`E := \mathrm{copyExp}(G, B, d_0, n)`$、$`H := G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ とおく。
[T.hostM_length](#t-hostM_length) より
$`\lvert H\rvert = \lvert G\rvert + \lvert B\rvert + 1`$ である。

$`j`$ を取り $`j \lt \lvert E\rvert`$、$`E_{0,j} = 0`$ とする。
[T.copyExp_length](#t-copyExp_length) より
$`\lvert E\rvert = \lvert G\rvert + n \lvert B\rvert`$ であるから
$`j \lt \lvert G\rvert + n \lvert B\rvert`$ である。$`j`$ と $`\lvert G\rvert`$ の大小で場合分けする。

**(a) $`j \lt \lvert G\rvert`$ のとき。**
[T.copyExp_getD_pre](#t-copyExp_getD_pre) より $`E\langle j\rangle = G\langle j\rangle`$、
[T.hostM_getD_pre](#t-hostM_getD_pre) より $`H\langle j\rangle = G\langle j\rangle`$ である。
$`j \lt \lvert G\rvert \le \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$ であるから、
$`\mathrm{z0ok}(H)`$ の定義（D.z0ok）を添字 $`j`$ に適用できる。その前件は
$`H_{0,j} = G_{0,j} = E_{0,j} = 0`$ で成り立つから、$`H_{1,j} = 0`$、すなわち
$`E_{1,j} = G_{1,j} = H_{1,j} = 0`$ を得る。

**(b) $`\lvert G\rvert \le j`$ のとき。**
まず $`0 \lt \lvert B\rvert`$ を示す。$`\lvert B\rvert = 0`$ とすると
$`n \lvert B\rvert = 0`$ となり $`j \lt \lvert G\rvert`$ となって、この場合の仮定に矛盾する。

$`j - \lvert G\rvert \lt n \lvert B\rvert`$ であるから、
[T.index_decomp](#t-index_decomp) を $`L := \lvert B\rvert`$ に適用して
$`k \lt n`$、$`q \lt \lvert B\rvert`$、$`j - \lvert G\rvert = k \lvert B\rvert + q`$ なる
$`k, q`$ を取る。$`\lvert G\rvert \le j`$ より
$`j = \lvert G\rvert + (k \lvert B\rvert + q)`$ である。

[T.copyExp_getD_copy](#t-copyExp_getD_copy) より

```math
E\langle j\rangle = \bigl(\pi_1(B\langle q\rangle) + k d_0,\ \pi_2(B\langle q\rangle)\bigr)
```

であり、$`M_{i,j}`$ の定義（D.entry）により
$`E_{0,j} = B_{0,q} + k d_0`$、$`E_{1,j} = B_{1,q}`$ である。
仮定 $`E_{0,j} = 0`$ より $`B_{0,q} + k d_0 = 0`$、したがって $`B_{0,q} = 0`$ である。

$`q \lt \lvert B\rvert`$ に [T.hostM_getD_blk](#t-hostM_getD_blk) を適用すると
$`H\langle \lvert G\rvert + q\rangle = B\langle q\rangle`$ である。
$`\lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$ であるから、
$`\mathrm{z0ok}(H)`$ の定義（D.z0ok）を添字 $`\lvert G\rvert + q`$ に適用できる。その前件は
$`H_{0,\lvert G\rvert + q} = B_{0,q} = 0`$ で成り立つから、
$`B_{1,q} = H_{1,\lvert G\rvert + q} = 0`$、すなわち $`E_{1,j} = 0`$ を得る。∎

<a id="t-nextrel0_unique"></a>
## 定理: 行 0 の親の一意性 (T.nextrel0_unique)

### 定理

$`k_1 \to^M_0 j`$ かつ $`k_2 \to^M_0 j`$ ならば $`k_1 = k_2`$。

### 証明

$`k_1`$ と $`k_2`$ の三分律で場合分けする。

**(a) $`k_1 \lt k_2`$ のとき。**
$`k_2 \to^M_0 j`$ の第 3 条件（D.nextrel0）より $`k_2 \lt j`$ である。
$`k_1 \to^M_0 j`$ の第 5 条件の全称変数に $`k_2`$ を代入すると、その前件
$`k_1 \lt k_2 \wedge k_2 \lt j`$ が成り立つから

```math
M_{0,j} \le M_{0,k_2}
```

を得る。一方 $`k_2 \to^M_0 j`$ の第 4 条件は $`M_{0,k_2} \lt M_{0,j}`$ である。
両者から $`M_{0,j} \lt M_{0,j}`$ となり、$`\lt`$ の非反射性に矛盾する。

**(b) $`k_1 = k_2`$ のとき。** 結論そのものである。

**(c) $`k_2 \lt k_1`$ のとき。**
$`k_1 \to^M_0 j`$ の第 3 条件より $`k_1 \lt j`$ である。
$`k_2 \to^M_0 j`$ の第 5 条件の全称変数に $`k_1`$ を代入すると、その前件
$`k_2 \lt k_1 \wedge k_1 \lt j`$ が成り立つから
$`M_{0,j} \le M_{0,k_1}`$ を得る。一方 $`k_1 \to^M_0 j`$ の第 4 条件は
$`M_{0,k_1} \lt M_{0,j}`$ である。両者から $`M_{0,j} \lt M_{0,j}`$ となり矛盾する。∎

<a id="t-nextrel1_unique"></a>
## 定理: 行 1 の親の一意性 (T.nextrel1_unique)

### 定理

$`k_1 \to^M_1 j`$ かつ $`k_2 \to^M_1 j`$ ならば $`k_1 = k_2`$。

### 証明

$`k_1`$ と $`k_2`$ の三分律で場合分けする。

**(a) $`k_1 \lt k_2`$ のとき。**
$`k_2 \to^M_1 j`$ の第 5 条件（D.nextrel1）より $`k_2 \le^M_0 j`$ である。
$`k_1 \to^M_1 j`$ の第 6 条件の全称変数に $`k_2`$ を代入すると、その前件
$`k_1 \lt k_2 \wedge k_2 \le^M_0 j`$ が成り立つから

```math
M_{1,j} \le M_{1,k_2}
```

を得る。一方 $`k_2 \to^M_1 j`$ の第 4 条件は $`M_{1,k_2} \lt M_{1,j}`$ である。
両者から $`M_{1,j} \lt M_{1,j}`$ となり、$`\lt`$ の非反射性に矛盾する。

**(b) $`k_1 = k_2`$ のとき。** 結論そのものである。

**(c) $`k_2 \lt k_1`$ のとき。**
$`k_1 \to^M_1 j`$ の第 5 条件より $`k_1 \le^M_0 j`$ である。
$`k_2 \to^M_1 j`$ の第 6 条件の全称変数に $`k_1`$ を代入すると、その前件
$`k_2 \lt k_1 \wedge k_1 \le^M_0 j`$ が成り立つから
$`M_{1,j} \le M_{1,k_1}`$ を得る。一方 $`k_1 \to^M_1 j`$ の第 4 条件は
$`M_{1,k_1} \lt M_{1,j}`$ である。両者から $`M_{1,j} \lt M_{1,j}`$ となり矛盾する。∎

<a id="t-blockok_head_zero"></a>
## 定理: ブロックの先頭は行 0 が 0 (T.blockok_head_zero)

### 定理

$`\mathrm{blockok}(0, M)`$ かつ $`0 \lt \lvert M\rvert`$ ならば $`M_{0,0} = 0`$。

### 証明

$`0 \lt \lvert M\rvert`$ より $`M`$ は空でないから、$`M = m_0 :: M'`$ と書ける。
このとき $`M\langle 0\rangle = m_0`$ であり、$`M`$ の先頭要素も $`m_0`$ である。

$`\mathrm{blockok}`$ の定義（D.blockok）の第 1 連言子は
「$`M \ne ()`$ ならば $`M`$ の先頭要素の第 1 成分が $`0`$ に等しい」である。
$`M = m_0 :: M' \ne ()`$ であるから、$`\pi_1(m_0) = 0`$ を得る。
$`M_{i,j}`$ の定義（D.entry）より $`M_{0,0} = \pi_1(M\langle 0\rangle) = \pi_1(m_0) = 0`$。∎

<a id="t-parent0_exists"></a>
## 定理: 行 0 の親の存在 (T.parent0_exists)

### 定理

$`\mathrm{blockok}(0, M)`$、$`j \lt \lvert M\rvert`$、$`0 \lt M_{0,j}`$ ならば、
ある $`k`$ が存在して $`k \to^M_0 j`$。

### 証明

**第 1 段：$`0 \lt j`$。**
$`j = 0`$ とすると、[T.blockok_head_zero](#t-blockok_head_zero) より $`M_{0,0} = 0`$ であり、
これは仮定 $`0 \lt M_{0,j} = M_{0,0}`$ に矛盾する。

**第 2 段：候補の最大元を取る。** 述語 $`P`$ を

```math
P(k) :\equiv M_{0,k} \lt M_{0,j}
```

で定める。[T.blockok_head_zero](#t-blockok_head_zero) より $`M_{0,0} = 0`$ であり、
仮定より $`0 \lt M_{0,j}`$ であるから $`P(0)`$ が成り立つ。
集合

```math
S := \{\, k \mid k \le j - 1 \ \wedge\ P(k) \,\}
```

は $`0`$ を要素にもち（第 1 段より $`0 \le j - 1`$）、$`\{0, 1, \dots, j-1\}`$ に含まれる
有限集合であるから最大元をもつ。それを $`k`$ とおく。$`k`$ について次の 3 つが成り立つ。

```math
\begin{aligned}
&(\mathrm{i})\ k \le j - 1, \cr
&(\mathrm{ii})\ M_{0,k} \lt M_{0,j}, \cr
&(\mathrm{iii})\ \forall l,\ \bigl(k \lt l \wedge l \le j - 1\bigr) \to \neg\,\bigl(M_{0,l} \lt M_{0,j}\bigr).
\end{aligned}
```

$`(\mathrm{i})`$ と $`(\mathrm{ii})`$ は $`k \in S`$ から、$`(\mathrm{iii})`$ は $`k`$ が
$`S`$ の最大元であることから従う。

**第 3 段：$`k \to^M_0 j`$ の 5 条件を確かめる。**

- 第 1 条件 $`k \lt \lvert M\rvert`$：$`(\mathrm{i})`$ と第 1 段より $`k \le j - 1 \lt j`$ であり、
  仮定 $`j \lt \lvert M\rvert`$ と合わせて $`k \lt \lvert M\rvert`$。
- 第 2 条件 $`j \lt \lvert M\rvert`$：仮定である。
- 第 3 条件 $`k \lt j`$：$`(\mathrm{i})`$ と第 1 段より $`k \le j - 1 \lt j`$。
- 第 4 条件 $`M_{0,k} \lt M_{0,j}`$：$`(\mathrm{ii})`$ である。
- 第 5 条件 $`\forall l,\ (k \lt l \wedge l \lt j) \to M_{0,j} \le M_{0,l}`$：
  $`l`$ を取り $`k \lt l`$、$`l \lt j`$ とする。$`l \lt j`$ より $`l \le j - 1`$ であるから
  $`(\mathrm{iii})`$ が使えて $`\neg(M_{0,l} \lt M_{0,j})`$、すなわち
  $`M_{0,j} \le M_{0,l}`$。∎

<a id="t-chain_to_zero"></a>
## 定理: 行 0 が 0 の列への鎖 (T.chain_to_zero)

### 定理

$`\mathrm{blockok}(0, M)`$ とする。任意の $`\mathrm{lev}, j \in \mathbb{N}`$ について、
$`M_{0,j} = \mathrm{lev}`$ かつ $`j \lt \lvert M\rvert`$ ならば、ある $`r`$ が存在して

```math
r \le j, \qquad M_{0,r} = 0, \qquad r \mathbin{(\to^M_0)^{*}} j .
```

### 証明

$`\mathrm{lev}`$ に関する強帰納法。帰納法の述語は

```math
\Phi(\mathrm{lev}) :\equiv \forall j,\ \bigl(M_{0,j} = \mathrm{lev} \wedge j \lt \lvert M\rvert\bigr)
  \to \exists r,\ \bigl(r \le j \wedge M_{0,r} = 0 \wedge r \mathbin{(\to^M_0)^{*}} j\bigr),
```

帰納法の仮定は「$`\mathrm{lev}' \lt \mathrm{lev}`$ なるすべての $`\mathrm{lev}'`$ について
$`\Phi(\mathrm{lev}')`$」である。$`j`$ を取り $`M_{0,j} = \mathrm{lev}`$、$`j \lt \lvert M\rvert`$ とし、
$`M_{0,j}`$ が $`0`$ かどうかで場合分けする。

**(a) $`M_{0,j} = 0`$ のとき。** $`r := j`$ と取る。$`j \le j`$、$`M_{0,j} = 0`$ であり、
$`j \mathbin{(\to^M_0)^{*}} j`$ は長さ $`0`$ の鎖である。

**(b) $`M_{0,j} \ne 0`$、すなわち $`0 \lt M_{0,j}`$ のとき。**
[T.parent0_exists](#t-parent0_exists) を $`\mathrm{blockok}(0,M)`$、$`j \lt \lvert M\rvert`$、
$`0 \lt M_{0,j}`$ に適用して、$`k \to^M_0 j`$ なる $`k`$ を取る。
$`\to^M_0`$ の定義（D.nextrel0）の第 1 条件より $`k \lt \lvert M\rvert`$、
第 3 条件より $`k \lt j`$、第 4 条件より

```math
M_{0,k} \lt M_{0,j} = \mathrm{lev}
```

である。よって帰納法の仮定を $`\mathrm{lev}' := M_{0,k}`$ に適用でき、それを
$`j := k`$（$`M_{0,k} = M_{0,k}`$ と $`k \lt \lvert M\rvert`$ による）に用いると、

```math
r \le k, \qquad M_{0,r} = 0, \qquad r \mathbin{(\to^M_0)^{*}} k
```

なる $`r`$ が得られる。この鎖の末尾に $`k \to^M_0 j`$ を継ぎ足せば
$`r \mathbin{(\to^M_0)^{*}} j`$ であり、$`r \le k \lt j`$ より $`r \le j`$ である。∎

<a id="t-parent1_exists"></a>
## 定理: 行 1 の親の存在 (T.parent1_exists)

### 定理

$`\mathrm{blockok}(0, M)`$、$`\mathrm{z0ok}(M)`$、$`j \lt \lvert M\rvert`$、$`0 \lt M_{1,j}`$
ならば、ある $`k`$ が存在して $`k \to^M_1 j`$。

### 証明

**第 1 段：行 0 の根までの鎖を取る。**
[T.chain_to_zero](#t-chain_to_zero) を $`\mathrm{lev} := M_{0,j}`$ に適用して、

```math
r \le j, \qquad M_{0,r} = 0, \qquad r \mathbin{(\to^M_0)^{*}} j
```

なる $`r`$ を取る。$`r \le j \lt \lvert M\rvert`$ である。
$`M_{0,r} = 0`$ に $`\mathrm{z0ok}(M)`$ の定義（D.z0ok）を適用して $`M_{1,r} = 0`$ を得る。

**第 2 段：$`r \lt j`$。**
$`r \le j`$ である。$`r = j`$ とすると $`M_{1,j} = M_{1,r} = 0`$ となり、
仮定 $`0 \lt M_{1,j}`$ に矛盾する。よって $`r \lt j`$。

**第 3 段：候補の最大元を取る。** 述語 $`P`$ を

```math
P(k) :\equiv k \le^M_0 j \ \wedge\ M_{1,k} \lt M_{1,j}
```

で定める。$`P(r)`$ が成り立つ。実際、$`\le^M_0`$ の定義（D.le0）の 3 条件は
$`r \lt \lvert M\rvert`$、$`j \lt \lvert M\rvert`$、$`r \mathbin{(\to^M_0)^{*}} j`$ で
いずれも第 1 段で得ており、また $`M_{1,r} = 0 \lt M_{1,j}`$ である。

集合

```math
S := \{\, k \mid k \le j - 1 \ \wedge\ P(k) \,\}
```

は $`r`$ を要素にもち（第 2 段より $`r \le j - 1`$）、$`\{0,1,\dots,j-1\}`$ に含まれる
有限集合であるから最大元をもつ。それを $`k`$ とおく。$`k`$ について

```math
\begin{aligned}
&(\mathrm{i})\ k \le j - 1, \cr
&(\mathrm{ii})\ k \le^M_0 j \ \wedge\ M_{1,k} \lt M_{1,j}, \cr
&(\mathrm{iii})\ \forall l,\ \bigl(k \lt l \wedge l \le j - 1\bigr) \to \neg\,P(l)
\end{aligned}
```

が成り立つ。

**第 4 段：$`k \to^M_1 j`$ の 6 条件を確かめる。**

- 第 1 条件 $`k \lt \lvert M\rvert`$：$`(\mathrm{i})`$ と第 2 段より $`k \le j - 1 \lt j`$ であり、
  $`j \lt \lvert M\rvert`$ と合わせてよい。
- 第 2 条件 $`j \lt \lvert M\rvert`$：仮定である。
- 第 3 条件 $`k \lt j`$：$`(\mathrm{i})`$ と第 2 段による。
- 第 4 条件 $`M_{1,k} \lt M_{1,j}`$：$`(\mathrm{ii})`$ の第 2 連言子である。
- 第 5 条件 $`k \le^M_0 j`$：$`(\mathrm{ii})`$ の第 1 連言子である。
- 第 6 条件 $`\forall j',\ (k \lt j' \wedge j' \le^M_0 j) \to M_{1,j} \le M_{1,j'}`$：
  $`j'`$ を取り $`k \lt j'`$、$`j' \le^M_0 j`$ とする。
  [T.le0_le](#t-le0_le) より $`j' \le j`$ である。
  - $`j' = j`$ のとき。示すべきは $`M_{1,j} \le M_{1,j}`$ であり、$`\le`$ の反射性による。
  - $`j' \lt j`$ のとき。$`M_{1,j} \le M_{1,j'}`$ を否定して $`M_{1,j'} \lt M_{1,j}`$ と
    仮定する。すると $`j' \le^M_0 j`$ と合わせて $`P(j')`$ が成り立つ。
    一方 $`k \lt j'`$ かつ $`j' \lt j`$ より $`j' \le j - 1`$ であるから、
    $`(\mathrm{iii})`$ が $`\neg P(j')`$ を与え、矛盾する。∎

<a id="t-nextR_one_iff"></a>
## 定理: 行 1 の親子関係の言い換え (T.nextR_one_iff)

### 定理

行つき親子関係 $`\to^M_i`$ に $`i := 1`$ を代入したものは、行 $`1`$ の親子関係
$`\to^M_1`$ に一致する。すなわち $`i = 1`$ のとき $`k \to^M_i j`$ と $`k \to^M_1 j`$ は
同値である。

### 証明

$`\to^M_i`$ の定義（D.nextR）は $`i = 0`$ かどうかによる場合分けである。
$`1 \ne 0`$ であるから第 2 の場合が選ばれ、両辺は定義により同一の命題である。∎

<a id="t-nextR_zero_iff"></a>
## 定理: 行 0 の親子関係の言い換え (T.nextR_zero_iff)

### 定理

行つき親子関係 $`\to^M_i`$ に $`i := 0`$ を代入したものは行 $`0`$ の親子関係
$`\to^M_0`$ に一致する。

### 証明

$`\to^M_i`$ の定義（D.nextR）の場合分けにおいて $`i = 0`$ の条件が成り立つから
第 1 の場合が選ばれ、両辺は定義により同一の命題である。∎

<a id="t-hp_last"></a>
## 定理: 末尾の列は親をもつ (T.hp_last)

### 定理

$`j_1 := \lvert M\rvert - 1`$ とおく。$`\mathrm{blockok}(0, M)`$、$`\mathrm{z0ok}(M)`$、
$`0 \lt \lvert M\rvert`$、$`M\langle j_1\rangle \ne (0,0)`$ ならば

```math
\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M, j_1),\ j_1\bigr).
```

### 証明

$`0 \lt \lvert M\rvert`$ より $`j_1 = \lvert M\rvert - 1 \lt \lvert M\rvert`$ である。
$`M_{1,j_1}`$ の正負で場合分けする。

**(a) $`0 \lt M_{1,j_1}`$ のとき。**
$`\mathrm{idx}_1`$ の定義（D.idx1）の第 1 の場合が選ばれ $`\mathrm{idx}_1(M,j_1) = 1`$ である。
[T.parent1_exists](#t-parent1_exists) を $`\mathrm{blockok}(0,M)`$、$`\mathrm{z0ok}(M)`$、
$`j_1 \lt \lvert M\rvert`$、$`0 \lt M_{1,j_1}`$ に適用して、$`k \to^M_1 j_1`$ なる $`k`$ を取る。

$`\mathrm{hasParent}`$ の定義（D.hasParent）は存在と一意性の連言である。

- 存在：$`\mathrm{idx}_1(M,j_1) = 1`$ であるから、示すべきは $`i = 1`$ の場合の
  $`k \to^M_i j_1`$ である。[T.nextR_one_iff](#t-nextR_one_iff) よりこれは
  $`k \to^M_1 j_1`$ と同値であり、後者は上で得た。
- 一意性：$`y`$ が $`i = 1`$ の場合の $`y \to^M_i j_1`$ をみたすとすると、ふたたび
  [T.nextR_one_iff](#t-nextR_one_iff) より $`y \to^M_1 j_1`$ である。
  [T.nextrel1_unique](#t-nextrel1_unique) を $`y \to^M_1 j_1`$ と $`k \to^M_1 j_1`$ に
  適用して $`y = k`$。

**(b) $`M_{1,j_1} = 0`$ のとき。**
まず $`0 \lt M_{0,j_1}`$ を示す。$`M_{0,j_1} = 0`$ とすると、
$`M_{i,j}`$ の定義（D.entry）より $`\pi_1(M\langle j_1\rangle) = M_{0,j_1} = 0`$、
$`\pi_2(M\langle j_1\rangle) = M_{1,j_1} = 0`$ であるから
$`M\langle j_1\rangle = (0,0)`$ となり、仮定 $`M\langle j_1\rangle \ne (0,0)`$ に矛盾する。

$`\mathrm{idx}_1`$ の定義（D.idx1）の条件 $`0 \lt M_{1,j_1}`$ は偽であるから
$`\mathrm{idx}_1(M,j_1) = 0`$ である。
[T.parent0_exists](#t-parent0_exists) を $`\mathrm{blockok}(0,M)`$、
$`j_1 \lt \lvert M\rvert`$、$`0 \lt M_{0,j_1}`$ に適用して、$`k \to^M_0 j_1`$ なる $`k`$ を取る。

$`\mathrm{hasParent}`$ の定義（D.hasParent）の 2 つを確かめる。

- 存在：$`\mathrm{idx}_1(M,j_1) = 0`$ であるから、示すべきは $`i = 0`$ の場合の
  $`k \to^M_i j_1`$ である。[T.nextR_zero_iff](#t-nextR_zero_iff) よりこれは
  $`k \to^M_0 j_1`$ と同値であり、後者は上で得た。
- 一意性：$`y`$ が $`i = 0`$ の場合の $`y \to^M_i j_1`$ をみたすとすると、ふたたび
  [T.nextR_zero_iff](#t-nextR_zero_iff) より $`y \to^M_0 j_1`$ である。
  [T.nextrel0_unique](#t-nextrel0_unique) を $`y \to^M_0 j_1`$ と $`k \to^M_0 j_1`$ に
  適用して $`y = k`$。∎

<a id="t-z0ok_oper"></a>
## 定理: 展開は $`\mathrm{z0ok}`$ を保つ (T.z0ok_oper)

### 定理

$`1 \le n`$ かつ $`\mathrm{z0ok}(M)`$ ならば $`\mathrm{z0ok}(M[n])`$。

### 証明

$`j_1 := \lvert M\rvert - 1`$、$`i_1 := \mathrm{idx}_1(M, j_1)`$ とおき、
$`M[n]`$ の定義（D.oper）の分岐に沿って場合分けする。

**(a) $`j_1 = 0`$ のとき。**
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より $`M[n] = M`$ であり、
結論は仮定 $`\mathrm{z0ok}(M)`$ そのものである。

**(b) $`j_1 \ne 0`$ かつ $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ のとき。**
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) より
$`M[n] = \mathrm{Pred}\,M`$ であり、[T.z0ok_Pred](#t-z0ok_Pred) を適用する。

**(c) $`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) より
$`M[n] = \mathrm{Pred}\,M`$ であり、[T.z0ok_Pred](#t-z0ok_Pred) を適用する。

**(d) $`j_1 \ne 0`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、かつ
$`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
$`j_1 = \lvert M\rvert - 1 \ne 0`$ と切り捨て減法より $`1 \lt \lvert M\rvert`$ である。
[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) を
$`1 \lt \lvert M\rvert`$、$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$、
$`\mathrm{hasParent}(M, i_1, j_1)`$、$`1 \le n`$ に適用して
$`G, v_0, w_0, R, d_0, \ell`$ を取る。その (1) と (2) は

```math
M = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} (\ell),
```
```math
M[n] = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+0 \cdot d_0}
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+(n-1)d_0}
```

である。後者の右辺は $`\mathrm{copyExp}`$ の定義（D.copyExp）により

```math
M[n] = \mathrm{copyExp}\bigl(G,\ (v_0,w_0) :: R,\ d_0,\ n\bigr)
```

と書ける。仮定 $`\mathrm{z0ok}(M)`$ を (1) で書き換えると
$`\mathrm{z0ok}\bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr)`$ であるから、
[T.z0ok_copyExp](#t-z0ok_copyExp) を $`B := (v_0,w_0) :: R`$ に適用して結論を得る。∎

<a id="t-z0ok_ST_PS"></a>
## 定理: 標準形は $`\mathrm{z0ok}`$ をみたす (T.z0ok_ST_PS)

### 定理

$`M \in \mathrm{ST\_PS}`$ ならば $`\mathrm{z0ok}(M)`$。

### 証明

$`\mathrm{ST\_PS}`$ の導出に関する帰納法。帰納法の述語は

```math
\Phi(M) :\equiv \mathrm{z0ok}(M).
```

- **基底段**（規則 (diag)）：$`M = \Delta_0^v`$ である。
  [T.z0ok_diagSeq](#t-z0ok_diagSeq) が $`\Phi(\Delta_0^v)`$ そのものである。

- **帰納段**（規則 (oper)）：$`N \in \mathrm{ST\_PS}`$、$`1 \le n`$ とし、帰納法の仮定は
  $`\Phi(N)`$、すなわち $`\mathrm{z0ok}(N)`$ である。
  [T.z0ok_oper](#t-z0ok_oper) を $`1 \le n`$ と $`\mathrm{z0ok}(N)`$ に適用して
  $`\mathrm{z0ok}(N[n])`$、すなわち $`\Phi(N[n])`$ を得る。∎

<a id="t-rtg_through_pivot"></a>
## 定理: 行 0 の鎖は枢軸を通る (T.rtg_through_pivot)

### 定理

$`M \in \mathrm{PairSeq}`$、$`\rho \in \mathbb{N}`$ とする。任意の $`a, b \in \mathbb{N}`$ について、

```math
a \mathbin{(\to^M_0)^{*}} b, \qquad a \lt \rho, \qquad \rho \le b, \qquad
\forall y,\ \bigl(\rho \lt y \wedge y \le b\bigr) \to M_{0,\rho} \lt M_{0,y}
```

ならば $`\rho \mathbin{(\to^M_0)^{*}} b`$。

### 証明

$`a`$ を固定し、鎖 $`a \mathbin{(\to^M_0)^{*}} b`$ の構成に関する帰納法を行う。
帰納法の述語は

```math
\Phi(b) :\equiv \Bigl(a \lt \rho \wedge \rho \le b \wedge
  \forall y,\ (\rho \lt y \wedge y \le b) \to M_{0,\rho} \lt M_{0,y}\Bigr)
  \to \rho \mathbin{(\to^M_0)^{*}} b .
```

- **基底段**（$`b = a`$、鎖の長さ $`0`$）：前件の第 1 連言子は $`a \lt \rho`$、
  第 2 連言子は $`\rho \le a`$ であり、両者から $`a \lt a`$ となって $`\lt`$ の
  非反射性に反する。よって前件が偽であり $`\Phi(a)`$ が成り立つ。

**帰納段**（$`a \mathbin{(\to^M_0)^{*}} y`$ と $`y \to^M_0 z`$ から
$`a \mathbin{(\to^M_0)^{*}} z`$）：帰納法の仮定は $`\Phi(y)`$ である。
$`a \lt \rho`$、$`\rho \le z`$、および

```math
(\ast)\qquad \forall y',\ \bigl(\rho \lt y' \wedge y' \le z\bigr) \to M_{0,\rho} \lt M_{0,y'}
```

を仮定して $`\rho \mathbin{(\to^M_0)^{*}} z`$ を示す。$`\rho`$ と $`y`$ の大小で場合分けする。

**(a) $`\rho \le y`$ のとき。**
[T.nextrel0_lt](#t-nextrel0_lt) より $`y \lt z`$ である。したがって
$`\rho \lt y' \wedge y' \le y`$ なる $`y'`$ は $`y' \le y \le z`$ をみたすから、
$`(\ast)`$ より $`M_{0,\rho} \lt M_{0,y'}`$ である。すなわち帰納法の仮定 $`\Phi(y)`$ の
前件 3 つがすべて成り立つ。よって $`\rho \mathbin{(\to^M_0)^{*}} y`$ を得る。
この鎖の末尾に $`y \to^M_0 z`$ を継ぎ足せば $`\rho \mathbin{(\to^M_0)^{*}} z`$ である。

**(b) $`y \lt \rho`$ のとき。** さらに $`\rho`$ と $`z`$ で場合分けする（$`\rho \le z`$ である）。

**(b-1) $`\rho = z`$ のとき。** $`\rho \mathbin{(\to^M_0)^{*}} z`$ は長さ $`0`$ の鎖である。

**(b-2) $`\rho \lt z`$ のとき。** $`y \to^M_0 z`$ すなわち $`\to^M_0`$ の定義（D.nextrel0）の
第 5 条件の全称変数に $`\rho`$ を代入すると、その前件 $`y \lt \rho \wedge \rho \lt z`$ が
成り立つから

```math
M_{0,z} \le M_{0,\rho}
```

を得る。一方 $`(\ast)`$ を $`y' := z`$ に適用すると（$`\rho \lt z`$ かつ $`z \le z`$）
$`M_{0,\rho} \lt M_{0,z}`$ である。両者から $`M_{0,z} \lt M_{0,z}`$ となり
$`\lt`$ の非反射性に矛盾する。よってこの場合は起こらない。∎

<a id="t-le0_through_pivot"></a>
## 定理: 行 0 の祖先関係は枢軸を通る (T.le0_through_pivot)

### 定理

$`a \le^M_0 b`$、$`a \lt \rho`$、$`\rho \le b`$、かつ

```math
\forall y,\ \bigl(\rho \lt y \wedge y \le b\bigr) \to M_{0,\rho} \lt M_{0,y}
```

ならば $`\rho \le^M_0 b`$。

### 証明

$`\le^M_0`$ の定義（D.le0）の 3 条件を確かめる。仮定 $`a \le^M_0 b`$ からは
$`a \lt \lvert M\rvert`$、$`b \lt \lvert M\rvert`$、$`a \mathbin{(\to^M_0)^{*}} b`$ が得られる。

- 第 1 条件 $`\rho \lt \lvert M\rvert`$：$`\rho \le b`$ と $`b \lt \lvert M\rvert`$ による。
- 第 2 条件 $`b \lt \lvert M\rvert`$：上のとおりである。
- 第 3 条件 $`\rho \mathbin{(\to^M_0)^{*}} b`$：
  [T.rtg_through_pivot](#t-rtg_through_pivot) を $`a \mathbin{(\to^M_0)^{*}} b`$、
  $`a \lt \rho`$、$`\rho \le b`$、および最後の仮定に適用する。∎

<a id="t-entry_shift"></a>
## 定理: 平行移動列の成分 (T.entry_shift)

### 定理

$`S \in \mathrm{PairSeq}`$、$`d, j \in \mathbb{N}`$ とし、$`S^{+d}`$ で $`S`$ の各対の
第 1 成分に一様に $`d`$ を足した列を表す。$`j \lt \lvert S\rvert`$ ならば

```math
(S^{+d})_{0,j} = S_{0,j} + d
\qquad\text{かつ}\qquad
(S^{+d})_{1,j} = S_{1,j} .
```

### 証明

$`S^{+d}`$ は $`S`$ の各要素を写したものであるから $`\lvert S^{+d}\rvert = \lvert S\rvert`$ で
あり、仮定 $`j \lt \lvert S\rvert`$ よりどちらの列でも第 $`j`$ 要素が存在する。
[T.getD_eq_getElem'](Cnf.md#t-getD_eq_getElem') より

```math
S\langle j\rangle = S_j, \qquad S^{+d}\langle j\rangle = (S^{+d})_j = \bigl(\pi_1(S_j) + d,\ \pi_2(S_j)\bigr)
```

である。$`M_{i,j}`$ の定義（D.entry）は $`i = 0`$ のとき第 1 成分、$`i \ne 0`$ のとき
第 2 成分を読むから、

```math
(S^{+d})_{0,j} = \pi_1(S_j) + d = S_{0,j} + d,
\qquad
(S^{+d})_{1,j} = \pi_2(S_j) = S_{1,j} . \qquad \blacksquare
```

<a id="t-nextrel0_shift_iff"></a>
## 定理: 行 0 の親子関係の平行移動不変性 (T.nextrel0_shift_iff)

### 定理

$`b \lt \lvert S\rvert`$ ならば

```math
a \to^{S^{+d}}_0 b \iff a \to^{S}_0 b .
```

### 証明

$`\lvert S^{+d}\rvert = \lvert S\rvert`$ であるから、$`\to^M_0`$ の定義（D.nextrel0）の
第 1・第 2・第 3 条件は両辺で同一の命題である。第 4・第 5 条件を両方向で移す。

**（左から右）** $`a \to^{S^{+d}}_0 b`$ を仮定する。第 1 条件より $`a \lt \lvert S\rvert`$ で
ある。示すべき第 4・第 5 条件は次のとおり。

- 第 4 条件：仮定の第 4 条件は $`(S^{+d})_{0,a} \lt (S^{+d})_{0,b}`$ である。
  [T.entry_shift](#t-entry_shift) を $`j := a`$ と $`j := b`$ に適用すると
  $`S_{0,a} + d \lt S_{0,b} + d`$ となり、$`\mathbb{N}`$ の加法の狭義単調性から
  $`S_{0,a} \lt S_{0,b}`$ を得る。

- 第 5 条件：$`l`$ を取り $`a \lt l`$、$`l \lt b`$ とする。$`l \lt b \lt \lvert S\rvert`$ で
  あるから [T.entry_shift](#t-entry_shift) が $`j := l`$ と $`j := b`$ で使えて、
  仮定の第 5 条件 $`(S^{+d})_{0,b} \le (S^{+d})_{0,l}`$ は
  $`S_{0,b} + d \le S_{0,l} + d`$、すなわち $`S_{0,b} \le S_{0,l}`$ に等しい。

**（右から左）** $`a \to^{S}_0 b`$ を仮定する。第 1 条件より $`a \lt \lvert S\rvert`$ である。

- 第 4 条件：仮定の第 4 条件 $`S_{0,a} \lt S_{0,b}`$ の両辺に $`d`$ を足して
  $`S_{0,a} + d \lt S_{0,b} + d`$ であり、[T.entry_shift](#t-entry_shift) により
  これは $`(S^{+d})_{0,a} \lt (S^{+d})_{0,b}`$ である。

- 第 5 条件：$`l`$ を取り $`a \lt l`$、$`l \lt b`$ とする。$`l \lt \lvert S\rvert`$ であるから
  [T.entry_shift](#t-entry_shift) が使え、仮定の第 5 条件
  $`S_{0,b} \le S_{0,l}`$ の両辺に $`d`$ を足して
  $`(S^{+d})_{0,b} \le (S^{+d})_{0,l}`$ を得る。∎

<a id="t-rtg_shift_of"></a>
## 定理: 平行移動列の鎖はもとの列の鎖 (T.rtg_shift_of)

### 定理

$`a \mathbin{(\to^{S^{+d}}_0)^{*}} b`$ ならば $`a \mathbin{(\to^{S}_0)^{*}} b`$。

### 証明

鎖 $`a \mathbin{(\to^{S^{+d}}_0)^{*}} b`$ の構成に関する帰納法。帰納法の述語は

```math
\Phi(b) :\equiv a \mathbin{(\to^{S}_0)^{*}} b .
```

- **基底段**（$`b = a`$、鎖の長さ $`0`$）：$`a \mathbin{(\to^{S}_0)^{*}} a`$ は
  長さ $`0`$ の鎖である。

- **帰納段**（$`a \mathbin{(\to^{S^{+d}}_0)^{*}} c`$ と $`c \to^{S^{+d}}_0 e`$）：
  帰納法の仮定は $`\Phi(c)`$、すなわち $`a \mathbin{(\to^{S}_0)^{*}} c`$ である。
  [T.nextrel0_bound](#t-nextrel0_bound) を $`c \to^{S^{+d}}_0 e`$ に適用して
  $`e \lt \lvert S^{+d}\rvert = \lvert S\rvert`$ を得る。
  よって [T.nextrel0_shift_iff](#t-nextrel0_shift_iff) が使えて $`c \to^{S}_0 e`$ である。
  帰納法の仮定の鎖の末尾にこの 1 歩を継ぎ足せば $`a \mathbin{(\to^{S}_0)^{*}} e`$、
  すなわち $`\Phi(e)`$。∎

<a id="t-rtg_shift_to"></a>
## 定理: もとの列の鎖は平行移動列の鎖 (T.rtg_shift_to)

### 定理

$`a \mathbin{(\to^{S}_0)^{*}} b`$ ならば $`a \mathbin{(\to^{S^{+d}}_0)^{*}} b`$。

### 証明

鎖 $`a \mathbin{(\to^{S}_0)^{*}} b`$ の構成に関する帰納法。帰納法の述語は

```math
\Phi(b) :\equiv a \mathbin{(\to^{S^{+d}}_0)^{*}} b .
```

- **基底段**（$`b = a`$、鎖の長さ $`0`$）：$`a \mathbin{(\to^{S^{+d}}_0)^{*}} a`$ は
  長さ $`0`$ の鎖である。

- **帰納段**（$`a \mathbin{(\to^{S}_0)^{*}} c`$ と $`c \to^{S}_0 e`$）：
  帰納法の仮定は $`\Phi(c)`$、すなわち $`a \mathbin{(\to^{S^{+d}}_0)^{*}} c`$ である。
  [T.nextrel0_bound](#t-nextrel0_bound) を $`c \to^{S}_0 e`$ に適用して
  $`e \lt \lvert S\rvert`$ を得る。よって
  [T.nextrel0_shift_iff](#t-nextrel0_shift_iff) が使えて $`c \to^{S^{+d}}_0 e`$ である。
  帰納法の仮定の鎖の末尾にこの 1 歩を継ぎ足せば
  $`a \mathbin{(\to^{S^{+d}}_0)^{*}} e`$、すなわち $`\Phi(e)`$。∎

<a id="t-le0_shift_iff"></a>
## 定理: 行 0 の祖先関係の平行移動不変性 (T.le0_shift_iff)

### 定理

```math
a \le^{S^{+d}}_0 b \iff a \le^{S}_0 b .
```

### 証明

$`\lvert S^{+d}\rvert = \lvert S\rvert`$ であるから、$`\le^M_0`$ の定義（D.le0）の
第 1・第 2 条件は両辺で同一の命題である。第 3 条件は、
左から右が [T.rtg_shift_of](#t-rtg_shift_of)、
右から左が [T.rtg_shift_to](#t-rtg_shift_to) である。∎

<a id="t-idx1_shift"></a>
## 定理: 探索行の平行移動不変性 (T.idx1_shift)

### 定理

```math
\mathrm{idx}_1(S^{+d}, j) = \mathrm{idx}_1(S, j) .
```

### 証明

$`\mathrm{idx}_1`$ の定義（D.idx1）は $`0 \lt M_{1,j}`$ の真偽だけで値が決まるから、
$`(S^{+d})_{1,j} = S_{1,j}`$ を示せばよい。$`j`$ と $`\lvert S\rvert`$ の大小で場合分けする。

**(a) $`j \lt \lvert S\rvert`$ のとき。**
[T.entry_shift](#t-entry_shift) の第 2 の等式そのものである。

**(b) $`\lvert S\rvert \le j`$ のとき。**
$`\lvert S^{+d}\rvert = \lvert S\rvert \le j`$ であるから、
$`M\langle j\rangle`$ の定義（D.entry）より
$`S\langle j\rangle = (0,0)`$ かつ $`S^{+d}\langle j\rangle = (0,0)`$ である。
よって $`(S^{+d})_{1,j} = \pi_2\bigl((0,0)\bigr) = 0 = S_{1,j}`$。∎

<a id="t-nextrel1_shift_iff"></a>
## 定理: 行 1 の親子関係の平行移動不変性 (T.nextrel1_shift_iff)

### 定理

$`b \lt \lvert S\rvert`$ ならば

```math
a \to^{S^{+d}}_1 b \iff a \to^{S}_1 b .
```

### 証明

$`\lvert S^{+d}\rvert = \lvert S\rvert`$ であるから、$`\to^M_1`$ の定義（D.nextrel1）の
第 1・第 2・第 3 条件は両辺で同一の命題である。第 5 条件は
[T.le0_shift_iff](#t-le0_shift_iff) により両辺で同値である。残る第 4・第 6 条件を
両方向で移す。

**（左から右）** $`a \to^{S^{+d}}_1 b`$ を仮定する。第 1 条件より $`a \lt \lvert S\rvert`$ で
ある。

- 第 4 条件：仮定の第 4 条件は $`(S^{+d})_{1,a} \lt (S^{+d})_{1,b}`$ である。
  [T.entry_shift](#t-entry_shift) を $`j := a`$ と $`j := b`$ に適用すると
  第 2 の等式により $`S_{1,a} \lt S_{1,b}`$ となる。

- 第 6 条件：$`l`$ を取り $`a \lt l`$、$`l \le^{S}_0 b`$ とする。
  [T.le0_shift_iff](#t-le0_shift_iff) より $`l \le^{S^{+d}}_0 b`$ であるから、
  仮定の第 6 条件の全称変数に $`l`$ を代入して
  $`(S^{+d})_{1,b} \le (S^{+d})_{1,l}`$ を得る。
  [T.le0_le](#t-le0_le) より $`l \le b \lt \lvert S\rvert`$ であるから、
  [T.entry_shift](#t-entry_shift) が $`j := l`$ と $`j := b`$ で使えて、
  この不等式は $`S_{1,b} \le S_{1,l}`$ に等しい。

**（右から左）** $`a \to^{S}_1 b`$ を仮定する。第 1 条件より $`a \lt \lvert S\rvert`$ である。

- 第 4 条件：仮定の第 4 条件 $`S_{1,a} \lt S_{1,b}`$ に
  [T.entry_shift](#t-entry_shift) の第 2 の等式を $`j := a`$ と $`j := b`$ で適用すれば
  $`(S^{+d})_{1,a} \lt (S^{+d})_{1,b}`$ である。

- 第 6 条件：$`l`$ を取り $`a \lt l`$、$`l \le^{S^{+d}}_0 b`$ とする。
  [T.le0_shift_iff](#t-le0_shift_iff) より $`l \le^{S}_0 b`$ であり、
  [T.le0_le](#t-le0_le) より $`l \le b \lt \lvert S\rvert`$ である。
  仮定の第 6 条件の全称変数に $`l`$ を代入して $`S_{1,b} \le S_{1,l}`$ を得る。
  [T.entry_shift](#t-entry_shift) が $`j := l`$ と $`j := b`$ で使えて、
  この不等式は $`(S^{+d})_{1,b} \le (S^{+d})_{1,l}`$ に等しい。∎
