[← README](README.md) ｜ Wset **1** [2](Wset-2.md) [3](Wset-3.md) [4](Wset-4.md)

<a id="t-translate_eq_Z_iff"></a>
## 定理: 翻訳が $`\mathsf{Z}`$ になるのは空列に限る (T.translate_eq_Z_iff)

### 定理

$`M \in \mathrm{PairSeq}`$（[D.PairSeq](Pss.md#d-PairSeq)）に対し

```math
\mathrm{tr}\,M = \mathsf{Z} \iff M = () .
```

ここで $`\mathrm{tr}`$（[D.translate](Term.md#d-translate)）は翻訳であり、$`\mathsf{Z}`$ は
$`\mathrm{Three}`$（[D.Three](Term.md#d-Three)）の第 1 の構成子である。

### 証明

$`M`$ の構成子で場合分けする。

- $`M = ()`$ のとき。$`\mathrm{tr}`$ の定義（D.translate）の第 1 式より
  $`\mathrm{tr}\,() = \mathsf{Z}`$ であるから左辺の等式は成り立つ。右辺の等式 $`() = ()`$ も
  $`=`$ の反射性により成り立つ。よって両辺は同値である。

- $`M = p :: L`$ のとき。$`\mathrm{tr}`$ の定義（D.translate）の第 2 式より
  $`\mathrm{tr}(p :: L) = \mathsf{P}\bigl(p_2, \mathrm{tr}(\mathrm{tw}_{p_1} L), \mathrm{tr}(\mathrm{dw}_{p_1} L)\bigr)`$
  である。$`\mathrm{Three}`$ の構成子の像は互いに交わらない（D.Three）から
  $`\mathsf{P}(\cdot,\cdot,\cdot) \ne \mathsf{Z}`$ であり、左辺の等式は偽である。
  また $`p :: L`$ の長さは $`1`$ 以上であり $`\lvert()\rvert = 0`$ であるから
  $`p :: L \ne ()`$ であり、右辺の等式も偽である。よって両辺は同値である。∎

<a id="t-eq_Z_of_olt_one"></a>
## 定理: $`\mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$ より小さい項は $`\mathsf{Z}`$ のみ (T.eq_Z_of_olt_one)

### 定理

$`t \in \mathrm{Three}`$ が $`t \prec \mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$（[D.olt](Term.md#d-olt)）を
みたすならば $`t = \mathsf{Z}`$。

### 証明

$`t`$ の構成子で場合分けする。

- $`t = \mathsf{Z}`$ のとき。示すべき $`\mathsf{Z} = \mathsf{Z}`$ は $`=`$ の反射性による。

- $`t = \mathsf{P}(a,b,c)`$ のとき。[T.olt_P_P](Term.md#t-olt_P_P) を
  $`e := 0`$、$`f := \mathsf{Z}`$、$`g := \mathsf{Z}`$ として適用すると、仮定は次の 3 つの
  いずれかである。
  - $`a \lt 0`$。自然数に $`0`$ より小さいものはないから偽である。
  - $`a = 0 \wedge b \prec \mathsf{Z}`$。[T.not_olt_Z](Term.md#t-not_olt_Z) より
    $`b \prec \mathsf{Z}`$ は偽である。
  - $`a = 0 \wedge b = \mathsf{Z} \wedge c \prec \mathsf{Z}`$。同じく
    [T.not_olt_Z](Term.md#t-not_olt_Z) より $`c \prec \mathsf{Z}`$ は偽である。

  3 つとも偽であるから、この場合は起こらない。∎

<a id="t-stps_ne_nil"></a>
## 定理: 標準形は空でない (T.stps_ne_nil)

### 定理

$`M \in \mathrm{ST\_PS}`$（[D.ST_PS](Pss.md#d-ST_PS)）ならば $`M \ne ()`$。

### 証明

$`M = ()`$ と仮定する。[T.stps_len_pos](Column.md#t-stps_len_pos) より $`0 \lt \lvert M\rvert`$ で
あるが、仮定を代入すると $`\lvert()\rvert = 0`$ であるから $`0 \lt 0`$ となり、
$`\lt`$ の非反射性に矛盾する。∎

<a id="t-stps_len_one"></a>
## 定理: 長さ $`1`$ の標準形 (T.stps_len_one)

### 定理

$`M \in \mathrm{ST\_PS}`$ かつ $`\lvert M\rvert = 1`$ ならば $`M = \bigl((0,0)\bigr)`$。

### 証明

$`\lvert M\rvert = 1`$ であるから $`M = (p)`$ なる対 $`p`$ が取れる。
[T.stps_head](Column.md#t-stps_head) は「$`M`$ の先頭要素（$`M`$ が空列のときは $`(0,0)`$）が
$`(0,0)`$ に等しい」ことを言う。$`M = (p)`$ の先頭要素は $`p`$ であるから $`p = (0,0)`$ であり、
$`M = \bigl((0,0)\bigr)`$。∎

<a id="d-domT"></a>
## 定義: 行 $`1`$ の孤児 (D.domT)

$`M \in \mathrm{PairSeq}`$、$`m \in \mathbb{N}`$ に対し

```math
\mathrm{domT}(M,m) :\iff
M_{1,\lvert M\rvert-1} = m+1 \ \wedge\ \neg\,\mathrm{hasParent}(M, 1, \lvert M\rvert-1)
```

とおく。ここで $`M_{i,j}`$（[D.entry](Pss.md#d-entry)）は成分、
$`\mathrm{hasParent}(M,i,j)`$（[D.hasParent](Pss.md#d-hasParent)）は親の存在であり、
$`\lvert M\rvert - 1`$ の減法は切り捨て減法である（$`M = ()`$ のとき $`\lvert M\rvert - 1 = 0`$）。

<a id="d-graft"></a>
## 定義: 接ぎ木 (D.graft)

$`L \in \mathrm{PairSeq}`$、$`e \in \mathbb{N}`$ に対し、$`L`$ の各対の第 1 成分に $`e`$ を
足した列を $`L^{+e}`$ と書く（[T.translate_shift](Term.md#t-translate_shift) の記法）。
また $`\mathrm{dropLast}\,M`$ を $`M`$ の末尾 1 要素を落とした列とする
（$`M = ()`$ のときは $`()`$）。$`M, z \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{graft}(M, z) := \mathrm{dropLast}\,M \mathbin{+\!\!+} z^{+M_{0,\lvert M\rvert-1}}
```

とおく。

<a id="d-based"></a>
## 定義: 深さ $`0`$ への錨づけ (D.based)

$`z \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{based}(z) :\iff z_{0,0} = 0 .
```

<a id="t-based_nil"></a>
## 定理: 空列は深さ $`0`$ に錨づけられている (T.based_nil)

### 定理

$`\mathrm{based}(())`$。

### 証明

$`M_{i,j}`$ の定義（D.entry）により、$`0 \ge \lvert()\rvert = 0`$ であるから
$`()\langle 0\rangle = (0,0)`$ であり、その第 1 成分をとって $`()_{0,0} = 0`$。
これが $`\mathrm{based}`$ の定義（D.based）の右辺である。∎

<a id="t-graft_nil"></a>
## 定理: 空ブロックの接ぎ木 (T.graft_nil)

### 定理

任意の $`M \in \mathrm{PairSeq}`$ に対し $`\mathrm{graft}(M, ()) = \mathrm{dropLast}\,M`$。

### 証明

空列の各対の第 1 成分に $`e`$ を足しても要素は増えないから $`()^{+e} = ()`$ である。
よって $`\mathrm{graft}`$ の定義（D.graft）より

```math
\mathrm{graft}(M,()) = \mathrm{dropLast}\,M \mathbin{+\!\!+} () = \mathrm{dropLast}\,M . \qquad \blacksquare
```

<a id="t-not_domT_nil"></a>
## 定理: 空列は孤児条件をみたさない (T.not_domT_nil)

### 定理

任意の $`m \in \mathbb{N}`$ に対し $`\neg\,\mathrm{domT}((), m)`$。

### 証明

$`\mathrm{domT}((),m)`$ を仮定する。$`\mathrm{domT}`$ の定義（D.domT）の第 1 連言子は
$`()_{1,\lvert()\rvert-1} = m+1`$ である。$`\lvert()\rvert - 1 = 0`$（切り捨て減法）であり、
$`M_{i,j}`$ の定義（D.entry）より $`()_{1,0} = 0`$ であるから、この等式は $`0 = m+1`$ となる。
自然数において $`m + 1 \ne 0`$ であるから矛盾である。∎

<a id="d-natDom"></a>
## 定義: 孤児条件の否定 (D.natDom)

$`M \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{natDom}(M) :\iff \forall m \in \mathbb{N},\ \neg\,\mathrm{domT}(M,m).
```

<a id="t-natDom_iff"></a>
## 定理: 孤児条件の否定の言い換え (T.natDom_iff)

### 定理

$`M \in \mathrm{PairSeq}`$ に対し、$`j_1 := \lvert M\rvert - 1`$ と書くと

```math
\mathrm{natDom}(M) \iff
\bigl(M_{1,j_1} = 0 \ \vee\ \mathrm{hasParent}(M,1,j_1)\bigr).
```

### 証明

両方向を示す。

**($`\Rightarrow`$)** $`\mathrm{natDom}(M)`$ を仮定する。$`M_{1,j_1} = 0`$ が成り立つかどうかで
場合分けする。

- $`M_{1,j_1} = 0`$ のとき。右辺の第 1 選言そのものである。

- $`M_{1,j_1} \ne 0`$ のとき。右辺の第 2 選言 $`\mathrm{hasParent}(M,1,j_1)`$ を背理法で示す。
  $`\neg\,\mathrm{hasParent}(M,1,j_1)`$ と仮定する。$`M_{1,j_1} \ne 0`$ であるから
  $`m := M_{1,j_1} - 1`$ とおけば $`M_{1,j_1} = m+1`$ である。よって $`\mathrm{domT}`$ の
  定義（D.domT）の 2 つの連言子がともに成り立ち $`\mathrm{domT}(M,m)`$ となるが、
  $`\mathrm{natDom}`$ の定義（D.natDom）をこの $`m`$ に適用した
  $`\neg\,\mathrm{domT}(M,m)`$ に矛盾する。

**($`\Leftarrow`$)** 右辺を仮定する。$`\mathrm{natDom}`$ の定義（D.natDom）により、$`m`$ を
取り $`\mathrm{domT}(M,m)`$ すなわち $`M_{1,j_1} = m+1`$ と
$`\neg\,\mathrm{hasParent}(M,1,j_1)`$ を仮定して矛盾を導けばよい。右辺の選言で場合分けする。

- $`M_{1,j_1} = 0`$ のとき。$`m + 1 = M_{1,j_1} = 0`$ となるが、自然数において
  $`m+1 \ne 0`$ であるから矛盾である。

- $`\mathrm{hasParent}(M,1,j_1)`$ のとき。$`\mathrm{domT}(M,m)`$ の第 2 連言子
  $`\neg\,\mathrm{hasParent}(M,1,j_1)`$ に矛盾する。∎

<a id="t-oper_eq_graft_nil_of_domT"></a>
## 定理: 孤児条件の下での展開 (T.oper_eq_graft_nil_of_domT)

### 定理

$`1 \lt \lvert M\rvert`$ かつ $`\mathrm{domT}(M,m)`$ ならば、任意の $`n \in \mathbb{N}`$ に対し
$`M[n] = \mathrm{graft}(M,())`$（[D.oper](Pss.md#d-oper)）。

### 証明

$`j_1 := \lvert M\rvert - 1`$ と書く。$`\mathrm{domT}`$ の定義（D.domT）より
$`M_{1,j_1} = m+1`$ と $`\neg\,\mathrm{hasParent}(M,1,j_1)`$ が成り立つ。次の 5 つを順に示す。

1. $`j_1 \ne 0`$。$`1 \lt \lvert M\rvert`$ より $`j_1 = \lvert M\rvert - 1 \ge 1`$ である。

2. $`\mathrm{idx}_1(M,j_1) = 1`$。$`M_{1,j_1} = m+1`$ であり自然数について $`0 \lt m+1`$ で
   あるから、$`\mathrm{idx}_1`$（[D.idx1](Pss.md#d-idx1)）の定義（D.idx1）の第 1 の場合が選ばれる。

3. $`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$。この連言が成り立つとすると
   第 2 連言子から $`m+1 = 0`$ となり、$`m+1 \ne 0`$ に矛盾する。

4. $`M[n] = \mathrm{Pred}\,M`$。2 により $`\mathrm{idx}_1(M,j_1) = 1`$ であるから、
   $`\neg\,\mathrm{hasParent}\bigl(M, \mathrm{idx}_1(M,j_1), j_1\bigr)`$ は仮定
   $`\neg\,\mathrm{hasParent}(M,1,j_1)`$ そのものである。1, 3 とこれに
   [T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) を適用する。

5. $`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$。$`\mathrm{Pred}`$（[D.Pred](Pss.md#d-Pred)）の
   定義（D.Pred）は $`\lvert M\rvert \le 1`$ かどうかで分岐する。仮定 $`1 \lt \lvert M\rvert`$ より
   $`\lvert M\rvert \le 1`$ は偽であるから第 2 の場合が選ばれ、末尾 1 列を落とした列になる。

最後に [T.graft_nil](#t-graft_nil) より $`\mathrm{graft}(M,()) = \mathrm{dropLast}\,M`$ である。
4, 5 とこれを合わせて $`M[n] = \mathrm{graft}(M,())`$ を得る。∎

<a id="d-r1cand"></a>
## 定義: 行 $`1`$ の親候補 (D.r1cand)

$`M \in \mathrm{PairSeq}`$、$`j_1, j_0 \in \mathbb{N}`$ に対し

```math
\mathrm{r1cand}(M,j_1,j_0) :\iff
j_0 \lt j_1 \ \wedge\ j_0 \le^M_0 j_1 \ \wedge\ M_{1,j_0} \lt M_{1,j_1}
```

とおく。ここで $`j_0 \le^M_0 j_1`$（[D.le0](Pss.md#d-le0)）は行 $`0`$ の祖先関係である。

<a id="t-hasParent_one_iff"></a>
## 定理: 行 $`1`$ の親の存在条件 (T.hasParent_one_iff)

### 定理

$`j_1 \lt \lvert M\rvert`$ ならば

```math
\mathrm{hasParent}(M,1,j_1) \iff \exists j_0,\ \mathrm{r1cand}(M,j_1,j_0).
```

### 証明

$`\to^M_i`$（[D.nextR](Pss.md#d-nextR)）の定義（D.nextR）は $`i = 0`$ かどうかで分岐する。
$`i = 1 \ne 0`$ であるから、任意の $`j_0`$ について $`j_0 \to^M_i j_1`$ は
行 $`1`$ の親子関係 $`j_0 \to^M_1 j_1`$（[D.nextrel1](Pss.md#d-nextrel1)）そのものである。以下これを用いる。

**($`\Rightarrow`$)** $`\mathrm{hasParent}`$ の定義（D.hasParent）より、
$`j_0 \to^M_1 j_1`$ をみたす $`j_0`$ が存在する。D.nextrel1 の条件 (3), (5), (4) は
それぞれ $`j_0 \lt j_1`$、$`j_0 \le^M_0 j_1`$、$`M_{1,j_0} \lt M_{1,j_1}`$ であり、これは
$`\mathrm{r1cand}`$ の定義（D.r1cand）の 3 つの連言子である。よって
$`\mathrm{r1cand}(M,j_1,j_0)`$。

**($`\Leftarrow`$)** $`\mathrm{r1cand}(M,j_1,j_0)`$ なる $`j_0`$ を取る。述語 $`P`$ を

```math
P(k) :\equiv \mathrm{r1cand}(M,j_1,k)
```

で定める。$`\{\,k \mid k \le j_1 \wedge P(k)\,\}`$ は有限集合であり、
$`\mathrm{r1cand}`$ の第 1 連言子より $`j_0 \lt j_1`$、したがって $`j_0 \le j_1`$ であるから
$`j_0`$ を元にもち空でない。その最大元を $`g`$ とおく。すなわち

```math
P(g), \qquad \forall k,\ \bigl(k \le j_1 \wedge P(k)\bigr) \to k \le g .
```

**第 1 段：$`g \to^M_1 j_1`$。** D.nextrel1 の 6 条件を順に確かめる。

- (1) $`g \lt \lvert M\rvert`$：$`P(g)`$ の第 1 連言子より $`g \lt j_1`$ であり、仮定
  $`j_1 \lt \lvert M\rvert`$ と $`\lt`$ の推移律による。
- (2) $`j_1 \lt \lvert M\rvert`$：仮定そのものである。
- (3) $`g \lt j_1`$：$`P(g)`$ の第 1 連言子である。
- (4) $`M_{1,g} \lt M_{1,j_1}`$：$`P(g)`$ の第 3 連言子である。
- (5) $`g \le^M_0 j_1`$：$`P(g)`$ の第 2 連言子である。
- (6) 任意の $`j`$ について $`g \lt j`$ かつ $`j \le^M_0 j_1`$ ならば
  $`M_{1,j_1} \le M_{1,j}`$：背理法で示す。$`M_{1,j} \lt M_{1,j_1}`$ と仮定する。
  $`\le^M_0`$ の定義（D.le0）の条件 (3) より
  $`j \mathbin{(\to^M_0)^{*}} j_1`$（[D.nextrel0](Pss.md#d-nextrel0)）であるから、
  [T.nextrel0_rtrancl_index_le](Term.md#t-nextrel0_rtrancl_index_le) より $`j \le j_1`$。
  $`j = j_1`$ とすると $`M_{1,j_1} \lt M_{1,j_1}`$ となり $`\lt`$ の非反射性に矛盾する。
  $`j \lt j_1`$ のときは、$`j \lt j_1`$、$`j \le^M_0 j_1`$、$`M_{1,j} \lt M_{1,j_1}`$ の
  3 つがそろうから $`P(j)`$ が成り立ち、$`j \le j_1`$ と最大性から $`j \le g`$ となって、
  いま仮定した $`g \lt j`$ に矛盾する。

**第 2 段：一意性。** $`y \to^M_1 j_1`$ とする。D.nextrel1 の条件 (3), (5), (4) より
$`P(y)`$ が成り立ち、条件 (3) より $`y \lt j_1`$ すなわち $`y \le j_1`$ であるから、
最大性より $`y \le g`$ である。$`y = g`$ でないとすると $`y \lt g`$ である。
$`y \to^M_1 j_1`$ の条件 (6) を $`j := g`$ に適用する。その前件 $`y \lt g`$ は
いまの仮定であり、$`g \le^M_0 j_1`$ は第 1 段の (5) であるから、
$`M_{1,j_1} \le M_{1,g}`$ を得る。一方、第 1 段の (4) は $`M_{1,g} \lt M_{1,j_1}`$ で
あるから $`M_{1,j_1} \lt M_{1,j_1}`$ となり、$`\lt`$ の非反射性に矛盾する。よって $`y = g`$。

第 1 段と第 2 段により、$`j_0 \to^M_1 j_1`$ をみたす $`j_0`$ は存在し一意である。
$`\mathrm{hasParent}`$ の定義（D.hasParent）よりこれが $`\mathrm{hasParent}(M,1,j_1)`$ である。∎

<a id="t-domT_iff"></a>
## 定理: 孤児条件の脊柱による言い換え (T.domT_iff)

### 定理

$`M \ne ()`$ とし $`j_1 := \lvert M\rvert - 1`$ と書く。このとき

```math
\mathrm{domT}(M,m) \iff \Bigl(M_{1,j_1} = m+1 \ \wedge\
  \forall j_0,\ \bigl(j_0 \lt j_1 \wedge j_0 \le^M_0 j_1\bigr) \to m+1 \le M_{1,j_0}\Bigr).
```

### 証明

$`M \ne ()`$ より $`0 \lt \lvert M\rvert`$ であり、切り捨て減法により
$`j_1 = \lvert M\rvert - 1 \lt \lvert M\rvert`$ である。よって
[T.hasParent_one_iff](#t-hasParent_one_iff) が使えて

```math
\mathrm{hasParent}(M,1,j_1) \iff \exists j_0,\ \mathrm{r1cand}(M,j_1,j_0)
```

である。$`\mathrm{domT}`$ の定義（D.domT）は $`M_{1,j_1} = m+1`$ と
$`\neg\,\mathrm{hasParent}(M,1,j_1)`$ の連言であるから、両辺の第 1 連言子は共通であり、
示すべきことは $`M_{1,j_1} = m+1`$ を仮定した上での

```math
\neg\,\exists j_0,\ \mathrm{r1cand}(M,j_1,j_0)
\iff \forall j_0,\ \bigl(j_0 \lt j_1 \wedge j_0 \le^M_0 j_1\bigr) \to m+1 \le M_{1,j_0}
```

である。

**($`\Rightarrow`$)** 左辺を仮定する。$`j_0`$ を取り $`j_0 \lt j_1`$ かつ
$`j_0 \le^M_0 j_1`$ とし、$`m+1 \le M_{1,j_0}`$ を背理法で示す。
$`M_{1,j_0} \lt m+1`$ とすると、$`M_{1,j_1} = m+1`$ であるから
$`M_{1,j_0} \lt M_{1,j_1}`$ である。これと $`j_0 \lt j_1`$、$`j_0 \le^M_0 j_1`$ を
合わせると $`\mathrm{r1cand}`$ の定義（D.r1cand）の 3 連言子がそろい
$`\mathrm{r1cand}(M,j_1,j_0)`$ となって、左辺に矛盾する。

**($`\Leftarrow`$)** 右辺を仮定し、$`\mathrm{r1cand}(M,j_1,j_0)`$ なる $`j_0`$ が
存在したとして矛盾を導く。その第 1 連言子 $`j_0 \lt j_1`$ と第 2 連言子
$`j_0 \le^M_0 j_1`$ に右辺を適用して $`m+1 \le M_{1,j_0}`$ を得る。第 3 連言子は
$`M_{1,j_0} \lt M_{1,j_1} = m+1`$ である。合わせて $`m+1 \le M_{1,j_0} \lt m+1`$ となり、
$`\lt`$ の非反射性に矛盾する。∎

<a id="d-lfpS"></a>
## 定義: 最小不動点 (D.lfpS)

$`f`$ を $`\mathrm{PairSeq}`$ の部分集合から $`\mathrm{PairSeq}`$ の部分集合への写像とする。

```math
\mathrm{lfp}(f) := \bigcap\,\bigl\{\, Y \subseteq \mathrm{PairSeq} \ \bigm|\ f(Y) \subseteq Y \,\bigr\}
```

とおく。すなわち $`x \in \mathrm{lfp}(f)`$ は、$`f(Y) \subseteq Y`$ をみたす**すべての**
$`Y \subseteq \mathrm{PairSeq}`$ について $`x \in Y`$ であることを言う。

<a id="t-lfpS_lowerbound"></a>
## 定理: 最小不動点は前不動点の下界 (T.lfpS_lowerbound)

### 定理

$`f(Y) \subseteq Y`$ ならば $`\mathrm{lfp}(f) \subseteq Y`$。

### 証明

$`x \in \mathrm{lfp}(f)`$ とする。$`\mathrm{lfp}`$ の定義（D.lfpS）より、$`x`$ は
$`f(Z) \subseteq Z`$ をみたすすべての $`Z`$ に属する。仮定より $`Y`$ はそのような $`Z`$ の
1 つであるから $`x \in Y`$。∎

<a id="t-lfpS_unfold_le"></a>
## 定理: 最小不動点の展開（$`\subseteq`$ 向き） (T.lfpS_unfold_le)

### 定理

$`f`$ が単調、すなわち $`X \subseteq Y`$ ならば $`f(X) \subseteq f(Y)`$ であるとする。
このとき $`f(\mathrm{lfp}(f)) \subseteq \mathrm{lfp}(f)`$。

### 証明

$`x \in f(\mathrm{lfp}(f))`$ とする。$`\mathrm{lfp}`$ の定義（D.lfpS）より、
$`f(Y) \subseteq Y`$ をみたす任意の $`Y`$ について $`x \in Y`$ を示せばよい。
[T.lfpS_lowerbound](#t-lfpS_lowerbound) より $`\mathrm{lfp}(f) \subseteq Y`$ であり、
$`f`$ の単調性より $`f(\mathrm{lfp}(f)) \subseteq f(Y)`$。よって $`x \in f(Y)`$ であり、
仮定 $`f(Y) \subseteq Y`$ より $`x \in Y`$。∎

<a id="t-lfpS_unfold_ge"></a>
## 定理: 最小不動点の展開（$`\supseteq`$ 向き） (T.lfpS_unfold_ge)

### 定理

$`f`$ が単調ならば $`\mathrm{lfp}(f) \subseteq f(\mathrm{lfp}(f))`$。

### 証明

[T.lfpS_lowerbound](#t-lfpS_lowerbound) を $`Y := f(\mathrm{lfp}(f))`$ に適用する。
その仮定は $`f\bigl(f(\mathrm{lfp}(f))\bigr) \subseteq f(\mathrm{lfp}(f))`$ であり、
これは [T.lfpS_unfold_le](#t-lfpS_unfold_le) の結論
$`f(\mathrm{lfp}(f)) \subseteq \mathrm{lfp}(f)`$ に $`f`$ の単調性を適用して得られる。∎

<a id="t-lfpS_unfold"></a>
## 定理: 最小不動点は不動点 (T.lfpS_unfold)

### 定理

$`f`$ が単調ならば $`f(\mathrm{lfp}(f)) = \mathrm{lfp}(f)`$。

### 証明

[T.lfpS_unfold_le](#t-lfpS_unfold_le) より $`f(\mathrm{lfp}(f)) \subseteq \mathrm{lfp}(f)`$ で
あり、[T.lfpS_unfold_ge](#t-lfpS_unfold_ge) より
$`\mathrm{lfp}(f) \subseteq f(\mathrm{lfp}(f))`$ である。$`\subseteq`$ の反対称性により
両者は等しい。∎

<a id="d-Aop"></a>
## 定義: 作用素 $`A_u`$ (D.Aop)

$`\mathcal{W}`$ を、各 $`m \in \mathbb{N}`$ に $`\mathrm{PairSeq}`$ の部分集合
$`\mathcal{W}(m)`$ を与える族とし、$`u \in \mathbb{N}`$、$`X \subseteq \mathrm{PairSeq}`$、
$`M \in \mathrm{PairSeq}`$ とする。次の 3 つの命題を考える。

```math
\begin{aligned}
&(1)\quad \lvert M\rvert \le 1 \ \wedge\ M_{1,0} = 0, \cr
&(2)\quad \mathrm{natDom}(M) \ \wedge\ \forall n \ge 1,\ M[n] \in X, \cr
&(3)\quad \exists m \lt u,\ \Bigl(\mathrm{domT}(M,m) \ \wedge\
  \forall z \in \mathcal{W}(m),\ \mathrm{based}(z) \to \mathrm{graft}(M,z) \in X\Bigr).
\end{aligned}
```

これらを用いて

```math
\mathrm{Aop}(\mathcal{W},u,X,M) :\iff (1) \ \vee\ (2) \ \vee\ (3)
```

と定める。以下、この 3 つをそれぞれ**分岐 (1) **、**分岐 (2) **、**分岐 (3) ** と呼ぶ。

<a id="d-Aset"></a>
## 定義: 作用素 $`A_u`$ の集合形 (D.Aset)

```math
\mathrm{Aset}(\mathcal{W},u,X) := \bigl\{\, M \in \mathrm{PairSeq} \ \bigm|\ \mathrm{Aop}(\mathcal{W},u,X,M) \,\bigr\} .
```

<a id="t-Aop_mono_X"></a>
## 定理: $`A_u`$ の第 3 引数についての単調性 (T.Aop_mono_X)

### 定理

$`\mathrm{Aop}(\mathcal{W},u,X,M)`$ かつ $`X \subseteq Y`$ ならば
$`\mathrm{Aop}(\mathcal{W},u,Y,M)`$。

### 証明

$`\mathrm{Aop}`$ の定義（D.Aop）の 3 つの選言で場合分けする。

- **分岐 (1) ** のとき。$`\lvert M\rvert \le 1 \wedge M_{1,0} = 0`$ には $`X`$ が現れないから、
  そのまま $`\mathrm{Aop}(\mathcal{W},u,Y,M)`$ の分岐 (1) が成り立つ。

- **分岐 (2) ** のとき。第 1 連言子 $`\mathrm{natDom}(M)`$ はそのまま成り立つ。
  第 2 連言子については、$`1 \le n`$ なる各 $`n`$ について $`M[n] \in X`$ であり、
  $`X \subseteq Y`$ より $`M[n] \in Y`$。よって分岐 (2) が成り立つ。

- **分岐 (3) ** のとき。$`m \lt u`$ と $`\mathrm{domT}(M,m)`$ はそのまま成り立つ。
  第 3 連言子については、$`z \in \mathcal{W}(m)`$ かつ $`\mathrm{based}(z)`$ なる各 $`z`$ に
  ついて $`\mathrm{graft}(M,z) \in X`$ であり、$`X \subseteq Y`$ より
  $`\mathrm{graft}(M,z) \in Y`$。よって同じ $`m`$ で分岐 (3) が成り立つ。∎

<a id="t-Aset_mono"></a>
## 定理: $`A_u`$ は単調 (T.Aset_mono)

### 定理

任意の $`\mathcal{W}`$, $`u`$ について、写像 $`X \mapsto \mathrm{Aset}(\mathcal{W},u,X)`$ は
単調である。すなわち $`X \subseteq Y`$ ならば
$`\mathrm{Aset}(\mathcal{W},u,X) \subseteq \mathrm{Aset}(\mathcal{W},u,Y)`$。

### 証明

$`X \subseteq Y`$ とし $`M \in \mathrm{Aset}(\mathcal{W},u,X)`$ とする。
$`\mathrm{Aset}`$ の定義（D.Aset）よりこれは $`\mathrm{Aop}(\mathcal{W},u,X,M)`$ である。
[T.Aop_mono_X](#t-Aop_mono_X) より $`\mathrm{Aop}(\mathcal{W},u,Y,M)`$ であり、
ふたたび D.Aset より $`M \in \mathrm{Aset}(\mathcal{W},u,Y)`$。∎

<a id="t-Aop_mono_level"></a>
## 定理: $`A_u`$ の段についての単調性 (T.Aop_mono_level)

### 定理

$`u \le v`$ かつ $`\mathrm{Aop}(\mathcal{W},u,X,M)`$ ならば
$`\mathrm{Aop}(\mathcal{W},v,X,M)`$。

### 証明

$`\mathrm{Aop}`$ の定義（D.Aop）の 3 つの選言で場合分けする。

- **分岐 (1) ** のとき。$`u`$ が現れないから、そのまま成り立つ。
- **分岐 (2) ** のとき。$`u`$ が現れないから、そのまま成り立つ。
- **分岐 (3) ** のとき。$`m \lt u`$ なる $`m`$ が取れている。$`u \le v`$ と合わせて
  $`m \lt v`$ であり、残りの 2 つの連言子 $`\mathrm{domT}(M,m)`$ と
  $`\forall z \in \mathcal{W}(m),\ \mathrm{based}(z) \to \mathrm{graft}(M,z) \in X`$ は
  $`u`$ にも $`v`$ にも依らないからそのまま成り立つ。∎

<a id="t-Aop_cong"></a>
## 定理: $`A_u`$ は $`u`$ 未満の段しか読まない (T.Aop_cong)

### 定理

$`\mathcal{W}`$, $`\mathcal{V}`$ を族とし、$`\forall m \lt u,\ \mathcal{W}(m) = \mathcal{V}(m)`$ と
する。このとき

```math
\mathrm{Aop}(\mathcal{W},u,X,M) \iff \mathrm{Aop}(\mathcal{V},u,X,M).
```

### 証明

両方向を示す。

**($`\Rightarrow`$)** $`\mathrm{Aop}(\mathcal{W},u,X,M)`$ の 3 つの選言で場合分けする。

- **分岐 (1) ** のとき。族が現れないから、$`\mathrm{Aop}(\mathcal{V},u,X,M)`$ の分岐 (1) が
  そのまま成り立つ。
- **分岐 (2) ** のとき。族が現れないから、分岐 (2) がそのまま成り立つ。
- **分岐 (3) ** のとき。$`m \lt u`$、$`\mathrm{domT}(M,m)`$、および
  $`\forall z \in \mathcal{W}(m),\ \mathrm{based}(z) \to \mathrm{graft}(M,z) \in X`$ が
  取れている。同じ $`m`$ で $`\mathrm{Aop}(\mathcal{V},u,X,M)`$ の分岐 (3) を示す。
  $`m \lt u`$ と $`\mathrm{domT}(M,m)`$ はそのままである。$`z \in \mathcal{V}(m)`$ かつ
  $`\mathrm{based}(z)`$ とすると、仮定を $`m \lt u`$ に適用した等式
  $`\mathcal{W}(m) = \mathcal{V}(m)`$ により $`z \in \mathcal{W}(m)`$ であるから、
  取れている連言子を適用して $`\mathrm{graft}(M,z) \in X`$。

**($`\Leftarrow`$)** $`\mathrm{Aop}(\mathcal{V},u,X,M)`$ の 3 つの選言で場合分けする。

- **分岐 (1) ** のとき。族が現れないから、$`\mathrm{Aop}(\mathcal{W},u,X,M)`$ の分岐 (1) が
  そのまま成り立つ。
- **分岐 (2) ** のとき。族が現れないから、分岐 (2) がそのまま成り立つ。
- **分岐 (3) ** のとき。$`m \lt u`$、$`\mathrm{domT}(M,m)`$、および
  $`\forall z \in \mathcal{V}(m),\ \mathrm{based}(z) \to \mathrm{graft}(M,z) \in X`$ が
  取れている。同じ $`m`$ で $`\mathrm{Aop}(\mathcal{W},u,X,M)`$ の分岐 (3) を示す。
  $`m \lt u`$ と $`\mathrm{domT}(M,m)`$ はそのままである。$`z \in \mathcal{W}(m)`$ かつ
  $`\mathrm{based}(z)`$ とすると、等式 $`\mathcal{W}(m) = \mathcal{V}(m)`$ を逆向きに
  用いて $`z \in \mathcal{V}(m)`$ であるから、取れている連言子を適用して
  $`\mathrm{graft}(M,z) \in X`$。∎

<a id="d-Wf"></a>
## 定義: 段の族 (D.Wf)

$`\mathrm{Wf}`$ を、2 つの自然数 $`v, m`$ に $`\mathrm{PairSeq}`$ の部分集合
$`\mathrm{Wf}(v,m)`$ を与える写像として、第 1 引数についての再帰で定める。

```math
\mathrm{Wf}(0, m) := \emptyset, \qquad
\mathrm{Wf}(v+1, m) := \begin{cases}
\mathrm{lfp}\bigl(\mathrm{Aset}(\mathrm{Wf}(v,-),\ v)\bigr) & (m = v) \cr
\mathrm{Wf}(v, m) & (m \ne v)
\end{cases}
```

ここで $`\mathrm{Wf}(v,-)`$ は $`m \mapsto \mathrm{Wf}(v,m)`$ なる族であり、
$`\mathrm{Aset}(\mathrm{Wf}(v,-),v)`$ は $`X \mapsto \mathrm{Aset}(\mathrm{Wf}(v,-),v,X)`$ なる
写像である。再帰呼び出しの第 1 引数は $`v+1`$ に対して $`v`$ であり構造的に減少するから、
この定義は整合的である。

<a id="d-W"></a>
## 定義: 反復帰納的集合 $`W_u`$ (D.W)

$`u \in \mathbb{N}`$ に対し

```math
W_u := \mathrm{Wf}(u+1,\ u).
```

以下、$`W`$ を族 $`m \mapsto W_m`$ そのものを表す記号としても用いる。また
$`u \in \mathbb{N}`$、$`X \subseteq \mathrm{PairSeq}`$ に対し
$`A_u(X) := \mathrm{Aset}(W,u,X)`$ と略記する。$`\mathrm{Aset}`$ の定義（D.Aset）により
$`M \in A_u(X)`$ は $`\mathrm{Aop}(W,u,X,M)`$ を表す。

<a id="t-Wf_coh"></a>
## 定理: 段の族の整合性 (T.Wf_coh)

### 定理

$`m \lt n`$ ならば $`\mathrm{Wf}(n,m) = \mathrm{Wf}(m+1,m)`$。

### 証明

$`n`$ に関する自然数の帰納法（$`m`$ は固定する）。帰納法の述語は

```math
\Phi(n) :\equiv m \lt n \to \mathrm{Wf}(n,m) = \mathrm{Wf}(m+1,m).
```

- **基底段** $`n = 0`$：前件 $`m \lt 0`$ は偽であるから $`\Phi(0)`$ が成り立つ。

- **帰納段** $`n = v+1`$：帰納法の仮定は $`\Phi(v)`$、すなわち
  $`m \lt v \to \mathrm{Wf}(v,m) = \mathrm{Wf}(m+1,m)`$ である。$`m \lt v+1`$ を仮定し、
  $`m = v`$ かどうかで場合分けする。

  - $`m = v`$ のとき。示すべき等式は $`\mathrm{Wf}(v+1,v) = \mathrm{Wf}(v+1,v)`$ であり、
    $`=`$ の反射性により成り立つ。

  - $`m \ne v`$ のとき。$`m \lt v+1`$ より $`m \le v`$ であり、$`m \ne v`$ と合わせて
    $`m \lt v`$ である。$`\mathrm{Wf}`$ の定義（D.Wf）の第 2 式は $`m = v`$ かどうかで
    分岐し、いまは $`m \ne v`$ であるから $`\mathrm{Wf}(v+1,m) = \mathrm{Wf}(v,m)`$ で
    ある。帰納法の仮定 $`\Phi(v)`$ を $`m \lt v`$ に適用して
    $`\mathrm{Wf}(v,m) = \mathrm{Wf}(m+1,m)`$ を得る。合わせて
    $`\mathrm{Wf}(v+1,m) = \mathrm{Wf}(m+1,m)`$。∎

<a id="t-Wf_eq_W"></a>
## 定理: 段の族と $`W`$ の一致 (T.Wf_eq_W)

### 定理

$`m \lt n`$ ならば $`\mathrm{Wf}(n,m) = W_m`$。

### 証明

$`W_m`$ の定義（D.W）より $`W_m = \mathrm{Wf}(m+1,m)`$ である。
[T.Wf_coh](#t-Wf_coh) の結論がそのままこれである。∎

<a id="t-W_unfold"></a>
## 定理: $`W_u`$ の定義方程式 (T.W_unfold)

### 定理

任意の $`u \in \mathbb{N}`$ に対し

```math
W_u = \mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr).
```

### 証明

3 段に分ける。

**第 1 段：$`W_u = \mathrm{lfp}\bigl(\mathrm{Aset}(\mathrm{Wf}(u,-),u)\bigr)`$。**
$`W`$ の定義（D.W）より $`W_u = \mathrm{Wf}(u+1,u)`$ である。$`\mathrm{Wf}`$ の
定義（D.Wf）の第 2 式を $`v := u`$、$`m := u`$ で読むと、条件 $`m = v`$ が
$`u = u`$ として成り立つから第 1 の場合が選ばれ、値は
$`\mathrm{lfp}\bigl(\mathrm{Aset}(\mathrm{Wf}(u,-),u)\bigr)`$ である。

**第 2 段：$`\forall m \lt u,\ \mathrm{Wf}(u,m) = W_m`$。**
[T.Wf_eq_W](#t-Wf_eq_W) を $`n := u`$ として適用する。

**第 3 段：2 つの写像が等しい。** 任意の $`X \subseteq \mathrm{PairSeq}`$ について
$`\mathrm{Aset}(\mathrm{Wf}(u,-),u,X) = \mathrm{Aset}(W,u,X)`$ を示す。
$`\mathrm{Aset}`$ の定義（D.Aset）より、左辺の元は
$`\mathrm{Aop}(\mathrm{Wf}(u,-),u,X,M)`$ をみたす $`M`$、右辺の元は
$`\mathrm{Aop}(W,u,X,M)`$ をみたす $`M`$ である。第 2 段と
[T.Aop_cong](#t-Aop_cong)（$`\mathcal{W} := \mathrm{Wf}(u,-)`$、$`\mathcal{V} := W`$）より
この 2 つの命題は同値であるから、両辺は同じ元をもち等しい。よって写像
$`X \mapsto \mathrm{Aset}(\mathrm{Wf}(u,-),u,X)`$ と $`X \mapsto \mathrm{Aset}(W,u,X)`$ は
各点で等しく、写像として等しい。

第 3 段の等式を第 1 段の右辺に代入して結論を得る。∎

<a id="t-A1"></a>
## 定理: 不動点方程式 (A1) (T.A1)

### 定理

任意の $`u \in \mathbb{N}`$ に対し $`\mathrm{Aset}(W,u,W_u) = W_u`$。

### 証明

[T.W_unfold](#t-W_unfold) より $`W_u = \mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr)`$ である。
[T.Aset_mono](#t-Aset_mono) より写像 $`X \mapsto \mathrm{Aset}(W,u,X)`$ は単調であるから、
[T.lfpS_unfold](#t-lfpS_unfold) を $`f := \mathrm{Aset}(W,u)`$ に適用して

```math
\mathrm{Aset}\bigl(W,u,\mathrm{lfp}(\mathrm{Aset}(W,u))\bigr) = \mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr)
```

を得る。両辺の $`\mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr)`$ を $`W_u`$ に書き換えればよい。∎

<a id="t-A2"></a>
## 定理: 帰納法の原理 (A2) (T.A2)

### 定理

$`\mathrm{Aset}(W,u,Y) \subseteq Y`$ ならば $`W_u \subseteq Y`$。

### 証明

[T.W_unfold](#t-W_unfold) より $`W_u = \mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr)`$ である。
仮定に [T.lfpS_lowerbound](#t-lfpS_lowerbound) を $`f := \mathrm{Aset}(W,u)`$ として適用すると
$`\mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr) \subseteq Y`$ を得る。左辺を $`W_u`$ に
書き換えればよい。∎

<a id="t-A2'"></a>
## 定理: 帰納法の原理の各点形 (A2′) (T.A2')

### 定理

すべての $`M \in \mathrm{PairSeq}`$ について $`\mathrm{Aop}(W,u,Y,M) \to M \in Y`$ が
成り立つならば、$`W_u \subseteq Y`$。

### 証明

$`\mathrm{Aset}`$ の定義（D.Aset）より、$`M \in \mathrm{Aset}(W,u,Y)`$ と
$`\mathrm{Aop}(W,u,Y,M)`$ は同一の命題である。したがって仮定は
$`\mathrm{Aset}(W,u,Y) \subseteq Y`$ と同一の命題であり、
[T.A2](#t-A2) を適用して $`W_u \subseteq Y`$ を得る。∎

<a id="t-A1_intro"></a>
## 定理: $`W_u`$ への導入 (T.A1_intro)

### 定理

$`\mathrm{Aop}(W,u,W_u,M)`$ ならば $`M \in W_u`$。

### 証明

$`\mathrm{Aset}`$ の定義（D.Aset）より、仮定は $`M \in \mathrm{Aset}(W,u,W_u)`$ と
同一の命題である。[T.A1](#t-A1) の等式 $`\mathrm{Aset}(W,u,W_u) = W_u`$ でこれを
書き換えて $`M \in W_u`$ を得る。∎

<a id="t-W_nil"></a>
## 定理: 空列は $`W_u`$ に属する (W1) (T.W_nil)

### 定理

任意の $`u \in \mathbb{N}`$ に対し $`() \in W_u`$。

### 証明

[T.A1_intro](#t-A1_intro) を $`M := ()`$ に適用すればよいから、
$`\mathrm{Aop}(W,u,W_u,())`$ を示す。$`\mathrm{Aop}`$ の定義（D.Aop）の分岐 (1) を選ぶ。
その 2 つの連言子は次のように成り立つ。

- $`\lvert()\rvert \le 1`$：$`\lvert()\rvert = 0`$ である。
- $`()_{1,0} = 0`$：$`M_{i,j}`$ の定義（D.entry）により $`0 \ge \lvert()\rvert = 0`$ で
  あるから $`()\langle 0\rangle = (0,0)`$ であり、その第 2 成分は $`0`$ である。∎

<a id="t-W_mono"></a>
## 定理: $`W_u`$ の段についての単調性 (T.W_mono)

### 定理

$`u \le v`$ ならば $`W_u \subseteq W_v`$。

### 証明

[T.A2'](#t-A2') を $`Y := W_v`$ として適用する。その仮定を確かめればよい。
$`M \in \mathrm{PairSeq}`$ を取り $`\mathrm{Aop}(W,u,W_v,M)`$ とする。
[T.Aop_mono_level](#t-Aop_mono_level) を $`u \le v`$ に適用して
$`\mathrm{Aop}(W,v,W_v,M)`$ を得る。[T.A1_intro](#t-A1_intro) より $`M \in W_v`$。∎

<a id="d-Rst"></a>
## 定義: 標準形上の目標関係 (D.Rst)

$`a, b \in \mathrm{PairSeq}`$ に対し

```math
a \mathbin{R_{\mathrm{st}}} b :\iff
a \in \mathrm{ST\_PS} \ \wedge\ b \in \mathrm{ST\_PS} \ \wedge\ \mathrm{tr}\,a \prec \mathrm{tr}\,b .
```

<a id="t-acc_of_translate_eq"></a>
## 定理: 到達可能性は翻訳のみに依る (T.acc_of_translate_eq)

### 定理

以下、$`\mathrm{PairSeq}`$ 上の二項関係 $`R`$ と $`a \in \mathrm{PairSeq}`$ に対し、
$`\mathrm{Acc}(R,a)`$ を次の 1 つの規則で生成される最小の述語とする。

```math
\bigl(\forall y,\ y \mathbin{R} a \to \mathrm{Acc}(R,y)\bigr)
\ \Longrightarrow\ \mathrm{Acc}(R,a).
```

規則がこの 1 つだけであるから、逆に $`\mathrm{Acc}(R,a)`$ が成り立つときはその前提が
取り出せる。すなわち $`\mathrm{Acc}(R,a)`$ かつ $`y \mathbin{R} a`$ ならば
$`\mathrm{Acc}(R,y)`$ である。以下ではこれを**取り出し**と呼ぶ。

主張は次である。$`a \in \mathrm{ST\_PS}`$、$`\mathrm{tr}\,b = \mathrm{tr}\,a`$、
$`\mathrm{Acc}(R_{\mathrm{st}},a)`$ ならば $`\mathrm{Acc}(R_{\mathrm{st}},b)`$。

### 証明

$`\mathrm{Acc}`$ の生成規則により、$`y \mathbin{R_{\mathrm{st}}} b`$ なる任意の $`y`$ に
ついて $`\mathrm{Acc}(R_{\mathrm{st}},y)`$ を示せばよい。$`R_{\mathrm{st}}`$ の
定義（D.Rst）より、$`y \mathbin{R_{\mathrm{st}}} b`$ は $`y \in \mathrm{ST\_PS}`$、
$`b \in \mathrm{ST\_PS}`$、$`\mathrm{tr}\,y \prec \mathrm{tr}\,b`$ の連言である。

ここから $`y \mathbin{R_{\mathrm{st}}} a`$ を得る。3 つの連言子は次のように成り立つ。

- $`y \in \mathrm{ST\_PS}`$：いま得た第 1 連言子である。
- $`a \in \mathrm{ST\_PS}`$：仮定である。
- $`\mathrm{tr}\,y \prec \mathrm{tr}\,a`$：仮定の等式 $`\mathrm{tr}\,b = \mathrm{tr}\,a`$ を
  $`\mathrm{tr}\,y \prec \mathrm{tr}\,b`$ に代入したものである。

仮定 $`\mathrm{Acc}(R_{\mathrm{st}},a)`$ と $`y \mathbin{R_{\mathrm{st}}} a`$ に取り出しを
適用して $`\mathrm{Acc}(R_{\mathrm{st}},y)`$ を得る。∎

<a id="t-acc_of_nat_branch"></a>
## 定理: $`\mathbb{N}`$ 分岐の橋渡し (T.acc_of_nat_branch)

### 定理

次の仮定をおく。

```math
\text{(hcof)}\quad
\forall M, N \in \mathrm{ST\_PS},\ \mathrm{tr}\,N \prec \mathrm{tr}\,M \to
  \exists n,\ \bigl(1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])\bigr)
```

ここで $`\preceq`$（[D.ole](Term.md#d-ole)）は広義順序である。このとき、$`c \in \mathrm{ST\_PS}`$ であり
$`1 \le n`$ なるすべての $`n`$ について $`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$ が成り立つ
ならば、$`\mathrm{Acc}(R_{\mathrm{st}},c)`$。

### 証明

$`\mathrm{Acc}`$ の生成規則により、$`b \mathbin{R_{\mathrm{st}}} c`$ なる任意の $`b`$ に
ついて $`\mathrm{Acc}(R_{\mathrm{st}},b)`$ を示せばよい。$`R_{\mathrm{st}}`$ の
定義（D.Rst）より $`b \in \mathrm{ST\_PS}`$、$`c \in \mathrm{ST\_PS}`$、
$`\mathrm{tr}\,b \prec \mathrm{tr}\,c`$ である。

(hcof) を $`M := c`$、$`N := b`$ に適用して、$`1 \le n`$ かつ
$`\mathrm{tr}\,b \preceq \mathrm{tr}\,(c[n])`$ なる $`n`$ を取る。次の 2 つを用意する。

- $`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$：仮定を $`n`$ に適用したものである。
- $`c[n] \in \mathrm{ST\_PS}`$：$`\mathrm{ST\_PS}`$ の定義（D.ST_PS）の規則 (oper) を
  $`c \in \mathrm{ST\_PS}`$ と $`1 \le n`$ に適用したものである。

$`\preceq`$ の定義（D.ole）により $`\mathrm{tr}\,b \preceq \mathrm{tr}\,(c[n])`$ は
次の 2 つの場合に分かれる。

- $`\mathrm{tr}\,b \prec \mathrm{tr}\,(c[n])`$ のとき。$`b \mathbin{R_{\mathrm{st}}} c[n]`$ が
  成り立つ（3 つの連言子は $`b \in \mathrm{ST\_PS}`$、$`c[n] \in \mathrm{ST\_PS}`$、
  いまの狭義不等式である）。$`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$ に取り出しを適用して
  $`\mathrm{Acc}(R_{\mathrm{st}},b)`$。

- $`\mathrm{tr}\,b = \mathrm{tr}\,(c[n])`$ のとき。
  [T.acc_of_translate_eq](#t-acc_of_translate_eq) を $`a := c[n]`$、$`b := b`$ として
  適用する。その 3 つの仮定 $`c[n] \in \mathrm{ST\_PS}`$、
  $`\mathrm{tr}\,b = \mathrm{tr}\,(c[n])`$、$`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$ は
  いずれもいま得ている。結論が $`\mathrm{Acc}(R_{\mathrm{st}},b)`$ である。∎

<a id="t-acc_of_W"></a>
## 定理: 橋渡し（$`W_u`$ の元は到達可能） (T.acc_of_W)

### 定理

(hcof) を仮定する。このとき任意の $`u \in \mathbb{N}`$ と任意の $`M \in W_u`$ について
$`\mathrm{Acc}(R_{\mathrm{st}},M)`$。

### 証明

$`Y := \{\, M \in \mathrm{PairSeq} \mid \mathrm{Acc}(R_{\mathrm{st}},M) \,\}`$ とおくと、
示すべきことは $`W_u \subseteq Y`$ である。[T.A2'](#t-A2') を適用するので、
$`c \in \mathrm{PairSeq}`$ を取り $`\mathrm{Aop}(W,u,Y,c)`$ を仮定して
$`\mathrm{Acc}(R_{\mathrm{st}},c)`$ を示せばよい。$`c \in \mathrm{ST\_PS}`$ かどうかで
場合分けする。

**(I) $`c \notin \mathrm{ST\_PS}`$ のとき。**
$`\mathrm{Acc}`$ の生成規則により、$`y \mathbin{R_{\mathrm{st}}} c`$ なる任意の $`y`$ に
ついて $`\mathrm{Acc}(R_{\mathrm{st}},y)`$ を示せばよい。ところが $`R_{\mathrm{st}}`$ の
定義（D.Rst）の第 2 連言子は $`c \in \mathrm{ST\_PS}`$ であり、いまの場合の仮定に
反する。よってそのような $`y`$ は存在せず、前件が偽であるから
$`\mathrm{Acc}(R_{\mathrm{st}},c)`$ が成り立つ。

**(II) $`c \in \mathrm{ST\_PS}`$ のとき。**
$`\mathrm{Aop}(W,u,Y,c)`$ を $`\mathrm{Aop}`$ の定義（D.Aop）の 3 つの選言で場合分けする。

**分岐 (1)：$`\lvert c\rvert \le 1`$ かつ $`c_{1,0} = 0`$ のとき。**
[T.stps_len_pos](Column.md#t-stps_len_pos) より $`0 \lt \lvert c\rvert`$ であり、
$`\lvert c\rvert \le 1`$ と合わせて $`\lvert c\rvert = 1`$ である。よって $`c = (p)`$ なる
対 $`p = (p_1,p_2)`$ が取れる。$`M_{i,j}`$ の定義（D.entry）より
$`c_{1,0} = p_2`$ であるから $`p_2 = 0`$ である。

$`\mathrm{tr}\,c`$ を計算する。[T.translate_single_tree](Term.md#t-translate_single_tree) を
$`p := p`$、$`R := ()`$ として適用する（その仮定「$`R`$ のすべての要素 $`x`$ が
$`p_1 \lt x_1`$ をみたす」は $`R = ()`$ が要素をもたないから成り立つ）と

```math
\mathrm{tr}\,(p) = \mathsf{P}\bigl(p_2,\ \mathrm{tr}\,(),\ \mathsf{Z}\bigr)
= \mathsf{P}(0,\mathsf{Z},\mathsf{Z})
```

である（$`\mathrm{tr}\,() = \mathsf{Z}`$ は $`\mathrm{tr}`$ の定義（D.translate）の
第 1 式、$`p_2 = 0`$ は上で示した）。

$`\mathrm{Acc}`$ の生成規則により、$`y \mathbin{R_{\mathrm{st}}} c`$ なる任意の $`y`$ に
ついて $`\mathrm{Acc}(R_{\mathrm{st}},y)`$ を示せばよい。$`R_{\mathrm{st}}`$ の
定義（D.Rst）より $`y \in \mathrm{ST\_PS}`$ と
$`\mathrm{tr}\,y \prec \mathrm{tr}\,c = \mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$ が得られる。
[T.eq_Z_of_olt_one](#t-eq_Z_of_olt_one) より $`\mathrm{tr}\,y = \mathsf{Z}`$ であり、
[T.translate_eq_Z_iff](#t-translate_eq_Z_iff) より $`y = ()`$ である。一方
[T.stps_ne_nil](#t-stps_ne_nil) を $`y \in \mathrm{ST\_PS}`$ に適用すると $`y \ne ()`$ で
あり、矛盾する。よってそのような $`y`$ は存在せず、前件が偽であるから
$`\mathrm{Acc}(R_{\mathrm{st}},c)`$ が成り立つ。

**分岐 (2)：$`\mathrm{natDom}(c)`$ かつ $`\forall n \ge 1,\ c[n] \in Y`$ のとき。**
$`Y`$ の定義より第 2 連言子は「$`1 \le n`$ なるすべての $`n`$ について
$`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$」である。これと $`c \in \mathrm{ST\_PS}`$ に
[T.acc_of_nat_branch](#t-acc_of_nat_branch) を適用して
$`\mathrm{Acc}(R_{\mathrm{st}},c)`$ を得る。

**分岐 (3)：ある $`m \lt u`$ について $`\mathrm{domT}(c,m)`$ かつ
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(c,z) \in Y`$ のとき。**
$`1 \lt \lvert c\rvert`$ かどうかでさらに場合分けする。

**(3a) $`1 \lt \lvert c\rvert`$ のとき。**
[T.acc_of_nat_branch](#t-acc_of_nat_branch) を適用するので、$`1 \le n`$ なる各 $`n`$ に
ついて $`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$ を示せばよい。
[T.W_nil](#t-W_nil) より $`() \in W_m`$ であり、[T.based_nil](#t-based_nil) より
$`\mathrm{based}(())`$ であるから、分岐 (3) の第 3 連言子を $`z := ()`$ に適用して
$`\mathrm{graft}(c,()) \in Y`$ を得る。また
[T.oper_eq_graft_nil_of_domT](#t-oper_eq_graft_nil_of_domT) を
$`1 \lt \lvert c\rvert`$ と $`\mathrm{domT}(c,m)`$ に適用して
$`c[n] = \mathrm{graft}(c,())`$ を得る。合わせて $`c[n] \in Y`$、すなわち
$`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$ である。

**(3b) $`\neg\bigl(1 \lt \lvert c\rvert\bigr)`$ のとき。**
[T.stps_len_pos](Column.md#t-stps_len_pos) より $`0 \lt \lvert c\rvert`$ であるから
$`\lvert c\rvert = 1`$ である。[T.stps_len_one](#t-stps_len_one) より
$`c = \bigl((0,0)\bigr)`$ である。$`\mathrm{domT}(c,m)`$ の第 1 連言子（D.domT）は
$`c_{1,\lvert c\rvert-1} = m+1`$ であり、$`\lvert c\rvert - 1 = 0`$ と
$`M_{i,j}`$ の定義（D.entry）より $`c_{1,0} = 0`$ であるから $`0 = m+1`$ となる。
自然数において $`m+1 \ne 0`$ であるから矛盾であり、この場合は起こらない。∎

<a id="d-argOK"></a>
## 定義: 引数ブロック (D.argOK)

$`R \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{argOK}(R) :\iff \forall p \in R,\ 0 \lt p_1 .
```

すなわち $`R`$ のすべての対の第 1 成分が $`0`$ より真に大きい。

<a id="d-rsum"></a>
## 定義: 先頭が最小の後置ブロック (D.rsum)

$`A, P \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{rsum}(A,P) :\iff \forall p \in A \mathbin{+\!\!+} P,\ P_{0,0} \le p_1 .
```

すなわち $`P`$ の先頭の対の第 1 成分が、連結列 $`A \mathbin{+\!\!+} P`$ の全要素の第 1 成分の
下界になっている。

<a id="t-nextR_shift_iff"></a>
## 定理: 親子関係は行 0 の平行移動で不変 (T.nextR_shift_iff)

### 定理

$`S \in \mathrm{PairSeq}`$、$`d, i, a, b \in \mathbb{N}`$ とし、$`b \lt \lvert S\rvert`$ とする。このとき

```math
a \to^{S^{+d}}_i b \iff a \to^S_i b .
```

### 証明

$`\to^{\cdot}_i`$ の定義（D.nextR）は $`i = 0`$ か否かの場合分けである。

- $`i = 0`$ のとき。両辺はそれぞれ $`a \to^{S^{+d}}_0 b`$ と $`a \to^S_0 b`$ であり、
  仮定 $`b \lt \lvert S\rvert`$ のもとで
  [T.nextrel0_shift_iff](Column-4.md#t-nextrel0_shift_iff) がこの同値を与える。

- $`i \ne 0`$ のとき。両辺はそれぞれ $`a \to^{S^{+d}}_1 b`$ と $`a \to^S_1 b`$ であり、
  仮定 $`b \lt \lvert S\rvert`$ のもとで
  [T.nextrel1_shift_iff](Column-4.md#t-nextrel1_shift_iff) がこの同値を与える。∎
