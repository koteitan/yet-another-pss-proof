[← README](README.md)

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
  [T.nextrel0_shift_iff](Column.md#t-nextrel0_shift_iff) がこの同値を与える。

- $`i \ne 0`$ のとき。両辺はそれぞれ $`a \to^{S^{+d}}_1 b`$ と $`a \to^S_1 b`$ であり、
  仮定 $`b \lt \lvert S\rvert`$ のもとで
  [T.nextrel1_shift_iff](Column.md#t-nextrel1_shift_iff) がこの同値を与える。∎

<a id="t-hasParent_shift"></a>
## 定理: 親の存在は行 0 の平行移動で不変 (T.hasParent_shift)

### 定理

$`b \lt \lvert S\rvert`$ ならば
$`\mathrm{hasParent}(S^{+d}, i, b) \iff \mathrm{hasParent}(S, i, b)`$。

### 証明

$`\mathrm{hasParent}`$ の定義（D.hasParent）より、両辺はそれぞれ
「$`j_0 \to^{S^{+d}}_i b`$ をみたす $`j_0`$ が存在し一意である」
「$`j_0 \to^{S}_i b`$ をみたす $`j_0`$ が存在し一意である」である。

**（左から右）** $`j_0`$ を取り、$`j_0 \to^{S^{+d}}_i b`$ かつ
「$`y \to^{S^{+d}}_i b`$ なる任意の $`y`$ について $`y = j_0`$」とする。
[T.nextR_shift_iff](#t-nextR_shift_iff) より $`j_0 \to^{S}_i b`$ である。
また $`y \to^{S}_i b`$ なる $`y`$ を取ると、ふたたび
[T.nextR_shift_iff](#t-nextR_shift_iff) より $`y \to^{S^{+d}}_i b`$ であるから
$`y = j_0`$ である。よって $`S`$ の側でも存在と一意性が成り立つ。

**（右から左）** $`j_0`$ を取り、$`j_0 \to^{S}_i b`$ かつ
「$`y \to^{S}_i b`$ なる任意の $`y`$ について $`y = j_0`$」とする。
[T.nextR_shift_iff](#t-nextR_shift_iff) より $`j_0 \to^{S^{+d}}_i b`$ である。
また $`y \to^{S^{+d}}_i b`$ なる $`y`$ を取ると、ふたたび
[T.nextR_shift_iff](#t-nextR_shift_iff) より $`y \to^{S}_i b`$ であるから
$`y = j_0`$ である。よって $`S^{+d}`$ の側でも存在と一意性が成り立つ。∎

<a id="t-parent_shift"></a>
## 定理: 親は行 0 の平行移動で変わらない (T.parent_shift)

### 定理

$`b \lt \lvert S\rvert`$ ならば
$`\mathrm{par}^{S^{+d}}_i(b) = \mathrm{par}^{S}_i(b)`$（[D.parent](Pss.md#d-parent)）。

### 証明

$`\mathrm{par}`$ の定義（D.parent）より、両辺はそれぞれ述語

```math
\varphi(j_0) :\equiv \bigl(j_0 \to^{S^{+d}}_i b\bigr),
\qquad
\psi(j_0) :\equiv \bigl(j_0 \to^{S}_i b\bigr)
```

に $`\varepsilon`$ を適用した値である。$`b \lt \lvert S\rvert`$ のもとで
[T.nextR_shift_iff](#t-nextR_shift_iff) はすべての $`j_0`$ について
$`\varphi(j_0) \iff \psi(j_0)`$ を与えるから、命題の外延性により各 $`j_0`$ で
$`\varphi(j_0)`$ と $`\psi(j_0)`$ は同一の命題であり、したがって $`\varphi = \psi`$ である。
$`\varepsilon`$ の値は述語のみで決まるから両辺は等しい。∎

<a id="t-oper_shift"></a>
## 定理: 展開は行 0 の平行移動と可換 (T.oper_shift)

### 定理

任意の $`M \in \mathrm{PairSeq}`$、$`d, n \in \mathbb{N}`$ に対し

```math
\bigl(M^{+d}\bigr)[n] = \bigl(M[n]\bigr)^{+d} .
```

### 証明

$`\lvert M^{+d}\rvert = \lvert M\rvert`$ である（平行移動は各要素を 1 つずつ写すだけである）。
以下 $`j_1 := \lvert M\rvert - 1`$ とおく。$`j_1 = 0`$ か否かで場合分けする。

**(I) $`j_1 = 0`$ のとき。** $`\lvert M^{+d}\rvert - 1 = j_1 = 0`$ でもあるから、
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) を $`M^{+d}`$ と $`M`$ の
双方に適用して $`(M^{+d})[n] = M^{+d}`$ と $`M[n] = M`$ を得る。よって両辺とも $`M^{+d}`$ である。

**(II) $`j_1 \ne 0`$ のとき。** このとき $`j_1 \lt \lvert M\rvert`$ である。
$`i_1 := \mathrm{idx}_1(M, j_1)`$ とおくと
[T.idx1_shift](Column.md#t-idx1_shift) より $`\mathrm{idx}_1(M^{+d}, j_1) = i_1`$ である。
$`\mathrm{hasParent}(M, i_1, j_1)`$ が成り立つか否かでさらに分ける。

**(II-a) $`\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
まず $`0 \lt M_{0,j_1}`$ である。実際 $`M_{0,j_1} = 0`$ とすると
[T.no_hasParent_of_row0_zero](Column.md#t-no_hasParent_of_row0_zero) により
$`\mathrm{hasParent}(M, i_1, j_1)`$ から矛盾が出る。したがって
$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ である。
[T.entry_shift](Column.md#t-entry_shift) より
$`(M^{+d})_{0,j_1} = M_{0,j_1} + d`$、$`(M^{+d})_{1,j_1} = M_{1,j_1}`$ であるから、
$`(M^{+d})_{0,j_1} \gt 0`$ で $`\neg\bigl((M^{+d})_{0,j_1} = 0 \wedge (M^{+d})_{1,j_1} = 0\bigr)`$ である。
また [T.hasParent_shift](#t-hasParent_shift) より $`\mathrm{hasParent}(M^{+d}, i_1, j_1)`$ である。
よって $`M`$ と $`M^{+d}`$ の双方で $`M[n]`$ の定義（D.oper）の分岐 (d) が選ばれ、
[T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) が適用できる。

[T.parent_shift](#t-parent_shift) より
$`j_0 := \mathrm{par}^{M}_{i_1}(j_1) = \mathrm{par}^{M^{+d}}_{i_1}(j_1)`$ であり、
[T.parent_nextR](Decrease.md#t-parent_nextR) と
[T.nextR_index_lt](Decrease.md#t-nextR_index_lt) より $`j_0 \lt j_1`$、とくに
$`j_0 \lt \lvert M\rvert`$ である。したがってふたたび
[T.entry_shift](Column.md#t-entry_shift) より $`(M^{+d})_{0,j_0} = M_{0,j_0} + d`$ であり、
$`d_0`$ の値は両者で一致する。すなわち $`0 \lt i_1`$ のとき

```math
(M^{+d})_{0,j_1} - (M^{+d})_{0,j_0} = (M_{0,j_1} + d) - (M_{0,j_0} + d) = M_{0,j_1} - M_{0,j_0}
```

であり（切り捨て減法でも右辺の $`d`$ は相殺する）、$`i_1 = 0`$ のときは両者とも $`0`$ である。
この共通の値を $`d_0`$ と書く。

[T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) の与える両辺は

```math
M[n] = (M_0,\dots,M_{j_0-1}) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1},
```
```math
\bigl(M^{+d}\bigr)[n]
  = \bigl((M^{+d})_0,\dots,(M^{+d})_{j_0-1}\bigr) \mathbin{+\!\!+} B'_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B'_{n-1},
\qquad
B'_k = \bigl(\,((M^{+d})_{0,j} + k\,d_0,\ (M^{+d})_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
```

である。前部分については $`\bigl((M^{+d})_0,\dots,(M^{+d})_{j_0-1}\bigr) = (M_0,\dots,M_{j_0-1})^{+d}`$
である（平行移動は各要素ごとの写像であり、先頭 $`j_0`$ 個を取る操作と交換する）。
各ブロックについては、$`j_0 \le j \lt j_1 \lt \lvert M\rvert`$ の範囲で
[T.entry_shift](Column.md#t-entry_shift) が使えて

```math
\bigl((M^{+d})_{0,j} + k\,d_0,\ (M^{+d})_{1,j}\bigr)
  = \bigl(M_{0,j} + d + k\,d_0,\ M_{1,j}\bigr)
  = \bigl((M_{0,j} + k\,d_0) + d,\ M_{1,j}\bigr)
```

であるから $`B'_k = (B_k)^{+d}`$ である。連結と平行移動は交換するから、両辺は等しい。

**(II-b) $`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ のとき。**
[T.hasParent_shift](#t-hasParent_shift) より
$`\neg\,\mathrm{hasParent}(M^{+d}, i_1, j_1)`$ である。
$`M`$ について、$`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ が成り立つなら
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) により、成り立たないなら
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) により、いずれにせよ
$`M[n] = \mathrm{Pred}\,M`$ である。同じ 2 つの定理を $`M^{+d}`$ に適用して
$`(M^{+d})[n] = \mathrm{Pred}(M^{+d})`$ を得る。

$`j_1 = \lvert M\rvert - 1 \ne 0`$ より $`2 \le \lvert M\rvert = \lvert M^{+d}\rvert`$ であるから、
$`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合が両者で選ばれ

```math
\mathrm{Pred}\,M = \mathrm{dropLast}\,M,
\qquad
\mathrm{Pred}(M^{+d}) = \mathrm{dropLast}(M^{+d})
```

である。平行移動は各要素ごとの写像であるから末尾 1 要素を落とす操作と交換し、
$`\mathrm{dropLast}(M^{+d}) = (\mathrm{dropLast}\,M)^{+d}`$ である。よって両辺は等しい。∎

<a id="t-domT_shift"></a>
## 定理: $`\mathrm{domT}`$ は行 0 の平行移動で不変 (T.domT_shift)

### 定理

$`\mathrm{domT}(M^{+d}, m) \iff \mathrm{domT}(M, m)`$。

### 証明

$`M`$ の構成子で場合分けする。

**(a) $`M = ()`$ のとき。** $`()^{+d} = ()`$ である。$`\lvert ()\rvert - 1 = 0`$ であり、
$`M_{i,j}`$ の定義（D.entry）より $`()_{1,0} = 0`$ であるから、
$`\mathrm{domT}`$ の定義（D.domT）の第 1 連言子 $`()_{1,0} = m+1`$ は偽である。
よって両辺とも偽であり、同値である。

**(b) $`M = p :: L`$ のとき。** $`\lvert M^{+d}\rvert = \lvert M\rvert`$ であるから、
両辺で読む添字は同じ $`j_1 := \lvert M\rvert - 1`$ であり、$`j_1 \lt \lvert M\rvert`$ である。
$`\mathrm{domT}`$ の定義（D.domT）の 2 つの連言子をそれぞれ比べる。
第 1 連言子は [T.entry_shift](Column.md#t-entry_shift) より
$`(M^{+d})_{1,j_1} = M_{1,j_1}`$ であるから同値であり、
第 2 連言子は [T.hasParent_shift](#t-hasParent_shift) より
$`\mathrm{hasParent}(M^{+d}, 1, j_1) \iff \mathrm{hasParent}(M, 1, j_1)`$ であるから同値である。∎

<a id="t-natDom_shift"></a>
## 定理: $`\mathrm{natDom}`$ は行 0 の平行移動で不変 (T.natDom_shift)

### 定理

$`\mathrm{natDom}(M^{+d}) \iff \mathrm{natDom}(M)`$。

### 証明

$`\mathrm{natDom}`$ の定義（D.natDom）より、左辺は
$`\forall m,\ \neg\,\mathrm{domT}(M^{+d}, m)`$、右辺は $`\forall m,\ \neg\,\mathrm{domT}(M, m)`$ である。

左辺を仮定し $`m`$ を取る。$`\mathrm{domT}(M,m)`$ とすると
[T.domT_shift](#t-domT_shift) より $`\mathrm{domT}(M^{+d}, m)`$ となり左辺に矛盾する。
よって $`\neg\,\mathrm{domT}(M,m)`$ である。

右辺を仮定し $`m`$ を取る。$`\mathrm{domT}(M^{+d},m)`$ とすると
[T.domT_shift](#t-domT_shift) より $`\mathrm{domT}(M, m)`$ となり右辺に矛盾する。
よって $`\neg\,\mathrm{domT}(M^{+d},m)`$ である。∎

<a id="t-graft_shift"></a>
## 定理: 接ぎ木は行 0 の平行移動と可換 (T.graft_shift)

### 定理

$`M \ne ()`$ ならば、任意の $`z \in \mathrm{PairSeq}`$、$`d \in \mathbb{N}`$ に対し

```math
\mathrm{graft}\bigl(M^{+d},\ z\bigr) = \bigl(\mathrm{graft}(M, z)\bigr)^{+d} .
```

### 証明

$`M \ne ()`$ より $`0 \lt \lvert M\rvert`$、したがって $`j_1 := \lvert M\rvert - 1 \lt \lvert M\rvert`$ である。
$`\lvert M^{+d}\rvert = \lvert M\rvert`$ であるから、$`M^{+d}`$ の末尾の添字も $`j_1`$ である。
$`\mathrm{graft}`$ の定義（D.graft）より

```math
\mathrm{graft}\bigl(M^{+d}, z\bigr)
  = \mathrm{dropLast}\bigl(M^{+d}\bigr) \mathbin{+\!\!+} z^{+(M^{+d})_{0,j_1}} .
```

[T.entry_shift](Column.md#t-entry_shift) より $`(M^{+d})_{0,j_1} = M_{0,j_1} + d`$ であり、
平行移動は末尾 1 要素を落とす操作と交換するから
$`\mathrm{dropLast}(M^{+d}) = (\mathrm{dropLast}\,M)^{+d}`$ である。よって

```math
\mathrm{graft}\bigl(M^{+d}, z\bigr)
  = (\mathrm{dropLast}\,M)^{+d} \mathbin{+\!\!+} z^{+(M_{0,j_1} + d)} .
```

一方

```math
\bigl(\mathrm{graft}(M,z)\bigr)^{+d}
  = \bigl(\mathrm{dropLast}\,M \mathbin{+\!\!+} z^{+M_{0,j_1}}\bigr)^{+d}
  = (\mathrm{dropLast}\,M)^{+d} \mathbin{+\!\!+} \bigl(z^{+M_{0,j_1}}\bigr)^{+d}
```

である（平行移動は連結と交換する）。$`z`$ の要素 $`q`$ は右辺の第 2 項では
$`\bigl((q_1 + M_{0,j_1}) + d,\ q_2\bigr)`$ に写り、左辺の第 2 項では
$`\bigl(q_1 + (M_{0,j_1} + d),\ q_2\bigr)`$ に写る。$`\mathbb{N}`$ の加法の結合律により
この 2 つは等しい。よって両辺は等しい。∎

<a id="t-W_shift"></a>
## 定理: 行 0 の平行移動による $`W_u`$ の不変性 (T.W_shift)

### 定理

$`M \in W_u`$ ならば、任意の $`d \in \mathbb{N}`$ に対し $`M^{+d} \in W_u`$。

### 証明

$`d`$ を固定し

```math
Y := \{\, N \in \mathrm{PairSeq} \mid N^{+d} \in W_u \,\}
```

とおく。[T.A2'](#t-A2') により $`W_u \subseteq Y`$ を示すには、
任意の $`N`$ について $`N \in A_u(Y)`$ ならば $`N \in Y`$、すなわち $`N^{+d} \in W_u`$ を示せばよい。
[T.A1_intro](#t-A1_intro) によりこれは $`N^{+d} \in A_u(W_u)`$ に帰着する。
$`A_u`$ の定義（D.Aop）の 3 分岐で場合分けする。

**分岐 (1)：$`\lvert N\rvert \le 1 \wedge N_{1,0} = 0`$ のとき。**
$`\lvert N^{+d}\rvert = \lvert N\rvert \le 1`$ である。また $`(N^{+d})_{1,0} = N_{1,0} = 0`$ である。
実際 $`N = ()`$ なら $`N^{+d} = ()`$ で両辺とも $`0`$（D.entry の範囲外の読み）、
$`N = p :: L`$ なら $`N^{+d}`$ の先頭は $`(p_1 + d,\ p_2)`$ でその第 2 成分は $`p_2 = N_{1,0}`$ である。
よって $`N^{+d}`$ は分岐 (1) をみたす。

**分岐 (2)：$`\mathrm{natDom}(N) \wedge \forall n \ge 1,\ N[n] \in Y`$ のとき。**
[T.natDom_shift](#t-natDom_shift) より $`\mathrm{natDom}(N^{+d})`$ である。
$`n \ge 1`$ を取ると [T.oper_shift](#t-oper_shift) より
$`(N^{+d})[n] = (N[n])^{+d}`$ であり、$`N[n] \in Y`$ すなわち $`(N[n])^{+d} \in W_u`$ である。
よって $`N^{+d}`$ は分岐 (2) をみたす。

**分岐 (3)、すなわち $`m \lt u`$、$`\mathrm{domT}(N,m)`$、
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(N,z) \in Y`$ をみたす $`m`$ があるとき。**
[T.domT_shift](#t-domT_shift) より $`\mathrm{domT}(N^{+d}, m)`$ である。
また $`N \ne ()`$ である（$`N = ()`$ なら [T.not_domT_nil](#t-not_domT_nil) が
$`\mathrm{domT}(N,m)`$ に矛盾する）。$`z \in W_m`$ が $`\mathrm{based}(z)`$ をみたすとき、
[T.graft_shift](#t-graft_shift) より

```math
\mathrm{graft}\bigl(N^{+d}, z\bigr) = \bigl(\mathrm{graft}(N,z)\bigr)^{+d}
```

であり、$`\mathrm{graft}(N,z) \in Y`$ よりこれは $`W_u`$ の元である。
よって $`N^{+d}`$ は同じ $`m`$ で分岐 (3) をみたす。

以上により $`W_u \subseteq Y`$ であり、$`M \in W_u`$ から $`M^{+d} \in W_u`$ を得る。∎

<a id="t-split_lastMin"></a>
## 定理: 最後の最上位木による分解 (T.split_lastMin)

### 定理

$`M \ne ()`$ ならば、$`A, P \in \mathrm{PairSeq}`$ が存在して

```math
M = A \mathbin{+\!\!+} P,
\qquad P \ne (),
\qquad \mathrm{rsum}(A, P),
\qquad \forall p \in \mathrm{tail}\,P,\ P_{0,0} \lt p_1 .
```

ここで $`\mathrm{tail}\,P`$ は $`P`$ の先頭 1 要素を落とした列である。

### 証明

列の末尾からの構成に関する帰納法を行う。すなわち、$`\mathrm{PairSeq}`$ の各元は
$`()`$ であるか、ある $`M'`$ と対 $`q`$ によって $`M' \mathbin{+\!\!+} (q)`$ と書けるかのいずれかであり、
後者では $`\lvert M'\rvert \lt \lvert M' \mathbin{+\!\!+} (q)\rvert`$ である。帰納法の述語は

```math
\Phi(M) :\equiv M \ne () \to \exists A, P,\
  \bigl(M = A \mathbin{+\!\!+} P \wedge P \ne () \wedge \mathrm{rsum}(A,P)
    \wedge \forall p \in \mathrm{tail}\,P,\ P_{0,0} \lt p_1\bigr).
```

- **基底段** $`M = ()`$：前件 $`M \ne ()`$ が偽であるから $`\Phi(())`$ が成り立つ。

**帰納段** $`M = M' \mathbin{+\!\!+} (q)`$：帰納法の仮定は $`\Phi(M')`$ である。
$`M'`$ が空か否かで場合分けする。

**(a) $`M' = ()`$ のとき。** $`A := ()`$、$`P := (q)`$ と取る。
$`M = () \mathbin{+\!\!+} (q)`$ であり $`P \ne ()`$ である。
$`P_{0,0} = q_1`$ であり、$`() \mathbin{+\!\!+} (q)`$ の要素は $`q`$ のみで $`q_1 \le q_1`$ が成り立つから
$`\mathrm{rsum}(A,P)`$ である。$`\mathrm{tail}\,(q) = ()`$ であるから最後の条件は要素をもたず成り立つ。

**(b) $`M' \ne ()`$ のとき。** 帰納法の仮定 $`\Phi(M')`$ より
$`M' = A' \mathbin{+\!\!+} P'`$、$`P' \ne ()`$、$`\mathrm{rsum}(A',P')`$、
$`\forall p \in \mathrm{tail}\,P',\ P'_{0,0} \lt p_1`$ をみたす $`A', P'`$ を取る。
$`q_1`$ と $`P'_{0,0}`$ の大小で分ける。

**(b-1) $`q_1 \le P'_{0,0}`$ のとき。** $`A := M'`$、$`P := (q)`$ と取る。
$`M = M' \mathbin{+\!\!+} (q)`$ であり $`P \ne ()`$ である。$`P_{0,0} = q_1`$ である。
$`p \in M' \mathbin{+\!\!+} (q)`$ を取る。$`p \in M' = A' \mathbin{+\!\!+} P'`$ のときは
$`\mathrm{rsum}(A',P')`$ より $`P'_{0,0} \le p_1`$ であり、仮定 $`q_1 \le P'_{0,0}`$ と合わせて
$`q_1 \le p_1`$ である。$`p = q`$ のときは $`q_1 \le q_1`$ である。よって $`\mathrm{rsum}(A,P)`$。
$`\mathrm{tail}\,(q) = ()`$ であるから最後の条件は成り立つ。

**(b-2) $`P'_{0,0} \lt q_1`$ のとき。** $`A := A'`$、$`P := P' \mathbin{+\!\!+} (q)`$ と取る。
連結の結合律より
$`M = (A' \mathbin{+\!\!+} P') \mathbin{+\!\!+} (q) = A' \mathbin{+\!\!+} (P' \mathbin{+\!\!+} (q))`$ であり、
$`P \ne ()`$ である。$`P' \ne ()`$ であるから $`P' = p_0 :: P''`$ と書け、
$`P' \mathbin{+\!\!+} (q) = p_0 :: (P'' \mathbin{+\!\!+} (q))`$ の先頭も $`p_0`$ である。よって

```math
P_{0,0} = (p_0)_1 = P'_{0,0} .
```

$`\mathrm{rsum}(A,P)`$ を示す。$`p \in A' \mathbin{+\!\!+} (P' \mathbin{+\!\!+} (q))`$ を取る。
$`p \in A'`$ のときは $`\mathrm{rsum}(A',P')`$ より $`P'_{0,0} \le p_1`$。
$`p \in P'`$ のときも $`\mathrm{rsum}(A',P')`$ より $`P'_{0,0} \le p_1`$。
$`p = q`$ のときは仮定 $`P'_{0,0} \lt q_1`$ より $`P'_{0,0} \le q_1`$。
いずれの場合も $`P_{0,0} = P'_{0,0} \le p_1`$ である。

最後の条件を示す。$`\mathrm{tail}\,P = P'' \mathbin{+\!\!+} (q)`$ である。
$`p \in P''`$ のときは $`P'' = \mathrm{tail}\,P'`$ であるから帰納法の仮定で得た条件より
$`P'_{0,0} \lt p_1`$ である。$`p = q`$ のときは仮定そのもの $`P'_{0,0} \lt q_1`$ である。
$`P_{0,0} = P'_{0,0}`$ であるから、いずれの場合も $`P_{0,0} \lt p_1`$ である。∎

<a id="t-map_sub_add"></a>
## 定理: 下方向と上方向の平行移動の合成 (T.map_sub_add)

### 定理

$`c \in \mathbb{N}`$、$`X \in \mathrm{PairSeq}`$ とし、$`\forall p \in X,\ c \le p_1`$ とする。このとき

```math
\bigl(X^{-c}\bigr)^{+c} = X .
```

ここで $`X^{-c}`$ は $`X`$ の各対の第 1 成分から一様に $`c`$ を切り捨て減法で引いた列である。

### 証明

$`X^{-c}`$ も $`(X^{-c})^{+c}`$ も $`X`$ の各要素を 1 つずつ写して得られる列であるから、
3 つの列の長さは等しい。$`X`$ の要素 $`q`$ が $`(X^{-c})^{+c}`$ の対応する位置で
何になるかを見ると、

```math
q \longmapsto (q_1 - c,\ q_2) \longmapsto \bigl((q_1 - c) + c,\ q_2\bigr)
```

である。仮定より $`c \le q_1`$ であるから、切り捨て減法について $`(q_1 - c) + c = q_1`$ であり、
この対は $`(q_1, q_2) = q`$ に等しい。よって対応する位置の要素がすべて一致し、両辺は等しい。∎

<a id="t-rsum_decomp"></a>
## 定理: 最上位分解の平行移動表示 (T.rsum_decomp)

### 定理

$`\mathrm{rsum}(A,P)`$ ならば、$`c := P_{0,0}`$ として

```math
\bigl(A^{-c} \mathbin{+\!\!+} P^{-c}\bigr)^{+c} = A \mathbin{+\!\!+} P .
```

### 証明

平行移動は各要素ごとの写像であるから連結と交換し、

```math
\bigl(A^{-c} \mathbin{+\!\!+} P^{-c}\bigr)^{+c} = \bigl(A^{-c}\bigr)^{+c} \mathbin{+\!\!+} \bigl(P^{-c}\bigr)^{+c}
```

である。$`\mathrm{rsum}(A,P)`$ の定義（D.rsum）は
$`\forall p \in A \mathbin{+\!\!+} P,\ c \le p_1`$ であるから、とくに
$`\forall p \in A,\ c \le p_1`$ と $`\forall p \in P,\ c \le p_1`$ が成り立つ。
[T.map_sub_add](#t-map_sub_add) を $`X := A`$ と $`X := P`$ に適用して
$`(A^{-c})^{+c} = A`$、$`(P^{-c})^{+c} = P`$ を得る。∎

<a id="t-entry_sub_zero"></a>
## 定理: 下げた列の先頭の行 0 の値は 0 (T.entry_sub_zero)

### 定理

$`P \ne ()`$ ならば、$`c := P_{0,0}`$ として $`\bigl(P^{-c}\bigr)_{0,0} = 0`$。

### 証明

$`P \ne ()`$ より $`P = p_0 :: P'`$ と書ける。$`M_{i,j}`$ の定義（D.entry）より
$`c = P_{0,0} = (p_0)_1`$ である。$`P^{-c}`$ の先頭は
$`\bigl((p_0)_1 - c,\ (p_0)_2\bigr) = \bigl((p_0)_1 - (p_0)_1,\ (p_0)_2\bigr) = \bigl(0,\ (p_0)_2\bigr)`$
であるから、ふたたび D.entry より $`(P^{-c})_{0,0} = 0`$ である。∎

<a id="t-oper_append_gen"></a>
## 定理: 最上位分解に沿う展開の前置可換性 (T.oper_append_gen)

### 定理

$`2 \le \lvert P\rvert`$ かつ $`\mathrm{rsum}(A,P)`$ ならば、任意の $`n`$ に対し

```math
(A \mathbin{+\!\!+} P)[n] = A \mathbin{+\!\!+} P[n] .
```

### 証明

$`c := P_{0,0}`$、$`\hat A := A^{-c}`$、$`\hat P := P^{-c}`$ とおく。
$`2 \le \lvert P\rvert`$ より $`P \ne ()`$ であり、次の 5 つが成り立つ。

1. $`(\hat P)_{0,0} = 0`$。[T.entry_sub_zero](#t-entry_sub_zero) による。
2. $`2 \le \lvert \hat P\rvert`$。平行移動は長さを変えないから $`\lvert \hat P\rvert = \lvert P\rvert`$ である。
3. $`(\hat A \mathbin{+\!\!+} \hat P)^{+c} = A \mathbin{+\!\!+} P`$。[T.rsum_decomp](#t-rsum_decomp) による。
4. $`(\hat P)^{+c} = P`$。$`\mathrm{rsum}(A,P)`$ より $`\forall p \in P,\ c \le p_1`$ であるから
   [T.map_sub_add](#t-map_sub_add) による。
5. $`(\hat A)^{+c} = A`$。$`\mathrm{rsum}(A,P)`$ より $`\forall p \in A,\ c \le p_1`$ であるから
   [T.map_sub_add](#t-map_sub_add) による。

これらを用いて計算する。

```math
\begin{aligned}
(A \mathbin{+\!\!+} P)[n]
  &= \Bigl(\bigl(\hat A \mathbin{+\!\!+} \hat P\bigr)^{+c}\Bigr)[n] && (3) \cr
  &= \Bigl(\bigl(\hat A \mathbin{+\!\!+} \hat P\bigr)[n]\Bigr)^{+c} && (6) \cr
  &= \bigl(\hat A \mathbin{+\!\!+} \hat P[n]\bigr)^{+c} && (7) \cr
  &= (\hat A)^{+c} \mathbin{+\!\!+} \bigl(\hat P[n]\bigr)^{+c} && (8) \cr
  &= A \mathbin{+\!\!+} \bigl(\hat P[n]\bigr)^{+c} && (5) \cr
  &= A \mathbin{+\!\!+} \bigl((\hat P)^{+c}\bigr)[n] && (6) \cr
  &= A \mathbin{+\!\!+} P[n] . && (4)
\end{aligned}
```

ここで (6) は [T.oper_shift](#t-oper_shift)（第 2 行では左から右へ、第 6 行では右から左へ）、
(7) は [T.oper_append_right](Column.md#t-oper_append_right) であり、その 2 つの仮定
$`2 \le \lvert \hat P\rvert`$ と $`(\hat P)_{0,0} = 0`$ は (2) と (1) である。
(8) は平行移動が連結と交換することによる。∎

<a id="t-graft_append"></a>
## 定理: 接ぎ木の前置可換性 (T.graft_append)

### 定理

$`P \ne ()`$ ならば、任意の $`A, z \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{graft}(A \mathbin{+\!\!+} P,\ z) = A \mathbin{+\!\!+} \mathrm{graft}(P, z) .
```

### 証明

$`P \ne ()`$ より $`0 \lt \lvert P\rvert`$ であるから

```math
\lvert A \mathbin{+\!\!+} P\rvert - 1 = \lvert A\rvert + \lvert P\rvert - 1 = \lvert A\rvert + (\lvert P\rvert - 1)
```

である。[T.entry_append_right](Column.md#t-entry_append_right) を
$`i := 0`$、$`j := \lvert P\rvert - 1`$ に適用して

```math
(A \mathbin{+\!\!+} P)_{0,\ \lvert A \mathbin{+\!\!+} P\rvert - 1} = P_{0,\ \lvert P\rvert - 1}
```

を得る。また $`P \ne ()`$ より
$`\mathrm{dropLast}(A \mathbin{+\!\!+} P) = A \mathbin{+\!\!+} \mathrm{dropLast}\,P`$ である。
よって $`\mathrm{graft}`$ の定義（D.graft）より

```math
\mathrm{graft}(A \mathbin{+\!\!+} P, z)
  = \bigl(A \mathbin{+\!\!+} \mathrm{dropLast}\,P\bigr) \mathbin{+\!\!+} z^{+P_{0,\lvert P\rvert-1}}
  = A \mathbin{+\!\!+} \bigl(\mathrm{dropLast}\,P \mathbin{+\!\!+} z^{+P_{0,\lvert P\rvert-1}}\bigr)
  = A \mathbin{+\!\!+} \mathrm{graft}(P,z)
```

である（中央の等号は連結の結合律による）。∎

<a id="t-hasParent_append_gen"></a>
## 定理: 最上位分解に沿う親の存在の前置不変性 (T.hasParent_append_gen)

### 定理

$`j \lt \lvert P\rvert`$ かつ $`\mathrm{rsum}(A,P)`$ ならば

```math
\mathrm{hasParent}\bigl(A \mathbin{+\!\!+} P,\ i,\ \lvert A\rvert + j\bigr) \iff \mathrm{hasParent}(P, i, j).
```

### 証明

$`j \lt \lvert P\rvert`$ より $`P \ne ()`$ である。
$`c := P_{0,0}`$、$`\hat A := A^{-c}`$、$`\hat P := P^{-c}`$ とおく。
平行移動は長さを変えないから $`\lvert \hat A\rvert = \lvert A\rvert`$、$`\lvert \hat P\rvert = \lvert P\rvert`$ である。
[T.entry_sub_zero](#t-entry_sub_zero) より $`(\hat P)_{0,0} = 0`$、
[T.rsum_decomp](#t-rsum_decomp) より $`(\hat A \mathbin{+\!\!+} \hat P)^{+c} = A \mathbin{+\!\!+} P`$、
[T.map_sub_add](#t-map_sub_add) より $`(\hat P)^{+c} = P`$ である。3 段に分ける。

**第 1 段。** 次を示す。

```math
\mathrm{hasParent}(A \mathbin{+\!\!+} P,\ i,\ \lvert A\rvert + j)
\iff \mathrm{hasParent}(\hat A \mathbin{+\!\!+} \hat P,\ i,\ \lvert \hat A\rvert + j).
```

$`\lvert \hat A \mathbin{+\!\!+} \hat P\rvert = \lvert A\rvert + \lvert P\rvert`$ であり
$`j \lt \lvert P\rvert`$ であるから $`\lvert A\rvert + j \lt \lvert \hat A \mathbin{+\!\!+} \hat P\rvert`$ である。
$`(\hat A \mathbin{+\!\!+} \hat P)^{+c} = A \mathbin{+\!\!+} P`$ であるから、
[T.hasParent_shift](#t-hasParent_shift) を $`S := \hat A \mathbin{+\!\!+} \hat P`$、$`d := c`$、
$`b := \lvert A\rvert + j`$ に適用すればよい（$`\lvert \hat A\rvert = \lvert A\rvert`$）。

**第 2 段。** 次を示す。

```math
\mathrm{hasParent}(\hat A \mathbin{+\!\!+} \hat P,\ i,\ \lvert \hat A\rvert + j)
\iff \mathrm{hasParent}(\hat P,\ i,\ j).
```

$`(\hat P)_{0,j}`$ が $`0`$ か否かで場合分けする。

**$`(\hat P)_{0,j} = 0`$ のとき。** [T.entry_append_right](Column.md#t-entry_append_right) より
$`(\hat A \mathbin{+\!\!+} \hat P)_{0,\lvert \hat A\rvert + j} = (\hat P)_{0,j} = 0`$ である。
[T.no_hasParent_of_row0_zero](Column.md#t-no_hasParent_of_row0_zero) を
$`\hat A \mathbin{+\!\!+} \hat P`$ に適用すると左辺は偽であり、同じ定理を $`\hat P`$ に適用すると
右辺も偽である。よって同値である。

**$`(\hat P)_{0,j} \ne 0`$ のとき。** 上と同じ等式より
$`0 \lt (\hat A \mathbin{+\!\!+} \hat P)_{0,\lvert \hat A\rvert + j}`$ である。
$`(\hat P)_{0,0} = 0`$ と合わせて
[T.hasParent_append_right](Column.md#t-hasParent_append_right) が適用でき、同値を得る。

**第 3 段：$`\mathrm{hasParent}(\hat P, i, j) \iff \mathrm{hasParent}(P, i, j)`$。**
$`j \lt \lvert P\rvert = \lvert \hat P\rvert`$ であり $`(\hat P)^{+c} = P`$ であるから、
[T.hasParent_shift](#t-hasParent_shift) を $`S := \hat P`$、$`d := c`$、$`b := j`$ に適用すればよい。

3 段をつなげば結論を得る。∎

<a id="t-domT_append"></a>
## 定理: $`\mathrm{domT}`$ の前置不変性 (T.domT_append)

### 定理

$`P \ne ()`$ かつ $`\mathrm{rsum}(A,P)`$ ならば

```math
\mathrm{domT}(A \mathbin{+\!\!+} P,\ m) \iff \mathrm{domT}(P, m).
```

### 証明

$`P \ne ()`$ より $`0 \lt \lvert P\rvert`$ であるから

```math
\lvert A \mathbin{+\!\!+} P\rvert - 1 = \lvert A\rvert + (\lvert P\rvert - 1)
```

である。$`\mathrm{domT}`$ の定義（D.domT）の 2 つの連言子をそれぞれ比べる。

第 1 連言子について、[T.entry_append_right](Column.md#t-entry_append_right) を
$`i := 1`$、$`j := \lvert P\rvert - 1`$ に適用して

```math
(A \mathbin{+\!\!+} P)_{1,\ \lvert A \mathbin{+\!\!+} P\rvert - 1} = P_{1,\ \lvert P\rvert - 1}
```

を得るから、$`(A \mathbin{+\!\!+} P)_{1,\lvert A \mathbin{+\!\!+} P\rvert-1} = m+1`$ と
$`P_{1,\lvert P\rvert-1} = m+1`$ は同値である。

第 2 連言子について、$`\lvert P\rvert - 1 \lt \lvert P\rvert`$ であるから
[T.hasParent_append_gen](#t-hasParent_append_gen) を $`i := 1`$、$`j := \lvert P\rvert - 1`$ に
適用して

```math
\mathrm{hasParent}\bigl(A \mathbin{+\!\!+} P,\ 1,\ \lvert A \mathbin{+\!\!+} P\rvert - 1\bigr)
  \iff \mathrm{hasParent}\bigl(P,\ 1,\ \lvert P\rvert - 1\bigr)
```

を得るから、その否定どうしも同値である。∎

<a id="t-natDom_append"></a>
## 定理: $`\mathrm{natDom}`$ の前置不変性 (T.natDom_append)

### 定理

$`P \ne ()`$ かつ $`\mathrm{rsum}(A,P)`$ ならば
$`\mathrm{natDom}(A \mathbin{+\!\!+} P) \iff \mathrm{natDom}(P)`$。

### 証明

$`\mathrm{natDom}`$ の定義（D.natDom）より、左辺は
$`\forall m,\ \neg\,\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$、右辺は $`\forall m,\ \neg\,\mathrm{domT}(P,m)`$ である。

左辺を仮定し $`m`$ を取る。$`\mathrm{domT}(P,m)`$ とすると
[T.domT_append](#t-domT_append) より $`\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$ となり左辺に矛盾する。
よって $`\neg\,\mathrm{domT}(P,m)`$ である。

右辺を仮定し $`m`$ を取る。$`\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$ とすると
[T.domT_append](#t-domT_append) より $`\mathrm{domT}(P, m)`$ となり右辺に矛盾する。
よって $`\neg\,\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$ である。∎

<a id="d-XA"></a>
## 定義: 前置による剰余集合 (D.XA)

$`A \in \mathrm{PairSeq}`$、$`X \subseteq \mathrm{PairSeq}`$ に対し

```math
X^{(A)} := \{\, B \in \mathrm{PairSeq} \mid \mathrm{rsum}(A,B) \to A \mathbin{+\!\!+} B \in X \,\} .
```

<a id="t-entry_zero_headD"></a>
## 定理: 先頭の行 0 の値 (T.entry_zero_headD)

### 定理

任意の $`X \in \mathrm{PairSeq}`$ に対し $`X_{0,0} = (\mathrm{hd}\,X)_1`$。
ここで $`\mathrm{hd}\,X`$ は $`X`$ の先頭要素であり、$`X = ()`$ のときは $`(0,0)`$ とする。

### 証明

$`X`$ の構成子で場合分けする。

- $`X = ()`$ のとき。$`M_{i,j}`$ の定義（D.entry）より $`()_{0,0} = 0`$ である
  （添字 $`0`$ は範囲外なので $`(0,0)`$ を読む）。また $`\mathrm{hd}\,() = (0,0)`$ でその第 1 成分は $`0`$ である。

- $`X = p :: X'`$ のとき。D.entry より $`X_{0,0} = p_1`$ である。また $`\mathrm{hd}\,X = p`$ で
  その第 1 成分は $`p_1`$ である。∎

<a id="t-oper_head_eq"></a>
## 定理: 展開は先頭の行 0 の値を変えない (T.oper_head_eq)

### 定理

$`1 \le n`$ ならば $`\bigl(N[n]\bigr)_{0,0} = N_{0,0}`$。

### 証明

$`1 \lt \lvert N\rvert`$ か否かで場合分けする。

- $`1 \lt \lvert N\rvert`$ のとき。[T.entry_zero_headD](#t-entry_zero_headD) を
  $`X := N[n]`$ と $`X := N`$ に適用すると、示すべきことは
  $`\bigl(\mathrm{hd}(N[n])\bigr)_1 = (\mathrm{hd}\,N)_1`$ である。
  [T.oper_headD](Column.md#t-oper_headD) が $`1 \lt \lvert N\rvert`$ と $`1 \le n`$ のもとで
  $`\mathrm{hd}(N[n]) = \mathrm{hd}\,N`$ を与えるから、第 1 成分どうしも等しい。

- $`\neg(1 \lt \lvert N\rvert)`$ のとき。$`\lvert N\rvert \le 1`$ すなわち $`\lvert N\rvert - 1 = 0`$
  であるから、[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より $`N[n] = N`$ であり、
  両辺は同一である。∎

<a id="t-entry_pair_mem"></a>
## 定理: 列の第 $`j`$ 成分は列の要素 (T.entry_pair_mem)

### 定理

$`j \lt \lvert N\rvert`$ ならば $`(N_{0,j},\ N_{1,j}) \in N`$。

### 証明

$`M_{i,j}`$ の定義（D.entry）より $`N_{0,j} = \pi_1\bigl(N\langle j\rangle\bigr)`$、
$`N_{1,j} = \pi_2\bigl(N\langle j\rangle\bigr)`$ であるから

```math
(N_{0,j},\ N_{1,j}) = N\langle j\rangle
```

である。仮定 $`j \lt \lvert N\rvert`$ より D.entry の $`N\langle j\rangle`$ は第 1 の場合になり
$`N\langle j\rangle = N_j`$、すなわち $`N`$ の第 $`j`$ 要素である。列の第 $`j`$ 要素は
$`j \lt \lvert N\rvert`$ のとき列の要素である。∎

<a id="t-oper_mem_ge"></a>
## 定理: 展開は行 0 の値の下界を保つ (T.oper_mem_ge)

### 定理

$`\forall p \in N,\ c \le p_1`$ ならば、任意の $`n`$ に対し $`\forall p \in N[n],\ c \le p_1`$。

### 証明

$`j_1 := \lvert N\rvert - 1`$ とおく。$`j_1 = 0`$ か否かで場合分けする。

**(I) $`j_1 = 0`$ のとき。** [T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より
$`N[n] = N`$ であるから、仮定そのものである。

**(II) $`j_1 \ne 0`$ のとき。** $`i_1 := \mathrm{idx}_1(N, j_1)`$ とおき、
$`\mathrm{hasParent}(N, i_1, j_1)`$ が成り立つか否かで分ける。

**(II-a) $`\mathrm{hasParent}(N, i_1, j_1)`$ のとき。**
$`N_{0,j_1} = 0`$ とすると
[T.no_hasParent_of_row0_zero](Column.md#t-no_hasParent_of_row0_zero) により矛盾するから
$`0 \lt N_{0,j_1}`$ であり、とくに $`\neg(N_{0,j_1} = 0 \wedge N_{1,j_1} = 0)`$ である。
よって [T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) が適用でき、
$`j_0 := \mathrm{par}^N_{i_1}(j_1)`$ として

```math
N[n] = (N_0,\dots,N_{j_0-1}) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(N_{0,j} + k\,d_0,\ N_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
```

である。$`p \in N[n]`$ を取り、$`p`$ がどの部分の要素かで分ける。

- $`p \in (N_0,\dots,N_{j_0-1})`$ のとき。これは $`N`$ の先頭部分列であるから $`p \in N`$ であり、
  仮定より $`c \le p_1`$ である。

- $`p \in B_k`$ のとき。ある $`j`$（$`j_0 \le j \lt j_1`$）について
  $`p = (N_{0,j} + k\,d_0,\ N_{1,j})`$ である。$`j \lt j_1 \lt \lvert N\rvert`$ であるから
  [T.entry_pair_mem](#t-entry_pair_mem) より $`(N_{0,j}, N_{1,j}) \in N`$ であり、
  仮定より $`c \le N_{0,j}`$ である。したがって
  $`c \le N_{0,j} \le N_{0,j} + k\,d_0 = p_1`$ である。

**(II-b) $`\neg\,\mathrm{hasParent}(N, i_1, j_1)`$ のとき。**
$`N_{0,j_1} = 0 \wedge N_{1,j_1} = 0`$ が成り立つなら
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) により、成り立たないなら
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) により、
いずれにせよ $`N[n] = \mathrm{Pred}\,N`$ である。
$`\mathrm{Pred}`$ の定義（D.Pred）の場合分けにより $`\mathrm{Pred}\,N`$ は $`N`$ 自身か
$`\mathrm{dropLast}\,N`$ である。前者なら仮定そのものであり、後者なら
$`\mathrm{dropLast}\,N`$ の要素は $`N`$ の要素であるから仮定が適用できる。∎

<a id="t-graft_mem_ge"></a>
## 定理: 接ぎ木は行 0 の値の下界を保つ (T.graft_mem_ge)

### 定理

$`N \ne ()`$ かつ $`\forall p \in N,\ c \le p_1`$ ならば、任意の $`z`$ に対し
$`\forall p \in \mathrm{graft}(N,z),\ c \le p_1`$。

### 証明

$`N \ne ()`$ より $`0 \lt \lvert N\rvert`$ であるから $`j_1 := \lvert N\rvert - 1 \lt \lvert N\rvert`$ である。
[T.entry_pair_mem](#t-entry_pair_mem) より $`(N_{0,j_1}, N_{1,j_1}) \in N`$ であり、
仮定より

```math
c \le N_{0,j_1} .
```

$`\mathrm{graft}`$ の定義（D.graft）より
$`\mathrm{graft}(N,z) = \mathrm{dropLast}\,N \mathbin{+\!\!+} z^{+N_{0,j_1}}`$ である。
$`p \in \mathrm{graft}(N,z)`$ を取り、どちらの部分の要素かで分ける。

- $`p \in \mathrm{dropLast}\,N`$ のとき。$`\mathrm{dropLast}\,N`$ の要素は $`N`$ の要素であるから、
  仮定より $`c \le p_1`$ である。

- $`p \in z^{+N_{0,j_1}}`$ のとき。ある $`q \in z`$ について
  $`p = (q_1 + N_{0,j_1},\ q_2)`$ である。上で示した $`c \le N_{0,j_1}`$ と
  $`N_{0,j_1} \le q_1 + N_{0,j_1}`$ から $`c \le p_1`$ である。∎

<a id="t-graft_head_eq"></a>
## 定理: 接ぎ木は先頭の行 0 の値を変えない (T.graft_head_eq)

### 定理

$`N \ne ()`$、$`\mathrm{based}(z)`$、$`\mathrm{graft}(N,z) \ne ()`$ ならば

```math
\bigl(\mathrm{graft}(N,z)\bigr)_{0,0} = N_{0,0} .
```

### 証明

$`N \ne ()`$ より $`N = b_0 :: N'`$ と書ける。$`N'`$ が空か否かで場合分けする。

**(a) $`N = (b_0)`$ のとき。** $`\lvert N\rvert - 1 = 0`$ であり、
$`M_{i,j}`$ の定義（D.entry）より $`N_{0,0} = (b_0)_1`$ である。
$`\mathrm{dropLast}\,(b_0) = ()`$ であるから $`\mathrm{graft}`$ の定義（D.graft）より

```math
\mathrm{graft}(N, z) = z^{+(b_0)_1} .
```

仮定 $`\mathrm{graft}(N,z) \ne ()`$ よりこれは空でなく、したがって $`z \ne ()`$ である。
$`z = z_0 :: z'`$ と書くと、$`\mathrm{based}`$ の定義（D.based）と D.entry より
$`z_{0,0} = (z_0)_1 = 0`$ である。$`z^{+(b_0)_1}`$ の先頭は
$`\bigl((z_0)_1 + (b_0)_1,\ (z_0)_2\bigr) = \bigl((b_0)_1,\ (z_0)_2\bigr)`$ であるから、
D.entry より

```math
\bigl(\mathrm{graft}(N,z)\bigr)_{0,0} = (b_0)_1 = N_{0,0} .
```

**(b) $`N = b_0 :: b_1 :: N''`$ のとき。**
$`\mathrm{dropLast}\,N = b_0 :: \mathrm{dropLast}(b_1 :: N'')`$ であり、これは空でなく先頭は $`b_0`$ である。
したがって $`\mathrm{graft}(N,z) = \mathrm{dropLast}\,N \mathbin{+\!\!+} z^{+N_{0,\lvert N\rvert-1}}`$ の
先頭も $`b_0`$ である。D.entry より

```math
\bigl(\mathrm{graft}(N,z)\bigr)_{0,0} = (b_0)_1 = N_{0,0} . \qquad \blacksquare
```

<a id="t-XA_closed"></a>
## 定理: $`A_u\bigl(X^{(A)}\bigr) \subseteq X^{(A)}`$ (T.XA_closed)

### 定理

$`X \subseteq \mathrm{PairSeq}`$ が $`\forall M,\ M \in A_u(X) \to M \in X`$ をみたし、
$`A \in X`$ とする。このとき

```math
\forall M,\ M \in A_u\bigl(X^{(A)}\bigr) \to M \in X^{(A)} .
```

### 証明

$`B \in A_u(X^{(A)})`$ とする。$`X^{(A)}`$ の定義（D.XA）より、
$`\mathrm{rsum}(A,B)`$ を仮定して $`A \mathbin{+\!\!+} B \in X`$ を示せばよい。

$`B = ()`$ のときは $`A \mathbin{+\!\!+} () = A \in X`$ である。以下 $`B \ne ()`$、
すなわち $`0 \lt \lvert B\rvert`$ とする。$`\mathrm{rsum}(A,B)`$ の定義（D.rsum）より

```math
(\ast)\qquad \forall p \in B,\ B_{0,0} \le p_1,
\qquad\qquad
(\ast\ast)\qquad \forall p \in A,\ B_{0,0} \le p_1
```

が成り立つ。$`A_u`$ の定義（D.Aop）の 3 分岐で場合分けする。

**分岐 (1)：$`\lvert B\rvert \le 1 \wedge B_{1,0} = 0`$ のとき。**
$`0 \lt \lvert B\rvert`$ と合わせて $`\lvert B\rvert = 1`$ である。$`A`$ が空か否かで分ける。

**$`A = ()`$ のとき。** 仮定より $`B \in A_u(X)`$（分岐 (1) そのもの）であるから
$`B \in X`$ であり、$`A \mathbin{+\!\!+} B = B \in X`$ である。

**$`A \ne ()`$ のとき。** $`0 \lt \lvert A\rvert`$ である。
$`\lvert A \mathbin{+\!\!+} B\rvert = \lvert A\rvert + 1`$ であるから

```math
\lvert A \mathbin{+\!\!+} B\rvert - 1 = \lvert A\rvert + 0 .
```

まず、任意の $`i`$ について $`\neg\,\mathrm{hasParent}(A \mathbin{+\!\!+} B,\ i,\ \lvert A \mathbin{+\!\!+} B\rvert - 1)`$
である。実際これが成り立つとすると、$`0 \lt \lvert B\rvert`$ より
[T.hasParent_append_gen](#t-hasParent_append_gen) を $`j := 0`$ に適用して
$`\mathrm{hasParent}(B, i, 0)`$ を得る。$`\mathrm{hasParent}`$ の定義（D.hasParent）より
$`j_0 \to^B_i 0`$ なる $`j_0`$ が存在するが、
[T.nextR_index_lt](Decrease.md#t-nextR_index_lt) より $`j_0 \lt 0`$ となり矛盾する。

次に $`\mathrm{natDom}(A \mathbin{+\!\!+} B)`$ を示す。$`\lvert B\rvert - 1 = 0`$ であるから
$`B_{1,\lvert B\rvert-1} = B_{1,0} = 0`$ であり、[T.natDom_iff](#t-natDom_iff) の右辺の
第 1 選言が成り立つので $`\mathrm{natDom}(B)`$ である。
[T.natDom_append](#t-natDom_append) より $`\mathrm{natDom}(A \mathbin{+\!\!+} B)`$ である。

最後に、任意の $`n \ge 1`$ に対し $`(A \mathbin{+\!\!+} B)[n] = A \in X`$ を示す。
$`2 \le \lvert A \mathbin{+\!\!+} B\rvert`$ であるから $`\lvert A \mathbin{+\!\!+} B\rvert - 1 \ne 0`$ である。
$`J := \lvert A \mathbin{+\!\!+} B\rvert - 1`$ と略記すると、
$`(A \mathbin{+\!\!+} B)_{0,J} = 0 \wedge (A \mathbin{+\!\!+} B)_{1,J} = 0`$ が成り立つなら
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) により、成り立たないなら
上で示した親の非存在と
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) により、
いずれにせよ $`(A \mathbin{+\!\!+} B)[n] = \mathrm{Pred}(A \mathbin{+\!\!+} B)`$ である。
$`2 \le \lvert A \mathbin{+\!\!+} B\rvert`$ より $`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合が選ばれ、
$`B \ne ()`$ より

```math
\mathrm{Pred}(A \mathbin{+\!\!+} B) = \mathrm{dropLast}(A \mathbin{+\!\!+} B)
  = A \mathbin{+\!\!+} \mathrm{dropLast}\,B = A \mathbin{+\!\!+} () = A
```

である（$`\lvert B\rvert = 1`$ より $`\mathrm{dropLast}\,B = ()`$）。よって
$`(A \mathbin{+\!\!+} B)[n] = A \in X`$ である。

以上により $`A \mathbin{+\!\!+} B`$ は $`A_u`$ の定義（D.Aop）の分岐 (2) をみたす。
すなわち $`A \mathbin{+\!\!+} B \in A_u(X)`$ であり、仮定より $`A \mathbin{+\!\!+} B \in X`$ である。

**分岐 (2)：$`\mathrm{natDom}(B) \wedge \forall n \ge 1,\ B[n] \in X^{(A)}`$ のとき。**
$`2 \le \lvert B\rvert`$ か否かで分ける。

**$`2 \le \lvert B\rvert`$ のとき。** [T.natDom_append](#t-natDom_append) より
$`\mathrm{natDom}(A \mathbin{+\!\!+} B)`$ である。$`n \ge 1`$ を取ると
[T.oper_append_gen](#t-oper_append_gen) より

```math
(A \mathbin{+\!\!+} B)[n] = A \mathbin{+\!\!+} B[n]
```

である。$`B[n] \in X^{(A)}`$ であるから、$`A \mathbin{+\!\!+} B[n] \in X`$ を得るには
$`\mathrm{rsum}(A,\ B[n])`$ を確かめればよい。
[T.oper_head_eq](#t-oper_head_eq) より $`(B[n])_{0,0} = B_{0,0}`$ である。
$`p \in A \mathbin{+\!\!+} B[n]`$ を取ると、$`p \in A`$ のときは $`(\ast\ast)`$ より
$`B_{0,0} \le p_1`$、$`p \in B[n]`$ のときは $`(\ast)`$ と
[T.oper_mem_ge](#t-oper_mem_ge)（$`c := B_{0,0}`$）より $`B_{0,0} \le p_1`$ である。
よって $`\mathrm{rsum}(A, B[n])`$ が成り立ち、$`(A \mathbin{+\!\!+} B)[n] \in X`$ である。
すなわち $`A \mathbin{+\!\!+} B`$ は分岐 (2) をみたすから、仮定より $`A \mathbin{+\!\!+} B \in X`$ である。

**$`\neg(2 \le \lvert B\rvert)`$ のとき。** $`\lvert B\rvert \le 1`$ すなわち $`\lvert B\rvert - 1 = 0`$ であるから
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) より $`B[1] = B`$ である。
分岐 (2) の第 2 連言子を $`n := 1`$ に適用すると $`B[1] \in X^{(A)}`$、すなわち
$`B \in X^{(A)}`$ である。仮定 $`\mathrm{rsum}(A,B)`$ をこれに適用して
$`A \mathbin{+\!\!+} B \in X`$ を得る。

**分岐 (3)、すなわち $`m \lt u`$、$`\mathrm{domT}(B,m)`$、
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(B,z) \in X^{(A)}`$ をみたす $`m`$ があるとき。**
[T.domT_append](#t-domT_append) より $`\mathrm{domT}(A \mathbin{+\!\!+} B,\ m)`$ である。
$`z \in W_m`$ が $`\mathrm{based}(z)`$ をみたすとする。
[T.graft_append](#t-graft_append) より

```math
\mathrm{graft}(A \mathbin{+\!\!+} B,\ z) = A \mathbin{+\!\!+} \mathrm{graft}(B,z)
```

である。$`\mathrm{graft}(B,z) \in X^{(A)}`$ であるから、これが $`X`$ に属することを示すには
$`\mathrm{rsum}\bigl(A,\ \mathrm{graft}(B,z)\bigr)`$ を確かめればよい。

- $`\mathrm{graft}(B,z) = ()`$ のとき。D.entry より $`()_{0,0} = 0`$ であるから、
  $`\mathrm{rsum}`$ の定義（D.rsum）の要求は $`\forall p \in A \mathbin{+\!\!+} (),\ 0 \le p_1`$ であり、
  自然数について常に成り立つ。

- $`\mathrm{graft}(B,z) \ne ()`$ のとき。[T.graft_head_eq](#t-graft_head_eq) より
  $`\bigl(\mathrm{graft}(B,z)\bigr)_{0,0} = B_{0,0}`$ である。
  $`p \in A \mathbin{+\!\!+} \mathrm{graft}(B,z)`$ を取ると、$`p \in A`$ のときは $`(\ast\ast)`$ より
  $`B_{0,0} \le p_1`$、$`p \in \mathrm{graft}(B,z)`$ のときは $`(\ast)`$ と
  [T.graft_mem_ge](#t-graft_mem_ge)（$`c := B_{0,0}`$）より $`B_{0,0} \le p_1`$ である。

よって $`A \mathbin{+\!\!+} B`$ は同じ $`m`$ で $`A_u`$ の分岐 (3) をみたし、
仮定より $`A \mathbin{+\!\!+} B \in X`$ である。∎

<a id="t-W_add"></a>
## 定理: $`W_u`$ の連結による加法性 (T.W_add)

### 定理

$`A \in W_u`$、$`B \in W_u`$、$`\mathrm{rsum}(A,B)`$ ならば $`A \mathbin{+\!\!+} B \in W_u`$。

### 証明

[T.A1_intro](#t-A1_intro) は $`\forall M,\ M \in A_u(W_u) \to M \in W_u`$ である。
これと $`A \in W_u`$ に [T.XA_closed](#t-XA_closed) を $`X := W_u`$ として適用すると

```math
\forall M,\ M \in A_u\bigl((W_u)^{(A)}\bigr) \to M \in (W_u)^{(A)}
```

を得る。これは [T.A2'](#t-A2') の仮定であるから $`W_u \subseteq (W_u)^{(A)}`$ である。
$`B \in W_u`$ よりとくに $`B \in (W_u)^{(A)}`$ であり、$`X^{(A)}`$ の定義（D.XA）に
仮定 $`\mathrm{rsum}(A,B)`$ を与えて $`A \mathbin{+\!\!+} B \in W_u`$ を得る。∎

<a id="t-graft_Om"></a>
## 定理: 単一列への接ぎ木 (T.graft_Om)

### 定理

任意の $`v \in \mathbb{N}`$、$`z \in \mathrm{PairSeq}`$ に対し
$`\mathrm{graft}\bigl(\bigl((0,v)\bigr),\ z\bigr) = z`$。

### 証明

$`\bigl((0,v)\bigr)`$ は長さ $`1`$ の列であるから $`\lvert \bigl((0,v)\bigr)\rvert - 1 = 0`$ であり、
$`M_{i,j}`$ の定義（D.entry）より $`\bigl((0,v)\bigr)_{0,0} = 0`$ である。
また $`\mathrm{dropLast}\,\bigl((0,v)\bigr) = ()`$ である。
よって $`\mathrm{graft}`$ の定義（D.graft）より

```math
\mathrm{graft}\bigl(\bigl((0,v)\bigr),\ z\bigr) = () \mathbin{+\!\!+} z^{+0} = z
```

である（各対の第 1 成分に $`0`$ を足しても列は変わらない）。∎

<a id="t-domT_Om"></a>
## 定理: 単一列の $`\mathrm{domT}`$ (T.domT_Om)

### 定理

任意の $`m \in \mathbb{N}`$ に対し $`\mathrm{domT}\bigl(\bigl((0,m+1)\bigr),\ m\bigr)`$。

### 証明

$`M := \bigl((0,m+1)\bigr)`$ とおく。$`\lvert M\rvert - 1 = 0`$ である。
$`\mathrm{domT}`$ の定義（D.domT）の 2 つの連言子を示す。

第 1 連言子は $`M_{1,0} = m+1`$ であり、$`M_{i,j}`$ の定義（D.entry）よりこれは成り立つ。

第 2 連言子 $`\neg\,\mathrm{hasParent}(M, 1, 0)`$ を示す。
$`\mathrm{hasParent}(M,1,0)`$ とすると、$`\mathrm{hasParent}`$ の定義（D.hasParent）より
$`j_0 \to^M_1 0`$ なる $`j_0`$ が存在する。$`\to^M_i`$ の定義（D.nextR）で $`i = 1 \ne 0`$ であるから
これは $`j_0 \to^M_1 0`$（行 $`1`$ の親子関係）であり、その定義（D.nextrel1）の第 3 条件は
$`j_0 \lt 0`$ である。自然数にこれをみたすものはないから矛盾する。∎

<a id="t-Om_mem_W"></a>
## 定理: $`\bigl((0,v)\bigr) \in W_v`$ (T.Om_mem_W)

### 定理

任意の $`v \in \mathbb{N}`$ に対し $`\bigl((0,v)\bigr) \in W_v`$。

### 証明

$`v`$ が $`0`$ か後続数かで場合分けする。

**(a) $`v = 0`$ のとき。** $`\lvert \bigl((0,0)\bigr)\rvert = 1 \le 1`$ であり、
$`M_{i,j}`$ の定義（D.entry）より $`\bigl((0,0)\bigr)_{1,0} = 0`$ である。
よって $`A_0`$ の定義（D.Aop）の分岐 (1) が成り立ち、
[T.A1_intro](#t-A1_intro) より $`\bigl((0,0)\bigr) \in W_0`$ である。

**(b) $`v = w + 1`$ のとき。** $`A_{w+1}`$ の定義（D.Aop）の分岐 (3) を $`m := w`$ で示す。
$`w \lt w+1`$ である。[T.domT_Om](#t-domT_Om) より
$`\mathrm{domT}\bigl(\bigl((0,w+1)\bigr),\ w\bigr)`$ である。
$`z \in W_w`$ を取ると（$`\mathrm{based}(z)`$ は使わない）、
[T.graft_Om](#t-graft_Om) より $`\mathrm{graft}\bigl(\bigl((0,w+1)\bigr),\ z\bigr) = z`$ であり、
[T.W_mono](#t-W_mono) を $`w \le w+1`$ に適用して $`z \in W_{w+1}`$ を得る。
よって分岐 (3) が成り立ち、[T.A1_intro](#t-A1_intro) より
$`\bigl((0,w+1)\bigr) \in W_{w+1}`$ である。∎

<a id="d-Wstar"></a>
## 定義: $`W^{*}`$ (D.Wstar)

```math
W^{*} := \bigl\{\, R \in \mathrm{PairSeq} \ \bigm|\
  \mathrm{argOK}(R) \to \forall v \in \mathbb{N},\ (0,v) :: R \in W_v \,\bigr\} .
```

<a id="d-tow"></a>
## 定義: 塔 (D.tow)

$`v \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ に対し、列 $`\mathrm{tow}_v(R,k)`$ を
$`k`$ に関する再帰で定める。

```math
\mathrm{tow}_v(R, 0) := (),
\qquad
\mathrm{tow}_v(R, k+1) := (0,v) :: \mathrm{graft}\bigl(R,\ \mathrm{tow}_v(R,k)\bigr).
```

再帰呼び出しの引数は $`k`$ であり $`k+1`$ より真に小さいから、この定義は整合的である。

<a id="t-graft_cons"></a>
## 定理: 根を越える接ぎ木 (T.graft_cons)

### 定理

$`R \ne ()`$ ならば

```math
\mathrm{graft}\bigl((0,v) :: R,\ z\bigr) = (0,v) :: \mathrm{graft}(R, z).
```

### 証明

[T.graft_append](#t-graft_append) を $`A := \bigl((0,v)\bigr)`$、$`P := R`$ に適用すると

```math
\mathrm{graft}\bigl(\bigl((0,v)\bigr) \mathbin{+\!\!+} R,\ z\bigr)
  = \bigl((0,v)\bigr) \mathbin{+\!\!+} \mathrm{graft}(R,z)
```

を得る。長さ $`1`$ の列との連結は先頭への付加であるから
$`\bigl((0,v)\bigr) \mathbin{+\!\!+} R = (0,v) :: R`$ であり、
$`\bigl((0,v)\bigr) \mathbin{+\!\!+} \mathrm{graft}(R,z) = (0,v) :: \mathrm{graft}(R,z)`$ である。∎

<a id="t-entry_cons"></a>
## 定理: 先頭付加による添字のずれ (T.entry_cons)

### 定理

任意の $`p \in \mathbb{N}\times\mathbb{N}`$、$`R \in \mathrm{PairSeq}`$、$`i, j \in \mathbb{N}`$ に対し

```math
(p :: R)_{i,\ j+1} = R_{i,j} .
```

### 証明

[T.entry_append_right](Column.md#t-entry_append_right) を $`A := (p)`$、$`T := R`$ に適用すると

```math
\bigl((p) \mathbin{+\!\!+} R\bigr)_{i,\ \lvert (p)\rvert + j} = R_{i,j}
```

を得る。$`(p) \mathbin{+\!\!+} R = p :: R`$、$`\lvert (p)\rvert = 1`$ であり、
$`\mathbb{N}`$ の加法の可換律より $`1 + j = j + 1`$ である。∎

<a id="t-nextR_cons"></a>
## 定理: 先頭付加による親子関係のずれ (T.nextR_cons)

### 定理

```math
(j_0 + 1) \to^{p :: R}_i (j_1 + 1) \iff j_0 \to^{R}_i j_1 .
```

### 証明

[T.nextR_append_right](Column.md#t-nextR_append_right) を $`A := (p)`$、$`T := R`$ に適用すると

```math
\bigl(\lvert (p)\rvert + j_0\bigr) \to^{(p) \mathbin{+\!\!+} R}_i \bigl(\lvert (p)\rvert + j_1\bigr)
  \iff j_0 \to^R_i j_1
```

を得る。$`(p) \mathbin{+\!\!+} R = p :: R`$、$`\lvert (p)\rvert = 1`$ であり、
$`1 + j_0 = j_0 + 1`$、$`1 + j_1 = j_1 + 1`$ である。∎

<a id="t-le0_cons"></a>
## 定理: 先頭付加による祖先関係のずれ (T.le0_cons)

### 定理

```math
(j_0 + 1) \le^{p :: R}_0 (j_1 + 1) \iff j_0 \le^{R}_0 j_1 .
```

### 証明

[T.le0_append_right](Column.md#t-le0_append_right) を $`A := (p)`$、$`T := R`$ に適用すると

```math
\bigl(\lvert (p)\rvert + j_0\bigr) \le^{(p) \mathbin{+\!\!+} R}_0 \bigl(\lvert (p)\rvert + j_1\bigr)
  \iff j_0 \le^R_0 j_1
```

を得る。$`(p) \mathbin{+\!\!+} R = p :: R`$、$`\lvert (p)\rvert = 1`$ であり、
$`1 + j_0 = j_0 + 1`$、$`1 + j_1 = j_1 + 1`$ である。∎

<a id="t-idx1_cons"></a>
## 定理: 先頭付加による探索行のずれ (T.idx1_cons)

### 定理

```math
\mathrm{idx}_1(p :: R,\ j+1) = \mathrm{idx}_1(R,\ j) .
```

### 証明

[T.idx1_append_right](Column.md#t-idx1_append_right) を $`A := (p)`$、$`T := R`$ に適用すると
$`\mathrm{idx}_1\bigl((p) \mathbin{+\!\!+} R,\ \lvert (p)\rvert + j\bigr) = \mathrm{idx}_1(R,j)`$ を得る。
$`(p) \mathbin{+\!\!+} R = p :: R`$、$`\lvert (p)\rvert = 1`$ であり、$`1 + j = j + 1`$ である。∎

<a id="t-hasParent_zero_iff"></a>
## 定理: 行 0 の親の存在判定 (T.hasParent_zero_iff)

### 定理

$`b \lt \lvert M\rvert`$ ならば

```math
\mathrm{hasParent}(M, 0, b) \iff \exists k,\ \bigl(k \lt b \wedge M_{0,k} \lt M_{0,b}\bigr).
```

### 証明

$`\to^M_i`$ の定義（D.nextR）で $`i = 0`$ であるから、以下 $`j_0 \to^M_0 j_1`$ は
行 $`0`$ の親子関係（D.nextrel0）である。

**（左から右）** $`\mathrm{hasParent}(M,0,b)`$ とすると、
$`\mathrm{hasParent}`$ の定義（D.hasParent）より $`k \to^M_0 b`$ なる $`k`$ が存在する。
$`\to^M_0`$ の定義（D.nextrel0）の第 3 条件が $`k \lt b`$、第 4 条件が
$`M_{0,k} \lt M_{0,b}`$ であるから、この $`k`$ が求めるものである。

**（右から左）** 述語

```math
P(t) :\equiv \bigl(t \lt b \wedge M_{0,t} \lt M_{0,b}\bigr)
```

をみたす $`k`$ が与えられたとする。集合 $`\{\, t \mid t \le b \wedge P(t)\,\}`$ は
$`k`$ を含む（$`P(k)`$ より $`k \lt b`$、とくに $`k \le b`$）ので空でなく、$`b`$ で上に有界であるから
最大値をもつ。それを $`g`$ とおく。このとき

```math
(\dagger)\qquad P(g),
\qquad\qquad
(\ddagger)\qquad \forall t,\ P(t) \to t \le g
```

が成り立つ（$`(\ddagger)`$ は、$`P(t)`$ から $`t \lt b`$ すなわち $`t \le b`$ が従い、
$`g`$ が最大値であることによる）。

まず $`g \to^M_0 b`$ を示す。$`\to^M_0`$ の定義（D.nextrel0）の 5 条件を順に確かめる。

- (1) $`g \lt \lvert M\rvert`$：$`(\dagger)`$ より $`g \lt b`$ であり、仮定より $`b \lt \lvert M\rvert`$ である。
- (2) $`b \lt \lvert M\rvert`$：仮定である。
- (3) $`g \lt b`$：$`(\dagger)`$ の第 1 連言子である。
- (4) $`M_{0,g} \lt M_{0,b}`$：$`(\dagger)`$ の第 2 連言子である。
- (5) $`\forall l,\ (g \lt l \wedge l \lt b) \to M_{0,b} \le M_{0,l}`$：
  $`g \lt l`$、$`l \lt b`$ なる $`l`$ を取り、$`M_{0,b} \le M_{0,l}`$ が成り立たないとすると
  $`M_{0,l} \lt M_{0,b}`$ であり、$`l \lt b`$ と合わせて $`P(l)`$ である。
  $`(\ddagger)`$ より $`l \le g`$ となり $`g \lt l`$ に矛盾する。

次に一意性を示す。$`y \to^M_0 b`$ とする。D.nextrel0 の第 3・第 4 条件より
$`y \lt b`$ かつ $`M_{0,y} \lt M_{0,b}`$、すなわち $`P(y)`$ であるから、
$`(\ddagger)`$ より $`y \le g`$ である。$`y \lt g`$ と仮定すると、
$`y \to^M_0 b`$ の第 5 条件を $`j := g`$ に適用できて（$`y \lt g`$ かつ $`g \lt b`$）
$`M_{0,b} \le M_{0,g}`$ を得るが、これは $`(\dagger)`$ の $`M_{0,g} \lt M_{0,b}`$ に矛盾する。
よって $`y = g`$ である。

以上により $`g`$ は $`j_0 \to^M_0 b`$ をみたす一意の $`j_0`$ であり、
$`\mathrm{hasParent}(M,0,b)`$ が成り立つ。∎

<a id="t-le0_cons_zero"></a>
## 定理: 主要ブロックの根はすべての列の祖先 (T.le0_cons_zero)

### 定理

$`\mathrm{argOK}(R)`$ ならば、任意の $`v \in \mathbb{N}`$ と $`j \lt \lvert R\rvert`$ に対し

```math
0 \le^{(0,v) :: R}_0 (j+1).
```

### 証明

$`M := (0,v) :: R`$ とおく。$`j`$ に関する強帰納法を行う。帰納法の述語は

```math
\Phi(j) :\equiv \bigl(j \lt \lvert R\rvert \to 0 \le^{M}_0 (j+1)\bigr)
```

であり、帰納法の仮定は「$`j' \lt j`$ なるすべての $`j'`$ について $`\Phi(j')`$」である。

$`j \lt \lvert R\rvert`$ とする。$`\lvert M\rvert = \lvert R\rvert + 1`$ であるから
$`j + 1 \lt \lvert M\rvert`$ である。次の 2 つを用意する。

1. $`M_{0,j+1} = R_{0,j}`$ であり、これは正である。実際
   [T.entry_cons](#t-entry_cons) より $`M_{0,j+1} = R_{0,j}`$ であり、
   $`j \lt \lvert R\rvert`$ と [T.entry_pair_mem](#t-entry_pair_mem) より
   $`(R_{0,j}, R_{1,j}) \in R`$ であるから、$`\mathrm{argOK}`$ の定義（D.argOK）より
   $`0 \lt R_{0,j}`$ である。
2. $`M_{0,0} = 0`$。$`M`$ の先頭は $`(0,v)`$ であるから
   $`M_{i,j}`$ の定義（D.entry）による。

1 と 2 より $`M_{0,0} \lt M_{0,j+1}`$ であり、$`0 \lt j+1`$ であるから、
$`k := 0`$ が [T.hasParent_zero_iff](#t-hasParent_zero_iff) の右辺の存在条件をみたす。
よって $`\mathrm{hasParent}(M, 0, j+1)`$ が成り立ち、
$`\mathrm{hasParent}`$ の定義（D.hasParent）より $`k \to^M_0 (j+1)`$ なる $`k`$ が存在する。
$`k`$ が $`0`$ か否かで場合分けする。

**(a) $`k = 0`$ のとき。** $`0 \to^M_0 (j+1)`$ であるから、長さ $`1`$ の鎖として
$`0 \mathbin{(\to^M_0)^{*}} (j+1)`$ が成り立つ。$`0 \lt \lvert M\rvert`$、
$`j+1 \lt \lvert M\rvert`$ と合わせ、$`\le^M_0`$ の定義（D.le0）の 3 条件がすべて成り立つから
$`0 \le^M_0 (j+1)`$ である。

**(b) $`k \ne 0`$ のとき。** $`k = k' + 1`$ と書ける。
$`\to^M_0`$ の定義（D.nextrel0）の第 3 条件より $`k'+1 \lt j+1`$、すなわち $`k' \lt j`$ である。
また $`k' \lt j \lt \lvert R\rvert`$ である。帰納法の仮定 $`\Phi(k')`$ を適用して
$`0 \le^M_0 (k'+1)`$ を得る。$`\le^M_0`$ の定義（D.le0）の第 3 条件より
$`0 \mathbin{(\to^M_0)^{*}} (k'+1)`$ であり、この鎖の末尾に
$`k'+1 = k \to^M_0 (j+1)`$ を継ぎ足すと $`0 \mathbin{(\to^M_0)^{*}} (j+1)`$ を得る。
$`0 \lt \lvert M\rvert`$、$`j+1 \lt \lvert M\rvert`$ と合わせて $`0 \le^M_0 (j+1)`$ である。∎

<a id="t-len_succ"></a>
## 定理: 空でない列の長さ (T.len_succ)

### 定理

$`R \ne ()`$ ならば $`\lvert R\rvert = (\lvert R\rvert - 1) + 1`$。

### 証明

$`R \ne ()`$ より $`0 \lt \lvert R\rvert`$ である。自然数 $`x`$ が $`0 \lt x`$ をみたすとき、
切り捨て減法について $`(x - 1) + 1 = x`$ である。∎

<a id="t-entry_cons_last"></a>
## 定理: 先頭付加後の末尾成分 (T.entry_cons_last)

### 定理

$`R \ne ()`$ ならば、任意の $`p`$、$`i`$ に対し

```math
(p :: R)_{i,\ \lvert R\rvert} = R_{i,\ \lvert R\rvert - 1} .
```

### 証明

[T.len_succ](#t-len_succ) より $`\lvert R\rvert = (\lvert R\rvert - 1) + 1`$ であるから、
左辺は $`(p :: R)_{i,\ (\lvert R\rvert - 1) + 1}`$ に書き換えられる。
これに [T.entry_cons](#t-entry_cons) を $`j := \lvert R\rvert - 1`$ として適用すればよい。∎

<a id="t-le0_cons_last"></a>
## 定理: 先頭付加後の末尾への祖先関係 (T.le0_cons_last)

### 定理

$`R \ne ()`$ ならば、任意の $`p`$、$`j`$ に対し

```math
(j+1) \le^{p :: R}_0 \lvert R\rvert \iff j \le^{R}_0 (\lvert R\rvert - 1).
```

### 証明

[T.len_succ](#t-len_succ) より $`\lvert R\rvert = (\lvert R\rvert - 1) + 1`$ であるから、
左辺は $`(j+1) \le^{p :: R}_0 \bigl((\lvert R\rvert - 1) + 1\bigr)`$ に書き換えられる。
これに [T.le0_cons](#t-le0_cons) を $`j_0 := j`$、$`j_1 := \lvert R\rvert - 1`$ として
適用すればよい。∎

<a id="t-nextR_cons_last"></a>
## 定理: 先頭付加後の末尾への親子関係 (T.nextR_cons_last)

### 定理

$`R \ne ()`$ ならば、任意の $`p`$、$`i`$、$`j`$ に対し

```math
(j+1) \to^{p :: R}_i \lvert R\rvert \iff j \to^{R}_i (\lvert R\rvert - 1).
```

### 証明

[T.len_succ](#t-len_succ) より $`\lvert R\rvert = (\lvert R\rvert - 1) + 1`$ であるから、
左辺は $`(j+1) \to^{p :: R}_i \bigl((\lvert R\rvert - 1) + 1\bigr)`$ に書き換えられる。
これに [T.nextR_cons](#t-nextR_cons) を $`j_0 := j`$、$`j_1 := \lvert R\rvert - 1`$ として
適用すればよい。∎

<a id="t-idx1_cons_last"></a>
## 定理: 先頭付加後の末尾の探索行 (T.idx1_cons_last)

### 定理

$`R \ne ()`$ ならば、任意の $`p`$ に対し

```math
\mathrm{idx}_1\bigl(p :: R,\ \lvert R\rvert\bigr) = \mathrm{idx}_1\bigl(R,\ \lvert R\rvert - 1\bigr).
```

### 証明

[T.len_succ](#t-len_succ) より $`\lvert R\rvert = (\lvert R\rvert - 1) + 1`$ であるから、
左辺は $`\mathrm{idx}_1\bigl(p :: R,\ (\lvert R\rvert - 1) + 1\bigr)`$ に書き換えられる。
これに [T.idx1_cons](#t-idx1_cons) を $`j := \lvert R\rvert - 1`$ として適用すればよい。∎

<a id="t-cons_len_lt"></a>
## 定理: 先頭付加は長さを増やす (T.cons_len_lt)

### 定理

任意の $`p`$、$`R`$ に対し $`\lvert R\rvert \lt \lvert p :: R\rvert`$。

### 証明

$`\lvert p :: R\rvert = \lvert R\rvert + 1`$ であり、$`\lvert R\rvert \lt \lvert R\rvert + 1`$ である。∎

<a id="t-hasParent_cons_one"></a>
## 定理: 根は行 1 の親になる (T.hasParent_cons_one)

### 定理

$`\mathrm{argOK}(R)`$、$`R \ne ()`$、かつ

```math
\mathrm{hasParent}\bigl(R,\ 1,\ \lvert R\rvert - 1\bigr)
\ \vee\
v \lt R_{1,\ \lvert R\rvert - 1}
```

とする。このとき $`\mathrm{hasParent}\bigl((0,v) :: R,\ 1,\ \lvert R\rvert\bigr)`$。

### 証明

$`M := (0,v) :: R`$ とおく。$`R \ne ()`$ より $`0 \lt \lvert R\rvert`$ であり、
[T.cons_len_lt](#t-cons_len_lt) より $`\lvert R\rvert \lt \lvert M\rvert`$ である。
よって [T.hasParent_one_iff](#t-hasParent_one_iff) を $`j_1 := \lvert R\rvert`$ に適用でき、
示すべきことは $`\mathrm{r1cand}(M,\ \lvert R\rvert,\ j_0)`$ をみたす $`j_0`$ の存在、
すなわち $`\mathrm{r1cand}`$ の定義（D.r1cand）により

```math
j_0 \lt \lvert R\rvert,
\qquad
j_0 \le^{M}_0 \lvert R\rvert,
\qquad
M_{1,j_0} \lt M_{1,\lvert R\rvert}
```

をみたす $`j_0`$ の存在に帰着する。[T.entry_cons_last](#t-entry_cons_last) より

```math
(\sharp)\qquad M_{1,\lvert R\rvert} = R_{1,\lvert R\rvert - 1}
```

である。仮定の選言で場合分けする。

**(a) $`\mathrm{hasParent}(R, 1, \lvert R\rvert - 1)`$ のとき。**
$`\lvert R\rvert - 1 \lt \lvert R\rvert`$ であるから
[T.hasParent_one_iff](#t-hasParent_one_iff) を $`R`$ と $`j_1 := \lvert R\rvert - 1`$ に適用して、
$`\mathrm{r1cand}(R,\ \lvert R\rvert - 1,\ j')`$ をみたす $`j'`$ を取る。すなわち

```math
j' \lt \lvert R\rvert - 1,
\qquad
j' \le^{R}_0 (\lvert R\rvert - 1),
\qquad
R_{1,j'} \lt R_{1,\lvert R\rvert - 1}
```

である。$`j_0 := j' + 1`$ と取る。3 条件を確かめる。

- $`j' \lt \lvert R\rvert - 1`$ より $`j' + 1 \lt \lvert R\rvert`$ である。
- [T.le0_cons_last](#t-le0_cons_last) を $`j := j'`$ に適用して、
  $`j' \le^R_0 (\lvert R\rvert - 1)`$ から $`(j'+1) \le^M_0 \lvert R\rvert`$ を得る。
- [T.entry_cons](#t-entry_cons) より $`M_{1,j'+1} = R_{1,j'}`$ であり、
  $`(\sharp)`$ と合わせて $`M_{1,j'+1} = R_{1,j'} \lt R_{1,\lvert R\rvert-1} = M_{1,\lvert R\rvert}`$ である。

**(b) $`v \lt R_{1,\lvert R\rvert - 1}`$ のとき。** $`j_0 := 0`$ と取る。3 条件を確かめる。

- $`0 \lt \lvert R\rvert`$ である。
- [T.le0_cons_zero](#t-le0_cons_zero) を $`j := \lvert R\rvert - 1`$（これは $`\lvert R\rvert`$ より
  真に小さい）に適用して $`0 \le^M_0 \bigl((\lvert R\rvert - 1) + 1\bigr)`$ を得る。
  [T.len_succ](#t-len_succ) より $`(\lvert R\rvert - 1) + 1 = \lvert R\rvert`$ であるから
  $`0 \le^M_0 \lvert R\rvert`$ である。
- $`M`$ の先頭は $`(0,v)`$ であるから $`M_{i,j}`$ の定義（D.entry）より $`M_{1,0} = v`$ であり、
  仮定と $`(\sharp)`$ より $`M_{1,0} = v \lt R_{1,\lvert R\rvert-1} = M_{1,\lvert R\rvert}`$ である。

いずれの場合も条件をみたす $`j_0`$ が得られたので、
[T.hasParent_one_iff](#t-hasParent_one_iff) より
$`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$ である。∎

<a id="t-oper_root_tiling"></a>
## 定理: 親が根のときの展開は先頭ブロックの敷き詰め (T.oper_root_tiling)

### 定理

$`M \in \mathrm{PairSeq}`$、$`n \in \mathbb{N}`$ とし、$`j_1 := \lvert M\rvert - 1`$、
$`i_1 := \mathrm{idx}_1(M, j_1)`$ とおく。次の 4 つを仮定する。

```math
\begin{aligned}
&(1)\ j_1 \ne 0, \cr
&(2)\ \neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr), \cr
&(3)\ \mathrm{hasParent}(M, i_1, j_1), \cr
&(4)\ \mathrm{par}^M_{i_1}(j_1) = 0 .
\end{aligned}
```

さらに

```math
e := \begin{cases} M_{0,j_1} - M_{0,0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
```

とおく。このとき

```math
M[n] = \bigl(\mathrm{dropLast}\,M\bigr)^{+0\cdot e} \mathbin{+\!\!+}
       \bigl(\mathrm{dropLast}\,M\bigr)^{+1\cdot e} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+}
       \bigl(\mathrm{dropLast}\,M\bigr)^{+(n-1)e} .
```

### 証明

仮定 (1)(2)(3) により [T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) が適用できる。
$`j_0 := \mathrm{par}^M_{i_1}(j_1)`$ と書くと、仮定 (4) より $`j_0 = 0`$ であり、
[T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) の $`d_0`$ は

```math
d_0 = \begin{cases} M_{0,j_1} - M_{0,j_0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
= e
```

である。同じ定理の結論で前置部分は $`(M_0,\dots,M_{j_0-1})`$ すなわち $`j_0 = 0`$ より
空列 $`()`$ であるから

```math
M[n] = B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,e,\ M_{1,j})\,\bigr)_{j=0}^{j_1-1}
```

を得る。あとは各 $`k`$ について $`B_k = (\mathrm{dropLast}\,M)^{+k\,e}`$ を示せばよい。

$`\mathrm{dropLast}\,M = \mathrm{take}_{j_1} M`$ である（$`\mathrm{take}_a L`$ は $`L`$ の先頭 $`a`$ 要素からなる列、
$`j_1 = \lvert M\rvert - 1`$）。$`j_1 \le \lvert M\rvert`$ であるから
[T.map_range_entry_eq_take](Column.md#t-map_range_entry_eq_take) が使えて

```math
\bigl(\,(M_{0,j},\ M_{1,j})\,\bigr)_{j=0}^{j_1-1} = \mathrm{take}_{j_1} M = \mathrm{dropLast}\,M
```

である。$`B_k`$ はこの列の各要素の第 1 成分に $`k\,e`$ を足した列にほかならないから、
$`B_k = (\mathrm{dropLast}\,M)^{+k\,e}`$ である。∎

<a id="t-oper_cons_nat"></a>
## 定理: 非崩壊の主要ステップ (T.oper_cons_nat)

### 定理

$`v, n \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ とし、$`k_1 := \lvert R\rvert - 1`$、
$`i := \mathrm{idx}_1(R, k_1)`$ とおく。
$`\mathrm{argOK}(R)`$、$`R \ne ()`$、$`\mathrm{hasParent}(R, i, k_1)`$ を仮定すると

```math
\bigl((0,v) :: R\bigr)[n] = (0,v) :: R[n] .
```

### 証明

$`M := (0,v) :: R`$ と書く。まず次の事実を用意する。

**(i)** $`R \ne ()`$ より $`0 \lt \lvert R\rvert`$。また $`\lvert M\rvert = \lvert R\rvert + 1`$ であるから
$`\lvert M\rvert - 1 = \lvert R\rvert`$、すなわち $`M`$ の最終列の添字は $`\lvert R\rvert`$ である。

**(ii)** $`M_{0,\lvert R\rvert} = R_{0,k_1}`$ かつ $`M_{1,\lvert R\rvert} = R_{1,k_1}`$。
[T.entry_cons_last](#t-entry_cons_last) による。

**(iii)** $`j_0 := \mathrm{par}^R_i(k_1)`$ とおくと $`j_0 \to^R_i k_1`$ であり
（[T.parent_nextR](Decrease.md#t-parent_nextR)）、
$`j_0 \lt k_1`$ である（[T.nextR_index_lt](Decrease.md#t-nextR_index_lt)）。とくに $`k_1 \ne 0`$。

**(iv)** $`0 \lt R_{0,k_1}`$。実際 $`k_1 \lt \lvert R\rvert`$ であるから
[T.entry_pair_mem](#t-entry_pair_mem) より対 $`(R_{0,k_1}, R_{1,k_1})`$ は $`R`$ の要素であり、
$`\mathrm{argOK}`$ の定義（D.argOK）よりその第 1 成分は正である。
したがって $`\neg(R_{0,k_1} = 0 \wedge R_{1,k_1} = 0)`$ であり、(ii) より
$`\neg(M_{0,\lvert R\rvert} = 0 \wedge M_{1,\lvert R\rvert} = 0)`$ でもある。

**(v)** $`\mathrm{idx}_1(M, \lvert M\rvert - 1) = \mathrm{idx}_1(M, \lvert R\rvert) = \mathrm{idx}_1(R, k_1) = i`$。
(i) と [T.idx1_cons_last](#t-idx1_cons_last) による。

**第 1 段：根 $`0`$ は $`M`$ の最終列の親ではない、すなわち $`\neg\bigl(0 \to^M_i \lvert R\rvert\bigr)`$。**
$`0 \to^M_i \lvert R\rvert`$ を仮定して矛盾を導く。$`i`$ で場合分けする。

**(a) $`i = 0`$ のとき。** $`\to^M_i`$ の定義（D.nextR）より $`0 \to^M_0 \lvert R\rvert`$ である。
その定義（D.nextrel0）の条件 (5) を $`j := j_0 + 1`$ に適用する。前件の第 1 連言子
$`0 \lt j_0 + 1`$ は自然数の後者が正であることによる。第 2 連言子は、(iii) の
$`j_0 \lt k_1 = \lvert R\rvert - 1`$ から $`j_0 + 1 \lt \lvert R\rvert`$ として得られる。よって
$`M_{0,\lvert R\rvert} \le M_{0,j_0+1}`$ を得る。
(ii) と [T.entry_cons](#t-entry_cons) によりこれは $`R_{0,k_1} \le R_{0,j_0}`$ である。
一方 (iii) の $`j_0 \to^R_0 k_1`$ の条件 (4) は $`R_{0,j_0} \lt R_{0,k_1}`$ であり、矛盾する。

**(b) $`i \ne 0`$ のとき。** $`\to^M_i`$ の定義（D.nextR）より $`0 \to^M_1 \lvert R\rvert`$ である。
その定義（D.nextrel1）の条件 (6) を $`j := j_0 + 1`$ に適用する。前件の第 1 連言子
$`0 \lt j_0 + 1`$ は自然数の後者が正であることによる。第 2 連言子 $`j_0 + 1 \le^M_0 \lvert R\rvert`$ は、
(iii) の $`j_0 \to^R_1 k_1`$ の条件 (5) が $`j_0 \le^R_0 k_1`$ であることと
[T.le0_cons_last](#t-le0_cons_last) から従う。よって
$`M_{1,\lvert R\rvert} \le M_{1,j_0+1}`$、すなわち (ii) と [T.entry_cons](#t-entry_cons) より
$`R_{1,k_1} \le R_{1,j_0}`$ を得る。
一方 $`j_0 \to^R_1 k_1`$ の条件 (4) は $`R_{1,j_0} \lt R_{1,k_1}`$ であり、矛盾する。

**第 2 段：$`y \to^M_i \lvert R\rvert`$ ならば $`y = j_0 + 1`$。**
$`y = 0`$ は第 1 段により排除される。よって $`y = y' + 1`$ と書ける。
[T.nextR_cons_last](#t-nextR_cons_last) より $`y' \to^R_i k_1`$ である。
仮定 $`\mathrm{hasParent}(R, i, k_1)`$ の一意性（$`\mathrm{hasParent}`$ の定義 D.hasParent）と
(iii) の $`j_0 \to^R_i k_1`$ から $`y' = j_0`$、すなわち $`y = j_0 + 1`$。

**第 3 段：$`M`$ の側の親。**
(iii) と [T.nextR_cons_last](#t-nextR_cons_last) より $`j_0 + 1 \to^M_i \lvert R\rvert`$ であり、
第 2 段よりそのような添字は $`j_0 + 1`$ に限る。よって
$`\mathrm{hasParent}(M, i, \lvert R\rvert)`$ が成り立ち、(i)(v) と合わせて
$`\mathrm{hasParent}\bigl(M, \mathrm{idx}_1(M,\lvert M\rvert-1), \lvert M\rvert-1\bigr)`$ である。
また $`\mathrm{par}^M_i(\lvert R\rvert)`$ は [T.parent_nextR](Decrease.md#t-parent_nextR) より
$`\to^M_i`$ で $`\lvert R\rvert`$ に至る添字であるから、第 2 段より
$`\mathrm{par}^M_i(\lvert R\rvert) = j_0 + 1`$。

**第 4 段：両辺を展開して比べる。**
(i)(iv) と第 3 段により [T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) が $`M`$ に適用でき、
(iii)(iv) と仮定により $`R`$ にも適用できる。それぞれ

```math
M[n] = (M_0,\dots,M_{j_0}) \mathbin{+\!\!+} B^M_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^M_{n-1},
\qquad
B^M_k = \bigl(\,(M_{0,j} + k\,d,\ M_{1,j})\,\bigr)_{j=j_0+1}^{\lvert R\rvert - 1},
```
```math
R[n] = (R_0,\dots,R_{j_0-1}) \mathbin{+\!\!+} B^R_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^R_{n-1},
\qquad
B^R_k = \bigl(\,(R_{0,j} + k\,d',\ R_{1,j})\,\bigr)_{j=j_0}^{k_1 - 1}
```

である。ここで

```math
d = \begin{cases} M_{0,\lvert R\rvert} - M_{0,j_0+1} & (0 \lt i) \cr 0 & (i = 0) \end{cases},
\qquad
d' = \begin{cases} R_{0,k_1} - R_{0,j_0} & (0 \lt i) \cr 0 & (i = 0) \end{cases}
```

である。3 点を確かめる。

- $`d = d'`$：(ii) より $`M_{0,\lvert R\rvert} = R_{0,k_1}`$、
  [T.entry_cons](#t-entry_cons) より $`M_{0,j_0+1} = R_{0,j_0}`$ である。
- 前置部分：$`M = (0,v) :: R`$ であるから
  $`(M_0,\dots,M_{j_0}) = (0,v) :: (R_0,\dots,R_{j_0-1})`$。
- ブロック：$`B^M_k`$ の添字 $`j`$ は $`j_0+1`$ から $`\lvert R\rvert - 1`$ まで、
  $`B^R_k`$ の添字 $`j`$ は $`j_0`$ から $`k_1 - 1 = \lvert R\rvert - 2`$ までを走り、
  どちらも長さは $`\lvert R\rvert - 1 - j_0`$ である。$`j = j' + 1`$ と置き換えれば
  [T.entry_cons](#t-entry_cons) より $`M_{0,j'+1} = R_{0,j'}`$、$`M_{1,j'+1} = R_{1,j'}`$
  であるから、第 $`j'`$ 成分どうしが一致する。よって $`B^M_k = B^R_k`$。

以上より

```math
M[n] = (0,v) :: \Bigl((R_0,\dots,R_{j_0-1}) \mathbin{+\!\!+} B^R_0 \mathbin{+\!\!+} \cdots
  \mathbin{+\!\!+} B^R_{n-1}\Bigr) = (0,v) :: R[n] . \qquad \blacksquare
```

<a id="t-oper_cons_succ"></a>
## 定理: 後続子の主要ステップ (T.oper_cons_succ)

### 定理

$`v, n \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ とし、$`k_1 := \lvert R\rvert - 1`$ とおく。
$`\mathrm{argOK}(R)`$、$`R \ne ()`$、$`R_{1,k_1} = 0`$、$`\neg\,\mathrm{hasParent}(R, 0, k_1)`$
を仮定すると

```math
\bigl((0,v) :: R\bigr)[n] = \bigl((0,v) :: \mathrm{dropLast}\,R\bigr)^{\frown n} .
```

ここで列 $`Q`$ に対し $`Q^{\frown n}`$ を $`Q`$ を $`n`$ 個連結した列とする。すなわち

```math
Q^{\frown 0} := (), \qquad Q^{\frown (n+1)} := Q^{\frown n} \mathbin{+\!\!+} Q .
```

### 証明

$`M := (0,v) :: R`$ と書く。$`R \ne ()`$ より $`0 \lt \lvert R\rvert`$ であり、
$`\lvert M\rvert - 1 = \lvert R\rvert`$ である。
[T.entry_cons_last](#t-entry_cons_last) より $`M_{0,\lvert R\rvert} = R_{0,k_1}`$ である。

**第 1 段：$`\mathrm{idx}_1(M, \lvert M\rvert - 1) = 0`$。**
[T.idx1_cons_last](#t-idx1_cons_last) より
$`\mathrm{idx}_1(M, \lvert R\rvert) = \mathrm{idx}_1(R, k_1)`$ であり、
仮定 $`R_{1,k_1} = 0`$ と $`\mathrm{idx}_1`$ の定義（D.idx1）の第 2 の場合により
$`\mathrm{idx}_1(R, k_1) = 0`$ である。

**第 2 段：$`\forall k \lt k_1,\ R_{0,k_1} \le R_{0,k}`$。**
$`k \lt k_1`$ かつ $`R_{0,k} \lt R_{0,k_1}`$ なる $`k`$ が存在したとすると、
$`k_1 \lt \lvert R\rvert`$ であるから [T.hasParent_zero_iff](#t-hasParent_zero_iff) より
$`\mathrm{hasParent}(R, 0, k_1)`$ となり、仮定に反する。

**第 3 段：$`0 \to^M_0 \lvert R\rvert`$。**
$`\to^M_0`$ の定義（D.nextrel0）の 5 条件を確かめる。

- (1) $`0 \lt \lvert M\rvert`$：$`\lvert M\rvert = \lvert R\rvert + 1 \ge 1`$。
- (2) $`\lvert R\rvert \lt \lvert M\rvert`$：同上。
- (3) $`0 \lt \lvert R\rvert`$：$`R \ne ()`$ による。
- (4) $`M_{0,0} \lt M_{0,\lvert R\rvert}`$：$`M`$ の第 $`0`$ 列は $`(0,v)`$ であるから
  $`M_{0,0} = 0`$ である。一方 $`k_1 \lt \lvert R\rvert`$ と
  [T.entry_pair_mem](#t-entry_pair_mem) より対 $`(R_{0,k_1}, R_{1,k_1})`$ は $`R`$ の要素だから、
  $`\mathrm{argOK}`$ の定義（D.argOK）より $`M_{0,\lvert R\rvert} = R_{0,k_1} \gt 0`$ である。
- (5) $`\forall l,\ (0 \lt l \wedge l \lt \lvert R\rvert) \to M_{0,\lvert R\rvert} \le M_{0,l}`$：
  $`l = l' + 1`$ と書けて $`l' \lt k_1`$ である。[T.entry_cons](#t-entry_cons) より
  $`M_{0,l'+1} = R_{0,l'}`$ であり、第 2 段が $`R_{0,k_1} \le R_{0,l'}`$ を与える。

**第 4 段：$`y \to^M_0 \lvert R\rvert`$ ならば $`y = 0`$。**
$`y \ne 0`$ とすると $`y = y' + 1`$ と書け、[T.nextR_cons_last](#t-nextR_cons_last) より
$`y' \to^R_0 k_1`$ である。その定義（D.nextrel0）の条件 (3) より $`y' \lt k_1`$、
条件 (4) より $`R_{0,y'} \lt R_{0,k_1}`$ である。ところが第 2 段は
$`R_{0,k_1} \le R_{0,y'}`$ を与えるから矛盾である。

**第 5 段：展開の適用。**
第 3 段と第 4 段より $`\mathrm{hasParent}(M, 0, \lvert R\rvert)`$ が成り立ち、
第 1 段と合わせて
$`\mathrm{hasParent}\bigl(M, \mathrm{idx}_1(M, \lvert M\rvert-1), \lvert M\rvert-1\bigr)`$ である。
また [T.parent_nextR](Decrease.md#t-parent_nextR) と第 4 段より
$`\mathrm{par}^M_0(\lvert R\rvert) = 0`$ である。
$`\lvert M\rvert - 1 = \lvert R\rvert \ne 0`$ であり、
$`M_{0,\lvert R\rvert} = R_{0,k_1} \gt 0`$ より
$`\neg(M_{0,\lvert M\rvert-1} = 0 \wedge M_{1,\lvert M\rvert-1} = 0)`$ である。
よって [T.oper_root_tiling](#t-oper_root_tiling) が適用できる。第 1 段により
$`\mathrm{idx}_1(M, \lvert M\rvert-1) = 0`$ であるから、そこに現れる $`e`$ は
$`0 \lt \mathrm{idx}_1(M,\lvert M\rvert-1)`$ が偽であることにより $`e = 0`$ であり、
各ブロックは $`(\mathrm{dropLast}\,M)^{+k\cdot 0} = \mathrm{dropLast}\,M`$ である。したがって

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
$`\mathrm{argOK}(R)`$、$`\mathrm{domT}(R, m)`$、$`v \le m`$ ならば

```math
\bigl((0,v) :: R\bigr)[n] = \mathrm{tow}_v(R,n) .
```

### 証明

$`M := (0,v) :: R`$、$`k_1 := \lvert R\rvert - 1`$、$`x := R_{0,k_1}`$ と書く。

まず $`R \ne ()`$ である。実際 $`R = ()`$ とすると
[T.not_domT_nil](#t-not_domT_nil) が $`\mathrm{domT}(R,m)`$ に反する。
したがって $`0 \lt \lvert R\rvert`$ であり $`\lvert M\rvert - 1 = \lvert R\rvert`$ である。
[T.entry_cons_last](#t-entry_cons_last) より
$`M_{0,\lvert R\rvert} = R_{0,k_1} = x`$、$`M_{1,\lvert R\rvert} = R_{1,k_1}`$ である。
$`\mathrm{domT}`$ の定義（D.domT）の第 1 連言子より $`R_{1,k_1} = m + 1`$、
第 2 連言子より $`\neg\,\mathrm{hasParent}(R, 1, k_1)`$ である。
また $`k_1 \lt \lvert R\rvert`$ と [T.entry_pair_mem](#t-entry_pair_mem)、
$`\mathrm{argOK}`$ の定義（D.argOK）より $`0 \lt x`$ である。

**第 1 段：$`\mathrm{idx}_1(M, \lvert M\rvert - 1) = 1`$。**
[T.idx1_cons_last](#t-idx1_cons_last) より
$`\mathrm{idx}_1(M, \lvert R\rvert) = \mathrm{idx}_1(R, k_1)`$ であり、
$`R_{1,k_1} = m + 1 \gt 0`$ と $`\mathrm{idx}_1`$ の定義（D.idx1）の第 1 の場合により
その値は $`1`$ である。

**第 2 段：$`y \to^M_1 \lvert R\rvert`$ ならば $`y = 0`$。**
$`y \ne 0`$ とすると $`y = y' + 1`$ と書け、[T.nextR_cons_last](#t-nextR_cons_last) より
$`y' \to^R_1 k_1`$ である。$`\to^R_1`$ の定義（D.nextrel1）の条件 (3)(4)(5) はそれぞれ
$`y' \lt k_1`$、$`R_{1,y'} \lt R_{1,k_1}`$、$`y' \le^R_0 k_1`$ であり、これは
$`\mathrm{r1cand}(R, k_1, y')`$ にほかならない。$`k_1 \lt \lvert R\rvert`$ であるから
[T.hasParent_one_iff](#t-hasParent_one_iff) より $`\mathrm{hasParent}(R, 1, k_1)`$ となり、
上で見た $`\neg\,\mathrm{hasParent}(R,1,k_1)`$ に矛盾する。

**第 3 段：$`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$ と $`\mathrm{par}^M_1(\lvert R\rvert) = 0`$。**
$`v \le m \lt m + 1 = R_{1,k_1}`$ であるから、
[T.hasParent_cons_one](#t-hasParent_cons_one) を第 2 選言で適用して
$`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$ を得る。
[T.parent_nextR](Decrease.md#t-parent_nextR) より
$`\mathrm{par}^M_1(\lvert R\rvert) \to^M_1 \lvert R\rvert`$ であるから、第 2 段より
$`\mathrm{par}^M_1(\lvert R\rvert) = 0`$ である。

**第 4 段：敷き詰めの形。**
$`\lvert M\rvert - 1 = \lvert R\rvert \ne 0`$ であり、$`M_{0,\lvert R\rvert} = x \gt 0`$ より
$`\neg(M_{0,\lvert M\rvert-1} = 0 \wedge M_{1,\lvert M\rvert-1} = 0)`$ である。
第 1 段・第 3 段と合わせて [T.oper_root_tiling](#t-oper_root_tiling) が適用できる。
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

- **帰納段** $`n \to n+1`$：帰納法の仮定は $`\Phi(n)`$ である。
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
  $`\mathrm{graft}`$ の定義（D.graft）より

```math
\mathrm{tow}_v(R,n+1) = (0,v) :: \mathrm{graft}\bigl(R, \mathrm{tow}_v(R,n)\bigr)
  = (0,v) :: \Bigl(\mathrm{dropLast}\,R \mathbin{+\!\!+} \bigl(\mathrm{tow}_v(R,n)\bigr)^{+R_{0,\lvert R\rvert-1}}\Bigr)
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
[T.not_domT_nil](#t-not_domT_nil) より $`R \ne ()`$ であり、
$`0 \lt \lvert R\rvert`$、$`\lvert M\rvert - 1 = \lvert R\rvert`$ である。
[T.entry_cons_last](#t-entry_cons_last) より $`M_{1,\lvert R\rvert} = R_{1,k_1}`$ である。

$`\mathrm{domT}`$ の定義（D.domT）の 2 つの連言子を示す。

**第 1 連言子 $`M_{1,\lvert M\rvert - 1} = m + 1`$。**
$`M_{1,\lvert M\rvert-1} = M_{1,\lvert R\rvert} = R_{1,k_1}`$ であり、
仮定 $`\mathrm{domT}(R,m)`$ の第 1 連言子より $`R_{1,k_1} = m + 1`$ である。

**第 2 連言子 $`\neg\,\mathrm{hasParent}(M, 1, \lvert M\rvert - 1)`$。**
$`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$ を仮定して矛盾を導く。
[T.cons_len_lt](#t-cons_len_lt) より $`\lvert R\rvert \lt \lvert M\rvert`$ であるから
[T.hasParent_one_iff](#t-hasParent_one_iff) が使えて、

```math
j_0 \lt \lvert R\rvert, \qquad j_0 \le^M_0 \lvert R\rvert, \qquad M_{1,j_0} \lt M_{1,\lvert R\rvert} = m+1
```

をみたす $`j_0`$ が取れる。$`j_0`$ で場合分けする。

- **$`j_0 = 0`$ のとき。** $`M`$ の第 $`0`$ 列は $`(0,v)`$ であるから $`M_{1,0} = v`$ であり、
  $`v \lt m + 1`$ すなわち $`v \le m`$ となる。これは仮定 $`m \lt v`$ に矛盾する。

- **$`j_0 = j' + 1`$ のとき。** [T.entry_cons](#t-entry_cons) より
  $`M_{1,j'+1} = R_{1,j'}`$ であるから $`R_{1,j'} \lt m + 1 = R_{1,k_1}`$ である。
  また $`j' + 1 \lt \lvert R\rvert`$ より $`j' \lt \lvert R\rvert - 1 = k_1`$ であり、
  $`j' + 1 \le^M_0 \lvert R\rvert`$ と [T.le0_cons_last](#t-le0_cons_last) より
  $`j' \le^R_0 k_1`$ である。
  これら 3 つは $`\mathrm{r1cand}(R, k_1, j')`$ にほかならないから、
  $`k_1 \lt \lvert R\rvert`$ と [T.hasParent_one_iff](#t-hasParent_one_iff) より
  $`\mathrm{hasParent}(R, 1, k_1)`$ を得る。これは仮定 $`\mathrm{domT}(R,m)`$ の
  第 2 連言子に矛盾する。∎

<a id="t-argOK_oper"></a>
## 定理: 引数ブロックは展開で保たれる (T.argOK_oper)

### 定理

$`\mathrm{argOK}(R)`$ ならば、任意の $`n`$ に対し $`\mathrm{argOK}(R[n])`$。

### 証明

$`\mathrm{argOK}`$ の定義（D.argOK）より、仮定は $`\forall p \in R,\ 0 \lt p_1`$、
すなわち $`\forall p \in R,\ 1 \le p_1`$ である。
[T.oper_mem_ge](#t-oper_mem_ge) を $`c := 1`$、$`B := R`$ として適用すると
$`\forall p \in R[n],\ 1 \le p_1`$、すなわち $`\forall p \in R[n],\ 0 \lt p_1`$ を得る。∎

<a id="t-argOK_graft"></a>
## 定理: 引数ブロックは接ぎ木で保たれる (T.argOK_graft)

### 定理

$`R \ne ()`$ かつ $`\mathrm{argOK}(R)`$ ならば、任意の $`z' \in \mathrm{PairSeq}`$ に対し
$`\mathrm{argOK}\bigl(\mathrm{graft}(R, z')\bigr)`$。

### 証明

仮定は $`\forall p \in R,\ 1 \le p_1`$ と同値である。
[T.graft_mem_ge](#t-graft_mem_ge) を $`c := 1`$、$`B := R`$、$`z := z'`$ として適用すると
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

任意の $`v \in \mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ に対し $`\mathrm{based}\bigl((0,v) :: R\bigr)`$。

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

$`Q \in W_u`$ かつ $`\forall p \in Q,\ Q_{0,0} \le p_1`$ ならば、任意の $`n \in \mathbb{N}`$ に対し
$`Q^{\frown n} \in W_u`$。

### 証明

$`n`$ に関する帰納法。帰納法の述語は

```math
\Phi(n) :\equiv Q^{\frown n} \in W_u .
```

- **基底段** $`n = 0`$：$`Q^{\frown 0} = ()`$ であり、
  [T.W_nil](#t-W_nil) より $`() \in W_u`$ である。

- **帰納段** $`n \to n+1`$：帰納法の仮定は $`\Phi(n)`$、すなわち $`Q^{\frown n} \in W_u`$ である。
  $`Q^{\frown(n+1)} = Q^{\frown n} \mathbin{+\!\!+} Q`$ であるから、
  [T.W_add](#t-W_add) を $`A := Q^{\frown n}`$、$`B := Q`$ として適用すればよい。
  その仮定 $`\mathrm{rsum}(Q^{\frown n}, Q)`$、すなわち

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
$`M \in A_u(W^{*})`$ ならば $`M \in W^{*}`$。

### 証明

定理の主張の $`M`$ を、以下 $`R`$ と書く。$`W^{*}`$ の定義（D.Wstar）より、示すべきことは

```math
\mathrm{argOK}(R) \ \longrightarrow\ \forall v \in \mathbb{N},\ (0,v) :: R \in W_v
```

である。そこで $`\mathrm{argOK}(R)`$ と $`v`$ を仮定する。
$`N := (0,v) :: R`$、$`k_1 := \lvert R\rvert - 1`$ と書く。

**$`R = ()`$ のとき。** $`N = (0,v) :: ()`$ であり、
[T.Om_mem_W](#t-Om_mem_W) より $`N \in W_v`$ である。

以下 $`R \ne ()`$ とする。$`0 \lt \lvert R\rvert`$、$`\lvert N\rvert - 1 = \lvert R\rvert`$ であり、
[T.entry_cons_last](#t-entry_cons_last) より
$`N_{1,\lvert N\rvert-1} = N_{1,\lvert R\rvert} = R_{1,k_1}`$ である。
次の 2 つを用意する。

- **(D1)** $`\mathrm{hasParent}(N, 1, \lvert R\rvert)`$ ならば $`\mathrm{natDom}(N)`$。
  [T.natDom_iff](#t-natDom_iff) の右辺の第 2 選言が
  $`\mathrm{hasParent}(N, 1, \lvert N\rvert - 1)`$ であり、
  $`\lvert N\rvert - 1 = \lvert R\rvert`$ だからである。
- **(D2)** $`R_{1,k_1} = 0`$ ならば $`\mathrm{natDom}(N)`$。
  [T.natDom_iff](#t-natDom_iff) の右辺の第 1 選言が $`N_{1,\lvert N\rvert-1} = 0`$ であり、
  これは $`R_{1,k_1} = 0`$ に等しいからである。

仮定 $`R \in A_u(W^{*})`$ について、$`A_u`$ の定義（D.Aop）の 3 分岐で場合分けする。

**分岐 (1)：$`\lvert R\rvert \le 1`$ かつ $`R_{1,0} = 0`$ のとき。**
$`R \ne ()`$ より $`\lvert R\rvert = 1`$、したがって $`k_1 = 0`$ であり $`R_{1,k_1} = 0`$ である。
また $`\neg\,\mathrm{hasParent}(R, 0, k_1)`$ である。実際
$`j_0 \to^R_0 0`$ なる $`j_0`$ があれば
[T.nextR_index_lt](Decrease.md#t-nextR_index_lt) より $`j_0 \lt 0`$ となり、
自然数についてこれは不可能である。さらに $`\lvert R\rvert = 1`$ より
$`\mathrm{dropLast}\,R = ()`$ である。

[T.A1_intro](#t-A1_intro) により $`N \in A_v(W_v)`$ を示せばよい。
$`A_v`$ の定義（D.Aop）の分岐 (2) を取る。
$`\mathrm{natDom}(N)`$ は (D2) による。$`n \ge 1`$ に対する $`N[n] \in W_v`$ は、
[T.oper_cons_succ](#t-oper_cons_succ) より

```math
N[n] = \bigl((0,v) :: \mathrm{dropLast}\,R\bigr)^{\frown n} = \bigl((0,v) :: ()\bigr)^{\frown n}
```

であり、[T.Om_mem_W](#t-Om_mem_W) より $`(0,v) :: () \in W_v`$、
[T.rsum_self_cons](#t-rsum_self_cons) より
$`\forall p \in (0,v) :: (),\ \bigl((0,v) :: ()\bigr)_{0,0} \le p_1`$ であるから、
[T.W_flatMap_copies](#t-W_flatMap_copies) が $`N[n] \in W_v`$ を与える。

**分岐 (2)：$`\mathrm{natDom}(R)`$ かつ $`\forall n \ge 1,\ R[n] \in W^{*}`$ のとき。**
$`\mathrm{hasParent}\bigl(R, \mathrm{idx}_1(R,k_1), k_1\bigr)`$ が成り立つかどうかで場合分けする。

**(2a) $`\mathrm{hasParent}\bigl(R, \mathrm{idx}_1(R,k_1), k_1\bigr)`$ のとき。**
まず $`\mathrm{natDom}(N)`$ を示す。$`R_{1,k_1} = 0`$ ならば (D2) による。
$`R_{1,k_1} \ne 0`$ ならば、$`\mathrm{idx}_1`$ の定義（D.idx1）の第 1 の場合より
$`\mathrm{idx}_1(R,k_1) = 1`$ であるから、いまの仮定は $`\mathrm{hasParent}(R,1,k_1)`$ である。
[T.hasParent_cons_one](#t-hasParent_cons_one) を第 1 選言で適用して
$`\mathrm{hasParent}(N, 1, \lvert R\rvert)`$ を得、(D1) を使う。

[T.A1_intro](#t-A1_intro) により $`N \in A_v(W_v)`$ を、その分岐 (2) で示す。
$`n \ge 1`$ とすると [T.oper_cons_nat](#t-oper_cons_nat) より
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

[T.A1_intro](#t-A1_intro) により $`N \in A_v(W_v)`$ を、その分岐 (2) で示す。
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
  [T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero)、
  成り立たないときは
  [T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) により
  $`R[1] = \mathrm{Pred}\,R`$ である。さらに $`\neg(\lvert R\rvert \le 1)`$ であるから
  $`\mathrm{Pred}`$ の定義（D.Pred）の第 2 の場合が選ばれ
  $`R[1] = \mathrm{dropLast}\,R`$ である。
  分岐 (2) の仮定を $`n := 1`$ に適用して $`\mathrm{dropLast}\,R \in W^{*}`$ を得る。
  [T.argOK_dropLast](#t-argOK_dropLast) より
  $`\mathrm{argOK}(\mathrm{dropLast}\,R)`$ であるから、
  $`W^{*}`$ の定義（D.Wstar）を $`v`$ に適用して
  $`(0,v) :: \mathrm{dropLast}\,R \in W_v`$ を得る。

- **$`\lvert R\rvert = 1`$ のとき。** $`\mathrm{dropLast}\,R = ()`$ であるから
  $`(0,v) :: \mathrm{dropLast}\,R = (0,v) :: ()`$ であり、
  [T.Om_mem_W](#t-Om_mem_W) より $`W_v`$ に属する。

**分岐 (3)：$`m \lt u`$、$`\mathrm{domT}(R,m)`$、かつ**
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(R,z) \in W^{*}`$ **のとき。**
$`v \le m`$ か否かで場合分けする。

**(3a) $`v \le m`$ のとき。**
まず $`\forall k \in \mathbb{N},\ \mathrm{tow}_v(R,k) \in W_v`$ を $`k`$ に関する帰納法で示す。
帰納法の述語は $`\Psi(k) :\equiv \mathrm{tow}_v(R,k) \in W_v`$ である。

- **基底段** $`k = 0`$：$`\mathrm{tow}`$ の定義（D.tow）の第 1 式より
  $`\mathrm{tow}_v(R,0) = ()`$ であり、[T.W_nil](#t-W_nil) より $`() \in W_v`$。

- **帰納段** $`k \to k+1`$：帰納法の仮定は $`\Psi(k)`$ である。
  まず $`\mathrm{based}(\mathrm{tow}_v(R,k))`$ を示す。$`k = 0`$ のときは
  $`\mathrm{tow}_v(R,0) = ()`$ であり [T.based_nil](#t-based_nil) による。
  $`k = k' + 1`$ のときは $`\mathrm{tow}`$ の定義（D.tow）の第 2 式より
  $`\mathrm{tow}_v(R,k) = (0,v) :: \mathrm{graft}(R, \mathrm{tow}_v(R,k'))`$ であり、
  [T.based_cons](#t-based_cons) による。
  次に $`v \le m`$ と [T.W_mono](#t-W_mono) を $`\Psi(k)`$ に適用して
  $`\mathrm{tow}_v(R,k) \in W_m`$ を得る。分岐 (3) の仮定を
  $`z := \mathrm{tow}_v(R,k)`$ に適用すると
  $`\mathrm{graft}(R, \mathrm{tow}_v(R,k)) \in W^{*}`$ である。
  $`R \ne ()`$（[T.not_domT_nil](#t-not_domT_nil) と $`\mathrm{domT}(R,m)`$ による）と
  [T.argOK_graft](#t-argOK_graft) より
  $`\mathrm{argOK}\bigl(\mathrm{graft}(R,\mathrm{tow}_v(R,k))\bigr)`$ であるから、
  $`W^{*}`$ の定義（D.Wstar）を $`v`$ に適用して

```math
\mathrm{tow}_v(R,k+1) = (0,v) :: \mathrm{graft}\bigl(R, \mathrm{tow}_v(R,k)\bigr) \in W_v
```

  を得る。すなわち $`\Psi(k+1)`$。

[T.A1_intro](#t-A1_intro) により $`N \in A_v(W_v)`$ を、その分岐 (2) で示す。
$`\mathrm{natDom}(N)`$ は次のように得る。$`\mathrm{domT}(R,m)`$ の第 1 連言子より
$`R_{1,k_1} = m + 1`$ であり、$`v \le m \lt m+1`$ であるから
[T.hasParent_cons_one](#t-hasParent_cons_one) を第 2 選言で適用して
$`\mathrm{hasParent}(N,1,\lvert R\rvert)`$ を得、(D1) を使う。
$`n \ge 1`$ に対しては [T.oper_cons_tower](#t-oper_cons_tower) より
$`N[n] = \mathrm{tow}_v(R,n)`$ であり、いま示した $`\Psi(n)`$ よりこれは $`W_v`$ に属する。

**(3b) $`\neg(v \le m)`$ すなわち $`m \lt v`$ のとき。**
[T.A1_intro](#t-A1_intro) により $`N \in A_v(W_v)`$ を、その分岐 (3) で示す。
分岐 (3) の 3 つの成分を確かめる。

- $`m \lt v`$：いまの場合分けの仮定である。
- $`\mathrm{domT}(N, m)`$：[T.domT_cons_of_lt](#t-domT_cons_of_lt) による。
- $`z \in W_m`$ かつ $`\mathrm{based}(z)`$ ならば $`\mathrm{graft}(N,z) \in W_v`$：
  $`R \ne ()`$ であるから [T.graft_cons](#t-graft_cons) より
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

### 証明

平行移動 $`(\cdot)^{+x}`$ は各対の第 1 成分に $`x`$ を足す操作であるから、
先頭要素と残りに分けて

```math
\Bigl((0,y) :: R^{-x}\Bigr)^{+x} = (0 + x,\ y) :: \bigl(R^{-x}\bigr)^{+x}
```

である。$`0 + x = x`$ であり、仮定 $`\forall r \in R,\ x \le r_1`$ のもとで
[T.map_sub_add](#t-map_sub_add) が $`\bigl(R^{-x}\bigr)^{+x} = R`$ を与える。∎

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

**帰納段** $`N \to N+1`$：帰納法の仮定は $`\Phi(N)`$ である。
$`\lvert M\rvert \le N+1`$ なる $`M`$ と $`\mathrm{(Acl)}`$ をみたす $`X`$ を取る。

$`M = ()`$ のときは、基底段で見たとおり $`() \in A_0(X)`$ であるから、
$`\mathrm{(Acl)}`$ を $`u := 0`$、$`M' := ()`$ に適用して $`M \in X`$ を得る。
以下 $`M \ne ()`$ とする。
[T.split_lastMin](#t-split_lastMin) により

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

を得る。[T.W_shift](#t-W_shift) を $`d := x`$ として適用すると
$`\bigl((0,y) :: R^{-x}\bigr)^{+x} \in W_y`$ であり、
$`\forall r \in R,\ x \le r_1`$ のもとで [T.tree_shift](#t-tree_shift) より
この列は $`(x,y) :: R = P = M`$ に等しい。すなわち $`M \in W_y`$ である。

最後に [T.A2'](#t-A2') を $`u := y`$、$`Y := X`$ として適用する。その仮定
「$`\forall M',\ M' \in A_y(X) \to M' \in X`$」は $`\mathrm{(Acl)}`$ を $`u := y`$ に
特殊化したものである。よって $`W_y \subseteq X`$ であり $`M \in X`$。

**(b) $`A \ne ()`$ のとき。** $`0 \lt \lvert A\rvert`$ かつ $`0 \lt \lvert P\rvert`$ であり、
$`\lvert A\rvert + \lvert P\rvert \le N+1`$ であるから
$`\lvert A\rvert \le N`$ かつ $`\lvert P\rvert \le N`$ である。

帰納法の仮定 $`\Phi(N)`$ を $`M := A`$、$`X := X`$ に適用して $`A \in X`$ を得る。
次に [T.XA_closed](#t-XA_closed) を、$`\mathrm{(Acl)}`$ を $`u`$ に特殊化したものと
$`A \in X`$ に適用すると、任意の $`u`$ について

```math
\forall M',\ M' \in A_u\bigl(X^{(A)}\bigr) \to M' \in X^{(A)}
```

が成り立つ。すなわち $`X^{(A)}`$ も $`\mathrm{(Acl)}`$ をみたす。
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
  [T.W_nil](#t-W_nil) より $`() \in W_u`$。

**帰納段** $`N \to N+1`$：帰納法の仮定は $`\Phi(N)`$ である。
$`\lvert M\rvert \le N+1`$ なる $`M`$、$`u`$、および
$`\forall p \in M,\ p_2 \le u`$ を取る。

$`M = ()`$ のときは [T.W_nil](#t-W_nil) による。以下 $`M \ne ()`$ とする。
[T.split_lastMin](#t-split_lastMin) により

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
$`(0,y) :: R^{-x} \in W_y`$ を得る。[T.W_shift](#t-W_shift) を $`d := x`$ として適用し、
$`\forall r \in R,\ x \le r_1`$ のもとで [T.tree_shift](#t-tree_shift) を使うと

```math
(x,y) :: R = \Bigl((0,y) :: R^{-x}\Bigr)^{+x} \in W_y
```

である。$`(x,y) \in A \mathbin{+\!\!+} P = M`$ であるから仮定より $`y \le u`$ であり、
[T.W_mono](#t-W_mono) より $`(x,y) :: R \in W_u`$、すなわち $`P \in W_u`$ である。

$`A`$ で場合分けする。

- **$`A = ()`$ のとき。** $`M = P \in W_u`$ である。

- **$`A \ne ()`$ のとき。** $`0 \lt \lvert A\rvert`$ かつ $`0 \lt \lvert P\rvert`$ であるから
  $`\lvert A\rvert \le N`$ である。$`A`$ の要素は $`M`$ の要素であるから
  $`\forall p \in A,\ p_2 \le u`$ であり、帰納法の仮定 $`\Phi(N)`$ を $`A`$ に適用して
  $`A \in W_u`$ を得る。$`\mathrm{rsum}(A,P)`$ と合わせて
  [T.W_add](#t-W_add) より $`M = A \mathbin{+\!\!+} P \in W_u`$。∎

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

任意の $`S \in \mathrm{PairSeq}`$ と $`p \in S`$ に対し $`p_2 \le \mathrm{maxr}_1(S)`$（[D.maxr1](Column.md#d-maxr1)）。

### 証明

$`S`$ の構造に関する帰納法。帰納法の述語は

```math
\Phi(S) :\equiv \forall p \in S,\ p_2 \le \mathrm{maxr}_1(S) .
```

- **基底段** $`S = ()`$：空列は要素をもたないから前件が偽であり、$`\Phi(())`$ が成り立つ。

- **帰納段** $`S = q :: S'`$：帰納法の仮定は $`\Phi(S')`$ である。
  [T.maxr1_cons](Column.md#t-maxr1_cons) より
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

任意の $`M \in \mathrm{PairSeq}`$ に対し、$`M \in \mathrm{ST\_PS}`$ ならば
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
&\text{(cof)}\quad \forall M, N \in \mathrm{PairSeq},\
  M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,N \prec \mathrm{tr}\,M \cr
&\phantom{\text{(cof)}\quad}
  \longrightarrow\ \exists n,\ 1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n]), \cr
&\text{(mem)}\quad \forall M \in \mathrm{PairSeq},\
  M \in \mathrm{ST\_PS} \to \exists u \in \mathbb{N},\ M \in W_u .
\end{aligned}
```

このとき関係 $`R_{\mathrm{st}}`$ は整礎である。

### 証明

$`R_{\mathrm{st}}`$ の定義（D.Rst）より

```math
a \mathbin{R_{\mathrm{st}}} b :\iff a \in \mathrm{ST\_PS} \wedge b \in \mathrm{ST\_PS}
  \wedge \mathrm{tr}\,a \prec \mathrm{tr}\,b
```

である。整礎性は $`\forall M,\ \mathrm{Acc}(R_{\mathrm{st}},M)`$ と同値であるから、
$`M`$ を任意に取り $`\mathrm{Acc}(R_{\mathrm{st}},M)`$ を示す。
$`M \in \mathrm{ST\_PS}`$ か否かで場合分けする。

- **$`M \in \mathrm{ST\_PS}`$ のとき。** 仮定 (mem) により $`M \in W_u`$ なる $`u`$ を取る。
  [T.acc_of_W](#t-acc_of_W) を仮定 (cof) と $`u`$、$`M`$ に適用して
  $`\mathrm{Acc}(R_{\mathrm{st}},M)`$ を得る。

- **$`M \notin \mathrm{ST\_PS}`$ のとき。** $`\mathrm{Acc}`$ の生成規則
  $`\bigl(\forall y,\ y \mathbin{R} a \to \mathrm{Acc}(R,y)\bigr) \to \mathrm{Acc}(R,a)`$ により、
  $`y \mathbin{R_{\mathrm{st}}} M`$ なるすべての $`y`$ について
  $`\mathrm{Acc}(R_{\mathrm{st}},y)`$ を示せばよい。ところが
  $`y \mathbin{R_{\mathrm{st}}} M`$ の第 2 連言子は $`M \in \mathrm{ST\_PS}`$ であり、
  いまの場合分けの仮定に矛盾する。よって前件をみたす $`y`$ は存在せず、
  $`\mathrm{Acc}(R_{\mathrm{st}},M)`$ が成り立つ。∎

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
