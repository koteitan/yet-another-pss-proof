[← README](README-ja.md) | [English](Wset-3.md) | [Japanese](Wset-3-ja.md) | Wset [1](Wset-ja.md) [2](Wset-2-ja.md) **3** [4](Wset-4-ja.md)

<a id="t-XA_closed"></a>
## 定理: $`A_u\bigl(X^{(A)}\bigr) \subseteq X^{(A)}`$ (T.XA_closed)

### 定理

$`X \subseteq \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）が
$`\forall M,\ M \in A_u(X) \to M \in X`$（[D.Aop](Wset-ja.md#d-Aop)）をみたし、
$`A \in X`$ とする。このとき

```math
\forall M,\ M \in A_u\bigl(X^{(A)}\bigr) \to M \in X^{(A)} .
```

### 証明

$`B \in A_u(X^{(A)})`$（[D.XA](Wset-2-ja.md#d-XA)）とする。$`X^{(A)}`$ の定義（D.XA）より、
$`\mathrm{rsum}(A,B)`$（[D.rsum](Wset-ja.md#d-rsum)）を仮定して
$`A \mathbin{+\!\!+} B \in X`$ を示せばよい。

$`B = ()`$ のときは $`A \mathbin{+\!\!+} () = A \in X`$ である。以下 $`B \ne ()`$、
すなわち $`0 \lt \lvert B\rvert`$ とする。$`\mathrm{rsum}(A,B)`$ の定義（D.rsum）より

```math
(\ast)\qquad \forall p \in B,\ B_{0,0} \le p_1,
\qquad\qquad
(\ast\ast)\qquad \forall p \in A,\ B_{0,0} \le p_1
```

が成り立つ。$`A_u`$ の定義（D.Aop）の 3 分岐で場合分けする。

**分岐 (1)：$`\lvert B\rvert \le 1 \wedge B_{1,0} = 0`$（[D.entry](Pss-ja.md#d-entry)）のとき。**
$`0 \lt \lvert B\rvert`$ と合わせて $`\lvert B\rvert = 1`$ である。$`A`$ が空か否かで分ける。

**$`A = ()`$ のとき。** 仮定より $`B \in A_u(X)`$（分岐 (1) そのもの）であるから
$`B \in X`$ であり、$`A \mathbin{+\!\!+} B = B \in X`$ である。

**$`A \ne ()`$ のとき。** $`0 \lt \lvert A\rvert`$ である。
$`\lvert A \mathbin{+\!\!+} B\rvert = \lvert A\rvert + 1`$ であるから

```math
\lvert A \mathbin{+\!\!+} B\rvert - 1 = \lvert A\rvert + 0 .
```

まず、任意の $`i`$ について
$`\neg\,\mathrm{hasParent}(A \mathbin{+\!\!+} B,\ i,\ \lvert A \mathbin{+\!\!+} B\rvert - 1)`$（[D.hasParent](Pss-ja.md#d-hasParent)）
である。実際これが成り立つとすると、$`0 \lt \lvert B\rvert`$ より
[T.hasParent_append_gen](Wset-2-ja.md#t-hasParent_append_gen) を $`j := 0`$ に適用して
$`\mathrm{hasParent}(B, i, 0)`$ を得る。$`\mathrm{hasParent}`$ の定義（D.hasParent）より
$`j_0 \to^B_i 0`$（[D.nextR](Pss-ja.md#d-nextR)）なる $`j_0`$ が存在するが、
[T.nextR_index_lt](Decrease-ja.md#t-nextR_index_lt) より $`j_0 \lt 0`$ となり矛盾する。

次に $`\mathrm{natDom}(A \mathbin{+\!\!+} B)`$（[D.natDom](Wset-ja.md#d-natDom)）を示す。$`\lvert B\rvert - 1 = 0`$ であるから
$`B_{1,\lvert B\rvert-1} = B_{1,0} = 0`$ であり、[T.natDom_iff](Wset-ja.md#t-natDom_iff) の右辺の
第 1 選言が成り立つので $`\mathrm{natDom}(B)`$ である。
[T.natDom_append](Wset-2-ja.md#t-natDom_append) より $`\mathrm{natDom}(A \mathbin{+\!\!+} B)`$ である。

最後に、任意の $`n \ge 1`$ に対し $`(A \mathbin{+\!\!+} B)[n] = A \in X`$（[D.oper](Pss-ja.md#d-oper)）を示す。
$`2 \le \lvert A \mathbin{+\!\!+} B\rvert`$ であるから $`\lvert A \mathbin{+\!\!+} B\rvert - 1 \ne 0`$ である。
$`J := \lvert A \mathbin{+\!\!+} B\rvert - 1`$ と略記すると、
$`(A \mathbin{+\!\!+} B)_{0,J} = 0 \wedge (A \mathbin{+\!\!+} B)_{1,J} = 0`$ が成り立つなら
[T.oper_eq_pred_of_zero](Decrease-ja.md#t-oper_eq_pred_of_zero) により、成り立たないなら
上で示した親の非存在と
[T.oper_eq_pred_of_noParent](Decrease-ja.md#t-oper_eq_pred_of_noParent) により、
いずれにせよ $`(A \mathbin{+\!\!+} B)[n] = \mathrm{Pred}(A \mathbin{+\!\!+} B)`$（[D.Pred](Pss-ja.md#d-Pred)）である。
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

**$`2 \le \lvert B\rvert`$ のとき。** [T.natDom_append](Wset-2-ja.md#t-natDom_append) より
$`\mathrm{natDom}(A \mathbin{+\!\!+} B)`$ である。$`n \ge 1`$ を取ると
[T.oper_append_gen](Wset-2-ja.md#t-oper_append_gen) より

```math
(A \mathbin{+\!\!+} B)[n] = A \mathbin{+\!\!+} B[n]
```

である。$`B[n] \in X^{(A)}`$ であるから、$`A \mathbin{+\!\!+} B[n] \in X`$ を得るには
$`\mathrm{rsum}(A,\ B[n])`$ を確かめればよい。
[T.oper_head_eq](Wset-2-ja.md#t-oper_head_eq) より $`(B[n])_{0,0} = B_{0,0}`$ である。
$`p \in A \mathbin{+\!\!+} B[n]`$ を取ると、$`p \in A`$ のときは $`(\ast\ast)`$ より
$`B_{0,0} \le p_1`$、$`p \in B[n]`$ のときは $`(\ast)`$ と
[T.oper_mem_ge](Wset-2-ja.md#t-oper_mem_ge)（$`c := B_{0,0}`$）より $`B_{0,0} \le p_1`$ である。
よって $`\mathrm{rsum}(A, B[n])`$ が成り立ち、$`(A \mathbin{+\!\!+} B)[n] \in X`$ である。
すなわち $`A \mathbin{+\!\!+} B`$ は分岐 (2) をみたすから、仮定より $`A \mathbin{+\!\!+} B \in X`$ である。

**$`\neg(2 \le \lvert B\rvert)`$ のとき。** $`\lvert B\rvert \le 1`$ すなわち $`\lvert B\rvert - 1 = 0`$ であるから
[T.oper_eq_self_of_short](Decrease-ja.md#t-oper_eq_self_of_short) より $`B[1] = B`$ である。
分岐 (2) の第 2 連言子を $`n := 1`$ に適用すると $`B[1] \in X^{(A)}`$、すなわち
$`B \in X^{(A)}`$ である。仮定 $`\mathrm{rsum}(A,B)`$ をこれに適用して
$`A \mathbin{+\!\!+} B \in X`$ を得る。

**分岐 (3)、すなわち $`m \lt u`$、$`\mathrm{domT}(B,m)`$（[D.domT](Wset-ja.md#d-domT)）、
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(B,z) \in X^{(A)}`$（[D.W](Wset-ja.md#d-W)、[D.based](Wset-ja.md#d-based)、[D.graft](Wset-ja.md#d-graft)）をみたす $`m`$ があるとき。**
[T.domT_append](Wset-2-ja.md#t-domT_append) より $`\mathrm{domT}(A \mathbin{+\!\!+} B,\ m)`$ である。
$`z \in W_m`$ が $`\mathrm{based}(z)`$ をみたすとする。
[T.graft_append](Wset-2-ja.md#t-graft_append) より

```math
\mathrm{graft}(A \mathbin{+\!\!+} B,\ z) = A \mathbin{+\!\!+} \mathrm{graft}(B,z)
```

である。$`\mathrm{graft}(B,z) \in X^{(A)}`$ であるから、これが $`X`$ に属することを示すには
$`\mathrm{rsum}\bigl(A,\ \mathrm{graft}(B,z)\bigr)`$ を確かめればよい。

- $`\mathrm{graft}(B,z) = ()`$ のとき。D.entry より $`()_{0,0} = 0`$ であるから、
  $`\mathrm{rsum}`$ の定義（D.rsum）の要求は $`\forall p \in A \mathbin{+\!\!+} (),\ 0 \le p_1`$ であり、
  自然数について常に成り立つ。

- $`\mathrm{graft}(B,z) \ne ()`$ のとき。[T.graft_head_eq](Wset-2-ja.md#t-graft_head_eq) より
  $`\bigl(\mathrm{graft}(B,z)\bigr)_{0,0} = B_{0,0}`$ である。
  $`p \in A \mathbin{+\!\!+} \mathrm{graft}(B,z)`$ を取ると、$`p \in A`$ のときは $`(\ast\ast)`$ より
  $`B_{0,0} \le p_1`$、$`p \in \mathrm{graft}(B,z)`$ のときは $`(\ast)`$ と
  [T.graft_mem_ge](Wset-2-ja.md#t-graft_mem_ge)（$`c := B_{0,0}`$）より $`B_{0,0} \le p_1`$ である。

よって $`A \mathbin{+\!\!+} B`$ は同じ $`m`$ で $`A_u`$ の分岐 (3) をみたし、
仮定より $`A \mathbin{+\!\!+} B \in X`$ である。∎

<a id="t-W_add"></a>
## 定理: $`W_u`$ の連結による加法性 (T.W_add)

### 定理

$`A \in W_u`$、$`B \in W_u`$、$`\mathrm{rsum}(A,B)`$ ならば $`A \mathbin{+\!\!+} B \in W_u`$。

### 証明

[T.A1_intro](Wset-ja.md#t-A1_intro) は $`\forall M,\ M \in A_u(W_u) \to M \in W_u`$ である。
これと $`A \in W_u`$ に [T.XA_closed](#t-XA_closed) を $`X := W_u`$ として適用すると

```math
\forall M,\ M \in A_u\bigl((W_u)^{(A)}\bigr) \to M \in (W_u)^{(A)}
```

を得る。これは [T.A2'](Wset-ja.md#t-A2') の仮定であるから $`W_u \subseteq (W_u)^{(A)}`$ である。
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

である（$`z^{+0}`$ [D.shiftr0](Cnf-2-ja.md#d-shiftr0) は各対の第 1 成分に $`0`$ を足した列であり、
$`z`$ に等しい）。∎

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
$`j_0 \to^M_1 0`$（[D.nextrel1](Pss-ja.md#d-nextrel1)）なる $`j_0`$ が存在する。
$`\to^M_i`$ の定義（D.nextR）で $`i = 1 \ne 0`$ であるから
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
[T.A1_intro](Wset-ja.md#t-A1_intro) より $`\bigl((0,0)\bigr) \in W_0`$ である。

**(b) $`v = w + 1`$ のとき。** $`A_{w+1}`$ の定義（D.Aop）の分岐 (3) を $`m := w`$ で示す。
$`w \lt w+1`$ である。[T.domT_Om](#t-domT_Om) より
$`\mathrm{domT}\bigl(\bigl((0,w+1)\bigr),\ w\bigr)`$ である。
$`z \in W_w`$ を取ると（$`\mathrm{based}(z)`$ は使わない）、
[T.graft_Om](#t-graft_Om) より $`\mathrm{graft}\bigl(\bigl((0,w+1)\bigr),\ z\bigr) = z`$ であり、
[T.W_mono](Wset-ja.md#t-W_mono) を $`w \le w+1`$ に適用して $`z \in W_{w+1}`$ を得る。
よって分岐 (3) が成り立ち、[T.A1_intro](Wset-ja.md#t-A1_intro) より
$`\bigl((0,w+1)\bigr) \in W_{w+1}`$ である。∎

<a id="d-Wstar"></a>
## 定義: $`W^{*}`$ (D.Wstar)

```math
W^{*} := \bigl\{\, R \in \mathrm{PairSeq} \ \bigm|\
  \mathrm{argOK}(R) \to \forall v \in \mathbb{N},\ (0,v) :: R \in W_v \,\bigr\} .
```

（$`\mathrm{argOK}`$ [D.argOK](Wset-ja.md#d-argOK)）

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

[T.graft_append](Wset-2-ja.md#t-graft_append) を $`A := \bigl((0,v)\bigr)`$、$`P := R`$ に適用すると

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

[T.entry_append_right](Column-ja.md#t-entry_append_right) を $`A := (p)`$、$`T := R`$ に適用すると

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

[T.nextR_append_right](Column-ja.md#t-nextR_append_right) を $`A := (p)`$、$`T := R`$ に適用すると

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

（$`\le^M_0`$ [D.le0](Pss-ja.md#d-le0)）

### 証明

[T.le0_append_right](Column-ja.md#t-le0_append_right) を $`A := (p)`$、$`T := R`$ に適用すると

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

[T.idx1_append_right](Column-ja.md#t-idx1_append_right) を $`A := (p)`$、$`T := R`$ に適用すると
$`\mathrm{idx}_1\bigl((p) \mathbin{+\!\!+} R,\ \lvert (p)\rvert + j\bigr) = \mathrm{idx}_1(R,j)`$（[D.idx1](Pss-ja.md#d-idx1)）
を得る。
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
行 $`0`$ の親子関係（[D.nextrel0](Pss-ja.md#d-nextrel0)）である。

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

である。

「$`j' \lt j`$ なるすべての $`j'`$ について $`\Phi(j')`$」を仮定する。

$`j \lt \lvert R\rvert`$ とする。$`\lvert M\rvert = \lvert R\rvert + 1`$ であるから
$`j + 1 \lt \lvert M\rvert`$ である。次の 2 つを用意する。

1. $`M_{0,j+1} = R_{0,j}`$ であり、これは正である。実際
   [T.entry_cons](#t-entry_cons) より $`M_{0,j+1} = R_{0,j}`$ であり、
   $`j \lt \lvert R\rvert`$ と [T.entry_pair_mem](Wset-2-ja.md#t-entry_pair_mem) より
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
よって [T.hasParent_one_iff](Wset-ja.md#t-hasParent_one_iff) を $`j_1 := \lvert R\rvert`$ に適用でき、
示すべきことは $`\mathrm{r1cand}(M,\ \lvert R\rvert,\ j_0)`$（[D.r1cand](Wset-ja.md#d-r1cand)）をみたす $`j_0`$ の存在、
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
[T.hasParent_one_iff](Wset-ja.md#t-hasParent_one_iff) を $`R`$ と $`j_1 := \lvert R\rvert - 1`$ に適用して、
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
[T.hasParent_one_iff](Wset-ja.md#t-hasParent_one_iff) より
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

仮定 (1)(2)(3) により [T.oper_bad_unfold](Decrease-ja.md#t-oper_bad_unfold) が適用できる。
$`j_0 := \mathrm{par}^M_{i_1}(j_1)`$（[D.parent](Pss-ja.md#d-parent)）と書くと、仮定 (4) より $`j_0 = 0`$ であり、
[T.oper_bad_unfold](Decrease-ja.md#t-oper_bad_unfold) の $`d_0`$ は

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
[T.map_range_entry_eq_take](Column-2-ja.md#t-map_range_entry_eq_take) が使えて

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
（[T.parent_nextR](Decrease-ja.md#t-parent_nextR)）、
$`j_0 \lt k_1`$ である（[T.nextR_index_lt](Decrease-ja.md#t-nextR_index_lt)）。とくに $`k_1 \ne 0`$。

**(iv)** $`0 \lt R_{0,k_1}`$。実際 $`k_1 \lt \lvert R\rvert`$ であるから
[T.entry_pair_mem](Wset-2-ja.md#t-entry_pair_mem) より対 $`(R_{0,k_1}, R_{1,k_1})`$ は $`R`$ の要素であり、
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
また $`\mathrm{par}^M_i(\lvert R\rvert)`$ は [T.parent_nextR](Decrease-ja.md#t-parent_nextR) より
$`\to^M_i`$ で $`\lvert R\rvert`$ に至る添字であるから、第 2 段より
$`\mathrm{par}^M_i(\lvert R\rvert) = j_0 + 1`$。

**第 4 段：両辺を展開して比べる。**
(i)(iv) と第 3 段により [T.oper_bad_unfold](Decrease-ja.md#t-oper_bad_unfold) が $`M`$ に適用でき、
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
