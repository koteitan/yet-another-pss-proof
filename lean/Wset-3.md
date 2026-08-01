[← README](README.md) | [English](Wset-3.md) | [Japanese](Wset-3-ja.md) | Wset [1](Wset.md) [2](Wset-2.md) **3** [4](Wset-4.md)

<a id="t-XA_closed"></a>
## Theorem: $`A_u\bigl(X^{(A)}\bigr) \subseteq X^{(A)}`$ (T.XA_closed)

### Theorem

Let $`X \subseteq \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) satisfy
$`\forall M,\ M \in A_u(X) \to M \in X`$ ([D.Aop](Wset.md#d-Aop)), and let $`A \in X`$. Then

```math
\forall M,\ M \in A_u\bigl(X^{(A)}\bigr) \to M \in X^{(A)} .
```

### Proof

Let $`B \in A_u(X^{(A)})`$ ([D.XA](Wset-2.md#d-XA)). By the definition of $`X^{(A)}`$ (D.XA), it
suffices to assume $`\mathrm{rsum}(A,B)`$ ([D.rsum](Wset.md#d-rsum)) and to show
$`A \mathbin{+\!\!+} B \in X`$.

If $`B = ()`$ then $`A \mathbin{+\!\!+} () = A \in X`$. So assume from now on $`B \ne ()`$,
that is, $`0 \lt \lvert B\rvert`$. By the definition of $`\mathrm{rsum}(A,B)`$ (D.rsum),

```math
(\ast)\qquad \forall p \in B,\ B_{0,0} \le p_1,
\qquad\qquad
(\ast\ast)\qquad \forall p \in A,\ B_{0,0} \le p_1
```

hold. We distinguish cases according to the three branches of the definition of $`A_u`$ (D.Aop).

**Branch (1): the case $`\lvert B\rvert \le 1 \wedge B_{1,0} = 0`$ ([D.entry](Pss.md#d-entry)).**
Together with $`0 \lt \lvert B\rvert`$ this gives $`\lvert B\rvert = 1`$. We distinguish according to
whether $`A`$ is empty.

**The case $`A = ()`$.** The hypothesis of the present case is branch (1) itself, so
$`B \in A_u(X)`$, and the hypothesis on $`X`$ gives $`B \in X`$; hence
$`A \mathbin{+\!\!+} B = B \in X`$.

**The case $`A \ne ()`$.** Then $`0 \lt \lvert A\rvert`$. Since
$`\lvert A \mathbin{+\!\!+} B\rvert = \lvert A\rvert + 1`$,

```math
\lvert A \mathbin{+\!\!+} B\rvert - 1 = \lvert A\rvert + 0 .
```

First, for every $`i`$ we have
$`\neg\,\mathrm{hasParent}(A \mathbin{+\!\!+} B,\ i,\ \lvert A \mathbin{+\!\!+} B\rvert - 1)`$ ([D.hasParent](Pss.md#d-hasParent)).
Indeed, if this were to hold then, since $`0 \lt \lvert B\rvert`$, applying
[T.hasParent_append_gen](Wset-2.md#t-hasParent_append_gen) with $`j := 0`$ gives
$`\mathrm{hasParent}(B, i, 0)`$. By the definition of $`\mathrm{hasParent}`$ (D.hasParent) there is
$`j_0`$ with $`j_0 \to^B_i 0`$ ([D.nextR](Pss.md#d-nextR)), but
[T.nextR_index_lt](Decrease.md#t-nextR_index_lt) gives $`j_0 \lt 0`$, a contradiction.

Next we show $`\mathrm{natDom}(A \mathbin{+\!\!+} B)`$ ([D.natDom](Wset.md#d-natDom)). Since
$`\lvert B\rvert - 1 = 0`$ we have $`B_{1,\lvert B\rvert-1} = B_{1,0} = 0`$, so the first disjunct on
the right-hand side of [T.natDom_iff](Wset.md#t-natDom_iff) holds and therefore
$`\mathrm{natDom}(B)`$. By [T.natDom_append](Wset-2.md#t-natDom_append) we get
$`\mathrm{natDom}(A \mathbin{+\!\!+} B)`$.

Finally we show $`(A \mathbin{+\!\!+} B)[n] = A \in X`$ ([D.oper](Pss.md#d-oper)) for every $`n \ge 1`$.
Since $`2 \le \lvert A \mathbin{+\!\!+} B\rvert`$ we have $`\lvert A \mathbin{+\!\!+} B\rvert - 1 \ne 0`$.
Abbreviate $`J := \lvert A \mathbin{+\!\!+} B\rvert - 1`$. If
$`(A \mathbin{+\!\!+} B)_{0,J} = 0 \wedge (A \mathbin{+\!\!+} B)_{1,J} = 0`$ holds, then
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) applies; if it does not, then the
absence of a parent shown above together with
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) applies; in either case
$`(A \mathbin{+\!\!+} B)[n] = \mathrm{Pred}(A \mathbin{+\!\!+} B)`$ ([D.Pred](Pss.md#d-Pred)).
From $`2 \le \lvert A \mathbin{+\!\!+} B\rvert`$ the second case of the definition of $`\mathrm{Pred}`$
(D.Pred) is selected, and since $`B \ne ()`$

```math
\mathrm{Pred}(A \mathbin{+\!\!+} B) = \mathrm{dropLast}(A \mathbin{+\!\!+} B)
  = A \mathbin{+\!\!+} \mathrm{dropLast}\,B = A \mathbin{+\!\!+} () = A
```

(because $`\lvert B\rvert = 1`$ gives $`\mathrm{dropLast}\,B = ()`$). Hence
$`(A \mathbin{+\!\!+} B)[n] = A \in X`$.

Therefore $`A \mathbin{+\!\!+} B`$ satisfies branch (2) of the definition of $`A_u`$ (D.Aop); that is,
$`A \mathbin{+\!\!+} B \in A_u(X)`$, and the hypothesis gives $`A \mathbin{+\!\!+} B \in X`$.

**Branch (2): the case $`\mathrm{natDom}(B) \wedge \forall n \ge 1,\ B[n] \in X^{(A)}`$.**
We distinguish according to whether $`2 \le \lvert B\rvert`$.

**The case $`2 \le \lvert B\rvert`$.** By [T.natDom_append](Wset-2.md#t-natDom_append) we have
$`\mathrm{natDom}(A \mathbin{+\!\!+} B)`$. Take $`n \ge 1`$; then
[T.oper_append_gen](Wset-2.md#t-oper_append_gen) gives

```math
(A \mathbin{+\!\!+} B)[n] = A \mathbin{+\!\!+} B[n]
```

Since $`B[n] \in X^{(A)}`$, in order to obtain $`A \mathbin{+\!\!+} B[n] \in X`$ it suffices to check
$`\mathrm{rsum}(A,\ B[n])`$. By [T.oper_head_eq](Wset-2.md#t-oper_head_eq) we have
$`(B[n])_{0,0} = B_{0,0}`$. Take $`p \in A \mathbin{+\!\!+} B[n]`$: if $`p \in A`$ then
$`B_{0,0} \le p_1`$ by $`(\ast\ast)`$, and if $`p \in B[n]`$ then $`B_{0,0} \le p_1`$ by
$`(\ast)`$ and [T.oper_mem_ge](Wset-2.md#t-oper_mem_ge) (with $`c := B_{0,0}`$).
Hence $`\mathrm{rsum}(A, B[n])`$ holds and $`(A \mathbin{+\!\!+} B)[n] \in X`$.
That is, $`A \mathbin{+\!\!+} B`$ satisfies branch (2), so the hypothesis gives
$`A \mathbin{+\!\!+} B \in X`$.

**The case $`\neg(2 \le \lvert B\rvert)`$.** Then $`\lvert B\rvert \le 1`$, that is
$`\lvert B\rvert - 1 = 0`$, so [T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) gives
$`B[1] = B`$. Applying the second conjunct of branch (2) with $`n := 1`$ yields
$`B[1] \in X^{(A)}`$, that is $`B \in X^{(A)}`$. Feeding the hypothesis $`\mathrm{rsum}(A,B)`$ to
this gives $`A \mathbin{+\!\!+} B \in X`$.

**Branch (3), that is, the case where there is $`m`$ with $`m \lt u`$, $`\mathrm{domT}(B,m)`$ ([D.domT](Wset.md#d-domT)) and
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(B,z) \in X^{(A)}`$ ([D.W](Wset.md#d-W), [D.based](Wset.md#d-based), [D.graft](Wset.md#d-graft)).**
By [T.domT_append](Wset-2.md#t-domT_append) we have $`\mathrm{domT}(A \mathbin{+\!\!+} B,\ m)`$.
Let $`z \in W_m`$ satisfy $`\mathrm{based}(z)`$. By
[T.graft_append](Wset-2.md#t-graft_append),

```math
\mathrm{graft}(A \mathbin{+\!\!+} B,\ z) = A \mathbin{+\!\!+} \mathrm{graft}(B,z)
```

Since $`\mathrm{graft}(B,z) \in X^{(A)}`$, in order to show that this belongs to $`X`$ it suffices to
check $`\mathrm{rsum}\bigl(A,\ \mathrm{graft}(B,z)\bigr)`$.

- The case $`\mathrm{graft}(B,z) = ()`$. By D.entry we have $`()_{0,0} = 0`$, so the requirement of
  the definition of $`\mathrm{rsum}`$ (D.rsum) is $`\forall p \in A \mathbin{+\!\!+} (),\ 0 \le p_1`$,
  which always holds for natural numbers.

- The case $`\mathrm{graft}(B,z) \ne ()`$. By [T.graft_head_eq](Wset-2.md#t-graft_head_eq) we have
  $`\bigl(\mathrm{graft}(B,z)\bigr)_{0,0} = B_{0,0}`$. Take
  $`p \in A \mathbin{+\!\!+} \mathrm{graft}(B,z)`$: if $`p \in A`$ then $`B_{0,0} \le p_1`$ by
  $`(\ast\ast)`$, and if $`p \in \mathrm{graft}(B,z)`$ then $`B_{0,0} \le p_1`$ by $`(\ast)`$ and
  [T.graft_mem_ge](Wset-2.md#t-graft_mem_ge) (with $`c := B_{0,0}`$).

Hence $`A \mathbin{+\!\!+} B`$ satisfies branch (3) of $`A_u`$ with the same $`m`$, and the hypothesis
gives $`A \mathbin{+\!\!+} B \in X`$. ∎

<a id="t-W_add"></a>
## Theorem: additivity of $`W_u`$ under concatenation (T.W_add)

### Theorem

If $`A \in W_u`$, $`B \in W_u`$ and $`\mathrm{rsum}(A,B)`$, then $`A \mathbin{+\!\!+} B \in W_u`$.

### Proof

[T.A1_intro](Wset.md#t-A1_intro) states $`\forall M,\ M \in A_u(W_u) \to M \in W_u`$. Applying
[T.XA_closed](#t-XA_closed) with $`X := W_u`$ to this and to $`A \in W_u`$ gives

```math
\forall M,\ M \in A_u\bigl((W_u)^{(A)}\bigr) \to M \in (W_u)^{(A)}
```

This is the hypothesis of [T.A2'](Wset.md#t-A2'), so $`W_u \subseteq (W_u)^{(A)}`$. From
$`B \in W_u`$ we get in particular $`B \in (W_u)^{(A)}`$, and feeding the hypothesis
$`\mathrm{rsum}(A,B)`$ to the definition of $`X^{(A)}`$ (D.XA) yields
$`A \mathbin{+\!\!+} B \in W_u`$. ∎

<a id="t-graft_Om"></a>
## Theorem: grafting onto a single-column sequence (T.graft_Om)

### Theorem

For all $`v \in \mathbb{N}`$ and $`z \in \mathrm{PairSeq}`$,
$`\mathrm{graft}\bigl(\bigl((0,v)\bigr),\ z\bigr) = z`$.

### Proof

$`\bigl((0,v)\bigr)`$ is a sequence of length $`1`$, so $`\lvert \bigl((0,v)\bigr)\rvert - 1 = 0`$,
and by the definition of $`M_{i,j}`$ (D.entry) we have $`\bigl((0,v)\bigr)_{0,0} = 0`$.
Moreover $`\mathrm{dropLast}\,\bigl((0,v)\bigr) = ()`$. Hence the definition of $`\mathrm{graft}`$
(D.graft) gives

```math
\mathrm{graft}\bigl(\bigl((0,v)\bigr),\ z\bigr) = () \mathbin{+\!\!+} z^{+0} = z
```

(here $`z^{+0}`$ [D.shiftr0](Cnf-2.md#d-shiftr0) is the sequence obtained by adding $`0`$ to the
first entry of each pair, which equals $`z`$). ∎

<a id="t-domT_Om"></a>
## Theorem: $`\mathrm{domT}`$ of a single-column sequence (T.domT_Om)

### Theorem

For every $`m \in \mathbb{N}`$, $`\mathrm{domT}\bigl(\bigl((0,m+1)\bigr),\ m\bigr)`$.

### Proof

Put $`M := \bigl((0,m+1)\bigr)`$. Then $`\lvert M\rvert - 1 = 0`$. We prove the two conjuncts of the
definition of $`\mathrm{domT}`$ (D.domT).

The first conjunct is $`M_{1,0} = m+1`$, and this holds by the definition of $`M_{i,j}`$ (D.entry).

We show the second conjunct $`\neg\,\mathrm{hasParent}(M, 1, 0)`$.
Suppose $`\mathrm{hasParent}(M,1,0)`$. By the definition of $`\mathrm{hasParent}`$ (D.hasParent)
there is $`j_0`$ with $`j_0 \to^M_1 0`$ ([D.nextrel1](Pss.md#d-nextrel1)).
In the definition of $`\to^M_i`$ (D.nextR) we have $`i = 1 \ne 0`$, so this is
$`j_0 \to^M_1 0`$ (the parent relation in row $`1`$), and the third condition of its definition
(D.nextrel1) is $`j_0 \lt 0`$. No natural number satisfies this, a contradiction. ∎

<a id="t-Om_mem_W"></a>
## Theorem: $`\bigl((0,v)\bigr) \in W_v`$ (T.Om_mem_W)

### Theorem

For every $`v \in \mathbb{N}`$, $`\bigl((0,v)\bigr) \in W_v`$.

### Proof

We distinguish cases according to whether $`v`$ is $`0`$ or a successor.

**(a) The case $`v = 0`$.** We have $`\lvert \bigl((0,0)\bigr)\rvert = 1 \le 1`$, and
by the definition of $`M_{i,j}`$ (D.entry) we have $`\bigl((0,0)\bigr)_{1,0} = 0`$.
Hence branch (1) of the definition of $`A_0`$ (D.Aop) holds, and
[T.A1_intro](Wset.md#t-A1_intro) gives $`\bigl((0,0)\bigr) \in W_0`$.

**(b) The case $`v = w + 1`$.** We verify branch (3) of the definition of $`A_{w+1}`$ (D.Aop) with
$`m := w`$. We have $`w \lt w+1`$. By [T.domT_Om](#t-domT_Om),
$`\mathrm{domT}\bigl(\bigl((0,w+1)\bigr),\ w\bigr)`$ holds.
Take $`z \in W_w`$ (the hypothesis $`\mathrm{based}(z)`$ is not used); by
[T.graft_Om](#t-graft_Om) we have $`\mathrm{graft}\bigl(\bigl((0,w+1)\bigr),\ z\bigr) = z`$, and
applying [T.W_mono](Wset.md#t-W_mono) to $`w \le w+1`$ gives $`z \in W_{w+1}`$.
Hence branch (3) holds, and [T.A1_intro](Wset.md#t-A1_intro) gives
$`\bigl((0,w+1)\bigr) \in W_{w+1}`$. ∎

<a id="d-Wstar"></a>
## Definition: $`W^{*}`$ (D.Wstar)

```math
W^{*} := \bigl\{\, R \in \mathrm{PairSeq} \ \bigm|\
  \mathrm{argOK}(R) \to \forall v \in \mathbb{N},\ (0,v) :: R \in W_v \,\bigr\} .
```

($`\mathrm{argOK}`$ [D.argOK](Wset.md#d-argOK))

<a id="d-tow"></a>
## Definition: tower (D.tow)

For $`v \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$, the sequence $`\mathrm{tow}_v(R,k)`$ is
defined by recursion on $`k`$.

```math
\mathrm{tow}_v(R, 0) := (),
\qquad
\mathrm{tow}_v(R, k+1) := (0,v) :: \mathrm{graft}\bigl(R,\ \mathrm{tow}_v(R,k)\bigr).
```

The argument of the recursive call is $`k`$, which is strictly smaller than $`k+1`$, so this
definition is well defined.

<a id="t-graft_cons"></a>
## Theorem: grafting past the root (T.graft_cons)

### Theorem

If $`R \ne ()`$ then

```math
\mathrm{graft}\bigl((0,v) :: R,\ z\bigr) = (0,v) :: \mathrm{graft}(R, z).
```

### Proof

Applying [T.graft_append](Wset-2.md#t-graft_append) with $`A := \bigl((0,v)\bigr)`$ and $`P := R`$
gives

```math
\mathrm{graft}\bigl(\bigl((0,v)\bigr) \mathbin{+\!\!+} R,\ z\bigr)
  = \bigl((0,v)\bigr) \mathbin{+\!\!+} \mathrm{graft}(R,z)
```

Concatenation with a sequence of length $`1`$ on the left is prepending, so
$`\bigl((0,v)\bigr) \mathbin{+\!\!+} R = (0,v) :: R`$ and
$`\bigl((0,v)\bigr) \mathbin{+\!\!+} \mathrm{graft}(R,z) = (0,v) :: \mathrm{graft}(R,z)`$. ∎

<a id="t-entry_cons"></a>
## Theorem: shift of the index under prepending (T.entry_cons)

### Theorem

For all $`p \in \mathbb{N}\times\mathbb{N}`$, $`R \in \mathrm{PairSeq}`$ and $`i, j \in \mathbb{N}`$,

```math
(p :: R)_{i,\ j+1} = R_{i,j} .
```

### Proof

Applying [T.entry_append_right](Column.md#t-entry_append_right) with $`A := (p)`$ and $`T := R`$
gives

```math
\bigl((p) \mathbin{+\!\!+} R\bigr)_{i,\ \lvert (p)\rvert + j} = R_{i,j}
```

Here $`(p) \mathbin{+\!\!+} R = p :: R`$ and $`\lvert (p)\rvert = 1`$, and by commutativity of
addition on $`\mathbb{N}`$ we have $`1 + j = j + 1`$. ∎

<a id="t-nextR_cons"></a>
## Theorem: shift of the parent relation under prepending (T.nextR_cons)

### Theorem

```math
(j_0 + 1) \to^{p :: R}_i (j_1 + 1) \iff j_0 \to^{R}_i j_1 .
```

### Proof

Applying [T.nextR_append_right](Column.md#t-nextR_append_right) with $`A := (p)`$ and $`T := R`$
gives

```math
\bigl(\lvert (p)\rvert + j_0\bigr) \to^{(p) \mathbin{+\!\!+} R}_i \bigl(\lvert (p)\rvert + j_1\bigr)
  \iff j_0 \to^R_i j_1
```

Here $`(p) \mathbin{+\!\!+} R = p :: R`$ and $`\lvert (p)\rvert = 1`$, and
$`1 + j_0 = j_0 + 1`$, $`1 + j_1 = j_1 + 1`$. ∎

<a id="t-le0_cons"></a>
## Theorem: shift of the ancestor relation under prepending (T.le0_cons)

### Theorem

```math
(j_0 + 1) \le^{p :: R}_0 (j_1 + 1) \iff j_0 \le^{R}_0 j_1 .
```

($`\le^M_0`$ [D.le0](Pss.md#d-le0))

### Proof

Applying [T.le0_append_right](Column.md#t-le0_append_right) with $`A := (p)`$ and $`T := R`$ gives

```math
\bigl(\lvert (p)\rvert + j_0\bigr) \le^{(p) \mathbin{+\!\!+} R}_0 \bigl(\lvert (p)\rvert + j_1\bigr)
  \iff j_0 \le^R_0 j_1
```

Here $`(p) \mathbin{+\!\!+} R = p :: R`$ and $`\lvert (p)\rvert = 1`$, and
$`1 + j_0 = j_0 + 1`$, $`1 + j_1 = j_1 + 1`$. ∎

<a id="t-idx1_cons"></a>
## Theorem: shift of the search row under prepending (T.idx1_cons)

### Theorem

```math
\mathrm{idx}_1(p :: R,\ j+1) = \mathrm{idx}_1(R,\ j) .
```

### Proof

Applying [T.idx1_append_right](Column.md#t-idx1_append_right) with $`A := (p)`$ and $`T := R`$ gives
$`\mathrm{idx}_1\bigl((p) \mathbin{+\!\!+} R,\ \lvert (p)\rvert + j\bigr) = \mathrm{idx}_1(R,j)`$ ([D.idx1](Pss.md#d-idx1)).
Here $`(p) \mathbin{+\!\!+} R = p :: R`$ and $`\lvert (p)\rvert = 1`$, and $`1 + j = j + 1`$. ∎

<a id="t-hasParent_zero_iff"></a>
## Theorem: criterion for the existence of a parent in row 0 (T.hasParent_zero_iff)

### Theorem

If $`b \lt \lvert M\rvert`$ then

```math
\mathrm{hasParent}(M, 0, b) \iff \exists k,\ \bigl(k \lt b \wedge M_{0,k} \lt M_{0,b}\bigr).
```

### Proof

In the definition of $`\to^M_i`$ (D.nextR) we have $`i = 0`$, so from now on $`j_0 \to^M_0 j_1`$ is
the parent relation in row $`0`$ ([D.nextrel0](Pss.md#d-nextrel0)).

**(Left to right)** Suppose $`\mathrm{hasParent}(M,0,b)`$. By the definition of
$`\mathrm{hasParent}`$ (D.hasParent) there is $`k`$ with $`k \to^M_0 b`$.
The third condition of the definition of $`\to^M_0`$ (D.nextrel0) is $`k \lt b`$ and the fourth is
$`M_{0,k} \lt M_{0,b}`$, so this $`k`$ is the one required.

**(Right to left)** Suppose we are given $`k`$ satisfying the predicate

```math
P(t) :\equiv \bigl(t \lt b \wedge M_{0,t} \lt M_{0,b}\bigr)
```

The set $`\{\, t \mid t \le b \wedge P(t)\,\}`$ contains $`k`$ (from $`P(k)`$ we get $`k \lt b`$,
in particular $`k \le b`$), hence is not empty, and it is bounded above by $`b`$, so it has a
greatest element. Call it $`g`$. Then

```math
(\dagger)\qquad P(g),
\qquad\qquad
(\ddagger)\qquad \forall t,\ P(t) \to t \le g
```

hold ($`(\ddagger)`$ because $`P(t)`$ implies $`t \lt b`$, in particular $`t \le b`$, and $`g`$ is
the greatest element).

First we show $`g \to^M_0 b`$. We verify the five conditions of the definition of $`\to^M_0`$
(D.nextrel0) in turn.

- (1) $`g \lt \lvert M\rvert`$: by $`(\dagger)`$ we have $`g \lt b`$, and $`b \lt \lvert M\rvert`$ by hypothesis.
- (2) $`b \lt \lvert M\rvert`$: this is the hypothesis.
- (3) $`g \lt b`$: this is the first conjunct of $`(\dagger)`$.
- (4) $`M_{0,g} \lt M_{0,b}`$: this is the second conjunct of $`(\dagger)`$.
- (5) $`\forall l,\ (g \lt l \wedge l \lt b) \to M_{0,b} \le M_{0,l}`$:
  take $`l`$ with $`g \lt l`$ and $`l \lt b`$, and suppose that $`M_{0,b} \le M_{0,l}`$ fails.
  Then $`M_{0,l} \lt M_{0,b}`$, which together with $`l \lt b`$ gives $`P(l)`$.
  By $`(\ddagger)`$ we get $`l \le g`$, contradicting $`g \lt l`$.

Next we show uniqueness. Suppose $`y \to^M_0 b`$. By the third and fourth conditions of D.nextrel0
we have $`y \lt b`$ and $`M_{0,y} \lt M_{0,b}`$, that is $`P(y)`$, so $`(\ddagger)`$ gives
$`y \le g`$. Suppose $`y \lt g`$. Then the fifth condition of $`y \to^M_0 b`$ can be applied with
$`j := g`$ (since $`y \lt g`$ and $`g \lt b`$), which gives $`M_{0,b} \le M_{0,g}`$; this
contradicts $`M_{0,g} \lt M_{0,b}`$ from $`(\dagger)`$. Hence $`y = g`$.

Therefore $`g`$ is the unique $`j_0`$ with $`j_0 \to^M_0 b`$, and $`\mathrm{hasParent}(M,0,b)`$
holds. ∎

<a id="t-le0_cons_zero"></a>
## Theorem: the root of the principal block is an ancestor of every column (T.le0_cons_zero)

### Theorem

If $`\mathrm{argOK}(R)`$ then, for every $`v \in \mathbb{N}`$ and every $`j \lt \lvert R\rvert`$,

```math
0 \le^{(0,v) :: R}_0 (j+1).
```

### Proof

Put $`M := (0,v) :: R`$. We argue by strong induction on $`j`$. Show

```math
\Phi(j) :\equiv \bigl(j \lt \lvert R\rvert \to 0 \le^{M}_0 (j+1)\bigr)
```

for every $`j`$,
and assume "$`\Phi(j')`$ for every $`j' \lt j`$".

Assume $`j \lt \lvert R\rvert`$. Since $`\lvert M\rvert = \lvert R\rvert + 1`$ we have
$`j + 1 \lt \lvert M\rvert`$. We prepare two facts.

1. $`M_{0,j+1} = R_{0,j}`$, and this is positive. Indeed, [T.entry_cons](#t-entry_cons) gives
   $`M_{0,j+1} = R_{0,j}`$, and from $`j \lt \lvert R\rvert`$ and
   [T.entry_pair_mem](Wset-2.md#t-entry_pair_mem) we get $`(R_{0,j}, R_{1,j}) \in R`$, so the
   definition of $`\mathrm{argOK}`$ (D.argOK) gives $`0 \lt R_{0,j}`$.
2. $`M_{0,0} = 0`$. The head of $`M`$ is $`(0,v)`$, so this holds by the definition of $`M_{i,j}`$
   (D.entry).

By 1 and 2 we have $`M_{0,0} \lt M_{0,j+1}`$, and $`0 \lt j+1`$, so $`k := 0`$ satisfies the
existence condition on the right-hand side of [T.hasParent_zero_iff](#t-hasParent_zero_iff).
Hence $`\mathrm{hasParent}(M, 0, j+1)`$ holds, and by the definition of $`\mathrm{hasParent}`$
(D.hasParent) there is $`k`$ with $`k \to^M_0 (j+1)`$. We distinguish cases according to whether
$`k`$ is $`0`$.

**(a) The case $`k = 0`$.** Since $`0 \to^M_0 (j+1)`$, we have
$`0 \mathbin{(\to^M_0)^{*}} (j+1)`$ as a chain of length $`1`$. Together with $`0 \lt \lvert M\rvert`$
and $`j+1 \lt \lvert M\rvert`$, all three conditions of the definition of $`\le^M_0`$ (D.le0) hold,
so $`0 \le^M_0 (j+1)`$.

**(b) The case $`k \ne 0`$.** Write $`k = k' + 1`$.
The third condition of the definition of $`\to^M_0`$ (D.nextrel0) gives $`k'+1 \lt j+1`$, that is
$`k' \lt j`$. Moreover $`k' \lt j \lt \lvert R\rvert`$. Applying the induction hypothesis
$`\Phi(k')`$ gives $`0 \le^M_0 (k'+1)`$. By the third condition of the definition of $`\le^M_0`$
(D.le0) we have $`0 \mathbin{(\to^M_0)^{*}} (k'+1)`$, and appending
$`k'+1 = k \to^M_0 (j+1)`$ to the end of this chain gives $`0 \mathbin{(\to^M_0)^{*}} (j+1)`$.
Together with $`0 \lt \lvert M\rvert`$ and $`j+1 \lt \lvert M\rvert`$ this gives
$`0 \le^M_0 (j+1)`$. ∎

<a id="t-len_succ"></a>
## Theorem: the length of a non-empty sequence (T.len_succ)

### Theorem

If $`R \ne ()`$ then $`\lvert R\rvert = (\lvert R\rvert - 1) + 1`$.

### Proof

From $`R \ne ()`$ we get $`0 \lt \lvert R\rvert`$. For a natural number $`x`$ with $`0 \lt x`$,
truncated subtraction satisfies $`(x - 1) + 1 = x`$. ∎

<a id="t-entry_cons_last"></a>
## Theorem: the last entry after prepending (T.entry_cons_last)

### Theorem

If $`R \ne ()`$ then, for all $`p`$ and $`i`$,

```math
(p :: R)_{i,\ \lvert R\rvert} = R_{i,\ \lvert R\rvert - 1} .
```

### Proof

By [T.len_succ](#t-len_succ) we have $`\lvert R\rvert = (\lvert R\rvert - 1) + 1`$, so the
left-hand side can be rewritten as $`(p :: R)_{i,\ (\lvert R\rvert - 1) + 1}`$.
It remains to apply [T.entry_cons](#t-entry_cons) to it with $`j := \lvert R\rvert - 1`$. ∎

<a id="t-le0_cons_last"></a>
## Theorem: the ancestor relation to the last column after prepending (T.le0_cons_last)

### Theorem

If $`R \ne ()`$ then, for all $`p`$ and $`j`$,

```math
(j+1) \le^{p :: R}_0 \lvert R\rvert \iff j \le^{R}_0 (\lvert R\rvert - 1).
```

### Proof

By [T.len_succ](#t-len_succ) we have $`\lvert R\rvert = (\lvert R\rvert - 1) + 1`$, so the
left-hand side can be rewritten as $`(j+1) \le^{p :: R}_0 \bigl((\lvert R\rvert - 1) + 1\bigr)`$.
It remains to apply [T.le0_cons](#t-le0_cons) to it with $`j_0 := j`$ and
$`j_1 := \lvert R\rvert - 1`$. ∎

<a id="t-nextR_cons_last"></a>
## Theorem: the parent relation to the last column after prepending (T.nextR_cons_last)

### Theorem

If $`R \ne ()`$ then, for all $`p`$, $`i`$ and $`j`$,

```math
(j+1) \to^{p :: R}_i \lvert R\rvert \iff j \to^{R}_i (\lvert R\rvert - 1).
```

### Proof

By [T.len_succ](#t-len_succ) we have $`\lvert R\rvert = (\lvert R\rvert - 1) + 1`$, so the
left-hand side can be rewritten as $`(j+1) \to^{p :: R}_i \bigl((\lvert R\rvert - 1) + 1\bigr)`$.
It remains to apply [T.nextR_cons](#t-nextR_cons) to it with $`j_0 := j`$ and
$`j_1 := \lvert R\rvert - 1`$. ∎

<a id="t-idx1_cons_last"></a>
## Theorem: the search row of the last column after prepending (T.idx1_cons_last)

### Theorem

If $`R \ne ()`$ then, for every $`p`$,

```math
\mathrm{idx}_1\bigl(p :: R,\ \lvert R\rvert\bigr) = \mathrm{idx}_1\bigl(R,\ \lvert R\rvert - 1\bigr).
```

### Proof

By [T.len_succ](#t-len_succ) we have $`\lvert R\rvert = (\lvert R\rvert - 1) + 1`$, so the
left-hand side can be rewritten as $`\mathrm{idx}_1\bigl(p :: R,\ (\lvert R\rvert - 1) + 1\bigr)`$.
It remains to apply [T.idx1_cons](#t-idx1_cons) to it with $`j := \lvert R\rvert - 1`$. ∎

<a id="t-cons_len_lt"></a>
## Theorem: prepending increases the length (T.cons_len_lt)

### Theorem

For all $`p`$ and $`R`$, $`\lvert R\rvert \lt \lvert p :: R\rvert`$.

### Proof

We have $`\lvert p :: R\rvert = \lvert R\rvert + 1`$, and $`\lvert R\rvert \lt \lvert R\rvert + 1`$. ∎

<a id="t-hasParent_cons_one"></a>
## Theorem: the root becomes a parent in row 1 (T.hasParent_cons_one)

### Theorem

Assume $`\mathrm{argOK}(R)`$, $`R \ne ()`$ and

```math
\mathrm{hasParent}\bigl(R,\ 1,\ \lvert R\rvert - 1\bigr)
\ \vee\
v \lt R_{1,\ \lvert R\rvert - 1}
```

Then $`\mathrm{hasParent}\bigl((0,v) :: R,\ 1,\ \lvert R\rvert\bigr)`$.

### Proof

Put $`M := (0,v) :: R`$. From $`R \ne ()`$ we get $`0 \lt \lvert R\rvert`$, and
[T.cons_len_lt](#t-cons_len_lt) gives $`\lvert R\rvert \lt \lvert M\rvert`$.
Hence [T.hasParent_one_iff](Wset.md#t-hasParent_one_iff) can be applied with
$`j_1 := \lvert R\rvert`$, and what is to be shown reduces to the existence of $`j_0`$ satisfying
$`\mathrm{r1cand}(M,\ \lvert R\rvert,\ j_0)`$ ([D.r1cand](Wset.md#d-r1cand)), that is, by the
definition of $`\mathrm{r1cand}`$ (D.r1cand), to the existence of $`j_0`$ satisfying

```math
j_0 \lt \lvert R\rvert,
\qquad
j_0 \le^{M}_0 \lvert R\rvert,
\qquad
M_{1,j_0} \lt M_{1,\lvert R\rvert}
```

By [T.entry_cons_last](#t-entry_cons_last) we have

```math
(\sharp)\qquad M_{1,\lvert R\rvert} = R_{1,\lvert R\rvert - 1}
```

We distinguish cases according to the disjunction in the hypothesis.

**(a) The case $`\mathrm{hasParent}(R, 1, \lvert R\rvert - 1)`$.**
Since $`\lvert R\rvert - 1 \lt \lvert R\rvert`$, we may apply
[T.hasParent_one_iff](Wset.md#t-hasParent_one_iff) to $`R`$ with $`j_1 := \lvert R\rvert - 1`$ and
take $`j'`$ satisfying $`\mathrm{r1cand}(R,\ \lvert R\rvert - 1,\ j')`$, that is,

```math
j' \lt \lvert R\rvert - 1,
\qquad
j' \le^{R}_0 (\lvert R\rvert - 1),
\qquad
R_{1,j'} \lt R_{1,\lvert R\rvert - 1}
```

Take $`j_0 := j' + 1`$. We verify the three conditions.

- From $`j' \lt \lvert R\rvert - 1`$ we get $`j' + 1 \lt \lvert R\rvert`$.
- Applying [T.le0_cons_last](#t-le0_cons_last) with $`j := j'`$ turns
  $`j' \le^R_0 (\lvert R\rvert - 1)`$ into $`(j'+1) \le^M_0 \lvert R\rvert`$.
- By [T.entry_cons](#t-entry_cons) we have $`M_{1,j'+1} = R_{1,j'}`$, so together with
  $`(\sharp)`$ we get $`M_{1,j'+1} = R_{1,j'} \lt R_{1,\lvert R\rvert-1} = M_{1,\lvert R\rvert}`$.

**(b) The case $`v \lt R_{1,\lvert R\rvert - 1}`$.** Take $`j_0 := 0`$. We verify the three conditions.

- $`0 \lt \lvert R\rvert`$.
- Applying [T.le0_cons_zero](#t-le0_cons_zero) with $`j := \lvert R\rvert - 1`$ (which is strictly
  smaller than $`\lvert R\rvert`$) gives $`0 \le^M_0 \bigl((\lvert R\rvert - 1) + 1\bigr)`$.
  By [T.len_succ](#t-len_succ) we have $`(\lvert R\rvert - 1) + 1 = \lvert R\rvert`$, hence
  $`0 \le^M_0 \lvert R\rvert`$.
- The head of $`M`$ is $`(0,v)`$, so the definition of $`M_{i,j}`$ (D.entry) gives $`M_{1,0} = v`$,
  and the hypothesis together with $`(\sharp)`$ gives
  $`M_{1,0} = v \lt R_{1,\lvert R\rvert-1} = M_{1,\lvert R\rvert}`$.

In either case we have obtained $`j_0`$ satisfying the conditions, so
[T.hasParent_one_iff](Wset.md#t-hasParent_one_iff) gives
$`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$. ∎

<a id="t-oper_root_tiling"></a>
## Theorem: when the parent is the root, the expansion is a tiling of the leading block (T.oper_root_tiling)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$, and put $`j_1 := \lvert M\rvert - 1`$ and
$`i_1 := \mathrm{idx}_1(M, j_1)`$. Assume the following four statements.

```math
\begin{aligned}
&(1)\ j_1 \ne 0, \cr
&(2)\ \neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr), \cr
&(3)\ \mathrm{hasParent}(M, i_1, j_1), \cr
&(4)\ \mathrm{par}^M_{i_1}(j_1) = 0 .
\end{aligned}
```

Furthermore put

```math
e := \begin{cases} M_{0,j_1} - M_{0,0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
```

Then

```math
M[n] = \bigl(\mathrm{dropLast}\,M\bigr)^{+0\cdot e} \mathbin{+\!\!+}
       \bigl(\mathrm{dropLast}\,M\bigr)^{+1\cdot e} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+}
       \bigl(\mathrm{dropLast}\,M\bigr)^{+(n-1)e} .
```

### Proof

By hypotheses (1), (2), (3), [T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) applies.
Writing $`j_0 := \mathrm{par}^M_{i_1}(j_1)`$ ([D.parent](Pss.md#d-parent)), hypothesis (4) gives
$`j_0 = 0`$, and the $`d_0`$ of [T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) is

```math
d_0 = \begin{cases} M_{0,j_1} - M_{0,j_0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
= e
```

In the conclusion of that same theorem the prefix part is $`(M_0,\dots,M_{j_0-1})`$, which by
$`j_0 = 0`$ is the empty sequence $`()`$, so

```math
M[n] = B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,e,\ M_{1,j})\,\bigr)_{j=0}^{j_1-1}
```

It remains to show $`B_k = (\mathrm{dropLast}\,M)^{+k\,e}`$ for each $`k`$.

We have $`\mathrm{dropLast}\,M = \mathrm{take}_{j_1} M`$ (here $`\mathrm{take}_a L`$ is the sequence
consisting of the first $`a`$ elements of $`L`$, and $`j_1 = \lvert M\rvert - 1`$).
Since $`j_1 \le \lvert M\rvert`$, [T.map_range_entry_eq_take](Column-2.md#t-map_range_entry_eq_take)
applies and gives

```math
\bigl(\,(M_{0,j},\ M_{1,j})\,\bigr)_{j=0}^{j_1-1} = \mathrm{take}_{j_1} M = \mathrm{dropLast}\,M
```

Now $`B_k`$ is nothing but the sequence obtained from this one by adding $`k\,e`$ to the first entry
of each of its elements, hence $`B_k = (\mathrm{dropLast}\,M)^{+k\,e}`$. ∎

<a id="t-oper_cons_nat"></a>
## Theorem: the principal non-collapsing step (T.oper_cons_nat)

### Theorem

Let $`v, n \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$, and put $`k_1 := \lvert R\rvert - 1`$ and
$`i := \mathrm{idx}_1(R, k_1)`$.
Assuming $`\mathrm{argOK}(R)`$, $`R \ne ()`$ and $`\mathrm{hasParent}(R, i, k_1)`$, we have

```math
\bigl((0,v) :: R\bigr)[n] = (0,v) :: R[n] .
```

### Proof

Write $`M := (0,v) :: R`$. We first prepare the following facts.

**(i)** From $`R \ne ()`$ we get $`0 \lt \lvert R\rvert`$. Moreover
$`\lvert M\rvert = \lvert R\rvert + 1`$, so $`\lvert M\rvert - 1 = \lvert R\rvert`$; that is, the
index of the last column of $`M`$ is $`\lvert R\rvert`$.

**(ii)** $`M_{0,\lvert R\rvert} = R_{0,k_1}`$ and $`M_{1,\lvert R\rvert} = R_{1,k_1}`$.
This is [T.entry_cons_last](#t-entry_cons_last).

**(iii)** Putting $`j_0 := \mathrm{par}^R_i(k_1)`$ we have $`j_0 \to^R_i k_1`$
([T.parent_nextR](Decrease.md#t-parent_nextR)) and
$`j_0 \lt k_1`$ ([T.nextR_index_lt](Decrease.md#t-nextR_index_lt)). In particular $`k_1 \ne 0`$.

**(iv)** $`0 \lt R_{0,k_1}`$. Indeed $`k_1 \lt \lvert R\rvert`$, so
[T.entry_pair_mem](Wset-2.md#t-entry_pair_mem) shows that the pair $`(R_{0,k_1}, R_{1,k_1})`$ is an
element of $`R`$, and by the definition of $`\mathrm{argOK}`$ (D.argOK) its first entry is positive.
Hence $`\neg(R_{0,k_1} = 0 \wedge R_{1,k_1} = 0)`$, and by (ii) also
$`\neg(M_{0,\lvert R\rvert} = 0 \wedge M_{1,\lvert R\rvert} = 0)`$.

**(v)** $`\mathrm{idx}_1(M, \lvert M\rvert - 1) = \mathrm{idx}_1(M, \lvert R\rvert) = \mathrm{idx}_1(R, k_1) = i`$.
This is (i) together with [T.idx1_cons_last](#t-idx1_cons_last).

**Step 1: the root $`0`$ is not the parent of the last column of $`M`$, that is, $`\neg\bigl(0 \to^M_i \lvert R\rvert\bigr)`$.**
Assume $`0 \to^M_i \lvert R\rvert`$ and derive a contradiction. We distinguish cases on $`i`$.

**(a) The case $`i = 0`$.** By the definition of $`\to^M_i`$ (D.nextR) we have
$`0 \to^M_0 \lvert R\rvert`$. Apply condition (5) of its definition (D.nextrel0) with
$`j := j_0 + 1`$. The first conjunct of the antecedent, $`0 \lt j_0 + 1`$, holds because the
successor of a natural number is positive. The second conjunct is obtained from
$`j_0 \lt k_1 = \lvert R\rvert - 1`$ in (iii) as $`j_0 + 1 \lt \lvert R\rvert`$. Hence
$`M_{0,\lvert R\rvert} \le M_{0,j_0+1}`$.
By (ii) and [T.entry_cons](#t-entry_cons) this is $`R_{0,k_1} \le R_{0,j_0}`$.
On the other hand condition (4) of $`j_0 \to^R_0 k_1`$ from (iii) is $`R_{0,j_0} \lt R_{0,k_1}`$,
a contradiction.

**(b) The case $`i \ne 0`$.** By the definition of $`\to^M_i`$ (D.nextR) we have
$`0 \to^M_1 \lvert R\rvert`$. Apply condition (6) of its definition (D.nextrel1) with
$`j := j_0 + 1`$. The first conjunct of the antecedent, $`0 \lt j_0 + 1`$, holds because the
successor of a natural number is positive. The second conjunct $`j_0 + 1 \le^M_0 \lvert R\rvert`$
follows from condition (5) of $`j_0 \to^R_1 k_1`$ in (iii), which is $`j_0 \le^R_0 k_1`$, together
with [T.le0_cons_last](#t-le0_cons_last). Hence
$`M_{1,\lvert R\rvert} \le M_{1,j_0+1}`$, that is, by (ii) and [T.entry_cons](#t-entry_cons),
$`R_{1,k_1} \le R_{1,j_0}`$.
On the other hand condition (4) of $`j_0 \to^R_1 k_1`$ is $`R_{1,j_0} \lt R_{1,k_1}`$,
a contradiction.

**Step 2: if $`y \to^M_i \lvert R\rvert`$ then $`y = j_0 + 1`$.**
The value $`y = 0`$ is excluded by Step 1, so we can write $`y = y' + 1`$.
By [T.nextR_cons_last](#t-nextR_cons_last) we have $`y' \to^R_i k_1`$.
The uniqueness in the hypothesis $`\mathrm{hasParent}(R, i, k_1)`$ (the definition D.hasParent of
$`\mathrm{hasParent}`$) together with $`j_0 \to^R_i k_1`$ from (iii) gives $`y' = j_0`$, that is
$`y = j_0 + 1`$.

**Step 3: the parent on the side of $`M`$.**
By (iii) and [T.nextR_cons_last](#t-nextR_cons_last) we have $`j_0 + 1 \to^M_i \lvert R\rvert`$, and
by Step 2 the only such index is $`j_0 + 1`$. Hence $`\mathrm{hasParent}(M, i, \lvert R\rvert)`$
holds, and together with (i) and (v) we get
$`\mathrm{hasParent}\bigl(M, \mathrm{idx}_1(M,\lvert M\rvert-1), \lvert M\rvert-1\bigr)`$.
Moreover $`\mathrm{par}^M_i(\lvert R\rvert)`$ is, by
[T.parent_nextR](Decrease.md#t-parent_nextR), an index reaching $`\lvert R\rvert`$ along
$`\to^M_i`$, so Step 2 gives $`\mathrm{par}^M_i(\lvert R\rvert) = j_0 + 1`$.

**Step 4: unfold both sides and compare.**
By (i), (iv) and Step 3, [T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) applies to $`M`$, and by
(iii), (iv) and the hypothesis it applies to $`R`$ as well. They give respectively

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

where

```math
d = \begin{cases} M_{0,\lvert R\rvert} - M_{0,j_0+1} & (0 \lt i) \cr 0 & (i = 0) \end{cases},
\qquad
d' = \begin{cases} R_{0,k_1} - R_{0,j_0} & (0 \lt i) \cr 0 & (i = 0) \end{cases}
```

We check three points.

- $`d = d'`$: by (ii) we have $`M_{0,\lvert R\rvert} = R_{0,k_1}`$, and by
  [T.entry_cons](#t-entry_cons) we have $`M_{0,j_0+1} = R_{0,j_0}`$.
- The prefix part: since $`M = (0,v) :: R`$, we have
  $`(M_0,\dots,M_{j_0}) = (0,v) :: (R_0,\dots,R_{j_0-1})`$.
- The blocks: the index $`j`$ of $`B^M_k`$ runs from $`j_0+1`$ to $`\lvert R\rvert - 1`$, and the
  index $`j`$ of $`B^R_k`$ runs from $`j_0`$ to $`k_1 - 1 = \lvert R\rvert - 2`$, so both have
  length $`\lvert R\rvert - 1 - j_0`$. Substituting $`j = j' + 1`$,
  [T.entry_cons](#t-entry_cons) gives $`M_{0,j'+1} = R_{0,j'}`$ and $`M_{1,j'+1} = R_{1,j'}`$,
  so the $`j'`$-th entries of the two agree. Hence $`B^M_k = B^R_k`$.

Therefore

```math
M[n] = (0,v) :: \Bigl((R_0,\dots,R_{j_0-1}) \mathbin{+\!\!+} B^R_0 \mathbin{+\!\!+} \cdots
  \mathbin{+\!\!+} B^R_{n-1}\Bigr) = (0,v) :: R[n] . \qquad \blacksquare
```
