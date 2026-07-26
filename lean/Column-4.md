[← README](README.md) | [English](Column-4.md) | [Japanese](Column-4-ja.md) | Column [1](Column.md) [2](Column-2.md) [3](Column-3.md) **4**

<a id="t-nextrel0_unique"></a>
## Theorem: uniqueness of the parent in row 0 (T.nextrel0_unique)

### Theorem

If $`k_1 \to^M_0 j`$ ([D.nextrel0](Pss.md#d-nextrel0)) and $`k_2 \to^M_0 j`$, then $`k_1 = k_2`$.

### Proof

Distinguish cases by the trichotomy between $`k_1`$ and $`k_2`$.

**(a) The case $`k_1 \lt k_2`$.**
By the third condition of $`k_2 \to^M_0 j`$ (D.nextrel0) we have $`k_2 \lt j`$.
Substituting $`k_2`$ for the universally quantified variable in the fifth condition of
$`k_1 \to^M_0 j`$, its antecedent $`k_1 \lt k_2 \wedge k_2 \lt j`$ holds, so

```math
M_{0,j} \le M_{0,k_2}
```

($`M_{i,j}`$ [D.entry](Pss.md#d-entry)). On the other hand, the fourth condition of $`k_2 \to^M_0 j`$ is
$`M_{0,k_2} \lt M_{0,j}`$.
The two together give $`M_{0,j} \lt M_{0,j}`$, contradicting the irreflexivity of $`\lt`$.

**(b) The case $`k_1 = k_2`$.** This is the conclusion itself.

**(c) The case $`k_2 \lt k_1`$.**
By the third condition of $`k_1 \to^M_0 j`$ we have $`k_1 \lt j`$.
Substituting $`k_1`$ for the universally quantified variable in the fifth condition of
$`k_2 \to^M_0 j`$, its antecedent $`k_2 \lt k_1 \wedge k_1 \lt j`$ holds, so
$`M_{0,j} \le M_{0,k_1}`$. On the other hand, the fourth condition of $`k_1 \to^M_0 j`$ is
$`M_{0,k_1} \lt M_{0,j}`$. The two together give $`M_{0,j} \lt M_{0,j}`$, a contradiction. ∎

<a id="t-nextrel1_unique"></a>
## Theorem: uniqueness of the parent in row 1 (T.nextrel1_unique)

### Theorem

If $`k_1 \to^M_1 j`$ ([D.nextrel1](Pss.md#d-nextrel1)) and $`k_2 \to^M_1 j`$, then $`k_1 = k_2`$.

### Proof

Distinguish cases by the trichotomy between $`k_1`$ and $`k_2`$.

**(a) The case $`k_1 \lt k_2`$.**
By the fifth condition of $`k_2 \to^M_1 j`$ (D.nextrel1) we have $`k_2 \le^M_0 j`$ ([D.le0](Pss.md#d-le0)).
Substituting $`k_2`$ for the universally quantified variable in the sixth condition of
$`k_1 \to^M_1 j`$, its antecedent $`k_1 \lt k_2 \wedge k_2 \le^M_0 j`$ holds, so

```math
M_{1,j} \le M_{1,k_2}
```

On the other hand, the fourth condition of $`k_2 \to^M_1 j`$ is $`M_{1,k_2} \lt M_{1,j}`$.
The two together give $`M_{1,j} \lt M_{1,j}`$, contradicting the irreflexivity of $`\lt`$.

**(b) The case $`k_1 = k_2`$.** This is the conclusion itself.

**(c) The case $`k_2 \lt k_1`$.**
By the fifth condition of $`k_1 \to^M_1 j`$ we have $`k_1 \le^M_0 j`$.
Substituting $`k_1`$ for the universally quantified variable in the sixth condition of
$`k_2 \to^M_1 j`$, its antecedent $`k_2 \lt k_1 \wedge k_1 \le^M_0 j`$ holds, so
$`M_{1,j} \le M_{1,k_1}`$. On the other hand, the fourth condition of $`k_1 \to^M_1 j`$ is
$`M_{1,k_1} \lt M_{1,j}`$. The two together give $`M_{1,j} \lt M_{1,j}`$, a contradiction. ∎

<a id="t-blockok_head_zero"></a>
## Theorem: the head of a block has row 0 equal to 0 (T.blockok_head_zero)

### Theorem

If $`\mathrm{blockok}(0, M)`$ ([D.blockok](Seqlex.md#d-blockok)) and $`0 \lt \lvert M\rvert`$, then
$`M_{0,0} = 0`$.

### Proof

From $`0 \lt \lvert M\rvert`$ the sequence $`M`$ is non-empty, so it can be written as $`M = m_0 :: M'`$.
Then $`M\langle 0\rangle = m_0`$, and the head element of $`M`$ is likewise $`m_0`$.

The first conjunct of the definition of $`\mathrm{blockok}`$ (D.blockok) says that
if $`M \ne ()`$ then the first entry of the head element of $`M`$ equals $`0`$.
Since $`M = m_0 :: M' \ne ()`$, we obtain $`\pi_1(m_0) = 0`$.
By the definition of $`M_{i,j}`$ (D.entry), $`M_{0,0} = \pi_1(M\langle 0\rangle) = \pi_1(m_0) = 0`$. ∎

<a id="t-parent0_exists"></a>
## Theorem: existence of the parent in row 0 (T.parent0_exists)

### Theorem

If $`\mathrm{blockok}(0, M)`$, $`j \lt \lvert M\rvert`$, and $`0 \lt M_{0,j}`$, then there exists
$`k`$ with $`k \to^M_0 j`$.

### Proof

**Step 1: $`0 \lt j`$.**
If $`j = 0`$, then [T.blockok_head_zero](#t-blockok_head_zero) gives $`M_{0,0} = 0`$,
which contradicts the hypothesis $`0 \lt M_{0,j} = M_{0,0}`$.

**Step 2: take the largest candidate.** Define the predicate $`P`$ by

```math
P(k) :\equiv M_{0,k} \lt M_{0,j}
```

By [T.blockok_head_zero](#t-blockok_head_zero) we have $`M_{0,0} = 0`$, and by hypothesis
$`0 \lt M_{0,j}`$, so $`P(0)`$ holds.
The set

```math
S := \{\, k \mid k \le j - 1 \ \wedge\ P(k) \,\}
```

has $`0`$ as an element (by Step 1, $`0 \le j - 1`$) and is a finite set contained in
$`\{0, 1, \dots, j-1\}`$, hence has a largest element. Let $`k`$ be that element.
For $`k`$ the following three statements hold.

```math
\begin{aligned}
&(\mathrm{i})\ k \le j - 1, \cr
&(\mathrm{ii})\ M_{0,k} \lt M_{0,j}, \cr
&(\mathrm{iii})\ \forall l,\ \bigl(k \lt l \wedge l \le j - 1\bigr) \to \neg\,\bigl(M_{0,l} \lt M_{0,j}\bigr).
\end{aligned}
```

Here $`(\mathrm{i})`$ and $`(\mathrm{ii})`$ follow from $`k \in S`$, and $`(\mathrm{iii})`$ from
$`k`$ being the largest element of $`S`$.

**Step 3: verify the five conditions of $`k \to^M_0 j`$.**

- First condition $`k \lt \lvert M\rvert`$: by $`(\mathrm{i})`$ and Step 1 we have $`k \le j - 1 \lt j`$,
  which together with the hypothesis $`j \lt \lvert M\rvert`$ gives $`k \lt \lvert M\rvert`$.
- Second condition $`j \lt \lvert M\rvert`$: this is a hypothesis.
- Third condition $`k \lt j`$: by $`(\mathrm{i})`$ and Step 1, $`k \le j - 1 \lt j`$.
- Fourth condition $`M_{0,k} \lt M_{0,j}`$: this is $`(\mathrm{ii})`$.
- Fifth condition $`\forall l,\ (k \lt l \wedge l \lt j) \to M_{0,j} \le M_{0,l}`$:
  take $`l`$ with $`k \lt l`$ and $`l \lt j`$. From $`l \lt j`$ we get $`l \le j - 1`$, so
  $`(\mathrm{iii})`$ applies and yields $`\neg(M_{0,l} \lt M_{0,j})`$, that is,
  $`M_{0,j} \le M_{0,l}`$. ∎

<a id="t-chain_to_zero"></a>
## Theorem: chain to a column whose row 0 is 0 (T.chain_to_zero)

### Theorem

Let $`\mathrm{blockok}(0, M)`$. For all $`\mathrm{lev}, j \in \mathbb{N}`$, if
$`M_{0,j} = \mathrm{lev}`$ and $`j \lt \lvert M\rvert`$, then there exists $`r`$ with

```math
r \le j, \qquad M_{0,r} = 0, \qquad r \mathbin{(\to^M_0)^{*}} j .
```

### Proof

Strong induction on $`\mathrm{lev}`$. The induction predicate is

```math
\Phi(\mathrm{lev}) :\equiv \forall j,\ \bigl(M_{0,j} = \mathrm{lev} \wedge j \lt \lvert M\rvert\bigr)
  \to \exists r,\ \bigl(r \le j \wedge M_{0,r} = 0 \wedge r \mathbin{(\to^M_0)^{*}} j\bigr),
```

and assume that $`\Phi(\mathrm{lev}')`$ holds for every $`\mathrm{lev}'`$ with
$`\mathrm{lev}' \lt \mathrm{lev}`$. Take $`j`$ with $`M_{0,j} = \mathrm{lev}`$ and $`j \lt \lvert M\rvert`$,
and distinguish cases according to whether $`M_{0,j}`$ is $`0`$.

**(a) The case $`M_{0,j} = 0`$.** Take $`r := j`$. Then $`j \le j`$ and $`M_{0,j} = 0`$, and
$`j \mathbin{(\to^M_0)^{*}} j`$ is the chain of length $`0`$.

**(b) The case $`M_{0,j} \ne 0`$, that is, $`0 \lt M_{0,j}`$.**
Applying [T.parent0_exists](#t-parent0_exists) to $`\mathrm{blockok}(0,M)`$, $`j \lt \lvert M\rvert`$ and
$`0 \lt M_{0,j}`$, take $`k`$ with $`k \to^M_0 j`$.
By the first condition of the definition of $`\to^M_0`$ (D.nextrel0) we have $`k \lt \lvert M\rvert`$,
by the third condition $`k \lt j`$, and by the fourth condition

```math
M_{0,k} \lt M_{0,j} = \mathrm{lev}
```

Hence the induction hypothesis applies with $`\mathrm{lev}' := M_{0,k}`$, and using it at
$`j := k`$ (by $`M_{0,k} = M_{0,k}`$ and $`k \lt \lvert M\rvert`$) yields $`r`$ with

```math
r \le k, \qquad M_{0,r} = 0, \qquad r \mathbin{(\to^M_0)^{*}} k
```

Appending $`k \to^M_0 j`$ to the end of this chain gives $`r \mathbin{(\to^M_0)^{*}} j`$, and
from $`r \le k \lt j`$ we get $`r \le j`$. ∎

<a id="t-parent1_exists"></a>
## Theorem: existence of the parent in row 1 (T.parent1_exists)

### Theorem

If $`\mathrm{blockok}(0, M)`$, $`\mathrm{z0ok}(M)`$ ([D.z0ok](Column-3.md#d-z0ok)),
$`j \lt \lvert M\rvert`$, and $`0 \lt M_{1,j}`$, then there exists $`k`$ with $`k \to^M_1 j`$.

### Proof

**Step 1: take a chain to a root in row 0.**
Applying [T.chain_to_zero](#t-chain_to_zero) with $`\mathrm{lev} := M_{0,j}`$, take $`r`$ with

```math
r \le j, \qquad M_{0,r} = 0, \qquad r \mathbin{(\to^M_0)^{*}} j
```

Then $`r \le j \lt \lvert M\rvert`$.
Applying the definition of $`\mathrm{z0ok}(M)`$ (D.z0ok) to $`M_{0,r} = 0`$ gives $`M_{1,r} = 0`$.

**Step 2: $`r \lt j`$.**
We have $`r \le j`$. If $`r = j`$, then $`M_{1,j} = M_{1,r} = 0`$, contradicting the hypothesis
$`0 \lt M_{1,j}`$. Hence $`r \lt j`$.

**Step 3: take the largest candidate.** Define the predicate $`P`$ by

```math
P(k) :\equiv k \le^M_0 j \ \wedge\ M_{1,k} \lt M_{1,j}
```

Then $`P(r)`$ holds. Indeed, the three conditions of the definition of $`\le^M_0`$ (D.le0) are
$`r \lt \lvert M\rvert`$, $`j \lt \lvert M\rvert`$ and $`r \mathbin{(\to^M_0)^{*}} j`$, all of which were
obtained in Step 1, and moreover $`M_{1,r} = 0 \lt M_{1,j}`$.

The set

```math
S := \{\, k \mid k \le j - 1 \ \wedge\ P(k) \,\}
```

has $`r`$ as an element (by Step 2, $`r \le j - 1`$) and is a finite set contained in
$`\{0,1,\dots,j-1\}`$, hence has a largest element. Let $`k`$ be that element. For $`k`$

```math
\begin{aligned}
&(\mathrm{i})\ k \le j - 1, \cr
&(\mathrm{ii})\ k \le^M_0 j \ \wedge\ M_{1,k} \lt M_{1,j}, \cr
&(\mathrm{iii})\ \forall l,\ \bigl(k \lt l \wedge l \le j - 1\bigr) \to \neg\,P(l)
\end{aligned}
```

hold.

**Step 4: verify the six conditions of $`k \to^M_1 j`$.**

- First condition $`k \lt \lvert M\rvert`$: by $`(\mathrm{i})`$ and Step 2 we have $`k \le j - 1 \lt j`$,
  which may be combined with $`j \lt \lvert M\rvert`$.
- Second condition $`j \lt \lvert M\rvert`$: this is a hypothesis.
- Third condition $`k \lt j`$: by $`(\mathrm{i})`$ and Step 2.
- Fourth condition $`M_{1,k} \lt M_{1,j}`$: this is the second conjunct of $`(\mathrm{ii})`$.
- Fifth condition $`k \le^M_0 j`$: this is the first conjunct of $`(\mathrm{ii})`$.
- Sixth condition $`\forall j',\ (k \lt j' \wedge j' \le^M_0 j) \to M_{1,j} \le M_{1,j'}`$:
  take $`j'`$ with $`k \lt j'`$ and $`j' \le^M_0 j`$.
  By [T.le0_le](Column-3.md#t-le0_le) we have $`j' \le j`$.
  - The case $`j' = j`$. What is to be shown is $`M_{1,j} \le M_{1,j}`$, which holds by the reflexivity of $`\le`$.
  - The case $`j' \lt j`$. Negating $`M_{1,j} \le M_{1,j'}`$, suppose $`M_{1,j'} \lt M_{1,j}`$.
    Together with $`j' \le^M_0 j`$ this makes $`P(j')`$ hold.
    On the other hand, from $`k \lt j'`$ and $`j' \lt j`$ we get $`j' \le j - 1`$, so
    $`(\mathrm{iii})`$ yields $`\neg P(j')`$, a contradiction. ∎

<a id="t-nextR_one_iff"></a>
## Theorem: restatement of the parent relation in row 1 (T.nextR_one_iff)

### Theorem

The row-indexed parent relation $`\to^M_i`$ ([D.nextR](Pss.md#d-nextR)) with $`i := 1`$ substituted coincides
with the parent relation $`\to^M_1`$ of row $`1`$. That is, for $`i = 1`$ the statements $`k \to^M_i j`$ and
$`k \to^M_1 j`$ are equivalent.

### Proof

The definition of $`\to^M_i`$ (D.nextR) is a case distinction according to whether $`i = 0`$.
Since $`1 \ne 0`$, the second case is selected, and the two sides are the same proposition by definition. ∎

<a id="t-nextR_zero_iff"></a>
## Theorem: restatement of the parent relation in row 0 (T.nextR_zero_iff)

### Theorem

The row-indexed parent relation $`\to^M_i`$ with $`i := 0`$ substituted coincides with the parent
relation $`\to^M_0`$ of row $`0`$.

### Proof

In the case distinction of the definition of $`\to^M_i`$ (D.nextR) the condition $`i = 0`$ holds, so
the first case is selected, and the two sides are the same proposition by definition. ∎

<a id="t-hp_last"></a>
## Theorem: the last column has a parent (T.hp_last)

### Theorem

Put $`j_1 := \lvert M\rvert - 1`$. If $`\mathrm{blockok}(0, M)`$, $`\mathrm{z0ok}(M)`$,
$`0 \lt \lvert M\rvert`$ and $`M\langle j_1\rangle \ne (0,0)`$, then

```math
\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M, j_1),\ j_1\bigr).
```

($`\mathrm{hasParent}`$ [D.hasParent](Pss.md#d-hasParent), $`\mathrm{idx}_1`$ [D.idx1](Pss.md#d-idx1))

### Proof

From $`0 \lt \lvert M\rvert`$ we get $`j_1 = \lvert M\rvert - 1 \lt \lvert M\rvert`$.
Distinguish cases according to whether $`M_{1,j_1}`$ is positive.

**(a) The case $`0 \lt M_{1,j_1}`$.**
The first case of the definition of $`\mathrm{idx}_1`$ (D.idx1) is selected, so $`\mathrm{idx}_1(M,j_1) = 1`$.
Applying [T.parent1_exists](#t-parent1_exists) to $`\mathrm{blockok}(0,M)`$, $`\mathrm{z0ok}(M)`$,
$`j_1 \lt \lvert M\rvert`$ and $`0 \lt M_{1,j_1}`$, take $`k`$ with $`k \to^M_1 j_1`$.

The definition of $`\mathrm{hasParent}`$ (D.hasParent) is the conjunction of existence and uniqueness.

- Existence: since $`\mathrm{idx}_1(M,j_1) = 1`$, what is to be shown is $`k \to^M_i j_1`$ in the
  case $`i = 1`$. By [T.nextR_one_iff](#t-nextR_one_iff) this is equivalent to
  $`k \to^M_1 j_1`$, and the latter was obtained above.
- Uniqueness: if $`y`$ satisfies $`y \to^M_i j_1`$ in the case $`i = 1`$, then again by
  [T.nextR_one_iff](#t-nextR_one_iff) we have $`y \to^M_1 j_1`$.
  Applying [T.nextrel1_unique](#t-nextrel1_unique) to $`y \to^M_1 j_1`$ and $`k \to^M_1 j_1`$
  gives $`y = k`$.

**(b) The case $`M_{1,j_1} = 0`$.**
First we show $`0 \lt M_{0,j_1}`$. If $`M_{0,j_1} = 0`$, then by the definition of
$`M_{i,j}`$ (D.entry) we have $`\pi_1(M\langle j_1\rangle) = M_{0,j_1} = 0`$ and
$`\pi_2(M\langle j_1\rangle) = M_{1,j_1} = 0`$, so that
$`M\langle j_1\rangle = (0,0)`$, contradicting the hypothesis $`M\langle j_1\rangle \ne (0,0)`$.

The condition $`0 \lt M_{1,j_1}`$ in the definition of $`\mathrm{idx}_1`$ (D.idx1) is false, so
$`\mathrm{idx}_1(M,j_1) = 0`$.
Applying [T.parent0_exists](#t-parent0_exists) to $`\mathrm{blockok}(0,M)`$,
$`j_1 \lt \lvert M\rvert`$ and $`0 \lt M_{0,j_1}`$, take $`k`$ with $`k \to^M_0 j_1`$.

We verify the two parts of the definition of $`\mathrm{hasParent}`$ (D.hasParent).

- Existence: since $`\mathrm{idx}_1(M,j_1) = 0`$, what is to be shown is $`k \to^M_i j_1`$ in the
  case $`i = 0`$. By [T.nextR_zero_iff](#t-nextR_zero_iff) this is equivalent to
  $`k \to^M_0 j_1`$, and the latter was obtained above.
- Uniqueness: if $`y`$ satisfies $`y \to^M_i j_1`$ in the case $`i = 0`$, then again by
  [T.nextR_zero_iff](#t-nextR_zero_iff) we have $`y \to^M_0 j_1`$.
  Applying [T.nextrel0_unique](#t-nextrel0_unique) to $`y \to^M_0 j_1`$ and $`k \to^M_0 j_1`$
  gives $`y = k`$. ∎

<a id="t-z0ok_oper"></a>
## Theorem: expansion preserves $`\mathrm{z0ok}`$ (T.z0ok_oper)

### Theorem

If $`1 \le n`$ and $`\mathrm{z0ok}(M)`$, then $`\mathrm{z0ok}(M[n])`$ ($`M[n]`$ [D.oper](Pss.md#d-oper)).

### Proof

Put $`j_1 := \lvert M\rvert - 1`$ and $`i_1 := \mathrm{idx}_1(M, j_1)`$, and distinguish cases
along the branches of the definition of $`M[n]`$ (D.oper).

**(a) The case $`j_1 = 0`$.**
By [T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) we have $`M[n] = M`$, and
the conclusion is exactly the hypothesis $`\mathrm{z0ok}(M)`$.

**(b) The case $`j_1 \ne 0`$ and $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$.**
By [T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) we have
$`M[n] = \mathrm{Pred}\,M`$ ([D.Pred](Pss.md#d-Pred)), and we apply [T.z0ok_Pred](Column-3.md#t-z0ok_Pred).

**(c) The case $`j_1 \ne 0`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$.**
By [T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) we have
$`M[n] = \mathrm{Pred}\,M`$, and we apply [T.z0ok_Pred](Column-3.md#t-z0ok_Pred).

**(d) The case $`j_1 \ne 0`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and
$`\mathrm{hasParent}(M, i_1, j_1)`$.**
We have $`1 \lt \lvert M\rvert`$. Indeed, if $`\lvert M\rvert \le 1`$, then since subtraction of
natural numbers is truncated at $`0`$, we get $`j_1 = \lvert M\rvert - 1 = 0`$, contradicting the
hypothesis $`j_1 \ne 0`$ of this case.
Applying [T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) to
$`1 \lt \lvert M\rvert`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$,
$`\mathrm{hasParent}(M, i_1, j_1)`$ and $`1 \le n`$, take
$`G, v_0, w_0, R, d_0, \ell`$. Its (1) and (2) read

```math
M = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} (\ell),
```
```math
M[n] = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+0\cdot d_0}
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+(n-1)d_0}
```

($`L^{+e}`$ [D.copyExp](Column-2.md#d-copyExp)).
By the definition of $`\mathrm{copyExp}`$ (D.copyExp), the right-hand side of the latter can be written as

```math
M[n] = \mathrm{copyExp}\bigl(G,\ (v_0,w_0) :: R,\ d_0,\ n\bigr)
```

Rewriting the hypothesis $`\mathrm{z0ok}(M)`$ by (1) gives
$`\mathrm{z0ok}\bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr)`$, so applying
[T.z0ok_copyExp](Column-3.md#t-z0ok_copyExp) with $`B := (v_0,w_0) :: R`$ yields the conclusion. ∎

<a id="t-z0ok_ST_PS"></a>
## Theorem: standard forms satisfy $`\mathrm{z0ok}`$ (T.z0ok_ST_PS)

### Theorem

If $`M \in \mathrm{ST\_PS}`$ ([D.ST_PS](Pss.md#d-ST_PS)), then $`\mathrm{z0ok}(M)`$.

### Proof

Induction on the derivation of $`\mathrm{ST\_PS}`$. The induction predicate is

```math
\Phi(M) :\equiv \mathrm{z0ok}(M).
```

- **Base case** (rule (diag)): here $`M = \Delta_0^v`$ ([D.diagSeq](Pss.md#d-diagSeq)).
  [T.z0ok_diagSeq](Column-3.md#t-z0ok_diagSeq) is exactly $`\Phi(\Delta_0^v)`$.

- **Inductive step** (rule (oper)): let $`N \in \mathrm{ST\_PS}`$ and $`1 \le n`$; the induction
  hypothesis is $`\Phi(N)`$, that is, $`\mathrm{z0ok}(N)`$.
  Applying [T.z0ok_oper](#t-z0ok_oper) to $`1 \le n`$ and $`\mathrm{z0ok}(N)`$ gives
  $`\mathrm{z0ok}(N[n])`$, that is, $`\Phi(N[n])`$. ∎

<a id="t-rtg_through_pivot"></a>
## Theorem: a chain in row 0 passes through the pivot (T.rtg_through_pivot)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) and $`\rho \in \mathbb{N}`$.
For all $`a, b \in \mathbb{N}`$, if

```math
a \mathbin{(\to^M_0)^{*}} b, \qquad a \lt \rho, \qquad \rho \le b, \qquad
\forall y,\ \bigl(\rho \lt y \wedge y \le b\bigr) \to M_{0,\rho} \lt M_{0,y}
```

then $`\rho \mathbin{(\to^M_0)^{*}} b`$.

### Proof

Fix $`a`$ and argue by induction on the construction of the chain $`a \mathbin{(\to^M_0)^{*}} b`$.
The induction predicate is

```math
\Phi(b) :\equiv \Bigl(a \lt \rho \wedge \rho \le b \wedge
  \forall y,\ (\rho \lt y \wedge y \le b) \to M_{0,\rho} \lt M_{0,y}\Bigr)
  \to \rho \mathbin{(\to^M_0)^{*}} b .
```

- **Base case** ($`b = a`$, chain of length $`0`$): the first conjunct of the antecedent is
  $`a \lt \rho`$ and the second is $`\rho \le a`$; together they give $`a \lt a`$, which
  contradicts the irreflexivity of $`\lt`$. Hence the antecedent is false and $`\Phi(a)`$ holds.

**Inductive step** (from $`a \mathbin{(\to^M_0)^{*}} y`$ and $`y \to^M_0 z`$ to
$`a \mathbin{(\to^M_0)^{*}} z`$): assume $`\Phi(y)`$.
Assume $`a \lt \rho`$, $`\rho \le z`$ and

```math
(\ast)\qquad \forall y',\ \bigl(\rho \lt y' \wedge y' \le z\bigr) \to M_{0,\rho} \lt M_{0,y'}
```

and show $`\rho \mathbin{(\to^M_0)^{*}} z`$. Distinguish cases by the order between $`\rho`$ and $`y`$.

**(a) The case $`\rho \le y`$.**
By [T.nextrel0_lt](Column.md#t-nextrel0_lt) we have $`y \lt z`$. Hence any $`y'`$ with
$`\rho \lt y' \wedge y' \le y`$ satisfies $`y' \le y \le z`$, so
$`(\ast)`$ gives $`M_{0,\rho} \lt M_{0,y'}`$. That is, all three conjuncts of the antecedent of the
induction hypothesis $`\Phi(y)`$ hold. We therefore obtain $`\rho \mathbin{(\to^M_0)^{*}} y`$.
Appending $`y \to^M_0 z`$ to the end of this chain gives $`\rho \mathbin{(\to^M_0)^{*}} z`$.

**(b) The case $`y \lt \rho`$.** Distinguish further cases on $`\rho`$ and $`z`$ (we have $`\rho \le z`$).

**(b-1) The case $`\rho = z`$.** Then $`\rho \mathbin{(\to^M_0)^{*}} z`$ is the chain of length $`0`$.

**(b-2) The case $`\rho \lt z`$.** Substituting $`\rho`$ for the universally quantified variable in the
fifth condition of $`y \to^M_0 z`$, that is, of the definition of $`\to^M_0`$ (D.nextrel0), its
antecedent $`y \lt \rho \wedge \rho \lt z`$ holds, so

```math
M_{0,z} \le M_{0,\rho}
```

On the other hand, applying $`(\ast)`$ with $`y' := z`$ (using $`\rho \lt z`$ and $`z \le z`$) gives
$`M_{0,\rho} \lt M_{0,z}`$. The two together give $`M_{0,z} \lt M_{0,z}`$, contradicting the
irreflexivity of $`\lt`$. Hence this case does not occur. ∎

<a id="t-le0_through_pivot"></a>
## Theorem: the ancestor relation in row 0 passes through the pivot (T.le0_through_pivot)

### Theorem

If $`a \le^M_0 b`$, $`a \lt \rho`$, $`\rho \le b`$ and

```math
\forall y,\ \bigl(\rho \lt y \wedge y \le b\bigr) \to M_{0,\rho} \lt M_{0,y}
```

then $`\rho \le^M_0 b`$.

### Proof

We verify the three conditions of the definition of $`\le^M_0`$ (D.le0). From the hypothesis
$`a \le^M_0 b`$ we obtain $`a \lt \lvert M\rvert`$, $`b \lt \lvert M\rvert`$ and $`a \mathbin{(\to^M_0)^{*}} b`$.

- First condition $`\rho \lt \lvert M\rvert`$: by $`\rho \le b`$ and $`b \lt \lvert M\rvert`$.
- Second condition $`b \lt \lvert M\rvert`$: as stated above.
- Third condition $`\rho \mathbin{(\to^M_0)^{*}} b`$:
  apply [T.rtg_through_pivot](#t-rtg_through_pivot) to $`a \mathbin{(\to^M_0)^{*}} b`$,
  $`a \lt \rho`$, $`\rho \le b`$ and the last hypothesis. ∎

<a id="t-entry_shift"></a>
## Theorem: entries of a shifted sequence (T.entry_shift)

### Theorem

Let $`S \in \mathrm{PairSeq}`$ and $`d, j \in \mathbb{N}`$. If $`j \lt \lvert S\rvert`$, then

```math
(S^{+d})_{0,j} = S_{0,j} + d
\qquad\text{and}\qquad
(S^{+d})_{1,j} = S_{1,j} .
```

### Proof

By the definition of $`L^{+e}`$ (D.copyExp), $`S^{+d}`$ is obtained by mapping each element of $`S`$, so
$`\lvert S^{+d}\rvert = \lvert S\rvert`$, and by the hypothesis $`j \lt \lvert S\rvert`$ the
$`j`$-th element exists in both sequences.
By [T.getD_eq_getElem'](Cnf.md#t-getD_eq_getElem') we have

```math
S\langle j\rangle = S_j, \qquad S^{+d}\langle j\rangle = (S^{+d})_j = \bigl(\pi_1(S_j) + d,\ \pi_2(S_j)\bigr)
```

The definition of $`M_{i,j}`$ (D.entry) reads the first entry when $`i = 0`$ and the second entry when
$`i \ne 0`$, hence

```math
(S^{+d})_{0,j} = \pi_1(S_j) + d = S_{0,j} + d,
\qquad
(S^{+d})_{1,j} = \pi_2(S_j) = S_{1,j} . \qquad \blacksquare
```

<a id="t-nextrel0_shift_iff"></a>
## Theorem: shift invariance of the parent relation in row 0 (T.nextrel0_shift_iff)

### Theorem

If $`b \lt \lvert S\rvert`$, then

```math
a \to^{S^{+d}}_0 b \iff a \to^{S}_0 b .
```

### Proof

Since $`\lvert S^{+d}\rvert = \lvert S\rvert`$, the first, second and third conditions of the
definition of $`\to^M_0`$ (D.nextrel0) are the same propositions on both sides. We transfer the
fourth and fifth conditions in both directions.

**(Left to right)** Assume $`a \to^{S^{+d}}_0 b`$. By the first condition, $`a \lt \lvert S\rvert`$.
The fourth and fifth conditions to be shown are as follows.

- Fourth condition: the fourth condition of the hypothesis is $`(S^{+d})_{0,a} \lt (S^{+d})_{0,b}`$.
  Applying [T.entry_shift](#t-entry_shift) with $`j := a`$ and $`j := b`$ turns this into
  $`S_{0,a} + d \lt S_{0,b} + d`$, and the strict monotonicity of addition on $`\mathbb{N}`$ gives
  $`S_{0,a} \lt S_{0,b}`$.

- Fifth condition: take $`l`$ with $`a \lt l`$ and $`l \lt b`$. Since $`l \lt b \lt \lvert S\rvert`$,
  [T.entry_shift](#t-entry_shift) applies with $`j := l`$ and $`j := b`$, so that the fifth condition
  of the hypothesis, $`(S^{+d})_{0,b} \le (S^{+d})_{0,l}`$, is the same as
  $`S_{0,b} + d \le S_{0,l} + d`$, that is, $`S_{0,b} \le S_{0,l}`$.

**(Right to left)** Assume $`a \to^{S}_0 b`$. By the first condition, $`a \lt \lvert S\rvert`$.

- Fourth condition: adding $`d`$ to both sides of the fourth condition of the hypothesis,
  $`S_{0,a} \lt S_{0,b}`$, gives $`S_{0,a} + d \lt S_{0,b} + d`$, which by
  [T.entry_shift](#t-entry_shift) is $`(S^{+d})_{0,a} \lt (S^{+d})_{0,b}`$.

- Fifth condition: take $`l`$ with $`a \lt l`$ and $`l \lt b`$. Since $`l \lt \lvert S\rvert`$,
  [T.entry_shift](#t-entry_shift) applies, and adding $`d`$ to both sides of the fifth condition of
  the hypothesis, $`S_{0,b} \le S_{0,l}`$, gives
  $`(S^{+d})_{0,b} \le (S^{+d})_{0,l}`$. ∎

<a id="t-rtg_shift_of"></a>
## Theorem: a chain in the shifted sequence is a chain in the original sequence (T.rtg_shift_of)

### Theorem

If $`a \mathbin{(\to^{S^{+d}}_0)^{*}} b`$, then $`a \mathbin{(\to^{S}_0)^{*}} b`$.

### Proof

Induction on the construction of the chain $`a \mathbin{(\to^{S^{+d}}_0)^{*}} b`$.
The induction predicate is

```math
\Phi(b) :\equiv a \mathbin{(\to^{S}_0)^{*}} b .
```

- **Base case** ($`b = a`$, chain of length $`0`$): $`a \mathbin{(\to^{S}_0)^{*}} a`$ is the
  chain of length $`0`$.

- **Inductive step** (from $`a \mathbin{(\to^{S^{+d}}_0)^{*}} c`$ and $`c \to^{S^{+d}}_0 e`$):
  assume $`\Phi(c)`$, that is, $`a \mathbin{(\to^{S}_0)^{*}} c`$.
  Applying [T.nextrel0_bound](Column-3.md#t-nextrel0_bound) to $`c \to^{S^{+d}}_0 e`$ gives
  $`e \lt \lvert S^{+d}\rvert = \lvert S\rvert`$.
  Hence [T.nextrel0_shift_iff](#t-nextrel0_shift_iff) applies and yields $`c \to^{S}_0 e`$.
  Appending this one step to the end of the chain of the induction hypothesis gives
  $`a \mathbin{(\to^{S}_0)^{*}} e`$, that is, $`\Phi(e)`$. ∎

<a id="t-rtg_shift_to"></a>
## Theorem: a chain in the original sequence is a chain in the shifted sequence (T.rtg_shift_to)

### Theorem

If $`a \mathbin{(\to^{S}_0)^{*}} b`$, then $`a \mathbin{(\to^{S^{+d}}_0)^{*}} b`$.

### Proof

Induction on the construction of the chain $`a \mathbin{(\to^{S}_0)^{*}} b`$. The induction predicate is

```math
\Phi(b) :\equiv a \mathbin{(\to^{S^{+d}}_0)^{*}} b .
```

- **Base case** ($`b = a`$, chain of length $`0`$): $`a \mathbin{(\to^{S^{+d}}_0)^{*}} a`$ is the
  chain of length $`0`$.

- **Inductive step** (from $`a \mathbin{(\to^{S}_0)^{*}} c`$ and $`c \to^{S}_0 e`$):
  assume $`\Phi(c)`$, that is, $`a \mathbin{(\to^{S^{+d}}_0)^{*}} c`$.
  Applying [T.nextrel0_bound](Column-3.md#t-nextrel0_bound) to $`c \to^{S}_0 e`$ gives
  $`e \lt \lvert S\rvert`$. Hence
  [T.nextrel0_shift_iff](#t-nextrel0_shift_iff) applies and yields $`c \to^{S^{+d}}_0 e`$.
  Appending this one step to the end of the chain of the induction hypothesis gives
  $`a \mathbin{(\to^{S^{+d}}_0)^{*}} e`$, that is, $`\Phi(e)`$. ∎

<a id="t-le0_shift_iff"></a>
## Theorem: shift invariance of the ancestor relation in row 0 (T.le0_shift_iff)

### Theorem

```math
a \le^{S^{+d}}_0 b \iff a \le^{S}_0 b .
```

### Proof

Since $`\lvert S^{+d}\rvert = \lvert S\rvert`$, the first and second conditions of the definition of
$`\le^M_0`$ (D.le0) are the same propositions on both sides. As for the third condition,
left to right is [T.rtg_shift_of](#t-rtg_shift_of) and
right to left is [T.rtg_shift_to](#t-rtg_shift_to). ∎

<a id="t-idx1_shift"></a>
## Theorem: shift invariance of the search row (T.idx1_shift)

### Theorem

```math
\mathrm{idx}_1(S^{+d}, j) = \mathrm{idx}_1(S, j) .
```

### Proof

The value of the definition of $`\mathrm{idx}_1`$ (D.idx1) is determined solely by the truth value of
$`0 \lt M_{1,j}`$, so it suffices to show $`(S^{+d})_{1,j} = S_{1,j}`$.
Distinguish cases by the order between $`j`$ and $`\lvert S\rvert`$.

**(a) The case $`j \lt \lvert S\rvert`$.**
This is exactly the second equation of [T.entry_shift](#t-entry_shift).

**(b) The case $`\lvert S\rvert \le j`$.**
Since $`\lvert S^{+d}\rvert = \lvert S\rvert \le j`$, the definition of
$`M\langle j\rangle`$ (D.entry) gives
$`S\langle j\rangle = (0,0)`$ and $`S^{+d}\langle j\rangle = (0,0)`$.
Hence $`(S^{+d})_{1,j} = \pi_2\bigl((0,0)\bigr) = 0 = S_{1,j}`$. ∎

<a id="t-nextrel1_shift_iff"></a>
## Theorem: shift invariance of the parent relation in row 1 (T.nextrel1_shift_iff)

### Theorem

If $`b \lt \lvert S\rvert`$, then

```math
a \to^{S^{+d}}_1 b \iff a \to^{S}_1 b .
```

### Proof

Since $`\lvert S^{+d}\rvert = \lvert S\rvert`$, the first, second and third conditions of the
definition of $`\to^M_1`$ (D.nextrel1) are the same propositions on both sides. The fifth condition
is equivalent on both sides by [T.le0_shift_iff](#t-le0_shift_iff). We transfer the remaining
fourth and sixth conditions in both directions.

**(Left to right)** Assume $`a \to^{S^{+d}}_1 b`$. By the first condition,
$`a \lt \lvert S\rvert`$.

- Fourth condition: the fourth condition of the hypothesis is $`(S^{+d})_{1,a} \lt (S^{+d})_{1,b}`$.
  Applying [T.entry_shift](#t-entry_shift) with $`j := a`$ and $`j := b`$, its second equation
  turns this into $`S_{1,a} \lt S_{1,b}`$.

- Sixth condition: take $`l`$ with $`a \lt l`$ and $`l \le^{S}_0 b`$.
  By [T.le0_shift_iff](#t-le0_shift_iff) we have $`l \le^{S^{+d}}_0 b`$, so substituting $`l`$ for
  the universally quantified variable in the sixth condition of the hypothesis gives
  $`(S^{+d})_{1,b} \le (S^{+d})_{1,l}`$.
  By [T.le0_le](Column-3.md#t-le0_le) we have $`l \le b \lt \lvert S\rvert`$, so
  [T.entry_shift](#t-entry_shift) applies with $`j := l`$ and $`j := b`$, and
  this inequality is the same as $`S_{1,b} \le S_{1,l}`$.

**(Right to left)** Assume $`a \to^{S}_1 b`$. By the first condition, $`a \lt \lvert S\rvert`$.

- Fourth condition: applying the second equation of [T.entry_shift](#t-entry_shift) with $`j := a`$
  and $`j := b`$ to the fourth condition of the hypothesis, $`S_{1,a} \lt S_{1,b}`$, gives
  $`(S^{+d})_{1,a} \lt (S^{+d})_{1,b}`$.

- Sixth condition: take $`l`$ with $`a \lt l`$ and $`l \le^{S^{+d}}_0 b`$.
  By [T.le0_shift_iff](#t-le0_shift_iff) we have $`l \le^{S}_0 b`$, and by
  [T.le0_le](Column-3.md#t-le0_le) we have $`l \le b \lt \lvert S\rvert`$.
  Substituting $`l`$ for the universally quantified variable in the sixth condition of the
  hypothesis gives $`S_{1,b} \le S_{1,l}`$.
  Here [T.entry_shift](#t-entry_shift) applies with $`j := l`$ and $`j := b`$, and
  this inequality is the same as $`(S^{+d})_{1,b} \le (S^{+d})_{1,l}`$. ∎
