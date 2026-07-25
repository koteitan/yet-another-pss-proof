[← README](README.md) | [English](Decrease.md) | [Japanese](Decrease-ja.md)

Throughout, for $`M \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) we write
$`j_1 := \lvert M\rvert - 1`$ and $`i_1 := \mathrm{idx}_1(M, j_1)`$ ([D.idx1](Pss.md#d-idx1)).

<a id="t-oper_eq_self_of_short"></a>
## Theorem: expansion is the identity on short sequences (T.oper_eq_self_of_short)

### Theorem

If $`j_1 = 0`$, then $`M[n] = M`$ ([D.oper](Pss.md#d-oper)) for every $`n`$.

### Proof

The condition of branch (a) in the definition of $`M[n]`$ (D.oper) is exactly the hypothesis. ∎

<a id="t-oper_eq_pred_of_zero"></a>
## Theorem: expansion when the last column is $`(0,0)`$ (T.oper_eq_pred_of_zero)

### Theorem

If $`j_1 \ne 0`$ and $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ ([D.entry](Pss.md#d-entry)), then
$`M[n] = \mathrm{Pred}\,M`$ ([D.Pred](Pss.md#d-Pred)) for every $`n`$.

### Proof

The condition of branch (a) in the definition of $`M[n]`$ (D.oper) is $`j_1 = 0`$, which is false
by hypothesis. The condition of branch (b) is exactly the second conjunct of the hypothesis, so
branch (b) is taken. ∎

<a id="t-oper_eq_pred_of_noParent"></a>
## Theorem: expansion when there is no parent (T.oper_eq_pred_of_noParent)

### Theorem

If $`j_1 \ne 0`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ ([D.hasParent](Pss.md#d-hasParent)), then
$`M[n] = \mathrm{Pred}\,M`$ for every $`n`$.

### Proof

The conditions of branches (a) and (b) in the definition of $`M[n]`$ (D.oper) are both false by
hypothesis. The condition of branch (c) is exactly the third conjunct of the hypothesis, so
branch (c) is taken. ∎

<a id="t-oper_bad_unfold"></a>
## Theorem: unfolded form of the fourth branch of expansion (T.oper_bad_unfold)

### Theorem

Suppose $`j_1 \ne 0`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and
$`\mathrm{hasParent}(M, i_1, j_1)`$. Put $`j_0 := \mathrm{par}^M_{i_1}(j_1)`$
([D.parent](Pss.md#d-parent)) and

```math
d_0 := \begin{cases} M_{0,j_1} - M_{0,j_0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
```

Then for every $`n`$

```math
M[n] = (M_0, \dots, M_{j_0-1}) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1} .
```

That is, **no term depending on $`k`$ occurs in the second entry of $`B_k`$**.

### Proof

The conditions of branches (a), (b), (c) in the definition of $`M[n]`$ (D.oper) are all false by
hypothesis, so branch (d) is taken. In that definition the second entry of $`B_k`$ is
$`M_{1,j} + k\,d_1`$, where

```math
d_1 = \begin{cases} M_{1,j_1} - M_{1,j_0} & (1 \lt i_1) \cr 0 & (i_1 \le 1) \end{cases}
```

By [T.idx1_le1](Term.md#t-idx1_le1) we have $`i_1 \le 1`$, so the condition $`1 \lt i_1`$ is false
and $`d_1 = 0`$. Hence the second entry is $`M_{1,j} + k\cdot 0 = M_{1,j}`$. ∎

<a id="t-oper_eq_self_short"></a>
## Theorem: expansion is the identity for length at most 1 (T.oper_eq_self_short)

### Theorem

If $`\lvert M\rvert \le 1`$, then $`M[n] = M`$ for every $`n`$.

### Proof

Subtraction on the natural numbers is truncated subtraction, so $`\lvert M\rvert \le 1`$ gives
$`j_1 = \lvert M\rvert - 1 = 0`$.
Apply [T.oper_eq_self_of_short](#t-oper_eq_self_of_short). ∎

<a id="t-translate_snoc_increase"></a>
## Theorem: appending one column at the end strictly increases the translation (T.translate_snoc_increase)

### Theorem

For all $`C \in \mathrm{PairSeq}`$ and $`m \in \mathbb{N}\times\mathbb{N}`$,

```math
\mathrm{tr}\,C \prec \mathrm{tr}\,(C \mathbin{+\!\!+} (m)) .
```

($`\mathrm{tr}`$ [D.translate](Term.md#d-translate), $`\prec`$ [D.olt](Term.md#d-olt))

### Proof

Induction along the recursion of $`\mathrm{tr}`$ ($`m`$ is not fixed: the induction predicate is
universally quantified over $`m`$). The induction predicate is

```math
\Psi(C) :\equiv \forall m,\ \mathrm{tr}\,C \prec \mathrm{tr}\,(C \mathbin{+\!\!+} (m)) .
```

- **Base case** $`C = ()`$: the left-hand side is $`\mathsf{Z}`$ ([D.Three](Term.md#d-Three)) and the right-hand side is $`\mathrm{tr}\,(m)`$.
  By the definition of $`\mathrm{tr}`$ (D.translate) we have $`\mathrm{tr}\,(m) = \mathsf{P}(m_2, \mathsf{Z}, \mathsf{Z})`$,
  so [T.olt_Z_P](Term.md#t-olt_Z_P) gives $`\mathsf{Z} \prec \mathrm{tr}\,(m)`$.

**Inductive step** $`C = p :: L`$: the induction hypotheses are $`\Psi(\mathrm{tw}_{p_1} L)`$ and
$`\Psi(\mathrm{dw}_{p_1} L)`$. We distinguish cases according to whether every element of $`L`$
satisfies $`p_1 \lt x_1`$.

**(a) Every element of $`L`$ satisfies $`p_1 \lt x_1`$.**
Then $`\mathrm{tw}_{p_1} L = L`$ and $`\mathrm{dw}_{p_1} L = ()`$, and
[T.translate_single_tree](Term.md#t-translate_single_tree) gives
$`\mathrm{tr}(p :: L) = \mathsf{P}(p_2, \mathrm{tr}\,L, \mathsf{Z})`$.
We distinguish further according to whether $`m`$ satisfies the predicate.

**Case $`p_1 \lt m_1`$.** Every element of $`L \mathbin{+\!\!+} (m)`$ also satisfies $`p_1 \lt x_1`$,
so [T.translate_single_tree](Term.md#t-translate_single_tree) again gives

```math
\mathrm{tr}\bigl(p :: (L \mathbin{+\!\!+} (m))\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}(L \mathbin{+\!\!+} (m)),\ \mathsf{Z}\bigr).
```

Applying the induction hypothesis $`\Psi(\mathrm{tw}_{p_1} L) = \Psi(L)`$ to $`m`$ yields
$`\mathrm{tr}\,L \prec \mathrm{tr}(L \mathbin{+\!\!+} (m))`$.
It suffices to apply [T.olt_P_b](Term.md#t-olt_P_b) to this.

**Case $`\neg(p_1 \lt m_1)`$.** By [T.takeWhile_append_all](Term.md#t-takeWhile_append_all) and
[T.dropWhile_append_all](Term.md#t-dropWhile_append_all) we have
$`\mathrm{tw}_{p_1}(L \mathbin{+\!\!+} (m)) = L`$ and $`\mathrm{dw}_{p_1}(L \mathbin{+\!\!+} (m)) = (m)`$,
so the definition of $`\mathrm{tr}`$ (D.translate) gives

```math
\mathrm{tr}\bigl(p :: (L \mathbin{+\!\!+} (m))\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}\,L,\ \mathrm{tr}\,(m)\bigr).
```

The successor sum on the left-hand side is $`\mathsf{Z}`$, the successor sum on the right-hand side
is $`\mathrm{tr}\,(m) = \mathsf{P}(m_2,\mathsf{Z},\mathsf{Z})`$,
and [T.olt_Z_P](Term.md#t-olt_Z_P) gives $`\mathsf{Z} \prec \mathrm{tr}\,(m)`$.
It suffices to apply [T.olt_P_c](Term.md#t-olt_P_c) to this.

**(b) Some element $`x`$ of $`L`$ satisfies $`\neg(p_1 \lt x_1)`$.**
By [T.takeWhile_append_not](Term.md#t-takeWhile_append_not) and
[T.dropWhile_append_not](Term.md#t-dropWhile_append_not) we have

```math
\mathrm{tw}_{p_1}(L \mathbin{+\!\!+} (m)) = \mathrm{tw}_{p_1} L,
\qquad
\mathrm{dw}_{p_1}(L \mathbin{+\!\!+} (m)) = \mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m)
```

so, by the definition of $`\mathrm{tr}`$ (D.translate), the two sides are

```math
\mathrm{tr}(p :: L) = \mathsf{P}\bigl(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\ \mathrm{tr}(\mathrm{dw}_{p_1} L)\bigr),
```
```math
\mathrm{tr}\bigl(p :: (L \mathbin{+\!\!+} (m))\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\ \mathrm{tr}(\mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m))\bigr)
```

and the subscript and the argument are common to both. Applying the induction hypothesis
$`\Psi(\mathrm{dw}_{p_1} L)`$ to $`m`$ yields
$`\mathrm{tr}(\mathrm{dw}_{p_1} L) \prec \mathrm{tr}(\mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m))`$.
It suffices to apply [T.olt_P_c](Term.md#t-olt_P_c) to this. ∎

<a id="t-translate_dropLast_decrease"></a>
## Theorem: dropping the last column strictly decreases the translation (T.translate_dropLast_decrease)

### Theorem

If $`C \ne ()`$, then $`\mathrm{tr}\,(\mathrm{dropLast}\,C) \prec \mathrm{tr}\,C`$.
Here $`\mathrm{dropLast}\,C`$ is the sequence obtained from $`C`$ by dropping its last element.

### Proof

Since $`C \ne ()`$, writing $`\ell`$ for the last element of $`C`$ we have

```math
C = \mathrm{dropLast}\,C \mathbin{+\!\!+} (\ell)
```

Applying [T.translate_snoc_increase](#t-translate_snoc_increase) with
$`C := \mathrm{dropLast}\,C`$ and $`m := \ell`$ gives

```math
\mathrm{tr}(\mathrm{dropLast}\,C) \prec \mathrm{tr}\bigl(\mathrm{dropLast}\,C \mathbin{+\!\!+} (\ell)\bigr)
= \mathrm{tr}\,C . \qquad \blacksquare
```

<a id="t-translate_takeWhile_snoc_le"></a>
## Theorem: the leading block does not decrease under appending at the end (T.translate_takeWhile_snoc_le)

### Theorem

For $`a \in \mathbb{N}`$, $`C \in \mathrm{PairSeq}`$ and $`m \in \mathbb{N}\times\mathbb{N}`$,

```math
\mathrm{tr}\bigl(\mathrm{tw}_a C\bigr) \preceq \mathrm{tr}\bigl(\mathrm{tw}_a (C \mathbin{+\!\!+} (m))\bigr)
```

($`\preceq`$ [D.ole](Term.md#d-ole)).

### Proof

We distinguish cases according to whether every element of $`C`$ satisfies $`a \lt x_1`$.

**(a) Every element satisfies it.** Then $`\mathrm{tw}_a C = C`$. We distinguish cases on $`m`$.

- Case $`a \lt m_1`$. Every element of $`C \mathbin{+\!\!+} (m)`$ also satisfies the predicate, so
  $`\mathrm{tw}_a(C \mathbin{+\!\!+} (m)) = C \mathbin{+\!\!+} (m)`$.
  By [T.translate_snoc_increase](#t-translate_snoc_increase),
  $`\mathrm{tr}\,C \prec \mathrm{tr}(C \mathbin{+\!\!+} (m))`$, so the first disjunct of the definition
  of $`\preceq`$ (D.ole) holds.

- Case $`\neg(a \lt m_1)`$. By [T.takeWhile_append_all](Term.md#t-takeWhile_append_all),
  $`\mathrm{tw}_a(C \mathbin{+\!\!+} (m)) = C \mathbin{+\!\!+} \mathrm{tw}_a\,(m) = C`$
  (since $`m`$ violates the predicate, $`\mathrm{tw}_a\,(m) = ()`$). Hence the two sides are the
  same term, and the second disjunct of the definition of $`\preceq`$ (D.ole) holds.

**(b) Some element $`x`$ satisfies $`\neg(a \lt x_1)`$.**
By [T.takeWhile_append_not](Term.md#t-takeWhile_append_not),
$`\mathrm{tw}_a(C \mathbin{+\!\!+} (m)) = \mathrm{tw}_a C`$. Hence the two sides are the same term, and
the second disjunct of the definition of $`\preceq`$ (D.ole) holds. ∎

<a id="t-core_i0"></a>
## Theorem: core of the complete copy (T.core_i0)

### Theorem

Let $`v_0, w_0 \in \mathbb{N}`$, $`R, T \in \mathrm{PairSeq}`$ and $`\ell \in \mathbb{N}\times\mathbb{N}`$, and assume

```math
\forall x \in R,\ v_0 \lt x_1,
\qquad v_0 \lt \ell_1,
\qquad T = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,T)_1\bigr)
```

Then

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} T\bigr)
  \prec \mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr).
```

### Proof

By [T.translate_block_append](Term.md#t-translate_block_append), the left-hand side is

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} T\bigr) = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T\bigr)
```

For the right-hand side, every element of $`R \mathbin{+\!\!+} (\ell)`$ satisfies $`v_0 \lt x_1`$
(for the elements of $`R`$ by the first hypothesis, for $`\ell`$ by the second), so
[T.translate_single_tree](Term.md#t-translate_single_tree) gives

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr)
= \mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
= \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

The two have the common subscript $`w_0`$, and their arguments satisfy
$`\mathrm{tr}\,R \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell))`$ by
[T.translate_snoc_increase](#t-translate_snoc_increase).
It suffices to apply [T.olt_P_b](Term.md#t-olt_P_b). ∎

<a id="t-core_i1"></a>
## Theorem: core of the ascending copy (T.core_i1)

### Theorem

Let $`v_0, w_0 \in \mathbb{N}`$, $`R, C' \in \mathrm{PairSeq}`$ and
$`c, \ell \in \mathbb{N}\times\mathbb{N}`$, and assume

```math
\forall x \in R,\ v_0 \lt x_1,
\qquad \forall x \in C',\ c_1 \le x_1,
\qquad c_1 = \ell_1,
\qquad v_0 \lt \ell_1,
\qquad c_2 \lt \ell_2
```

Then

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (c :: C')\bigr)
  \prec \mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr).
```

### Proof

We proceed in three steps.

**Step 1: $`\mathrm{tr}(c :: C') \prec \mathrm{tr}\,(\ell)`$.**
By [T.lead_translate](Term.md#t-lead_translate) we have
$`\mathrm{lead}\,\mathrm{tr}(c :: C') = c_2`$ ([D.lead](Term.md#d-lead)), and
$`c_2 \lt \ell_2`$ by hypothesis.
On the other hand, the definition of $`\mathrm{tr}`$ (D.translate) gives
$`\mathrm{tr}\,(\ell) = \mathsf{P}(\ell_2, \mathsf{Z}, \mathsf{Z})`$.
Applying [T.olt_P_of_lead_lt](Term.md#t-olt_P_of_lead_lt) with
$`t := \mathrm{tr}(c :: C')`$ and $`w := \ell_2`$ yields Step 1.

**Step 2: $`\mathrm{tr}(R \mathbin{+\!\!+} c :: C') \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell))`$.**
Apply [T.translate_ctx_cong](Term.md#t-translate_ctx_cong) with
$`z_1 := c`$, $`T_1 := C'`$, $`z_2 := \ell`$, $`T_2 := ()`$, $`G := R`$.
Its four hypotheses are met as follows.

- (base): Step 1.
- (root): $`c_1 = \ell_1`$ is a hypothesis.
- (r1): $`\forall x \in C',\ c_1 \le x_1`$ is a hypothesis.
- (r2): $`T_2 = ()`$ has no element, so the antecedent is false and it holds.

**Step 3: putting the root $`(v_0,w_0)`$ on top.**
We show that every element $`x`$ of $`R \mathbin{+\!\!+} c :: C'`$ satisfies $`v_0 \lt x_1`$.
For $`x \in R`$ this is a hypothesis. For $`x = c`$, $`c_1 = \ell_1`$ and $`v_0 \lt \ell_1`$ give
$`v_0 \lt c_1`$. For $`x \in C'`$, the $`v_0 \lt c_1`$ just proved and the hypothesis
$`c_1 \le x_1`$ give $`v_0 \lt x_1`$. In the same way every element of $`R \mathbin{+\!\!+} (\ell)`$
satisfies $`v_0 \lt x_1`$.

Hence [T.translate_single_tree](Term.md#t-translate_single_tree) gives

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (c :: C')\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} c :: C'),\ \mathsf{Z}\bigr),
```
```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

and the conclusion follows from Step 2 and [T.olt_P_b](Term.md#t-olt_P_b). ∎

<a id="t-translate_oper_pred"></a>
## Theorem: decrease in the predecessor branch (T.translate_oper_pred)

### Theorem

Let $`1 \lt \lvert M\rvert`$ and assume

```math
\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr) \ \vee\ \neg\,\mathrm{hasParent}(M, i_1, j_1)
```

Then $`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$ for every $`n`$.

### Proof

From $`1 \lt \lvert M\rvert`$ we get $`j_1 = \lvert M\rvert - 1 \ne 0`$.

First we show $`M[n] = \mathrm{Pred}\,M`$. We distinguish cases on the disjunction in the
hypothesis. For the first disjunct this is
[T.oper_eq_pred_of_zero](#t-oper_eq_pred_of_zero). For the second disjunct we distinguish further
according to whether $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ holds: if it does, again
[T.oper_eq_pred_of_zero](#t-oper_eq_pred_of_zero); if it does not,
[T.oper_eq_pred_of_noParent](#t-oper_eq_pred_of_noParent).

Next, $`1 \lt \lvert M\rvert`$ gives $`\neg(\lvert M\rvert \le 1)`$, so the second case of the
definition of $`\mathrm{Pred}`$ (D.Pred) is taken and $`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$.

Finally $`M \ne ()`$ (if $`M = ()`$ then $`\lvert M\rvert = 0`$, contradicting
$`1 \lt \lvert M\rvert`$). Hence
[T.translate_dropLast_decrease](#t-translate_dropLast_decrease) applies and

```math
\mathrm{tr}\,(M[n]) = \mathrm{tr}(\mathrm{dropLast}\,M) \prec \mathrm{tr}\,M . \qquad \blacksquare
```

<a id="t-parent_nextR"></a>
## Theorem: the parent satisfies the parent relation (T.parent_nextR)

### Theorem

If $`\mathrm{hasParent}(M, i, j_1)`$, then
$`\mathrm{par}^M_i(j_1)`$ $`\to^M_i j_1`$ ([D.nextR](Pss.md#d-nextR)).

### Proof

By the definition of $`\mathrm{hasParent}`$ (D.hasParent) there exists $`j_0`$ with
$`j_0 \to^M_i j_1`$. The $`\varepsilon`$ in the definition of $`\mathrm{par}`$ (D.parent) returns a
value satisfying the condition whenever a value satisfying it exists. ∎

<a id="t-nextR_index_lt"></a>
## Theorem: the index increases along the parent relation (T.nextR_index_lt)

### Theorem

If $`j_0 \to^M_i j_1`$, then $`j_0 \lt j_1`$.

### Proof

By the case distinction in the definition of $`\to^M_i`$ (D.nextR). If $`i = 0`$, then
$`j_0 \to^M_0 j_1`$ ([D.nextrel0](Pss.md#d-nextrel0)), and the third condition of the definition of
$`\to^M_0`$ (D.nextrel0) is $`j_0 \lt j_1`$.
If $`i \ne 0`$, then $`j_0 \to^M_1 j_1`$ ([D.nextrel1](Pss.md#d-nextrel1)), and the third condition
of the definition of $`\to^M_1`$ (D.nextrel1) is $`j_0 \lt j_1`$. ∎

<a id="t-nextR_chain0"></a>
## Theorem: the parent relation gives a chain of ancestors in row 0 (T.nextR_chain0)

### Theorem

If $`j_0 \to^M_i j_1`$, then $`j_0 \mathbin{(\to^M_0)^{*}} j_1`$.

### Proof

By the case distinction in the definition of $`\to^M_i`$ (D.nextR).

- Case $`i = 0`$. Since $`j_0 \to^M_0 j_1`$, the relation
  $`j_0 \mathbin{(\to^M_0)^{*}} j_1`$ holds as a chain of length $`1`$.

- Case $`i \ne 0`$. Then $`j_0 \to^M_1 j_1`$, and the fifth condition of the definition of
  $`\to^M_1`$ (D.nextrel1) is $`j_0 \le^M_0 j_1`$ ([D.le0](Pss.md#d-le0)).
  The third condition of the definition of $`\le^M_0`$ (D.le0) is
  $`j_0 \mathbin{(\to^M_0)^{*}} j_1`$. ∎

<a id="t-oper_bad_blocks"></a>
## Theorem: block decomposition of the fourth branch (T.oper_bad_blocks)

### Theorem

Assume $`1 \lt \lvert M\rvert`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$,
$`\mathrm{hasParent}(M, i_1, j_1)`$ and $`1 \le n`$.
Then there exist $`G, R \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0 \in \mathbb{N}`$ and
$`\ell \in \mathbb{N}\times\mathbb{N}`$ for which the following six statements hold.

```math
\begin{aligned}
&(1)\ M = G \mathbin{+\!\!+} ((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell), \cr
&(2)\ M[n] = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+0\cdot d_0}
        \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+(n-1)d_0}, \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ v_0 \lt \ell_1, \cr
&(5)\ \bigl(d_0 = 0 \wedge i_1 = 0\bigr) \ \vee\
        \bigl(0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0
              \wedge \lvert G\rvert \to^M_1 j_1\bigr), \cr
&(6)\ \lvert G\rvert \to^M_{i_1} j_1 .
\end{aligned}
```

Here $`L^{+e}`$ is the sequence obtained from $`L`$ by adding $`e`$ to the first entry of each pair
(the notation of [T.translate_shift](Term.md#t-translate_shift)).

### Proof

Put $`j_0 := \mathrm{par}^M_{i_1}(j_1)`$.
By [T.parent_nextR](#t-parent_nextR) we have $`j_0 \to^M_{i_1} j_1`$, by
[T.nextR_index_lt](#t-nextR_index_lt) we have $`j_0 \lt j_1`$, and by
[T.nextR_chain0](#t-nextR_chain0) we have $`j_0 \mathbin{(\to^M_0)^{*}} j_1`$.
Applying [T.le0_interval_gt](Term.md#t-le0_interval_gt) to the last of these gives

```math
(\ast)\qquad \forall k,\ \bigl(j_0 \lt k \wedge k \le j_1\bigr) \to M_{0,j_0} \lt M_{0,k}
```

Define $`d_0`$ by the same formula as in [T.oper_bad_unfold](#t-oper_bad_unfold).
The required objects are taken as follows.

```math
G := (M_0,\dots,M_{j_0-1}), \quad
v_0 := M_{0,j_0}, \quad
w_0 := M_{1,j_0},
```
```math
R := \bigl(\,(M_{0,j},\ M_{1,j})\,\bigr)_{j=j_0+1}^{j_1-1}, \quad
\ell := M\langle j_1\rangle .
```

Here $`\lvert G\rvert = j_0`$ (since $`j_0 \lt j_1 \lt \lvert M\rvert`$, the first $`j_0`$ elements
can be taken exactly). We prove the six statements in turn.

**(1)** Cutting $`M`$ at position $`j_0`$ gives $`M = G \mathbin{+\!\!+} \mathrm{drop}_{j_0} M`$.
By [T.drop_eq_map_getD](Term.md#t-drop_eq_map_getD),

```math
\mathrm{drop}_{j_0} M = \bigl(M\langle j_0\rangle,\ M\langle j_0+1\rangle,\ \dots,\ M\langle j_1\rangle\bigr)
```

(using $`\lvert M\rvert - j_0 = (j_1 - j_0) + 1`$), and in the range
$`j \le j_1 \lt \lvert M\rvert`$ we have $`M\langle j\rangle = (M_{0,j}, M_{1,j})`$
(definition of $`M_{i,j}`$, D.entry). Cutting off the first element and the last element gives

```math
\mathrm{drop}_{j_0} M = \bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} (\ell)
```

which is (1).

**(2)** By [T.oper_bad_unfold](#t-oper_bad_unfold),

```math
M[n] = G \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
```

Splitting the range $`[j_0, j_1)`$ of the index $`j`$ into its first value $`j_0`$ and the rest,
the first element of $`B_k`$ is $`(v_0 + k\,d_0,\ w_0)`$ and the remainder is obtained from $`R`$
by adding $`k\,d_0`$ to the first entry of each pair. That is,
$`B_k = ((v_0,w_0) :: R)^{+k\,d_0}`$, which is (2).

**(3)** The elements of $`R`$ are of the form $`(M_{0,j}, M_{1,j})`$ for the $`j`$ with
$`j_0 \lt j \lt j_1`$. Applying $`(\ast)`$ with $`k := j`$ gives
$`v_0 = M_{0,j_0} \lt M_{0,j}`$.

**(4)** Apply $`(\ast)`$ with $`k := j_1`$ (we have $`j_0 \lt j_1`$ and $`j_1 \le j_1`$).
Since $`\ell_1 = M_{0,j_1}`$, we get $`v_0 \lt \ell_1`$.

**(5)** We distinguish cases on $`i_1`$.

- Case $`i_1 = 0`$. The condition $`0 \lt i_1`$ in the definition of $`d_0`$ is false, so
  $`d_0 = 0`$ and the first disjunct holds.

- Case $`0 \lt i_1`$. By the definition of $`\to^M_i`$ (D.nextR), $`j_0 \to^M_{i_1} j_1`$ is
  $`j_0 \to^M_1 j_1`$. Here $`d_0 = M_{0,j_1} - M_{0,j_0}`$, and the
  $`M_{0,j_0} \lt M_{0,j_1}`$ obtained in the proof of (4) gives $`0 \lt d_0`$ and
  $`M_{0,j_1} = M_{0,j_0} + d_0`$, that is, $`\ell_1 = v_0 + d_0`$.
  Moreover the fourth condition of the definition of $`\to^M_1`$ (D.nextrel1) is
  $`M_{1,j_0} \lt M_{1,j_1}`$, that is, $`w_0 \lt \ell_2`$. Since $`\lvert G\rvert = j_0`$,
  $`\lvert G\rvert \to^M_1 j_1`$ holds as well. Hence the second disjunct holds.

**(6)** We have $`\lvert G\rvert = j_0`$, and $`j_0 \to^M_{i_1} j_1`$ was shown at the outset. ∎

<a id="t-translate_oper_bad"></a>
## Theorem: decrease in the fourth branch (T.translate_oper_bad)

### Theorem

Assume $`1 \lt \lvert M\rvert`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$,
$`\mathrm{hasParent}(M, i_1, j_1)`$ and $`1 \le n`$; then
$`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$.

### Proof

Take $`G, v_0, w_0, R, d_0, \ell`$ by [T.oper_bad_blocks](#t-oper_bad_blocks).
We call $`(v_0,w_0) :: R`$ the **basic block**.

**Step 1: putting the two sides into the same shape.**
The $`k = 0`$ term of (2) is $`((v_0,w_0) :: R)^{+0} = (v_0,w_0) :: R`$, so collecting the terms
with $`k \ge 1`$ into

```math
C := \bigl((v_0,w_0) :: R\bigr)^{+1\cdot d_0} \mathbin{+\!\!+} \cdots
      \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+(n-1)d_0}
```

we can write (1) and (2) as

```math
M[n] = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: (R \mathbin{+\!\!+} C)\bigr),
\qquad
M = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
```

**Step 2: every element of $`C`$ has row 0 at least $`v_0`$.**
Let $`x \in C`$. Then $`x = (p_1 + k\,d_0,\ p_2)`$ for some $`k \ge 1`$ and some element $`p`$ of
the basic block. If $`p = (v_0,w_0)`$ then $`p_1 = v_0`$; if $`p \in R`$ then $`v_0 \lt p_1`$
by (3); in either case $`v_0 \le p_1`$.
Hence $`v_0 \le p_1 \le p_1 + k\,d_0 = x_1`$.

**Step 3 (the core): $`\mathrm{tr}(((v_0,w_0) :: R) \mathbin{+\!\!+} C) \prec \mathrm{tr}(((v_0,w_0) :: R) \mathbin{+\!\!+} (\ell))`$.**
We distinguish cases on $`n`$.

- **Case $`n = 1`$.** $`C`$ is an empty concatenation, so $`C = ()`$.
  Apply [T.core_i0](#t-core_i0) with $`T := ()`$ (the first disjunct of its third hypothesis).

**Case $`n \ge 2`$.** Extracting the leading block of $`C`$ gives

```math
C = (v_0 + d_0,\ w_0) :: \Bigl(R^{+d_0} \mathbin{+\!\!+}
      \bigl((v_0,w_0) :: R\bigr)^{+2 d_0} \mathbin{+\!\!+} \cdots
      \mathbin{+\!\!+} \bigl((v_0,w_0) :: R\bigr)^{+(n-1)d_0}\Bigr)
```

We distinguish cases on the disjunction (5).

- **Case $`d_0 = 0`$ (complete copy).** The head of $`C`$ is $`(v_0 + 0,\ w_0) = (v_0, w_0)`$,
  so $`\neg\bigl(v_0 \lt (\mathrm{head}\,C)_1\bigr)`$.
  Apply [T.core_i0](#t-core_i0) with $`T := C`$ (the second disjunct of its third hypothesis).

- **Case $`0 \lt d_0`$ (ascending copy).**
  Apply [T.core_i1](#t-core_i1) with $`c := (v_0 + d_0,\ w_0)`$ and $`C' := C`$ with its head removed.
  We check the five hypotheses.
  - $`\forall x \in R,\ v_0 \lt x_1`$: this is (3).
  - $`\forall x \in C',\ c_1 \le x_1`$: if $`x`$ is an element of $`R^{+d_0}`$, then for the $`p`$
    with $`v_0 \lt p_1`$ given by (3) we have $`x_1 = p_1 + d_0 \ge v_0 + d_0 = c_1`$.
    If $`x`$ is an element of a block with $`k \ge 2`$, then $`v_0 \le p_1`$ by the same argument
    as in Step 2, and $`d_0 \le k\,d_0`$, so $`x_1 = p_1 + k\,d_0 \ge v_0 + d_0 = c_1`$.
  - $`c_1 = \ell_1`$: here $`c_1 = v_0 + d_0`$, and the second disjunct of (5) contains $`\ell_1 = v_0 + d_0`$.
  - $`v_0 \lt \ell_1`$: this is (4).
  - $`c_2 \lt \ell_2`$: here $`c_2 = w_0`$, and the second disjunct of (5) contains $`w_0 \lt \ell_2`$.

**Step 4: lifting through the good part $`G`$.**
Apply [T.translate_ctx_cong](Term.md#t-translate_ctx_cong) with
$`z_1 := (v_0,w_0)`$, $`T_1 := R \mathbin{+\!\!+} C`$,
$`z_2 := (v_0,w_0)`$, $`T_2 := R \mathbin{+\!\!+} (\ell)`$, $`G := G`$.
Its four hypotheses are met as follows.

- (base): this is the conclusion of Step 3 rewritten by
  $`((v_0,w_0) :: R) \mathbin{+\!\!+} X = (v_0,w_0) :: (R \mathbin{+\!\!+} X)`$.
- (root): the roots of the two sides are the same $`(v_0,w_0)`$, so $`v_0 = v_0`$.
- (r1): if $`x \in R`$ then $`v_0 \lt x_1`$ by (3); if $`x \in C`$ then $`v_0 \le x_1`$ by Step 2.
- (r2): if $`x \in R`$ the same as above; if $`x = \ell`$ then $`v_0 \lt \ell_1`$ by (4).

By the rewriting of Step 1, the conclusion obtained is $`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$. ∎

<a id="t-m_step_decreases"></a>
## Theorem: expansion strictly decreases the measure (T.m_step_decreases)

### Theorem

If $`1 \lt \lvert M\rvert`$ and $`1 \le n`$, then
$`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$.

### Proof

We distinguish cases along the branches of the definition of $`M[n]`$ (D.oper). From
$`1 \lt \lvert M\rvert`$ we get $`j_1 \ne 0`$, so branch (a) does not occur.

- Case $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$.
  Apply [T.translate_oper_pred](#t-translate_oper_pred) with the first disjunct.

- Otherwise, case $`\mathrm{hasParent}(M, i_1, j_1)`$.
  Apply [T.translate_oper_bad](#t-translate_oper_bad).

- Otherwise, case $`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$.
  Apply [T.translate_oper_pred](#t-translate_oper_pred) with the second disjunct.

In each case the conclusion is obtained. ∎
