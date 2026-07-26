[← README](README.md) | [English](Column-2.md) | [Japanese](Column-2-ja.md) | Column [1](Column.md) **2** [3](Column-3.md) [4](Column-4.md)

<a id="t-oper_append_right"></a>
## Theorem: expansion commutes with prefixing (T.oper_append_right)

### Theorem

Let $`A, T \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) and $`n \in \mathbb{N}`$, and suppose
$`2 \le \lvert T\rvert`$ and $`T_{0,0} = 0`$ ([D.entry](Pss.md#d-entry)).
Then

```math
(A \mathbin{+\!\!+} T)[n] = A \mathbin{+\!\!+} T[n] .
```

($`M[n]`$ [D.oper](Pss.md#d-oper))

### Proof

Put $`j_1 := \lvert T\rvert - 1`$. From $`2 \le \lvert T\rvert`$ we get $`1 \le j_1`$, in particular $`j_1 \ne 0`$.
Moreover

```math
\lvert A \mathbin{+\!\!+} T\rvert - 1 = (\lvert A\rvert + \lvert T\rvert) - 1 = \lvert A\rvert + j_1
```

so the last index in the definition of $`M[n]`$ (D.oper) applied to $`A \mathbin{+\!\!+} T`$ is $`\lvert A\rvert + j_1`$.
We now match the four branches of D.oper on the two sides.

**Branch (a).** The condition is $`\lvert A\rvert + j_1 = 0`$ on the left and $`j_1 = 0`$ on the right,
and both are false since $`1 \le j_1`$. Hence neither side takes branch (a).

**Branch (b).** The condition is
$`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = 0 \wedge (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} = 0`$ on the left
and $`T_{0,j_1} = 0 \wedge T_{1,j_1} = 0`$ on the right.
By [T.entry_append_right](Column.md#t-entry_append_right),

```math
(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = T_{0,j_1},
\qquad
(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} = T_{1,j_1}
```

so the two conditions are the same proposition. If it holds, the two sides are
$`\mathrm{Pred}\,(A \mathbin{+\!\!+} T)`$ ([D.Pred](Pss.md#d-Pred)) and $`\mathrm{Pred}\,T`$ respectively, and by
[T.Pred_append_right](Column.md#t-Pred_append_right) we have
$`\mathrm{Pred}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{Pred}\,T`$.
From now on suppose that this condition fails.

**The search row.** By [T.idx1_append_right](Column.md#t-idx1_append_right),
$`\mathrm{idx}_1(A \mathbin{+\!\!+} T, \lvert A\rvert + j_1) = \mathrm{idx}_1(T, j_1)`$ ([D.idx1](Pss.md#d-idx1)),
so the $`i_1`$ of the two sides is one and the same value. Write $`i_1 := \mathrm{idx}_1(T, j_1)`$.
We distinguish cases according to whether $`\mathrm{hasParent}(T, i_1, j_1)`$ ([D.hasParent](Pss.md#d-hasParent)) holds.

**(A) The case where $`\mathrm{hasParent}(T, i_1, j_1)`$ holds.**
We first show $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$.
By the rewriting above this is equivalent to $`0 \lt T_{0,j_1}`$.
If $`T_{0,j_1} = 0`$, then applying [T.no_hasParent_of_row0_zero](Column.md#t-no_hasParent_of_row0_zero)
with $`M := T`$, $`i := i_1`$, $`j_1 := j_1`$ yields a contradiction.
Hence the ($`\Leftarrow`$) direction of [T.hasParent_append_right](Column.md#t-hasParent_append_right) applies,
and $`\mathrm{hasParent}(A \mathbin{+\!\!+} T, i_1, \lvert A\rvert + j_1)`$ holds.
Therefore the condition of branch (c) is false on both sides, and both sides take branch (d).

We compare the constituents of branch (d). Put $`j_0 := \mathrm{par}^{T}_{i_1}(j_1)`$ ([D.parent](Pss.md#d-parent)).

**The parent.** By [T.parent_append_right](Column.md#t-parent_append_right),
$`\mathrm{par}^{A \mathbin{+\!\!+} T}_{i_1}(\lvert A\rvert + j_1) = \lvert A\rvert + j_0`$.

**The increments.** By the formulas of D.oper, the $`d_0`$ and $`d_1`$ of the left-hand side are

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

Applying [T.entry_append_right](Column.md#t-entry_append_right) to the four entries, these are equal to
$`T_{0,j_1} - T_{0,j_0}`$ when $`0 \lt i_1`$ and to $`T_{1,j_1} - T_{1,j_0}`$ when $`1 \lt i_1`$,
and the conditions are the same as well, so they agree with the $`d_0`$ and $`d_1`$ of the right-hand side.

**The prefix.** By [T.take_append_right](Column.md#t-take_append_right),
$`\mathrm{take}_{\lvert A\rvert + j_0}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{take}_{j_0}\,T`$.

**The copy blocks.** The $`k`$-th block of the left-hand side is the sequence of length
$`(\lvert A\rvert + j_1) - (\lvert A\rvert + j_0) = j_1 - j_0`$ obtained by letting the index $`j`$ run
from $`\lvert A\rvert + j_0`$ to $`(\lvert A\rvert + j_1) - 1`$:

```math
\Bigl(\bigl((A \mathbin{+\!\!+} T)_{0,j} + k\,d_0,\ (A \mathbin{+\!\!+} T)_{1,j} + k\,d_1\bigr)\Bigr)_{j = \lvert A\rvert + j_0}^{\lvert A\rvert + j_1 - 1}
```

Applying [T.copyblock_append](Column.md#t-copyblock_append) with $`a := j_0`$ and $`m := j_1 - j_0`$,
this is equal to the $`k`$-th block of the right-hand side

```math
\Bigl(\bigl(T_{0,j} + k\,d_0,\ T_{1,j} + k\,d_1\bigr)\Bigr)_{j = j_0}^{j_1 - 1}
```

This holds for every $`k = 0, 1, \dots, n-1`$.

Hence, writing the common blocks as $`B_0, \dots, B_{n-1}`$,

```math
\begin{aligned}
(A \mathbin{+\!\!+} T)[n]
 &= \bigl(A \mathbin{+\!\!+} \mathrm{take}_{j_0}\,T\bigr)
    \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1} \cr
 &= A \mathbin{+\!\!+} \bigl(\mathrm{take}_{j_0}\,T
    \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1}\bigr) \cr
 &= A \mathbin{+\!\!+} T[n]
\end{aligned}
```

where the middle equality is associativity of concatenation.

**(B) The case $`\neg\,\mathrm{hasParent}(T, i_1, j_1)`$.**
We show $`\neg\,\mathrm{hasParent}(A \mathbin{+\!\!+} T, i_1, \lvert A\rvert + j_1)`$.
Suppose $`\mathrm{hasParent}(A \mathbin{+\!\!+} T, i_1, \lvert A\rvert + j_1)`$ holds, and
distinguish cases on $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$.

- The case $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$.
  The ($`\Rightarrow`$) direction of [T.hasParent_append_right](Column.md#t-hasParent_append_right) gives
  $`\mathrm{hasParent}(T, i_1, j_1)`$, contradicting the assumption of this case.
- The case $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = 0`$.
  Applying [T.no_hasParent_of_row0_zero](Column.md#t-no_hasParent_of_row0_zero) with
  $`M := A \mathbin{+\!\!+} T`$, $`j_1 := \lvert A\rvert + j_1`$ yields a contradiction.

Hence both sides take branch (c), and they are $`\mathrm{Pred}\,(A \mathbin{+\!\!+} T)`$ and $`\mathrm{Pred}\,T`$ respectively.
By [T.Pred_append_right](Column.md#t-Pred_append_right) the two are related by concatenation with $`A`$. ∎

<a id="t-map_range_entry_eq_take"></a>
## Theorem: enumerating the entries gives a prefix (T.map_range_entry_eq_take)

### Theorem

Let $`N \in \mathrm{PairSeq}`$ and $`j_1 \in \mathbb{N}`$ with $`j_1 \le \lvert N\rvert`$. Then

```math
\bigl((N_{0,j},\ N_{1,j})\bigr)_{j = 0}^{j_1 - 1} = \mathrm{take}_{j_1}\,N .
```

### Proof

We compare the lengths and the elements of the two sides.

**Length.** The left-hand side is a sequence of length $`j_1`$. The length of the right-hand side is
$`\min(j_1, \lvert N\rvert)`$, which by the hypothesis $`j_1 \le \lvert N\rvert`$ equals $`j_1`$.

**The $`i`$-th element ($`i \lt j_1`$).**
Since $`i \lt j_1 \le \lvert N\rvert`$, the first case of the definition of $`M\langle j\rangle`$ (D.entry) gives
$`N\langle i\rangle = N_i`$. Hence the $`i`$-th element of the left-hand side is

```math
(N_{0,i},\ N_{1,i}) = \bigl(\pi_1(N_i),\ \pi_2(N_i)\bigr) = N_i
```

The $`i`$-th element of the right-hand side is, since $`i \lt j_1`$, the $`i`$-th element $`N_i`$ of $`N`$.
Hence the $`i`$-th elements of the two sides agree. ∎

<a id="t-oper_headD"></a>
## Theorem: expansion does not change the head (T.oper_headD)

### Theorem

Let $`N \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$, and suppose $`1 \lt \lvert N\rvert`$ and $`1 \le n`$.
Then $`\mathrm{head}\,(N[n]) = \mathrm{head}\,N`$.

### Proof

By [T.oper_eq_dropLast_append](Cnf.md#t-oper_eq_dropLast_append) there is $`R \in \mathrm{PairSeq}`$ with
$`N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R`$.
From $`1 \lt \lvert N\rvert`$, the sequence $`N`$ has at least two elements and can be written $`N = a :: b :: u`$.
Then

```math
\mathrm{dropLast}\,(a :: b :: u) = a :: \mathrm{dropLast}\,(b :: u)
```

so

```math
N[n] = a :: \bigl(\mathrm{dropLast}\,(b :: u) \mathbin{+\!\!+} R\bigr)
```

and therefore $`\mathrm{head}\,(N[n]) = a = \mathrm{head}\,N`$. ∎

<a id="t-translate_nil"></a>
## Theorem: translation of the empty sequence (T.translate_nil)

### Theorem

$`\mathrm{tr}\,()`$ ([D.translate](Term.md#d-translate)) equals $`\mathsf{Z}`$ ([D.Three](Term.md#d-Three)).

### Proof

This is exactly the first clause of the definition of $`\mathrm{tr}`$ (D.translate). ∎

<a id="d-maxr1"></a>
## Definition: maximum of row 1 (D.maxr1)

For $`S \in \mathrm{PairSeq}`$ we define $`\mathrm{maxr}_1(S) \in \mathbb{N}`$ by recursion on the constructors of sequences.

```math
\mathrm{maxr}_1(()) := 0,
\qquad
\mathrm{maxr}_1(c :: S) := \max\bigl(c_2,\ \mathrm{maxr}_1(S)\bigr) .
```

Here $`c = (c_1, c_2)`$. The argument $`S`$ of the recursive call is a proper suffix of $`c :: S`$ and hence
strictly shorter, so this definition is well defined.

<a id="t-maxr1_cons"></a>
## Theorem: recursion equation for the maximum of row 1 (T.maxr1_cons)

### Theorem

For $`c \in \mathbb{N} \times \mathbb{N}`$ and $`S \in \mathrm{PairSeq}`$,

```math
\mathrm{maxr}_1(c :: S) = \max\bigl(c_2,\ \mathrm{maxr}_1(S)\bigr) .
```

### Proof

This is exactly the second clause of the definition of $`\mathrm{maxr}_1`$ (D.maxr1), and the two sides are
the same value by definition. ∎

<a id="d-r1ok"></a>
## Definition: row-1 discipline (D.r1ok)

For $`M \in \mathrm{PairSeq}`$ we define the proposition $`\mathrm{r1ok}(M)`$ to be the following.

> For every $`j`$, if $`j \lt \lvert M\rvert`$ and $`0 \lt M_{0,j}`$, then there exists $`k`$
> satisfying the following four conditions.

```math
\begin{aligned}
&(1)\ k \lt j, \cr
&(2)\ M_{0,k} + 1 = M_{0,j}, \cr
&(3)\ \forall l\ \bigl(k \lt l \wedge l \lt j \to M_{0,j} \le M_{0,l}\bigr), \cr
&(4)\ M_{1,j} \le M_{1,k} + 1 .
\end{aligned}
```

A $`k`$ satisfying conditions (1)–(4) is called a **witness** for column $`j`$ in the sequence $`M`$.

<a id="t-diagSeq0_length"></a>
## Theorem: length of the diagonal sequence (T.diagSeq0_length)

### Theorem

For every $`v \in \mathbb{N}`$, $`\lvert \Delta_0^v\rvert = v + 1`$ ([D.diagSeq](Pss.md#d-diagSeq)).

### Proof

By the definition of $`\Delta_a^b`$ (D.diagSeq) we have
$`\Delta_0^v = ((0,0),(1,1),\dots,(v,v))`$, whose length is $`v + 1 - 0`$,
that is, $`v + 1`$. ∎

<a id="t-diagSeq0_getD"></a>
## Theorem: entries of the diagonal sequence (T.diagSeq0_getD)

### Theorem

For all $`v, i \in \mathbb{N}`$, if $`i \lt v + 1`$ then
$`\Delta_0^v\langle i\rangle = (i,i)`$.

### Proof

By [T.diagSeq0_length](#t-diagSeq0_length) we have $`\lvert \Delta_0^v\rvert = v+1`$, and the hypothesis
$`i \lt v+1`$ says that the index $`i`$ is in range. Hence the first case of the definition of
$`M\langle i\rangle`$ (D.entry) is selected, and $`\Delta_0^v\langle i\rangle`$ is the $`i`$-th element of $`\Delta_0^v`$.
By the definition of $`\Delta_a^b`$ (D.diagSeq) we have $`\Delta_0^v = ((0,0),(1,1),\dots,(v,v))`$,
so its $`i`$-th element is $`(i,i)`$. ∎

<a id="t-r1ok_diagSeq"></a>
## Theorem: the diagonal sequence satisfies the row-1 discipline (T.r1ok_diagSeq)

### Theorem

For every $`v \in \mathbb{N}`$, $`\mathrm{r1ok}(\Delta_0^v)`$.

### Proof

Suppose $`j \lt \lvert \Delta_0^v\rvert`$ and $`0 \lt (\Delta_0^v)_{0,j}`$.
By [T.diagSeq0_length](#t-diagSeq0_length) we have $`j \lt v+1`$, and by
[T.diagSeq0_getD](#t-diagSeq0_getD) we have $`\Delta_0^v\langle j\rangle = (j,j)`$,
hence $`(\Delta_0^v)_{0,j} = j`$. The hypothesis then gives $`0 \lt j`$.

Take $`k := j - 1`$ as witness. From $`0 \lt j`$ we get $`j - 1 + 1 = j`$, and
$`j - 1 \lt j \lt v+1`$, so [T.diagSeq0_getD](#t-diagSeq0_getD) applies to $`j-1`$ as well and gives
$`\Delta_0^v\langle j-1\rangle = (j-1, j-1)`$.
We check the four conditions of the definition of $`\mathrm{r1ok}`$ (D.r1ok).

**(1)** From $`0 \lt j`$ we get $`j - 1 \lt j`$.

**(2)** $`(\Delta_0^v)_{0,j-1} + 1 = (j-1) + 1 = j = (\Delta_0^v)_{0,j}`$.

**(3)** Take $`l`$ with $`j - 1 \lt l`$ and $`l \lt j`$. From $`0 \lt j`$ we get
$`j - 1 \lt l \lt j = (j-1) + 1`$, and no natural number $`l`$ is of that form.
Hence the antecedent is false and the condition holds.

**(4)** $`(\Delta_0^v)_{1,j} = j`$ and $`(\Delta_0^v)_{1,j-1} + 1 = (j-1) + 1 = j`$, so
$`(\Delta_0^v)_{1,j} \le (\Delta_0^v)_{1,j-1} + 1`$. ∎

<a id="t-getD_take"></a>
## Theorem: entries of a prefix (T.getD_take)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and $`m, j \in \mathbb{N}`$. If $`j \lt m`$ then

```math
(\mathrm{take}_m M)\langle j\rangle = M\langle j\rangle .
```

### Proof

When $`j \lt m`$, the $`j`$-th element of $`\mathrm{take}_m M`$ is the $`j`$-th element of $`M`$, and when
the $`j`$-th element of $`M`$ does not exist (that is, when $`j \ge \lvert M\rvert`$), the $`j`$-th element of
$`\mathrm{take}_m M`$ does not exist either. That is, for $`j \lt m`$,

```math
j \lt \lvert \mathrm{take}_m M\rvert \iff j \lt \lvert M\rvert
```

and in that case the $`j`$-th elements of the two agree.
Since the definition of $`M\langle j\rangle`$ (D.entry) returns the $`j`$-th element when the index is in
range and $`(0,0)`$ when it is out of range, the two sides agree. ∎

<a id="t-r1ok_take"></a>
## Theorem: the row-1 discipline is inherited by prefixes (T.r1ok_take)

### Theorem

If $`\mathrm{r1ok}(M)`$, then for every $`m \in \mathbb{N}`$,
$`\mathrm{r1ok}(\mathrm{take}_m M)`$.

### Proof

Suppose $`j \lt \lvert \mathrm{take}_m M\rvert`$ and $`0 \lt (\mathrm{take}_m M)_{0,j}`$.
Since $`\lvert \mathrm{take}_m M\rvert = \min(m, \lvert M\rvert)`$, we have
$`j \lt m`$ and $`j \lt \lvert M\rvert`$.
By [T.getD_take](#t-getD_take) we have $`(\mathrm{take}_m M)\langle j\rangle = M\langle j\rangle`$, and
therefore $`0 \lt M_{0,j}`$.

Applying the hypothesis $`\mathrm{r1ok}(M)`$ to $`j`$, we obtain a $`k`$ satisfying conditions
(1)–(4) of the definition of $`\mathrm{r1ok}`$ (D.r1ok). We show that this $`k`$ is also a witness for
column $`j`$ in $`\mathrm{take}_m M`$. Condition (1) $`k \lt j`$ is common to both.
Since $`k \lt j \lt m`$, [T.getD_take](#t-getD_take) applies to $`k`$ as well and gives
$`(\mathrm{take}_m M)\langle k\rangle = M\langle k\rangle`$. Hence conditions (2) and (4) become exactly
conditions (2) and (4) for $`M`$.
As for condition (3), for $`l`$ with $`k \lt l`$ and $`l \lt j`$ we have $`l \lt j \lt m`$,
so [T.getD_take](#t-getD_take) gives
$`(\mathrm{take}_m M)\langle l\rangle = M\langle l\rangle`$, and
condition (3) for $`M`$ is the required condition verbatim. ∎

<a id="t-r1ok_dropLast"></a>
## Theorem: the row-1 discipline is inherited under dropLast (T.r1ok_dropLast)

### Theorem

If $`\mathrm{r1ok}(M)`$ then $`\mathrm{r1ok}(\mathrm{dropLast}\,M)`$.

### Proof

We have $`\mathrm{dropLast}\,M = \mathrm{take}_{\lvert M\rvert - 1} M`$
(both are the sequence consisting of the first $`\lvert M\rvert - 1`$ elements of $`M`$).
Hence it suffices to apply [T.r1ok_take](#t-r1ok_take) with $`m := \lvert M\rvert - 1`$. ∎

<a id="t-getD_append_left"></a>
## Theorem: entries in the left part of a concatenation (T.getD_append_left)

### Theorem

Let $`G, X \in \mathrm{PairSeq}`$. If $`i \lt \lvert G\rvert`$ then
$`(G \mathbin{+\!\!+} X)\langle i\rangle = G\langle i\rangle`$.

### Proof

When $`i \lt \lvert G\rvert`$, the $`i`$-th element of the concatenation $`G \mathbin{+\!\!+} X`$ is
the $`i`$-th element of $`G`$. Both indices are in range, so the first case of the definition of
$`M\langle i\rangle`$ (D.entry) is selected on both sides, and the values agree. ∎

<a id="t-getD_append_right"></a>
## Theorem: entries in the right part of a concatenation (T.getD_append_right)

### Theorem

Let $`G, X \in \mathrm{PairSeq}`$. If $`\lvert G\rvert \le i`$ then
$`(G \mathbin{+\!\!+} X)\langle i\rangle = X\langle i - \lvert G\rvert\rangle`$.

### Proof

When $`\lvert G\rvert \le i`$, the $`i`$-th element of $`G \mathbin{+\!\!+} X`$ exists if and only if
the $`i - \lvert G\rvert`$-th element of $`X`$ exists
($`i \lt \lvert G\rvert + \lvert X\rvert \iff i - \lvert G\rvert \lt \lvert X\rvert`$),
and when they exist they are the same element.
Hence the case distinction of the definition of $`M\langle i\rangle`$ (D.entry) agrees on both sides,
and so do the values. ∎

<a id="t-index_decomp"></a>
## Theorem: quotient-remainder decomposition of an index (T.index_decomp)

### Theorem

If $`0 \lt L`$ and $`i \lt n L`$, then there exist $`k, q \in \mathbb{N}`$ with
$`k \lt n`$, $`q \lt L`$ and $`i = k L + q`$.

### Proof

Take $`k := \lfloor i / L\rfloor`$ and $`q := i \bmod L`$.

$`q \lt L`$: since $`0 \lt L`$, the remainder is less than $`L`$.

$`k \lt n`$: from the division identity $`i = L\lfloor i/L\rfloor + (i \bmod L)`$ we get
$`L\lfloor i/L\rfloor \le i`$. If $`n \le \lfloor i/L\rfloor`$, then
$`nL \le L\lfloor i/L\rfloor \le i`$, contradicting the hypothesis $`i \lt nL`$.
Hence $`\lfloor i/L\rfloor \lt n`$.

$`i = kL + q`$: by the division identity and commutativity of multiplication,

```math
i = L\lfloor i/L\rfloor + (i \bmod L) = \lfloor i/L\rfloor \cdot L + (i \bmod L) = kL + q . \qquad \blacksquare
```

<a id="t-copies_map_length"></a>
## Theorem: length of the copy sequence (T.copies_map_length)

### Theorem

In what follows, for $`f : \mathbb{N} \to (\mathbb{N}\times\mathbb{N}) \to (\mathbb{N}\times\mathbb{N})`$,
$`B \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$ we write

```math
\mathrm{cp}(B, f, n) := \mathrm{map}(f_0, B) \mathbin{+\!\!+} \mathrm{map}(f_1, B)
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \mathrm{map}(f_{n-1}, B)
```

Here $`f_k := f(k)`$, and $`\mathrm{map}(g, B)`$ is the sequence obtained from $`B`$ by replacing each
element $`x`$ by $`g(x)`$. For $`n = 0`$ we have $`\mathrm{cp}(B,f,0) = ()`$.
The sequence $`\mathrm{cp}(B,f,n+1)`$ is the concatenation, from left to right, of $`\mathrm{map}(f_k, B)`$
for $`k = 0, 1, \dots, n`$, and separating off its last one gives

```math
\mathrm{cp}(B,f,n+1) = \mathrm{cp}(B,f,n) \mathbin{+\!\!+} \mathrm{map}(f_n, B)
```

Then

```math
\lvert \mathrm{cp}(B,f,n)\rvert = n\,\lvert B\rvert .
```

### Proof

Induction on $`n`$. The induction predicate is

```math
\Phi(n) :\equiv \lvert \mathrm{cp}(B,f,n)\rvert = n\,\lvert B\rvert .
```

- **Base case** $`n = 0`$: we have $`\mathrm{cp}(B,f,0) = ()`$ and
  $`\lvert ()\rvert = 0 = 0 \cdot \lvert B\rvert`$.

**Inductive step** $`n \to n+1`$. Assume
$`\Phi(n)`$, that is, $`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert`$.
By the decomposition stated above, the fact that the length of a concatenation is the sum of the lengths,
and $`\lvert \mathrm{map}(f_n, B)\rvert = \lvert B\rvert`$, we get

```math
\lvert \mathrm{cp}(B,f,n+1)\rvert = n\lvert B\rvert + \lvert B\rvert = (n+1)\lvert B\rvert
```

Hence $`\Phi(n+1)`$. ∎

<a id="t-copies_map_getD"></a>
## Theorem: entries of the copy sequence (T.copies_map_getD)

### Theorem

If $`k \lt n`$ and $`q \lt \lvert B\rvert`$ then

```math
\mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle = f_k\bigl(B\langle q\rangle\bigr).
```

### Proof

Induction on $`n`$. The induction predicate is

```math
\Phi(n) :\equiv \forall k, q,\ \bigl(k \lt n \wedge q \lt \lvert B\rvert\bigr)
  \to \mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle = f_k\bigl(B\langle q\rangle\bigr).
```

- **Base case** $`n = 0`$: there is no natural number $`k`$ with $`k \lt 0`$, so the antecedent is false
  and $`\Phi(0)`$ holds.

**Inductive step** $`n \to n+1`$. Assume $`\Phi(n)`$.
Let $`k \lt n+1`$ and $`q \lt \lvert B\rvert`$, and use the decomposition
$`\mathrm{cp}(B,f,n+1) = \mathrm{cp}(B,f,n) \mathbin{+\!\!+} \mathrm{map}(f_n, B)`$ of
[T.copies_map_length](#t-copies_map_length).
By [T.copies_map_length](#t-copies_map_length) we have
$`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert`$. We distinguish cases according to the comparison of $`k`$ and $`n`$.

**(a) The case $`k \lt n`$.** From $`q \lt \lvert B\rvert`$ we get

```math
k\lvert B\rvert + q \lt k\lvert B\rvert + \lvert B\rvert = (k+1)\lvert B\rvert \le n\lvert B\rvert
```

where the last inequality is by $`k + 1 \le n`$. Hence the index $`k\lvert B\rvert + q`$ lies in the range
of the left part $`\mathrm{cp}(B,f,n)`$, and [T.getD_append_left](#t-getD_append_left) gives

```math
\mathrm{cp}(B,f,n+1)\bigl\langle k\lvert B\rvert + q\bigr\rangle
  = \mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle
```

Applying the induction hypothesis $`\Phi(n)`$ to this yields $`f_k(B\langle q\rangle)`$.

**(b) The case $`k = n`$.** The index is $`n\lvert B\rvert + q`$, and
$`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert \le n\lvert B\rvert + q`$, so
[T.getD_append_right](#t-getD_append_right) gives

```math
\mathrm{cp}(B,f,n+1)\bigl\langle n\lvert B\rvert + q\bigr\rangle
  = \mathrm{map}(f_n, B)\bigl\langle (n\lvert B\rvert + q) - n\lvert B\rvert\bigr\rangle
  = \mathrm{map}(f_n, B)\langle q\rangle
```

Since $`q \lt \lvert B\rvert = \lvert \mathrm{map}(f_n,B)\rvert`$ the index is in range, and
the $`q`$-th element of $`\mathrm{map}(f_n,B)`$ is $`f_n`$ applied to the $`q`$-th element of $`B`$,
that is, $`f_n(B\langle q\rangle)`$. ∎

<a id="d-copyExp"></a>
## Definition: copy expansion (D.copyExp)

For $`L \in \mathrm{PairSeq}`$ and $`e \in \mathbb{N}`$, we write $`L^{+e}`$ ([D.shiftr0](Cnf-2.md#d-shiftr0))
for the sequence obtained from $`L`$ by adding $`e`$ to the first entry of each pair.
For $`G, B \in \mathrm{PairSeq}`$ and $`d_0, n \in \mathbb{N}`$ we define

```math
\mathrm{copyExp}(G,B,d_0,n) := G \mathbin{+\!\!+} \mathrm{cp}(B, f, n),
\qquad f_k(p) := (p_1 + k\,d_0,\ p_2)
```

That is,

```math
\mathrm{copyExp}(G,B,d_0,n)
  = G \mathbin{+\!\!+} B^{+0\cdot d_0} \mathbin{+\!\!+} B^{+1\cdot d_0}
    \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}
```

We call $`G`$ the **prefix part** and
$`B^{+0\cdot d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}`$ the **copy part**.

<a id="t-copyExp_length"></a>
## Theorem: length of a copy expansion (T.copyExp_length)

### Theorem

```math
\lvert \mathrm{copyExp}(G,B,d_0,n)\rvert = \lvert G\rvert + n\,\lvert B\rvert .
```

### Proof

By the definition of $`\mathrm{copyExp}`$ (D.copyExp) we have
$`\mathrm{copyExp}(G,B,d_0,n) = G \mathbin{+\!\!+} \mathrm{cp}(B,f,n)`$, and the length of a concatenation is
the sum of the lengths, so its length is
$`\lvert G\rvert + \lvert \mathrm{cp}(B,f,n)\rvert`$.
By [T.copies_map_length](#t-copies_map_length) we have
$`\lvert \mathrm{cp}(B,f,n)\rvert = n\lvert B\rvert`$. ∎

<a id="t-copyExp_getD_pre"></a>
## Theorem: entries in the prefix part of a copy expansion (T.copyExp_getD_pre)

### Theorem

If $`i \lt \lvert G\rvert`$ then
$`\mathrm{copyExp}(G,B,d_0,n)\langle i\rangle = G\langle i\rangle`$.

### Proof

By the definition of $`\mathrm{copyExp}`$ (D.copyExp) the left-hand side is
$`(G \mathbin{+\!\!+} \mathrm{cp}(B,f,n))\langle i\rangle`$, and it suffices to apply
[T.getD_append_left](#t-getD_append_left). ∎

<a id="t-copyExp_getD_copy"></a>
## Theorem: entries in the copy part of a copy expansion (T.copyExp_getD_copy)

### Theorem

If $`k \lt n`$ and $`q \lt \lvert B\rvert`$ then

```math
\mathrm{copyExp}(G,B,d_0,n)\bigl\langle \lvert G\rvert + (k\lvert B\rvert + q)\bigr\rangle
  = \bigl(B_{0,q} + k\,d_0,\ B_{1,q}\bigr).
```

### Proof

By the definition of $`\mathrm{copyExp}`$ (D.copyExp) the left-hand side is
$`(G \mathbin{+\!\!+} \mathrm{cp}(B,f,n))\langle \lvert G\rvert + (k\lvert B\rvert + q)\rangle`$.
Since $`\lvert G\rvert \le \lvert G\rvert + (k\lvert B\rvert + q)`$,
[T.getD_append_right](#t-getD_append_right) applies and this is equal to

```math
\mathrm{cp}(B,f,n)\bigl\langle \bigl(\lvert G\rvert + (k\lvert B\rvert + q)\bigr) - \lvert G\rvert\bigr\rangle
  = \mathrm{cp}(B,f,n)\bigl\langle k\lvert B\rvert + q\bigr\rangle
```

By [T.copies_map_getD](#t-copies_map_getD) this equals
$`f_k(B\langle q\rangle)`$, that is, the result of applying
$`f_k(p) = (p_1 + k d_0, p_2)`$ from the definition of $`\mathrm{copyExp}`$ (D.copyExp) to
$`p := B\langle q\rangle`$, namely $`(B_{0,q} + k d_0,\ B_{1,q})`$. ∎

<a id="t-hostM_getD_pre"></a>
## Theorem: entries in the prefix part of the concatenation $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ (T.hostM_getD_pre)

### Theorem

Let $`G, B \in \mathrm{PairSeq}`$ and $`\ell \in \mathbb{N}\times\mathbb{N}`$.
If $`i \lt \lvert G\rvert`$ then

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)\langle i\rangle = G\langle i\rangle .
```

### Proof

We have $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell) = (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$ and
$`i \lt \lvert G\rvert \le \lvert G\rvert + \lvert B\rvert = \lvert G \mathbin{+\!\!+} B\rvert`$, so by
[T.getD_append_left](#t-getD_append_left) the left-hand side is equal to
$`(G \mathbin{+\!\!+} B)\langle i\rangle`$.
Applying [T.getD_append_left](#t-getD_append_left) again to $`i \lt \lvert G\rvert`$ yields
$`G\langle i\rangle`$. ∎

<a id="t-hostM_getD_blk"></a>
## Theorem: entries in the block part of the concatenation $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ (T.hostM_getD_blk)

### Theorem

If $`q \lt \lvert B\rvert`$ then

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)\langle \lvert G\rvert + q\rangle = B\langle q\rangle .
```

### Proof

From $`q \lt \lvert B\rvert`$ we get
$`\lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert = \lvert G \mathbin{+\!\!+} B\rvert`$, so by
[T.getD_append_left](#t-getD_append_left) the left-hand side is equal to
$`(G \mathbin{+\!\!+} B)\langle \lvert G\rvert + q\rangle`$.
Since $`\lvert G\rvert \le \lvert G\rvert + q`$,
[T.getD_append_right](#t-getD_append_right) applies and this is equal to
$`B\langle (\lvert G\rvert + q) - \lvert G\rvert\rangle = B\langle q\rangle`$. ∎

<a id="t-hostM_length"></a>
## Theorem: length of the concatenation $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ (T.hostM_length)

### Theorem

```math
\bigl\lvert G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr\rvert = \lvert G\rvert + \lvert B\rvert + 1 .
```

### Proof

The length of a concatenation is the sum of the lengths, and $`\lvert (\ell)\rvert = 1`$, so

```math
\bigl\lvert (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)\bigr\rvert
  = \bigl(\lvert G\rvert + \lvert B\rvert\bigr) + 1 . \qquad \blacksquare
```

<a id="t-r1ok_copyExp"></a>
## Theorem: the row-1 discipline for a copy expansion (T.r1ok_copyExp)

### Theorem

Let $`G, B \in \mathrm{PairSeq}`$, $`\ell \in \mathbb{N}\times\mathbb{N}`$ and $`n, d_0 \in \mathbb{N}`$, and put
$`E := \mathrm{copyExp}(G,B,d_0,n)`$. Assume the following two.

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

Then $`\mathrm{r1ok}(E)`$ holds.

### Proof

Put $`H := G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$.
Suppose $`j \lt \lvert E\rvert`$ and $`0 \lt E_{0,j}`$.
By [T.copyExp_length](#t-copyExp_length) we have
$`j \lt \lvert G\rvert + n\lvert B\rvert`$. We distinguish cases on the position of $`j`$.

**(A) The case $`j \lt \lvert G\rvert + \lvert B\rvert`$.**
We first show

```math
(\ast)\qquad \forall i \le j,\ E\langle i\rangle = H\langle i\rangle .
```

Take $`i \le j`$.

**(A-1) The case $`i \lt \lvert G\rvert`$.**
By [T.copyExp_getD_pre](#t-copyExp_getD_pre) we have $`E\langle i\rangle = G\langle i\rangle`$, and by
[T.hostM_getD_pre](#t-hostM_getD_pre) we have $`H\langle i\rangle = G\langle i\rangle`$, so
the two sides agree.

**(A-2) The case $`\lvert G\rvert \le i`$.**
From $`i \le j \lt \lvert G\rvert + \lvert B\rvert`$ we get $`i - \lvert G\rvert \lt \lvert B\rvert`$.
Moreover $`0 \lt n`$. Indeed, if $`n = 0`$ then
$`j \lt \lvert G\rvert + 0 \cdot \lvert B\rvert = \lvert G\rvert`$, contradicting
$`\lvert G\rvert \le i \le j`$.
Since $`i = \lvert G\rvert + (0 \cdot \lvert B\rvert + (i - \lvert G\rvert))`$, applying
[T.copyExp_getD_copy](#t-copyExp_getD_copy) with $`k := 0`$ and $`q := i - \lvert G\rvert`$ gives

```math
E\langle i\rangle
  = \bigl(B_{0,\,i - \lvert G\rvert} + 0 \cdot d_0,\ B_{1,\,i - \lvert G\rvert}\bigr)
  = B\langle i - \lvert G\rvert\rangle
```

On the other hand $`i = \lvert G\rvert + (i - \lvert G\rvert)`$, so
[T.hostM_getD_blk](#t-hostM_getD_blk) gives
$`H\langle i\rangle = B\langle i - \lvert G\rvert\rangle`$. Hence the two sides agree.

This proves $`(\ast)`$. By [T.hostM_length](#t-hostM_length) we have
$`\lvert H\rvert = \lvert G\rvert + \lvert B\rvert + 1`$, so
$`j \lt \lvert G\rvert + \lvert B\rvert \lt \lvert H\rvert`$.
Using $`(\ast)`$ with $`i := j`$ gives $`0 \lt H_{0,j}`$.
Applying the hypothesis (hr) to $`j`$, we obtain a witness $`p`$ for column $`j`$ in $`H`$;
that is, $`p \lt j`$, $`H_{0,p} + 1 = H_{0,j}`$,
$`\forall l\ (p \lt l \wedge l \lt j \to H_{0,j} \le H_{0,l})`$ and
$`H_{1,j} \le H_{1,p} + 1`$.
We show that this $`p`$ is also a witness for column $`j`$ in $`E`$.

Condition (1) $`p \lt j`$ carries over unchanged.
From $`p \lt j`$ we get $`p \le j`$, so $`(\ast)`$ applies to $`p`$, giving
$`E\langle p\rangle = H\langle p\rangle`$ and $`E\langle j\rangle = H\langle j\rangle`$.
Hence condition (2) $`E_{0,p} + 1 = E_{0,j}`$ and condition (4) $`E_{1,j} \le E_{1,p} + 1`$ become
exactly the equality and the inequality for $`H`$.
As for condition (3), for $`l`$ with $`p \lt l`$ and $`l \lt j`$ we have $`l \le j`$, so
$`(\ast)`$ gives $`E\langle l\rangle = H\langle l\rangle`$, and
the condition for $`H`$ yields $`E_{0,j} \le E_{0,l}`$ verbatim.

**(B) The case $`\lvert G\rvert + \lvert B\rvert \le j`$.**
First, $`0 \lt \lvert B\rvert`$. Indeed, if $`\lvert B\rvert = 0`$ then
$`j \lt \lvert G\rvert + n \cdot 0 = \lvert G\rvert`$, contradicting
$`\lvert G\rvert \le \lvert G\rvert + \lvert B\rvert \le j`$.
From $`j \lt \lvert G\rvert + n\lvert B\rvert`$ we get $`j - \lvert G\rvert \lt n\lvert B\rvert`$, so by
[T.index_decomp](#t-index_decomp) there exist $`k, q`$ with $`k \lt n`$, $`q \lt \lvert B\rvert`$ and
$`j - \lvert G\rvert = k\lvert B\rvert + q`$.
Since $`\lvert G\rvert \le j`$ we have $`j = \lvert G\rvert + (k\lvert B\rvert + q)`$.
Moreover $`0 \lt k`$. Indeed, if $`k = 0`$ then
$`j = \lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert`$, contradicting
the assumption of case (B).
By [T.copyExp_getD_copy](#t-copyExp_getD_copy),

```math
E\langle j\rangle = \bigl(B_{0,q} + k d_0,\ B_{1,q}\bigr),
```

in particular $`0 \lt B_{0,q} + k d_0`$. We distinguish cases according to the comparison with the
row-$`0`$ values at the positions before $`q`$.

**(B-1) The case $`\forall r \lt q,\ B_{0,q} \le B_{0,r}`$.**
It suffices to apply the hypothesis (hmin) to $`k, q`$. That the resulting $`p`$ satisfies conditions
(1)–(4) is exactly the conclusion of (hmin) (using $`E_{0,j} = B_{0,q} + k d_0`$ and
$`E_{1,j} = B_{1,q}`$).

**(B-2) The case where some $`r \lt q`$ satisfies $`B_{0,r} \lt B_{0,q}`$.**
From $`0 \le B_{0,r} \lt B_{0,q}`$ we get $`0 \lt B_{0,q}`$.
By [T.hostM_length](#t-hostM_length) we have
$`\lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$, and by
[T.hostM_getD_blk](#t-hostM_getD_blk) we have $`H\langle \lvert G\rvert + q\rangle = B\langle q\rangle`$,
in particular $`0 \lt H_{0,\lvert G\rvert + q}`$.
Applying the hypothesis (hr) to the index $`\lvert G\rvert + q`$, we obtain a witness $`p`$ for
column $`\lvert G\rvert + q`$ in $`H`$; that is,

```math
\begin{aligned}
&p \lt \lvert G\rvert + q, \cr
&H_{0,p} + 1 = H_{0,\lvert G\rvert + q} = B_{0,q}, \cr
&\forall l\ \bigl(p \lt l \wedge l \lt \lvert G\rvert + q \to B_{0,q} \le H_{0,l}\bigr), \cr
&B_{1,q} = H_{1,\lvert G\rvert + q} \le H_{1,p} + 1 .
\end{aligned}
```

Here $`\lvert G\rvert + r \le p`$. Indeed, if $`p \lt \lvert G\rvert + r`$, then
from $`r \lt q`$ we get $`\lvert G\rvert + r \lt \lvert G\rvert + q`$, so the third condition applies with
$`l := \lvert G\rvert + r`$, and [T.hostM_getD_blk](#t-hostM_getD_blk) gives
$`B_{0,q} \le H_{0,\lvert G\rvert + r} = B_{0,r}`$, contradicting $`B_{0,r} \lt B_{0,q}`$.

Therefore, putting $`r' := p - \lvert G\rvert`$, we have $`p = \lvert G\rvert + r'`$, and
from $`p \lt \lvert G\rvert + q`$ we get $`r' \lt q`$, hence $`r' \lt \lvert B\rvert`$.
By [T.hostM_getD_blk](#t-hostM_getD_blk) we have $`H\langle p\rangle = B\langle r'\rangle`$, so
the conditions above can be rewritten as

```math
B_{0,r'} + 1 = B_{0,q}, \qquad B_{1,q} \le B_{1,r'} + 1
```

As a witness for column $`j`$ in $`E`$ we take
$`p^{*} := \lvert G\rvert + (k\lvert B\rvert + r')`$.
We check the four conditions of the definition of $`\mathrm{r1ok}`$ (D.r1ok).

**(1)** From $`r' \lt q`$ we get
$`p^{*} = \lvert G\rvert + (k\lvert B\rvert + r') \lt \lvert G\rvert + (k\lvert B\rvert + q) = j`$.

**(2)** Applying [T.copyExp_getD_copy](#t-copyExp_getD_copy) to $`k`$ and $`r'`$ gives
$`E_{0,p^{*}} = B_{0,r'} + k d_0`$. Hence

```math
E_{0,p^{*}} + 1 = B_{0,r'} + k d_0 + 1 = (B_{0,r'} + 1) + k d_0 = B_{0,q} + k d_0 = E_{0,j} .
```

**(3)** Take $`l`$ with $`p^{*} \lt l`$ and $`l \lt j`$.
Since $`\lvert G\rvert + k\lvert B\rvert \le p^{*} \lt l \lt \lvert G\rvert + (k\lvert B\rvert + q)`$,
putting $`rr := l - \lvert G\rvert - k\lvert B\rvert`$ we have
$`l = \lvert G\rvert + (k\lvert B\rvert + rr)`$, $`r' \lt rr`$ and $`rr \lt q`$.
In particular $`rr \lt \lvert B\rvert`$, so
[T.copyExp_getD_copy](#t-copyExp_getD_copy) gives $`E_{0,l} = B_{0,rr} + k d_0`$.
On the other hand $`p = \lvert G\rvert + r' \lt \lvert G\rvert + rr \lt \lvert G\rvert + q`$, so
applying the third condition for $`H`$ with $`l := \lvert G\rvert + rr`$,
[T.hostM_getD_blk](#t-hostM_getD_blk) gives $`B_{0,q} \le B_{0,rr}`$. Hence

```math
E_{0,j} = B_{0,q} + k d_0 \le B_{0,rr} + k d_0 = E_{0,l} .
```

**(4)** By [T.copyExp_getD_copy](#t-copyExp_getD_copy) we have
$`E_{1,p^{*}} = B_{1,r'}`$, and $`E_{1,j} = B_{1,q} \le B_{1,r'} + 1 = E_{1,p^{*}} + 1`$. ∎
