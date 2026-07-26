[← README](README.md) | [English](Wset-2.md) | [Japanese](Wset-2-ja.md) | Wset [1](Wset.md) **2** [3](Wset-3.md) [4](Wset-4.md)

<a id="t-hasParent_shift"></a>
## Theorem: existence of a parent is invariant under the shift of row 0 (T.hasParent_shift)

### Theorem

If $`b \lt \lvert S\rvert`$, then
$`\mathrm{hasParent}(S^{+d}, i, b) \iff \mathrm{hasParent}(S, i, b)`$
($`\mathrm{hasParent}`$ [D.hasParent](Pss.md#d-hasParent), $`S^{+d}`$ [D.shiftr0](Cnf-2.md#d-shiftr0)).

### Proof

By the definition of $`\mathrm{hasParent}`$ (D.hasParent), the two sides read, respectively,
"there exists $`j_0`$ with $`j_0 \to^{S^{+d}}_i b`$ ([D.nextR](Pss.md#d-nextR)), and it is unique"
and "there exists $`j_0`$ with $`j_0 \to^{S}_i b`$, and it is unique".

**(Left to right)** Take $`j_0`$ with $`j_0 \to^{S^{+d}}_i b`$ and such that
every $`y`$ with $`y \to^{S^{+d}}_i b`$ satisfies $`y = j_0`$.
By [T.nextR_shift_iff](Wset.md#t-nextR_shift_iff) we have $`j_0 \to^{S}_i b`$.
Moreover, given $`y`$ with $`y \to^{S}_i b`$, again by
[T.nextR_shift_iff](Wset.md#t-nextR_shift_iff) we have $`y \to^{S^{+d}}_i b`$, hence
$`y = j_0`$. So existence and uniqueness hold on the side of $`S`$ as well.

**(Right to left)** Take $`j_0`$ with $`j_0 \to^{S}_i b`$ and such that
every $`y`$ with $`y \to^{S}_i b`$ satisfies $`y = j_0`$.
By [T.nextR_shift_iff](Wset.md#t-nextR_shift_iff) we have $`j_0 \to^{S^{+d}}_i b`$.
Moreover, given $`y`$ with $`y \to^{S^{+d}}_i b`$, again by
[T.nextR_shift_iff](Wset.md#t-nextR_shift_iff) we have $`y \to^{S}_i b`$, hence
$`y = j_0`$. So existence and uniqueness hold on the side of $`S^{+d}`$ as well. ∎

<a id="t-parent_shift"></a>
## Theorem: the shift of row 0 does not change the parent (T.parent_shift)

### Theorem

If $`b \lt \lvert S\rvert`$, then
$`\mathrm{par}^{S^{+d}}_i(b) = \mathrm{par}^{S}_i(b)`$ ([D.parent](Pss.md#d-parent)).

### Proof

By the definition of $`\mathrm{par}`$ (D.parent), the two sides are the values obtained by
applying $`\varepsilon`$ to the predicates

```math
\varphi(j_0) :\equiv \bigl(j_0 \to^{S^{+d}}_i b\bigr),
\qquad
\psi(j_0) :\equiv \bigl(j_0 \to^{S}_i b\bigr)
```

respectively. Under $`b \lt \lvert S\rvert`$,
[T.nextR_shift_iff](Wset.md#t-nextR_shift_iff) gives
$`\varphi(j_0) \iff \psi(j_0)`$ for every $`j_0`$, so by propositional extensionality
$`\varphi(j_0)`$ and $`\psi(j_0)`$ are the same proposition for each $`j_0`$, and therefore
$`\varphi = \psi`$.
The value of $`\varepsilon`$ is determined by the predicate alone, so the two sides are equal. ∎

<a id="t-oper_shift"></a>
## Theorem: expansion commutes with the shift of row 0 (T.oper_shift)

### Theorem

For every $`M \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) and all $`d, n \in \mathbb{N}`$,

```math
\bigl(M^{+d}\bigr)[n] = \bigl(M[n]\bigr)^{+d} .
```

($`M[n]`$ [D.oper](Pss.md#d-oper))

### Proof

We have $`\lvert M^{+d}\rvert = \lvert M\rvert`$ (the shift maps each element to one element).
Put $`j_1 := \lvert M\rvert - 1`$. Distinguish cases according to whether $`j_1 = 0`$.

**(I) The case $`j_1 = 0`$.** Since $`\lvert M^{+d}\rvert - 1 = j_1 = 0`$ as well, applying
[T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) to both $`M^{+d}`$ and
$`M`$ gives $`(M^{+d})[n] = M^{+d}`$ and $`M[n] = M`$. Hence both sides equal $`M^{+d}`$.

**(II) The case $`j_1 \ne 0`$.** Then $`j_1 \lt \lvert M\rvert`$.
Put $`i_1 := \mathrm{idx}_1(M, j_1)`$ ([D.idx1](Pss.md#d-idx1)); by
[T.idx1_shift](Column-4.md#t-idx1_shift) we have $`\mathrm{idx}_1(M^{+d}, j_1) = i_1`$.
We distinguish further according to whether $`\mathrm{hasParent}(M, i_1, j_1)`$ holds.

**(II-a) The case $`\mathrm{hasParent}(M, i_1, j_1)`$.**
First, $`0 \lt M_{0,j_1}`$ ([D.entry](Pss.md#d-entry)). Indeed, if $`M_{0,j_1} = 0`$, then
[T.no_hasParent_of_row0_zero](Column.md#t-no_hasParent_of_row0_zero) yields a contradiction
with $`\mathrm{hasParent}(M, i_1, j_1)`$. Hence
$`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$.
By [T.entry_shift](Column-4.md#t-entry_shift) we have
$`(M^{+d})_{0,j_1} = M_{0,j_1} + d`$ and $`(M^{+d})_{1,j_1} = M_{1,j_1}`$, so
$`(M^{+d})_{0,j_1} \gt 0`$ and $`\neg\bigl((M^{+d})_{0,j_1} = 0 \wedge (M^{+d})_{1,j_1} = 0\bigr)`$.
Moreover, by [T.hasParent_shift](#t-hasParent_shift) we have $`\mathrm{hasParent}(M^{+d}, i_1, j_1)`$.
Hence branch (d) of the definition of $`M[n]`$ (D.oper) is taken for both $`M`$ and $`M^{+d}`$,
and [T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) applies.

By [T.parent_shift](#t-parent_shift) we have
$`j_0 := \mathrm{par}^{M}_{i_1}(j_1) = \mathrm{par}^{M^{+d}}_{i_1}(j_1)`$, and by
[T.parent_nextR](Decrease.md#t-parent_nextR) and
[T.nextR_index_lt](Decrease.md#t-nextR_index_lt) we have $`j_0 \lt j_1`$, in particular
$`j_0 \lt \lvert M\rvert`$. Hence, again by
[T.entry_shift](Column-4.md#t-entry_shift), $`(M^{+d})_{0,j_0} = M_{0,j_0} + d`$, and
the value of $`d_0`$ is the same for both. Indeed, for $`0 \lt i_1`$

```math
(M^{+d})_{0,j_1} - (M^{+d})_{0,j_0} = (M_{0,j_1} + d) - (M_{0,j_0} + d) = M_{0,j_1} - M_{0,j_0}
```

(the $`d`$ cancels on the right-hand side even for truncated subtraction), while for
$`i_1 = 0`$ both are $`0`$. We write $`d_0`$ for this common value.

The two sides given by [T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) are

```math
M[n] = (M_0,\dots,M_{j_0-1}) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1},
```
```math
\begin{aligned}
\bigl(M^{+d}\bigr)[n]
  &= \bigl((M^{+d})_0,\dots,(M^{+d})_{j_0-1}\bigr) \mathbin{+\!\!+} B'_0
     \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B'_{n-1}, \qquad \cr
B'_k
  &= \bigl(\,((M^{+d})_{0,j} + k\,d_0,\ (M^{+d})_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
\end{aligned}
```

For the prefix,
$`\bigl((M^{+d})_0,\dots,(M^{+d})_{j_0-1}\bigr) = (M_0,\dots,M_{j_0-1})^{+d}`$
(the shift is a map applied to each element, and it commutes with taking the first
$`j_0`$ elements). For the blocks,
[T.entry_shift](Column-4.md#t-entry_shift) applies in the range
$`j_0 \le j \lt j_1 \lt \lvert M\rvert`$ and gives

```math
\bigl((M^{+d})_{0,j} + k\,d_0,\ (M^{+d})_{1,j}\bigr)
  = \bigl(M_{0,j} + d + k\,d_0,\ M_{1,j}\bigr)
  = \bigl((M_{0,j} + k\,d_0) + d,\ M_{1,j}\bigr)
```

so that $`B'_k = (B_k)^{+d}`$. Since concatenation commutes with the shift, the two sides are equal.

**(II-b) The case $`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$.**
By [T.hasParent_shift](#t-hasParent_shift) we have
$`\neg\,\mathrm{hasParent}(M^{+d}, i_1, j_1)`$.
For $`M`$: if $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ holds, then by
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero), and if it does not, then by
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent); in either case
$`M[n] = \mathrm{Pred}\,M`$ ([D.Pred](Pss.md#d-Pred)). Applying the same two theorems to $`M^{+d}`$ gives
$`(M^{+d})[n] = \mathrm{Pred}(M^{+d})`$.

From $`j_1 = \lvert M\rvert - 1 \ne 0`$ we get $`2 \le \lvert M\rvert = \lvert M^{+d}\rvert`$, so
the second case of the definition of $`\mathrm{Pred}`$ (D.Pred) is taken for both, and

```math
\mathrm{Pred}\,M = \mathrm{dropLast}\,M,
\qquad
\mathrm{Pred}(M^{+d}) = \mathrm{dropLast}(M^{+d})
```

The shift is a map applied to each element, so it commutes with dropping the last element and
$`\mathrm{dropLast}(M^{+d}) = (\mathrm{dropLast}\,M)^{+d}`$. Hence the two sides are equal. ∎

<a id="t-domT_shift"></a>
## Theorem: $`\mathrm{domT}`$ is invariant under the shift of row 0 (T.domT_shift)

### Theorem

$`\mathrm{domT}(M^{+d}, m) \iff \mathrm{domT}(M, m)`$ ([D.domT](Wset.md#d-domT)).

### Proof

Distinguish cases on the constructor of $`M`$.

**(a) The case $`M = ()`$.** We have $`()^{+d} = ()`$. Also $`\lvert ()\rvert - 1 = 0`$ and, by
the definition of $`M_{i,j}`$ (D.entry), $`()_{1,0} = 0`$, so the first conjunct
$`()_{1,0} = m+1`$ in the definition of $`\mathrm{domT}`$ (D.domT) is false.
Hence both sides are false and the equivalence holds.

**(b) The case $`M = p :: L`$.** Since $`\lvert M^{+d}\rvert = \lvert M\rvert`$,
the index read on both sides is the same $`j_1 := \lvert M\rvert - 1`$, and $`j_1 \lt \lvert M\rvert`$.
Compare the two conjuncts in the definition of $`\mathrm{domT}`$ (D.domT) one by one.
The first conjuncts are equivalent because [T.entry_shift](Column-4.md#t-entry_shift) gives
$`(M^{+d})_{1,j_1} = M_{1,j_1}`$, and
the second conjuncts are equivalent because [T.hasParent_shift](#t-hasParent_shift) gives
$`\mathrm{hasParent}(M^{+d}, 1, j_1) \iff \mathrm{hasParent}(M, 1, j_1)`$. ∎

<a id="t-natDom_shift"></a>
## Theorem: $`\mathrm{natDom}`$ is invariant under the shift of row 0 (T.natDom_shift)

### Theorem

$`\mathrm{natDom}(M^{+d}) \iff \mathrm{natDom}(M)`$ ([D.natDom](Wset.md#d-natDom)).

### Proof

By the definition of $`\mathrm{natDom}`$ (D.natDom), the left-hand side reads
$`\forall m,\ \neg\,\mathrm{domT}(M^{+d}, m)`$ and the right-hand side reads $`\forall m,\ \neg\,\mathrm{domT}(M, m)`$.

Assume the left-hand side and take $`m`$. If $`\mathrm{domT}(M,m)`$, then
[T.domT_shift](#t-domT_shift) gives $`\mathrm{domT}(M^{+d}, m)`$, contradicting the left-hand side.
Hence $`\neg\,\mathrm{domT}(M,m)`$.

Assume the right-hand side and take $`m`$. If $`\mathrm{domT}(M^{+d},m)`$, then
[T.domT_shift](#t-domT_shift) gives $`\mathrm{domT}(M, m)`$, contradicting the right-hand side.
Hence $`\neg\,\mathrm{domT}(M^{+d},m)`$. ∎

<a id="t-graft_shift"></a>
## Theorem: grafting commutes with the shift of row 0 (T.graft_shift)

### Theorem

If $`M \ne ()`$, then for all $`z \in \mathrm{PairSeq}`$ and $`d \in \mathbb{N}`$

```math
\mathrm{graft}\bigl(M^{+d},\ z\bigr) = \bigl(\mathrm{graft}(M, z)\bigr)^{+d} .
```

($`\mathrm{graft}`$ [D.graft](Wset.md#d-graft))

### Proof

From $`M \ne ()`$ we get $`0 \lt \lvert M\rvert`$, hence $`j_1 := \lvert M\rvert - 1 \lt \lvert M\rvert`$.
Since $`\lvert M^{+d}\rvert = \lvert M\rvert`$, the index of the last element of $`M^{+d}`$ is also $`j_1`$.
By the definition of $`\mathrm{graft}`$ (D.graft),

```math
\mathrm{graft}\bigl(M^{+d}, z\bigr)
  = \mathrm{dropLast}\bigl(M^{+d}\bigr) \mathbin{+\!\!+} z^{+(M^{+d})_{0,j_1}} .
```

By [T.entry_shift](Column-4.md#t-entry_shift) we have $`(M^{+d})_{0,j_1} = M_{0,j_1} + d`$, and
the shift commutes with dropping the last element, so
$`\mathrm{dropLast}(M^{+d}) = (\mathrm{dropLast}\,M)^{+d}`$. Hence

```math
\mathrm{graft}\bigl(M^{+d}, z\bigr)
  = (\mathrm{dropLast}\,M)^{+d} \mathbin{+\!\!+} z^{+(M_{0,j_1} + d)} .
```

On the other hand,

```math
\bigl(\mathrm{graft}(M,z)\bigr)^{+d}
  = \bigl(\mathrm{dropLast}\,M \mathbin{+\!\!+} z^{+M_{0,j_1}}\bigr)^{+d}
  = (\mathrm{dropLast}\,M)^{+d} \mathbin{+\!\!+} \bigl(z^{+M_{0,j_1}}\bigr)^{+d}
```

(the shift commutes with concatenation). An element $`q`$ of $`z`$ is mapped, in the second
summand of the right-hand side, to $`\bigl((q_1 + M_{0,j_1}) + d,\ q_2\bigr)`$, and in the second
summand of the left-hand side, to $`\bigl(q_1 + (M_{0,j_1} + d),\ q_2\bigr)`$. By the
associativity of addition on $`\mathbb{N}`$ these two are equal. Hence the two sides are equal. ∎

<a id="t-W_shift"></a>
## Theorem: invariance of $`W_u`$ under the shift of row 0 (T.W_shift)

### Theorem

If $`M \in W_u`$ ([D.W](Wset.md#d-W)), then $`M^{+d} \in W_u`$ for every $`d \in \mathbb{N}`$.

### Proof

Fix $`d`$ and put

```math
Y := \{\, N \in \mathrm{PairSeq} \mid N^{+d} \in W_u \,\}
```

By [T.A2'](Wset.md#t-A2'), in order to prove $`W_u \subseteq Y`$ it suffices to prove that,
for every $`N`$, if $`N \in A_u(Y)`$ ([D.Aop](Wset.md#d-Aop)) then $`N \in Y`$, that is,
$`N^{+d} \in W_u`$.
By [T.A1_intro](Wset.md#t-A1_intro) this reduces to $`N^{+d} \in A_u(W_u)`$.
Distinguish cases according to the three branches of the definition of $`A_u`$ (D.Aop).

**Branch (1): the case $`\lvert N\rvert \le 1 \wedge N_{1,0} = 0`$.**
We have $`\lvert N^{+d}\rvert = \lvert N\rvert \le 1`$. Also $`(N^{+d})_{1,0} = N_{1,0} = 0`$.
Indeed, if $`N = ()`$ then $`N^{+d} = ()`$ and both sides are $`0`$ (a read out of range in D.entry),
while if $`N = p :: L`$ then the head of $`N^{+d}`$ is $`(p_1 + d,\ p_2)`$, whose second entry is $`p_2 = N_{1,0}`$.
Hence $`N^{+d}`$ satisfies branch (1).

**Branch (2): the case $`\mathrm{natDom}(N) \wedge \forall n \ge 1,\ N[n] \in Y`$.**
By [T.natDom_shift](#t-natDom_shift) we have $`\mathrm{natDom}(N^{+d})`$.
Take $`n \ge 1`$; by [T.oper_shift](#t-oper_shift) we have
$`(N^{+d})[n] = (N[n])^{+d}`$, and $`N[n] \in Y`$, that is, $`(N[n])^{+d} \in W_u`$.
Hence $`N^{+d}`$ satisfies branch (2).

**Branch (3), that is, the case where there is an $`m`$ with $`m \lt u`$, $`\mathrm{domT}(N,m)`$ and
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(N,z) \in Y`$
($`\mathrm{based}`$ [D.based](Wset.md#d-based)).**
By [T.domT_shift](#t-domT_shift) we have $`\mathrm{domT}(N^{+d}, m)`$.
Moreover $`N \ne ()`$ (if $`N = ()`$, then [T.not_domT_nil](Wset.md#t-not_domT_nil)
contradicts $`\mathrm{domT}(N,m)`$). If $`z \in W_m`$ satisfies $`\mathrm{based}(z)`$, then by
[T.graft_shift](#t-graft_shift)

```math
\mathrm{graft}\bigl(N^{+d}, z\bigr) = \bigl(\mathrm{graft}(N,z)\bigr)^{+d}
```

and since $`\mathrm{graft}(N,z) \in Y`$ this is an element of $`W_u`$.
Hence $`N^{+d}`$ satisfies branch (3) with the same $`m`$.

This proves $`W_u \subseteq Y`$, and from $`M \in W_u`$ we obtain $`M^{+d} \in W_u`$. ∎

<a id="t-split_lastMin"></a>
## Theorem: decomposition by the last top-level tree (T.split_lastMin)

### Theorem

If $`M \ne ()`$, then there exist $`A, P \in \mathrm{PairSeq}`$ with

```math
M = A \mathbin{+\!\!+} P,
\qquad P \ne (),
\qquad \mathrm{rsum}(A, P),
\qquad \forall p \in \mathrm{tail}\,P,\ P_{0,0} \lt p_1 .
```

($`\mathrm{rsum}`$ [D.rsum](Wset.md#d-rsum))

Here $`\mathrm{tail}\,P`$ is the sequence obtained from $`P`$ by dropping its first element.

### Proof

We argue by induction on the construction of sequences from the end. That is, every element of
$`\mathrm{PairSeq}`$ is either $`()`$ or can be written as $`M' \mathbin{+\!\!+} (q)`$ for some $`M'`$ and some pair $`q`$,
and in the latter case $`\lvert M'\rvert \lt \lvert M' \mathbin{+\!\!+} (q)\rvert`$. The induction predicate is

```math
\Phi(M) :\equiv M \ne () \to \exists A, P,\
  \bigl(M = A \mathbin{+\!\!+} P \wedge P \ne () \wedge \mathrm{rsum}(A,P)
    \wedge \forall p \in \mathrm{tail}\,P,\ P_{0,0} \lt p_1\bigr).
```

- **Base case** $`M = ()`$: the antecedent $`M \ne ()`$ is false, so $`\Phi(())`$ holds.

**Inductive step** $`M = M' \mathbin{+\!\!+} (q)`$: assume $`\Phi(M')`$.
Distinguish cases according to whether $`M'`$ is empty.

**(a) The case $`M' = ()`$.** Take $`A := ()`$ and $`P := (q)`$.
Then $`M = () \mathbin{+\!\!+} (q)`$ and $`P \ne ()`$.
We have $`P_{0,0} = q_1`$, and the only element of $`() \mathbin{+\!\!+} (q)`$ is $`q`$, for which $`q_1 \le q_1`$ holds, so
$`\mathrm{rsum}(A,P)`$. Since $`\mathrm{tail}\,(q) = ()`$, the last condition has no element to satisfy and holds.

**(b) The case $`M' \ne ()`$.** By the induction hypothesis $`\Phi(M')`$, take $`A', P'`$ with
$`M' = A' \mathbin{+\!\!+} P'`$, $`P' \ne ()`$, $`\mathrm{rsum}(A',P')`$ and
$`\forall p \in \mathrm{tail}\,P',\ P'_{0,0} \lt p_1`$.
Distinguish cases according to the comparison between $`q_1`$ and $`P'_{0,0}`$.

**(b-1) The case $`q_1 \le P'_{0,0}`$.** Take $`A := M'`$ and $`P := (q)`$.
Then $`M = M' \mathbin{+\!\!+} (q)`$ and $`P \ne ()`$, and $`P_{0,0} = q_1`$.
Take $`p \in M' \mathbin{+\!\!+} (q)`$. If $`p \in M' = A' \mathbin{+\!\!+} P'`$, then
$`\mathrm{rsum}(A',P')`$ gives $`P'_{0,0} \le p_1`$, which together with the hypothesis $`q_1 \le P'_{0,0}`$ gives
$`q_1 \le p_1`$. If $`p = q`$, then $`q_1 \le q_1`$. Hence $`\mathrm{rsum}(A,P)`$.
Since $`\mathrm{tail}\,(q) = ()`$, the last condition holds.

**(b-2) The case $`P'_{0,0} \lt q_1`$.** Take $`A := A'`$ and $`P := P' \mathbin{+\!\!+} (q)`$.
By the associativity of concatenation,
$`M = (A' \mathbin{+\!\!+} P') \mathbin{+\!\!+} (q) = A' \mathbin{+\!\!+} (P' \mathbin{+\!\!+} (q))`$, and
$`P \ne ()`$. Since $`P' \ne ()`$ we can write $`P' = p_0 :: P''`$, and the head of
$`P' \mathbin{+\!\!+} (q) = p_0 :: (P'' \mathbin{+\!\!+} (q))`$ is $`p_0`$ as well. Hence

```math
P_{0,0} = (p_0)_1 = P'_{0,0} .
```

We prove $`\mathrm{rsum}(A,P)`$. Take $`p \in A' \mathbin{+\!\!+} (P' \mathbin{+\!\!+} (q))`$.
If $`p \in A'`$, then $`\mathrm{rsum}(A',P')`$ gives $`P'_{0,0} \le p_1`$.
If $`p \in P'`$, then again $`\mathrm{rsum}(A',P')`$ gives $`P'_{0,0} \le p_1`$.
If $`p = q`$, then the hypothesis $`P'_{0,0} \lt q_1`$ gives $`P'_{0,0} \le q_1`$.
In every case $`P_{0,0} = P'_{0,0} \le p_1`$.

We prove the last condition. We have $`\mathrm{tail}\,P = P'' \mathbin{+\!\!+} (q)`$.
If $`p \in P''`$, then $`P'' = \mathrm{tail}\,P'`$, so the condition obtained from the induction hypothesis gives
$`P'_{0,0} \lt p_1`$. If $`p = q`$, this is the hypothesis $`P'_{0,0} \lt q_1`$ itself.
Since $`P_{0,0} = P'_{0,0}`$, in every case $`P_{0,0} \lt p_1`$. ∎

<a id="t-map_sub_add"></a>
## Theorem: composition of a downward and an upward shift (T.map_sub_add)

### Theorem

Let $`c \in \mathbb{N}`$ and $`X \in \mathrm{PairSeq}`$, and suppose $`\forall p \in X,\ c \le p_1`$. Then

```math
\bigl(X^{-c}\bigr)^{+c} = X .
```

Here $`X^{-c}`$ ([D.shiftl0](ArgDom-2.md#d-shiftl0)) is the sequence obtained from $`X`$ by
subtracting $`c`$ uniformly, by truncated subtraction, from the first entry of every pair.

### Proof

Both $`X^{-c}`$ and $`(X^{-c})^{+c}`$ are obtained from $`X`$ by mapping its elements one by one,
so the three sequences have the same length. Looking at what an element $`q`$ of $`X`$ becomes at
the corresponding position of $`(X^{-c})^{+c}`$, we get

```math
q \longmapsto (q_1 - c,\ q_2) \longmapsto \bigl((q_1 - c) + c,\ q_2\bigr)
```

By hypothesis $`c \le q_1`$, so truncated subtraction gives $`(q_1 - c) + c = q_1`$, and
this pair equals $`(q_1, q_2) = q`$. Hence the elements at corresponding positions all agree, and
the two sides are equal. ∎

<a id="t-rsum_decomp"></a>
## Theorem: the top-level decomposition expressed by a shift (T.rsum_decomp)

### Theorem

If $`\mathrm{rsum}(A,P)`$, then, with $`c := P_{0,0}`$,

```math
\bigl(A^{-c} \mathbin{+\!\!+} P^{-c}\bigr)^{+c} = A \mathbin{+\!\!+} P .
```

### Proof

The shift is a map applied to each element, so it commutes with concatenation and

```math
\bigl(A^{-c} \mathbin{+\!\!+} P^{-c}\bigr)^{+c} = \bigl(A^{-c}\bigr)^{+c} \mathbin{+\!\!+} \bigl(P^{-c}\bigr)^{+c}
```

The definition of $`\mathrm{rsum}(A,P)`$ (D.rsum) is
$`\forall p \in A \mathbin{+\!\!+} P,\ c \le p_1`$, so in particular
$`\forall p \in A,\ c \le p_1`$ and $`\forall p \in P,\ c \le p_1`$ hold.
Applying [T.map_sub_add](#t-map_sub_add) with $`X := A`$ and with $`X := P`$ gives
$`(A^{-c})^{+c} = A`$ and $`(P^{-c})^{+c} = P`$. ∎

<a id="t-entry_sub_zero"></a>
## Theorem: the row-0 value at the head of a lowered sequence is 0 (T.entry_sub_zero)

### Theorem

If $`P \ne ()`$, then, with $`c := P_{0,0}`$, $`\bigl(P^{-c}\bigr)_{0,0} = 0`$.

### Proof

From $`P \ne ()`$ we can write $`P = p_0 :: P'`$. By the definition of $`M_{i,j}`$ (D.entry),
$`c = P_{0,0} = (p_0)_1`$. The head of $`P^{-c}`$ is
$`\bigl((p_0)_1 - c,\ (p_0)_2\bigr) = \bigl((p_0)_1 - (p_0)_1,\ (p_0)_2\bigr) = \bigl(0,\ (p_0)_2\bigr)`$,
so, again by D.entry, $`(P^{-c})_{0,0} = 0`$. ∎

<a id="t-oper_append_gen"></a>
## Theorem: expansion along the top-level decomposition commutes with prefixing (T.oper_append_gen)

### Theorem

If $`2 \le \lvert P\rvert`$ and $`\mathrm{rsum}(A,P)`$, then for every $`n`$

```math
(A \mathbin{+\!\!+} P)[n] = A \mathbin{+\!\!+} P[n] .
```

### Proof

Put $`c := P_{0,0}`$, $`\hat A := A^{-c}`$ and $`\hat P := P^{-c}`$.
From $`2 \le \lvert P\rvert`$ we get $`P \ne ()`$, and the following five statements hold.

1. $`(\hat P)_{0,0} = 0`$. By [T.entry_sub_zero](#t-entry_sub_zero).
2. $`2 \le \lvert \hat P\rvert`$. The shift does not change the length, so $`\lvert \hat P\rvert = \lvert P\rvert`$.
3. $`(\hat A \mathbin{+\!\!+} \hat P)^{+c} = A \mathbin{+\!\!+} P`$. By [T.rsum_decomp](#t-rsum_decomp).
4. $`(\hat P)^{+c} = P`$. Since $`\mathrm{rsum}(A,P)`$ gives $`\forall p \in P,\ c \le p_1`$, this is
   [T.map_sub_add](#t-map_sub_add).
5. $`(\hat A)^{+c} = A`$. Since $`\mathrm{rsum}(A,P)`$ gives $`\forall p \in A,\ c \le p_1`$, this is
   [T.map_sub_add](#t-map_sub_add).

Using these we compute.

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

Here (6) is [T.oper_shift](#t-oper_shift) (from left to right in the second line, from right to
left in the sixth line), and (7) is
[T.oper_append_right](Column-2.md#t-oper_append_right), whose two hypotheses
$`2 \le \lvert \hat P\rvert`$ and $`(\hat P)_{0,0} = 0`$ are (2) and (1).
(8) holds because the shift commutes with concatenation. ∎

<a id="t-graft_append"></a>
## Theorem: grafting commutes with prefixing (T.graft_append)

### Theorem

If $`P \ne ()`$, then for all $`A, z \in \mathrm{PairSeq}`$

```math
\mathrm{graft}(A \mathbin{+\!\!+} P,\ z) = A \mathbin{+\!\!+} \mathrm{graft}(P, z) .
```

### Proof

From $`P \ne ()`$ we get $`0 \lt \lvert P\rvert`$, so

```math
\lvert A \mathbin{+\!\!+} P\rvert - 1 = \lvert A\rvert + \lvert P\rvert - 1 = \lvert A\rvert + (\lvert P\rvert - 1)
```

Applying [T.entry_append_right](Column.md#t-entry_append_right) with
$`i := 0`$ and $`j := \lvert P\rvert - 1`$ gives

```math
(A \mathbin{+\!\!+} P)_{0,\ \lvert A \mathbin{+\!\!+} P\rvert - 1} = P_{0,\ \lvert P\rvert - 1}
```

Moreover, from $`P \ne ()`$ we have
$`\mathrm{dropLast}(A \mathbin{+\!\!+} P) = A \mathbin{+\!\!+} \mathrm{dropLast}\,P`$.
Hence, by the definition of $`\mathrm{graft}`$ (D.graft),

```math
\begin{aligned}
\mathrm{graft}(A \mathbin{+\!\!+} P, z)
  &= \bigl(A \mathbin{+\!\!+} \mathrm{dropLast}\,P\bigr) \mathbin{+\!\!+} z^{+P_{0,\lvert P\rvert-1}} \cr
  &= A \mathbin{+\!\!+} \bigl(\mathrm{dropLast}\,P \mathbin{+\!\!+} z^{+P_{0,\lvert P\rvert-1}}\bigr) \cr
  &= A \mathbin{+\!\!+} \mathrm{graft}(P,z)
\end{aligned}
```

(the middle equality is the associativity of concatenation). ∎

<a id="t-hasParent_append_gen"></a>
## Theorem: existence of a parent along the top-level decomposition is prefix-invariant (T.hasParent_append_gen)

### Theorem

If $`j \lt \lvert P\rvert`$ and $`\mathrm{rsum}(A,P)`$, then

```math
\mathrm{hasParent}\bigl(A \mathbin{+\!\!+} P,\ i,\ \lvert A\rvert + j\bigr) \iff \mathrm{hasParent}(P, i, j).
```

### Proof

From $`j \lt \lvert P\rvert`$ we get $`P \ne ()`$.
Put $`c := P_{0,0}`$, $`\hat A := A^{-c}`$ and $`\hat P := P^{-c}`$.
The shift does not change the length, so $`\lvert \hat A\rvert = \lvert A\rvert`$ and $`\lvert \hat P\rvert = \lvert P\rvert`$.
By [T.entry_sub_zero](#t-entry_sub_zero) we have $`(\hat P)_{0,0} = 0`$,
by [T.rsum_decomp](#t-rsum_decomp) we have $`(\hat A \mathbin{+\!\!+} \hat P)^{+c} = A \mathbin{+\!\!+} P`$, and
by [T.map_sub_add](#t-map_sub_add) we have $`(\hat P)^{+c} = P`$. We proceed in three steps.

**Step 1.** We prove the following.

```math
\mathrm{hasParent}(A \mathbin{+\!\!+} P,\ i,\ \lvert A\rvert + j)
\iff \mathrm{hasParent}(\hat A \mathbin{+\!\!+} \hat P,\ i,\ \lvert \hat A\rvert + j).
```

We have $`\lvert \hat A \mathbin{+\!\!+} \hat P\rvert = \lvert A\rvert + \lvert P\rvert`$ and
$`j \lt \lvert P\rvert`$, so $`\lvert A\rvert + j \lt \lvert \hat A \mathbin{+\!\!+} \hat P\rvert`$.
Since $`(\hat A \mathbin{+\!\!+} \hat P)^{+c} = A \mathbin{+\!\!+} P`$, it suffices to apply
[T.hasParent_shift](#t-hasParent_shift) with $`S := \hat A \mathbin{+\!\!+} \hat P`$, $`d := c`$ and
$`b := \lvert A\rvert + j`$ (recall $`\lvert \hat A\rvert = \lvert A\rvert`$).

**Step 2.** We prove the following.

```math
\mathrm{hasParent}(\hat A \mathbin{+\!\!+} \hat P,\ i,\ \lvert \hat A\rvert + j)
\iff \mathrm{hasParent}(\hat P,\ i,\ j).
```

Distinguish cases according to whether $`(\hat P)_{0,j}`$ is $`0`$.

**The case $`(\hat P)_{0,j} = 0`$.** By [T.entry_append_right](Column.md#t-entry_append_right),
$`(\hat A \mathbin{+\!\!+} \hat P)_{0,\lvert \hat A\rvert + j} = (\hat P)_{0,j} = 0`$.
Applying [T.no_hasParent_of_row0_zero](Column.md#t-no_hasParent_of_row0_zero) to
$`\hat A \mathbin{+\!\!+} \hat P`$ makes the left-hand side false, and applying the same theorem to $`\hat P`$
makes the right-hand side false as well. Hence the equivalence holds.

**The case $`(\hat P)_{0,j} \ne 0`$.** By the same equality,
$`0 \lt (\hat A \mathbin{+\!\!+} \hat P)_{0,\lvert \hat A\rvert + j}`$.
Together with $`(\hat P)_{0,0} = 0`$, this makes
[T.hasParent_append_right](Column.md#t-hasParent_append_right) applicable, and it gives the equivalence.

**Step 3: $`\mathrm{hasParent}(\hat P, i, j) \iff \mathrm{hasParent}(P, i, j)`$.**
We have $`j \lt \lvert P\rvert = \lvert \hat P\rvert`$ and $`(\hat P)^{+c} = P`$, so it suffices to apply
[T.hasParent_shift](#t-hasParent_shift) with $`S := \hat P`$, $`d := c`$ and $`b := j`$.

Chaining the three steps gives the conclusion. ∎

<a id="t-domT_append"></a>
## Theorem: $`\mathrm{domT}`$ is prefix-invariant (T.domT_append)

### Theorem

If $`P \ne ()`$ and $`\mathrm{rsum}(A,P)`$, then

```math
\mathrm{domT}(A \mathbin{+\!\!+} P,\ m) \iff \mathrm{domT}(P, m).
```

### Proof

From $`P \ne ()`$ we get $`0 \lt \lvert P\rvert`$, so

```math
\lvert A \mathbin{+\!\!+} P\rvert - 1 = \lvert A\rvert + (\lvert P\rvert - 1)
```

Compare the two conjuncts in the definition of $`\mathrm{domT}`$ (D.domT) one by one.

For the first conjunct, applying [T.entry_append_right](Column.md#t-entry_append_right) with
$`i := 1`$ and $`j := \lvert P\rvert - 1`$ gives

```math
(A \mathbin{+\!\!+} P)_{1,\ \lvert A \mathbin{+\!\!+} P\rvert - 1} = P_{1,\ \lvert P\rvert - 1}
```

so that $`(A \mathbin{+\!\!+} P)_{1,\lvert A \mathbin{+\!\!+} P\rvert-1} = m+1`$ and
$`P_{1,\lvert P\rvert-1} = m+1`$ are equivalent.

For the second conjunct, since $`\lvert P\rvert - 1 \lt \lvert P\rvert`$, applying
[T.hasParent_append_gen](#t-hasParent_append_gen) with $`i := 1`$ and $`j := \lvert P\rvert - 1`$
gives

```math
\mathrm{hasParent}\bigl(A \mathbin{+\!\!+} P,\ 1,\ \lvert A \mathbin{+\!\!+} P\rvert - 1\bigr)
  \iff \mathrm{hasParent}\bigl(P,\ 1,\ \lvert P\rvert - 1\bigr)
```

so that their negations are equivalent as well. ∎

<a id="t-natDom_append"></a>
## Theorem: $`\mathrm{natDom}`$ is prefix-invariant (T.natDom_append)

### Theorem

If $`P \ne ()`$ and $`\mathrm{rsum}(A,P)`$, then
$`\mathrm{natDom}(A \mathbin{+\!\!+} P) \iff \mathrm{natDom}(P)`$.

### Proof

By the definition of $`\mathrm{natDom}`$ (D.natDom), the left-hand side reads
$`\forall m,\ \neg\,\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$ and the right-hand side reads $`\forall m,\ \neg\,\mathrm{domT}(P,m)`$.

Assume the left-hand side and take $`m`$. If $`\mathrm{domT}(P,m)`$, then
[T.domT_append](#t-domT_append) gives $`\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$, contradicting the left-hand side.
Hence $`\neg\,\mathrm{domT}(P,m)`$.

Assume the right-hand side and take $`m`$. If $`\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$, then
[T.domT_append](#t-domT_append) gives $`\mathrm{domT}(P, m)`$, contradicting the right-hand side.
Hence $`\neg\,\mathrm{domT}(A \mathbin{+\!\!+} P, m)`$. ∎

<a id="d-XA"></a>
## Definition: residual set under prefixing (D.XA)

For $`A \in \mathrm{PairSeq}`$ and $`X \subseteq \mathrm{PairSeq}`$ put

```math
X^{(A)} := \{\, B \in \mathrm{PairSeq} \mid \mathrm{rsum}(A,B) \to A \mathbin{+\!\!+} B \in X \,\} .
```

<a id="t-entry_zero_headD"></a>
## Theorem: the row-0 value at the head (T.entry_zero_headD)

### Theorem

For every $`X \in \mathrm{PairSeq}`$ we have $`X_{0,0} = (\mathrm{hd}\,X)_1`$.
Here $`\mathrm{hd}\,X`$ is the head element of $`X`$, taken to be $`(0,0)`$ when $`X = ()`$.

### Proof

Distinguish cases on the constructor of $`X`$.

- The case $`X = ()`$. By the definition of $`M_{i,j}`$ (D.entry) we have $`()_{0,0} = 0`$
  (the index $`0`$ is out of range, so $`(0,0)`$ is read). Also $`\mathrm{hd}\,() = (0,0)`$, whose first entry is $`0`$.

- The case $`X = p :: X'`$. By D.entry we have $`X_{0,0} = p_1`$. Also $`\mathrm{hd}\,X = p`$, whose
  first entry is $`p_1`$. ∎

<a id="t-oper_head_eq"></a>
## Theorem: expansion does not change the row-0 value at the head (T.oper_head_eq)

### Theorem

If $`1 \le n`$, then $`\bigl(N[n]\bigr)_{0,0} = N_{0,0}`$.

### Proof

Distinguish cases according to whether $`1 \lt \lvert N\rvert`$.

- The case $`1 \lt \lvert N\rvert`$. Applying [T.entry_zero_headD](#t-entry_zero_headD) with
  $`X := N[n]`$ and with $`X := N`$, what has to be proved is
  $`\bigl(\mathrm{hd}(N[n])\bigr)_1 = (\mathrm{hd}\,N)_1`$.
  Since [T.oper_headD](Column-2.md#t-oper_headD) gives $`\mathrm{hd}(N[n]) = \mathrm{hd}\,N`$
  under $`1 \lt \lvert N\rvert`$ and $`1 \le n`$, the first entries are equal as well.

- The case $`\neg(1 \lt \lvert N\rvert)`$. Then $`\lvert N\rvert \le 1`$, that is, $`\lvert N\rvert - 1 = 0`$,
  so [T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) gives $`N[n] = N`$, and
  the two sides are identical. ∎

<a id="t-entry_pair_mem"></a>
## Theorem: the $`j`$-th entry of a sequence is an element of the sequence (T.entry_pair_mem)

### Theorem

If $`j \lt \lvert N\rvert`$, then $`(N_{0,j},\ N_{1,j}) \in N`$.

### Proof

By the definition of $`M_{i,j}`$ (D.entry) we have $`N_{0,j} = \pi_1\bigl(N\langle j\rangle\bigr)`$ and
$`N_{1,j} = \pi_2\bigl(N\langle j\rangle\bigr)`$, so

```math
(N_{0,j},\ N_{1,j}) = N\langle j\rangle
```

By the hypothesis $`j \lt \lvert N\rvert`$, the term $`N\langle j\rangle`$ of D.entry falls under the
first case and $`N\langle j\rangle = N_j`$, the $`j`$-th element of $`N`$. The $`j`$-th element of a
sequence is an element of that sequence when $`j \lt \lvert N\rvert`$. ∎

<a id="t-oper_mem_ge"></a>
## Theorem: expansion preserves a lower bound on the row-0 values (T.oper_mem_ge)

### Theorem

If $`\forall p \in N,\ c \le p_1`$, then $`\forall p \in N[n],\ c \le p_1`$ for every $`n`$.

### Proof

Put $`j_1 := \lvert N\rvert - 1`$. Distinguish cases according to whether $`j_1 = 0`$.

**(I) The case $`j_1 = 0`$.** [T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) gives
$`N[n] = N`$, so this is the hypothesis itself.

**(II) The case $`j_1 \ne 0`$.** Put $`i_1 := \mathrm{idx}_1(N, j_1)`$ and distinguish
according to whether $`\mathrm{hasParent}(N, i_1, j_1)`$ holds.

**(II-a) The case $`\mathrm{hasParent}(N, i_1, j_1)`$.**
If $`N_{0,j_1} = 0`$, then
[T.no_hasParent_of_row0_zero](Column.md#t-no_hasParent_of_row0_zero) yields a contradiction, so
$`0 \lt N_{0,j_1}`$, and in particular $`\neg(N_{0,j_1} = 0 \wedge N_{1,j_1} = 0)`$.
Hence [T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold) applies and, with
$`j_0 := \mathrm{par}^N_{i_1}(j_1)`$,

```math
N[n] = (N_0,\dots,N_{j_0-1}) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(N_{0,j} + k\,d_0,\ N_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
```

Take $`p \in N[n]`$ and distinguish according to which part $`p`$ belongs to.

- The case $`p \in (N_0,\dots,N_{j_0-1})`$. This is a prefix of $`N`$, so $`p \in N`$ and
  the hypothesis gives $`c \le p_1`$.

- The case $`p \in B_k`$. Then $`p = (N_{0,j} + k\,d_0,\ N_{1,j})`$ for some $`j`$
  with $`j_0 \le j \lt j_1`$. Since $`j \lt j_1 \lt \lvert N\rvert`$,
  [T.entry_pair_mem](#t-entry_pair_mem) gives $`(N_{0,j}, N_{1,j}) \in N`$, and
  the hypothesis gives $`c \le N_{0,j}`$. Hence
  $`c \le N_{0,j} \le N_{0,j} + k\,d_0 = p_1`$.

**(II-b) The case $`\neg\,\mathrm{hasParent}(N, i_1, j_1)`$.**
If $`N_{0,j_1} = 0 \wedge N_{1,j_1} = 0`$ holds, then by
[T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero), and if it does not, then by
[T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent);
in either case $`N[n] = \mathrm{Pred}\,N`$.
By the case distinction in the definition of $`\mathrm{Pred}`$ (D.Pred), $`\mathrm{Pred}\,N`$ is either
$`N`$ itself or $`\mathrm{dropLast}\,N`$. In the former case this is the hypothesis itself, and in
the latter case every element of $`\mathrm{dropLast}\,N`$ is an element of $`N`$, so the hypothesis applies. ∎

<a id="t-graft_mem_ge"></a>
## Theorem: grafting preserves a lower bound on the row-0 values (T.graft_mem_ge)

### Theorem

If $`N \ne ()`$ and $`\forall p \in N,\ c \le p_1`$, then for every $`z`$ we have
$`\forall p \in \mathrm{graft}(N,z),\ c \le p_1`$.

### Proof

From $`N \ne ()`$ we get $`0 \lt \lvert N\rvert`$, hence $`j_1 := \lvert N\rvert - 1 \lt \lvert N\rvert`$.
By [T.entry_pair_mem](#t-entry_pair_mem) we have $`(N_{0,j_1}, N_{1,j_1}) \in N`$, so
the hypothesis gives

```math
c \le N_{0,j_1} .
```

By the definition of $`\mathrm{graft}`$ (D.graft) we have
$`\mathrm{graft}(N,z) = \mathrm{dropLast}\,N \mathbin{+\!\!+} z^{+N_{0,j_1}}`$.
Take $`p \in \mathrm{graft}(N,z)`$ and distinguish according to which of the two parts it belongs to.

- The case $`p \in \mathrm{dropLast}\,N`$. Every element of $`\mathrm{dropLast}\,N`$ is an element of $`N`$, so
  the hypothesis gives $`c \le p_1`$.

- The case $`p \in z^{+N_{0,j_1}}`$. Then $`p = (q_1 + N_{0,j_1},\ q_2)`$ for some $`q \in z`$.
  From $`c \le N_{0,j_1}`$ proved above and $`N_{0,j_1} \le q_1 + N_{0,j_1}`$ we get $`c \le p_1`$. ∎

<a id="t-graft_head_eq"></a>
## Theorem: grafting does not change the row-0 value at the head (T.graft_head_eq)

### Theorem

If $`N \ne ()`$, $`\mathrm{based}(z)`$ and $`\mathrm{graft}(N,z) \ne ()`$, then

```math
\bigl(\mathrm{graft}(N,z)\bigr)_{0,0} = N_{0,0} .
```

### Proof

From $`N \ne ()`$ we can write $`N = b_0 :: N'`$. Distinguish cases according to whether $`N'`$ is empty.

**(a) The case $`N = (b_0)`$.** Then $`\lvert N\rvert - 1 = 0`$ and, by the definition of
$`M_{i,j}`$ (D.entry), $`N_{0,0} = (b_0)_1`$.
Since $`\mathrm{dropLast}\,(b_0) = ()`$, the definition of $`\mathrm{graft}`$ (D.graft) gives

```math
\mathrm{graft}(N, z) = z^{+(b_0)_1} .
```

By the hypothesis $`\mathrm{graft}(N,z) \ne ()`$ this is non-empty, hence $`z \ne ()`$.
Writing $`z = z_0 :: z'`$, the definition of $`\mathrm{based}`$ (D.based) and D.entry give
$`z_{0,0} = (z_0)_1 = 0`$. The head of $`z^{+(b_0)_1}`$ is
$`\bigl((z_0)_1 + (b_0)_1,\ (z_0)_2\bigr) = \bigl((b_0)_1,\ (z_0)_2\bigr)`$, so, by
D.entry,

```math
\bigl(\mathrm{graft}(N,z)\bigr)_{0,0} = (b_0)_1 = N_{0,0} .
```

**(b) The case $`N = b_0 :: b_1 :: N''`$.**
We have $`\mathrm{dropLast}\,N = b_0 :: \mathrm{dropLast}(b_1 :: N'')`$, which is non-empty and whose head is $`b_0`$.
Hence the head of $`\mathrm{graft}(N,z) = \mathrm{dropLast}\,N \mathbin{+\!\!+} z^{+N_{0,\lvert N\rvert-1}}`$ is
$`b_0`$ as well. By D.entry,

```math
\bigl(\mathrm{graft}(N,z)\bigr)_{0,0} = (b_0)_1 = N_{0,0} . \qquad \blacksquare
```
