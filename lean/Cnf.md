[← README](README.md) | [English](Cnf.md) | [Japanese](Cnf-ja.md) | Cnf **1** [2](Cnf-2.md) [3](Cnf-3.md)

<a id="t-getD_eq_getElem'"></a>
## Theorem: value of indexing with a default (T.getD_eq_getElem')

### Theorem

Let $`l`$ be a sequence, $`d`$ a default value and $`i \in \mathbb{N}`$. If $`i \lt \lvert l\rvert`$ then

```math
l\langle i\rangle = l_i .
```

Here $`l\langle i\rangle`$ is the operation returning the $`i`$-th element of $`l`$ when $`i \lt \lvert l\rvert`$
and $`d`$ otherwise, and $`l_i`$ is the $`i`$-th element taken together with a proof of $`i \lt \lvert l\rvert`$.

### Proof

$`l\langle i\rangle`$ is defined as the composition of two stages. The first stage searches for the
$`i`$-th element of $`l`$: when $`i \lt \lvert l\rvert`$ it returns the result that the $`i`$-th element
$`l_i`$ has been found, and when $`\lvert l\rvert \le i`$ it returns the result that nothing has been
found. The second stage returns that value when something has been found, and $`d`$ when nothing has.

By the hypothesis $`i \lt \lvert l\rvert`$ the first stage returns the result that $`l_i`$ has been
found, so the value of the second stage is $`l_i`$. ∎

<a id="t-oper_eq_dropLast_append"></a>
## Theorem: an expansion is a concatenation onto the sequence with its last column dropped (T.oper_eq_dropLast_append)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) and $`n \in \mathbb{N}`$, and suppose
$`1 \lt \lvert M\rvert`$ and $`1 \le n`$. Then there is $`R \in \mathrm{PairSeq}`$ such that

```math
M[n] = \mathrm{dropLast}\,M \mathbin{+\!\!+} R
\qquad\text{and}\qquad
\mathrm{snd}(R) \subseteq \mathrm{snd}(\mathrm{dropLast}\,M)
```

holds. Here $`\mathrm{dropLast}\,M`$ is the sequence obtained from $`M`$ by dropping its last element
($`M[n]`$ [D.oper](Pss.md#d-oper), $`\mathrm{snd}`$ [D.sndSet](Term.md#d-sndSet)).

### Proof

Put $`j_1 := \lvert M\rvert - 1`$ and $`i_1 := \mathrm{idx}_1(M, j_1)`$ ([D.idx1](Pss.md#d-idx1)).
From $`1 \lt \lvert M\rvert`$ we get $`j_1 \ne 0`$, and since $`\neg(\lvert M\rvert \le 1)`$, the second
case in the definition of $`\mathrm{Pred}\,M`$ ([D.Pred](Pss.md#d-Pred)) is the one selected, so

```math
\mathrm{Pred}\,M = \mathrm{dropLast}\,M
```

We distinguish the following three cases.

**(a) The case $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ ([D.entry](Pss.md#d-entry)).**
By [T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) we have
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$. Take $`R := ()`$.
The first formula holds because $`\mathrm{dropLast}\,M \mathbin{+\!\!+} () = \mathrm{dropLast}\,M`$.
The second holds because $`\mathrm{snd}(()) = \emptyset`$ by [T.sndSet_nil](Term.md#t-sndSet_nil)
and the empty set is a subset of every set.

**(b) The case $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ ([D.hasParent](Pss.md#d-hasParent)).**
By [T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) we have
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$. Take $`R := ()`$.
The first formula holds because $`\mathrm{dropLast}\,M \mathbin{+\!\!+} () = \mathrm{dropLast}\,M`$.
The second holds because $`\mathrm{snd}(()) = \emptyset`$ by [T.sndSet_nil](Term.md#t-sndSet_nil)
and the empty set is a subset of every set.

**(c) The case $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and $`\mathrm{hasParent}(M, i_1, j_1)`$.**
Apply [T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) and take
$`G, R_0 \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0 \in \mathbb{N}`$ and $`\ell \in \mathbb{N}\times\mathbb{N}`$
as provided by it. Its (1) and (2) read

```math
M = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R_0\bigr) \mathbin{+\!\!+} (\ell),
```
```math
M[n] = G \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} B_1 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k := \bigl((v_0,w_0) :: R_0\bigr)^{+k\,d_0}
```

Here $`L^{+e}`$ ([D.shiftr0](Cnf-2.md#d-shiftr0)) is the sequence obtained from $`L`$ by adding
$`e`$ to the first entry of each pair.

First, the last element of $`M`$ is $`\ell`$, so by (1)

```math
\mathrm{dropLast}\,M = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R_0\bigr)
```

Next, since $`1 \le n`$, the factor $`B_0`$ occurs in the concatenation (2).
As $`B_0 = ((v_0,w_0) :: R_0)^{+0\cdot d_0}`$ adds $`0`$ to the first entry of each pair, we have
$`B_0 = (v_0,w_0) :: R_0`$. So put

```math
R := B_1 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1}
```

(with $`R = ()`$ when $`n = 1`$); then (2) becomes

```math
M[n] = \Bigl(G \mathbin{+\!\!+} \bigl((v_0,w_0) :: R_0\bigr)\Bigr) \mathbin{+\!\!+} R
  = \mathrm{dropLast}\,M \mathbin{+\!\!+} R
```

and the first formula holds.

We prove the second formula. Let $`y \in \mathrm{snd}(R)`$. By [T.mem_sndSet](Term.md#t-mem_sndSet)
there is $`p \in R`$ with $`p_2 = y`$. Since $`R`$ is the concatenation of $`B_1, \dots, B_{n-1}`$,
we have $`p \in B_k`$ for some $`k`$ with $`1 \le k \le n-1`$.
The elements of $`B_k = ((v_0,w_0) :: R_0)^{+k\,d_0}`$ are of the form
$`(q_1 + k\,d_0,\ q_2)`$ for $`q \in (v_0,w_0) :: R_0`$, hence $`p_2 = q_2`$, that is, $`y = q_2`$.
Now $`q \in (v_0,w_0) :: R_0`$ and $`\mathrm{dropLast}\,M = G \mathbin{+\!\!+} ((v_0,w_0) :: R_0)`$,
so $`q \in \mathrm{dropLast}\,M`$. By [T.mem_sndSet](Term.md#t-mem_sndSet) again,
$`y \in \mathrm{snd}(\mathrm{dropLast}\,M)`$. ∎

<a id="t-diagSeq_cons"></a>
## Theorem: splitting off the head of a diagonal sequence (T.diagSeq_cons)

### Theorem

If $`u \le v`$ then $`\Delta_u^v = (u,u) :: \Delta_{u+1}^v`$ ([D.diagSeq](Pss.md#d-diagSeq)).

### Proof

By the definition of $`\Delta_a^b`$ (D.diagSeq), $`\Delta_u^v`$ is obtained from the sequence
$`(u,\ u+1,\ \dots)`$ of consecutive integers of length $`v + 1 - u`$ starting at $`u`$ by sending
each of its terms $`j`$ to the pair $`(j,j)`$.

From the hypothesis $`u \le v`$ we get $`v + 1 - u = \bigl(v + 1 - (u+1)\bigr) + 1`$.
A sequence of $`m + 1`$ consecutive integers starting at $`u`$ splits into its head term $`u`$ and the
sequence of $`m`$ consecutive integers starting at $`u+1`$. Applying $`j \mapsto (j,j)`$ to each term,
the head becomes $`(u,u)`$ and the rest is the image of the sequence of $`v + 1 - (u+1)`$ consecutive
integers starting at $`u+1`$, that is, $`\Delta_{u+1}^v`$. ∎

<a id="t-fst_in_diagSeq"></a>
## Theorem: lower bound for row 0 of an element of a diagonal sequence (T.fst_in_diagSeq)

### Theorem

If $`q \in \Delta_a^b`$ then $`a \le q_1`$.

### Proof

By the definition of $`\Delta_a^b`$ (D.diagSeq), $`q`$ is of the form $`(j,j)`$ for some $`j`$, and this
$`j`$ is an element of the sequence of consecutive integers of length $`b + 1 - a`$ starting at $`a`$,
that is, $`j = a + i`$ for some $`i \lt b + 1 - a`$. Hence $`q_1 = a + i`$, and $`a \le a + i`$. ∎

<a id="t-translate_diagSeq"></a>
## Theorem: the translation of a diagonal sequence (T.translate_diagSeq)

### Theorem

If $`u \le v`$ then

```math
\mathrm{tr}(\Delta_u^v) = \mathsf{P}\bigl(u,\ \mathrm{tr}(\Delta_{u+1}^v),\ \mathsf{Z}\bigr)
```

($`\mathrm{tr}`$ [D.translate](Term.md#d-translate), $`\mathsf{Z}`$ and $`\mathsf{P}`$ [D.Three](Term.md#d-Three)).

### Proof

By [T.diagSeq_cons](#t-diagSeq_cons) we have $`\Delta_u^v = (u,u) :: \Delta_{u+1}^v`$.
Apply [T.translate_single_tree](Term.md#t-translate_single_tree) with $`p := (u,u)`$ and
$`R := \Delta_{u+1}^v`$. Its hypothesis, that every element $`x`$ of $`R`$ satisfies $`p_1 \lt x_1`$,
is checked as follows. Let $`x \in \Delta_{u+1}^v`$; then
[T.fst_in_diagSeq](#t-fst_in_diagSeq) gives $`u + 1 \le x_1`$, hence $`u \lt x_1`$.
Since $`p_1 = u`$, this is the required condition.

The conclusion reads $`\mathrm{tr}((u,u) :: \Delta_{u+1}^v) = \mathsf{P}(p_2, \mathrm{tr}(\Delta_{u+1}^v), \mathsf{Z})`$,
and $`p_2 = u`$. ∎

<a id="d-cnf"></a>
## Definition: Cantor normal form condition (D.cnf)

We define a predicate $`\mathrm{cnf}`$ on $`\mathrm{Three}`$ by recursion on the structure of terms.

```math
\begin{aligned}
\mathrm{cnf}(\mathsf{Z}) &:\iff \top, \cr
\mathrm{cnf}\bigl(\mathsf{P}(a,b,\mathsf{Z})\bigr) &:\iff \mathrm{cnf}(b), \cr
\mathrm{cnf}\bigl(\mathsf{P}(a,b,\mathsf{P}(e,f,g))\bigr) &:\iff
  \mathrm{cnf}(b)
  \ \wedge\ \neg\bigl(\mathsf{P}(a,b,\mathsf{Z}) \prec \mathsf{P}(e,f,\mathsf{Z})\bigr) \cr
&\qquad \ \wedge\ \mathrm{cnf}\bigl(\mathsf{P}(e,f,g)\bigr).
\end{aligned}
```

The case distinction is on the constructor of the first argument and, when that constructor is
$`\mathsf{P}`$, on the constructor of its third argument; the three clauses exhaust all elements of
$`\mathrm{Three}`$ and are pairwise disjoint. The recursive calls are on $`b`$ in the second clause and
on $`b`$ and $`\mathsf{P}(e,f,g)`$ in the third, all of which are proper subterms of the given term,
so this definition is well defined.

The second conjunct of the third clause,
$`\neg\bigl(\mathsf{P}(a,b,\mathsf{Z}) \prec \mathsf{P}(e,f,\mathsf{Z})\bigr)`$ ([D.olt](Term.md#d-olt)),
states that $`\mathsf{P}(e,f,\mathsf{Z})`$, obtained from the leading principal term of the successor sum
by deleting its successor sum, is not strictly greater than $`\mathsf{P}(a,b,\mathsf{Z})`$, obtained from
the leading principal term by deleting its successor sum.

<a id="t-cnf_Z"></a>
## Theorem: $`\mathsf{Z}`$ satisfies the condition (T.cnf_Z)

### Theorem

$`\mathrm{cnf}(\mathsf{Z})`$.

### Proof

By the first clause of the definition of $`\mathrm{cnf}`$ (D.cnf), $`\mathrm{cnf}(\mathsf{Z})`$ is the
same proposition as $`\top`$ by definition, and $`\top`$ holds. ∎

<a id="t-cnf_P_Z"></a>
## Theorem: the criterion when the successor sum is $`\mathsf{Z}`$ (T.cnf_P_Z)

### Theorem

For all $`a \in \mathbb{N}`$ and $`b \in \mathrm{Three}`$,

```math
\mathrm{cnf}\bigl(\mathsf{P}(a,b,\mathsf{Z})\bigr) \iff \mathrm{cnf}(b).
```

### Proof

This is exactly the second clause of the definition of $`\mathrm{cnf}`$ (D.cnf); the two sides are the
same proposition by definition. ∎

<a id="t-cnf_P_P"></a>
## Theorem: the criterion when the successor sum is a principal term (T.cnf_P_P)

### Theorem

For all $`a, e \in \mathbb{N}`$ and $`b, f, g \in \mathrm{Three}`$,

```math
\begin{aligned}
\mathrm{cnf}\bigl(\mathsf{P}(a,b,\mathsf{P}(e,f,g))\bigr) &\iff
  \mathrm{cnf}(b)
  \ \wedge\ \neg\bigl(\mathsf{P}(a,b,\mathsf{Z}) \prec \mathsf{P}(e,f,\mathsf{Z})\bigr) \cr
&\qquad \ \wedge\ \mathrm{cnf}\bigl(\mathsf{P}(e,f,g)\bigr).
\end{aligned}
```

### Proof

This is exactly the third clause of the definition of $`\mathrm{cnf}`$ (D.cnf); the two sides are the
same proposition by definition. ∎

<a id="t-cnf_translate_diagSeq_aux"></a>
## Theorem: the translation of a diagonal sequence satisfies the condition (general starting point) (T.cnf_translate_diagSeq_aux)

### Theorem

For all $`n, u \in \mathbb{N}`$ we have $`\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_u^{u+n})\bigr)`$.

### Proof

We argue by induction on $`n`$, keeping $`u`$ universally quantified. Show

```math
\Phi(n) :\equiv \forall u \in \mathbb{N},\ \mathrm{cnf}\bigl(\mathrm{tr}(\Delta_u^{u+n})\bigr)
```

for every $`n`$.

**Base case** $`n = 0`$. Let $`u`$ be given. We have $`u + 0 = u`$.
Applying [T.translate_diagSeq](#t-translate_diagSeq) with $`u \le u`$ gives

```math
\mathrm{tr}(\Delta_u^u) = \mathsf{P}\bigl(u,\ \mathrm{tr}(\Delta_{u+1}^u),\ \mathsf{Z}\bigr)
```

By the definition of $`\Delta_a^b`$ (D.diagSeq), $`\Delta_{u+1}^u`$ is a sequence of length
$`u + 1 - (u + 1) = 0`$, that is, $`()`$. By the definition of $`\mathrm{tr}`$ (D.translate) we have
$`\mathrm{tr}\,() = \mathsf{Z}`$, hence $`\mathrm{tr}(\Delta_u^u) = \mathsf{P}(u, \mathsf{Z}, \mathsf{Z})`$.
By [T.cnf_P_Z](#t-cnf_P_Z) this term satisfies the condition if and only if $`\mathrm{cnf}(\mathsf{Z})`$,
which is [T.cnf_Z](#t-cnf_Z). Hence $`\Phi(0)`$.

**Inductive step** $`n \to n+1`$. Assume $`\Phi(n)`$, that is,
$`\forall u,\ \mathrm{cnf}(\mathrm{tr}(\Delta_u^{u+n}))`$. Let $`u`$ be given.
Since $`u \le u + (n+1)`$, [T.translate_diagSeq](#t-translate_diagSeq) gives

```math
\mathrm{tr}\bigl(\Delta_u^{u+(n+1)}\bigr)
  = \mathsf{P}\bigl(u,\ \mathrm{tr}\bigl(\Delta_{u+1}^{u+(n+1)}\bigr),\ \mathsf{Z}\bigr)
```

As $`u + (n+1) = (u+1) + n`$, we have $`\Delta_{u+1}^{u+(n+1)} = \Delta_{u+1}^{(u+1)+n}`$, and applying
the induction hypothesis $`\Phi(n)`$ with $`u := u + 1`$ gives
$`\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_{u+1}^{(u+1)+n})\bigr)`$.
By [T.cnf_P_Z](#t-cnf_P_Z) this is equivalent to
$`\mathrm{cnf}\bigl(\mathsf{P}(u, \mathrm{tr}(\Delta_{u+1}^{u+(n+1)}), \mathsf{Z})\bigr)`$, so
$`\Phi(n+1)`$ holds. ∎

<a id="t-cnf_diag"></a>
## Theorem: the translation of a diagonal sequence satisfies the condition (T.cnf_diag)

### Theorem

For every $`v \in \mathbb{N}`$ we have $`\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_0^v)\bigr)`$.

### Proof

Applying [T.cnf_translate_diagSeq_aux](#t-cnf_translate_diagSeq_aux) with $`n := v`$ and $`u := 0`$
gives $`\mathrm{cnf}\bigl(\mathrm{tr}(\Delta_0^{0+v})\bigr)`$. Since $`0 + v = v`$, this is the
required statement. ∎

<a id="t-cnf_snoc"></a>
## Theorem: if the sequence with one column appended satisfies the condition, so does the original (T.cnf_snoc)

### Theorem

Let $`D \in \mathrm{PairSeq}`$ and $`m \in \mathbb{N}\times\mathbb{N}`$.
If $`\mathrm{cnf}\bigl(\mathrm{tr}(D \mathbin{+\!\!+} (m))\bigr)`$ then $`\mathrm{cnf}(\mathrm{tr}\,D)`$.

### Proof

Fix $`m`$ and argue by induction along the recursion of $`\mathrm{tr}`$. Show

```math
\Psi(D) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(D \mathbin{+\!\!+} (m))\bigr) \to \mathrm{cnf}(\mathrm{tr}\,D)
```

for every $`D`$.

**Base case** $`D = ()`$. The conclusion is $`\mathrm{cnf}(\mathrm{tr}\,())`$.
By the definition of $`\mathrm{tr}`$ (D.translate) we have $`\mathrm{tr}\,() = \mathsf{Z}`$, and
$`\mathrm{cnf}(\mathsf{Z})`$ holds by [T.cnf_Z](#t-cnf_Z) (the antecedent is not used).

**Inductive step** $`D = p :: L`$. Assume $`\Psi(\mathrm{tw}_{p_1} L)`$ and
$`\Psi(\mathrm{dw}_{p_1} L)`$. Assume the antecedent
$`\mathrm{cnf}\bigl(\mathrm{tr}((p :: L) \mathbin{+\!\!+} (m))\bigr)`$.
We distinguish cases according to whether every element $`x`$ of $`L`$ satisfies $`p_1 \lt x_1`$.

**(a) The case where every element $`x`$ of $`L`$ satisfies $`p_1 \lt x_1`$.**
Then $`\mathrm{tw}_{p_1} L = L`$ and $`\mathrm{dw}_{p_1} L = ()`$, so by the definition of
$`\mathrm{tr}`$ (D.translate)

```math
\mathrm{tr}(p :: L) = \mathsf{P}\bigl(p_2,\ \mathrm{tr}\,L,\ \mathsf{Z}\bigr)
```

We distinguish further according to whether $`m`$ satisfies the predicate.

**The case $`p_1 \lt m_1`$.** Every element of $`L \mathbin{+\!\!+} (m)`$ satisfies $`p_1 \lt x_1`$ as well,
so $`\mathrm{tw}_{p_1}(L \mathbin{+\!\!+} (m)) = L \mathbin{+\!\!+} (m)`$ and
$`\mathrm{dw}_{p_1}(L \mathbin{+\!\!+} (m)) = ()`$; together with
$`(p :: L) \mathbin{+\!\!+} (m) = p :: (L \mathbin{+\!\!+} (m))`$, the definition of $`\mathrm{tr}`$
(D.translate) gives

```math
\mathrm{tr}\bigl((p :: L) \mathbin{+\!\!+} (m)\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}(L \mathbin{+\!\!+} (m)),\ \mathsf{Z}\bigr)
```

Substituting this into the antecedent and using [T.cnf_P_Z](#t-cnf_P_Z) yields
$`\mathrm{cnf}\bigl(\mathrm{tr}(L \mathbin{+\!\!+} (m))\bigr)`$.
Since $`\mathrm{tw}_{p_1} L = L`$, the induction hypothesis $`\Psi(\mathrm{tw}_{p_1} L)`$ is $`\Psi(L)`$,
and applying it yields $`\mathrm{cnf}(\mathrm{tr}\,L)`$.
By [T.cnf_P_Z](#t-cnf_P_Z) again, $`\mathrm{cnf}\bigl(\mathsf{P}(p_2, \mathrm{tr}\,L, \mathsf{Z})\bigr)`$
holds, that is, $`\mathrm{cnf}(\mathrm{tr}(p :: L))`$.

**The case $`\neg(p_1 \lt m_1)`$.**
By [T.takeWhile_append_all](Term.md#t-takeWhile_append_all) and
[T.dropWhile_append_all](Term.md#t-dropWhile_append_all) we have
$`\mathrm{tw}_{p_1}(L \mathbin{+\!\!+} (m)) = L \mathbin{+\!\!+} \mathrm{tw}_{p_1}(m)`$ and
$`\mathrm{dw}_{p_1}(L \mathbin{+\!\!+} (m)) = \mathrm{dw}_{p_1}(m)`$, and since $`m`$ violates the
predicate, $`\mathrm{tw}_{p_1}(m) = ()`$ and $`\mathrm{dw}_{p_1}(m) = (m)`$. Hence

```math
\mathrm{tr}\bigl((p :: L) \mathbin{+\!\!+} (m)\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}\,L,\ \mathrm{tr}\,(m)\bigr)
```

Moreover, by the definition of $`\mathrm{tr}`$ (D.translate) we have
$`\mathrm{tr}\,(m) = \mathsf{P}(m_2, \mathsf{Z}, \mathsf{Z})`$.
Substituting these into the antecedent and using [T.cnf_P_P](#t-cnf_P_P), we obtain
$`\mathrm{cnf}(\mathrm{tr}\,L)`$ as the first conjunct of its right-hand side.
By [T.cnf_P_Z](#t-cnf_P_Z) we get $`\mathrm{cnf}\bigl(\mathsf{P}(p_2, \mathrm{tr}\,L, \mathsf{Z})\bigr)`$,
that is, $`\mathrm{cnf}(\mathrm{tr}(p :: L))`$.

**(b) The case where some element $`x`$ of $`L`$ satisfies $`\neg(p_1 \lt x_1)`$.**
By [T.takeWhile_append_not](Term.md#t-takeWhile_append_not) and
[T.dropWhile_append_not](Term.md#t-dropWhile_append_not) we have

```math
\mathrm{tw}_{p_1}(L \mathbin{+\!\!+} (m)) = \mathrm{tw}_{p_1} L,
\qquad
\mathrm{dw}_{p_1}(L \mathbin{+\!\!+} (m)) = \mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m)
```

Also $`\mathrm{dw}_{p_1} L \ne ()`$. Indeed, if $`\mathrm{dw}_{p_1} L = ()`$ then every element of
$`L`$ would satisfy $`p_1 \lt x_1`$, contradicting the assumption on $`x`$.
So write $`\mathrm{dw}_{p_1} L = q :: L_2`$. By the definition of $`\mathrm{tr}`$ (D.translate)

```math
\mathrm{tr}(\mathrm{dw}_{p_1} L)
  = \mathsf{P}\bigl(q_2,\ \mathrm{tr}(\mathrm{tw}_{q_1} L_2),\ \mathrm{tr}(\mathrm{dw}_{q_1} L_2)\bigr),
```
```math
\mathrm{tr}\bigl(\mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m)\bigr)
  = \mathsf{P}\bigl(q_2,\ \mathrm{tr}(\mathrm{tw}_{q_1}(L_2 \mathbin{+\!\!+} (m))),\
      \mathrm{tr}(\mathrm{dw}_{q_1}(L_2 \mathbin{+\!\!+} (m)))\bigr)
```

(in the second formula we used $`(q :: L_2) \mathbin{+\!\!+} (m) = q :: (L_2 \mathbin{+\!\!+} (m))`$).
In what follows we abbreviate $`A := \mathrm{tr}(\mathrm{tw}_{q_1} L_2)`$ and
$`A' := \mathrm{tr}(\mathrm{tw}_{q_1}(L_2 \mathbin{+\!\!+} (m)))`$.
By [T.translate_takeWhile_snoc_le](Decrease.md#t-translate_takeWhile_snoc_le) we have
$`A \preceq A'`$ ([D.ole](Term.md#d-ole)).

By the definition of $`\mathrm{tr}`$ (D.translate) and the two formulas above, the antecedent can be
written as

```math
\mathrm{cnf}\Bigl(\mathsf{P}\bigl(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\
  \mathsf{P}(q_2,\ A',\ \mathrm{tr}(\mathrm{dw}_{q_1}(L_2 \mathbin{+\!\!+} (m))))\bigr)\Bigr)
```

By [T.cnf_P_P](#t-cnf_P_P) the following three statements hold.

1. $`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{tw}_{p_1} L)\bigr)`$.
2. $`\neg\bigl(\mathsf{P}(p_2, \mathrm{tr}(\mathrm{tw}_{p_1} L), \mathsf{Z}) \prec \mathsf{P}(q_2, A', \mathsf{Z})\bigr)`$.
3. $`\mathrm{cnf}\bigl(\mathsf{P}(q_2, A', \mathrm{tr}(\mathrm{dw}_{q_1}(L_2 \mathbin{+\!\!+} (m))))\bigr)`$,
   that is, $`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dw}_{p_1} L \mathbin{+\!\!+} (m))\bigr)`$.

Applying the induction hypothesis $`\Psi(\mathrm{dw}_{p_1} L)`$ to 3 yields
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dw}_{p_1} L)\bigr)`$.

Next we prove

```math
\mathsf{P}(q_2,\ A,\ \mathsf{Z}) \preceq \mathsf{P}(q_2,\ A',\ \mathsf{Z})
```

By the definition of $`\preceq`$ (D.ole), $`A \preceq A'`$ says that $`A \prec A'`$ or $`A = A'`$.
In the former case [T.olt_P_b](Term.md#t-olt_P_b) gives
$`\mathsf{P}(q_2, A, \mathsf{Z}) \prec \mathsf{P}(q_2, A', \mathsf{Z})`$, so the first disjunct in the
definition of $`\preceq`$ holds. In the latter case the two sides are the same term, so the second
disjunct holds.

Using this, we prove

```math
\neg\bigl(\mathsf{P}(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\ \mathsf{Z}) \prec \mathsf{P}(q_2,\ A,\ \mathsf{Z})\bigr)
```

Suppose the formula inside the negation held. Then the relation $`\preceq`$ just proved and
[T.olt_ole_trans](Term.md#t-olt_ole_trans) would give
$`\mathsf{P}(p_2, \mathrm{tr}(\mathrm{tw}_{p_1} L), \mathsf{Z}) \prec \mathsf{P}(q_2, A', \mathsf{Z})`$,
contradicting 2.

Finally, by the definition of $`\mathrm{tr}`$ (D.translate)

```math
\mathrm{tr}(p :: L) = \mathsf{P}\bigl(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\
  \mathsf{P}(q_2,\ A,\ \mathrm{tr}(\mathrm{dw}_{q_1} L_2))\bigr)
```

and feeding [T.cnf_P_P](#t-cnf_P_P) with 1, with the negation just proved, and with
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dw}_{p_1} L)\bigr)`$ (which is nothing but
$`\mathrm{cnf}\bigl(\mathsf{P}(q_2, A, \mathrm{tr}(\mathrm{dw}_{q_1} L_2))\bigr)`$) yields
$`\mathrm{cnf}(\mathrm{tr}(p :: L))`$. ∎

<a id="t-cnf_dropLast"></a>
## Theorem: the condition is preserved when the last column is dropped (T.cnf_dropLast)

### Theorem

Let $`C \in \mathrm{PairSeq}`$ with $`C \ne ()`$. If $`\mathrm{cnf}(\mathrm{tr}\,C)`$ then
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,C)\bigr)`$.

### Proof

Since $`C \ne ()`$, the last element $`\ell`$ of $`C`$ exists and

```math
C = \mathrm{dropLast}\,C \mathbin{+\!\!+} (\ell)
```

By this, the hypothesis $`\mathrm{cnf}(\mathrm{tr}\,C)`$ can be written as
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,C \mathbin{+\!\!+} (\ell))\bigr)`$.
It remains to apply [T.cnf_snoc](#t-cnf_snoc) with $`D := \mathrm{dropLast}\,C`$ and $`m := \ell`$. ∎

<a id="t-cnf_take"></a>
## Theorem: the condition is preserved on prefixes (T.cnf_take)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and assume $`\mathrm{cnf}(\mathrm{tr}\,M)`$.
Then $`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}_k M)\bigr)`$ for every $`k \in \mathbb{N}`$.
Here $`\mathrm{take}_k M`$ is the sequence consisting of the first $`k`$ elements of $`M`$,
and equals $`M`$ itself when $`\lvert M\rvert \le k`$.

### Proof

It suffices to prove the following statement, from which the conclusion follows by taking
$`d := \lvert M\rvert - k`$.

```math
\forall d,\ \forall k,\ \bigl(\lvert M\rvert - k = d\bigr) \to \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}_k M)\bigr).
```

We argue by induction on $`d`$, keeping $`k`$ universally quantified. Show

```math
\Xi(d) :\equiv \forall k,\ \bigl(\lvert M\rvert - k = d\bigr)
  \to \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}_k M)\bigr)
```

for every $`d`$.

**Base case** $`d = 0`$. Let $`k`$ be given with $`\lvert M\rvert - k = 0`$. Subtraction of natural
numbers is truncated subtraction, so this means $`\lvert M\rvert \le k`$, and $`\mathrm{take}_k M = M`$.
The conclusion is then the hypothesis $`\mathrm{cnf}(\mathrm{tr}\,M)`$ itself.

**Inductive step** $`d \to d+1`$. Assume $`\Xi(d)`$. Let $`k`$ be given with
$`\lvert M\rvert - k = d + 1`$. Since $`\lvert M\rvert - k \ne 0`$ we have $`k \lt \lvert M\rvert`$,
that is, $`k + 1 \le \lvert M\rvert`$. Moreover $`\lvert M\rvert - (k+1) = d`$, so applying the
induction hypothesis $`\Xi(d)`$ with $`k + 1`$ yields
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}_{k+1} M)\bigr)`$.

From $`k + 1 \le \lvert M\rvert`$ we get $`\lvert \mathrm{take}_{k+1} M\rvert = k + 1`$, and since
$`k + 1 \ne 0`$ we have $`\mathrm{take}_{k+1} M \ne ()`$.
Moreover, dropping the last element of a sequence of length $`k+1`$ leaves its first $`k`$ elements, so

```math
\mathrm{dropLast}\bigl(\mathrm{take}_{k+1} M\bigr) = \mathrm{take}_k\bigl(\mathrm{take}_{k+1} M\bigr) = \mathrm{take}_k M
```

(the second equality holds because $`k \le k+1`$).
Applying [T.cnf_dropLast](#t-cnf_dropLast) with $`C := \mathrm{take}_{k+1} M`$ yields
$`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{take}_k M)\bigr)`$. Hence $`\Xi(d+1)`$. ∎

<a id="t-cnf_replicate_block"></a>
## Theorem: a repetition of the same block satisfies the condition (T.cnf_replicate_block)

### Theorem

Let $`v_0, w_0 \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$, and assume
$`\forall x \in R,\ v_0 \lt x_1`$ and $`\mathrm{cnf}(\mathrm{tr}\,R)`$.
Put $`B := (v_0,w_0) :: R`$. Moreover, for a sequence $`L`$ and $`k \in \mathbb{N}`$, write
$`L^{\ast k}`$ for the concatenation of $`k`$ copies of $`L`$, that is,

```math
L^{\ast 0} := (), \qquad L^{\ast(k+1)} := L \mathbin{+\!\!+} L^{\ast k} .
```

Then $`\mathrm{cnf}\bigl(\mathrm{tr}(B^{\ast n})\bigr)`$ for every $`n \in \mathbb{N}`$.

### Proof

We first check that

```math
(\ast)\qquad B^{\ast k} = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,B^{\ast k})_1\bigr)
```

holds for every $`k \in \mathbb{N}`$. For $`k = 0`$ we have $`B^{\ast 0} = ()`$, so the first disjunct
holds. For $`k = k' + 1`$, the head of $`B^{\ast(k'+1)} = B \mathbin{+\!\!+} B^{\ast k'}`$ is the head
$`(v_0,w_0)`$ of $`B`$, and $`\neg(v_0 \lt v_0)`$, so the second disjunct holds.

Hence [T.translate_block_append](Term.md#t-translate_block_append) can be applied with
$`T := B^{\ast k}`$, and

```math
(\ast\ast)\qquad \mathrm{tr}\bigl(B^{\ast(k+1)}\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}(B^{\ast k})\bigr)
```

holds for every $`k`$ (its first hypothesis is $`\forall x \in R,\ v_0 \lt x_1`$).

We argue by induction on $`n`$. Show

```math
\Phi(n) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(B^{\ast n})\bigr)
```

for every $`n`$.

**Base case** $`n = 0`$. We have $`B^{\ast 0} = ()`$, and by the definition of $`\mathrm{tr}`$
(D.translate) $`\mathrm{tr}\,() = \mathsf{Z}`$. By [T.cnf_Z](#t-cnf_Z) we get $`\Phi(0)`$.

**Inductive step** $`n = m + 1`$. Assume $`\Phi(m)`$, that is,
$`\mathrm{cnf}\bigl(\mathrm{tr}(B^{\ast m})\bigr)`$. We distinguish cases on $`m`$.

**The case $`m = 0`$.** Using $`(\ast\ast)`$ with $`k := 0`$ gives

```math
\mathrm{tr}(B^{\ast 1}) = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,()\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathsf{Z}\bigr)
```

By [T.cnf_P_Z](#t-cnf_P_Z) this term satisfies the condition if and only if
$`\mathrm{cnf}(\mathrm{tr}\,R)`$, which is one of the hypotheses. Hence $`\Phi(1)`$.

**The case $`m = m' + 1`$.** Using $`(\ast\ast)`$ with $`k := m`$ and with $`k := m'`$ gives

```math
\mathrm{tr}\bigl(B^{\ast(m+1)}\bigr)
  = \mathsf{P}\Bigl(w_0,\ \mathrm{tr}\,R,\
      \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}(B^{\ast m'})\bigr)\Bigr)
```

By [T.cnf_P_P](#t-cnf_P_P), for this term to satisfy the condition it suffices to prove the following
three statements.

1. $`\mathrm{cnf}(\mathrm{tr}\,R)`$: this is a hypothesis.
2. $`\neg\bigl(\mathsf{P}(w_0, \mathrm{tr}\,R, \mathsf{Z}) \prec \mathsf{P}(w_0, \mathrm{tr}\,R, \mathsf{Z})\bigr)`$:
   this is [T.olt_irrefl](Term.md#t-olt_irrefl).
3. $`\mathrm{cnf}\bigl(\mathsf{P}(w_0, \mathrm{tr}\,R, \mathrm{tr}(B^{\ast m'}))\bigr)`$:
   using $`(\ast\ast)`$ with $`k := m'`$, this term is $`\mathrm{tr}(B^{\ast(m'+1)}) = \mathrm{tr}(B^{\ast m})`$,
   so the statement is the induction hypothesis $`\Phi(m)`$.

Hence $`\Phi(m+1)`$. ∎
