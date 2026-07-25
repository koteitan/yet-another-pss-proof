[← README](README.md) | [English](Wset-4.md) | [Japanese](Wset-4-ja.md) | Wset [1](Wset.md) [2](Wset-2.md) [3](Wset-3.md) **4**

<a id="t-oper_cons_succ"></a>
## Theorem: the principal step for a successor (T.oper_cons_succ)

### Theorem

Let $`v, n \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)), and put
$`k_1 := \lvert R\rvert - 1`$.
Assume $`\mathrm{argOK}(R)`$ ([D.argOK](Wset.md#d-argOK)), $`R \ne ()`$,
$`R_{1,k_1} = 0`$ ([D.entry](Pss.md#d-entry)) and
$`\neg\,\mathrm{hasParent}(R, 0, k_1)`$ ([D.hasParent](Pss.md#d-hasParent)).
Then

```math
\bigl((0,v) :: R\bigr)[n] = \bigl((0,v) :: \mathrm{dropLast}\,R\bigr)^{\frown n} .
```

($`M[n]`$ [D.oper](Pss.md#d-oper))

Here, for a sequence $`Q`$, let $`Q^{\frown n}`$ denote the concatenation of $`n`$ copies of $`Q`$; that is,

```math
Q^{\frown 0} := (), \qquad Q^{\frown (n+1)} := Q^{\frown n} \mathbin{+\!\!+} Q .
```

### Proof

Write $`M := (0,v) :: R`$. From $`R \ne ()`$ we get $`0 \lt \lvert R\rvert`$, hence
$`\lvert M\rvert - 1 = \lvert R\rvert`$.
By [T.entry_cons_last](Wset-3.md#t-entry_cons_last) we have $`M_{0,\lvert R\rvert} = R_{0,k_1}`$.

**Step 1: $`\mathrm{idx}_1(M, \lvert M\rvert - 1) = 0`$ ([D.idx1](Pss.md#d-idx1)).**
By [T.idx1_cons_last](Wset-3.md#t-idx1_cons_last) we have
$`\mathrm{idx}_1(M, \lvert R\rvert) = \mathrm{idx}_1(R, k_1)`$, and the hypothesis $`R_{1,k_1} = 0`$
together with the second case of the definition of $`\mathrm{idx}_1`$ (D.idx1) gives
$`\mathrm{idx}_1(R, k_1) = 0`$.

**Step 2: $`\forall k \lt k_1,\ R_{0,k_1} \le R_{0,k}`$.**
Suppose there were a $`k`$ with $`k \lt k_1`$ and $`R_{0,k} \lt R_{0,k_1}`$. Since
$`k_1 \lt \lvert R\rvert`$, [T.hasParent_zero_iff](Wset-3.md#t-hasParent_zero_iff) would give
$`\mathrm{hasParent}(R, 0, k_1)`$, contrary to the hypothesis.

**Step 3: $`0 \to^M_0 \lvert R\rvert`$ ([D.nextrel0](Pss.md#d-nextrel0)).**
We verify the five conditions of the definition of $`\to^M_0`$ (D.nextrel0).

- (1) $`0 \lt \lvert M\rvert`$: indeed $`\lvert M\rvert = \lvert R\rvert + 1 \ge 1`$.
- (2) $`\lvert R\rvert \lt \lvert M\rvert`$: likewise.
- (3) $`0 \lt \lvert R\rvert`$: this is because $`R \ne ()`$.
- (4) $`M_{0,0} \lt M_{0,\lvert R\rvert}`$: column $`0`$ of $`M`$ is $`(0,v)`$, so
  $`M_{0,0} = 0`$. On the other hand, $`k_1 \lt \lvert R\rvert`$ and
  [T.entry_pair_mem](Wset-2.md#t-entry_pair_mem) show that the pair $`(R_{0,k_1}, R_{1,k_1})`$ is an element of $`R`$, so
  the definition of $`\mathrm{argOK}`$ (D.argOK) gives $`M_{0,\lvert R\rvert} = R_{0,k_1} \gt 0`$.
- (5) $`\forall l,\ (0 \lt l \wedge l \lt \lvert R\rvert) \to M_{0,\lvert R\rvert} \le M_{0,l}`$:
  such an $`l`$ can be written $`l = l' + 1`$ with $`l' \lt k_1`$. By [T.entry_cons](Wset-3.md#t-entry_cons) we have
  $`M_{0,l'+1} = R_{0,l'}`$, and Step 2 gives $`R_{0,k_1} \le R_{0,l'}`$.

**Step 4: if $`y \to^M_0 \lvert R\rvert`$ then $`y = 0`$.**
Suppose $`y \ne 0`$. Then $`y = y' + 1`$ for some $`y'`$, and by [T.nextR_cons_last](Wset-3.md#t-nextR_cons_last) we have
$`y' \to^R_0 k_1`$. Condition (3) of its definition (D.nextrel0) gives $`y' \lt k_1`$, and
condition (4) gives $`R_{0,y'} \lt R_{0,k_1}`$. But Step 2 gives
$`R_{0,k_1} \le R_{0,y'}`$, a contradiction.

**Step 5: applying the expansion.**
By Steps 3 and 4 we have $`\mathrm{hasParent}(M, 0, \lvert R\rvert)`$, and together with
Step 1 this is
$`\mathrm{hasParent}\bigl(M, \mathrm{idx}_1(M, \lvert M\rvert-1), \lvert M\rvert-1\bigr)`$.
Moreover [T.parent_nextR](Decrease.md#t-parent_nextR) and Step 4 give
$`\mathrm{par}^M_0(\lvert R\rvert) = 0`$ ([D.parent](Pss.md#d-parent)).
We have $`\lvert M\rvert - 1 = \lvert R\rvert \ne 0`$, and
$`M_{0,\lvert R\rvert} = R_{0,k_1} \gt 0`$ gives
$`\neg(M_{0,\lvert M\rvert-1} = 0 \wedge M_{1,\lvert M\rvert-1} = 0)`$.
Hence [T.oper_root_tiling](Wset-3.md#t-oper_root_tiling) applies. By Step 1 we have
$`\mathrm{idx}_1(M, \lvert M\rvert-1) = 0`$, so the $`e`$ occurring there is $`e = 0`$, because
$`0 \lt \mathrm{idx}_1(M,\lvert M\rvert-1)`$ is false, and
each block is $`(\mathrm{dropLast}\,M)^{+k\cdot 0} = \mathrm{dropLast}\,M`$ ([D.shiftr0](Cnf-2.md#d-shiftr0)).
Therefore

```math
M[n] = \bigl(\mathrm{dropLast}\,M\bigr)^{\frown n} .
```

Finally, since $`R \ne ()`$, the last element of $`M = (0,v) :: R`$ is the last element of $`R`$, so

```math
\mathrm{dropLast}\,M = \mathrm{dropLast}\bigl((0,v) :: R\bigr) = (0,v) :: \mathrm{dropLast}\,R
```

as required. ∎

<a id="t-oper_cons_tower"></a>
## Theorem: the tower equation (T.oper_cons_tower)

### Theorem

Let $`v, m, n \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$.
If $`\mathrm{argOK}(R)`$, $`\mathrm{domT}(R, m)`$ ([D.domT](Wset.md#d-domT)) and $`v \le m`$, then

```math
\bigl((0,v) :: R\bigr)[n] = \mathrm{tow}_v(R,n) .
```

($`\mathrm{tow}_v(R,n)`$ [D.tow](Wset-3.md#d-tow))

### Proof

Write $`M := (0,v) :: R`$, $`k_1 := \lvert R\rvert - 1`$ and $`x := R_{0,k_1}`$.

First, $`R \ne ()`$. Indeed, if $`R = ()`$ then
[T.not_domT_nil](Wset.md#t-not_domT_nil) contradicts $`\mathrm{domT}(R,m)`$.
Hence $`0 \lt \lvert R\rvert`$ and $`\lvert M\rvert - 1 = \lvert R\rvert`$.
By [T.entry_cons_last](Wset-3.md#t-entry_cons_last) we have
$`M_{0,\lvert R\rvert} = R_{0,k_1} = x`$ and $`M_{1,\lvert R\rvert} = R_{1,k_1}`$.
The first conjunct of the definition of $`\mathrm{domT}`$ (D.domT) gives $`R_{1,k_1} = m + 1`$, and
the second conjunct gives $`\neg\,\mathrm{hasParent}(R, 1, k_1)`$.
Moreover $`k_1 \lt \lvert R\rvert`$, [T.entry_pair_mem](Wset-2.md#t-entry_pair_mem) and
the definition of $`\mathrm{argOK}`$ (D.argOK) give $`0 \lt x`$.

**Step 1: $`\mathrm{idx}_1(M, \lvert M\rvert - 1) = 1`$.**
By [T.idx1_cons_last](Wset-3.md#t-idx1_cons_last) we have
$`\mathrm{idx}_1(M, \lvert R\rvert) = \mathrm{idx}_1(R, k_1)`$, and
$`R_{1,k_1} = m + 1 \gt 0`$ together with the first case of the definition of $`\mathrm{idx}_1`$ (D.idx1)
shows that this value is $`1`$.

**Step 2: if $`y \to^M_1 \lvert R\rvert`$ ([D.nextrel1](Pss.md#d-nextrel1)) then $`y = 0`$.**
Suppose $`y \ne 0`$. Then $`y = y' + 1`$ for some $`y'`$, and by [T.nextR_cons_last](Wset-3.md#t-nextR_cons_last) we have
$`y' \to^R_1 k_1`$. Conditions (3), (4) and (5) of the definition of $`\to^R_1`$ (D.nextrel1) read
$`y' \lt k_1`$, $`R_{1,y'} \lt R_{1,k_1}`$ and $`y' \le^R_0 k_1`$ ([D.le0](Pss.md#d-le0)) respectively, and these are
exactly $`\mathrm{r1cand}(R, k_1, y')`$ ([D.r1cand](Wset.md#d-r1cand)). Since $`k_1 \lt \lvert R\rvert`$,
[T.hasParent_one_iff](Wset.md#t-hasParent_one_iff) gives $`\mathrm{hasParent}(R, 1, k_1)`$, which
contradicts the $`\neg\,\mathrm{hasParent}(R,1,k_1)`$ obtained above.

**Step 3: $`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$ and $`\mathrm{par}^M_1(\lvert R\rvert) = 0`$.**
Since $`v \le m \lt m + 1 = R_{1,k_1}`$, applying
[T.hasParent_cons_one](Wset-3.md#t-hasParent_cons_one) with the second disjunct gives
$`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$.
By [T.parent_nextR](Decrease.md#t-parent_nextR) we have
$`\mathrm{par}^M_1(\lvert R\rvert) \to^M_1 \lvert R\rvert`$, so Step 2 gives
$`\mathrm{par}^M_1(\lvert R\rvert) = 0`$.

**Step 4: the shape of the tiling.**
We have $`\lvert M\rvert - 1 = \lvert R\rvert \ne 0`$, and $`M_{0,\lvert R\rvert} = x \gt 0`$ gives
$`\neg(M_{0,\lvert M\rvert-1} = 0 \wedge M_{1,\lvert M\rvert-1} = 0)`$.
Together with Steps 1 and 3, [T.oper_root_tiling](Wset-3.md#t-oper_root_tiling) applies.
By Step 1 we have $`\mathrm{idx}_1(M,\lvert M\rvert-1) = 1 \gt 0`$, so the $`e`$ occurring there is

```math
e = M_{0,\lvert M\rvert-1} - M_{0,0} = x - 0 = x
```

(column $`0`$ of $`M`$ is $`(0,v)`$, so $`M_{0,0} = 0`$). Moreover
$`R \ne ()`$ gives $`\mathrm{dropLast}\,M = (0,v) :: \mathrm{dropLast}\,R`$.
Putting $`D := (0,v) :: \mathrm{dropLast}\,R`$, we get

```math
M[n] = D^{+0\cdot x} \mathbin{+\!\!+} D^{+1\cdot x} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} D^{+(n-1)x} .
```

**Step 5: the right-hand side equals $`\mathrm{tow}_v(R,n)`$.**
By induction on $`n`$. The induction predicate is

```math
\Phi(n) :\equiv D^{+0\cdot x} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} D^{+(n-1)x} = \mathrm{tow}_v(R,n) .
```

- **Base case** $`n = 0`$: the left-hand side is the empty concatenation, that is $`()`$, and
  the first clause of the definition of $`\mathrm{tow}`$ (D.tow) gives $`\mathrm{tow}_v(R,0) = ()`$.

- **Inductive step** $`n \to n+1`$: the induction hypothesis is $`\Phi(n)`$.
  Splitting off the first block of the left-hand side, we have $`D^{+0\cdot x} = D`$, and
  the remaining blocks are those of the left-hand side with each index shifted by one, so

```math
D^{+0\cdot x} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} D^{+n x}
  = D \mathbin{+\!\!+} \Bigl(D^{+0\cdot x} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} D^{+(n-1)x}\Bigr)^{+x}
```

  (this uses $`(L^{+a})^{+b} = L^{+(a+b)}`$ and $`k\,x + x = (k+1)x`$).
  Applying the induction hypothesis $`\Phi(n)`$ inside the parentheses on the right-hand side gives

```math
D^{+0\cdot x} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} D^{+n x}
  = D \mathbin{+\!\!+} \bigl(\mathrm{tow}_v(R,n)\bigr)^{+x}
```

  On the other hand, the second clause of the definition of $`\mathrm{tow}`$ (D.tow) and
  the definition of $`\mathrm{graft}`$ ([D.graft](Wset.md#d-graft)) give

```math
\begin{aligned}
\mathrm{tow}_v(R,n+1)
  &= (0,v) :: \mathrm{graft}\bigl(R, \mathrm{tow}_v(R,n)\bigr) \cr
  &= (0,v) :: \Bigl(\mathrm{dropLast}\,R
       \mathbin{+\!\!+} \bigl(\mathrm{tow}_v(R,n)\bigr)^{+R_{0,\lvert R\rvert-1}}\Bigr)
\end{aligned}
```

  and since $`R_{0,\lvert R\rvert-1} = x`$ and $`(0,v) :: \mathrm{dropLast}\,R = D`$, the
  right-hand side equals $`D \mathbin{+\!\!+} (\mathrm{tow}_v(R,n))^{+x}`$. Hence $`\Phi(n+1)`$. ∎

<a id="t-domT_cons_of_lt"></a>
## Theorem: inheritance of $`\mathrm{dom}`$ in the continuing case (T.domT_cons_of_lt)

### Theorem

Let $`v, m \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$.
If $`\mathrm{argOK}(R)`$, $`\mathrm{domT}(R, m)`$ and $`m \lt v`$, then
$`\mathrm{domT}\bigl((0,v) :: R,\ m\bigr)`$.

### Proof

Write $`M := (0,v) :: R`$ and $`k_1 := \lvert R\rvert - 1`$.
By [T.not_domT_nil](Wset.md#t-not_domT_nil) we have $`R \ne ()`$, hence
$`0 \lt \lvert R\rvert`$ and $`\lvert M\rvert - 1 = \lvert R\rvert`$.
By [T.entry_cons_last](Wset-3.md#t-entry_cons_last) we have $`M_{1,\lvert R\rvert} = R_{1,k_1}`$.

We prove the two conjuncts of the definition of $`\mathrm{domT}`$ (D.domT).

**First conjunct $`M_{1,\lvert M\rvert - 1} = m + 1`$.**
We have $`M_{1,\lvert M\rvert-1} = M_{1,\lvert R\rvert} = R_{1,k_1}`$, and the first conjunct of
the hypothesis $`\mathrm{domT}(R,m)`$ gives $`R_{1,k_1} = m + 1`$.

**Second conjunct $`\neg\,\mathrm{hasParent}(M, 1, \lvert M\rvert - 1)`$.**
Assume $`\mathrm{hasParent}(M, 1, \lvert R\rvert)`$ and derive a contradiction.
By [T.cons_len_lt](Wset-3.md#t-cons_len_lt) we have $`\lvert R\rvert \lt \lvert M\rvert`$, so
[T.hasParent_one_iff](Wset.md#t-hasParent_one_iff) applies and yields a $`j_0`$ satisfying

```math
j_0 \lt \lvert R\rvert, \qquad j_0 \le^M_0 \lvert R\rvert, \qquad M_{1,j_0} \lt M_{1,\lvert R\rvert} = m+1
```

We distinguish cases on $`j_0`$.

- **The case $`j_0 = 0`$.** Column $`0`$ of $`M`$ is $`(0,v)`$, so $`M_{1,0} = v`$ and hence
  $`v \lt m + 1`$, that is $`v \le m`$. This contradicts the hypothesis $`m \lt v`$.

- **The case $`j_0 = j' + 1`$.** By [T.entry_cons](Wset-3.md#t-entry_cons) we have
  $`M_{1,j'+1} = R_{1,j'}`$, hence $`R_{1,j'} \lt m + 1 = R_{1,k_1}`$.
  Moreover $`j' + 1 \lt \lvert R\rvert`$ gives $`j' \lt \lvert R\rvert - 1 = k_1`$, and
  $`j' + 1 \le^M_0 \lvert R\rvert`$ together with [T.le0_cons_last](Wset-3.md#t-le0_cons_last) gives
  $`j' \le^R_0 k_1`$.
  These three are exactly $`\mathrm{r1cand}(R, k_1, j')`$, so
  $`k_1 \lt \lvert R\rvert`$ and [T.hasParent_one_iff](Wset.md#t-hasParent_one_iff) give
  $`\mathrm{hasParent}(R, 1, k_1)`$. This contradicts the second conjunct of the hypothesis
  $`\mathrm{domT}(R,m)`$. ∎

<a id="t-argOK_oper"></a>
## Theorem: the argument block is preserved under expansion (T.argOK_oper)

### Theorem

If $`\mathrm{argOK}(R)`$, then $`\mathrm{argOK}(R[n])`$ for every $`n`$.

### Proof

By the definition of $`\mathrm{argOK}`$ (D.argOK), the hypothesis reads $`\forall p \in R,\ 0 \lt p_1`$,
that is $`\forall p \in R,\ 1 \le p_1`$.
Applying [T.oper_mem_ge](Wset-2.md#t-oper_mem_ge) with $`c := 1`$ and $`B := R`$ gives
$`\forall p \in R[n],\ 1 \le p_1`$, that is $`\forall p \in R[n],\ 0 \lt p_1`$. ∎

<a id="t-argOK_graft"></a>
## Theorem: the argument block is preserved under grafting (T.argOK_graft)

### Theorem

If $`R \ne ()`$ and $`\mathrm{argOK}(R)`$, then for every $`z' \in \mathrm{PairSeq}`$ we have
$`\mathrm{argOK}\bigl(\mathrm{graft}(R, z')\bigr)`$.

### Proof

The hypothesis is equivalent to $`\forall p \in R,\ 1 \le p_1`$.
Applying [T.graft_mem_ge](Wset-2.md#t-graft_mem_ge) with $`c := 1`$, $`B := R`$ and $`z := z'`$ gives
$`\forall p \in \mathrm{graft}(R,z'),\ 1 \le p_1`$, that is
$`\forall p \in \mathrm{graft}(R,z'),\ 0 \lt p_1`$. ∎

<a id="t-argOK_dropLast"></a>
## Theorem: the argument block is preserved under dropLast (T.argOK_dropLast)

### Theorem

If $`\mathrm{argOK}(R)`$ then $`\mathrm{argOK}(\mathrm{dropLast}\,R)`$.

### Proof

Let $`p \in \mathrm{dropLast}\,R`$. Since $`\mathrm{dropLast}\,R`$ is a prefix of $`R`$, we have
$`p \in R`$, and the definition of $`\mathrm{argOK}`$ (D.argOK) gives $`0 \lt p_1`$. ∎

<a id="t-based_cons"></a>
## Theorem: the principal block is in normalized form (T.based_cons)

### Theorem

For all $`v \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$,
$`\mathrm{based}\bigl((0,v) :: R\bigr)`$ ([D.based](Wset.md#d-based)).

### Proof

By the definition of $`\mathrm{based}`$ (D.based), what is to be shown is
$`\bigl((0,v) :: R\bigr)_{0,0} = 0`$.
Column $`0`$ of $`(0,v) :: R`$ is $`(0,v)`$, so by
the definition of $`M_{i,j}`$ (D.entry) its row $`0`$ value is $`0`$. ∎

<a id="t-rsum_self_cons"></a>
## Theorem: the root of the principal block has minimal depth (T.rsum_self_cons)

### Theorem

For all $`v \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$,

```math
\forall p \in (0,v) :: R,\ \bigl((0,v) :: R\bigr)_{0,0} \le p_1 .
```

### Proof

Column $`0`$ of $`(0,v) :: R`$ is $`(0,v)`$, so
$`\bigl((0,v) :: R\bigr)_{0,0} = 0`$ (definition of $`M_{i,j}`$, D.entry).
Since $`p_1`$ is a natural number, $`0 \le p_1`$. ∎

<a id="t-W_flatMap_copies"></a>
## Theorem: repeated copies of the same tree also belong to $`W_u`$ (T.W_flatMap_copies)

### Theorem

If $`Q \in W_u`$ ([D.W](Wset.md#d-W)) and $`\forall p \in Q,\ Q_{0,0} \le p_1`$, then
$`Q^{\frown n} \in W_u`$ for every $`n \in \mathbb{N}`$.

### Proof

By induction on $`n`$. The induction predicate is

```math
\Phi(n) :\equiv Q^{\frown n} \in W_u .
```

- **Base case** $`n = 0`$: $`Q^{\frown 0} = ()`$, and
  [T.W_nil](Wset.md#t-W_nil) gives $`() \in W_u`$.

- **Inductive step** $`n \to n+1`$: the induction hypothesis is $`\Phi(n)`$, that is $`Q^{\frown n} \in W_u`$.
  Since $`Q^{\frown(n+1)} = Q^{\frown n} \mathbin{+\!\!+} Q`$, it suffices to apply
  [T.W_add](Wset-3.md#t-W_add) with $`A := Q^{\frown n}`$ and $`B := Q`$.
  We verify its hypothesis $`\mathrm{rsum}(Q^{\frown n}, Q)`$ ([D.rsum](Wset.md#d-rsum)), that is

```math
\forall p \in Q^{\frown n} \mathbin{+\!\!+} Q,\ Q_{0,0} \le p_1
```

  Let $`p \in Q^{\frown n} \mathbin{+\!\!+} Q`$. Then
  $`p \in Q^{\frown n}`$ or $`p \in Q`$. In the latter case this is the hypothesis itself.
  In the former case, since $`Q^{\frown n}`$ is the concatenation of $`n`$ copies of $`Q`$, we have $`p \in Q`$,
  and again the hypothesis gives $`Q_{0,0} \le p_1`$. Hence $`\Phi(n+1)`$. ∎

<a id="t-Wstar_closed"></a>
## Theorem: $`A_u(W^{*}) \subseteq W^{*}`$ (T.Wstar_closed)

### Theorem

For all $`u \in \mathbb{N}`$ and $`M \in \mathrm{PairSeq}`$, if
$`M \in A_u(W^{*})`$ ($`A_u`$ [D.Aop](Wset.md#d-Aop), $`W^{*}`$ [D.Wstar](Wset-3.md#d-Wstar)) then
$`M \in W^{*}`$.

### Proof

In what follows we write $`R`$ for the $`M`$ of the statement. By the definition of $`W^{*}`$ (D.Wstar), what is to be shown is

```math
\mathrm{argOK}(R) \ \longrightarrow\ \forall v \in \mathbb{N},\ (0,v) :: R \in W_v
```

So assume $`\mathrm{argOK}(R)`$ and fix $`v`$.
Write $`N := (0,v) :: R`$ and $`k_1 := \lvert R\rvert - 1`$.

**The case $`R = ()`$.** Here $`N = (0,v) :: ()`$, and
[T.Om_mem_W](Wset-3.md#t-Om_mem_W) gives $`N \in W_v`$.

From now on assume $`R \ne ()`$. Then $`0 \lt \lvert R\rvert`$ and $`\lvert N\rvert - 1 = \lvert R\rvert`$, and
[T.entry_cons_last](Wset-3.md#t-entry_cons_last) gives
$`N_{1,\lvert N\rvert-1} = N_{1,\lvert R\rvert} = R_{1,k_1}`$.
We record the following two facts.

- **(D1)** If $`\mathrm{hasParent}(N, 1, \lvert R\rvert)`$ then
  $`\mathrm{natDom}(N)`$ ([D.natDom](Wset.md#d-natDom)).
  Indeed, the second disjunct of the right-hand side of [T.natDom_iff](Wset.md#t-natDom_iff) is
  $`\mathrm{hasParent}(N, 1, \lvert N\rvert - 1)`$, and
  $`\lvert N\rvert - 1 = \lvert R\rvert`$.
- **(D2)** If $`R_{1,k_1} = 0`$ then $`\mathrm{natDom}(N)`$.
  Indeed, the first disjunct of the right-hand side of [T.natDom_iff](Wset.md#t-natDom_iff) is $`N_{1,\lvert N\rvert-1} = 0`$,
  and this is the same as $`R_{1,k_1} = 0`$.

We distinguish cases on the hypothesis $`R \in A_u(W^{*})`$ according to the three branches of the definition of $`A_u`$ (D.Aop).

**Branch (1): the case $`\lvert R\rvert \le 1`$ and $`R_{1,0} = 0`$.**
From $`R \ne ()`$ we get $`\lvert R\rvert = 1`$, hence $`k_1 = 0`$ and $`R_{1,k_1} = 0`$.
Also $`\neg\,\mathrm{hasParent}(R, 0, k_1)`$: indeed, if there were a $`j_0`$ with
$`j_0 \to^R_0 0`$, then
[T.nextR_index_lt](Decrease.md#t-nextR_index_lt) would give $`j_0 \lt 0`$, which is
impossible for a natural number. Furthermore $`\lvert R\rvert = 1`$ gives
$`\mathrm{dropLast}\,R = ()`$.

By [T.A1_intro](Wset.md#t-A1_intro) it suffices to show $`N \in A_v(W_v)`$.
We take branch (2) of the definition of $`A_v`$ (D.Aop).
Here $`\mathrm{natDom}(N)`$ holds by (D2). As for $`N[n] \in W_v`$ for $`n \ge 1`$,
[T.oper_cons_succ](#t-oper_cons_succ) gives

```math
N[n] = \bigl((0,v) :: \mathrm{dropLast}\,R\bigr)^{\frown n} = \bigl((0,v) :: ()\bigr)^{\frown n}
```

and since [T.Om_mem_W](Wset-3.md#t-Om_mem_W) gives $`(0,v) :: () \in W_v`$ and
[T.rsum_self_cons](#t-rsum_self_cons) gives
$`\forall p \in (0,v) :: (),\ \bigl((0,v) :: ()\bigr)_{0,0} \le p_1`$,
[T.W_flatMap_copies](#t-W_flatMap_copies) yields $`N[n] \in W_v`$.

**Branch (2): the case $`\mathrm{natDom}(R)`$ and $`\forall n \ge 1,\ R[n] \in W^{*}`$.**
We distinguish cases according to whether $`\mathrm{hasParent}\bigl(R, \mathrm{idx}_1(R,k_1), k_1\bigr)`$ holds.

**(2a) The case $`\mathrm{hasParent}\bigl(R, \mathrm{idx}_1(R,k_1), k_1\bigr)`$.**
First we show $`\mathrm{natDom}(N)`$. If $`R_{1,k_1} = 0`$, this holds by (D2).
If $`R_{1,k_1} \ne 0`$, then the first case of the definition of $`\mathrm{idx}_1`$ (D.idx1) gives
$`\mathrm{idx}_1(R,k_1) = 1`$, so the hypothesis of the present case reads $`\mathrm{hasParent}(R,1,k_1)`$;
applying [T.hasParent_cons_one](Wset-3.md#t-hasParent_cons_one) with the first disjunct gives
$`\mathrm{hasParent}(N, 1, \lvert R\rvert)`$, and we use (D1).

By [T.A1_intro](Wset.md#t-A1_intro) we show $`N \in A_v(W_v)`$, taking its branch (2).
Let $`n \ge 1`$. Then [T.oper_cons_nat](Wset-3.md#t-oper_cons_nat) gives
$`N[n] = (0,v) :: R[n]`$. The hypothesis of branch (2) gives $`R[n] \in W^{*}`$, and
[T.argOK_oper](#t-argOK_oper) gives $`\mathrm{argOK}(R[n])`$, so applying
the definition of $`W^{*}`$ (D.Wstar) with $`v`$ gives $`(0,v) :: R[n] \in W_v`$.

**(2b) The case $`\neg\,\mathrm{hasParent}\bigl(R, \mathrm{idx}_1(R,k_1), k_1\bigr)`$.**
First we show $`R_{1,k_1} = 0`$. Suppose $`R_{1,k_1} \ne 0`$; then we can write
$`R_{1,k_1} = m + 1`$. By the definition of $`\mathrm{natDom}`$ (D.natDom) we have
$`\neg\,\mathrm{domT}(R,m)`$, and since the first conjunct of the definition of $`\mathrm{domT}`$ (D.domT)
holds here, the second conjunct fails, that is $`\mathrm{hasParent}(R,1,k_1)`$.
But $`R_{1,k_1} \gt 0`$ gives $`\mathrm{idx}_1(R,k_1) = 1`$, so
this contradicts the hypothesis of the present case.

Next we show $`\neg\,\mathrm{hasParent}(R, 0, k_1)`$. Suppose $`\mathrm{hasParent}(R,0,k_1)`$. Since
$`R_{1,k_1} = 0`$ gives $`\mathrm{idx}_1(R,k_1) = 0`$,
this too contradicts the hypothesis of the present case.

By [T.A1_intro](Wset.md#t-A1_intro) we show $`N \in A_v(W_v)`$, taking its branch (2).
Here $`\mathrm{natDom}(N)`$ holds by (D2). For $`n \ge 1`$,
[T.oper_cons_succ](#t-oper_cons_succ) gives

```math
N[n] = \bigl((0,v) :: \mathrm{dropLast}\,R\bigr)^{\frown n}
```

By [T.rsum_self_cons](#t-rsum_self_cons) and
[T.W_flatMap_copies](#t-W_flatMap_copies), it suffices to show
$`(0,v) :: \mathrm{dropLast}\,R \in W_v`$. We distinguish cases on $`\lvert R\rvert`$.

- **The case $`2 \le \lvert R\rvert`$.** Here $`k_1 = \lvert R\rvert - 1 \ne 0`$.
  By the hypothesis $`\neg\,\mathrm{hasParent}\bigl(R,\mathrm{idx}_1(R,k_1),k_1\bigr)`$ of the present case,
  $`R[1] = \mathrm{Pred}\,R`$ ([D.Pred](Pss.md#d-Pred)): when
  $`R_{0,k_1} = 0 \wedge R_{1,k_1} = 0`$ holds this is
  [T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero), and when it does not this is
  [T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent).
  Furthermore $`\neg(\lvert R\rvert \le 1)`$, so
  the second case of the definition of $`\mathrm{Pred}`$ (D.Pred) is selected and
  $`R[1] = \mathrm{dropLast}\,R`$.
  Applying the hypothesis of branch (2) with $`n := 1`$ gives $`\mathrm{dropLast}\,R \in W^{*}`$.
  Since [T.argOK_dropLast](#t-argOK_dropLast) gives
  $`\mathrm{argOK}(\mathrm{dropLast}\,R)`$,
  applying the definition of $`W^{*}`$ (D.Wstar) with $`v`$ gives
  $`(0,v) :: \mathrm{dropLast}\,R \in W_v`$.

- **The case $`\lvert R\rvert = 1`$.** Here $`\mathrm{dropLast}\,R = ()`$, so
  $`(0,v) :: \mathrm{dropLast}\,R = (0,v) :: ()`$, which belongs to $`W_v`$ by
  [T.Om_mem_W](Wset-3.md#t-Om_mem_W).

**Branch (3): the case where $`m \lt u`$, $`\mathrm{domT}(R,m)`$ and**
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(R,z) \in W^{*}`$ **hold.**
We distinguish cases according to whether $`v \le m`$ or not.

**(3a) The case $`v \le m`$.**
First we show $`\forall k \in \mathbb{N},\ \mathrm{tow}_v(R,k) \in W_v`$ by induction on $`k`$.
The induction predicate is $`\Psi(k) :\equiv \mathrm{tow}_v(R,k) \in W_v`$.

- **Base case** $`k = 0`$: the first clause of the definition of $`\mathrm{tow}`$ (D.tow) gives
  $`\mathrm{tow}_v(R,0) = ()`$, and [T.W_nil](Wset.md#t-W_nil) gives $`() \in W_v`$.

- **Inductive step** $`k \to k+1`$: the induction hypothesis is $`\Psi(k)`$.
  First we show $`\mathrm{based}(\mathrm{tow}_v(R,k))`$. For $`k = 0`$ we have
  $`\mathrm{tow}_v(R,0) = ()`$, and this is [T.based_nil](Wset.md#t-based_nil).
  For $`k = k' + 1`$, the second clause of the definition of $`\mathrm{tow}`$ (D.tow) gives
  $`\mathrm{tow}_v(R,k) = (0,v) :: \mathrm{graft}(R, \mathrm{tow}_v(R,k'))`$, and this is
  [T.based_cons](#t-based_cons).
  Next, applying $`v \le m`$ and [T.W_mono](Wset.md#t-W_mono) to $`\Psi(k)`$ gives
  $`\mathrm{tow}_v(R,k) \in W_m`$. Applying the hypothesis of branch (3) with
  $`z := \mathrm{tow}_v(R,k)`$ gives
  $`\mathrm{graft}(R, \mathrm{tow}_v(R,k)) \in W^{*}`$.
  Since $`R \ne ()`$ (by [T.not_domT_nil](Wset.md#t-not_domT_nil) and $`\mathrm{domT}(R,m)`$) and
  [T.argOK_graft](#t-argOK_graft) give
  $`\mathrm{argOK}\bigl(\mathrm{graft}(R,\mathrm{tow}_v(R,k))\bigr)`$,
  applying the definition of $`W^{*}`$ (D.Wstar) with $`v`$ gives

```math
\mathrm{tow}_v(R,k+1) = (0,v) :: \mathrm{graft}\bigl(R, \mathrm{tow}_v(R,k)\bigr) \in W_v
```

  That is, $`\Psi(k+1)`$.

By [T.A1_intro](Wset.md#t-A1_intro) we show $`N \in A_v(W_v)`$, taking its branch (2).
We obtain $`\mathrm{natDom}(N)`$ as follows. The first conjunct of $`\mathrm{domT}(R,m)`$ gives
$`R_{1,k_1} = m + 1`$, and $`v \le m \lt m+1`$, so applying
[T.hasParent_cons_one](Wset-3.md#t-hasParent_cons_one) with the second disjunct gives
$`\mathrm{hasParent}(N,1,\lvert R\rvert)`$, and we use (D1).
For $`n \ge 1`$, [T.oper_cons_tower](#t-oper_cons_tower) gives
$`N[n] = \mathrm{tow}_v(R,n)`$, which belongs to $`W_v`$ by the $`\Psi(n)`$ just proved.

**(3b) The case $`\neg(v \le m)`$, that is $`m \lt v`$.**
By [T.A1_intro](Wset.md#t-A1_intro) we show $`N \in A_v(W_v)`$, taking its branch (3).
We verify the three components of branch (3).

- $`m \lt v`$: this is the hypothesis of the present case.
- $`\mathrm{domT}(N, m)`$: this is [T.domT_cons_of_lt](#t-domT_cons_of_lt).
- if $`z \in W_m`$ and $`\mathrm{based}(z)`$ then $`\mathrm{graft}(N,z) \in W_v`$:
  since $`R \ne ()`$, [T.graft_cons](Wset-3.md#t-graft_cons) gives
  $`\mathrm{graft}(N,z) = (0,v) :: \mathrm{graft}(R,z)`$. The hypothesis of branch (3) gives
  $`\mathrm{graft}(R,z) \in W^{*}`$, and [T.argOK_graft](#t-argOK_graft) gives
  $`\mathrm{argOK}(\mathrm{graft}(R,z))`$, so
  applying the definition of $`W^{*}`$ (D.Wstar) with $`v`$ gives
  $`(0,v) :: \mathrm{graft}(R,z) \in W_v`$. ∎

<a id="t-tree_shift"></a>
## Theorem: shifting a single tree (T.tree_shift)

### Theorem

Let $`(x,y) \in \mathbb{N}\times\mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$, and assume
$`\forall r \in R,\ x \le r_1`$. Then

```math
\Bigl((0,y) :: R^{-x}\Bigr)^{+x} = (x,y) :: R .
```

($`R^{-x}`$ [D.shiftl0](ArgDom-2.md#d-shiftl0))

### Proof

The shift $`(\cdot)^{+x}`$ adds $`x`$ to the first entry of each pair, so splitting the head element
off from the rest we get

```math
\Bigl((0,y) :: R^{-x}\Bigr)^{+x} = (0 + x,\ y) :: \bigl(R^{-x}\bigr)^{+x}
```

Now $`0 + x = x`$, and under the hypothesis $`\forall r \in R,\ x \le r_1`$
[T.map_sub_add](Wset-2.md#t-map_sub_add) gives $`\bigl(R^{-x}\bigr)^{+x} = R`$. ∎

<a id="t-mem_of_Aclosed_aux"></a>
## Theorem: membership by induction on the length (lemma) (T.mem_of_Aclosed_aux)

### Theorem

For all $`N \in \mathbb{N}`$ and $`M \in \mathrm{PairSeq}`$ with
$`\lvert M\rvert \le N`$, and for every $`X \subseteq \mathrm{PairSeq}`$ satisfying the condition

```math
\mathrm{(Acl)}\qquad \forall u \in \mathbb{N},\ \forall M' \in \mathrm{PairSeq},\
  M' \in A_u(X) \to M' \in X
```

we have $`M \in X`$.

### Proof

By induction on $`N`$. The induction predicate is

```math
\Phi(N) :\equiv \forall M,\ \lvert M\rvert \le N \to
  \forall X,\ \mathrm{(Acl)} \to M \in X .
```

- **Base case** $`N = 0`$: from $`\lvert M\rvert \le 0`$ we get $`M = ()`$.
  Branch (1) of the definition of $`A_0`$ (D.Aop), namely $`\lvert M\rvert \le 1 \wedge M_{1,0} = 0`$, holds:
  we have $`\lvert ()\rvert = 0 \le 1`$, and $`()_{1,0} = 0`$ because by the definition of $`M_{i,j}`$ (D.entry)
  an out-of-range index reads as $`(0,0)`$.
  Hence $`() \in A_0(X)`$, and applying $`\mathrm{(Acl)}`$ with $`u := 0`$ and $`M' := ()`$ gives
  $`() \in X`$.

**Inductive step** $`N \to N+1`$: the induction hypothesis is $`\Phi(N)`$.
Take $`M`$ with $`\lvert M\rvert \le N+1`$ and $`X`$ satisfying $`\mathrm{(Acl)}`$.

If $`M = ()`$, then as seen in the base case $`() \in A_0(X)`$, so applying
$`\mathrm{(Acl)}`$ with $`u := 0`$ and $`M' := ()`$ gives $`M \in X`$.
From now on assume $`M \ne ()`$.
By [T.split_lastMin](Wset-2.md#t-split_lastMin) we take $`A, P`$ with

```math
M = A \mathbin{+\!\!+} P, \qquad P \ne (), \qquad \mathrm{rsum}(A,P), \qquad
\forall p \in \mathrm{tail}\,P,\ P_{0,0} \lt p_1
```

Then $`0 \lt \lvert P\rvert`$ and
$`\lvert A\rvert + \lvert P\rvert = \lvert M\rvert \le N+1`$. We distinguish cases on $`A`$.

**(a) The case $`A = ()`$.** Then $`M = P`$. From $`P \ne ()`$ we can write
$`P = (x,y) :: R`$. Since $`P_{0,0} = x`$ and $`\mathrm{tail}\,P = R`$,
the fourth property above reads

```math
\forall r \in R,\ x \lt r_1
```

From this $`\mathrm{argOK}\bigl(R^{-x}\bigr)`$ follows. Indeed, the elements of
$`R^{-x}`$ are of the form $`(r_1 - x,\ r_2)`$ for $`r \in R`$, and
$`x \lt r_1`$ gives $`0 \lt r_1 - x`$.

Since $`\lvert R^{-x}\rvert = \lvert R\rvert = \lvert P\rvert - 1 \le N`$, the
induction hypothesis $`\Phi(N)`$ can be applied with $`M := R^{-x}`$ and $`X := W^{*}`$.
That $`W^{*}`$ satisfies $`\mathrm{(Acl)}`$ is [T.Wstar_closed](#t-Wstar_closed).
Hence $`R^{-x} \in W^{*}`$. Together with $`\mathrm{argOK}(R^{-x})`$,
applying the definition of $`W^{*}`$ (D.Wstar) with $`y`$ gives

```math
(0,y) :: R^{-x} \in W_y
```

Applying [T.W_shift](Wset-2.md#t-W_shift) with $`d := x`$ gives
$`\bigl((0,y) :: R^{-x}\bigr)^{+x} \in W_y`$, and under
$`\forall r \in R,\ x \le r_1`$ this sequence equals $`(x,y) :: R = P = M`$ by
[T.tree_shift](#t-tree_shift). That is, $`M \in W_y`$.

Finally we apply [T.A2'](Wset.md#t-A2') with $`u := y`$ and $`Y := X`$. Its hypothesis
$`\forall M',\ M' \in A_y(X) \to M' \in X`$ is $`\mathrm{(Acl)}`$ specialized to
$`u := y`$. Hence $`W_y \subseteq X`$ and $`M \in X`$.

**(b) The case $`A \ne ()`$.** Here $`0 \lt \lvert A\rvert`$ and $`0 \lt \lvert P\rvert`$, and
$`\lvert A\rvert + \lvert P\rvert \le N+1`$, so
$`\lvert A\rvert \le N`$ and $`\lvert P\rvert \le N`$.

Applying the induction hypothesis $`\Phi(N)`$ with $`M := A`$ and $`X := X`$ gives $`A \in X`$.
Next, applying [T.XA_closed](Wset-3.md#t-XA_closed) to $`\mathrm{(Acl)}`$ specialized to $`u`$ and to
$`A \in X`$, we obtain, for every $`u`$,

```math
\forall M',\ M' \in A_u\bigl(X^{(A)}\bigr) \to M' \in X^{(A)}
```

That is, $`X^{(A)}`$ ([D.XA](Wset-2.md#d-XA)) satisfies $`\mathrm{(Acl)}`$ as well.
So applying the induction hypothesis $`\Phi(N)`$ with $`M := P`$ and $`X := X^{(A)}`$ gives
$`P \in X^{(A)}`$. By the definition of $`X^{(A)}`$ (D.XA),
$`P \in X^{(A)}`$ is $`\mathrm{rsum}(A,P) \to A \mathbin{+\!\!+} P \in X`$, and
$`\mathrm{rsum}(A,P)`$ is as taken above, so $`M = A \mathbin{+\!\!+} P \in X`$. ∎

<a id="t-mem_of_Aclosed"></a>
## Theorem: a set satisfying condition (Acl) contains every sequence (T.mem_of_Aclosed)

### Theorem

If $`X \subseteq \mathrm{PairSeq}`$ satisfies

```math
\forall u \in \mathbb{N},\ \forall M \in \mathrm{PairSeq},\ M \in A_u(X) \to M \in X
```

then $`M \in X`$ for every $`M \in \mathrm{PairSeq}`$.

### Proof

Apply [T.mem_of_Aclosed_aux](#t-mem_of_Aclosed_aux) with $`N := \lvert M\rvert`$.
Its hypothesis $`\lvert M\rvert \le N`$ holds by reflexivity of $`\le`$. ∎

<a id="t-mem_Wstar"></a>
## Theorem: every sequence belongs to $`W^{*}`$ (T.mem_Wstar)

### Theorem

For every $`R \in \mathrm{PairSeq}`$ we have $`R \in W^{*}`$.

### Proof

Apply [T.mem_of_Aclosed](#t-mem_of_Aclosed) with $`X := W^{*}`$.
Its hypothesis is exactly [T.Wstar_closed](#t-Wstar_closed). ∎

<a id="t-mem_W_of_bound_aux"></a>
## Theorem: membership from an upper bound on row 1 (lemma) (T.mem_W_of_bound_aux)

### Theorem

For all $`N \in \mathbb{N}`$, $`M \in \mathrm{PairSeq}`$ and $`u \in \mathbb{N}`$, if
$`\lvert M\rvert \le N`$ and $`\forall p \in M,\ p_2 \le u`$, then $`M \in W_u`$.

### Proof

By induction on $`N`$. The induction predicate is

```math
\Phi(N) :\equiv \forall M,\ \lvert M\rvert \le N \to
  \forall u,\ \bigl(\forall p \in M,\ p_2 \le u\bigr) \to M \in W_u .
```

- **Base case** $`N = 0`$: from $`\lvert M\rvert \le 0`$ we get $`M = ()`$, and
  [T.W_nil](Wset.md#t-W_nil) gives $`() \in W_u`$.

**Inductive step** $`N \to N+1`$: the induction hypothesis is $`\Phi(N)`$.
Take $`M`$ with $`\lvert M\rvert \le N+1`$, take $`u`$, and take
$`\forall p \in M,\ p_2 \le u`$.

If $`M = ()`$, this holds by [T.W_nil](Wset.md#t-W_nil). From now on assume $`M \ne ()`$.
By [T.split_lastMin](Wset-2.md#t-split_lastMin) we take $`A, P`$ with

```math
M = A \mathbin{+\!\!+} P, \qquad P \ne (), \qquad \mathrm{rsum}(A,P), \qquad
\forall p \in \mathrm{tail}\,P,\ P_{0,0} \lt p_1
```

Then $`0 \lt \lvert P\rvert`$ and
$`\lvert A\rvert + \lvert P\rvert \le N+1`$.
From $`P \ne ()`$ we can write $`P = (x,y) :: R`$, and since $`P_{0,0} = x`$ and $`\mathrm{tail}\,P = R`$,

```math
\forall r \in R,\ x \lt r_1
```

From this $`\mathrm{argOK}\bigl(R^{-x}\bigr)`$ follows. Indeed, the elements of
$`R^{-x}`$ are of the form $`(r_1 - x,\ r_2)`$ for $`r \in R`$, and
$`x \lt r_1`$ gives $`0 \lt r_1 - x`$.

By [T.mem_Wstar](#t-mem_Wstar) we have $`R^{-x} \in W^{*}`$, so applying
the definition of $`W^{*}`$ (D.Wstar) to $`\mathrm{argOK}(R^{-x})`$ and $`y`$ gives
$`(0,y) :: R^{-x} \in W_y`$. Applying [T.W_shift](Wset-2.md#t-W_shift) with $`d := x`$ and
using [T.tree_shift](#t-tree_shift) under $`\forall r \in R,\ x \le r_1`$, we get

```math
(x,y) :: R = \Bigl((0,y) :: R^{-x}\Bigr)^{+x} \in W_y
```

Since $`(x,y) \in A \mathbin{+\!\!+} P = M`$, the hypothesis gives $`y \le u`$, and
[T.W_mono](Wset.md#t-W_mono) gives $`(x,y) :: R \in W_u`$, that is $`P \in W_u`$.

We distinguish cases on $`A`$.

- **The case $`A = ()`$.** Then $`M = P \in W_u`$.

- **The case $`A \ne ()`$.** Since $`0 \lt \lvert A\rvert`$ and $`0 \lt \lvert P\rvert`$, we have
  $`\lvert A\rvert \le N`$. The elements of $`A`$ are elements of $`M`$, so
  $`\forall p \in A,\ p_2 \le u`$, and applying the induction hypothesis $`\Phi(N)`$ to $`A`$ gives
  $`A \in W_u`$. Together with $`\mathrm{rsum}(A,P)`$,
  [T.W_add](Wset-3.md#t-W_add) gives $`M = A \mathbin{+\!\!+} P \in W_u`$. ∎

<a id="t-mem_W_of_bound"></a>
## Theorem: membership from an upper bound on row 1 (T.mem_W_of_bound)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and $`u \in \mathbb{N}`$. If
$`\forall p \in M,\ p_2 \le u`$, then $`M \in W_u`$.

### Proof

Apply [T.mem_W_of_bound_aux](#t-mem_W_of_bound_aux) with $`N := \lvert M\rvert`$.
Its hypothesis $`\lvert M\rvert \le N`$ holds by reflexivity of $`\le`$. ∎

<a id="t-le_maxr1"></a>
## Theorem: the values in row 1 are at most the maximum (T.le_maxr1)

### Theorem

For every $`S \in \mathrm{PairSeq}`$ and every $`p \in S`$ we have $`p_2 \le \mathrm{maxr}_1(S)`$ ([D.maxr1](Column-2.md#d-maxr1)).

### Proof

By induction on the structure of $`S`$. The induction predicate is

```math
\Phi(S) :\equiv \forall p \in S,\ p_2 \le \mathrm{maxr}_1(S) .
```

- **Base case** $`S = ()`$: the empty sequence has no elements, so the antecedent is false and $`\Phi(())`$ holds.

- **Inductive step** $`S = q :: S'`$: the induction hypothesis is $`\Phi(S')`$.
  By [T.maxr1_cons](Column-2.md#t-maxr1_cons) we have
  $`\mathrm{maxr}_1(q :: S') = \max\bigl(q_2,\ \mathrm{maxr}_1(S')\bigr)`$.
  For $`\max`$ on natural numbers, $`a \le \max(a,b)`$ and $`b \le \max(a,b)`$ hold.
  Let $`p \in q :: S'`$; then $`p = q`$ or $`p \in S'`$.
  - The case $`p = q`$. Then $`p_2 = q_2 \le \max\bigl(q_2, \mathrm{maxr}_1(S')\bigr)`$.
  - The case $`p \in S'`$. The induction hypothesis gives $`p_2 \le \mathrm{maxr}_1(S')`$, and
    together with $`\mathrm{maxr}_1(S') \le \max\bigl(q_2, \mathrm{maxr}_1(S')\bigr)`$ and transitivity of $`\le`$ we get
    $`p_2 \le \max\bigl(q_2, \mathrm{maxr}_1(S')\bigr)`$.

  In either case $`p_2 \le \mathrm{maxr}_1(q :: S')`$, hence $`\Phi(q :: S')`$. ∎

<a id="t-mem_W_maxr1"></a>
## Theorem: membership at the stage given by the maximum of row 1 (T.mem_W_maxr1)

### Theorem

For every $`M \in \mathrm{PairSeq}`$ we have $`M \in W_{\mathrm{maxr}_1(M)}`$.

### Proof

Apply [T.mem_W_of_bound](#t-mem_W_of_bound) with $`u := \mathrm{maxr}_1(M)`$.
Its hypothesis $`\forall p \in M,\ p_2 \le \mathrm{maxr}_1(M)`$ is
[T.le_maxr1](#t-le_maxr1). ∎

<a id="t-W_membership"></a>
## Theorem: a standard form belongs to some stage (T.W_membership)

### Theorem

For every $`M \in \mathrm{PairSeq}`$, if $`M \in \mathrm{ST\_PS}`$ ([D.ST_PS](Pss.md#d-ST_PS)) then
there exists $`u \in \mathbb{N}`$ with $`M \in W_u`$.

### Proof

Take $`u := \mathrm{maxr}_1(M)`$.
Then $`M \in W_{\mathrm{maxr}_1(M)}`$ is [T.mem_W_maxr1](#t-mem_W_maxr1). ∎

<a id="t-wf_of_cofinality_and_membership"></a>
## Theorem: from cofinality and membership to well-foundedness (T.wf_of_cofinality_and_membership)

### Theorem

Assume the following two statements.

```math
\begin{aligned}
&\text{(cof)}\quad &&\forall M, N \in \mathrm{PairSeq},\
  M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,N \prec \mathrm{tr}\,M \cr
& &&\longrightarrow\ \exists n,\ 1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n]), \cr
&\text{(mem)}\quad &&\forall M \in \mathrm{PairSeq},\
  M \in \mathrm{ST\_PS} \to \exists u \in \mathbb{N},\ M \in W_u .
\end{aligned}
```

($`\mathrm{tr}`$ [D.translate](Term.md#d-translate), $`\prec`$ [D.olt](Term.md#d-olt), $`\preceq`$ [D.ole](Term.md#d-ole))

Then the relation $`R_{\mathrm{st}}`$ ([D.Rst](Wset.md#d-Rst)) is well-founded.

### Proof

By the definition of $`R_{\mathrm{st}}`$ (D.Rst),

```math
a \mathbin{R_{\mathrm{st}}} b :\iff a \in \mathrm{ST\_PS} \wedge b \in \mathrm{ST\_PS}
  \wedge \mathrm{tr}\,a \prec \mathrm{tr}\,b
```

Well-foundedness is equivalent to $`\forall M,\ \mathrm{Acc}(R_{\mathrm{st}},M)`$, so we
take an arbitrary $`M`$ and show $`\mathrm{Acc}(R_{\mathrm{st}},M)`$.
We distinguish cases according to whether $`M \in \mathrm{ST\_PS}`$.

- **The case $`M \in \mathrm{ST\_PS}`$.** By hypothesis (mem) take $`u`$ with $`M \in W_u`$.
  Applying [T.acc_of_W](Wset.md#t-acc_of_W) to hypothesis (cof), to $`u`$ and to $`M`$ gives
  $`\mathrm{Acc}(R_{\mathrm{st}},M)`$.

- **The case $`M \notin \mathrm{ST\_PS}`$.** By the generating rule of $`\mathrm{Acc}`$,
  namely $`\bigl(\forall y,\ y \mathbin{R} a \to \mathrm{Acc}(R,y)\bigr) \to \mathrm{Acc}(R,a)`$,
  it suffices to show $`\mathrm{Acc}(R_{\mathrm{st}},y)`$ for every $`y`$ with
  $`y \mathbin{R_{\mathrm{st}}} M`$. But
  the second conjunct of $`y \mathbin{R_{\mathrm{st}}} M`$ is $`M \in \mathrm{ST\_PS}`$, which
  contradicts the hypothesis of the present case. Hence no $`y`$ satisfies the antecedent, and
  $`\mathrm{Acc}(R_{\mathrm{st}},M)`$ holds. ∎

<a id="t-wf_olt_ST_PS_of_cofinality"></a>
## Theorem: from cofinality to well-foundedness of the order on standard forms (T.wf_olt_ST_PS_of_cofinality)

### Theorem

Under hypothesis (cof), that is,

```math
\begin{aligned}
&\forall M, N \in \mathrm{PairSeq},\
  M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,N \prec \mathrm{tr}\,M \cr
&\qquad \longrightarrow\ \exists n,\ 1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])
\end{aligned}
```

the relation

```math
a \mathbin{\rho} b :\iff a \in \mathrm{ST\_PS} \wedge b \in \mathrm{ST\_PS}
  \wedge \mathrm{tr}\,a \prec \mathrm{tr}\,b
```

is well-founded.

### Proof

The relation $`\rho`$ is the right-hand side of the definition of $`R_{\mathrm{st}}`$ (D.Rst) written out, so
the two are the same relation by definition.
It suffices to apply [T.wf_of_cofinality_and_membership](#t-wf_of_cofinality_and_membership) to
hypothesis (cof) and, as (mem), to [T.W_membership](#t-W_membership). ∎
