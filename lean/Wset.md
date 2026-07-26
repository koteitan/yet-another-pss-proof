[← README](README.md) | [English](Wset.md) | [Japanese](Wset-ja.md) | Wset **1** [2](Wset-2.md) [3](Wset-3.md) [4](Wset-4.md)

<a id="t-translate_eq_Z_iff"></a>
## Theorem: the translation is $`\mathsf{Z}`$ only for the empty sequence (T.translate_eq_Z_iff)

### Theorem

For $`M \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)),

```math
\mathrm{tr}\,M = \mathsf{Z} \iff M = () .
```

Here $`\mathrm{tr}`$ ([D.translate](Term.md#d-translate)) is the translation, and $`\mathsf{Z}`$ is
the first constructor of $`\mathrm{Three}`$ ([D.Three](Term.md#d-Three)).

### Proof

Distinguish cases on the constructor of $`M`$.

- $`M = ()`$. By the first clause of the definition of $`\mathrm{tr}`$ (D.translate) we have
  $`\mathrm{tr}\,() = \mathsf{Z}`$, so the equality on the left holds. The equality on the right,
  $`() = ()`$, holds by reflexivity of $`=`$. Hence the two sides are equivalent.

- $`M = p :: L`$. By the second clause of the definition of $`\mathrm{tr}`$ (D.translate),
  $`\mathrm{tr}(p :: L) = \mathsf{P}\bigl(p_2, \mathrm{tr}(\mathrm{tw}_{p_1} L), \mathrm{tr}(\mathrm{dw}_{p_1} L)\bigr)`$.
  The images of the constructors of $`\mathrm{Three}`$ are pairwise disjoint (D.Three), so
  $`\mathsf{P}(\cdot,\cdot,\cdot) \ne \mathsf{Z}`$ and the equality on the left is false.
  Moreover the length of $`p :: L`$ is at least $`1`$ while $`\lvert()\rvert = 0`$, so
  $`p :: L \ne ()`$ and the equality on the right is false as well. Hence the two sides are
  equivalent. ∎

<a id="t-eq_Z_of_olt_one"></a>
## Theorem: $`\mathsf{Z}`$ is the only term below $`\mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$ (T.eq_Z_of_olt_one)

### Theorem

If $`t \in \mathrm{Three}`$ satisfies $`t \prec \mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$ ([D.olt](Term.md#d-olt)),
then $`t = \mathsf{Z}`$.

### Proof

Distinguish cases on the constructor of $`t`$.

- $`t = \mathsf{Z}`$. The goal $`\mathsf{Z} = \mathsf{Z}`$ holds by reflexivity of $`=`$.

- $`t = \mathsf{P}(a,b,c)`$. Applying [T.olt_P_P](Term.md#t-olt_P_P) with
  $`e := 0`$, $`f := \mathsf{Z}`$ and $`g := \mathsf{Z}`$, the hypothesis becomes one of the
  following three.
  - $`a \lt 0`$. No natural number is below $`0`$, so this is false.
  - $`a = 0 \wedge b \prec \mathsf{Z}`$. By [T.not_olt_Z](Term.md#t-not_olt_Z),
    $`b \prec \mathsf{Z}`$ is false.
  - $`a = 0 \wedge b = \mathsf{Z} \wedge c \prec \mathsf{Z}`$. Likewise by
    [T.not_olt_Z](Term.md#t-not_olt_Z), $`c \prec \mathsf{Z}`$ is false.

  All three are false, so this case does not occur. ∎

<a id="t-stps_ne_nil"></a>
## Theorem: a standard form is not the empty sequence (T.stps_ne_nil)

### Theorem

If $`M \in \mathrm{ST\_PS}`$ ([D.ST_PS](Pss.md#d-ST_PS)) then $`M \ne ()`$.

### Proof

Suppose $`M = ()`$. By [T.stps_len_pos](Column.md#t-stps_len_pos) we have $`0 \lt \lvert M\rvert`$,
but substituting the hypothesis gives $`\lvert()\rvert = 0`$, hence $`0 \lt 0`$, which contradicts
irreflexivity of $`\lt`$. ∎

<a id="t-stps_len_one"></a>
## Theorem: standard forms of length $`1`$ (T.stps_len_one)

### Theorem

If $`M \in \mathrm{ST\_PS}`$ and $`\lvert M\rvert = 1`$, then $`M = \bigl((0,0)\bigr)`$.

### Proof

Since $`\lvert M\rvert = 1`$, there is a pair $`p`$ with $`M = (p)`$.
[T.stps_head](Column.md#t-stps_head) states that the first element of $`M`$ (read as $`(0,0)`$ when
$`M`$ is the empty sequence) equals $`(0,0)`$. The first element of $`M = (p)`$ is $`p`$, so
$`p = (0,0)`$ and $`M = \bigl((0,0)\bigr)`$. ∎

<a id="d-domT"></a>
## Definition: orphan in row $`1`$ (D.domT)

For $`M \in \mathrm{PairSeq}`$ and $`m \in \mathbb{N}`$ put

```math
\mathrm{domT}(M,m) :\iff
M_{1,\lvert M\rvert-1} = m+1 \ \wedge\ \neg\,\mathrm{hasParent}(M, 1, \lvert M\rvert-1)
```

Here $`M_{i,j}`$ ([D.entry](Pss.md#d-entry)) is the entry,
$`\mathrm{hasParent}(M,i,j)`$ ([D.hasParent](Pss.md#d-hasParent)) is the existence of a parent, and
the subtraction in $`\lvert M\rvert - 1`$ is truncated subtraction ($`\lvert M\rvert - 1 = 0`$ when
$`M = ()`$).

<a id="d-graft"></a>
## Definition: grafting (D.graft)

For $`L \in \mathrm{PairSeq}`$ and $`e \in \mathbb{N}`$, write $`L^{+e}`$
([D.shiftr0](Cnf-2.md#d-shiftr0)) for the sequence obtained from $`L`$ by adding $`e`$ to the first
entry of each pair (the notation of [T.translate_shift](Term.md#t-translate_shift)).
Let $`\mathrm{dropLast}\,M`$ be $`M`$ with its last element removed ($`()`$ when $`M = ()`$).
For $`M, z \in \mathrm{PairSeq}`$ put

```math
\mathrm{graft}(M, z) := \mathrm{dropLast}\,M \mathbin{+\!\!+} z^{+M_{0,\lvert M\rvert-1}}
```

<a id="d-based"></a>
## Definition: anchoring at depth $`0`$ (D.based)

For $`z \in \mathrm{PairSeq}`$,

```math
\mathrm{based}(z) :\iff z_{0,0} = 0 .
```

<a id="t-based_nil"></a>
## Theorem: the empty sequence is anchored at depth $`0`$ (T.based_nil)

### Theorem

$`\mathrm{based}(())`$.

### Proof

By the definition of $`M_{i,j}`$ (D.entry), since $`0 \ge \lvert()\rvert = 0`$ we have
$`()\langle 0\rangle = (0,0)`$, and taking its first entry gives $`()_{0,0} = 0`$.
This is exactly the right-hand side of the definition of $`\mathrm{based}`$ (D.based). ∎

<a id="t-graft_nil"></a>
## Theorem: grafting the empty block (T.graft_nil)

### Theorem

For every $`M \in \mathrm{PairSeq}`$, $`\mathrm{graft}(M, ()) = \mathrm{dropLast}\,M`$.

### Proof

Adding $`e`$ to the first entry of each pair of the empty sequence produces no elements, so
$`()^{+e} = ()`$. Hence the definition of $`\mathrm{graft}`$ (D.graft) gives

```math
\mathrm{graft}(M,()) = \mathrm{dropLast}\,M \mathbin{+\!\!+} () = \mathrm{dropLast}\,M . \qquad \blacksquare
```

<a id="t-not_domT_nil"></a>
## Theorem: the empty sequence does not satisfy the orphan condition (T.not_domT_nil)

### Theorem

For every $`m \in \mathbb{N}`$, $`\neg\,\mathrm{domT}((), m)`$.

### Proof

Suppose $`\mathrm{domT}((),m)`$. The first conjunct of the definition of $`\mathrm{domT}`$ (D.domT) is
$`()_{1,\lvert()\rvert-1} = m+1`$. Since $`\lvert()\rvert - 1 = 0`$ (truncated subtraction) and
$`()_{1,0} = 0`$ by the definition of $`M_{i,j}`$ (D.entry), this equality reads $`0 = m+1`$.
In the natural numbers $`m + 1 \ne 0`$, a contradiction. ∎

<a id="d-natDom"></a>
## Definition: negation of the orphan condition (D.natDom)

For $`M \in \mathrm{PairSeq}`$,

```math
\mathrm{natDom}(M) :\iff \forall m \in \mathbb{N},\ \neg\,\mathrm{domT}(M,m).
```

<a id="t-natDom_iff"></a>
## Theorem: restatement of the negation of the orphan condition (T.natDom_iff)

### Theorem

For $`M \in \mathrm{PairSeq}`$, writing $`j_1 := \lvert M\rvert - 1`$,

```math
\mathrm{natDom}(M) \iff
\bigl(M_{1,j_1} = 0 \ \vee\ \mathrm{hasParent}(M,1,j_1)\bigr).
```

### Proof

We prove both directions.

**($`\Rightarrow`$)** Suppose $`\mathrm{natDom}(M)`$. Distinguish cases according to whether
$`M_{1,j_1} = 0`$.

- $`M_{1,j_1} = 0`$. This is the first disjunct on the right-hand side itself.

- $`M_{1,j_1} \ne 0`$. We prove the second disjunct $`\mathrm{hasParent}(M,1,j_1)`$ by
  contradiction. Suppose $`\neg\,\mathrm{hasParent}(M,1,j_1)`$. Since $`M_{1,j_1} \ne 0`$, putting
  $`m := M_{1,j_1} - 1`$ gives $`M_{1,j_1} = m+1`$. Hence the two conjuncts of the definition of
  $`\mathrm{domT}`$ (D.domT) both hold and $`\mathrm{domT}(M,m)`$, which contradicts
  $`\neg\,\mathrm{domT}(M,m)`$, the definition of $`\mathrm{natDom}`$ (D.natDom) applied to this
  $`m`$.

**($`\Leftarrow`$)** Suppose the right-hand side. By the definition of $`\mathrm{natDom}`$
(D.natDom) it suffices to take $`m`$, to assume $`\mathrm{domT}(M,m)`$, that is
$`M_{1,j_1} = m+1`$ and $`\neg\,\mathrm{hasParent}(M,1,j_1)`$, and to derive a contradiction.
Distinguish cases on the disjunction on the right-hand side.

- $`M_{1,j_1} = 0`$. Then $`m + 1 = M_{1,j_1} = 0`$, but $`m+1 \ne 0`$ in the natural numbers,
  a contradiction.

- $`\mathrm{hasParent}(M,1,j_1)`$. This contradicts the second conjunct
  $`\neg\,\mathrm{hasParent}(M,1,j_1)`$ of $`\mathrm{domT}(M,m)`$. ∎

<a id="t-oper_eq_graft_nil_of_domT"></a>
## Theorem: expansion under the orphan condition (T.oper_eq_graft_nil_of_domT)

### Theorem

If $`1 \lt \lvert M\rvert`$ and $`\mathrm{domT}(M,m)`$, then for every $`n \in \mathbb{N}`$ we have
$`M[n] = \mathrm{graft}(M,())`$ ([D.oper](Pss.md#d-oper)).

### Proof

Write $`j_1 := \lvert M\rvert - 1`$. The definition of $`\mathrm{domT}`$ (D.domT) gives
$`M_{1,j_1} = m+1`$ and $`\neg\,\mathrm{hasParent}(M,1,j_1)`$. We prove the following five
statements in turn.

1. $`j_1 \ne 0`$. From $`1 \lt \lvert M\rvert`$ we get $`j_1 = \lvert M\rvert - 1 \ge 1`$.

2. $`\mathrm{idx}_1(M,j_1) = 1`$. Since $`M_{1,j_1} = m+1`$ and $`0 \lt m+1`$ for natural numbers,
   the first case in the definition of $`\mathrm{idx}_1`$ ([D.idx1](Pss.md#d-idx1)) is selected.

3. $`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$. If this conjunction held, its second
   conjunct would give $`m+1 = 0`$, contradicting $`m+1 \ne 0`$.

4. $`M[n] = \mathrm{Pred}\,M`$ ([D.Pred](Pss.md#d-Pred)). By 2 we have
   $`\mathrm{idx}_1(M,j_1) = 1`$, so
   $`\neg\,\mathrm{hasParent}\bigl(M, \mathrm{idx}_1(M,j_1), j_1\bigr)`$ is exactly the hypothesis
   $`\neg\,\mathrm{hasParent}(M,1,j_1)`$. Apply
   [T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) to 1, 3 and this.

5. $`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$. The definition of $`\mathrm{Pred}`$ (D.Pred)
   branches according to whether $`\lvert M\rvert \le 1`$. By the hypothesis
   $`1 \lt \lvert M\rvert`$ the condition $`\lvert M\rvert \le 1`$ is false, so the second case is
   selected, which is the sequence with its last column removed.

Finally, [T.graft_nil](#t-graft_nil) gives $`\mathrm{graft}(M,()) = \mathrm{dropLast}\,M`$.
Combining 4, 5 and this we obtain $`M[n] = \mathrm{graft}(M,())`$. ∎

<a id="d-r1cand"></a>
## Definition: parent candidate in row $`1`$ (D.r1cand)

For $`M \in \mathrm{PairSeq}`$ and $`j_1, j_0 \in \mathbb{N}`$ put

```math
\mathrm{r1cand}(M,j_1,j_0) :\iff
j_0 \lt j_1 \ \wedge\ j_0 \le^M_0 j_1 \ \wedge\ M_{1,j_0} \lt M_{1,j_1}
```

Here $`j_0 \le^M_0 j_1`$ ([D.le0](Pss.md#d-le0)) is the ancestor relation of row $`0`$.

<a id="t-hasParent_one_iff"></a>
## Theorem: criterion for the existence of a parent in row $`1`$ (T.hasParent_one_iff)

### Theorem

If $`j_1 \lt \lvert M\rvert`$ then

```math
\mathrm{hasParent}(M,1,j_1) \iff \exists j_0,\ \mathrm{r1cand}(M,j_1,j_0).
```

### Proof

The definition of $`\to^M_i`$ ([D.nextR](Pss.md#d-nextR)) branches according to whether $`i = 0`$.
Since $`i = 1 \ne 0`$, for every $`j_0`$ the statement $`j_0 \to^M_i j_1`$ is exactly the parent
relation of row $`1`$, that is $`j_0 \to^M_1 j_1`$ ([D.nextrel1](Pss.md#d-nextrel1)). We use this
below.

**($`\Rightarrow`$)** By the definition of $`\mathrm{hasParent}`$ (D.hasParent) there exists $`j_0`$
with $`j_0 \to^M_1 j_1`$. Conditions (3), (5), (4) of D.nextrel1 are $`j_0 \lt j_1`$,
$`j_0 \le^M_0 j_1`$ and $`M_{1,j_0} \lt M_{1,j_1}`$ respectively, and these are the three conjuncts
of the definition of $`\mathrm{r1cand}`$ (D.r1cand). Hence $`\mathrm{r1cand}(M,j_1,j_0)`$.

**($`\Leftarrow`$)** Take $`j_0`$ with $`\mathrm{r1cand}(M,j_1,j_0)`$. Define the predicate $`P`$ by

```math
P(k) :\equiv \mathrm{r1cand}(M,j_1,k)
```

The set $`\{\,k \mid k \le j_1 \wedge P(k)\,\}`$ is finite, and by the first conjunct of
$`\mathrm{r1cand}`$ we have $`j_0 \lt j_1`$, hence $`j_0 \le j_1`$; therefore the set contains
$`j_0`$ and is non-empty. Let $`g`$ be its largest element, that is,

```math
P(g), \qquad \forall k,\ \bigl(k \le j_1 \wedge P(k)\bigr) \to k \le g .
```

**Step 1: $`g \to^M_1 j_1`$.** We check the six conditions of D.nextrel1 in turn.

- (1) $`g \lt \lvert M\rvert`$: the first conjunct of $`P(g)`$ gives $`g \lt j_1`$, and the claim
  follows from the hypothesis $`j_1 \lt \lvert M\rvert`$ by transitivity of $`\lt`$.
- (2) $`j_1 \lt \lvert M\rvert`$: this is the hypothesis itself.
- (3) $`g \lt j_1`$: this is the first conjunct of $`P(g)`$.
- (4) $`M_{1,g} \lt M_{1,j_1}`$: this is the third conjunct of $`P(g)`$.
- (5) $`g \le^M_0 j_1`$: this is the second conjunct of $`P(g)`$.
- (6) For every $`j`$, if $`g \lt j`$ and $`j \le^M_0 j_1`$ then $`M_{1,j_1} \le M_{1,j}`$: we argue
  by contradiction. Suppose $`M_{1,j} \lt M_{1,j_1}`$. Condition (3) of the definition of
  $`\le^M_0`$ (D.le0) gives $`j \mathbin{(\to^M_0)^{*}} j_1`$
  ([D.nextrel0](Pss.md#d-nextrel0)), so [T.nextrel0_rtrancl_index_le](Term.md#t-nextrel0_rtrancl_index_le)
  gives $`j \le j_1`$. If $`j = j_1`$ then $`M_{1,j_1} \lt M_{1,j_1}`$, contradicting
  irreflexivity of $`\lt`$. If $`j \lt j_1`$, then $`j \lt j_1`$, $`j \le^M_0 j_1`$ and
  $`M_{1,j} \lt M_{1,j_1}`$ all hold, so $`P(j)`$ holds; from $`j \le j_1`$ and maximality we get
  $`j \le g`$, which contradicts the assumption $`g \lt j`$.

**Step 2: uniqueness.** Let $`y \to^M_1 j_1`$. Conditions (3), (5), (4) of D.nextrel1 give
$`P(y)`$, and condition (3) gives $`y \lt j_1`$, hence $`y \le j_1`$, so maximality yields
$`y \le g`$. Suppose $`y \ne g`$; then $`y \lt g`$. Apply condition (6) of $`y \to^M_1 j_1`$ with
$`j := g`$. Its antecedent $`y \lt g`$ is the present assumption, and $`g \le^M_0 j_1`$ is (5) of
Step 1, so we obtain $`M_{1,j_1} \le M_{1,g}`$. On the other hand (4) of Step 1 is
$`M_{1,g} \lt M_{1,j_1}`$, so $`M_{1,j_1} \lt M_{1,j_1}`$, contradicting irreflexivity of $`\lt`$.
Hence $`y = g`$.

By Steps 1 and 2, a $`j_0`$ with $`j_0 \to^M_1 j_1`$ exists and is unique. By the definition of
$`\mathrm{hasParent}`$ (D.hasParent) this is $`\mathrm{hasParent}(M,1,j_1)`$. ∎

<a id="t-domT_iff"></a>
## Theorem: restatement of the orphan condition along the spine (T.domT_iff)

### Theorem

Let $`M \ne ()`$ and write $`j_1 := \lvert M\rvert - 1`$. Then

```math
\mathrm{domT}(M,m) \iff \Bigl(M_{1,j_1} = m+1 \ \wedge\
  \forall j_0,\ \bigl(j_0 \lt j_1 \wedge j_0 \le^M_0 j_1\bigr) \to m+1 \le M_{1,j_0}\Bigr).
```

### Proof

From $`M \ne ()`$ we get $`0 \lt \lvert M\rvert`$, and by truncated subtraction
$`j_1 = \lvert M\rvert - 1 \lt \lvert M\rvert`$. Hence [T.hasParent_one_iff](#t-hasParent_one_iff)
applies and gives

```math
\mathrm{hasParent}(M,1,j_1) \iff \exists j_0,\ \mathrm{r1cand}(M,j_1,j_0)
```

The definition of $`\mathrm{domT}`$ (D.domT) is the conjunction of $`M_{1,j_1} = m+1`$ and
$`\neg\,\mathrm{hasParent}(M,1,j_1)`$, so the first conjunct is common to both sides, and it remains
to prove, under the assumption $`M_{1,j_1} = m+1`$, that

```math
\neg\,\exists j_0,\ \mathrm{r1cand}(M,j_1,j_0)
\iff \forall j_0,\ \bigl(j_0 \lt j_1 \wedge j_0 \le^M_0 j_1\bigr) \to m+1 \le M_{1,j_0}
```

**($`\Rightarrow`$)** Suppose the left-hand side. Take $`j_0`$ with $`j_0 \lt j_1`$ and
$`j_0 \le^M_0 j_1`$, and prove $`m+1 \le M_{1,j_0}`$ by contradiction. If
$`M_{1,j_0} \lt m+1`$, then, since $`M_{1,j_1} = m+1`$, we get $`M_{1,j_0} \lt M_{1,j_1}`$.
Together with $`j_0 \lt j_1`$ and $`j_0 \le^M_0 j_1`$ this supplies the three conjuncts of the
definition of $`\mathrm{r1cand}`$ (D.r1cand), so $`\mathrm{r1cand}(M,j_1,j_0)`$, contradicting the
left-hand side.

**($`\Leftarrow`$)** Suppose the right-hand side, and derive a contradiction from the existence of
$`j_0`$ with $`\mathrm{r1cand}(M,j_1,j_0)`$. Applying the right-hand side to its first conjunct
$`j_0 \lt j_1`$ and its second conjunct $`j_0 \le^M_0 j_1`$ gives $`m+1 \le M_{1,j_0}`$.
Its third conjunct is $`M_{1,j_0} \lt M_{1,j_1} = m+1`$. Together these give
$`m+1 \le M_{1,j_0} \lt m+1`$, contradicting irreflexivity of $`\lt`$. ∎

<a id="d-lfpS"></a>
## Definition: least fixpoint (D.lfpS)

Let $`f`$ be a map from subsets of $`\mathrm{PairSeq}`$ to subsets of $`\mathrm{PairSeq}`$. Put

```math
\mathrm{lfp}(f) := \bigcap\,\bigl\{\, Y \subseteq \mathrm{PairSeq} \ \bigm|\ f(Y) \subseteq Y \,\bigr\}
```

That is, $`x \in \mathrm{lfp}(f)`$ says that $`x \in Y`$ for **every**
$`Y \subseteq \mathrm{PairSeq}`$ with $`f(Y) \subseteq Y`$.

<a id="t-lfpS_lowerbound"></a>
## Theorem: the least fixpoint is a lower bound of the prefixpoints (T.lfpS_lowerbound)

### Theorem

If $`f(Y) \subseteq Y`$ then $`\mathrm{lfp}(f) \subseteq Y`$.

### Proof

Let $`x \in \mathrm{lfp}(f)`$. By the definition of $`\mathrm{lfp}`$ (D.lfpS), $`x`$ belongs to every
$`Z`$ with $`f(Z) \subseteq Z`$. By hypothesis $`Y`$ is one such $`Z`$, so $`x \in Y`$. ∎

<a id="t-lfpS_unfold_le"></a>
## Theorem: unfolding the least fixpoint (the $`\subseteq`$ direction) (T.lfpS_unfold_le)

### Theorem

Suppose $`f`$ is monotone, that is, $`X \subseteq Y`$ implies $`f(X) \subseteq f(Y)`$.
Then $`f(\mathrm{lfp}(f)) \subseteq \mathrm{lfp}(f)`$.

### Proof

Let $`x \in f(\mathrm{lfp}(f))`$. By the definition of $`\mathrm{lfp}`$ (D.lfpS) it suffices to show
$`x \in Y`$ for every $`Y`$ with $`f(Y) \subseteq Y`$.
By [T.lfpS_lowerbound](#t-lfpS_lowerbound) we have $`\mathrm{lfp}(f) \subseteq Y`$, and
monotonicity of $`f`$ gives $`f(\mathrm{lfp}(f)) \subseteq f(Y)`$. Hence $`x \in f(Y)`$, and the
hypothesis $`f(Y) \subseteq Y`$ gives $`x \in Y`$. ∎

<a id="t-lfpS_unfold_ge"></a>
## Theorem: unfolding the least fixpoint (the $`\supseteq`$ direction) (T.lfpS_unfold_ge)

### Theorem

If $`f`$ is monotone then $`\mathrm{lfp}(f) \subseteq f(\mathrm{lfp}(f))`$.

### Proof

Apply [T.lfpS_lowerbound](#t-lfpS_lowerbound) with $`Y := f(\mathrm{lfp}(f))`$.
Its hypothesis is $`f\bigl(f(\mathrm{lfp}(f))\bigr) \subseteq f(\mathrm{lfp}(f))`$, which is obtained
by applying monotonicity of $`f`$ to the conclusion
$`f(\mathrm{lfp}(f)) \subseteq \mathrm{lfp}(f)`$ of [T.lfpS_unfold_le](#t-lfpS_unfold_le). ∎

<a id="t-lfpS_unfold"></a>
## Theorem: the least fixpoint is a fixpoint (T.lfpS_unfold)

### Theorem

If $`f`$ is monotone then $`f(\mathrm{lfp}(f)) = \mathrm{lfp}(f)`$.

### Proof

By [T.lfpS_unfold_le](#t-lfpS_unfold_le) we have $`f(\mathrm{lfp}(f)) \subseteq \mathrm{lfp}(f)`$,
and by [T.lfpS_unfold_ge](#t-lfpS_unfold_ge) we have
$`\mathrm{lfp}(f) \subseteq f(\mathrm{lfp}(f))`$. By antisymmetry of $`\subseteq`$ the two are
equal. ∎

<a id="d-Aop"></a>
## Definition: the operator $`A_u`$ (D.Aop)

Let $`\mathcal{W}`$ be a family assigning to each $`m \in \mathbb{N}`$ a subset
$`\mathcal{W}(m)`$ of $`\mathrm{PairSeq}`$, and let $`u \in \mathbb{N}`$,
$`X \subseteq \mathrm{PairSeq}`$ and $`M \in \mathrm{PairSeq}`$. Consider the following three
statements.

```math
\begin{aligned}
&(1)\quad \lvert M\rvert \le 1 \ \wedge\ M_{1,0} = 0, \cr
&(2)\quad \mathrm{natDom}(M) \ \wedge\ \forall n \ge 1,\ M[n] \in X, \cr
&(3)\quad \exists m \lt u,\ \Bigl(\mathrm{domT}(M,m) \ \wedge\
  \forall z \in \mathcal{W}(m),\ \mathrm{based}(z) \to \mathrm{graft}(M,z) \in X\Bigr).
\end{aligned}
```

Using these, define

```math
\mathrm{Aop}(\mathcal{W},u,X,M) :\iff (1) \ \vee\ (2) \ \vee\ (3)
```

Below we call these three **branch (1)**, **branch (2)** and **branch (3)** respectively.

<a id="d-Aset"></a>
## Definition: the set form of the operator $`A_u`$ (D.Aset)

```math
\mathrm{Aset}(\mathcal{W},u,X) := \bigl\{\, M \in \mathrm{PairSeq} \ \bigm|\ \mathrm{Aop}(\mathcal{W},u,X,M) \,\bigr\} .
```

<a id="t-Aop_mono_X"></a>
## Theorem: monotonicity of $`A_u`$ in its third argument (T.Aop_mono_X)

### Theorem

If $`\mathrm{Aop}(\mathcal{W},u,X,M)`$ and $`X \subseteq Y`$, then
$`\mathrm{Aop}(\mathcal{W},u,Y,M)`$.

### Proof

Distinguish cases on the three disjuncts of the definition of $`\mathrm{Aop}`$ (D.Aop).

- **Branch (1).** Since $`X`$ does not occur in $`\lvert M\rvert \le 1 \wedge M_{1,0} = 0`$,
  branch (1) of $`\mathrm{Aop}(\mathcal{W},u,Y,M)`$ holds as it stands.

- **Branch (2).** The first conjunct $`\mathrm{natDom}(M)`$ holds as it stands. As for the second
  conjunct, for each $`n`$ with $`1 \le n`$ we have $`M[n] \in X`$, and $`X \subseteq Y`$ gives
  $`M[n] \in Y`$. Hence branch (2) holds.

- **Branch (3).** Both $`m \lt u`$ and $`\mathrm{domT}(M,m)`$ hold as they stand. As for the third
  conjunct, for each $`z`$ with $`z \in \mathcal{W}(m)`$ and $`\mathrm{based}(z)`$ we have
  $`\mathrm{graft}(M,z) \in X`$, and $`X \subseteq Y`$ gives $`\mathrm{graft}(M,z) \in Y`$.
  Hence branch (3) holds with the same $`m`$. ∎

<a id="t-Aset_mono"></a>
## Theorem: $`A_u`$ is monotone (T.Aset_mono)

### Theorem

For every $`\mathcal{W}`$ and $`u`$ the map $`X \mapsto \mathrm{Aset}(\mathcal{W},u,X)`$ is
monotone; that is, $`X \subseteq Y`$ implies
$`\mathrm{Aset}(\mathcal{W},u,X) \subseteq \mathrm{Aset}(\mathcal{W},u,Y)`$.

### Proof

Let $`X \subseteq Y`$ and $`M \in \mathrm{Aset}(\mathcal{W},u,X)`$. By the definition of
$`\mathrm{Aset}`$ (D.Aset) this is $`\mathrm{Aop}(\mathcal{W},u,X,M)`$.
By [T.Aop_mono_X](#t-Aop_mono_X) we get $`\mathrm{Aop}(\mathcal{W},u,Y,M)`$, and again by D.Aset,
$`M \in \mathrm{Aset}(\mathcal{W},u,Y)`$. ∎

<a id="t-Aop_mono_level"></a>
## Theorem: monotonicity of $`A_u`$ in the level (T.Aop_mono_level)

### Theorem

If $`u \le v`$ and $`\mathrm{Aop}(\mathcal{W},u,X,M)`$, then $`\mathrm{Aop}(\mathcal{W},v,X,M)`$.

### Proof

Distinguish cases on the three disjuncts of the definition of $`\mathrm{Aop}`$ (D.Aop).

- **Branch (1).** Since $`u`$ does not occur, the statement holds as it stands.
- **Branch (2).** Since $`u`$ does not occur, the statement holds as it stands.
- **Branch (3).** We have some $`m`$ with $`m \lt u`$. Together with $`u \le v`$ this gives
  $`m \lt v`$, and the remaining two conjuncts $`\mathrm{domT}(M,m)`$ and
  $`\forall z \in \mathcal{W}(m),\ \mathrm{based}(z) \to \mathrm{graft}(M,z) \in X`$ depend on
  neither $`u`$ nor $`v`$, so they hold as they stand. ∎

<a id="t-Aop_cong"></a>
## Theorem: $`A_u`$ reads only the levels below $`u`$ (T.Aop_cong)

### Theorem

Let $`\mathcal{W}`$ and $`\mathcal{V}`$ be families with
$`\forall m \lt u,\ \mathcal{W}(m) = \mathcal{V}(m)`$. Then

```math
\mathrm{Aop}(\mathcal{W},u,X,M) \iff \mathrm{Aop}(\mathcal{V},u,X,M).
```

### Proof

We prove both directions.

**($`\Rightarrow`$)** Distinguish cases on the three disjuncts of
$`\mathrm{Aop}(\mathcal{W},u,X,M)`$.

- **Branch (1).** No family occurs, so branch (1) of $`\mathrm{Aop}(\mathcal{V},u,X,M)`$ holds as it
  stands.
- **Branch (2).** No family occurs, so branch (2) holds as it stands.
- **Branch (3).** We have $`m \lt u`$, $`\mathrm{domT}(M,m)`$ and
  $`\forall z \in \mathcal{W}(m),\ \mathrm{based}(z) \to \mathrm{graft}(M,z) \in X`$.
  We prove branch (3) of $`\mathrm{Aop}(\mathcal{V},u,X,M)`$ with the same $`m`$.
  Both $`m \lt u`$ and $`\mathrm{domT}(M,m)`$ carry over unchanged. Let $`z \in \mathcal{V}(m)`$
  with $`\mathrm{based}(z)`$. By the equality $`\mathcal{W}(m) = \mathcal{V}(m)`$, obtained by
  applying the hypothesis to $`m \lt u`$, we have $`z \in \mathcal{W}(m)`$, so applying the
  conjunct we have gives $`\mathrm{graft}(M,z) \in X`$.

**($`\Leftarrow`$)** Distinguish cases on the three disjuncts of
$`\mathrm{Aop}(\mathcal{V},u,X,M)`$.

- **Branch (1).** No family occurs, so branch (1) of $`\mathrm{Aop}(\mathcal{W},u,X,M)`$ holds as it
  stands.
- **Branch (2).** No family occurs, so branch (2) holds as it stands.
- **Branch (3).** We have $`m \lt u`$, $`\mathrm{domT}(M,m)`$ and
  $`\forall z \in \mathcal{V}(m),\ \mathrm{based}(z) \to \mathrm{graft}(M,z) \in X`$.
  We prove branch (3) of $`\mathrm{Aop}(\mathcal{W},u,X,M)`$ with the same $`m`$.
  Both $`m \lt u`$ and $`\mathrm{domT}(M,m)`$ carry over unchanged. Let $`z \in \mathcal{W}(m)`$
  with $`\mathrm{based}(z)`$. Using the equality $`\mathcal{W}(m) = \mathcal{V}(m)`$ in the
  opposite direction we have $`z \in \mathcal{V}(m)`$, so applying the conjunct we have gives
  $`\mathrm{graft}(M,z) \in X`$. ∎

<a id="d-Wf"></a>
## Definition: the family of levels (D.Wf)

Define $`\mathrm{Wf}`$, the map assigning to two natural numbers $`v, m`$ a subset
$`\mathrm{Wf}(v,m)`$ of $`\mathrm{PairSeq}`$, by recursion on the first argument.

```math
\mathrm{Wf}(0, m) := \emptyset, \qquad
\mathrm{Wf}(v+1, m) := \begin{cases}
\mathrm{lfp}\bigl(\mathrm{Aset}(\mathrm{Wf}(v,-),\ v)\bigr) & (m = v) \cr
\mathrm{Wf}(v, m) & (m \ne v)
\end{cases}
```

Here $`\mathrm{Wf}(v,-)`$ is the family $`m \mapsto \mathrm{Wf}(v,m)`$, and
$`\mathrm{Aset}(\mathrm{Wf}(v,-),v)`$ is the map
$`X \mapsto \mathrm{Aset}(\mathrm{Wf}(v,-),v,X)`$. The first argument of the recursive call is
$`v`$ for $`v+1`$ and hence decreases structurally, so this definition is well defined.

<a id="d-W"></a>
## Definition: the iterated inductive set $`W_u`$ (D.W)

For $`u \in \mathbb{N}`$,

```math
W_u := \mathrm{Wf}(u+1,\ u).
```

Below we also use $`W`$ as a symbol denoting the family $`m \mapsto W_m`$ itself. Moreover, for
$`u \in \mathbb{N}`$ and $`X \subseteq \mathrm{PairSeq}`$ we abbreviate
$`A_u(X) := \mathrm{Aset}(W,u,X)`$. By the definition of $`\mathrm{Aset}`$ (D.Aset),
$`M \in A_u(X)`$ denotes $`\mathrm{Aop}(W,u,X,M)`$.

<a id="t-Wf_coh"></a>
## Theorem: coherence of the family of levels (T.Wf_coh)

### Theorem

If $`m \lt n`$ then $`\mathrm{Wf}(n,m) = \mathrm{Wf}(m+1,m)`$.

### Proof

Induction on the natural number $`n`$ (with $`m`$ fixed). The induction predicate is

```math
\Phi(n) :\equiv m \lt n \to \mathrm{Wf}(n,m) = \mathrm{Wf}(m+1,m).
```

- **Base case** $`n = 0`$: the antecedent $`m \lt 0`$ is false, so $`\Phi(0)`$ holds.

- **Inductive step** $`n = v+1`$: assume $`\Phi(v)`$, that is,
  $`m \lt v \to \mathrm{Wf}(v,m) = \mathrm{Wf}(m+1,m)`$. Assume $`m \lt v+1`$ and distinguish cases
  according to whether $`m = v`$.

  - $`m = v`$. The equality to be shown is $`\mathrm{Wf}(v+1,v) = \mathrm{Wf}(v+1,v)`$, which holds
    by reflexivity of $`=`$.

  - $`m \ne v`$. From $`m \lt v+1`$ we get $`m \le v`$, and together with $`m \ne v`$ this gives
    $`m \lt v`$. The second clause of the definition of $`\mathrm{Wf}`$ (D.Wf) branches according
    to whether $`m = v`$, and here $`m \ne v`$, so $`\mathrm{Wf}(v+1,m) = \mathrm{Wf}(v,m)`$.
    Applying the induction hypothesis $`\Phi(v)`$ to $`m \lt v`$ gives
    $`\mathrm{Wf}(v,m) = \mathrm{Wf}(m+1,m)`$. Combining,
    $`\mathrm{Wf}(v+1,m) = \mathrm{Wf}(m+1,m)`$. ∎

<a id="t-Wf_eq_W"></a>
## Theorem: the family of levels agrees with $`W`$ (T.Wf_eq_W)

### Theorem

If $`m \lt n`$ then $`\mathrm{Wf}(n,m) = W_m`$.

### Proof

By the definition of $`W_m`$ (D.W) we have $`W_m = \mathrm{Wf}(m+1,m)`$.
This is exactly the conclusion of [T.Wf_coh](#t-Wf_coh). ∎

<a id="t-W_unfold"></a>
## Theorem: the defining equation of $`W_u`$ (T.W_unfold)

### Theorem

For every $`u \in \mathbb{N}`$,

```math
W_u = \mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr).
```

### Proof

We proceed in three steps.

**Step 1: $`W_u = \mathrm{lfp}\bigl(\mathrm{Aset}(\mathrm{Wf}(u,-),u)\bigr)`$.**
By the definition of $`W`$ (D.W) we have $`W_u = \mathrm{Wf}(u+1,u)`$. Reading the second clause of
the definition of $`\mathrm{Wf}`$ (D.Wf) with $`v := u`$ and $`m := u`$, the condition $`m = v`$
holds as $`u = u`$, so the first case is selected and the value is
$`\mathrm{lfp}\bigl(\mathrm{Aset}(\mathrm{Wf}(u,-),u)\bigr)`$.

**Step 2: $`\forall m \lt u,\ \mathrm{Wf}(u,m) = W_m`$.**
Apply [T.Wf_eq_W](#t-Wf_eq_W) with $`n := u`$.

**Step 3: the two maps are equal.** We show
$`\mathrm{Aset}(\mathrm{Wf}(u,-),u,X) = \mathrm{Aset}(W,u,X)`$ for every
$`X \subseteq \mathrm{PairSeq}`$. By the definition of $`\mathrm{Aset}`$ (D.Aset), the elements of
the left-hand side are the $`M`$ satisfying $`\mathrm{Aop}(\mathrm{Wf}(u,-),u,X,M)`$, and the
elements of the right-hand side are the $`M`$ satisfying $`\mathrm{Aop}(W,u,X,M)`$. By Step 2 and
[T.Aop_cong](#t-Aop_cong) (with $`\mathcal{W} := \mathrm{Wf}(u,-)`$ and $`\mathcal{V} := W`$) these
two statements are equivalent, so the two sides have the same elements and are equal. Hence the maps
$`X \mapsto \mathrm{Aset}(\mathrm{Wf}(u,-),u,X)`$ and $`X \mapsto \mathrm{Aset}(W,u,X)`$ agree
pointwise and are equal as maps.

Substituting the equality of Step 3 into the right-hand side of Step 1 yields the conclusion. ∎

<a id="t-A1"></a>
## Theorem: the fixpoint equation (A1) (T.A1)

### Theorem

For every $`u \in \mathbb{N}`$, $`\mathrm{Aset}(W,u,W_u) = W_u`$.

### Proof

By [T.W_unfold](#t-W_unfold) we have $`W_u = \mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr)`$.
By [T.Aset_mono](#t-Aset_mono) the map $`X \mapsto \mathrm{Aset}(W,u,X)`$ is monotone, so applying
[T.lfpS_unfold](#t-lfpS_unfold) with $`f := \mathrm{Aset}(W,u)`$ gives

```math
\mathrm{Aset}\bigl(W,u,\mathrm{lfp}(\mathrm{Aset}(W,u))\bigr) = \mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr)
```

It remains to rewrite $`\mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr)`$ as $`W_u`$ on both sides. ∎

<a id="t-A2"></a>
## Theorem: the induction principle (A2) (T.A2)

### Theorem

If $`\mathrm{Aset}(W,u,Y) \subseteq Y`$ then $`W_u \subseteq Y`$.

### Proof

By [T.W_unfold](#t-W_unfold) we have $`W_u = \mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr)`$.
Applying [T.lfpS_lowerbound](#t-lfpS_lowerbound) with $`f := \mathrm{Aset}(W,u)`$ to the hypothesis
gives $`\mathrm{lfp}\bigl(\mathrm{Aset}(W,u)\bigr) \subseteq Y`$. It remains to rewrite the
left-hand side as $`W_u`$. ∎

<a id="t-A2'"></a>
## Theorem: the pointwise form of the induction principle (A2′) (T.A2')

### Theorem

If $`\mathrm{Aop}(W,u,Y,M) \to M \in Y`$ holds for every $`M \in \mathrm{PairSeq}`$, then
$`W_u \subseteq Y`$.

### Proof

By the definition of $`\mathrm{Aset}`$ (D.Aset), $`M \in \mathrm{Aset}(W,u,Y)`$ and
$`\mathrm{Aop}(W,u,Y,M)`$ are the same proposition. Hence the hypothesis is the same proposition as
$`\mathrm{Aset}(W,u,Y) \subseteq Y`$, and applying [T.A2](#t-A2) gives $`W_u \subseteq Y`$. ∎

<a id="t-A1_intro"></a>
## Theorem: introduction into $`W_u`$ (T.A1_intro)

### Theorem

If $`\mathrm{Aop}(W,u,W_u,M)`$ then $`M \in W_u`$.

### Proof

By the definition of $`\mathrm{Aset}`$ (D.Aset), the hypothesis is the same proposition as
$`M \in \mathrm{Aset}(W,u,W_u)`$. Rewriting it with the equality
$`\mathrm{Aset}(W,u,W_u) = W_u`$ of [T.A1](#t-A1) gives $`M \in W_u`$. ∎

<a id="t-W_nil"></a>
## Theorem: the empty sequence belongs to $`W_u`$ (W1) (T.W_nil)

### Theorem

For every $`u \in \mathbb{N}`$, $`() \in W_u`$.

### Proof

It suffices to apply [T.A1_intro](#t-A1_intro) with $`M := ()`$, so we show
$`\mathrm{Aop}(W,u,W_u,())`$. Choose branch (1) of the definition of $`\mathrm{Aop}`$ (D.Aop).
Its two conjuncts hold as follows.

- $`\lvert()\rvert \le 1`$: indeed $`\lvert()\rvert = 0`$.
- $`()_{1,0} = 0`$: by the definition of $`M_{i,j}`$ (D.entry), since $`0 \ge \lvert()\rvert = 0`$
  we have $`()\langle 0\rangle = (0,0)`$, whose second entry is $`0`$. ∎

<a id="t-W_mono"></a>
## Theorem: monotonicity of $`W_u`$ in the level (T.W_mono)

### Theorem

If $`u \le v`$ then $`W_u \subseteq W_v`$.

### Proof

Apply [T.A2'](#t-A2') with $`Y := W_v`$; it remains to check its hypothesis.
Take $`M \in \mathrm{PairSeq}`$ and assume $`\mathrm{Aop}(W,u,W_v,M)`$.
Applying [T.Aop_mono_level](#t-Aop_mono_level) to $`u \le v`$ gives
$`\mathrm{Aop}(W,v,W_v,M)`$, and [T.A1_intro](#t-A1_intro) gives $`M \in W_v`$. ∎

<a id="d-Rst"></a>
## Definition: the target relation on standard forms (D.Rst)

For $`a, b \in \mathrm{PairSeq}`$,

```math
a \mathbin{R_{\mathrm{st}}} b :\iff
a \in \mathrm{ST\_PS} \ \wedge\ b \in \mathrm{ST\_PS} \ \wedge\ \mathrm{tr}\,a \prec \mathrm{tr}\,b .
```

<a id="t-acc_of_translate_eq"></a>
## Theorem: accessibility depends only on the translation (T.acc_of_translate_eq)

### Theorem

In what follows, for a binary relation $`R`$ on $`\mathrm{PairSeq}`$ and $`a \in \mathrm{PairSeq}`$,
let $`\mathrm{Acc}(R,a)`$ be the least predicate generated by the single rule

```math
\bigl(\forall y,\ y \mathbin{R} a \to \mathrm{Acc}(R,y)\bigr)
\ \Longrightarrow\ \mathrm{Acc}(R,a).
```

Since this is the only rule, conversely, whenever $`\mathrm{Acc}(R,a)`$ holds its premise can be
recovered: if $`\mathrm{Acc}(R,a)`$ and $`y \mathbin{R} a`$ then $`\mathrm{Acc}(R,y)`$.
We call this **extraction** below.

The claim is the following. If $`a \in \mathrm{ST\_PS}`$, $`\mathrm{tr}\,b = \mathrm{tr}\,a`$ and
$`\mathrm{Acc}(R_{\mathrm{st}},a)`$, then $`\mathrm{Acc}(R_{\mathrm{st}},b)`$.

### Proof

By the generating rule for $`\mathrm{Acc}`$ it suffices to show
$`\mathrm{Acc}(R_{\mathrm{st}},y)`$ for every $`y`$ with $`y \mathbin{R_{\mathrm{st}}} b`$.
By the definition of $`R_{\mathrm{st}}`$ (D.Rst), $`y \mathbin{R_{\mathrm{st}}} b`$ is the
conjunction of $`y \in \mathrm{ST\_PS}`$, $`b \in \mathrm{ST\_PS}`$ and
$`\mathrm{tr}\,y \prec \mathrm{tr}\,b`$.

From this we obtain $`y \mathbin{R_{\mathrm{st}}} a`$. Its three conjuncts hold as follows.

- $`y \in \mathrm{ST\_PS}`$: this is the first conjunct just obtained.
- $`a \in \mathrm{ST\_PS}`$: this is a hypothesis.
- $`\mathrm{tr}\,y \prec \mathrm{tr}\,a`$: substitute the hypothesised equality
  $`\mathrm{tr}\,b = \mathrm{tr}\,a`$ into $`\mathrm{tr}\,y \prec \mathrm{tr}\,b`$.

Applying extraction to the hypothesis $`\mathrm{Acc}(R_{\mathrm{st}},a)`$ and
$`y \mathbin{R_{\mathrm{st}}} a`$ gives $`\mathrm{Acc}(R_{\mathrm{st}},y)`$. ∎

<a id="t-acc_of_nat_branch"></a>
## Theorem: the bridge for the $`\mathbb{N}`$ branch (T.acc_of_nat_branch)

### Theorem

We make the following hypothesis.

```math
\text{(hcof)}\quad
\forall M, N \in \mathrm{ST\_PS},\ \mathrm{tr}\,N \prec \mathrm{tr}\,M \to
  \exists n,\ \bigl(1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])\bigr)
```

Here $`\preceq`$ ([D.ole](Term.md#d-ole)) is the non-strict order. Then, if
$`c \in \mathrm{ST\_PS}`$ and $`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$ holds for every $`n`$ with
$`1 \le n`$, then $`\mathrm{Acc}(R_{\mathrm{st}},c)`$.

### Proof

By the generating rule for $`\mathrm{Acc}`$ it suffices to show
$`\mathrm{Acc}(R_{\mathrm{st}},b)`$ for every $`b`$ with $`b \mathbin{R_{\mathrm{st}}} c`$.
By the definition of $`R_{\mathrm{st}}`$ (D.Rst) we have $`b \in \mathrm{ST\_PS}`$,
$`c \in \mathrm{ST\_PS}`$ and $`\mathrm{tr}\,b \prec \mathrm{tr}\,c`$.

Applying (hcof) with $`M := c`$ and $`N := b`$, take $`n`$ with $`1 \le n`$ and
$`\mathrm{tr}\,b \preceq \mathrm{tr}\,(c[n])`$. We prepare the following two facts.

- $`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$: this is the hypothesis applied to $`n`$.
- $`c[n] \in \mathrm{ST\_PS}`$: this is rule (oper) of the definition of $`\mathrm{ST\_PS}`$
  (D.ST_PS) applied to $`c \in \mathrm{ST\_PS}`$ and $`1 \le n`$.

By the definition of $`\preceq`$ (D.ole), $`\mathrm{tr}\,b \preceq \mathrm{tr}\,(c[n])`$ splits into
the following two cases.

- $`\mathrm{tr}\,b \prec \mathrm{tr}\,(c[n])`$. Then $`b \mathbin{R_{\mathrm{st}}} c[n]`$ holds
  (its three conjuncts are $`b \in \mathrm{ST\_PS}`$, $`c[n] \in \mathrm{ST\_PS}`$ and the present
  strict inequality). Applying extraction to $`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$ gives
  $`\mathrm{Acc}(R_{\mathrm{st}},b)`$.

- $`\mathrm{tr}\,b = \mathrm{tr}\,(c[n])`$. Apply
  [T.acc_of_translate_eq](#t-acc_of_translate_eq) with $`a := c[n]`$ and $`b := b`$.
  Its three hypotheses $`c[n] \in \mathrm{ST\_PS}`$, $`\mathrm{tr}\,b = \mathrm{tr}\,(c[n])`$ and
  $`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$ are all available, and its conclusion is
  $`\mathrm{Acc}(R_{\mathrm{st}},b)`$. ∎

<a id="t-acc_of_W"></a>
## Theorem: the bridge (elements of $`W_u`$ are accessible) (T.acc_of_W)

### Theorem

Assume (hcof). Then $`\mathrm{Acc}(R_{\mathrm{st}},M)`$ for every $`u \in \mathbb{N}`$ and every
$`M \in W_u`$.

### Proof

Put $`Y := \{\, M \in \mathrm{PairSeq} \mid \mathrm{Acc}(R_{\mathrm{st}},M) \,\}`$; then the claim
to be shown is $`W_u \subseteq Y`$. We apply [T.A2'](#t-A2'), so it suffices to take
$`c \in \mathrm{PairSeq}`$, assume $`\mathrm{Aop}(W,u,Y,c)`$ and show
$`\mathrm{Acc}(R_{\mathrm{st}},c)`$. Distinguish cases according to whether
$`c \in \mathrm{ST\_PS}`$.

**(I) $`c \notin \mathrm{ST\_PS}`$.**
By the generating rule for $`\mathrm{Acc}`$ it suffices to show
$`\mathrm{Acc}(R_{\mathrm{st}},y)`$ for every $`y`$ with $`y \mathbin{R_{\mathrm{st}}} c`$.
But the second conjunct of the definition of $`R_{\mathrm{st}}`$ (D.Rst) is
$`c \in \mathrm{ST\_PS}`$, contrary to the assumption of the present case. Hence no such $`y`$
exists, the antecedent is false, and $`\mathrm{Acc}(R_{\mathrm{st}},c)`$ holds.

**(II) $`c \in \mathrm{ST\_PS}`$.**
Distinguish cases on the three disjuncts of the definition of $`\mathrm{Aop}`$ (D.Aop) applied to
$`\mathrm{Aop}(W,u,Y,c)`$.

**Branch (1): $`\lvert c\rvert \le 1`$ and $`c_{1,0} = 0`$.**
By [T.stps_len_pos](Column.md#t-stps_len_pos) we have $`0 \lt \lvert c\rvert`$, and together with
$`\lvert c\rvert \le 1`$ this gives $`\lvert c\rvert = 1`$. Hence there is a pair
$`p = (p_1,p_2)`$ with $`c = (p)`$. By the definition of $`M_{i,j}`$ (D.entry) we have
$`c_{1,0} = p_2`$, so $`p_2 = 0`$.

We compute $`\mathrm{tr}\,c`$. Apply [T.translate_single_tree](Term.md#t-translate_single_tree) with
$`p := p`$ and $`R := ()`$ (its hypothesis, that every element $`x`$ of $`R`$ satisfies
$`p_1 \lt x_1`$, holds because $`R = ()`$ has no elements), which gives

```math
\mathrm{tr}\,(p) = \mathsf{P}\bigl(p_2,\ \mathrm{tr}\,(),\ \mathsf{Z}\bigr)
= \mathsf{P}(0,\mathsf{Z},\mathsf{Z})
```

(here $`\mathrm{tr}\,() = \mathsf{Z}`$ is the first clause of the definition of $`\mathrm{tr}`$
(D.translate), and $`p_2 = 0`$ was shown above).

By the generating rule for $`\mathrm{Acc}`$ it suffices to show
$`\mathrm{Acc}(R_{\mathrm{st}},y)`$ for every $`y`$ with $`y \mathbin{R_{\mathrm{st}}} c`$.
The definition of $`R_{\mathrm{st}}`$ (D.Rst) gives $`y \in \mathrm{ST\_PS}`$ and
$`\mathrm{tr}\,y \prec \mathrm{tr}\,c = \mathsf{P}(0,\mathsf{Z},\mathsf{Z})`$.
By [T.eq_Z_of_olt_one](#t-eq_Z_of_olt_one) we have $`\mathrm{tr}\,y = \mathsf{Z}`$, and by
[T.translate_eq_Z_iff](#t-translate_eq_Z_iff) we have $`y = ()`$. On the other hand, applying
[T.stps_ne_nil](#t-stps_ne_nil) to $`y \in \mathrm{ST\_PS}`$ gives $`y \ne ()`$, a contradiction.
Hence no such $`y`$ exists, the antecedent is false, and $`\mathrm{Acc}(R_{\mathrm{st}},c)`$ holds.

**Branch (2): $`\mathrm{natDom}(c)`$ and $`\forall n \ge 1,\ c[n] \in Y`$.**
By the definition of $`Y`$, the second conjunct says that $`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$
holds for every $`n`$ with $`1 \le n`$. Applying
[T.acc_of_nat_branch](#t-acc_of_nat_branch) to this and to $`c \in \mathrm{ST\_PS}`$ gives
$`\mathrm{Acc}(R_{\mathrm{st}},c)`$.

**Branch (3): for some $`m \lt u`$, $`\mathrm{domT}(c,m)`$ and
$`\forall z \in W_m,\ \mathrm{based}(z) \to \mathrm{graft}(c,z) \in Y`$.**
Distinguish further cases according to whether $`1 \lt \lvert c\rvert`$.

**(3a) $`1 \lt \lvert c\rvert`$.**
We apply [T.acc_of_nat_branch](#t-acc_of_nat_branch), so it suffices to show
$`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$ for each $`n`$ with $`1 \le n`$.
By [T.W_nil](#t-W_nil) we have $`() \in W_m`$, and by [T.based_nil](#t-based_nil) we have
$`\mathrm{based}(())`$, so applying the third conjunct of branch (3) with $`z := ()`$ gives
$`\mathrm{graft}(c,()) \in Y`$. Moreover, applying
[T.oper_eq_graft_nil_of_domT](#t-oper_eq_graft_nil_of_domT) to
$`1 \lt \lvert c\rvert`$ and $`\mathrm{domT}(c,m)`$ gives
$`c[n] = \mathrm{graft}(c,())`$. Together these give $`c[n] \in Y`$, that is,
$`\mathrm{Acc}(R_{\mathrm{st}},c[n])`$.

**(3b) $`\neg\bigl(1 \lt \lvert c\rvert\bigr)`$.**
By [T.stps_len_pos](Column.md#t-stps_len_pos) we have $`0 \lt \lvert c\rvert`$, hence
$`\lvert c\rvert = 1`$. By [T.stps_len_one](#t-stps_len_one) we have
$`c = \bigl((0,0)\bigr)`$. The first conjunct of $`\mathrm{domT}(c,m)`$ (D.domT) is
$`c_{1,\lvert c\rvert-1} = m+1`$, and since $`\lvert c\rvert - 1 = 0`$ and
$`c_{1,0} = 0`$ by the definition of $`M_{i,j}`$ (D.entry), this reads $`0 = m+1`$.
In the natural numbers $`m+1 \ne 0`$, a contradiction, so this case does not occur. ∎

<a id="d-argOK"></a>
## Definition: argument block (D.argOK)

For $`R \in \mathrm{PairSeq}`$,

```math
\mathrm{argOK}(R) :\iff \forall p \in R,\ 0 \lt p_1 .
```

That is, the first entry of every pair of $`R`$ is strictly greater than $`0`$.

<a id="d-rsum"></a>
## Definition: trailing block with minimal head (D.rsum)

For $`A, P \in \mathrm{PairSeq}`$,

```math
\mathrm{rsum}(A,P) :\iff \forall p \in A \mathbin{+\!\!+} P,\ P_{0,0} \le p_1 .
```

That is, the first entry of the head pair of $`P`$ is a lower bound for the first entries of all
elements of the concatenation $`A \mathbin{+\!\!+} P`$.

<a id="t-nextR_shift_iff"></a>
## Theorem: the parent relation is invariant under a shift of row 0 (T.nextR_shift_iff)

### Theorem

Let $`S \in \mathrm{PairSeq}`$ and $`d, i, a, b \in \mathbb{N}`$, and suppose $`b \lt \lvert S\rvert`$. Then

```math
a \to^{S^{+d}}_i b \iff a \to^S_i b .
```

### Proof

The definition of $`\to^{\cdot}_i`$ (D.nextR) is a case distinction according to whether $`i = 0`$.

- $`i = 0`$. The two sides are $`a \to^{S^{+d}}_0 b`$ and $`a \to^S_0 b`$ respectively, and under
  the hypothesis $`b \lt \lvert S\rvert`$ this equivalence is given by
  [T.nextrel0_shift_iff](Column-4.md#t-nextrel0_shift_iff).

- $`i \ne 0`$. The two sides are $`a \to^{S^{+d}}_1 b`$ and $`a \to^S_1 b`$ respectively, and under
  the hypothesis $`b \lt \lvert S\rvert`$ this equivalence is given by
  [T.nextrel1_shift_iff](Column-4.md#t-nextrel1_shift_iff). ∎
