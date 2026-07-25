[← README](README.md) | [English](Seqlex-2.md) | [Japanese](Seqlex-2-ja.md) | Seqlex [1](Seqlex.md) **2**

<a id="t-seqlex_imp_olt"></a>
## Theorem: from the column-lex order to the order on terms (T.seqlex_imp_olt)

### Theorem

Let $`d \in \mathbb{N}`$ and $`M, N \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)).
If $`\mathrm{blockok}(d, M)`$ ([D.blockok](Seqlex.md#d-blockok)), $`\mathrm{blockok}(d, N)`$ and
$`M \prec_{\mathrm{lex}} N`$ ([D.seqlex](Seqlex.md#d-seqlex)), then

```math
\mathrm{tr}\,M \prec \mathrm{tr}\,N .
```

($`\mathrm{tr}`$ [D.translate](Term.md#d-translate), $`\prec`$ [D.olt](Term.md#d-olt))

### Proof

By strong induction on $`\lvert M\rvert + \lvert N\rvert`$. The depth $`d`$ moves from $`d`$ to $`d+1`$
in the course of the recursion, so $`d`$ is universally quantified in the induction predicate. That is, put

```math
\Phi(M, N) :\equiv \forall d \in \mathbb{N},\
  \bigl(\mathrm{blockok}(d,M) \wedge \mathrm{blockok}(d,N) \wedge M \prec_{\mathrm{lex}} N\bigr)
  \to \mathrm{tr}\,M \prec \mathrm{tr}\,N
```

so that the induction hypothesis reads: $`\Phi(M', N')`$ holds for all $`M', N'`$ with
$`\lvert M'\rvert + \lvert N'\rvert \lt \lvert M\rvert + \lvert N\rvert`$.

We distinguish four cases according to the constructors of $`M`$ and $`N`$.

**(1) $`M = ()`$ and $`N = ()`$.**
By the first clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex), $`() \prec_{\mathrm{lex}} ()`$
is the same proposition as $`() \ne ()`$, which contradicts reflexivity of $`=`$. Hence the antecedent is false.

**(2) $`M = ()`$ and $`N = q :: N'`$.**
By the first clause of the definition of $`\mathrm{tr}`$ (D.translate) we have $`\mathrm{tr}\,() = \mathsf{Z}`$ ([D.Three](Term.md#d-Three)), and
by the second clause $`\mathrm{tr}(q :: N') = \mathsf{P}\bigl(q_2, \mathrm{tr}(\mathrm{tw}_{q_1}N'), \mathrm{tr}(\mathrm{dw}_{q_1}N')\bigr)`$.
By [T.olt_Z_P](Term.md#t-olt_Z_P), $`\mathsf{Z} \prec \mathsf{P}(\cdot,\cdot,\cdot)`$.

**(3) $`M = p :: r`$ and $`N = ()`$.**
By [T.not_seqlex_nil](Seqlex.md#t-not_seqlex_nil), $`(p :: r) \prec_{\mathrm{lex}} ()`$ is false, so the antecedent is false.

**(4) $`M = p :: r`$ and $`N = q :: r'`$.**
Applying the first conjunct of $`\mathrm{blockok}(d, p :: r)`$ to $`p :: r \ne ()`$ gives
$`\bigl(\mathrm{head}(p :: r)\bigr)_1 = d`$, that is, $`p_1 = d`$.
Applying the first conjunct of $`\mathrm{blockok}(d, q :: r')`$ to $`q :: r' \ne ()`$ gives
$`\bigl(\mathrm{head}(q :: r')\bigr)_1 = d`$, that is, $`q_1 = d`$.
So, putting $`y := p_2`$ and $`y' := q_2`$, we may write $`p = (d, y)`$ and $`q = (d, y')`$.
By the second clause of the definition of $`\mathrm{tr}`$ (D.translate),

```math
\mathrm{tr}\bigl((d,y) :: r\bigr)
  = \mathsf{P}\bigl(y,\ \mathrm{tr}(\mathrm{tw}_{d}\,r),\ \mathrm{tr}(\mathrm{dw}_{d}\,r)\bigr),
```
```math
\mathrm{tr}\bigl((d,y') :: r'\bigr)
  = \mathsf{P}\bigl(y',\ \mathrm{tr}(\mathrm{tw}_{d}\,r'),\ \mathrm{tr}(\mathrm{dw}_{d}\,r')\bigr)
```

We distinguish cases according to whether $`y`$ and $`y'`$ are equal.

**(4a) $`y = y'`$.**
By [T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons), the hypothesis $`(d,y) :: r \prec_{\mathrm{lex}} (d,y) :: r'`$ says that
$`(d,y) \prec_{\mathrm{p}} (d,y)`$ ([D.pairlt](Seqlex.md#d-pairlt)) or
$`\bigl((d,y) = (d,y) \wedge r \prec_{\mathrm{lex}} r'\bigr)`$.
By the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt), the first disjunct says $`d \lt d`$ or
$`(d = d \wedge y \lt y)`$, and both are false by irreflexivity of $`\lt`$.
Hence $`r \prec_{\mathrm{lex}} r'`$ holds.

Applying [T.seqlex_arg_or_tail](Seqlex.md#t-seqlex_arg_or_tail) to $`d`$ and $`r \prec_{\mathrm{lex}} r'`$,
one of the following holds.

- (i) $`\mathrm{tw}_d\,r = \mathrm{tw}_d\,r'`$ and $`\mathrm{dw}_d\,r \prec_{\mathrm{lex}} \mathrm{dw}_d\,r'`$
- (ii) $`\mathrm{tw}_d\,r \ne \mathrm{tw}_d\,r'`$ and $`\mathrm{tw}_d\,r \prec_{\mathrm{lex}} \mathrm{tw}_d\,r'`$

**Case (i).** Applying [T.blockok_tail](Seqlex.md#t-blockok_tail) to $`\mathrm{blockok}(d, (d,y) :: r)`$ and
$`\mathrm{blockok}(d, (d,y) :: r')`$ gives $`\mathrm{blockok}(d, \mathrm{dw}_d\,r)`$ and
$`\mathrm{blockok}(d, \mathrm{dw}_d\,r')`$. By the definitions of $`\mathrm{tw}`$ and $`\mathrm{dw}`$ (D.translate) we have
$`\mathrm{tw}_d\,r \mathbin{+\!\!+} \mathrm{dw}_d\,r = r`$, hence
$`\lvert \mathrm{dw}_d\,r\rvert \le \lvert \mathrm{tw}_d\,r\rvert + \lvert \mathrm{dw}_d\,r\rvert = \lvert r\rvert`$, and
using the same identity for $`r'`$,
$`\lvert \mathrm{dw}_d\,r'\rvert \le \lvert \mathrm{tw}_d\,r'\rvert + \lvert \mathrm{dw}_d\,r'\rvert = \lvert r'\rvert`$. Therefore

```math
\lvert \mathrm{dw}_d\,r\rvert + \lvert \mathrm{dw}_d\,r'\rvert
  \le \lvert r\rvert + \lvert r'\rvert
  \lt \lvert (d,y) :: r\rvert + \lvert (d,y) :: r'\rvert
```

Hence the induction hypothesis may be applied to $`(\mathrm{dw}_d\,r, \mathrm{dw}_d\,r')`$ at depth $`d`$, giving

```math
\mathrm{tr}(\mathrm{dw}_d\,r) \prec \mathrm{tr}(\mathrm{dw}_d\,r')
```

From the first conjunct of (i) we get $`\mathrm{tr}(\mathrm{tw}_d\,r) = \mathrm{tr}(\mathrm{tw}_d\,r')`$, so the third
disjunct on the right-hand side of [T.olt_P_P](Term.md#t-olt_P_P),
$`y = y \wedge \mathrm{tr}(\mathrm{tw}_d r) = \mathrm{tr}(\mathrm{tw}_d r') \wedge \mathrm{tr}(\mathrm{dw}_d r) \prec \mathrm{tr}(\mathrm{dw}_d r')`$,
holds, and the conclusion follows.

**Case (ii).** Applying [T.blockok_arg](Seqlex.md#t-blockok_arg) to the same two hypotheses gives
$`\mathrm{blockok}(d+1, \mathrm{tw}_d\,r)`$ and $`\mathrm{blockok}(d+1, \mathrm{tw}_d\,r')`$.
By the definitions of $`\mathrm{tw}`$ and $`\mathrm{dw}`$ (D.translate) we have
$`\mathrm{tw}_d\,r \mathbin{+\!\!+} \mathrm{dw}_d\,r = r`$, hence
$`\lvert \mathrm{tw}_d\,r\rvert \le \lvert \mathrm{tw}_d\,r\rvert + \lvert \mathrm{dw}_d\,r\rvert = \lvert r\rvert`$, and
using the same identity for $`r'`$,
$`\lvert \mathrm{tw}_d\,r'\rvert \le \lvert \mathrm{tw}_d\,r'\rvert + \lvert \mathrm{dw}_d\,r'\rvert = \lvert r'\rvert`$. Therefore

```math
\lvert \mathrm{tw}_d\,r\rvert + \lvert \mathrm{tw}_d\,r'\rvert
  \le \lvert r\rvert + \lvert r'\rvert
  \lt \lvert (d,y) :: r\rvert + \lvert (d,y) :: r'\rvert
```

Hence the induction hypothesis may be applied to $`(\mathrm{tw}_d\,r, \mathrm{tw}_d\,r')`$ at depth $`d+1`$, giving

```math
\mathrm{tr}(\mathrm{tw}_d\,r) \prec \mathrm{tr}(\mathrm{tw}_d\,r')
```

The second disjunct on the right-hand side of [T.olt_P_P](Term.md#t-olt_P_P),
$`y = y \wedge \mathrm{tr}(\mathrm{tw}_d r) \prec \mathrm{tr}(\mathrm{tw}_d r')`$, holds, and the conclusion follows.

**(4b) $`y \ne y'`$.**
By [T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons), the hypothesis says that
$`(d,y) \prec_{\mathrm{p}} (d,y')`$ or $`\bigl((d,y) = (d,y') \wedge r \prec_{\mathrm{lex}} r'\bigr)`$.
If the second disjunct held, injectivity of the constructor of pairs would give $`y = y'`$, contradicting the hypothesis.
Hence $`(d,y) \prec_{\mathrm{p}} (d,y')`$, and by the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt) this says
$`d \lt d`$ or $`(d = d \wedge y \lt y')`$. The former contradicts irreflexivity of $`\lt`$, so
$`y \lt y'`$. This is the first disjunct on the right-hand side of [T.olt_P_P](Term.md#t-olt_P_P), so
together with the two translation formulas written above the conclusion follows. ∎

<a id="t-seqlex_total"></a>
## Theorem: trichotomy for the column-lex order (T.seqlex_total)

### Theorem

For all $`M, N \in \mathrm{PairSeq}`$,

```math
M = N \ \vee\ M \prec_{\mathrm{lex}} N \ \vee\ N \prec_{\mathrm{lex}} M .
```

### Proof

By induction on the list structure of $`M`$ (with $`N`$ left universally quantified). The induction predicate is

```math
\Phi(M) :\equiv \forall N \in \mathrm{PairSeq},\
  \bigl(M = N \vee M \prec_{\mathrm{lex}} N \vee N \prec_{\mathrm{lex}} M\bigr).
```

**Base case $`M = ()`$.** We distinguish cases on the constructor of $`N`$.

- $`N = ()`$. Then $`M = N`$ holds (first disjunct).
- $`N = q :: N'`$. By [T.seqlex_nil_iff](Seqlex.md#t-seqlex_nil_iff),
  $`() \prec_{\mathrm{lex}} (q :: N')`$ is equivalent to $`q :: N' \ne ()`$, and this holds because the images of
  the constructors of sequences are pairwise disjoint (second disjunct).

**Inductive step $`M = p :: M'`$.** The induction hypothesis is $`\Phi(M')`$, that is,
$`\forall N,\ (M' = N \vee M' \prec_{\mathrm{lex}} N \vee N \prec_{\mathrm{lex}} M')`$.
We distinguish cases on the constructor of $`N`$.

- $`N = ()`$. By [T.seqlex_nil_iff](Seqlex.md#t-seqlex_nil_iff),
  $`() \prec_{\mathrm{lex}} (p :: M')`$ is equivalent to $`p :: M' \ne ()`$, which holds (third disjunct).

- $`N = q :: N'`$. We distinguish further according to whether $`p = q`$.

**Case $`p = q`$.** Applying the induction hypothesis $`\Phi(M')`$ to $`N'`$ splits into three cases.

- $`M' = N'`$. Together with $`p = q`$ this gives $`p :: M' = q :: N'`$ (first disjunct).
- $`M' \prec_{\mathrm{lex}} N'`$. The second disjunct on the right-hand side of [T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons),
  $`p = q \wedge M' \prec_{\mathrm{lex}} N'`$, holds, so $`p :: M' \prec_{\mathrm{lex}} q :: N'`$ (second disjunct).
- $`N' \prec_{\mathrm{lex}} M'`$. The second disjunct on the right-hand side of [T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons),
  $`q = p \wedge N' \prec_{\mathrm{lex}} M'`$, holds, so
  $`q :: N' \prec_{\mathrm{lex}} p :: M'`$ (third disjunct).

**Case $`p \ne q`$.** First we show
$`p \prec_{\mathrm{p}} q \vee q \prec_{\mathrm{p}} p`$.
Applying the trichotomy of $`\lt`$ on $`\mathbb{N}`$ to $`p_1`$ and $`q_1`$ splits into three cases.

- $`p_1 \lt q_1`$. By the first disjunct of the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt),
  $`p \prec_{\mathrm{p}} q`$.
- $`p_1 = q_1`$. Apply the trichotomy of $`\lt`$ on $`\mathbb{N}`$ to $`p_2`$ and $`q_2`$ once more.
  - $`p_2 \lt q_2`$. The second disjunct of the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt),
    $`p_1 = q_1 \wedge p_2 \lt q_2`$, gives $`p \prec_{\mathrm{p}} q`$.
  - $`p_2 = q_2`$. From $`p_1 = q_1`$ and $`p_2 = q_2`$, extensionality of pairs gives $`p = q`$,
    contradicting the hypothesis $`p \ne q`$.
  - $`q_2 \lt p_2`$. Together with $`q_1 = p_1`$, the second disjunct of the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt)
    gives $`q \prec_{\mathrm{p}} p`$.
- $`q_1 \lt p_1`$. By the first disjunct of the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt),
  $`q \prec_{\mathrm{p}} p`$.

In every case we have obtained $`p \prec_{\mathrm{p}} q`$ or $`q \prec_{\mathrm{p}} p`$.
In the former case the first disjunct $`p \prec_{\mathrm{p}} q`$ on the right-hand side of [T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons) gives
$`p :: M' \prec_{\mathrm{lex}} q :: N'`$ (second disjunct), and in the latter case the first disjunct
$`q \prec_{\mathrm{p}} p`$ on the right-hand side of [T.seqlex_cons_cons](Seqlex.md#t-seqlex_cons_cons) gives
$`q :: N' \prec_{\mathrm{lex}} p :: M'`$ (third disjunct). ∎

<a id="t-olt_iff_seqlex"></a>
## Theorem: order isomorphism on blocks (T.olt_iff_seqlex)

### Theorem

Let $`d \in \mathbb{N}`$ and $`M, N \in \mathrm{PairSeq}`$.
If $`\mathrm{blockok}(d, M)`$, $`\mathrm{blockok}(d, N)`$ and $`M \ne N`$, then

```math
\mathrm{tr}\,M \prec \mathrm{tr}\,N \iff M \prec_{\mathrm{lex}} N .
```

### Proof

We prove both directions.

**($`\Rightarrow`$)** Assume $`\mathrm{tr}\,M \prec \mathrm{tr}\,N`$.
Suppose that $`M \prec_{\mathrm{lex}} N`$ does not hold, and derive a contradiction.
Applying [T.seqlex_total](#t-seqlex_total) to $`M`$ and $`N`$ gives the following three cases.

- $`M = N`$. This contradicts the hypothesis $`M \ne N`$.
- $`M \prec_{\mathrm{lex}} N`$. This contradicts the assumption just made, that $`M \prec_{\mathrm{lex}} N`$ does not hold.
- $`N \prec_{\mathrm{lex}} M`$. Applying [T.seqlex_imp_olt](#t-seqlex_imp_olt) to
  $`d`$, $`N`$, $`M`$, $`\mathrm{blockok}(d,N)`$ and $`\mathrm{blockok}(d,M)`$ gives
  $`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$. Applying [T.olt_trans](Term.md#t-olt_trans) to this and
  $`\mathrm{tr}\,M \prec \mathrm{tr}\,N`$ gives $`\mathrm{tr}\,M \prec \mathrm{tr}\,M`$, which
  contradicts [T.olt_irrefl](Term.md#t-olt_irrefl).

Since every case leads to a contradiction, $`M \prec_{\mathrm{lex}} N`$ holds.

**($`\Leftarrow`$)** It suffices to apply [T.seqlex_imp_olt](#t-seqlex_imp_olt) to $`d`$, $`M`$, $`N`$. ∎

<a id="t-getLastD_eq_getD"></a>
## Theorem: the last element expressed by indexing (T.getLastD_eq_getD)

### Theorem

For a finite sequence $`l`$ of type $`\alpha`$ and $`d \in \alpha`$,

```math
\mathrm{last}_d\,l = l\langle \lvert l\rvert - 1\rangle_d .
```

Here

```math
l\langle i\rangle_d := \begin{cases} l_i & (i \lt \lvert l\rvert) \cr d & (i \ge \lvert l\rvert) \end{cases}
```

and the subtraction is truncated subtraction of natural numbers. For $`\alpha = \mathbb{N}\times\mathbb{N}`$ and $`d = (0,0)`$,
$`l\langle i\rangle_{(0,0)}`$ is the $`l\langle i\rangle`$ occurring in the definition of $`M_{i,j}`$ ([D.entry](Pss.md#d-entry)).

### Proof

We distinguish cases according to whether $`l`$ is empty.

- $`l = ()`$. By the first clause of the definition of $`\mathrm{last}_d`$, the left-hand side is $`d`$.
  On the right-hand side $`\lvert l\rvert - 1 = 0 - 1 = 0`$, and $`0 \lt \lvert l\rvert = 0`$ is false, so by
  the second clause of the definition of $`\langle\cdot\rangle_d`$ it is $`d`$.

- $`l \ne ()`$. Then $`1 \le \lvert l\rvert`$, hence $`\lvert l\rvert - 1 \lt \lvert l\rvert`$, and
  by the first clause of the definition of $`\langle\cdot\rangle_d`$ the right-hand side is $`l_{\lvert l\rvert - 1}`$.
  By the second clause of the definition of $`\mathrm{last}_d`$ the left-hand side is $`l_{\lvert l\rvert - 1}`$ as well. ∎

<a id="t-getLastD_ne_nil_indep"></a>
## Theorem: the last element of a non-empty sequence does not depend on the default value (T.getLastD_ne_nil_indep)

### Theorem

If a finite sequence $`B`$ of type $`\alpha`$ satisfies $`B \ne ()`$, then for all $`d, d' \in \alpha`$

```math
\mathrm{last}_d\,B = \mathrm{last}_{d'}\,B .
```

### Proof

We distinguish cases on the constructor of $`B`$.

- $`B = ()`$. This contradicts the hypothesis $`B \ne ()`$.

- $`B = b :: bs`$. By the second clause of the definition of $`\mathrm{last}_d`$, both sides are equal to
  $`(b :: bs)_{\lvert b :: bs\rvert - 1}`$. This value depends neither on $`d`$ nor on $`d'`$. ∎

<a id="t-headI_append_left"></a>
## Theorem: the head of a concatenation whose left part is non-empty (T.headI_append_left)

### Theorem

For finite sequences $`A, B`$ of type $`\alpha`$, if $`A \ne ()`$ then

```math
\mathrm{head}(A \mathbin{+\!\!+} B) = \mathrm{head}\,A .
```

### Proof

We distinguish cases on the constructor of $`A`$.

- $`A = ()`$. This contradicts the hypothesis $`A \ne ()`$.

- $`A = a :: as`$. Since $`(a :: as) \mathbin{+\!\!+} B = a :: (as \mathbin{+\!\!+} B)`$, the left-hand side is
  $`a`$ by the definition of $`\mathrm{head}`$. The right-hand side is $`\mathrm{head}(a :: as) = a`$ as well. ∎

<a id="t-getLastD_append_right"></a>
## Theorem: the last element of a concatenation whose right part is non-empty (T.getLastD_append_right)

### Theorem

For finite sequences $`A, B`$ of type $`\alpha`$, if $`B \ne ()`$ then for every $`d \in \alpha`$

```math
\mathrm{last}_d(A \mathbin{+\!\!+} B) = \mathrm{last}_d\,B .
```

### Proof

By induction on the list structure of $`A`$ (with $`d`$ left universally quantified). The induction predicate is

```math
\Phi(A) :\equiv \forall d \in \alpha,\ \mathrm{last}_d(A \mathbin{+\!\!+} B) = \mathrm{last}_d\,B .
```

- **Base case** $`A = ()`$: since $`() \mathbin{+\!\!+} B = B`$, the two sides are identical.

**Inductive step $`A = a :: A'`$.** The induction hypothesis is $`\Phi(A')`$, that is,
$`\forall d,\ \mathrm{last}_d(A' \mathbin{+\!\!+} B) = \mathrm{last}_d\,B`$.
First we show that for every $`b \in \alpha`$ and every finite sequence $`bs`$ of type $`\alpha`$,

```math
\mathrm{last}_d(b :: bs) = \mathrm{last}_b\,bs
```

holds. If $`bs = ()`$, then $`b :: bs = (b) \ne ()`$, so by the second clause of the definition of
$`\mathrm{last}_d`$ the left-hand side is $`(b)_{\lvert (b)\rvert - 1} = (b)_0 = b`$, while the
right-hand side is $`\mathrm{last}_b\,()`$, which is $`b`$ by the first clause of the same definition.
If $`bs \ne ()`$, then $`b :: bs \ne ()`$ as well, so applying the second clause of the definition of
$`\mathrm{last}_d`$ to both sides, the left-hand side is
$`(b :: bs)_{\lvert b :: bs\rvert - 1} = (b :: bs)_{\lvert bs\rvert}`$ and the right-hand side is
$`bs_{\lvert bs\rvert - 1}`$. Since $`\lvert bs\rvert \ge 1`$, the element of $`b :: bs`$ at index
$`\lvert bs\rvert`$ is the element of $`bs`$ at index $`\lvert bs\rvert - 1`$, so the two sides are equal.

Since $`(a :: A') \mathbin{+\!\!+} B = a :: (A' \mathbin{+\!\!+} B)`$, applying this formula with
$`b := a`$ and $`bs := A' \mathbin{+\!\!+} B`$ gives

```math
\mathrm{last}_d\bigl(a :: (A' \mathbin{+\!\!+} B)\bigr) = \mathrm{last}_a(A' \mathbin{+\!\!+} B)
```

Applying here the induction hypothesis $`\Phi(A')`$ with $`d := a`$ gives
$`\mathrm{last}_a(A' \mathbin{+\!\!+} B) = \mathrm{last}_a\,B`$.
Finally, $`B \ne ()`$ and [T.getLastD_ne_nil_indep](#t-getLastD_ne_nil_indep) give
$`\mathrm{last}_a\,B = \mathrm{last}_d\,B`$. Hence $`\Phi(a :: A')`$. ∎

<a id="t-steps1_flatMap"></a>
## Theorem: the step-1 condition for a concatenation of blocks (T.steps1_flatMap)

### Theorem

Let $`F : \mathbb{N} \to \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$, and put

```math
\mathrm{cat}_n F := F(0) \mathbin{+\!\!+} F(1) \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} F(n-1)
```

(the empty sequence when $`n = 0`$). Assume the following three conditions.

```math
\begin{aligned}
&\text{(F1)}\quad \forall k \lt n,\ \mathrm{steps}_1\bigl(F(k)\bigr), \cr
&\text{(Fne)}\quad \forall k \lt n,\ F(k) \ne (), \cr
&\text{(Fj)}\quad \forall k,\ k + 1 \lt n \to
   \bigl(\mathrm{head}\,F(k+1)\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)} F(k)\bigr)_1 + 1 .
\end{aligned}
```

($`\mathrm{steps}_1`$ [D.steps1](Seqlex.md#d-steps1))

Then $`\mathrm{steps}_1(\mathrm{cat}_n F)`$ holds, and moreover, if $`0 \lt n`$, then

```math
\mathrm{cat}_n F \ne (),
\qquad
\mathrm{head}(\mathrm{cat}_n F) = \mathrm{head}\,F(0),
\qquad
\mathrm{last}_{(0,0)}(\mathrm{cat}_n F) = \mathrm{last}_{(0,0)} F(n-1)
```

hold.

### Proof

Induction on the natural number $`n`$, with $`F`$ fixed. The induction predicate is

```math
\begin{aligned}
\Phi(n) :\equiv\ &\Bigl(\forall k \lt n,\ \mathrm{steps}_1(F(k))\Bigr)
  \wedge \Bigl(\forall k \lt n,\ F(k) \ne ()\Bigr) \cr
&\wedge \Bigl(\forall k,\ k+1 \lt n \to
   (\mathrm{head}\,F(k+1))_1 \le (\mathrm{last}_{(0,0)} F(k))_1 + 1\Bigr) \cr
&\to\ \mathrm{steps}_1(\mathrm{cat}_n F) \wedge \Bigl(0 \lt n \to
   \bigl(\mathrm{cat}_n F \ne ()
   \wedge \mathrm{head}(\mathrm{cat}_n F) = \mathrm{head}\,F(0) \cr
&\qquad\qquad\qquad
   \wedge \mathrm{last}_{(0,0)}(\mathrm{cat}_n F) = \mathrm{last}_{(0,0)} F(n-1)\bigr)\Bigr) .
\end{aligned}
```

**Base case $`n = 0`$.** We have $`\mathrm{cat}_0 F = ()`$.
By [T.steps1_nil](Seqlex.md#t-steps1_nil), $`\mathrm{steps}_1(())`$ holds.
The antecedent $`0 \lt 0`$ of the second conjunct is false, so that implication holds.

**Inductive step $`n = m + 1`$.** The induction hypothesis is $`\Phi(m)`$.
By the definition of $`\mathrm{cat}`$ and associativity of concatenation,

```math
\mathrm{cat}_{m+1} F = \mathrm{cat}_m F \mathbin{+\!\!+} F(m)
```

We distinguish cases according to whether $`m`$ is $`0`$.

**(a) $`m = 0`$.** We have $`\mathrm{cat}_1 F = F(0)`$.
Applying (F1) with $`k := 0 \lt 1`$ gives $`\mathrm{steps}_1(F(0))`$.
Moreover, when $`0 \lt 1`$, applying (Fne) with $`k := 0`$ gives $`F(0) \ne ()`$; the two sides of
$`\mathrm{head}(\mathrm{cat}_1 F) = \mathrm{head}\,F(0)`$ are identical, and the two sides of
$`\mathrm{last}_{(0,0)}(\mathrm{cat}_1 F) = \mathrm{last}_{(0,0)} F(0) = \mathrm{last}_{(0,0)} F(1-1)`$
are identical as well.

**(b) $`m \ne 0`$.** Since $`k \lt m`$ implies $`k \lt m + 1`$ and
$`k + 1 \lt m`$ implies $`k + 1 \lt m + 1`$, the hypotheses (F1), (Fne), (Fj) hold with $`n := m`$ as well.
Hence the induction hypothesis $`\Phi(m)`$ is available and gives

```math
\mathrm{steps}_1(\mathrm{cat}_m F)
```

Moreover, $`m \ne 0`$ gives $`0 \lt m`$, so

```math
\mathrm{cat}_m F \ne (),
\qquad
\mathrm{head}(\mathrm{cat}_m F) = \mathrm{head}\,F(0),
\qquad
\mathrm{last}_{(0,0)}(\mathrm{cat}_m F) = \mathrm{last}_{(0,0)} F(m-1)
```

are obtained as well.

Next we show the estimate at the junction

```math
\bigl(\mathrm{head}\,F(m)\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)}(\mathrm{cat}_m F)\bigr)_1 + 1
```

By the third formula above, the right-hand side equals $`\bigl(\mathrm{last}_{(0,0)} F(m-1)\bigr)_1 + 1`$.
Since $`m \ne 0`$ gives $`(m-1) + 1 = m \lt m + 1`$, applying (Fj) with $`k := m - 1`$ gives

```math
\bigl(\mathrm{head}\,F(m)\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)} F(m-1)\bigr)_1 + 1
```

Applying (Fne) with $`k := m \lt m + 1`$ also gives $`F(m) \ne ()`$.

On this basis we prove the four conclusions.

**Step-1 condition.** By the decomposition above and [T.steps1_append](Seqlex.md#t-steps1_append),
in order to prove $`\mathrm{steps}_1(\mathrm{cat}_m F \mathbin{+\!\!+} F(m))`$ it suffices to prove the three statements
$`\mathrm{steps}_1(\mathrm{cat}_m F)`$, $`\mathrm{steps}_1(F(m))`$, and the disjunction
"$`\mathrm{cat}_m F = ()`$, or $`F(m) = ()`$, or
$`(\mathrm{head}\,F(m))_1 \le (\mathrm{last}_{(0,0)}(\mathrm{cat}_m F))_1 + 1`$".
The first was obtained above. The second follows by applying (F1) with $`k := m \lt m+1`$.
For the third, the estimate at the junction shown above is the third disjunct.

**Non-emptiness.** If $`\mathrm{cat}_m F \mathbin{+\!\!+} F(m) = ()`$, then, since a concatenation is empty only
when both parts are empty, $`\mathrm{cat}_m F = ()`$, which contradicts $`\mathrm{cat}_m F \ne ()`$ obtained above.

**Head.** Applying [T.headI_append_left](#t-headI_append_left) with $`A := \mathrm{cat}_m F \ne ()`$ gives

```math
\mathrm{head}(\mathrm{cat}_{m+1} F) = \mathrm{head}(\mathrm{cat}_m F) = \mathrm{head}\,F(0)
```

(the second equality is the formula obtained from the induction hypothesis).

**Last element.** Applying [T.getLastD_append_right](#t-getLastD_append_right) with $`B := F(m) \ne ()`$ gives

```math
\mathrm{last}_{(0,0)}(\mathrm{cat}_{m+1} F) = \mathrm{last}_{(0,0)} F(m)
```

Since $`(m+1) - 1 = m`$, this is the required formula. ∎

<a id="t-steps1_diag_range"></a>
## Theorem: the step-1 condition for a diagonal range (T.steps1_diag_range)

### Theorem

For all $`m, s \in \mathbb{N}`$,

```math
\mathrm{steps}_1\bigl(\,\bigl((s,s),\ (s+1,s+1),\ \dots,\ (s+m-1,s+m-1)\bigr)\,\bigr).
```

That is, the sequence obtained by mapping each element $`j`$ of the sequence of $`m`$ consecutive integers
starting at $`s`$ to $`(j,j)`$ satisfies the step-1 condition.

### Proof

Induction on the natural number $`m`$ (with $`s`$ left universally quantified). The induction predicate is

```math
\Phi(m) :\equiv \forall s \in \mathbb{N},\
  \mathrm{steps}_1\bigl(\,\bigl((s+i,\,s+i)\bigr)_{i=0}^{m-1}\,\bigr).
```

- **Base case** $`m = 0`$: the sequence is the empty sequence, and the claim is [T.steps1_nil](Seqlex.md#t-steps1_nil).

**Inductive step $`m + 1`$.** The induction hypothesis is $`\Phi(m)`$, that is,
$`\forall s,\ \mathrm{steps}_1\bigl((\,(s+i,s+i)\,)_{i=0}^{m-1}\bigr)`$.
Take $`s`$. Splitting off the head, the sequence of length $`m+1`$ can be written as

```math
\bigl((s+i,\,s+i)\bigr)_{i=0}^{m} = (s,s) :: \bigl((s+1+i,\,s+1+i)\bigr)_{i=0}^{m-1}
```

We distinguish further according to whether $`m`$ is $`0`$.

**Case $`m = 0`$.** The right-hand side is $`\bigl((s,s)\bigr)`$, a sequence of length 1, and the claim is
[T.steps1_single](Seqlex.md#t-steps1_single).

**Case $`m = m' + 1`$.** Splitting off the head once more,

```math
\bigl((s+1+i,\,s+1+i)\bigr)_{i=0}^{m-1}
  = (s+1,s+1) :: \bigl((s+2+i,\,s+2+i)\bigr)_{i=0}^{m'-1}
```

Hence the sequence to be treated is of the form $`(s,s) :: (s+1,s+1) :: \cdots`$, and by
[T.steps1_cons_cons](Seqlex.md#t-steps1_cons_cons) it suffices to show the following two statements.

The first is $`(s+1,s+1)_1 \le (s,s)_1 + 1`$, that is, $`s + 1 \le s + 1`$, which holds by
reflexivity of $`\le`$.

The second is $`\mathrm{steps}_1\bigl((s+1,s+1) :: ((s+2+i,s+2+i))_{i=0}^{m'-1}\bigr)`$, which is
nothing but $`\mathrm{steps}_1\bigl(((s+1+i,s+1+i))_{i=0}^{m-1}\bigr)`$, obtained by applying the
induction hypothesis $`\Phi(m)`$ with $`s := s + 1`$, rewritten by the head-splitting formula above. ∎

<a id="t-blockok_diagSeq"></a>
## Theorem: a diagonal sequence is a block (T.blockok_diagSeq)

### Theorem

For every $`v \in \mathbb{N}`$, $`\mathrm{blockok}(0, \Delta_0^v)`$ ([D.diagSeq](Pss.md#d-diagSeq)).

### Proof

We prove the three conjuncts of the definition of $`\mathrm{blockok}`$ (D.blockok) in turn.

**First (the head has depth $`0`$).** Assume $`\Delta_0^v \ne ()`$.
Since $`0 \le v`$, [T.diagSeq_cons](Cnf.md#t-diagSeq_cons) gives
$`\Delta_0^v = (0,0) :: \Delta_1^v`$. Hence
$`\mathrm{head}\,\Delta_0^v = (0,0)`$, whose first entry is $`0`$.

**Second (the values in row $`0`$ are at least $`0`$).** For every $`p \in \Delta_0^v`$,
$`0 \le p_1`$ holds because $`0`$ is the least natural number.

**Third (step-1 condition).** By the definition of $`\Delta_0^v`$ (D.diagSeq), $`\Delta_0^v`$ is the
sequence obtained by mapping each element $`j`$ of the sequence of $`v + 1 - 0`$ consecutive integers starting at $`0`$ to $`(j,j)`$.
It suffices to apply [T.steps1_diag_range](#t-steps1_diag_range) with $`m := v + 1`$ and $`s := 0`$. ∎

<a id="t-blockok_oper"></a>
## Theorem: expansion preserves blocks (T.blockok_oper)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$.
If $`\mathrm{blockok}(0, M)`$ and $`1 \le n`$, then $`\mathrm{blockok}(0, M[n])`$ ([D.oper](Pss.md#d-oper)).

### Proof

Below we write $`j_1 := \lvert M\rvert - 1`$ and $`i_1 := \mathrm{idx}_1(M, j_1)`$ ([D.idx1](Pss.md#d-idx1)).
We distinguish cases according to whether $`j_1 = 0`$.

**(A) $`j_1 = 0`$.**
By [T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short), $`M[n] = M`$, and
the conclusion is the hypothesis $`\mathrm{blockok}(0, M)`$ itself.

**(B) $`j_1 \ne 0`$.**
From $`j_1 = \lvert M\rvert - 1 \ne 0`$ we get $`1 \lt \lvert M\rvert`$, in particular $`M \ne ()`$.
Moreover, in the case distinction of the definition of $`\mathrm{Pred}\,M`$ ([D.Pred](Pss.md#d-Pred)) the condition $`\lvert M\rvert \le 1`$ is false, so

```math
\mathrm{Pred}\,M = \mathrm{dropLast}\,M
```

We distinguish cases according to whether $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ holds.

**(B-1) $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$.**
By [T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero),
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$.
It suffices to apply [T.blockok_dropLast](Seqlex.md#t-blockok_dropLast) to $`\mathrm{blockok}(0,M)`$.

**(B-2) $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ ([D.hasParent](Pss.md#d-hasParent)).**
By [T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent),
$`M[n] = \mathrm{Pred}\,M = \mathrm{dropLast}\,M`$.
It suffices to apply [T.blockok_dropLast](Seqlex.md#t-blockok_dropLast).

**(B-3) $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and $`\mathrm{hasParent}(M, i_1, j_1)`$.**
By [T.parent_nextR](Decrease.md#t-parent_nextR), putting $`j_0 := \mathrm{par}^M_{i_1}(j_1)`$ ([D.parent](Pss.md#d-parent)), we have
$`j_0 \to^M_{i_1} j_1`$ ([D.nextR](Pss.md#d-nextR)). By [T.nextR_index_lt](Decrease.md#t-nextR_index_lt),
$`j_0 \lt j_1`$. Put moreover

```math
d_0 := \begin{cases} M_{0,j_1} - M_{0,j_0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
```

**Steps in row $`0`$ (formula E1).** The third conjunct of $`\mathrm{blockok}(0,M)`$ is
$`\mathrm{steps}_1(M)`$. By [T.steps1_iff](Seqlex.md#t-steps1_iff),

```math
\forall j,\ j + 1 \lt \lvert M\rvert \ \to\ M_{0,j+1} \le M_{0,j} + 1 .
```

(That the first entry of $`M\langle j\rangle`$ is $`M_{0,j}`$ holds by the definition of $`M_{i,j}`$ (D.entry).)

**Estimate at the junction (formula E2).**

```math
M_{0,j_0} + d_0 \le M_{0,j_1 - 1} + 1 .
```

We prove this. First, $`j_1 \ne 0`$ gives $`(j_1 - 1) + 1 = j_1 \lt \lvert M\rvert`$, so
applying formula E1 with $`j := j_1 - 1`$ gives

```math
M_{0,j_1} \le M_{0,j_1 - 1} + 1
```

We distinguish cases according to whether $`i_1`$ is $`0`$.

**Case $`0 \lt i_1`$.** By the second clause of the definition of $`\to^M_{i}`$ (D.nextR),
$`j_0 \to^M_{i_1} j_1`$ is $`j_0 \to^M_1 j_1`$ ([D.nextrel1](Pss.md#d-nextrel1)).
The fifth condition in the definition of $`\to^M_1`$ (D.nextrel1) is $`j_0 \le^M_0 j_1`$ ([D.le0](Pss.md#d-le0)), and
[T.le0_entry0_mono](Term.md#t-le0_entry0_mono) gives $`M_{0,j_0} \le M_{0,j_1}`$.
By the first clause of the definition of $`d_0`$ we have $`d_0 = M_{0,j_1} - M_{0,j_0}`$, and truncated subtraction satisfies,
when $`M_{0,j_0} \le M_{0,j_1}`$,

```math
M_{0,j_0} + d_0 = M_{0,j_0} + (M_{0,j_1} - M_{0,j_0}) = M_{0,j_1}
```

Combining this with the formula above gives $`M_{0,j_0} + d_0 \le M_{0,j_1-1} + 1`$.

**Case $`i_1 = 0`$.** By the first clause of the definition of $`\to^M_{i}`$ (D.nextR),
$`j_0 \to^M_0 j_1`$ ([D.nextrel0](Pss.md#d-nextrel0)). By [T.nextrel0_entry0_less](Term.md#t-nextrel0_entry0_less),
$`M_{0,j_0} \lt M_{0,j_1}`$. By the second clause of the definition of $`d_0`$ we have $`d_0 = 0`$, hence

```math
M_{0,j_0} + d_0 = M_{0,j_0} \lt M_{0,j_1} \le M_{0,j_1-1} + 1
```

and in particular $`M_{0,j_0} + d_0 \le M_{0,j_1-1} + 1`$.

**Form of the expansion.** By [T.oper_bad_unfold](Decrease.md#t-oper_bad_unfold),

```math
M[n] = \mathrm{take}_{j_0} M \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
\qquad
B_k = \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j})\,\bigr)_{j=j_0}^{j_1-1}
```

Here $`\mathrm{take}_{j_0} M := (M_0, \dots, M_{j_0-1})`$.
Putting $`F(k) := B_k`$, the right-hand side is $`\mathrm{take}_{j_0} M \mathbin{+\!\!+} \mathrm{cat}_n F`$.

**Properties of each block.** From $`j_0 \lt j_1`$ we get $`1 \le j_1 - j_0`$, so the sequence of
indices over which $`B_k`$ ranges can be split at the head as

```math
(j_0,\ j_0+1,\ \dots,\ j_1-1) = j_0 :: (j_0+1,\ \dots,\ j_1-1)
```

From this the following five facts follow.

**(F-ne)** $`B_k \ne ()`$. By the splitting above, $`B_k`$ has at least one element.

**(F-hd)** $`\mathrm{head}\,B_k = (M_{0,j_0} + k\,d_0,\ M_{1,j_0})`$. It is the image of the head $`j_0`$ in the splitting above.

**(F-len)** $`\lvert B_k\rvert = j_1 - j_0`$, because that is the length of the sequence of indices.

**(F-get)** If $`j \lt j_1 - j_0`$ then
$`B_k\langle j\rangle = (M_{0,j_0+j} + k\,d_0,\ M_{1,j_0+j})`$.
The element of the sequence of indices at index $`j`$ is $`j_0 + j`$, and this is its image.

**(F-last)** $`\mathrm{last}_{(0,0)} B_k = (M_{0,j_1-1} + k\,d_0,\ M_{1,j_1-1})`$.
By [T.getLastD_eq_getD](#t-getLastD_eq_getD) and (F-len) we have
$`\mathrm{last}_{(0,0)} B_k = B_k\langle j_1 - j_0 - 1\rangle`$, and
applying (F-get) with $`j := j_1 - j_0 - 1`$ (which is less than $`j_1 - j_0`$) gives this value,
since $`j_0 + (j_1 - j_0 - 1) = j_1 - 1`$.

**(F-steps) the step-1 condition for each block.** We show $`\mathrm{steps}_1(B_k)`$.
By [T.steps1_iff](Seqlex.md#t-steps1_iff) it suffices to show
$`\bigl(B_k\langle j+1\rangle\bigr)_1 \le \bigl(B_k\langle j\rangle\bigr)_1 + 1`$ for every $`j`$ with $`j + 1 \lt \lvert B_k\rvert = j_1 - j_0`$.
Applying (F-get) to $`j`$ and $`j+1`$, the formula to be shown is

```math
M_{0,j_0+j+1} + k\,d_0 \le M_{0,j_0+j} + k\,d_0 + 1
```

From $`j + 1 \lt j_1 - j_0`$ we get $`j_0 + j + 1 \lt j_1 \lt \lvert M\rvert`$, so
applying formula E1 with $`j := j_0 + j`$ gives $`M_{0,j_0+j+1} \le M_{0,j_0+j} + 1`$.
Adding $`k\,d_0`$ to both sides yields the formula above.

**(F-junc) junction between blocks.** For every $`k`$ with $`k + 1 \lt n`$ we show

```math
\bigl(\mathrm{head}\,B_{k+1}\bigr)_1 \le \bigl(\mathrm{last}_{(0,0)} B_k\bigr)_1 + 1
```

By (F-hd) and (F-last), the formula to be shown is

```math
M_{0,j_0} + (k+1)\,d_0 \le M_{0,j_1-1} + k\,d_0 + 1
```

Since $`(k+1)\,d_0 = k\,d_0 + d_0`$, this is obtained by adding $`k\,d_0`$ to both sides of
$`M_{0,j_0} + d_0 \le M_{0,j_1-1} + 1`$, and it holds by formula E2.

**The concatenated sequence of blocks.** Apply [T.steps1_flatMap](#t-steps1_flatMap) with
$`F(k) = B_k`$ and this $`n`$. The hypothesis (F1) is (F-steps), (Fne) is (F-ne),
and (Fj) is (F-junc). As the conclusion we obtain $`\mathrm{steps}_1(\mathrm{cat}_n F)`$.
Moreover, $`1 \le n`$ gives $`0 \lt n`$, so

```math
\mathrm{cat}_n F \ne (),
\qquad
\mathrm{head}(\mathrm{cat}_n F) = \mathrm{head}\,B_0
```

are obtained as well. Applying (F-hd) with $`k := 0`$ gives $`\mathrm{head}\,B_0 = (M_{0,j_0} + 0\cdot d_0, M_{1,j_0})`$,
and $`0 \cdot d_0 = 0`$, so

```math
\mathrm{head}(\mathrm{cat}_n F) = (M_{0,j_0},\ M_{1,j_0}) .
```

**The step-1 condition for the prefix.** We show $`\mathrm{steps}_1(\mathrm{take}_{j_0} M)`$.
By [T.steps1_iff](Seqlex.md#t-steps1_iff) it suffices to show
$`\bigl((\mathrm{take}_{j_0} M)\langle j+1\rangle\bigr)_1 \le \bigl((\mathrm{take}_{j_0} M)\langle j\rangle\bigr)_1 + 1`$
for every $`j`$ with $`j + 1 \lt \lvert \mathrm{take}_{j_0} M\rvert`$.
We have $`\lvert \mathrm{take}_{j_0} M\rvert = \min(j_0, \lvert M\rvert)`$, which is
at most $`\lvert M\rvert`$, so $`j + 1 \lt \lvert M\rvert`$.
Moreover both $`j`$ and $`j+1`$ are less than $`\lvert \mathrm{take}_{j_0} M\rvert`$, so the elements of the
prefix at indices $`j`$ and $`j+1`$ are equal to the elements of $`M`$ at indices $`j`$ and $`j+1`$ respectively, that is,

```math
(\mathrm{take}_{j_0} M)\langle j\rangle = M\langle j\rangle,
\qquad
(\mathrm{take}_{j_0} M)\langle j+1\rangle = M\langle j+1\rangle
```

Hence the formula to be shown is $`M_{0,j+1} \le M_{0,j} + 1`$, which holds by formula E1.

**Junction between the prefix and the concatenated blocks.** We show that one of the following three disjuncts holds.

```math
\mathrm{take}_{j_0} M = ()
\ \vee\ \mathrm{cat}_n F = ()
\ \vee\ \bigl(\mathrm{head}(\mathrm{cat}_n F)\bigr)_1
        \le \bigl(\mathrm{last}_{(0,0)}(\mathrm{take}_{j_0} M)\bigr)_1 + 1 .
```

We distinguish cases according to whether $`j_0`$ is $`0`$.

**Case $`j_0 = 0`$.** We have $`\mathrm{take}_0 M = ()`$, so the first disjunct holds.

**Case $`j_0 \ne 0`$.** From $`j_0 \lt j_1 \lt \lvert M\rvert`$ we get $`j_0 \le \lvert M\rvert`$, so
$`\lvert \mathrm{take}_{j_0} M\rvert = \min(j_0, \lvert M\rvert) = j_0`$.
By [T.getLastD_eq_getD](#t-getLastD_eq_getD),
$`\mathrm{last}_{(0,0)}(\mathrm{take}_{j_0} M) = (\mathrm{take}_{j_0} M)\langle j_0 - 1\rangle`$, and
since $`j_0 - 1 \lt j_0 \le \lvert M\rvert`$ this equals $`M\langle j_0 - 1\rangle`$.
Moreover $`j_0 \ne 0`$ gives $`(j_0 - 1) + 1 = j_0 \lt \lvert M\rvert`$, so applying formula E1 with
$`j := j_0 - 1`$ gives

```math
M_{0,j_0} \le M_{0,j_0-1} + 1
```

Together with $`\mathrm{head}(\mathrm{cat}_n F) = (M_{0,j_0}, M_{1,j_0})`$ obtained above,
this is the third disjunct.

**Conclusion.** We prove the three conjuncts of the definition of $`\mathrm{blockok}`$ (D.blockok) for
$`M[n] = \mathrm{take}_{j_0} M \mathbin{+\!\!+} \mathrm{cat}_n F`$ in turn.

**First (the head has depth $`0`$).** Assume $`M[n] \ne ()`$. We distinguish cases according to whether $`j_0`$ is $`0`$.

- $`j_0 = 0`$. Since $`\mathrm{take}_0 M = ()`$ we have
  $`M[n] = \mathrm{cat}_n F`$, and as obtained above
  $`\mathrm{head}(M[n]) = (M_{0,j_0}, M_{1,j_0}) = (M_{0,0}, M_{1,0})`$.
  Its first entry is $`M_{0,0}`$. Since $`M \ne ()`$ we may write $`M = x :: xs`$, and
  $`\mathrm{head}\,M = x`$ and $`M\langle 0\rangle = x`$, so $`M_{0,0} = x_1`$.
  Applying the first conjunct of $`\mathrm{blockok}(0,M)`$ to $`M \ne ()`$ gives $`x_1 = 0`$.

- $`j_0 \ne 0`$. We have $`\lvert \mathrm{take}_{j_0} M\rvert = \min(j_0, \lvert M\rvert)`$, and since
  $`0 \lt j_0`$ and $`0 \lt \lvert M\rvert`$ this value is greater than $`0`$, so
  $`\mathrm{take}_{j_0} M \ne ()`$.
  By [T.headI_append_left](#t-headI_append_left),
  $`\mathrm{head}(M[n]) = \mathrm{head}(\mathrm{take}_{j_0} M)`$.
  Writing $`M = x :: xs`$ and putting $`j_0 = m + 1`$, we have
  $`\mathrm{take}_{m+1}(x :: xs) = x :: \mathrm{take}_m\,xs`$, so
  $`\mathrm{head}(\mathrm{take}_{j_0} M) = x = \mathrm{head}\,M`$.
  Applying the first conjunct of $`\mathrm{blockok}(0,M)`$ to $`M \ne ()`$ gives
  $`(\mathrm{head}\,M)_1 = 0`$.

**Second (the values in row $`0`$ are at least $`0`$).** For every $`p \in M[n]`$, $`0 \le p_1`$ holds because
$`0`$ is the least natural number.

**Third (step-1 condition).** By [T.steps1_append](Seqlex.md#t-steps1_append) it suffices to prove the three statements
$`\mathrm{steps}_1(\mathrm{take}_{j_0} M)`$, $`\mathrm{steps}_1(\mathrm{cat}_n F)`$, and
the three-fold disjunction shown above, all of which have already been proved. ∎

<a id="t-blockok_ST_PS"></a>
## Theorem: a standard form is a block (T.blockok_ST_PS)

### Theorem

If $`M \in \mathrm{ST\_PS}`$ ([D.ST_PS](Pss.md#d-ST_PS)) then $`\mathrm{blockok}(0, M)`$.

### Proof

Induction on the derivation of $`\mathrm{ST\_PS}`$. The induction predicate is

```math
\Phi(M) :\equiv \mathrm{blockok}(0, M).
```

- **Base case** (rule (diag), $`M = \Delta_0^v`$): [T.blockok_diagSeq](#t-blockok_diagSeq) is
  exactly $`\Phi(\Delta_0^v)`$.

- **Inductive step** (rule (oper), from $`M \in \mathrm{ST\_PS}`$ and $`1 \le n`$ to $`M[n]`$):
  the induction hypothesis is $`\Phi(M)`$, that is, $`\mathrm{blockok}(0, M)`$.
  Applying [T.blockok_oper](#t-blockok_oper) to this and $`1 \le n`$ gives
  $`\mathrm{blockok}(0, M[n])`$, that is, $`\Phi(M[n])`$. ∎

<a id="t-olt_ST_iff_seqlex"></a>
## Theorem: order isomorphism on standard forms (T.olt_ST_iff_seqlex)

### Theorem

If $`M, N \in \mathrm{ST\_PS}`$ and $`M \ne N`$, then

```math
\mathrm{tr}\,M \prec \mathrm{tr}\,N \iff M \prec_{\mathrm{lex}} N .
```

### Proof

Applying [T.blockok_ST_PS](#t-blockok_ST_PS) to $`M`$ and $`N`$ gives
$`\mathrm{blockok}(0, M)`$ and $`\mathrm{blockok}(0, N)`$.
It suffices to apply [T.olt_iff_seqlex](#t-olt_iff_seqlex) with $`d := 0`$ to these and $`M \ne N`$. ∎
