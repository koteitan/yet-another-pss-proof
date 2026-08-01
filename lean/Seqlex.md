[← README](README.md) | [English](Seqlex.md) | [Japanese](Seqlex-ja.md) | Seqlex **1** [2](Seqlex-2.md)

<a id="d-pairlt"></a>
## Definition: lexicographic order on pairs (D.pairlt)

For $`p, q \in \mathbb{N}\times\mathbb{N}`$ put

```math
p \prec_{\mathrm{p}} q :\iff p_1 \lt q_1 \ \vee\ \bigl(p_1 = q_1 \wedge p_2 \lt q_2\bigr).
```

Here $`p = (p_1, p_2)`$ and $`q = (q_1, q_2)`$. Thus $`\prec_{\mathrm{p}}`$ is the lexicographic
order that compares pairs by the first entry and then by the second entry.

<a id="d-seqlex"></a>
## Definition: lexicographic order on sequences (D.seqlex)

For $`M, N \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) the relation
$`M \prec_{\mathrm{lex}} N`$ is defined by case distinction on the constructors of both arguments.
Below, $`()`$ is the empty sequence and $`p :: M`$ is the sequence obtained by prepending the
pair $`p`$ to the sequence $`M`$.

```math
\begin{aligned}
() &\prec_{\mathrm{lex}} N &&:\iff N \ne (), \cr
(p :: M) &\prec_{\mathrm{lex}} () &&:\iff \bot, \cr
(p :: M) &\prec_{\mathrm{lex}} (q :: N) &&:\iff
  p \prec_{\mathrm{p}} q \ \vee\ \bigl(p = q \wedge M \prec_{\mathrm{lex}} N\bigr).
\end{aligned}
```

The recursive call on the right-hand side of the third clause is $`M \prec_{\mathrm{lex}} N`$, and
$`M`$, $`N`$ are shorter by $`1`$ than $`p :: M`$, $`q :: N`$ respectively, so this definition
is well defined.

Thus $`\prec_{\mathrm{lex}}`$ is the lexicographic order that compares sequences one column at a
time from the front by $`\prec_{\mathrm{p}}`$. The first clause says that the empty sequence is
smaller than every non-empty sequence, and the second clause says that no sequence is smaller
than the empty sequence.

<a id="t-seqlex_nil_iff"></a>
## Theorem: comparison with the empty sequence on the left (T.seqlex_nil_iff)

### Theorem

For $`N \in \mathrm{PairSeq}`$ we have $`() \prec_{\mathrm{lex}} N \iff N \ne ()`$.

### Proof

By the first clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex), the left-hand side
and the right-hand side are the same proposition by definition. ∎

<a id="t-not_seqlex_nil"></a>
## Theorem: comparison with the empty sequence on the right (T.not_seqlex_nil)

### Theorem

For $`p \in \mathbb{N}\times\mathbb{N}`$ and $`M \in \mathrm{PairSeq}`$ we have
$`\neg\bigl((p :: M) \prec_{\mathrm{lex}} ()\bigr)`$.

### Proof

By the second clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex),
$`(p :: M) \prec_{\mathrm{lex}} ()`$ is the same proposition as $`\bot`$ by definition.
Hence that hypothesis yields $`\bot`$. ∎

<a id="t-seqlex_cons_cons"></a>
## Theorem: comparison of two sequences with a head prepended (T.seqlex_cons_cons)

### Theorem

For $`p, q \in \mathbb{N}\times\mathbb{N}`$ and $`M, N \in \mathrm{PairSeq}`$,

```math
(p :: M) \prec_{\mathrm{lex}} (q :: N) \iff
  p \prec_{\mathrm{p}} q \ \vee\ \bigl(p = q \wedge M \prec_{\mathrm{lex}} N\bigr).
```

### Proof

This is exactly the third clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex), and
both sides are the same proposition by definition. ∎

<a id="t-seqlex_append_cancel"></a>
## Theorem: cancellation of a common prefix (T.seqlex_append_cancel)

### Theorem

For $`A, u, v \in \mathrm{PairSeq}`$,

```math
(A \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A \mathbin{+\!\!+} v) \iff u \prec_{\mathrm{lex}} v .
```

### Proof

By induction on the list structure of $`A`$ (with $`u`$, $`v`$ fixed). Show

```math
\Phi(A) :\equiv \Bigl((A \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A \mathbin{+\!\!+} v)
  \iff u \prec_{\mathrm{lex}} v\Bigr)
```

for every $`A`$.

- **Base case** $`A = ()`$: since $`() \mathbin{+\!\!+} u = u`$ and $`() \mathbin{+\!\!+} v = v`$,
  the two sides are the same proposition.

**Inductive step** $`A = a :: A'`$: assume $`\Phi(A')`$, that is,

```math
(A' \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A' \mathbin{+\!\!+} v) \iff u \prec_{\mathrm{lex}} v
```

Since $`(a :: A') \mathbin{+\!\!+} u = a :: (A' \mathbin{+\!\!+} u)`$ and
$`(a :: A') \mathbin{+\!\!+} v = a :: (A' \mathbin{+\!\!+} v)`$, by
[T.seqlex_cons_cons](#t-seqlex_cons_cons) the left-hand side to be proved is equivalent to

```math
a \prec_{\mathrm{p}} a \ \vee\ \bigl(a = a \wedge
  (A' \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A' \mathbin{+\!\!+} v)\bigr)
```

Here, by the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt), $`a \prec_{\mathrm{p}} a`$ means
$`a_1 \lt a_1`$ or $`a_1 = a_1 \wedge a_2 \lt a_2`$, and both are false by irreflexivity of
$`\lt`$ on $`\mathbb{N}`$; hence $`\neg(a \prec_{\mathrm{p}} a)`$. We prove both directions.

- ($`\to`$) Assume the left-hand side. The first disjunct contradicts
  $`\neg(a \prec_{\mathrm{p}} a)`$, so the second disjunct holds and we obtain
  $`(A' \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A' \mathbin{+\!\!+} v)`$.
  The $`\to`$ direction of the induction hypothesis $`\Phi(A')`$ gives $`u \prec_{\mathrm{lex}} v`$.

- ($`\leftarrow`$) Assume $`u \prec_{\mathrm{lex}} v`$. The $`\leftarrow`$ direction of the
  induction hypothesis $`\Phi(A')`$ gives
  $`(A' \mathbin{+\!\!+} u) \prec_{\mathrm{lex}} (A' \mathbin{+\!\!+} v)`$.
  Together with $`a = a`$, the second disjunct holds.

Hence $`\Phi(a :: A')`$. ∎

<a id="t-seqlex_prefix"></a>
## Theorem: a proper prefix is smaller (T.seqlex_prefix)

### Theorem

If $`v \ne ()`$ then, for every $`u \in \mathrm{PairSeq}`$,
$`u \prec_{\mathrm{lex}} (u \mathbin{+\!\!+} v)`$.

### Proof

By induction on the list structure of $`u`$ (with $`v`$ and the hypothesis $`v \ne ()`$ fixed).
Show

```math
\Phi(u) :\equiv u \prec_{\mathrm{lex}} (u \mathbin{+\!\!+} v)
```

for every $`u`$.

- **Base case** $`u = ()`$: we have $`() \mathbin{+\!\!+} v = v`$, and by
  [T.seqlex_nil_iff](#t-seqlex_nil_iff) the statement $`() \prec_{\mathrm{lex}} v`$ is equivalent
  to $`v \ne ()`$, which is the hypothesis.

- **Inductive step** $`u = a :: u'`$: assume $`\Phi(u')`$, that is,
  $`u' \prec_{\mathrm{lex}} (u' \mathbin{+\!\!+} v)`$.
  Since $`(a :: u') \mathbin{+\!\!+} v = a :: (u' \mathbin{+\!\!+} v)`$, the second disjunct
  $`a = a \wedge u' \prec_{\mathrm{lex}} (u' \mathbin{+\!\!+} v)`$ on the right-hand side of
  [T.seqlex_cons_cons](#t-seqlex_cons_cons) holds by reflexivity of $`=`$ and the induction
  hypothesis. Hence $`\Phi(a :: u')`$. ∎

<a id="d-steps1"></a>
## Definition: adjacent row 0 steps are at most 1 (D.steps1)

For $`B \in \mathrm{PairSeq}`$ the predicate $`\mathrm{steps}_1(B)`$ is defined by case
distinction on whether the first two elements are present.

```math
\begin{aligned}
\mathrm{steps}_1(()) &:\iff \top, \cr
\mathrm{steps}_1((p)) &:\iff \top, \cr
\mathrm{steps}_1(p :: q :: r) &:\iff q_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(q :: r).
\end{aligned}
```

The argument $`q :: r`$ of the recursive call on the right-hand side of the third clause is
shorter by $`1`$ than $`p :: q :: r`$, so this definition is well defined.

Thus $`\mathrm{steps}_1(B)`$ says that, for any two adjacent columns, the row $`0`$ value of the
right column is at most the row $`0`$ value of the left column plus $`1`$.

<a id="t-steps1_nil"></a>
## Theorem: adjacent steps of the empty sequence (T.steps1_nil)

### Theorem

$`\mathrm{steps}_1(())`$.

### Proof

By the first clause of the definition of $`\mathrm{steps}_1`$ (D.steps1), $`\mathrm{steps}_1(())`$
is the same proposition as $`\top`$ by definition, and $`\top`$ holds. ∎

<a id="t-steps1_single"></a>
## Theorem: adjacent steps of a sequence with a single column (T.steps1_single)

### Theorem

For every $`p \in \mathbb{N}\times\mathbb{N}`$ we have $`\mathrm{steps}_1((p))`$.

### Proof

By the second clause of the definition of $`\mathrm{steps}_1`$ (D.steps1),
$`\mathrm{steps}_1((p))`$ is the same proposition as $`\top`$ by definition, and $`\top`$ holds. ∎

<a id="t-steps1_cons_cons"></a>
## Theorem: decomposition at the first two elements (T.steps1_cons_cons)

### Theorem

For $`p, q \in \mathbb{N}\times\mathbb{N}`$ and $`r \in \mathrm{PairSeq}`$,

```math
\mathrm{steps}_1(p :: q :: r) \iff q_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(q :: r).
```

### Proof

This is exactly the third clause of the definition of $`\mathrm{steps}_1`$ (D.steps1), and both
sides are the same proposition by definition. ∎

<a id="d-blockok"></a>
## Definition: block of depth $`d`$ (D.blockok)

Write $`\mathrm{head}\,L`$ for the first element of a finite sequence $`L`$ of type $`\alpha`$;
that is, $`\mathrm{head}\,L := L_0`$ when $`L \ne ()`$, and the default value fixed for the type
$`\alpha`$ when $`L = ()`$ (for $`\alpha = \mathbb{N}\times\mathbb{N}`$ the default value is
$`(0,0)`$). For $`B \in \mathrm{PairSeq}`$ and $`d \in \mathbb{N}`$ put

```math
\mathrm{blockok}(d, B) :\iff
  \bigl(B \ne () \to (\mathrm{head}\,B)_1 = d\bigr)
  \ \wedge\ \bigl(\forall p \in B,\ d \le p_1\bigr)
  \ \wedge\ \mathrm{steps}_1(B).
```

When $`\mathrm{blockok}(d, B)`$ holds we call $`B`$ a **block of depth $`d`$**.
The first conjunct says that if $`B`$ is non-empty then the row $`0`$ value of its head is
exactly $`d`$, the second conjunct says that the row $`0`$ value of every column of $`B`$ is at
least $`d`$, and the third conjunct is the content of the definition of $`\mathrm{steps}_1`$
(D.steps1).

<a id="t-steps1_iff"></a>
## Theorem: characterization of the adjacent steps by indices (T.steps1_iff)

### Theorem

For $`B \in \mathrm{PairSeq}`$ and $`j \in \mathbb{N}`$, let
$`B\langle j\rangle`$ ([D.entry](Pss.md#d-entry)) be the $`j`$-th element of $`B`$
(equal to $`(0,0)`$ when $`j \ge \lvert B\rvert`$). Then

```math
\mathrm{steps}_1(B) \iff
  \forall j,\ \Bigl(j + 1 \lt \lvert B\rvert \to
    (B\langle j+1\rangle)_1 \le (B\langle j\rangle)_1 + 1\Bigr).
```

### Proof

By induction on the list structure of $`B`$. Show

```math
\Phi(B) :\equiv \Bigl(\mathrm{steps}_1(B) \iff
  \forall j,\ \bigl(j + 1 \lt \lvert B\rvert \to
    (B\langle j+1\rangle)_1 \le (B\langle j\rangle)_1 + 1\bigr)\Bigr)
```

for every $`B`$.

- **Base case** $`B = ()`$: the left-hand side holds by [T.steps1_nil](#t-steps1_nil).
  As for the right-hand side, $`\lvert B\rvert = 0`$, so no $`j`$ satisfies the antecedent
  $`j + 1 \lt 0`$ and it holds. Both sides hold, hence they are equivalent.

**Inductive step** $`B = p :: B'`$: assume $`\Phi(B')`$. We distinguish
cases on $`B'`$.

**(a) $`B' = ()`$.** The left-hand side $`\mathrm{steps}_1((p))`$ holds by
[T.steps1_single](#t-steps1_single). As for the right-hand side, $`\lvert B\rvert = 1`$, so no
$`j`$ satisfies the antecedent $`j + 1 \lt 1`$ and it holds. Both sides hold, hence they are
equivalent.

**(b) $`B' = q :: r`$.** In this case

```math
\lvert B\rvert = \lvert B'\rvert + 1,\qquad
B\langle 0\rangle = p,\qquad
B\langle j+1\rangle = B'\langle j\rangle \quad (\forall j),\qquad
B'\langle 0\rangle = q
```

The first equality holds because $`B = p :: B'`$. The second and fourth hold because the
$`0`$-th elements of $`B`$ and $`B'`$ are $`p`$ and $`q`$ respectively. The third holds because,
for $`j \lt \lvert B'\rvert`$, the element of $`B`$ at index $`j+1`$ is the element of $`B'`$ at
index $`j`$, while for $`j \ge \lvert B'\rvert`$ we have $`j + 1 \ge \lvert B\rvert`$ and both
sides equal $`(0,0)`$. By [T.steps1_cons_cons](#t-steps1_cons_cons) the left-hand side is equivalent to

```math
q_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(B')
```

and by the induction hypothesis $`\Phi(B')`$ this is in turn equivalent to

```math
q_1 \le p_1 + 1 \ \wedge\
  \forall j,\ \bigl(j + 1 \lt \lvert B'\rvert \to
    (B'\langle j+1\rangle)_1 \le (B'\langle j\rangle)_1 + 1\bigr)
```

We show that this is equivalent to the right-hand side, in both directions.

- ($`\to`$) Assume the above conjunction and take $`j`$ with $`j + 1 \lt \lvert B\rvert`$.
  For $`j = 0`$, what has to be shown is
  $`(B\langle 1\rangle)_1 \le (B\langle 0\rangle)_1 + 1`$, that is, $`q_1 \le p_1 + 1`$, which is
  the first conjunct. For $`j = j' + 1`$, what has to be shown is
  $`(B'\langle j'+1\rangle)_1 \le (B'\langle j'\rangle)_1 + 1`$. From
  $`j' + 2 \lt \lvert B\rvert = \lvert B'\rvert + 1`$ we get $`j' + 1 \lt \lvert B'\rvert`$, so it
  suffices to apply the second conjunct to $`j'`$.

- ($`\leftarrow`$) Assume the right-hand side. For the first conjunct, from
  $`\lvert B\rvert = \lvert B'\rvert + 1 \ge 2`$ we get $`0 + 1 \lt \lvert B\rvert`$, so applying
  the right-hand side with $`j := 0`$ gives
  $`(B\langle 1\rangle)_1 \le (B\langle 0\rangle)_1 + 1`$, that is, $`q_1 \le p_1 + 1`$.
  For the second conjunct, take $`j`$ with $`j + 1 \lt \lvert B'\rvert`$; then
  $`(j+1) + 1 \lt \lvert B'\rvert + 1 = \lvert B\rvert`$, so applying the right-hand side to
  $`j + 1`$ gives $`(B\langle j+2\rangle)_1 \le (B\langle j+1\rangle)_1 + 1`$, that is,
  $`(B'\langle j+1\rangle)_1 \le (B'\langle j\rangle)_1 + 1`$.

Hence $`\Phi(p :: B')`$. ∎

<a id="t-steps1_tail"></a>
## Theorem: adjacent steps of the tail (T.steps1_tail)

### Theorem

If $`\mathrm{steps}_1(p :: r)`$ then $`\mathrm{steps}_1(r)`$.

### Proof

We distinguish cases on the constructor of $`r`$.

- Case $`r = ()`$. By [T.steps1_nil](#t-steps1_nil).

- Case $`r = q :: r'`$. The hypothesis is $`\mathrm{steps}_1(p :: q :: r')`$, and the second
  conjunct on the right-hand side of [T.steps1_cons_cons](#t-steps1_cons_cons) is
  $`\mathrm{steps}_1(q :: r') = \mathrm{steps}_1(r)`$. ∎

<a id="t-steps1_append"></a>
## Theorem: adjacent steps of a concatenation (T.steps1_append)

### Theorem

For a finite sequence $`L`$ of type $`\alpha`$ and $`d \in \alpha`$ put

```math
\mathrm{last}_d\,L := \begin{cases} d & (L = ()) \cr L_{\lvert L\rvert - 1} & (L \ne ()) \end{cases}
```

(the subtraction is truncated subtraction of natural numbers). Then, for
$`A, B \in \mathrm{PairSeq}`$,

```math
\mathrm{steps}_1(A \mathbin{+\!\!+} B) \iff
  \mathrm{steps}_1(A) \ \wedge\ \mathrm{steps}_1(B) \ \wedge\
  \Bigl(A = () \ \vee\ B = () \ \vee\
    (\mathrm{head}\,B)_1 \le (\mathrm{last}_{(0,0)} A)_1 + 1\Bigr).
```

### Proof

By induction on the list structure of $`A`$ (with $`B`$ fixed). Show

```math
\begin{aligned}
\Phi(A) :\equiv \Bigl(
  &\mathrm{steps}_1(A \mathbin{+\!\!+} B) \iff
    \mathrm{steps}_1(A) \wedge \mathrm{steps}_1(B) \cr
  &\qquad \wedge \bigl(A = () \vee B = () \vee
    (\mathrm{head}\,B)_1 \le (\mathrm{last}_{(0,0)} A)_1 + 1\bigr)\Bigr)
\end{aligned}
```

for every $`A`$.

- **Base case** $`A = ()`$: since $`() \mathbin{+\!\!+} B = B`$, the left-hand side is
  $`\mathrm{steps}_1(B)`$. On the right-hand side the first conjunct holds by
  [T.steps1_nil](#t-steps1_nil) and the third conjunct holds by its first disjunct $`A = ()`$,
  so the right-hand side is also equivalent to $`\mathrm{steps}_1(B)`$.

**Inductive step** $`A = p :: A'`$: assume $`\Phi(A')`$. We distinguish
cases on $`A'`$.

**(a) $`A' = ()`$.** Then $`A = (p)`$ and $`A \mathbin{+\!\!+} B = p :: B`$, and
$`\mathrm{last}_{(0,0)} A = p`$, while $`A = ()`$ is false. We distinguish further cases on $`B`$.

**(a-1) $`B = ()`$.** The left-hand side is $`\mathrm{steps}_1((p))`$, which holds by
[T.steps1_single](#t-steps1_single). On the right-hand side the first conjunct holds by
[T.steps1_single](#t-steps1_single), the second conjunct by [T.steps1_nil](#t-steps1_nil), and
the third conjunct by its second disjunct $`B = ()`$. Both sides hold, hence they are equivalent.

**(a-2) $`B = q :: B'`$.** Here $`\mathrm{head}\,B = q`$. By
[T.steps1_cons_cons](#t-steps1_cons_cons) the left-hand side is equivalent to
$`q_1 \le p_1 + 1 \wedge \mathrm{steps}_1(B)`$.
On the right-hand side the first conjunct holds by [T.steps1_single](#t-steps1_single), and the
third conjunct is equivalent to its third disjunct $`q_1 \le p_1 + 1`$ because both the first
disjunct $`A = ()`$ and the second disjunct $`B = ()`$ are false. Hence the right-hand side is
also equivalent to $`q_1 \le p_1 + 1 \wedge \mathrm{steps}_1(B)`$, and the two sides are
equivalent.

**(b) $`A' = p' :: A''`$.** In this case

```math
A \mathbin{+\!\!+} B = p :: (A' \mathbin{+\!\!+} B),\qquad
A' \mathbin{+\!\!+} B = p' :: (A'' \mathbin{+\!\!+} B),\qquad
\mathrm{last}_{(0,0)} A = \mathrm{last}_{(0,0)} A'
```

(the third equality holds because $`A' \ne ()`$: the last element of $`A = p :: A'`$ is the last
element of $`A'`$). Moreover both $`A = ()`$ and $`A' = ()`$ are false. Applying
[T.steps1_cons_cons](#t-steps1_cons_cons) twice gives

```math
\mathrm{steps}_1(A \mathbin{+\!\!+} B) \iff
  p'_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(A' \mathbin{+\!\!+} B),
```
```math
\mathrm{steps}_1(A) \iff p'_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(A')
```

Consequently the right-hand side is equivalent to

```math
p'_1 \le p_1 + 1 \ \wedge\ \Bigl(\mathrm{steps}_1(A') \wedge \mathrm{steps}_1(B) \wedge
  \bigl(A' = () \vee B = () \vee
    (\mathrm{head}\,B)_1 \le (\mathrm{last}_{(0,0)} A')_1 + 1\bigr)\Bigr)
```

Indeed, since $`A = ()`$ and $`A' = ()`$ are both false, the lists of disjuncts in the third
conjunct agree, and the third disjuncts agree as well because
$`\mathrm{last}_{(0,0)} A = \mathrm{last}_{(0,0)} A'`$. Everything else is just a rearrangement of
the association of the conjunction. By the induction hypothesis $`\Phi(A')`$, the expression
inside the large parentheses is equivalent to $`\mathrm{steps}_1(A' \mathbin{+\!\!+} B)`$, so the
right-hand side is equivalent to

```math
p'_1 \le p_1 + 1 \ \wedge\ \mathrm{steps}_1(A' \mathbin{+\!\!+} B)
```

which by the first of the equivalences above is equivalent to the left-hand side. Hence
$`\Phi(p :: A')`$. ∎

<a id="t-steps1_dropLast"></a>
## Theorem: dropping the last element preserves the adjacent steps (T.steps1_dropLast)

### Theorem

If $`\mathrm{steps}_1(B)`$ then $`\mathrm{steps}_1(\mathrm{dropLast}\,B)`$.
Here $`\mathrm{dropLast}\,B`$ is the sequence obtained from $`B`$ by dropping its last element
($`()`$ when $`B = ()`$).

### Proof

We distinguish cases according to whether $`B = ()`$.

**(a) $`B = ()`$.** Then $`\mathrm{dropLast}\,() = ()`$, and the claim follows by
[T.steps1_nil](#t-steps1_nil).

**(b) $`B \ne ()`$.** Let $`\ell`$ be the last element of $`B`$; then

```math
B = \mathrm{dropLast}\,B \mathbin{+\!\!+} (\ell)
```

Rewriting the hypothesis $`\mathrm{steps}_1(B)`$ accordingly and applying the $`\to`$ direction of
[T.steps1_append](#t-steps1_append) with $`A := \mathrm{dropLast}\,B`$ and $`B := (\ell)`$, its
first conjunct is $`\mathrm{steps}_1(\mathrm{dropLast}\,B)`$. ∎

<a id="t-blockok_dropLast"></a>
## Theorem: dropping the last element preserves being a block (T.blockok_dropLast)

### Theorem

If $`\mathrm{blockok}(d, B)`$ then $`\mathrm{blockok}(d, \mathrm{dropLast}\,B)`$.

### Proof

We prove in turn the three conjuncts of the definition of $`\mathrm{blockok}`$ (D.blockok). From
the hypothesis we have $`B \ne () \to (\mathrm{head}\,B)_1 = d`$,
$`\forall p \in B,\ d \le p_1`$ and $`\mathrm{steps}_1(B)`$.

**Third conjunct.** Apply [T.steps1_dropLast](#t-steps1_dropLast) to $`\mathrm{steps}_1(B)`$.

**Second conjunct.** Let $`p \in \mathrm{dropLast}\,B`$. If $`B = ()`$ then
$`\mathrm{dropLast}\,B = ()`$ has no element, so $`B \ne ()`$; letting $`\ell`$ be its last
element we have $`B = \mathrm{dropLast}\,B \mathbin{+\!\!+} (\ell)`$. Hence $`p \in B`$, and the
hypothesis gives $`d \le p_1`$.

**First conjunct.** Assume $`\mathrm{dropLast}\,B \ne ()`$. If $`B = ()`$ then
$`\mathrm{dropLast}\,B = ()`$, contradicting this assumption; so $`B \ne ()`$ and we may write
$`B = x :: xs`$. Here $`xs \ne ()`$: indeed, if $`xs = ()`$ then $`B = (x)`$ and
$`\mathrm{dropLast}\,B = ()`$, contradicting the assumption. Since
$`\mathrm{dropLast}(x :: xs) = x :: \mathrm{dropLast}\,xs`$ when $`xs \ne ()`$, we have

```math
\mathrm{head}\,(\mathrm{dropLast}\,B) = x = \mathrm{head}\,B
```

and applying the first conjunct of the hypothesis to $`B \ne ()`$ gives
$`(\mathrm{head}\,B)_1 = d`$, that is, $`x_1 = d`$. ∎

<a id="t-blockok_arg"></a>
## Theorem: the maximal prefix whose row 0 values are greater than $`d`$ is a block (T.blockok_arg)

### Theorem

Let $`d, y \in \mathbb{N}`$ and $`r \in \mathrm{PairSeq}`$.
If $`\mathrm{blockok}\bigl(d, (d,y) :: r\bigr)`$ then
$`\mathrm{blockok}\bigl(d+1,\ \mathrm{tw}_d r\bigr)`$ ([D.translate](Term.md#d-translate)).

### Proof

From the hypothesis we have $`\forall p \in (d,y) :: r,\ d \le p_1`$ and
$`\mathrm{steps}_1\bigl((d,y) :: r\bigr)`$.
We prove in turn the three conjuncts of the definition of $`\mathrm{blockok}`$ (D.blockok).

**First conjunct.** Assume $`\mathrm{tw}_d r \ne ()`$. By the definition of $`\mathrm{tw}`$
(D.translate) we have $`\mathrm{tw}_d\,() = ()`$, so $`r \ne ()`$ and we may write
$`r = p' :: r'`$. By the definition of $`\mathrm{tw}`$ (D.translate), if $`\neg(d \lt p'_1)`$
then $`\mathrm{tw}_d(p' :: r') = ()`$, contradicting the assumption. Hence $`d \lt p'_1`$, and in
that case $`\mathrm{tw}_d(p' :: r') = p' :: \mathrm{tw}_d r'`$, so

```math
\mathrm{head}\,(\mathrm{tw}_d r) = p' .
```

On the other hand, applying [T.steps1_cons_cons](#t-steps1_cons_cons) to
$`\mathrm{steps}_1\bigl((d,y) :: p' :: r'\bigr)`$, its first conjunct is
$`p'_1 \le d + 1`$. Since $`d \lt p'_1`$ means $`d + 1 \le p'_1`$, antisymmetry of $`\le`$ gives
$`p'_1 = d + 1`$.

**Second conjunct.** Let $`q \in \mathrm{tw}_d r`$. By the definition of $`\mathrm{tw}`$
(D.translate), every element of $`\mathrm{tw}_d r`$ satisfies the predicate $`d \lt x_1`$, so
$`d \lt q_1`$, that is, $`d + 1 \le q_1`$.

**Third conjunct.** By the definitions of $`\mathrm{tw}`$ and $`\mathrm{dw}`$ (D.translate) we
have $`\mathrm{tw}_d r \mathbin{+\!\!+} \mathrm{dw}_d r = r`$.
Applying [T.steps1_tail](#t-steps1_tail) to $`\mathrm{steps}_1\bigl((d,y) :: r\bigr)`$ gives
$`\mathrm{steps}_1(r)`$, hence
$`\mathrm{steps}_1\bigl(\mathrm{tw}_d r \mathbin{+\!\!+} \mathrm{dw}_d r\bigr)`$ holds.
Applying the $`\to`$ direction of [T.steps1_append](#t-steps1_append), its first conjunct is
$`\mathrm{steps}_1(\mathrm{tw}_d r)`$. ∎

<a id="t-blockok_tail"></a>
## Theorem: the remainder after removing that prefix is also a block (T.blockok_tail)

### Theorem

Let $`d, y \in \mathbb{N}`$ and $`r \in \mathrm{PairSeq}`$.
If $`\mathrm{blockok}\bigl(d, (d,y) :: r\bigr)`$ then
$`\mathrm{blockok}\bigl(d,\ \mathrm{dw}_d r\bigr)`$.

### Proof

From the hypothesis we have $`\forall p \in (d,y) :: r,\ d \le p_1`$ and
$`\mathrm{steps}_1\bigl((d,y) :: r\bigr)`$.
We prove in turn the three conjuncts of the definition of $`\mathrm{blockok}`$ (D.blockok).

**First conjunct.** Assume $`\mathrm{dw}_d r \ne ()`$ and let $`a`$ be its first element.
By the definition of $`\mathrm{dw}`$ (D.translate), if $`\mathrm{dw}_d r`$ is non-empty then its
first element violates the predicate $`d \lt x_1`$, so $`\neg(d \lt a_1)`$, that is,
$`a_1 \le d`$. Moreover $`\mathrm{dw}_d r`$ is a sublist of $`r`$, so $`a \in r`$ and hence
$`a \in (d,y) :: r`$. The second conjunct of the hypothesis gives $`d \le a_1`$.
By antisymmetry of $`\le`$ we obtain $`a_1 = d`$, that is,
$`(\mathrm{head}\,(\mathrm{dw}_d r))_1 = d`$.

**Second conjunct.** Let $`q \in \mathrm{dw}_d r`$. Since $`\mathrm{dw}_d r`$ is a sublist of
$`r`$, we have $`q \in r`$ and therefore $`q \in (d,y) :: r`$, so the hypothesis gives
$`d \le q_1`$.

**Third conjunct.** By the definitions of $`\mathrm{tw}`$ and $`\mathrm{dw}`$ (D.translate) we
have $`\mathrm{tw}_d r \mathbin{+\!\!+} \mathrm{dw}_d r = r`$.
Applying [T.steps1_tail](#t-steps1_tail) to $`\mathrm{steps}_1\bigl((d,y) :: r\bigr)`$ gives
$`\mathrm{steps}_1(r)`$, hence
$`\mathrm{steps}_1\bigl(\mathrm{tw}_d r \mathbin{+\!\!+} \mathrm{dw}_d r\bigr)`$ holds.
Applying the $`\to`$ direction of [T.steps1_append](#t-steps1_append), its second conjunct is
$`\mathrm{steps}_1(\mathrm{dw}_d r)`$. ∎

<a id="t-seqlex_arg_or_tail"></a>
## Theorem: the first difference occurs either on the prefix side or on the remainder side (T.seqlex_arg_or_tail)

### Theorem

Let $`d \in \mathbb{N}`$ and $`r, r' \in \mathrm{PairSeq}`$.
If $`r \prec_{\mathrm{lex}} r'`$ then one of the following two statements holds.

```math
\begin{aligned}
&\text{(T)}\quad \mathrm{tw}_d r = \mathrm{tw}_d r' \ \wedge\
  \mathrm{dw}_d r \prec_{\mathrm{lex}} \mathrm{dw}_d r', \cr
&\text{(A)}\quad \mathrm{tw}_d r \ne \mathrm{tw}_d r' \ \wedge\
  \mathrm{tw}_d r \prec_{\mathrm{lex}} \mathrm{tw}_d r' .
\end{aligned}
```

### Proof

By induction on the list structure of $`r`$ (with $`r'`$ kept universally quantified).
Show

```math
\Phi(r) :\equiv \forall r' \in \mathrm{PairSeq},\
  r \prec_{\mathrm{lex}} r' \to \bigl(\text{(T)} \vee \text{(A)}\bigr)
```

for every $`r`$.

In what follows we use the following four equalities, which follow from the definitions of
$`\mathrm{tw}`$ and $`\mathrm{dw}`$ (D.translate). If $`d \lt p_1`$ then

```math
\mathrm{tw}_d(p :: L) = p :: \mathrm{tw}_d L, \qquad
\mathrm{dw}_d(p :: L) = \mathrm{dw}_d L
```

and if $`\neg(d \lt p_1)`$ then

```math
\mathrm{tw}_d(p :: L) = (), \qquad
\mathrm{dw}_d(p :: L) = p :: L
```

**Base case** $`r = ()`$: take $`r'`$ and assume $`() \prec_{\mathrm{lex}} r'`$.
By [T.seqlex_nil_iff](#t-seqlex_nil_iff) we have $`r' \ne ()`$.
By the definitions of $`\mathrm{tw}`$ and $`\mathrm{dw}`$ (D.translate) we have
$`\mathrm{tw}_d\,() = ()`$ and $`\mathrm{dw}_d\,() = ()`$.
We distinguish cases according to whether $`\mathrm{tw}_d r'`$ is empty.

**(i) $`\mathrm{tw}_d r' = ()`$.** We show (T). The first conjunct is
$`\mathrm{tw}_d\,() = () = \mathrm{tw}_d r'`$. For the second conjunct, we first show
$`\mathrm{dw}_d r' = r'`$. Since $`r' \ne ()`$ we may write $`r' = q :: t`$.
If $`d \lt q_1`$ then $`\mathrm{tw}_d r' = q :: \mathrm{tw}_d t \ne ()`$, contradicting the
assumption; hence $`\neg(d \lt q_1)`$ and $`\mathrm{dw}_d(q :: t) = q :: t = r'`$.
Therefore what has to be shown is $`() \prec_{\mathrm{lex}} r'`$, which follows from
[T.seqlex_nil_iff](#t-seqlex_nil_iff) and $`r' \ne ()`$.

**(ii) $`\mathrm{tw}_d r' \ne ()`$.** We show (A). The first conjunct follows from
$`\mathrm{tw}_d\,() = ()`$ and the assumption $`\mathrm{tw}_d r' \ne ()`$.
The second conjunct $`() \prec_{\mathrm{lex}} \mathrm{tw}_d r'`$ follows from
[T.seqlex_nil_iff](#t-seqlex_nil_iff) and the assumption $`\mathrm{tw}_d r' \ne ()`$.

**Inductive step** $`r = p :: rr`$: assume $`\Phi(rr)`$, that is,

```math
\begin{aligned}
\forall r'',\ rr \prec_{\mathrm{lex}} r'' \to \Bigl(
  &\bigl(\mathrm{tw}_d rr = \mathrm{tw}_d r'' \wedge
    \mathrm{dw}_d rr \prec_{\mathrm{lex}} \mathrm{dw}_d r''\bigr) \cr
  &\vee \bigl(\mathrm{tw}_d rr \ne \mathrm{tw}_d r'' \wedge
    \mathrm{tw}_d rr \prec_{\mathrm{lex}} \mathrm{tw}_d r''\bigr)\Bigr)
\end{aligned}
```

Take $`r'`$ and assume $`(p :: rr) \prec_{\mathrm{lex}} r'`$.
If $`r' = ()`$ this contradicts [T.not_seqlex_nil](#t-not_seqlex_nil), so we may write
$`r' = q :: rr'`$. We distinguish cases according to whether $`p = q`$.

**(a) $`p = q`$.** In what follows we rewrite $`q`$ as $`p`$, so that $`r' = p :: rr'`$.
By [T.seqlex_cons_cons](#t-seqlex_cons_cons) we have
$`p \prec_{\mathrm{p}} p`$ or $`p = p \wedge rr \prec_{\mathrm{lex}} rr'`$.
By the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt), $`p \prec_{\mathrm{p}} p`$ means
$`p_1 \lt p_1`$ or $`p_1 = p_1 \wedge p_2 \lt p_2`$, and both are false by irreflexivity of
$`\lt`$ on $`\mathbb{N}`$. Hence we obtain $`rr \prec_{\mathrm{lex}} rr'`$.
We distinguish further cases according to whether $`d \lt p_1`$.

**(a-1) $`d \lt p_1`$.** In this case

```math
\mathrm{tw}_d(p :: rr) = p :: \mathrm{tw}_d rr, \qquad
\mathrm{dw}_d(p :: rr) = \mathrm{dw}_d rr,
```
```math
\mathrm{tw}_d(p :: rr') = p :: \mathrm{tw}_d rr', \qquad
\mathrm{dw}_d(p :: rr') = \mathrm{dw}_d rr'
```

Apply the induction hypothesis with $`r'' := rr'`$ to $`rr \prec_{\mathrm{lex}} rr'`$, and
distinguish cases on the disjunction in its conclusion.

- Case (T) holds, that is, $`\mathrm{tw}_d rr = \mathrm{tw}_d rr'`$ and
  $`\mathrm{dw}_d rr \prec_{\mathrm{lex}} \mathrm{dw}_d rr'`$.
  We show (T) in the conclusion. The first conjunct is
  $`p :: \mathrm{tw}_d rr = p :: \mathrm{tw}_d rr'`$, which follows from
  $`\mathrm{tw}_d rr = \mathrm{tw}_d rr'`$. The second conjunct is exactly
  $`\mathrm{dw}_d rr \prec_{\mathrm{lex}} \mathrm{dw}_d rr'`$.

- Case (A) holds, that is, $`\mathrm{tw}_d rr \ne \mathrm{tw}_d rr'`$ and
  $`\mathrm{tw}_d rr \prec_{\mathrm{lex}} \mathrm{tw}_d rr'`$.
  We show (A) in the conclusion. For the first conjunct, assuming
  $`p :: \mathrm{tw}_d rr = p :: \mathrm{tw}_d rr'`$, injectivity of the constructor $`::`$ gives
  $`\mathrm{tw}_d rr = \mathrm{tw}_d rr'`$, a contradiction.
  The second conjunct follows from the second disjunct
  $`p = p \wedge \mathrm{tw}_d rr \prec_{\mathrm{lex}} \mathrm{tw}_d rr'`$ on the right-hand side
  of [T.seqlex_cons_cons](#t-seqlex_cons_cons).

**(a-2) $`\neg(d \lt p_1)`$.** In this case

```math
\mathrm{tw}_d(p :: rr) = () = \mathrm{tw}_d(p :: rr'), \qquad
\mathrm{dw}_d(p :: rr) = p :: rr, \qquad
\mathrm{dw}_d(p :: rr') = p :: rr'
```

We show (T) in the conclusion. The first conjunct is the equality above. The second conjunct
$`(p :: rr) \prec_{\mathrm{lex}} (p :: rr')`$ is exactly the hypothesis
$`(p :: rr) \prec_{\mathrm{lex}} r'`$.

**(b) $`p \ne q`$.** By [T.seqlex_cons_cons](#t-seqlex_cons_cons) we have
$`p \prec_{\mathrm{p}} q`$ or $`p = q \wedge rr \prec_{\mathrm{lex}} rr'`$, and the second
disjunct contradicts $`p \ne q`$, so $`p \prec_{\mathrm{p}} q`$.
We distinguish cases according to whether $`d \lt p_1`$ and $`d \lt q_1`$ hold.

**(b-1) $`d \lt p_1`$.** By the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt) we have
$`p_1 \lt q_1`$ or $`p_1 = q_1`$; in either case $`p_1 \le q_1`$, so
$`d \lt p_1 \le q_1`$, that is, $`d \lt q_1`$. Therefore

```math
\mathrm{tw}_d(p :: rr) = p :: \mathrm{tw}_d rr, \qquad
\mathrm{tw}_d(q :: rr') = q :: \mathrm{tw}_d rr'
```

We show (A) in the conclusion. For the first conjunct, assuming
$`p :: \mathrm{tw}_d rr = q :: \mathrm{tw}_d rr'`$, injectivity of the constructor $`::`$ gives
$`p = q`$, contradicting $`p \ne q`$. The second conjunct follows from the first disjunct
$`p \prec_{\mathrm{p}} q`$ on the right-hand side of
[T.seqlex_cons_cons](#t-seqlex_cons_cons).

**(b-2) $`\neg(d \lt p_1)`$ and $`d \lt q_1`$.** In this case

```math
\mathrm{tw}_d(p :: rr) = (), \qquad
\mathrm{tw}_d(q :: rr') = q :: \mathrm{tw}_d rr'
```

We show (A) in the conclusion. The first conjunct holds because $`q :: \mathrm{tw}_d rr'`$ is
non-empty. The second conjunct $`() \prec_{\mathrm{lex}} (q :: \mathrm{tw}_d rr')`$ follows from
[T.seqlex_nil_iff](#t-seqlex_nil_iff) and $`q :: \mathrm{tw}_d rr' \ne ()`$.

**(b-3) $`\neg(d \lt p_1)`$ and $`\neg(d \lt q_1)`$.** In this case

```math
\mathrm{tw}_d(p :: rr) = () = \mathrm{tw}_d(q :: rr'), \qquad
\mathrm{dw}_d(p :: rr) = p :: rr, \qquad
\mathrm{dw}_d(q :: rr') = q :: rr'
```

We show (T) in the conclusion. The first conjunct is the equality above. The second conjunct
$`(p :: rr) \prec_{\mathrm{lex}} (q :: rr')`$ is exactly the hypothesis
$`(p :: rr) \prec_{\mathrm{lex}} r'`$.

Since (T) or (A) has now been established in every one of the cases (a-1), (a-2), (b-1), (b-2),
(b-3), we obtain $`\Phi(p :: rr)`$. ∎
