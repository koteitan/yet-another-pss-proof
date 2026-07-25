[← README](README.md) | [English](Cofinality.md) | [Japanese](Cofinality-ja.md) | Cofinality **1** [2](Cofinality-2.md) [3](Cofinality-3.md)

<a id="t-pairlt_trans"></a>
## Theorem: transitivity of the order on pairs (T.pairlt_trans)

### Theorem

Let $`p, q, r \in \mathbb{N}\times\mathbb{N}`$. If $`p \prec_{\mathrm{p}} q`$ ([D.pairlt](Seqlex.md#d-pairlt)) and
$`q \prec_{\mathrm{p}} r`$, then $`p \prec_{\mathrm{p}} r`$.

### Proof

The definition of $`\prec_{\mathrm{p}}`$ (D.pairlt) is

```math
x \prec_{\mathrm{p}} y \iff x_1 \lt y_1 \ \vee\ (x_1 = y_1 \wedge x_2 \lt y_2)
```

The hypothesis $`p \prec_{\mathrm{p}} q`$ is one of the following.

- (1) $`p_1 \lt q_1`$
- (2) $`p_1 = q_1 \wedge p_2 \lt q_2`$

The hypothesis $`q \prec_{\mathrm{p}} r`$ is one of the following.

- (I) $`q_1 \lt r_1`$
- (II) $`q_1 = r_1 \wedge q_2 \lt r_2`$

For each of the four cases we show which disjunct on the right-hand side of $`p \prec_{\mathrm{p}} r`$ holds.

| | (I) | (II) |
|---|---|---|
| **(1)** | $`p_1 \lt r_1`$ | $`p_1 \lt r_1`$ |
| **(2)** | $`p_1 \lt r_1`$ | $`p_1 = r_1 \wedge p_2 \lt r_2`$ |

The entries are justified as follows.

- **(1)(I)**: apply transitivity of $`\lt`$ on $`\mathbb{N}`$ to $`p_1 \lt q_1`$ and $`q_1 \lt r_1`$.
- **(1)(II)**: substituting $`q_1 = r_1`$ into $`p_1 \lt q_1`$ gives $`p_1 \lt r_1`$.
- **(2)(I)**: substituting $`p_1 = q_1`$ into $`q_1 \lt r_1`$ gives $`p_1 \lt r_1`$.
- **(2)(II)**: here $`p_1 = q_1 = r_1`$, and applying transitivity of $`\lt`$ on $`\mathbb{N}`$ to
  $`p_2 \lt q_2`$ and $`q_2 \lt r_2`$ gives $`p_2 \lt r_2`$. ∎

<a id="t-seqlex_trans"></a>
## Theorem: transitivity of the column-lex order (T.seqlex_trans)

### Theorem

Let $`A, B, C \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)).
If $`A \prec_{\mathrm{lex}} B`$ ([D.seqlex](Seqlex.md#d-seqlex)) and $`B \prec_{\mathrm{lex}} C`$, then
$`A \prec_{\mathrm{lex}} C`$.

### Proof

We argue by induction on the constructor of $`A`$ ($`()`$ or $`::`$), keeping $`B`$ and $`C`$ universally quantified.
The induction predicate is

```math
\Phi(A) :\equiv \forall B, C \in \mathrm{PairSeq},\
  \bigl(A \prec_{\mathrm{lex}} B \wedge B \prec_{\mathrm{lex}} C\bigr) \to A \prec_{\mathrm{lex}} C .
```

- **Base case** $`A = ()`$: by the first clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex),
  what has to be shown is $`C \ne ()`$. Suppose $`C = ()`$ and derive a contradiction.
  Distinguish cases on the constructor of $`B`$ in the hypothesis $`B \prec_{\mathrm{lex}} ()`$.
  If $`B = ()`$, then by the first clause of the definition (D.seqlex) the statement
  $`B \prec_{\mathrm{lex}} ()`$ is $`() \ne ()`$, which is false. If $`B = b :: B'`$, then by
  the second clause of the definition (D.seqlex) the statement $`B \prec_{\mathrm{lex}} ()`$ is $`\bot`$.
  Both cases are contradictory, hence $`C \ne ()`$.

- **Inductive step** $`A = a :: A'`$: the induction hypothesis is $`\Phi(A')`$.
  Take $`B`$ and $`C`$ with $`a :: A' \prec_{\mathrm{lex}} B`$ and $`B \prec_{\mathrm{lex}} C`$.
  If $`B = ()`$, the second clause of the definition (D.seqlex) turns the first hypothesis into $`\bot`$,
  so $`B = b :: B'`$. If $`C = ()`$, the second clause of the definition (D.seqlex) likewise turns
  the second hypothesis into $`\bot`$, so $`C = c :: C'`$.
  By the third clause of the definition (D.seqlex), the first hypothesis is one of the following.

  - (1) $`a \prec_{\mathrm{p}} b`$
  - (2) $`a = b \wedge A' \prec_{\mathrm{lex}} B'`$

  Likewise the second hypothesis is one of the following.

  - (I) $`b \prec_{\mathrm{p}} c`$
  - (II) $`b = c \wedge B' \prec_{\mathrm{lex}} C'`$

  For each of the four cases we show which disjunct on the right-hand side of the third clause of
  the definition (D.seqlex) holds.

  | | (I) | (II) |
  |---|---|---|
  | **(1)** | $`a \prec_{\mathrm{p}} c`$ | $`a \prec_{\mathrm{p}} c`$ |
  | **(2)** | $`a \prec_{\mathrm{p}} c`$ | $`a = c \wedge A' \prec_{\mathrm{lex}} C'`$ |

  The entries are justified as follows.

  - **(1)(I)**: apply [T.pairlt_trans](#t-pairlt_trans) to $`a \prec_{\mathrm{p}} b`$ and
    $`b \prec_{\mathrm{p}} c`$.
  - **(1)(II)**: substitute $`b = c`$ into $`a \prec_{\mathrm{p}} b`$.
  - **(2)(I)**: substitute $`a = b`$ into $`b \prec_{\mathrm{p}} c`$.
  - **(2)(II)**: here $`a = b = c`$, and applying the induction hypothesis $`\Phi(A')`$ to
    $`A' \prec_{\mathrm{lex}} B'`$ and $`B' \prec_{\mathrm{lex}} C'`$ gives $`A' \prec_{\mathrm{lex}} C'`$.

  In every case $`a :: A' \prec_{\mathrm{lex}} c :: C'`$ is obtained, hence $`\Phi(a :: A')`$. ∎

<a id="d-sle"></a>
## Definition: non-strict column-lex order (D.sle)

For $`M, N \in \mathrm{PairSeq}`$,

```math
M \preceq_{\mathrm{lex}} N :\iff M = N \ \vee\ M \prec_{\mathrm{lex}} N .
```

<a id="t-sle_refl"></a>
## Theorem: reflexivity of the non-strict column-lex order (T.sle_refl)

### Theorem

For every $`M \in \mathrm{PairSeq}`$, $`M \preceq_{\mathrm{lex}} M`$.

### Proof

The first disjunct $`M = M`$ of the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle) holds by reflexivity of $`=`$. ∎

<a id="t-seqlex_sle_trans"></a>
## Theorem: composing the strict and the non-strict order (T.seqlex_sle_trans)

### Theorem

If $`A \prec_{\mathrm{lex}} B`$ and $`B \preceq_{\mathrm{lex}} C`$, then $`A \prec_{\mathrm{lex}} C`$.

### Proof

By the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle), $`B \preceq_{\mathrm{lex}} C`$ means $`B = C`$ or
$`B \prec_{\mathrm{lex}} C`$. In the former case, rewriting $`C`$ as $`B`$ turns the goal into the hypothesis
$`A \prec_{\mathrm{lex}} B`$ itself. In the latter case, apply [T.seqlex_trans](#t-seqlex_trans) to
$`A \prec_{\mathrm{lex}} B`$ and $`B \prec_{\mathrm{lex}} C`$. ∎

<a id="t-seqlex_append_mono"></a>
## Theorem: appending on the larger side preserves the order (T.seqlex_append_mono)

### Theorem

If $`A \prec_{\mathrm{lex}} B`$, then $`A \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$ for every
$`C \in \mathrm{PairSeq}`$.

### Proof

Induction on the constructor of $`A`$. The induction predicate is

```math
\Phi(A) :\equiv \forall B \in \mathrm{PairSeq},\ A \prec_{\mathrm{lex}} B \to
  \forall C \in \mathrm{PairSeq},\ A \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C .
```

- **Base case** $`A = ()`$: if $`B = ()`$, then by the first clause of the definition of
  $`\prec_{\mathrm{lex}}`$ (D.seqlex) the hypothesis $`() \prec_{\mathrm{lex}} ()`$ is $`() \ne ()`$,
  which is false. Hence $`B = b :: B'`$, and
  $`B \mathbin{+\!\!+} C = b :: (B' \mathbin{+\!\!+} C) \ne ()`$.
  By the first clause of the definition (D.seqlex) again, $`() \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$.

- **Inductive step** $`A = a :: A'`$: the induction hypothesis is $`\Phi(A')`$.
  If $`B = ()`$, the second clause of the definition (D.seqlex) turns the hypothesis into $`\bot`$,
  so $`B = b :: B'`$. By the third clause of the definition (D.seqlex), the hypothesis is one of the following.

  - Case $`a \prec_{\mathrm{p}} b`$.
    Since $`(a :: A') \mathbin{+\!\!+} C = a :: (A' \mathbin{+\!\!+} C)`$ and
    $`(b :: B') \mathbin{+\!\!+} C = b :: (B' \mathbin{+\!\!+} C)`$,
    the first disjunct on the right-hand side of the third clause of the definition (D.seqlex) holds as it stands.

  - Case $`a = b \wedge A' \prec_{\mathrm{lex}} B'`$. Applying the induction hypothesis $`\Phi(A')`$ to
    $`B'`$ and $`C`$ gives $`A' \prec_{\mathrm{lex}} B' \mathbin{+\!\!+} C`$.
    Together with $`a = b`$, the second disjunct on the right-hand side of the third clause of the
    definition (D.seqlex) holds. ∎

<a id="t-sle_append_mono"></a>
## Theorem: monotonicity under appending, non-strict version (T.sle_append_mono)

### Theorem

If $`A \preceq_{\mathrm{lex}} B`$, then $`A \preceq_{\mathrm{lex}} B \mathbin{+\!\!+} C`$ for every
$`C \in \mathrm{PairSeq}`$.

### Proof

Distinguish cases according to the disjunction in the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle).

- Case $`A = B`$. Distinguish cases on the constructor of $`C`$.
  - Case $`C = ()`$. Since $`B \mathbin{+\!\!+} () = B = A`$, the first disjunct of the definition (D.sle) holds.
  - Case $`C = c :: C'`$. Here $`C \ne ()`$, so applying
    [T.seqlex_prefix](Seqlex.md#t-seqlex_prefix) with $`u := A`$ and $`v := C`$ gives
    $`A \prec_{\mathrm{lex}} A \mathbin{+\!\!+} C = B \mathbin{+\!\!+} C`$.
    Thus the second disjunct of the definition (D.sle) holds.

- Case $`A \prec_{\mathrm{lex}} B`$. By [T.seqlex_append_mono](#t-seqlex_append_mono) we have
  $`A \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$, so the second disjunct of the definition (D.sle) holds. ∎

<a id="t-seqlex_snoc_cases"></a>
## Theorem: case distinction below a sequence with one column appended (T.seqlex_snoc_cases)

### Theorem

Let $`D, N \in \mathrm{PairSeq}`$ and $`\ell \in \mathbb{N}\times\mathbb{N}`$.
If $`N \prec_{\mathrm{lex}} D \mathbin{+\!\!+} (\ell)`$, then

```math
N \preceq_{\mathrm{lex}} D
\qquad\text{or}\qquad
\exists q, S,\ \bigl(N = D \mathbin{+\!\!+} q :: S \wedge q \prec_{\mathrm{p}} \ell\bigr).
```

### Proof

Induction on the constructor of $`D`$, keeping $`\ell`$ and $`N`$ universally quantified. The induction predicate is

```math
\Phi(D) :\equiv \forall \ell, N,\ N \prec_{\mathrm{lex}} D \mathbin{+\!\!+} (\ell) \to
  \Bigl(N \preceq_{\mathrm{lex}} D \ \vee\
    \exists q, S,\ \bigl(N = D \mathbin{+\!\!+} q :: S \wedge q \prec_{\mathrm{p}} \ell\bigr)\Bigr).
```

- **Base case** $`D = ()`$: here $`D \mathbin{+\!\!+} (\ell) = (\ell)`$. Distinguish cases on the constructor of $`N`$.
  - Case $`N = ()`$. By [T.sle_refl](#t-sle_refl) we have $`() \preceq_{\mathrm{lex}} ()`$, so
    the first disjunct holds.
  - Case $`N = q :: S`$. By the third clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex),
    the hypothesis is $`q \prec_{\mathrm{p}} \ell`$ or $`(q = \ell \wedge S \prec_{\mathrm{lex}} ())`$.
    The second conjunct of the latter is false: if $`S = ()`$ it reads $`() \ne ()`$ by the first clause of
    the definition (D.seqlex), and if $`S = s :: S'`$ it is $`\bot`$ by the second clause of the definition (D.seqlex).
    Hence $`q \prec_{\mathrm{p}} \ell`$, and since $`N = () \mathbin{+\!\!+} q :: S`$,
    the second disjunct holds.

- **Inductive step** $`D = d :: D'`$: the induction hypothesis is $`\Phi(D')`$.
  Here $`(d :: D') \mathbin{+\!\!+} (\ell) = d :: (D' \mathbin{+\!\!+} (\ell))`$. Distinguish cases on the constructor of $`N`$.

  - Case $`N = ()`$. Since $`d :: D' \ne ()`$, the first clause of the definition (D.seqlex) gives
    $`() \prec_{\mathrm{lex}} d :: D'`$, and the second disjunct of the definition (D.sle) gives
    $`N \preceq_{\mathrm{lex}} D`$. Thus the first disjunct holds.

  - Case $`N = q :: S`$. By the third clause of the definition (D.seqlex), the hypothesis is one of the following.

    - Case $`q \prec_{\mathrm{p}} d`$. The first disjunct of the third clause of the definition (D.seqlex) gives
      $`q :: S \prec_{\mathrm{lex}} d :: D'`$, and the second disjunct of the definition (D.sle) gives
      $`N \preceq_{\mathrm{lex}} D`$. Thus the first disjunct holds.

    - Case $`q = d \wedge S \prec_{\mathrm{lex}} D' \mathbin{+\!\!+} (\ell)`$.
      Apply the induction hypothesis $`\Phi(D')`$ to $`\ell`$ and $`S`$.

      - If $`S \preceq_{\mathrm{lex}} D'`$ is obtained, distinguish cases according to the definition (D.sle).
        If $`S = D'`$, then $`N = d :: S = d :: D' = D`$ and the first disjunct of the definition (D.sle) holds.
        If $`S \prec_{\mathrm{lex}} D'`$, then together with $`q = d`$ the second disjunct of the third clause of
        the definition (D.seqlex) gives $`N = d :: S \prec_{\mathrm{lex}} d :: D' = D`$, so
        the second disjunct of the definition (D.sle) holds. In both cases this is the first disjunct.

      - If $`S = D' \mathbin{+\!\!+} q' :: S'`$ with $`q' \prec_{\mathrm{p}} \ell`$ is obtained, then
        $`N = d :: S = (d :: D') \mathbin{+\!\!+} q' :: S' = D \mathbin{+\!\!+} q' :: S'`$, so
        the second disjunct holds. ∎

<a id="d-SeqlexCofinality"></a>
## Definition: the column-lex form of cofinality (D.SeqlexCofinality)

Define the proposition $`\mathrm{SeqlexCofinality}`$ by

```math
\begin{aligned}
&\mathrm{SeqlexCofinality} :\equiv
  \forall M, N \in \mathrm{PairSeq},\ \cr
&\qquad \bigl(M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS}
  \wedge N \prec_{\mathrm{lex}} M\bigr) \cr
&\qquad \to \exists n,\ \bigl(1 \le n \wedge N \preceq_{\mathrm{lex}} M[n]\bigr).
\end{aligned}
```

($`\mathrm{ST\_PS}`$ [D.ST_PS](Pss.md#d-ST_PS), $`M[n]`$ [D.oper](Pss.md#d-oper))

<a id="t-pss_cofinality_of_seqlex"></a>
## Theorem: cofinality from the column-lex form (T.pss_cofinality_of_seqlex)

### Theorem

Suppose $`\mathrm{SeqlexCofinality}`$ holds. If $`M, N \in \mathrm{ST\_PS}`$ satisfy
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ ([D.translate](Term.md#d-translate)), then

```math
\exists n,\ \bigl(1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])\bigr).
```

($`\prec`$ [D.olt](Term.md#d-olt), $`\preceq`$ [D.ole](Term.md#d-ole))

### Proof

First, $`N \ne M`$. Indeed, if $`N = M`$ the hypothesis becomes $`\mathrm{tr}\,M \prec \mathrm{tr}\,M`$,
contradicting [T.olt_irrefl](Term.md#t-olt_irrefl).

By $`N \ne M`$ and $`N, M \in \mathrm{ST\_PS}`$,
[T.olt_ST_iff_seqlex](Seqlex-2.md#t-olt_ST_iff_seqlex) applies, and the hypothesis gives
$`N \prec_{\mathrm{lex}} M`$. Applying $`\mathrm{SeqlexCofinality}`$ to this, take $`n`$ with
$`1 \le n`$ and $`N \preceq_{\mathrm{lex}} M[n]`$. It remains to show
$`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$ for this $`n`$.
Distinguish cases according to the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle).

- Case $`N = M[n]`$. The translations of the two sides are the same term, so the second disjunct of
  the definition of $`\preceq`$ (D.ole) holds.

- Case $`N \prec_{\mathrm{lex}} M[n]`$. Distinguish further according to whether $`N = M[n]`$.
  - Case $`N = M[n]`$. As above, the second disjunct of the definition of $`\preceq`$ (D.ole) holds.
  - Case $`N \ne M[n]`$. Applying the rule (oper) of the definition of $`\mathrm{ST\_PS}`$ (D.ST_PS) to
    $`M \in \mathrm{ST\_PS}`$ and $`1 \le n`$ gives $`M[n] \in \mathrm{ST\_PS}`$.
    Applying [T.olt_ST_iff_seqlex](Seqlex-2.md#t-olt_ST_iff_seqlex) to $`N`$ and $`M[n]`$ gives
    $`\mathrm{tr}\,N \prec \mathrm{tr}\,(M[n])`$, so the first disjunct of the definition of
    $`\preceq`$ (D.ole) holds. ∎

<a id="t-entry_zero"></a>
## Theorem: the entry in row 0 (T.entry_zero)

### Theorem

For every $`M \in \mathrm{PairSeq}`$ and $`j \in \mathbb{N}`$,
$`M_{0,j} = \pi_1\bigl(M\langle j\rangle\bigr)`$ ([D.entry](Pss.md#d-entry)).

### Proof

The side condition $`i = 0`$ of the case distinction in the definition of $`M_{i,j}`$ (D.entry) holds for
$`i := 0`$, so the first case is selected. ∎

<a id="t-entry_one"></a>
## Theorem: the entry in row 1 (T.entry_one)

### Theorem

For every $`M \in \mathrm{PairSeq}`$ and $`j \in \mathbb{N}`$,
$`M_{1,j} = \pi_2\bigl(M\langle j\rangle\bigr)`$.

### Proof

For $`i := 1`$ the side condition $`i = 0`$ of the case distinction in the definition of $`M_{i,j}`$ (D.entry)
reads $`1 = 0`$, which is false. Hence the second case is selected. ∎

<a id="t-dropLast_snoc_getD"></a>
## Theorem: splitting off the last column (T.dropLast_snoc_getD)

### Theorem

If $`M \ne ()`$, then

```math
\mathrm{dropLast}\,M \mathbin{+\!\!+} \bigl(M\langle \lvert M\rvert - 1\rangle\bigr) = M .
```

### Proof

From $`M \ne ()`$ we get $`0 \lt \lvert M\rvert`$, hence $`\lvert M\rvert - 1 \lt \lvert M\rvert`$, so
the first case of the definition of $`M\langle j\rangle`$ (D.entry) gives
$`M\langle \lvert M\rvert - 1\rangle = M_{\lvert M\rvert - 1}`$, that is, the last element of $`M`$.
Since $`\mathrm{dropLast}\,M`$ is $`M`$ with its last element removed, appending that last element to it
gives back $`M`$. ∎

<a id="t-seqlex_cof_short"></a>
## Theorem: cofinality in the branch where the length is at most 1 (T.seqlex_cof_short)

### Theorem

If $`\lvert M\rvert - 1 = 0`$ and $`N \prec_{\mathrm{lex}} M`$, then

```math
\exists n,\ \bigl(1 \le n \wedge N \preceq_{\mathrm{lex}} M[n]\bigr).
```

### Proof

Take $`n := 1`$; indeed $`1 \le 1`$.
Applying [T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) to the hypothesis
$`\lvert M\rvert - 1 = 0`$ with $`n := 1`$ gives $`M[1] = M`$, so what has to be shown is
$`N \preceq_{\mathrm{lex}} M`$. By the hypothesis $`N \prec_{\mathrm{lex}} M`$, the second disjunct of
the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle) holds. ∎

<a id="t-seqlex_cof_zero"></a>
## Theorem: cofinality in the branch whose last column is $`(0,0)`$ (T.seqlex_cof_zero)

### Theorem

If $`1 \lt \lvert M\rvert`$, $`M_{0,\lvert M\rvert - 1} = 0 \wedge M_{1,\lvert M\rvert - 1} = 0`$
and $`N \prec_{\mathrm{lex}} M`$, then

```math
\exists n,\ \bigl(1 \le n \wedge N \preceq_{\mathrm{lex}} M[n]\bigr).
```

### Proof

Put $`j_1 := \lvert M\rvert - 1`$. From $`1 \lt \lvert M\rvert`$ we get $`M \ne ()`$ and
$`j_1 \ne 0`$.

**Step 1: $`M\langle j_1\rangle = (0,0)`$.**
By [T.entry_zero](#t-entry_zero) and [T.entry_one](#t-entry_one) we have
$`\pi_1(M\langle j_1\rangle) = M_{0,j_1} = 0`$ and $`\pi_2(M\langle j_1\rangle) = M_{1,j_1} = 0`$.
A pair is determined by its two entries, hence $`M\langle j_1\rangle = (0,0)`$.

**Step 2: $`M[1] = \mathrm{dropLast}\,M`$.**
Applying [T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) to $`j_1 \ne 0`$ and the second
conjunct of the hypothesis gives $`M[1] = \mathrm{Pred}\,M`$ ([D.Pred](Pss.md#d-Pred)).
From $`1 \lt \lvert M\rvert`$ we get $`\neg(\lvert M\rvert \le 1)`$, so
the second case of the definition of $`\mathrm{Pred}`$ (D.Pred) is selected and
$`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$.

**Step 3: $`N \preceq_{\mathrm{lex}} \mathrm{dropLast}\,M`$.**
By [T.dropLast_snoc_getD](#t-dropLast_snoc_getD) we have
$`\mathrm{dropLast}\,M \mathbin{+\!\!+} (M\langle j_1\rangle) = M`$, so the hypothesis
$`N \prec_{\mathrm{lex}} M`$ is exactly $`N \prec_{\mathrm{lex}} \mathrm{dropLast}\,M \mathbin{+\!\!+} (M\langle j_1\rangle)`$.
Apply [T.seqlex_snoc_cases](#t-seqlex_snoc_cases) with
$`D := \mathrm{dropLast}\,M`$ and $`\ell := M\langle j_1\rangle`$.

- If the first disjunct $`N \preceq_{\mathrm{lex}} \mathrm{dropLast}\,M`$ is obtained, this is the goal.
- If the second disjunct is obtained, there exists $`q`$ with
  $`q \prec_{\mathrm{p}} M\langle j_1\rangle = (0,0)`$. By the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt)
  this means $`q_1 \lt 0`$ or $`(q_1 = 0 \wedge q_2 \lt 0)`$, and both are false since $`\mathbb{N}`$ has
  no element smaller than $`0`$. Hence this case does not occur.

Taking $`n := 1`$, Steps 2 and 3 give $`N \preceq_{\mathrm{lex}} M[1]`$. ∎

<a id="t-hasParent_last_ST_PS"></a>
## Theorem: the last column of a standard form always has a parent (T.hasParent_last_ST_PS)

### Theorem

If $`M \in \mathrm{ST\_PS}`$, $`0 \lt \lvert M\rvert`$ and
$`\neg\bigl(M_{0,\lvert M\rvert - 1} = 0 \wedge M_{1,\lvert M\rvert - 1} = 0\bigr)`$, then

```math
\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M, \lvert M\rvert - 1),\ \lvert M\rvert - 1\bigr) .
```

($`\mathrm{hasParent}`$ [D.hasParent](Pss.md#d-hasParent), $`\mathrm{idx}_1`$ [D.idx1](Pss.md#d-idx1))

### Proof

Put $`j_1 := \lvert M\rvert - 1`$ and apply [T.hp_last](Column-4.md#t-hp_last).
Its four hypotheses are met as follows.

- $`\mathrm{blockok}(0, M)`$ ([D.blockok](Seqlex.md#d-blockok)):
  by [T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS).
- $`\mathrm{z0ok}(M)`$ ([D.z0ok](Column-3.md#d-z0ok)): by [T.z0ok_ST_PS](Column-4.md#t-z0ok_ST_PS).
- $`0 \lt \lvert M\rvert`$: this is a hypothesis.
- $`\neg\bigl(M\langle j_1\rangle = (0,0)\bigr)`$: suppose $`M\langle j_1\rangle = (0,0)`$; then
  [T.entry_zero](#t-entry_zero) gives $`M_{0,j_1} = \pi_1((0,0)) = 0`$ and
  [T.entry_one](#t-entry_one) gives $`M_{1,j_1} = \pi_2((0,0)) = 0`$,
  contradicting the third hypothesis. ∎

<a id="t-sle_append_cancel"></a>
## Theorem: cancelling a common prefix (T.sle_append_cancel)

### Theorem

For $`A, u, v \in \mathrm{PairSeq}`$,

```math
A \mathbin{+\!\!+} u \preceq_{\mathrm{lex}} A \mathbin{+\!\!+} v \iff u \preceq_{\mathrm{lex}} v .
```

### Proof

By the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle), the left-hand side is

```math
A \mathbin{+\!\!+} u = A \mathbin{+\!\!+} v \ \vee\ A \mathbin{+\!\!+} u \prec_{\mathrm{lex}} A \mathbin{+\!\!+} v
```

The second disjunct is equivalent to $`u \prec_{\mathrm{lex}} v`$ by
[T.seqlex_append_cancel](Seqlex.md#t-seqlex_append_cancel). As for the first disjunct,
concatenation cancels on the left, that is,

```math
A \mathbin{+\!\!+} u = A \mathbin{+\!\!+} v \iff u = v
```

holds ($`\Leftarrow`$ is just prepending $`A`$ to both sides, and for $`\Rightarrow`$ it suffices to drop
the first $`\lvert A\rvert`$ elements of both sequences). Hence the left-hand side is equivalent to
$`u = v \vee u \prec_{\mathrm{lex}} v`$, that is, by the definition (D.sle), to $`u \preceq_{\mathrm{lex}} v`$. ∎

<a id="t-getD_append_right'"></a>
## Theorem: indexing into the right part of a concatenation (T.getD_append_right')

### Theorem

For $`A, B \in \mathrm{PairSeq}`$ and $`i \in \mathbb{N}`$,

```math
(A \mathbin{+\!\!+} B)\langle \lvert A\rvert + i\rangle = B\langle i\rangle .
```

### Proof

We have $`\lvert A \mathbin{+\!\!+} B\rvert = \lvert A\rvert + \lvert B\rvert`$. Distinguish cases according to
$`i`$ and $`\lvert B\rvert`$.

- Case $`i \lt \lvert B\rvert`$. Here $`\lvert A\rvert + i \lt \lvert A\rvert + \lvert B\rvert = \lvert A \mathbin{+\!\!+} B\rvert`$,
  so by the first case of the definition of $`M\langle j\rangle`$ (D.entry) both sides read an actual element.
  The element of the concatenation $`A \mathbin{+\!\!+} B`$ at index $`\lvert A\rvert + i`$ is, this index being
  at least $`\lvert A\rvert`$, the element of $`B`$ at index $`(\lvert A\rvert + i) - \lvert A\rvert = i`$.
  Hence the two sides are equal.

- Case $`\lvert B\rvert \le i`$. Here $`\lvert A \mathbin{+\!\!+} B\rvert = \lvert A\rvert + \lvert B\rvert \le \lvert A\rvert + i`$,
  so by the second case of the definition of $`M\langle j\rangle`$ (D.entry) both sides are $`(0,0)`$. ∎

<a id="t-getD_last_of_snoc"></a>
## Theorem: reading back the column appended at the end (T.getD_last_of_snoc)

### Theorem

For $`D \in \mathrm{PairSeq}`$ and $`\ell \in \mathbb{N}\times\mathbb{N}`$,

```math
\bigl(D \mathbin{+\!\!+} (\ell)\bigr)\bigl\langle \lvert D \mathbin{+\!\!+} (\ell)\rvert - 1\bigr\rangle = \ell .
```

### Proof

Since $`\lvert D \mathbin{+\!\!+} (\ell)\rvert = \lvert D\rvert + 1`$, we have
$`\lvert D \mathbin{+\!\!+} (\ell)\rvert - 1 = \lvert D\rvert`$.
Applying [T.getD_append_right'](#t-getD_append_right') with left sequence $`D`$, right sequence $`(\ell)`$
and index $`0`$ gives

```math
\bigl(D \mathbin{+\!\!+} (\ell)\bigr)\langle \lvert D\rvert + 0\rangle = (\ell)\langle 0\rangle
```

and since $`0 \lt 1 = \lvert (\ell)\rvert`$, the first case of the definition of $`M\langle j\rangle`$ (D.entry)
gives $`(\ell)\langle 0\rangle = \ell`$. ∎

<a id="t-nextrel1_snd_succ"></a>
## Theorem: row 1 increases by exactly 1 along the row-1 parent relation (T.nextrel1_snd_succ)

### Theorem

If $`\mathrm{r1ok}(M)`$ ([D.r1ok](Column-2.md#d-r1ok)) and $`j_0 \to^M_1 j_1`$ ([D.nextrel1](Pss.md#d-nextrel1)), then

```math
M_{1,j_1} = M_{1,j_0} + 1 .
```

### Proof

By the definition of $`\to^M_1`$ (D.nextrel1), the hypothesis is the conjunction of the following six statements.

```math
\begin{aligned}
&(1)\ j_0 \lt \lvert M\rvert, \cr
&(2)\ j_1 \lt \lvert M\rvert, \cr
&(3)\ j_0 \lt j_1, \cr
&(4)\ M_{1,j_0} \lt M_{1,j_1}, \cr
&(5)\ j_0 \le^M_0 j_1, \cr
&(6)\ \forall j\ \bigl(j_0 \lt j \wedge j \le^M_0 j_1 \to M_{1,j_1} \le M_{1,j}\bigr).
\end{aligned}
```

($`\le^M_0`$ [D.le0](Pss.md#d-le0))

**Step 1: take the first step $`c`$ of the chain in row $`0`$.**
From (5) and the third condition of the definition of $`\le^M_0`$ (D.le0) we get
$`j_0 \mathbin{(\to^M_0)^{*}} j_1`$ ([D.nextrel0](Pss.md#d-nextrel0)).
The reflexive transitive closure gives either $`j_0 = j_1`$, or, for some $`c`$,
$`j_0 \to^M_0 c`$ and $`c \mathbin{(\to^M_0)^{*}} j_1`$;
the former contradicts $`j_0 \lt j_1`$ from (3). Hence $`c`$ as in the latter can be taken.

By the third condition of the definition of $`\to^M_0`$ (D.nextrel0) we have $`j_0 \lt c`$, and by
the second condition $`c \lt \lvert M\rvert`$. Together with (2) and $`c \mathbin{(\to^M_0)^{*}} j_1`$,
all three conditions of the definition of $`\le^M_0`$ (D.le0) are met, giving $`c \le^M_0 j_1`$.

**Step 2: $`M_{1,j_1} \le M_{1,c}`$.**
Apply (6) with $`j := c`$. Its antecedent consists of $`j_0 \lt c`$ and $`c \le^M_0 j_1`$ from Step 1.

**Step 3: apply $`\mathrm{r1ok}(M)`$ to $`c`$.**
By the fourth condition of the definition of $`\to^M_0`$ (D.nextrel0) we have $`M_{0,j_0} \lt M_{0,c}`$,
which by [T.entry_zero](#t-entry_zero) reads $`\pi_1(M\langle j_0\rangle) \lt \pi_1(M\langle c\rangle)`$.
In particular $`0 \lt \pi_1(M\langle c\rangle)`$. Together with $`c \lt \lvert M\rvert`$,
applying $`\mathrm{r1ok}(M)`$ with $`j := c`$ yields $`k`$ satisfying the following four conditions.

```math
\begin{aligned}
&\text{(i)}\ k \lt c, \cr
&\text{(ii)}\ \pi_1(M\langle k\rangle) + 1 = \pi_1(M\langle c\rangle), \cr
&\text{(iii)}\ \forall l\ \bigl(k \lt l \wedge l \lt c \to \pi_1(M\langle c\rangle) \le \pi_1(M\langle l\rangle)\bigr), \cr
&\text{(iv)}\ \pi_2(M\langle c\rangle) \le \pi_2(M\langle k\rangle) + 1 .
\end{aligned}
```

**Step 4: $`k = j_0`$.**
We show $`k \to^M_0 c`$ by checking the five conditions of the definition of $`\to^M_0`$ (D.nextrel0) in turn.

- (1) $`k \lt \lvert M\rvert`$: from $`k \lt c`$ in (i) and $`c \lt \lvert M\rvert`$.
- (2) $`c \lt \lvert M\rvert`$: obtained in Step 1.
- (3) $`k \lt c`$: this is (i).
- (4) $`M_{0,k} \lt M_{0,c}`$: by [T.entry_zero](#t-entry_zero) this reads
  $`\pi_1(M\langle k\rangle) \lt \pi_1(M\langle c\rangle)`$, which follows from (ii).
- (5) $`\forall l\ (k \lt l \wedge l \lt c \to M_{0,c} \le M_{0,l})`$:
  by [T.entry_zero](#t-entry_zero) this is exactly (iii).

Since Step 1 also gives $`j_0 \to^M_0 c`$,
[T.nextrel0_unique](Column-4.md#t-nextrel0_unique) yields $`k = j_0`$.

**Step 5: conclusion.**
Substituting $`k = j_0`$ into (iv) and rewriting with [T.entry_one](#t-entry_one) gives

```math
M_{1,c} \le M_{1,j_0} + 1
```

Together with Step 2 this gives $`M_{1,j_1} \le M_{1,c} \le M_{1,j_0} + 1`$.
On the other hand (4) gives $`M_{1,j_0} \lt M_{1,j_1}`$, that is, $`M_{1,j_0} + 1 \le M_{1,j_1}`$.
By antisymmetry of $`\le`$ we conclude $`M_{1,j_1} = M_{1,j_0} + 1`$. ∎

<a id="t-oper_bad_blocks_all"></a>
## Theorem: block decomposition for the fourth branch (uniform in $`n`$) (T.oper_bad_blocks_all)

### Theorem

Put $`j_1 := \lvert M\rvert - 1`$ and $`i_1 := \mathrm{idx}_1(M, j_1)`$.
Assume $`1 \lt \lvert M\rvert`$, $`\mathrm{steps}_1(M)`$ ([D.steps1](Seqlex.md#d-steps1)), $`\mathrm{r1ok}(M)`$,
$`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$ and $`\mathrm{hasParent}(M, i_1, j_1)`$.
Then there exist $`G, R \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0 \in \mathbb{N}`$ and
$`\ell \in \mathbb{N}\times\mathbb{N}`$ such that, putting $`B := (v_0,w_0) :: R`$, the following five statements hold.

```math
\begin{aligned}
&(1)\ M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell), \cr
&(2)\ \forall n,\ 1 \le n \to M[n] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n), \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ v_0 \lt \ell_1, \cr
&(5)\ \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr) \ \vee\
        \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
              \wedge \lvert G\rvert \to^M_1 j_1\bigr).
\end{aligned}
```

($`\mathrm{cp}_{d}(B,n)`$ [D.copies](Cnf-2.md#d-copies))

### Proof

**Step 1: take the block decomposition at $`n = 1`$.**
Apply [T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks) with $`n := 1`$.
Of its four hypotheses $`1 \lt \lvert M\rvert`$, $`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$,
$`\mathrm{hasParent}(M, i_1, j_1)`$ and $`1 \le n`$, the first three are hypotheses of the present theorem
and the last is $`1 \le 1`$. This yields $`G, v_0, w_0, R, d_0, \ell`$.
Among the statements obtained, (1), (3) and (4) are exactly (1), (3) and (4) above, and the remaining ones are

```math
\begin{aligned}
&(5')\ \bigl(d_0 = 0 \wedge i_1 = 0\bigr) \ \vee\
        \bigl(0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0
              \wedge \lvert G\rvert \to^M_1 j_1\bigr), \cr
&(6)\ \lvert G\rvert \to^M_{i_1} j_1
\end{aligned}
```

($`\to^M_i`$ [D.nextR](Pss.md#d-nextR)).

**Step 2: identifying the positions.**
By (1) and associativity of concatenation, $`M = G \mathbin{+\!\!+} \bigl(B \mathbin{+\!\!+} (\ell)\bigr)`$.
Hence

```math
\lvert M\rvert = \lvert G\rvert + \bigl(\lvert R\rvert + 2\bigr)
```

using $`\lvert B\rvert = \lvert R\rvert + 1`$. We show the following two facts.

- $`M\langle \lvert G\rvert\rangle = (v_0,w_0)`$.
  Applying [T.getD_append_right'](#t-getD_append_right') with left sequence $`G`$, right sequence
  $`B \mathbin{+\!\!+} (\ell)`$ and index $`0`$ gives
  $`M\langle \lvert G\rvert + 0\rangle = \bigl(B \mathbin{+\!\!+} (\ell)\bigr)\langle 0\rangle`$, and
  the first element of $`B \mathbin{+\!\!+} (\ell)`$ is $`(v_0,w_0)`$.

- $`\ell = M\langle j_1\rangle`$.
  Reading (1) as $`M = \bigl(G \mathbin{+\!\!+} B\bigr) \mathbin{+\!\!+} (\ell)`$ and applying
  [T.getD_last_of_snoc](#t-getD_last_of_snoc) with $`D := G \mathbin{+\!\!+} B`$ gives
  $`M\langle \lvert M\rvert - 1\rangle = \ell`$, that is, $`M\langle j_1\rangle = \ell`$.

**Step 3: deriving (5) from $`(5')`$.**
Distinguish cases according to the disjunction in $`(5')`$.

**(a) The case $`d_0 = 0 \wedge i_1 = 0`$.**
First we show $`\ell_2 = 0`$. The definition of $`\mathrm{idx}_1`$ (D.idx1) is $`1`$ when $`0 \lt M_{1,j_1}`$
and $`0`$ when $`M_{1,j_1} = 0`$. Here $`i_1 = 0`$ and $`1 \ne 0`$, so the first case is not the one selected.
Hence $`M_{1,j_1} = 0`$, and by [T.entry_one](#t-entry_one) together with $`\ell = M\langle j_1\rangle`$
from Step 2, $`\ell_2 = \pi_2(M\langle j_1\rangle) = M_{1,j_1} = 0`$.

Next we show $`\ell_1 = v_0 + 1`$. We prepare the following five facts.

1. $`\lvert G\rvert \to^M_0 j_1`$. Substitute $`i_1 = 0`$ into (6) and use
   [T.nextR_zero_iff](Column-4.md#t-nextR_zero_iff).
2. $`j_1 = \lvert G\rvert + 1 + \lvert R\rvert`$. From the length identity in Step 2 and $`j_1 = \lvert M\rvert - 1`$.
3. $`M_{0,\lvert G\rvert + 1} \le M_{0,\lvert G\rvert} + 1`$.
   Apply [T.steps1_iff](Seqlex.md#t-steps1_iff) to $`\mathrm{steps}_1(M)`$ with $`j := \lvert G\rvert`$
   (its antecedent $`\lvert G\rvert + 1 \lt \lvert M\rvert`$ follows from the length identity in Step 2).
   This is the resulting inequality rewritten with [T.entry_zero](#t-entry_zero).
4. $`M_{0,\lvert G\rvert} = v_0`$. From [T.entry_zero](#t-entry_zero) and
   $`M\langle \lvert G\rvert\rangle = (v_0,w_0)`$ in Step 2.
5. $`\ell_1 = M_{0,j_1}`$. From [T.entry_zero](#t-entry_zero) and $`\ell = M\langle j_1\rangle`$ in Step 2.

We further show $`M_{0,j_1} \le M_{0,\lvert G\rvert + 1}`$. By 2 we have $`\lvert G\rvert + 1 \le j_1`$, so
either $`\lvert G\rvert + 1 = j_1`$ or $`\lvert G\rvert + 1 \lt j_1`$. In the former case the two sides are identical.
In the latter case, apply the fifth condition of the definition of $`\to^M_0`$ (D.nextrel0) in 1 with
$`j := \lvert G\rvert + 1`$
(its antecedent consists of $`\lvert G\rvert \lt \lvert G\rvert + 1`$ and $`\lvert G\rvert + 1 \lt j_1`$).

Putting all of this together,

```math
\ell_1 = M_{0,j_1} \le M_{0,\lvert G\rvert + 1} \le M_{0,\lvert G\rvert} + 1 = v_0 + 1
```

On the other hand (4) gives $`v_0 \lt \ell_1`$, that is, $`v_0 + 1 \le \ell_1`$, whence
$`\ell_1 = v_0 + 1`$. Thus the first disjunct of (5) holds.

**(b) The case $`0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0 \wedge \lvert G\rvert \to^M_1 j_1`$.**
Applying [T.nextrel1_snd_succ](#t-nextrel1_snd_succ) to $`\mathrm{r1ok}(M)`$ and
$`\lvert G\rvert \to^M_1 j_1`$ gives $`M_{1,j_1} = M_{1,\lvert G\rvert} + 1`$.
Rewriting both sides with [T.entry_one](#t-entry_one) and substituting $`M\langle j_1\rangle = \ell`$ and
$`M\langle \lvert G\rvert\rangle = (v_0,w_0)`$ from Step 2 gives $`\ell_2 = w_0 + 1`$.
Since $`0 \lt d_0`$, $`\ell_1 = v_0 + d_0`$ and $`\lvert G\rvert \to^M_1 j_1`$ are unchanged,
the second disjunct of (5) holds.

**Step 4: (2) — the decomposition does not depend on $`n`$.**
Take $`n`$ with $`1 \le n`$. Applying [T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks)
with this $`n`$ yields $`G', v_0', w_0', R', d_0', \ell'`$ and its statements $`(1_n)`$–$`(6_n)`$.
Put $`B' := (v_0',w_0') :: R'`$.

**(i) $`\lvert G'\rvert = \lvert G\rvert`$.**
$`(6_n)`$ reads $`\lvert G'\rvert \to^M_{i_1} j_1`$ and (6) reads $`\lvert G\rvert \to^M_{i_1} j_1`$.
The definition of $`\mathrm{hasParent}(M, i_1, j_1)`$ (D.hasParent) is the unique existence of
$`j_0`$ with $`j_0 \to^M_{i_1} j_1`$, hence $`\lvert G'\rvert = \lvert G\rvert`$.

**(ii) $`G' = G`$, $`v_0' = v_0`$, $`w_0' = w_0`$, $`R' = R`$, $`\ell' = \ell`$.**
From $`(1_n)`$ and (1),

```math
\bigl(G' \mathbin{+\!\!+} B'\bigr) \mathbin{+\!\!+} (\ell') = M = \bigl(G \mathbin{+\!\!+} B\bigr) \mathbin{+\!\!+} (\ell)
```

The two trailing sequences $`(\ell')`$ and $`(\ell)`$ have the same length $`1`$, so comparing
the last $`1`$ element of each side gives $`(\ell') = (\ell)`$, that is, $`\ell' = \ell`$, and
what remains gives $`G' \mathbin{+\!\!+} B' = G \mathbin{+\!\!+} B`$. Since moreover $`\lvert G'\rvert = \lvert G\rvert`$,
comparing the first $`\lvert G\rvert`$ elements of each side gives $`G' = G`$ and $`B' = B`$.
Now $`B' = B`$ reads $`(v_0',w_0') :: R' = (v_0,w_0) :: R`$, so comparing the heads gives
$`v_0' = v_0`$ and $`w_0' = w_0`$, and comparing the tails gives $`R' = R`$.

**(iii) $`d_0' = d_0`$.**
First we prove the following auxiliary claim: for every $`e`$, if $`e \to^M_1 j_1`$ then $`i_1 \ne 0`$.
Indeed, the fourth condition of the definition of $`\to^M_1`$ (D.nextrel1) gives $`M_{1,e} \lt M_{1,j_1}`$,
hence $`0 \lt M_{1,j_1}`$, so the first case of the definition of $`\mathrm{idx}_1`$ (D.idx1) is selected and
$`i_1 = 1 \ne 0`$.

We exhaust the four combinations of the disjunctions in $`(5')`$ and $`(5'_n)`$.

- Both are the first disjunct. Then $`d_0 = 0`$ and $`d_0' = 0`$, hence $`d_0' = d_0`$.
- $`(5')`$ is the first disjunct and $`(5'_n)`$ the second. The former gives $`i_1 = 0`$ and the latter
  $`\lvert G'\rvert \to^M_1 j_1`$; applying the auxiliary claim with $`e := \lvert G'\rvert`$ gives
  $`i_1 \ne 0`$, a contradiction. Hence this case does not occur.
- $`(5')`$ is the second disjunct and $`(5'_n)`$ the first. The latter gives $`i_1 = 0`$ and the former
  $`\lvert G\rvert \to^M_1 j_1`$; applying the auxiliary claim with $`e := \lvert G\rvert`$ gives
  $`i_1 \ne 0`$, a contradiction. Hence this case does not occur.
- Both are the second disjunct. Then $`\ell_1 = v_0 + d_0`$ and $`\ell'_1 = v_0' + d_0'`$, and since
  $`\ell' = \ell`$ and $`v_0' = v_0`$, we get $`v_0 + d_0 = v_0 + d_0'`$, that is, $`d_0' = d_0`$.

Consequently $`G'`$, $`B'`$ and $`d_0'`$ on the right-hand side of $`(2_n)`$ may all be rewritten as
$`G`$, $`B`$ and $`d_0`$. Thus $`(2_n)`$ reads

```math
M[n] = G \mathbin{+\!\!+} B^{+0\cdot d_0} \mathbin{+\!\!+} B^{+1\cdot d_0}
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}
```

where $`L^{+e}`$ [D.shiftr0](Cnf-2.md#d-shiftr0) is the sequence obtained from $`L`$ by adding $`e`$ to
the first entry of each pair, and the part $`B^{+0\cdot d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}`$
of the right-hand side is exactly the definition of $`\mathrm{cp}`$ (D.copies), hence equals
$`\mathrm{cp}_{d_0}(B, n)`$. This gives (2). ∎
