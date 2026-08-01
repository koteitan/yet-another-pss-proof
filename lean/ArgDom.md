[← README](README.md) | [English](ArgDom.md) | [Japanese](ArgDom-ja.md) | ArgDom **1** [2](ArgDom-2.md) [3](ArgDom-3.md) [4](ArgDom-4.md) [5](ArgDom-5.md)

<a id="t-seqlex_of_sle_not_prefix"></a>
## Theorem: strict comparison when one side is not a prefix (T.seqlex_of_sle_not_prefix)

### Theorem

Let $`W, X, Y \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)).
If $`X \preceq_{\mathrm{lex}} W \mathbin{+\!\!+} Y`$ ([D.sle](Cofinality.md#d-sle)) and
$`X \ne W \mathbin{+\!\!+} X'`$ for every $`X' \in \mathrm{PairSeq}`$, then
$`X \prec_{\mathrm{lex}} W \mathbin{+\!\!+} Y'`$ ([D.seqlex](Seqlex.md#d-seqlex))
for every $`Y' \in \mathrm{PairSeq}`$.

### Proof

Induction on the length of $`W`$ (with $`X`$, $`Y`$, $`Y'`$ left universally quantified). Show

```math
\Phi(W) :\equiv \forall X, Y \in \mathrm{PairSeq},\
  X \preceq_{\mathrm{lex}} W \mathbin{+\!\!+} Y
  \ \to\ \bigl(\forall X',\ X \ne W \mathbin{+\!\!+} X'\bigr)
  \ \to\ \forall Y',\ X \prec_{\mathrm{lex}} W \mathbin{+\!\!+} Y'
```

for every $`W`$.

- **Base case** $`W = ()`$: applying the second hypothesis with $`X' := X`$ yields
  $`X \ne () \mathbin{+\!\!+} X`$, that is $`X \ne X`$, which contradicts reflexivity of $`=`$.
  Hence the antecedent is false and $`\Phi(())`$ holds.

- **Inductive step** $`W = w :: W'`$: assume $`\Phi(W')`$.
  Take $`X`$, $`Y`$, assume $`X \preceq_{\mathrm{lex}} (w :: W') \mathbin{+\!\!+} Y`$ and
  $`\forall X',\ X \ne (w :: W') \mathbin{+\!\!+} X'`$, and take $`Y'`$.
  Distinguish cases on the shape of $`X`$.

  **(a) The case $`X = ()`$.**
  The sequence $`(w :: W') \mathbin{+\!\!+} Y' = w :: (W' \mathbin{+\!\!+} Y')`$ is not empty.
  By the first clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex),
  $`() \prec_{\mathrm{lex}} L`$ is the same proposition as $`L \ne ()`$ by definition, so the conclusion holds.

  **(b) The case $`X = x :: X''`$.**
  The hypothesis reads $`x :: X'' \preceq_{\mathrm{lex}} w :: (W' \mathbin{+\!\!+} Y)`$.
  By the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle) this splits into the case of equality
  and the case of $`\prec_{\mathrm{lex}}`$.

  In the case of equality, $`X = w :: (W' \mathbin{+\!\!+} Y) = (w :: W') \mathbin{+\!\!+} Y`$,
  which contradicts the second hypothesis applied with $`X' := Y`$.

  In the case $`x :: X'' \prec_{\mathrm{lex}} w :: (W' \mathbin{+\!\!+} Y)`$,
  the third clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex) gives one of the following.

  - The case $`x \prec_{\mathrm{p}} w`$ ([D.pairlt](Seqlex.md#d-pairlt)).
    What is to be shown is $`x :: X'' \prec_{\mathrm{lex}} w :: (W' \mathbin{+\!\!+} Y')`$,
    and the first disjunct on the right-hand side of the third clause of D.seqlex is exactly the present hypothesis.
  - The case $`x = w`$ and $`X'' \prec_{\mathrm{lex}} W' \mathbin{+\!\!+} Y`$.
    First, $`X'' \preceq_{\mathrm{lex}} W' \mathbin{+\!\!+} Y`$ (the second disjunct of D.sle).
    Next, $`X'' \ne W' \mathbin{+\!\!+} Z`$ for every $`Z`$. Indeed, if
    $`X'' = W' \mathbin{+\!\!+} Z`$, then $`x = w`$ gives
    $`X = x :: X'' = w :: (W' \mathbin{+\!\!+} Z) = (w :: W') \mathbin{+\!\!+} Z`$,
    which contradicts the second hypothesis applied with $`X' := Z`$.
    Hence the induction hypothesis $`\Phi(W')`$ applies with $`X := X''`$, $`Y := Y`$, $`Y' := Y'`$, and yields
    $`X'' \prec_{\mathrm{lex}} W' \mathbin{+\!\!+} Y'`$.
    Together with $`x = w`$, the second disjunct on the right-hand side of the third clause of D.seqlex holds. ∎

<a id="t-peel_aux"></a>
## Theorem: peeling off a self-referential upper bound (T.peel_aux)

### Theorem

Let $`d, w, n, a \in \mathbb{N}`$ and $`X, Q, A_2 \in \mathrm{PairSeq}`$.
If $`\lvert X\rvert \le n`$ and
$`X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} (a,w) :: (X \mathbin{+\!\!+} A_2)^{+d}`$ ([D.shiftr0](Cnf-2.md#d-shiftr0)),
then there exists $`m \in \mathbb{N}`$ such that
$`X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} \mathrm{copies}_d\bigl((a,w) :: Q^{+d},\ m\bigr)`$ ([D.copies](Cnf-2.md#d-copies)).

### Proof

Induction on the natural number $`n`$ (with $`X`$, $`Q`$, $`A_2`$, $`a`$ left universally quantified).
Show

```math
\begin{aligned}
&\Psi(n) :\equiv \forall X, Q, A_2 \in \mathrm{PairSeq},\ \forall a \in \mathbb{N},\
  \lvert X\rvert \le n \cr
&\qquad \ \to\ X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} (a,w) :: (X \mathbin{+\!\!+} A_2)^{+d} \cr
&\qquad \ \to\ \exists m,\ X \preceq_{\mathrm{lex}}
  Q \mathbin{+\!\!+} \mathrm{copies}_d\bigl((a,w) :: Q^{+d},\ m\bigr)
\end{aligned}
```

for every $`n`$.

- **Base case** $`n = 0`$: from $`\lvert X\rvert \le 0`$ we get $`X = ()`$.
  Take $`m := 0`$; by the definition of $`\mathrm{copies}`$ (D.copies) we have
  $`\mathrm{copies}_d(B, 0) = ()`$, so what is to be shown is
  $`() \preceq_{\mathrm{lex}} Q`$. If $`Q = ()`$ then
  $`() = Q`$ and the first disjunct of D.sle holds. If $`Q = q :: Q'`$ then
  $`Q \ne ()`$, so the first clause of D.seqlex gives $`() \prec_{\mathrm{lex}} Q`$,
  that is, the second disjunct of D.sle holds.

- **Inductive step** $`n \to n+1`$: assume $`\Psi(n)`$.
  Take $`X`$, $`Q`$, $`A_2`$, $`a`$ and assume $`\lvert X\rvert \le n+1`$ and
  $`X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} (a,w) :: (X \mathbin{+\!\!+} A_2)^{+d}`$.
  Distinguish cases according to whether $`X`$ has $`Q \mathbin{+\!\!+} ((a,w))`$ as a prefix
  (below, $`(x)`$ denotes the sequence of length $`1`$ consisting of the single element $`x`$).

**(a) The case $`X = Q \mathbin{+\!\!+} (a,w) :: X'`$ for some $`X'`$.**
Rewriting $`X`$ in the hypothesis into this shape gives

```math
Q \mathbin{+\!\!+} (a,w) :: X'
  \ \preceq_{\mathrm{lex}}\
Q \mathbin{+\!\!+} (a,w) :: \bigl((Q \mathbin{+\!\!+} (a,w) :: X') \mathbin{+\!\!+} A_2\bigr)^{+d}
```

Applying [T.sle_append_cancel](Cofinality.md#t-sle_append_cancel) first with $`Q`$
and then with $`((a,w))`$ yields

```math
X' \preceq_{\mathrm{lex}} \bigl((Q \mathbin{+\!\!+} (a,w) :: X') \mathbin{+\!\!+} A_2\bigr)^{+d}
```

Here associativity gives
$`(Q \mathbin{+\!\!+} (a,w) :: X') \mathbin{+\!\!+} A_2 = Q \mathbin{+\!\!+} (a,w) :: (X' \mathbin{+\!\!+} A_2)`$,
so by [T.shiftr0_append](Cofinality-3.md#t-shiftr0_append) and
[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons)

```math
\bigl((Q \mathbin{+\!\!+} (a,w) :: X') \mathbin{+\!\!+} A_2\bigr)^{+d}
  = Q^{+d} \mathbin{+\!\!+} (a+d,\ w) :: (X' \mathbin{+\!\!+} A_2)^{+d}
```

and therefore

```math
X' \preceq_{\mathrm{lex}} Q^{+d} \mathbin{+\!\!+} (a+d,\ w) :: (X' \mathbin{+\!\!+} A_2)^{+d} .
```

Moreover $`\lvert X\rvert = \lvert Q\rvert + 1 + \lvert X'\rvert \le n+1`$ gives
$`\lvert X'\rvert \le n`$. Hence the induction hypothesis $`\Psi(n)`$ applies with
$`X := X'`$, $`Q := Q^{+d}`$, $`A_2 := A_2`$, $`a := a+d`$, and for some $`m`$

```math
X' \preceq_{\mathrm{lex}} Q^{+d} \mathbin{+\!\!+}
  \mathrm{copies}_d\bigl((a+d,\ w) :: (Q^{+d})^{+d},\ m\bigr)
```

holds. Take $`m+1`$ as the required $`m`$.
By [T.copies_succ_front](Cnf-3.md#t-copies_succ_front)

```math
\mathrm{copies}_d\bigl((a,w) :: Q^{+d},\ m+1\bigr)
  = \bigl((a,w) :: Q^{+d}\bigr) \mathbin{+\!\!+}
    \Bigl(\mathrm{copies}_d\bigl((a,w) :: Q^{+d},\ m\bigr)\Bigr)^{+d}
```

and by [T.shiftr0_copies](Cofinality-2.md#t-shiftr0_copies) and [T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons)

```math
\Bigl(\mathrm{copies}_d\bigl((a,w) :: Q^{+d},\ m\bigr)\Bigr)^{+d}
  = \mathrm{copies}_d\bigl((a+d,\ w) :: (Q^{+d})^{+d},\ m\bigr)
```

Hence associativity gives

```math
\begin{aligned}
&Q \mathbin{+\!\!+} \mathrm{copies}_d\bigl((a,w) :: Q^{+d},\ m+1\bigr) \cr
&\qquad = \bigl(Q \mathbin{+\!\!+} ((a,w))\bigr) \mathbin{+\!\!+}
    \Bigl(Q^{+d} \mathbin{+\!\!+}
      \mathrm{copies}_d\bigl((a+d,\ w) :: (Q^{+d})^{+d},\ m\bigr)\Bigr)
\end{aligned}
```

and moreover $`X = Q \mathbin{+\!\!+} (a,w) :: X' = (Q \mathbin{+\!\!+} ((a,w))) \mathbin{+\!\!+} X'`$.
Both sides carry the common prefix $`Q \mathbin{+\!\!+} ((a,w))`$, so using
[T.sle_append_cancel](Cofinality.md#t-sle_append_cancel) in the reverse direction,
the required comparison follows from the comparison for $`X'`$ obtained above.

**(b) The case $`X \ne Q \mathbin{+\!\!+} (a,w) :: X'`$ for every $`X'`$.**
Take $`m := 1`$. By [T.copies_one](Cnf-3.md#t-copies_one) we have
$`\mathrm{copies}_d(B, 1) = B`$, so what is to be shown is

```math
X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} \bigl((a,w) :: Q^{+d}\bigr)
  = \bigl(Q \mathbin{+\!\!+} ((a,w))\bigr) \mathbin{+\!\!+} Q^{+d}
```

Regrouping the hypothesis by associativity as well gives

```math
X \preceq_{\mathrm{lex}} \bigl(Q \mathbin{+\!\!+} ((a,w))\bigr) \mathbin{+\!\!+} (X \mathbin{+\!\!+} A_2)^{+d}
```

and the case hypothesis is equivalent to: for every $`X'`$,
$`X \ne (Q \mathbin{+\!\!+} ((a,w))) \mathbin{+\!\!+} X'`$
(because $`(Q \mathbin{+\!\!+} ((a,w))) \mathbin{+\!\!+} X' = Q \mathbin{+\!\!+} (a,w) :: X'`$).
Hence applying [T.seqlex_of_sle_not_prefix](#t-seqlex_of_sle_not_prefix) with
$`W := Q \mathbin{+\!\!+} ((a,w))`$, $`Y := (X \mathbin{+\!\!+} A_2)^{+d}`$ and
$`Y' := Q^{+d}`$ yields
$`X \prec_{\mathrm{lex}} (Q \mathbin{+\!\!+} ((a,w))) \mathbin{+\!\!+} Q^{+d}`$.
By the second disjunct of D.sle this is the required comparison. ∎

<a id="t-sle_take_of_short"></a>
## Theorem: the shorter side is decided by the front part (T.sle_take_of_short)

### Theorem

Let $`P, X, Y \in \mathrm{PairSeq}`$. If $`X \preceq_{\mathrm{lex}} P \mathbin{+\!\!+} Y`$ and
$`\lvert X\rvert \le \lvert P\rvert`$, then $`X \preceq_{\mathrm{lex}} P`$.

### Proof

Induction on the length of $`P`$ (with $`X`$, $`Y`$ left universally quantified). Show

```math
\Xi(P) :\equiv \forall X, Y \in \mathrm{PairSeq},\
  X \preceq_{\mathrm{lex}} P \mathbin{+\!\!+} Y \to \lvert X\rvert \le \lvert P\rvert
  \to X \preceq_{\mathrm{lex}} P
```

for every $`P`$.

- **Base case** $`P = ()`$: from $`\lvert X\rvert \le 0`$ we get $`X = ()`$, hence
  $`X = P`$ and the first disjunct of D.sle holds.

- **Inductive step** $`P = p :: P'`$: assume $`\Xi(P')`$.
  Take $`X`$, $`Y`$ and assume $`X \preceq_{\mathrm{lex}} p :: (P' \mathbin{+\!\!+} Y)`$ and
  $`\lvert X\rvert \le \lvert P'\rvert + 1`$. Distinguish cases on the shape of $`X`$.

  **(a) The case $`X = ()`$.** The sequence $`p :: P'`$ is not empty, so the first clause of D.seqlex gives
  $`() \prec_{\mathrm{lex}} p :: P'`$, and the second disjunct of D.sle holds.

  **(b) The case $`X = x :: X''`$.** The length hypothesis reads $`\lvert X''\rvert \le \lvert P'\rvert`$.
  By the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle) this splits into the case of equality
  and the case of $`\prec_{\mathrm{lex}}`$.

  In the case of equality $`x :: X'' = p :: (P' \mathbin{+\!\!+} Y)`$, comparing the head and the tail
  of the pair sequences yields $`x = p`$ and $`X'' = P' \mathbin{+\!\!+} Y`$.
  Taking lengths gives $`\lvert X''\rvert = \lvert P'\rvert + \lvert Y\rvert`$, which together with
  $`\lvert X''\rvert \le \lvert P'\rvert`$ forces $`\lvert Y\rvert = 0`$, that is $`Y = ()`$.
  Hence $`X'' = P'`$, so $`X = p :: P' = P`$, and the first disjunct of D.sle holds.

  In the case $`x :: X'' \prec_{\mathrm{lex}} p :: (P' \mathbin{+\!\!+} Y)`$, the third clause of D.seqlex
  gives one of the following.

  - The case $`x \prec_{\mathrm{p}} p`$. By the first disjunct on the right-hand side of the third clause of D.seqlex,
    $`x :: X'' \prec_{\mathrm{lex}} p :: P'`$, and the second disjunct of D.sle holds.
  - The case $`x = p`$ and $`X'' \prec_{\mathrm{lex}} P' \mathbin{+\!\!+} Y`$.
    By the second disjunct of D.sle we have $`X'' \preceq_{\mathrm{lex}} P' \mathbin{+\!\!+} Y`$, and
    $`\lvert X''\rvert \le \lvert P'\rvert`$, so the induction hypothesis $`\Xi(P')`$ applies and yields
    $`X'' \preceq_{\mathrm{lex}} P'`$. This splits further into two cases.
    If $`X'' = P'`$ then $`X = p :: P' = P`$ and the first disjunct of D.sle holds.
    If $`X'' \prec_{\mathrm{lex}} P'`$ then, together with $`x = p`$, the second disjunct on the
    right-hand side of the third clause of D.seqlex gives $`x :: X'' \prec_{\mathrm{lex}} p :: P'`$,
    and the second disjunct of D.sle holds. ∎

<a id="t-sle_trans"></a>
## Theorem: transitivity of the non-strict comparison (T.sle_trans)

### Theorem

If $`A \preceq_{\mathrm{lex}} B`$ and $`B \preceq_{\mathrm{lex}} C`$, then $`A \preceq_{\mathrm{lex}} C`$.

### Proof

By the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle), $`A \preceq_{\mathrm{lex}} B`$ means
$`A = B`$ or $`A \prec_{\mathrm{lex}} B`$.

- The case $`A = B`$. Rewriting $`B`$ as $`A`$ turns the second hypothesis into the conclusion itself.
- The case $`A \prec_{\mathrm{lex}} B`$.
  Applying [T.seqlex_sle_trans](Cofinality.md#t-seqlex_sle_trans) to
  $`A \prec_{\mathrm{lex}} B`$ and $`B \preceq_{\mathrm{lex}} C`$ yields
  $`A \prec_{\mathrm{lex}} C`$. By the second disjunct of D.sle this is the conclusion. ∎

<a id="t-sle_of_append_left"></a>
## Theorem: truncating the smaller side on the right (T.sle_of_append_left)

### Theorem

If $`X \mathbin{+\!\!+} Y \preceq_{\mathrm{lex}} W`$, then $`X \preceq_{\mathrm{lex}} W`$.

### Proof

First we show $`X \preceq_{\mathrm{lex}} X \mathbin{+\!\!+} Y`$. Distinguish cases on the shape of $`Y`$.

- The case $`Y = ()`$. Then $`X \mathbin{+\!\!+} () = X`$, so the first disjunct of D.sle holds.
- The case $`Y = y :: Y'`$. Then $`Y \ne ()`$, so
  [T.seqlex_prefix](Seqlex.md#t-seqlex_prefix) gives
  $`X \prec_{\mathrm{lex}} X \mathbin{+\!\!+} Y`$, and the second disjunct of D.sle holds.

It remains to apply [T.sle_trans](#t-sle_trans) to the resulting
$`X \preceq_{\mathrm{lex}} X \mathbin{+\!\!+} Y`$ and the hypothesis
$`X \mathbin{+\!\!+} Y \preceq_{\mathrm{lex}} W`$. ∎

<a id="t-shiftr0_injective"></a>
## Theorem: the right shift of row 0 is injective (T.shiftr0_injective)

### Theorem

Let $`d \in \mathbb{N}`$. If $`X^{+d} = Y^{+d}`$, then $`X = Y`$.

### Proof

Below we write $`p_1`$ for the first entry and $`p_2`$ for the second entry of a pair $`p \in \mathbb{N} \times \mathbb{N}`$.

We show that the map $`f : p \mapsto (p_1 + d,\ p_2)`$ is injective. Suppose $`f(p) = f(q)`$; comparing
the entries of the pairs gives $`p_1 + d = q_1 + d`$ and $`p_2 = q_2`$.
The former yields $`p_1 = q_1`$, hence $`p = q`$.

The definition of $`(\cdot)^{+d}`$ (D.shiftr0) is the application of $`f`$ to each element, and
applying an injective map to each element of a sequence is injective on sequences. That is,
$`X^{+d} = Y^{+d}`$ implies $`X = Y`$. ∎

<a id="t-seqlex_shiftr0"></a>
## Theorem: the right shift of row 0 preserves the strict comparison (T.seqlex_shiftr0)

### Theorem

Let $`d \in \mathbb{N}`$. For all $`X, Y \in \mathrm{PairSeq}`$,

```math
X^{+d} \prec_{\mathrm{lex}} Y^{+d} \iff X \prec_{\mathrm{lex}} Y .
```

### Proof

Induction on the length of $`X`$ (with $`Y`$ left universally quantified). Show

```math
\Theta(X) :\equiv \forall Y \in \mathrm{PairSeq},\
  \bigl(X^{+d} \prec_{\mathrm{lex}} Y^{+d} \iff X \prec_{\mathrm{lex}} Y\bigr)
```

for every $`X`$.

- **Base case** $`X = ()`$: here $`()^{+d} = ()`$. Distinguish cases on the shape of $`Y`$.
  If $`Y = ()`$ then $`Y^{+d} = ()`$, and by the first clause of D.seqlex
  both sides read $`() \ne ()`$, so both are false.
  If $`Y = y :: Y'`$ then $`Y^{+d} = (y_1+d,\ y_2) :: Y'^{+d}`$, and by
  the first clause of D.seqlex both sides are conditions on sequences that are not empty, so both are true.

- **Inductive step** $`X = x :: X'`$: assume $`\Theta(X')`$. Distinguish cases on the shape of $`Y`$.

  **(a) The case $`Y = ()`$.** Here $`Y^{+d} = ()`$ and
  $`X^{+d} = (x_1+d,\ x_2) :: X'^{+d}`$, so by
  the second clause of D.seqlex both sides are false.

  **(b) The case $`Y = y :: Y'`$.** By [T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons)

```math
X^{+d} = (x_1+d,\ x_2) :: X'^{+d}, \qquad
Y^{+d} = (y_1+d,\ y_2) :: Y'^{+d}
```

  Applying the third clause of D.seqlex to both sides, what is to be shown is

```math
\begin{aligned}
&\Bigl((x_1+d,\ x_2) \prec_{\mathrm{p}} (y_1+d,\ y_2) \cr
&\qquad \ \vee\ \bigl((x_1+d,\ x_2) = (y_1+d,\ y_2)
  \wedge X'^{+d} \prec_{\mathrm{lex}} Y'^{+d}\bigr)\Bigr) \cr
&\qquad \iff
\Bigl(x \prec_{\mathrm{p}} y \ \vee\ (x = y \wedge X' \prec_{\mathrm{lex}} Y')\Bigr)
\end{aligned}
```

  Applying the induction hypothesis $`\Theta(X')`$ with $`Y := Y'`$ gives
  $`X'^{+d} \prec_{\mathrm{lex}} Y'^{+d} \iff X' \prec_{\mathrm{lex}} Y'`$,
  so two points remain.

  First, by the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt)

```math
(x_1+d,\ x_2) \prec_{\mathrm{p}} (y_1+d,\ y_2)
  \iff x_1 + d \lt y_1 + d \ \vee\ (x_1 + d = y_1 + d \wedge x_2 \lt y_2)
```

  and since $`x_1 + d \lt y_1 + d \iff x_1 \lt y_1`$ and
  $`x_1 + d = y_1 + d \iff x_1 = y_1`$, the right-hand side is equivalent to
  $`x_1 \lt y_1 \vee (x_1 = y_1 \wedge x_2 \lt y_2)`$, that is, to $`x \prec_{\mathrm{p}} y`$.

  Second, $`(x_1+d,\ x_2) = (y_1+d,\ y_2)`$ is equivalent to
  $`x_1 + d = y_1 + d`$ and $`x_2 = y_2`$, and since
  $`x_1 + d = y_1 + d \iff x_1 = y_1`$ it is equivalent to $`x = y`$.

  Thus the two disjuncts on either side correspond, and the equivalence holds. ∎

<a id="t-sle_shiftr0"></a>
## Theorem: the right shift of row 0 preserves the non-strict comparison (T.sle_shiftr0)

### Theorem

Let $`d \in \mathbb{N}`$. For all $`X, Y \in \mathrm{PairSeq}`$,

```math
X^{+d} \preceq_{\mathrm{lex}} Y^{+d} \iff X \preceq_{\mathrm{lex}} Y .
```

### Proof

By the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle), what is to be shown is

```math
\bigl(X^{+d} = Y^{+d} \vee X^{+d} \prec_{\mathrm{lex}} Y^{+d}\bigr)
\iff \bigl(X = Y \vee X \prec_{\mathrm{lex}} Y\bigr)
```

The second disjuncts are equivalent by [T.seqlex_shiftr0](#t-seqlex_shiftr0), so it suffices to see
that the first disjuncts correspond.

- From left to right: if $`X^{+d} = Y^{+d}`$ then
  [T.shiftr0_injective](#t-shiftr0_injective) gives $`X = Y`$.
- From right to left: if $`X = Y`$, applying $`(\cdot)^{+d}`$ to both sides gives
  $`X^{+d} = Y^{+d}`$. ∎

<a id="d-SpineOK"></a>
## Definition: lower bound on row 1 of the right-visible columns (D.SpineOK)

For $`A \in \mathrm{PairSeq}`$ and $`L, w \in \mathbb{N}`$,

```math
\begin{aligned}
&\mathrm{SpineOK}(A, L, w) :\iff
\forall U, V \in \mathrm{PairSeq},\ \forall x \in \mathbb{N} \times \mathbb{N},\ \cr
&\qquad \Bigl(A = U \mathbin{+\!\!+} x :: V \ \wedge\ x_1 \lt L
  \ \wedge\ \bigl(\forall y \in V,\ x_1 \lt y_1\bigr)\Bigr) \cr
&\qquad \ \longrightarrow\ w \le x_2 .
\end{aligned}
```

That is, the condition says that every column $`x`$ of $`A`$ whose row-0 value is smaller than $`L`$ and
such that every column of $`A`$ situated after $`x`$ has row-0 value greater than $`x_1`$
(such an $`x`$ is called **right-visible**) has row-1 value at least $`w`$.

<a id="d-ArgDomCore"></a>
## Definition: the core of argument domination (D.ArgDomCore)

Below, for $`L \in \mathrm{PairSeq}`$ let $`\mathrm{head}\,L`$ denote the first element of $`L`$
(with $`\mathrm{head}\,L := (0,0)`$ when $`L = ()`$).

The proposition $`\mathrm{ArgDomCore}`$ is defined as follows. It is the proposition that for all
$`X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$ and $`u, w, e \in \mathbb{N}`$,
if the following 8 conditions all hold then the conclusion (9) holds.

1. $`\bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z \in \mathrm{ST\_PS}`$ ([D.ST_PS](Pss.md#d-ST_PS))
2. $`0 \lt e`$
3. $`\forall x \in A_1,\ u \lt x_1`$
4. $`\forall x \in B,\ u + e \lt x_1`$
5. $`\forall x \in A_2,\ u \lt x_1`$
6. $`A_2 = () \ \vee\ (\mathrm{head}\,A_2)_1 \le u + e`$
7. $`Z = () \ \vee\ (\mathrm{head}\,Z)_1 \le u`$
8. $`\mathrm{SpineOK}(A_1,\ u+e,\ w)`$
9. $`B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}`$

<a id="t-spineOK_of_nextrel1"></a>
## Theorem: SpineOK from the row-1 parent relation (T.spineOK_of_nextrel1)

### Theorem

Let $`G, R \in \mathrm{PairSeq}`$ and $`v_0, w_0, d_0 \in \mathbb{N}`$, and put

```math
\ell := (v_0 + d_0,\ w_0 + 1), \qquad
M := \bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} (\ell), \qquad
j := \bigl\lvert G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr\rvert
```

If $`\lvert G\rvert \to^M_1 j`$ ([D.nextrel1](Pss.md#d-nextrel1)), then
$`\mathrm{SpineOK}(R,\ v_0 + d_0,\ w_0)`$.

### Proof

Of the 6 conditions in the definition of $`\to^M_1`$ (D.nextrel1), we use condition (5)

```math
\lvert G\rvert \le^M_0 j
```

and condition (6)

```math
\forall j'\ \bigl(\lvert G\rvert \lt j' \ \wedge\ j' \le^M_0 j \ \to\ M_{1,j} \le M_{1,j'}\bigr)
```

($`\le^M_0`$ [D.le0](Pss.md#d-le0), $`M_{i,j}`$ [D.entry](Pss.md#d-entry)).

Following the definition of $`\mathrm{SpineOK}`$ (D.SpineOK), take $`U, V \in \mathrm{PairSeq}`$ and
$`x \in \mathbb{N}\times\mathbb{N}`$, assume

```math
R = U \mathbin{+\!\!+} x :: V, \qquad x_1 \lt v_0 + d_0, \qquad \forall y \in V,\ x_1 \lt y_1
```

and show $`w_0 \le x_2`$. Put $`A := G \mathbin{+\!\!+} ((v_0,w_0) :: U)`$; substituting the
decomposition of $`R`$ gives

```math
M = A \mathbin{+\!\!+} \bigl(x :: (V \mathbin{+\!\!+} (\ell))\bigr), \qquad
\lvert A\rvert = \lvert G\rvert + 1 + \lvert U\rvert, \qquad
j = \lvert A\rvert + 1 + \lvert V\rvert
```

Applying [T.getD_append_right'](Cofinality.md#t-getD_append_right') to
$`A`$ and $`x :: (V \mathbin{+\!\!+} (\ell))`$ with index $`0`$ gives

```math
M\langle \lvert A\rvert \rangle = x
```

and applying the same lemma with index $`t+1`$ gives

```math
M\bigl\langle \lvert A\rvert + (t+1) \bigr\rangle = (V \mathbin{+\!\!+} (\ell))\langle t \rangle
```

Moreover $`j = \lvert G \mathbin{+\!\!+} ((v_0,w_0) :: R)\rvert`$ is the position of $`\ell`$ in $`M`$, so
applying the same lemma to $`G \mathbin{+\!\!+} ((v_0,w_0) :: R)`$ and $`(\ell)`$ with index $`0`$ gives
$`M\langle j\rangle = \ell`$.

**An intermediate estimate on the row-0 values.** We show that for every $`y`$, if
$`\lvert A\rvert \lt y`$ and $`y \le j`$, then $`M_{0,\lvert A\rvert} \lt M_{0,y}`$.
From $`\lvert A\rvert \lt y`$ we may write $`y = \lvert A\rvert + (t+1)`$.
From $`y \le j = \lvert A\rvert + 1 + \lvert V\rvert`$ we get $`t \le \lvert V\rvert`$.
By [T.entry_zero](Cofinality.md#t-entry_zero) we have
$`M_{0,\lvert A\rvert} = x_1`$ and $`M_{0,y} = \bigl((V \mathbin{+\!\!+} (\ell))\langle t\rangle\bigr)_1`$.

- The case $`t \lt \lvert V\rvert`$. Then $`(V \mathbin{+\!\!+} (\ell))\langle t\rangle = V\langle t\rangle`$,
  which is an element of $`V`$. The hypothesis $`\forall y \in V,\ x_1 \lt y_1`$ gives
  $`x_1 \lt \bigl(V\langle t\rangle\bigr)_1`$.
- The case $`t = \lvert V\rvert`$. Then $`(V \mathbin{+\!\!+} (\ell))\langle \lvert V\rvert\rangle = \ell`$ and
  $`\ell_1 = v_0 + d_0`$, so the hypothesis $`x_1 \lt v_0 + d_0`$ gives $`x_1 \lt \ell_1`$.

**Lifting the row-0 ancestor relation.** We have $`\lvert G\rvert \lt \lvert A\rvert`$ and
$`\lvert A\rvert \le j`$, and the intermediate estimate just shown holds, so applying
[T.le0_through_pivot](Column-4.md#t-le0_through_pivot) to condition (5) yields

```math
\lvert A\rvert \le^M_0 j
```

**Conclusion from minimality on row 1.** By [T.entry_one](Cofinality.md#t-entry_one) and
$`M\langle j\rangle = \ell`$ we have $`M_{1,j} = \ell_2 = w_0 + 1`$, and from
$`M\langle \lvert A\rvert\rangle = x`$ we have $`M_{1,\lvert A\rvert} = x_2`$.
Applying condition (6) with $`j' := \lvert A\rvert`$, from
$`\lvert G\rvert \lt \lvert A\rvert`$ and $`\lvert A\rvert \le^M_0 j`$ we obtain

```math
w_0 + 1 = M_{1,j} \le M_{1,\lvert A\rvert} = x_2
```

In particular $`w_0 \le x_2`$. ∎

<a id="t-ascArgDom_of_core"></a>
## Theorem: from the core to ascending argument domination (T.ascArgDom_of_core)

### Theorem

If $`\mathrm{ArgDomCore}`$ holds, then
$`\mathrm{AscArgDom}`$ ([D.AscArgDom](Cofinality-3.md#d-AscArgDom)) holds.

### Proof

Below, for $`a \in \mathbb{N}`$ and $`L \in \mathrm{PairSeq}`$, let $`\mathrm{tw}_a L`$ be
the maximal prefix of $`L`$ along which, from the front on, every element has first entry greater than $`a`$,
and let $`\mathrm{dw}_a L`$ be the remaining sequence. That is,
$`\mathrm{tw}_a L \mathbin{+\!\!+} \mathrm{dw}_a L = L`$, every element $`x`$ of $`\mathrm{tw}_a L`$ satisfies
$`a \lt x_1`$, and if $`\mathrm{dw}_a L \ne ()`$ then
$`\neg\bigl(a \lt (\mathrm{head}(\mathrm{dw}_a L))_1\bigr)`$.

Following the definition of $`\mathrm{AscArgDom}`$ (D.AscArgDom), take
$`G, R, S \in \mathrm{PairSeq}`$ and $`v_0, w_0, d_0 \in \mathbb{N}`$, and assume the following.

```math
\bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr) \in \mathrm{ST\_PS},
```
```math
\bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS},
```
```math
\forall x \in R,\ v_0 \lt x_1, \qquad 0 \lt d_0, \qquad
\lvert G\rvert \to^{M}_1 \bigl\lvert G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr\rvert
```

Here $`M := (G \mathbin{+\!\!+} ((v_0,w_0) :: R)) \mathbin{+\!\!+} ((v_0+d_0,\ w_0+1))`$.
What is to be shown is that for some $`m`$

```math
\mathrm{tw}_{v_0+d_0} S \ \preceq_{\mathrm{lex}}\
  \Bigl(R \mathbin{+\!\!+} \mathrm{copies}_{d_0}\bigl(((v_0,w_0) :: R)^{+d_0},\ m\bigr)\Bigr)^{+d_0}
```

holds.

**Splitting the sequence.** Put $`S_{\mathrm{hi}} := \mathrm{tw}_{v_0+d_0} S`$,
$`D := \mathrm{dw}_{v_0+d_0} S`$, $`A_2 := \mathrm{tw}_{v_0} D`$, $`Z := \mathrm{dw}_{v_0} D`$.
By the definitions of $`\mathrm{tw}`$ and $`\mathrm{dw}`$ we have
$`S_{\mathrm{hi}} \mathbin{+\!\!+} D = S`$ and $`A_2 \mathbin{+\!\!+} Z = D`$.
Moreover the following five statements hold.

**(i) $`\forall x \in S_{\mathrm{hi}},\ v_0 + d_0 \lt x_1`$.**
This holds because the elements of $`\mathrm{tw}_{v_0+d_0} S`$ satisfy the predicate that the first entry
is greater than $`v_0+d_0`$.

**(ii) $`\forall x \in A_2,\ v_0 \lt x_1`$.**
This holds because the elements of $`\mathrm{tw}_{v_0} D`$ satisfy the predicate that the first entry
is greater than $`v_0`$.

**(iii) $`D = () \ \vee\ (\mathrm{head}\,D)_1 \le v_0 + d_0`$.**
If $`D = \mathrm{dw}_{v_0+d_0} S`$ is not empty, its first element is the first element failing the predicate,
so $`\neg(v_0 + d_0 \lt (\mathrm{head}\,D)_1)`$, that is $`(\mathrm{head}\,D)_1 \le v_0 + d_0`$.

**(iv) $`A_2 = () \ \vee\ (\mathrm{head}\,A_2)_1 \le v_0 + d_0`$.**
Suppose $`A_2 \ne ()`$. Since $`A_2 = \mathrm{tw}_{v_0} D`$ is not empty, $`D \ne ()`$, and since
$`\mathrm{tw}_{v_0} D`$ is a non-empty prefix taken from the front of $`D`$, we have
$`\mathrm{head}\,A_2 = \mathrm{head}\,D`$. The first disjunct of (iii) is false because $`D \ne ()`$, so
the second disjunct holds and $`(\mathrm{head}\,A_2)_1 = (\mathrm{head}\,D)_1 \le v_0 + d_0`$.

**(v) $`Z = () \ \vee\ (\mathrm{head}\,Z)_1 \le v_0`$.**
If $`Z = \mathrm{dw}_{v_0} D`$ is not empty, its first element fails the predicate that the first entry
is greater than $`v_0`$, so $`(\mathrm{head}\,Z)_1 \le v_0`$.

**Applying the core.** Substituting $`S = S_{\mathrm{hi}} \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)`$
and regrouping by associativity gives

```math
\begin{aligned}
&\bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \cr
&\qquad = \Bigl(G \mathbin{+\!\!+} (v_0,w_0) ::
  \bigl(R \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: (S_{\mathrm{hi}} \mathbin{+\!\!+} A_2)\bigr)\Bigr)
  \mathbin{+\!\!+} Z
\end{aligned}
```

Apply $`\mathrm{ArgDomCore}`$ with
$`X := G`$, $`A_1 := R`$, $`B := S_{\mathrm{hi}}`$, $`A_2 := A_2`$, $`Z := Z`$,
$`u := v_0`$, $`w := w_0`$, $`e := d_0`$.
The 8 conditions of D.ArgDomCore are supplied as follows.

- Condition (1): exactly the second $`\mathrm{ST\_PS}`$ hypothesis, as just rewritten.
- Condition (2): the hypothesis $`0 \lt d_0`$.
- Condition (3): the hypothesis $`\forall x \in R,\ v_0 \lt x_1`$.
- Condition (4): (i).
- Condition (5): (ii).
- Condition (6): (iv).
- Condition (7): (v).
- Condition (8): $`\mathrm{SpineOK}(R,\ v_0+d_0,\ w_0)`$, obtained by applying
  [T.spineOK_of_nextrel1](#t-spineOK_of_nextrel1) to the fifth hypothesis.

We therefore obtain the conclusion (9)

```math
S_{\mathrm{hi}} \preceq_{\mathrm{lex}}
  \bigl(R \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: (S_{\mathrm{hi}} \mathbin{+\!\!+} A_2)\bigr)^{+d_0}
```

By [T.shiftr0_append](Cofinality-3.md#t-shiftr0_append) and [T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons) the right-hand side equals

```math
R^{+d_0} \mathbin{+\!\!+} (v_0+d_0+d_0,\ w_0) :: (S_{\mathrm{hi}} \mathbin{+\!\!+} A_2)^{+d_0}
```

**Expansion into the tower of copies.** Apply [T.peel_aux](#t-peel_aux) with
$`d := d_0`$, $`w := w_0`$, $`n := \lvert S_{\mathrm{hi}}\rvert`$,
$`X := S_{\mathrm{hi}}`$, $`Q := R^{+d_0}`$, $`A_2 := A_2`$,
$`a := v_0+d_0+d_0`$. The length condition
$`\lvert S_{\mathrm{hi}}\rvert \le \lvert S_{\mathrm{hi}}\rvert`$ holds by reflexivity of $`\le`$.
Hence for some $`m`$

```math
S_{\mathrm{hi}} \preceq_{\mathrm{lex}}
  R^{+d_0} \mathbin{+\!\!+}
  \mathrm{copies}_{d_0}\bigl((v_0+d_0+d_0,\ w_0) :: (R^{+d_0})^{+d_0},\ m\bigr)
```

holds. This $`m`$ is the required one. Indeed, by [T.shiftr0_append](Cofinality-3.md#t-shiftr0_append), [T.shiftr0_copies](Cofinality-2.md#t-shiftr0_copies) and
[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons)

```math
\begin{aligned}
&\Bigl(R \mathbin{+\!\!+} \mathrm{copies}_{d_0}\bigl(((v_0,w_0) :: R)^{+d_0},\ m\bigr)\Bigr)^{+d_0} \cr
&\qquad = R^{+d_0} \mathbin{+\!\!+}
   \mathrm{copies}_{d_0}\bigl((((v_0,w_0) :: R)^{+d_0})^{+d_0},\ m\bigr) \cr
&\qquad = R^{+d_0} \mathbin{+\!\!+}
   \mathrm{copies}_{d_0}\bigl((v_0+d_0+d_0,\ w_0) :: (R^{+d_0})^{+d_0},\ m\bigr)
\end{aligned}
```

which coincides with the right-hand side of the comparison just obtained. ∎

<a id="t-pss_cofinality_of_core"></a>
## Theorem: from the core to cofinality for PSS (T.pss_cofinality_of_core)

### Theorem

Assume $`\mathrm{ArgDomCore}`$. If $`M, N \in \mathrm{ST\_PS}`$ and
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ ($`\mathrm{tr}`$ [D.translate](Term.md#d-translate), $`\prec`$ [D.olt](Term.md#d-olt)), then there exists $`n`$ such that
$`1 \le n`$ and $`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$ ($`M[n]`$ [D.oper](Pss.md#d-oper), $`\preceq`$ [D.ole](Term.md#d-ole)).

### Proof

Applying [T.ascArgDom_of_core](#t-ascArgDom_of_core) to the hypothesis $`\mathrm{ArgDomCore}`$ yields
$`\mathrm{AscArgDom}`$. Feeding this, together with the hypotheses $`M \in \mathrm{ST\_PS}`$, $`N \in \mathrm{ST\_PS}`$ and
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$, into
[T.pss_cofinality_of_argdom](Cofinality-3.md#t-pss_cofinality_of_argdom) produces an $`n`$ satisfying
$`1 \le n`$ and $`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$. ∎

<a id="d-ArgDomCoreOn"></a>
## Definition: the per-sequence form of the core (D.ArgDomCoreOn)

For $`N \in \mathrm{PairSeq}`$, the proposition $`\mathrm{ArgDomCoreOn}(N)`$ is defined as follows.
It is the proposition that for all $`X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$ and $`u, w, e \in \mathbb{N}`$,
if the following 8 conditions all hold then the conclusion (9) holds.

1. $`N = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z`$
2. $`0 \lt e`$
3. $`\forall x \in A_1,\ u \lt x_1`$
4. $`\forall x \in B,\ u + e \lt x_1`$
5. $`\forall x \in A_2,\ u \lt x_1`$
6. $`A_2 = () \ \vee\ (\mathrm{head}\,A_2)_1 \le u + e`$
7. $`Z = () \ \vee\ (\mathrm{head}\,Z)_1 \le u`$
8. $`\mathrm{SpineOK}(A_1,\ u+e,\ w)`$
9. $`B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}`$

<a id="t-argDomCore_of_on"></a>
## Theorem: from the per-sequence form to the core (T.argDomCore_of_on)

### Theorem

If $`N \in \mathrm{ST\_PS} \to \mathrm{ArgDomCoreOn}(N)`$ holds for every $`N \in \mathrm{PairSeq}`$,
then $`\mathrm{ArgDomCore}`$ holds.

### Proof

Following D.ArgDomCore, take $`X, A_1, B, A_2, Z`$ and $`u, w, e`$, and assume conditions (1) to (8). Put

```math
N := \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z
```

Then condition (1) says $`N \in \mathrm{ST\_PS}`$. Applying the hypothesis to this $`N`$ yields
$`\mathrm{ArgDomCoreOn}(N)`$.

Apply $`\mathrm{ArgDomCoreOn}(N)`$ to the same $`X, A_1, B, A_2, Z, u, w, e`$.
Condition (1) of D.ArgDomCoreOn reads $`N = N`$, which holds by reflexivity of $`=`$.
Conditions (2) to (8) are identical with conditions (2) to (8) of D.ArgDomCore.
We therefore obtain the conclusion (9), and this is identical with the conclusion (9) of D.ArgDomCore. ∎
