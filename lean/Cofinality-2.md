[← README](README.md) | [English](Cofinality-2.md) | [Japanese](Cofinality-2-ja.md) | Cofinality [1](Cofinality.md) **2** [3](Cofinality-3.md)

<a id="t-seqlex_splice"></a>
## Theorem: splice (T.seqlex_splice)

### Theorem

Let $`A \prec_{\mathrm{lex}} B`$ ([D.seqlex](Seqlex.md#d-seqlex)) and let
$`U \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) satisfy

```math
U = () \ \vee\ \forall x \in B,\ \mathrm{head}\,U \prec_{\mathrm{p}} x
```

Then for every $`C \in \mathrm{PairSeq}`$,

```math
A \mathbin{+\!\!+} U \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C .
```

Here $`\mathrm{head}\,U`$ is the first element of $`U`$
($`\prec_{\mathrm{p}}`$ [D.pairlt](Seqlex.md#d-pairlt)).

### Proof

Induction on the constructors of $`A`$ (with $`B`$, $`U`$, $`C`$ left universally quantified).
The induction predicate is

```math
\Phi(A) :\equiv \forall B,\ A \prec_{\mathrm{lex}} B \to \forall U,\
  \bigl(U = () \vee \forall x \in B,\ \mathrm{head}\,U \prec_{\mathrm{p}} x\bigr) \to
  \forall C,\ A \mathbin{+\!\!+} U \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C .
```

- **Base case** $`A = ()`$: if $`B = ()`$, then by the first clause of the definition of
  $`\prec_{\mathrm{lex}}`$ (D.seqlex) the hypothesis becomes $`() \ne ()`$, which is false.
  Hence $`B = b_0 :: B'`$. Distinguish cases on the constructor of $`U`$.

  - Case $`U = ()`$. Here $`A \mathbin{+\!\!+} U = ()`$ and
    $`B \mathbin{+\!\!+} C = b_0 :: (B' \mathbin{+\!\!+} C) \ne ()`$, so the first clause of the
    definition (D.seqlex) gives $`() \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$.

  - Case $`U = u :: U'`$. The first disjunct $`U = ()`$ is false, so the second disjunct holds,
    and since $`\mathrm{head}\,U = u`$ we have $`\forall x \in B,\ u \prec_{\mathrm{p}} x`$.
    Applying this with $`x := b_0`$ ($`b_0 \in B`$) yields $`u \prec_{\mathrm{p}} b_0`$.
    Since $`A \mathbin{+\!\!+} U = u :: U'`$ and $`B \mathbin{+\!\!+} C = b_0 :: (B' \mathbin{+\!\!+} C)`$,
    the first disjunct on the right-hand side of the third clause of the definition (D.seqlex) holds.

- **Inductive step** $`A = a :: A'`$: assume $`\Phi(A')`$.
  If $`B = ()`$, then by the second clause of the definition (D.seqlex) the hypothesis
  $`A \prec_{\mathrm{lex}} B`$ becomes $`\bot`$, so $`B = b_0 :: B'`$. By the third clause of the
  definition (D.seqlex) the hypothesis is one of the following.

  - Case $`a \prec_{\mathrm{p}} b_0`$. Here
    $`A \mathbin{+\!\!+} U = a :: (A' \mathbin{+\!\!+} U)`$ and
    $`B \mathbin{+\!\!+} C = b_0 :: (B' \mathbin{+\!\!+} C)`$, so the first disjunct on the right-hand
    side of the third clause of the definition (D.seqlex) holds directly.

  - Case $`a = b_0 \wedge A' \prec_{\mathrm{lex}} B'`$. Apply the induction hypothesis $`\Phi(A')`$
    to $`B'`$, $`U`$, $`C`$. Among its antecedents, the condition on $`U`$ is met as follows.
    If $`U = ()`$, this is directly the first disjunct. Otherwise the second disjunct of the
    hypothesis, $`\forall x \in B,\ \mathrm{head}\,U \prec_{\mathrm{p}} x`$, holds, and since
    $`B' \subseteq B`$ (if $`x \in B'`$ then $`x \in b_0 :: B' = B`$) we get
    $`\forall x \in B',\ \mathrm{head}\,U \prec_{\mathrm{p}} x`$.
    This yields $`A' \mathbin{+\!\!+} U \prec_{\mathrm{lex}} B' \mathbin{+\!\!+} C`$, which together with
    $`a = b_0`$ gives the second disjunct on the right-hand side of the third clause of the
    definition (D.seqlex). ∎

<a id="t-split_block"></a>
## Theorem: block split at the base depth (T.split_block)

### Theorem

Let $`v_0 \in \mathbb{N}`$ and $`R, Y \in \mathrm{PairSeq}`$, and assume
$`\forall x \in R,\ v_0 \lt x_1`$ together with

```math
Y = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,Y)_1\bigr)
```

Then

```math
\mathrm{tw}_{v_0}(R \mathbin{+\!\!+} Y) = R
\qquad\text{and}\qquad
\mathrm{dw}_{v_0}(R \mathbin{+\!\!+} Y) = Y .
```

Here $`\mathrm{tw}_a L`$ is the maximal prefix of $`L`$ along which the first entry stays greater
than $`a`$, and $`\mathrm{dw}_a L`$ is the sequence that remains after removing
$`\mathrm{tw}_a L`$ from $`L`$; both are notation from the definition (D.translate) of
$`\mathrm{tr}`$ ([D.translate](Term.md#d-translate)).

### Proof

By hypothesis every element of $`R`$ satisfies the predicate $`x \mapsto v_0 \lt x_1`$.
Distinguish cases on $`Y`$.

- Case $`Y = ()`$. Here $`R \mathbin{+\!\!+} () = R`$. Since every element of $`R`$ satisfies the
  predicate, $`\mathrm{tw}_{v_0} R = R`$, and from
  $`\mathrm{tw}_{v_0} R \mathbin{+\!\!+} \mathrm{dw}_{v_0} R = R`$ it follows that
  $`\mathrm{dw}_{v_0} R = () = Y`$.

- Case $`Y = y :: Y'`$. The first disjunct of the hypothesis is false, so the second disjunct
  holds, and since $`\mathrm{head}\,Y = y`$ we have $`\neg(v_0 \lt y_1)`$.
  Applying [T.takeWhile_append_all](Term.md#t-takeWhile_append_all) with $`xs := R`$ and
  $`ys := Y`$ gives $`\mathrm{tw}_{v_0}(R \mathbin{+\!\!+} Y) = R \mathbin{+\!\!+} \mathrm{tw}_{v_0} Y`$.
  The head $`y`$ of $`Y`$ violates the predicate, so $`\mathrm{tw}_{v_0} Y = ()`$ and the
  right-hand side is $`R`$. Applying [T.dropWhile_append_all](Term.md#t-dropWhile_append_all),
  again with $`xs := R`$ and $`ys := Y`$, gives
  $`\mathrm{dw}_{v_0}(R \mathbin{+\!\!+} Y) = \mathrm{dw}_{v_0} Y`$.
  The head $`y`$ of $`Y`$ violates the predicate, so $`\mathrm{dw}_{v_0} Y = Y`$. ∎

<a id="t-copy_dom_zero"></a>
## Theorem: domination by exact copies (T.copy_dom_zero)

### Theorem

Let $`d \in \mathbb{N}`$, $`Y, R \in \mathrm{PairSeq}`$ and $`v_0, w_0 \in \mathbb{N}`$, and put
$`B := (v_0,w_0) :: R`$. Assume the following five conditions.

```math
\begin{aligned}
&\text{(len)}\quad \lvert Y\rvert \le d, \cr
&\text{(blk)}\quad \mathrm{blockok}\bigl(v_0,\ (v_0,w_0) :: (R \mathbin{+\!\!+} Y)\bigr), \cr
&\text{(R)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hd)}\quad Y = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,Y)_1\bigr), \cr
&\text{(cnf)}\quad \mathrm{cnf}\bigl(\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} Y)\bigr)\bigr).
\end{aligned}
```

($`\mathrm{blockok}`$ [D.blockok](Seqlex.md#d-blockok), $`\mathrm{cnf}`$ [D.cnf](Cnf.md#d-cnf))

Then

```math
\exists m,\ \bigl(1 \le m \wedge Y \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)\bigr).
```

($`\mathrm{cp}_d(B,n)`$ [D.copies](Cnf-2.md#d-copies),
$`\preceq_{\mathrm{lex}}`$ [D.sle](Cofinality.md#d-sle). Below, $`\mathsf{Z}`$ and $`\mathsf{P}`$
are the constructors of $`\mathrm{Three}`$ [D.Three](Term.md#d-Three).)

### Proof

Induction on the natural number $`d`$. The induction predicate is

```math
\Phi(d) :\equiv \forall Y, v_0, w_0, R,\
  \bigl(\text{(len)} \wedge \text{(blk)} \wedge \text{(R)} \wedge \text{(hd)} \wedge \text{(cnf)}\bigr)
  \to \exists m,\ \bigl(1 \le m \wedge Y \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)\bigr).
```

Here (len), (blk), (R), (hd), (cnf) are the five hypotheses of the theorem, and
$`Y, v_0, w_0, R`$ are the bound variables of $`\Phi(d)`$ (so $`B = (v_0,w_0) :: R`$ varies
with them).

- **Base case** $`d = 0`$: (len) reads $`\lvert Y\rvert \le 0`$, that is $`\lvert Y\rvert = 0`$, so
  $`Y = ()`$. Take $`m := 1`$. By [T.copies_one](Cnf-3.md#t-copies_one),
  $`\mathrm{cp}_0(B, 1) = B = (v_0,w_0) :: R \ne ()`$, so the first clause of the definition of
  $`\prec_{\mathrm{lex}}`$ (D.seqlex) gives
  $`() \prec_{\mathrm{lex}} \mathrm{cp}_0(B,1)`$, and the second disjunct of the definition of
  $`\preceq_{\mathrm{lex}}`$ (D.sle) holds.

**Inductive step** $`d + 1`$: assume $`\Phi(d)`$. Distinguish cases on the
constructor of $`Y`$.

**(a) The case $`Y = ()`$.** As in the base case, it suffices to take $`m := 1`$.

**(b) The case $`Y = y :: Y'`$.** The rest of the proof treats this case.

**Step 1: $`y = (v_0, y_2)`$.**
Since $`y`$ is an element of $`(v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$, hypothesis (blk), that is the
second conjunct
$`\forall p \in (v_0,w_0) :: (R \mathbin{+\!\!+} Y),\ v_0 \le p_1`$ of the definition of
$`\mathrm{blockok}`$ (D.blockok), gives $`v_0 \le y_1`$.
Moreover the first disjunct of (hd) is false because $`Y = y :: Y' \ne ()`$, so the second
disjunct holds, and since $`\mathrm{head}\,Y = y`$ we get $`\neg(v_0 \lt y_1)`$, that is
$`y_1 \le v_0`$. Hence $`y_1 = v_0`$, and since a pair is determined by its two entries,
$`y = (v_0, y_2)`$.

**Step 2: splitting $`Y'`$.**
Put

```math
R' := \mathrm{tw}_{v_0} Y', \qquad Y'' := \mathrm{dw}_{v_0} Y'
```

By the definitions of $`\mathrm{tw}`$ and $`\mathrm{dw}`$ (notation from the definition
D.translate of $`\mathrm{tr}`$), $`R' \mathbin{+\!\!+} Y'' = Y'`$. Moreover:

- $`\forall x \in R',\ v_0 \lt x_1`$: the elements of $`\mathrm{tw}_{v_0} Y'`$ satisfy the
  predicate $`x \mapsto v_0 \lt x_1`$.
- $`Y'' = () \vee \neg\bigl(v_0 \lt (\mathrm{head}\,Y'')_1\bigr)`$: if $`\mathrm{dw}_{v_0} Y'`$ is
  non-empty, its first element violates the predicate.

**Step 3: the shape of the two translations.**
By Steps 1 and 2, $`\bigl((v_0,y_2) :: R'\bigr) \mathbin{+\!\!+} Y'' = (v_0,y_2) :: Y' = y :: Y'`$.
Apply [T.translate_block_append](Term.md#t-translate_block_append) with
$`v_0 := v_0`$, $`w_0 := y_2`$, $`R := R'`$, $`T := Y''`$.
Its two hypotheses, that every element $`x`$ of $`R'`$ satisfies $`v_0 \lt x_1`$, and that
$`Y'' = ()`$ or $`\neg\bigl(v_0 \lt (\mathrm{head}\,Y'')_1\bigr)`$, were established in Step 2.
This gives

```math
\mathrm{tr}(y :: Y') = \mathsf{P}\bigl(y_2,\ \mathrm{tr}\,R',\ \mathrm{tr}\,Y''\bigr) .
```

Also, since $`Y = y :: Y'`$, we have
$`\bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} (y :: Y') = (v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$.
Apply [T.translate_block_append](Term.md#t-translate_block_append) with
$`v_0 := v_0`$, $`w_0 := w_0`$, $`R := R`$, $`T := y :: Y'`$.
Its two hypotheses, that every element $`x`$ of $`R`$ satisfies $`v_0 \lt x_1`$, and that
$`y :: Y' = ()`$ or $`\neg\bigl(v_0 \lt (\mathrm{head}\,(y :: Y'))_1\bigr)`$, are
(R) and (hd) respectively. This gives

```math
\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} Y)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}(y :: Y')\bigr) .
```

**Step 4: decomposing the CNF condition.**
Substituting the two equations of Step 3 into (cnf) gives

```math
\mathrm{cnf}\Bigl(\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\
  \mathsf{P}(y_2,\ \mathrm{tr}\,R',\ \mathrm{tr}\,Y'')\bigr)\Bigr)
```

By [T.cnf_P_P](Cnf.md#t-cnf_P_P) this is equivalent to the conjunction of the following three.

```math
\begin{aligned}
&\text{(c1)}\quad \mathrm{cnf}(\mathrm{tr}\,R), \cr
&\text{(c2)}\quad \neg\bigl(\mathsf{P}(w_0, \mathrm{tr}\,R, \mathsf{Z})
  \prec \mathsf{P}(y_2, \mathrm{tr}\,R', \mathsf{Z})\bigr), \cr
&\text{(c3)}\quad \mathrm{cnf}\bigl(\mathsf{P}(y_2, \mathrm{tr}\,R', \mathrm{tr}\,Y'')\bigr).
\end{aligned}
```

($`\prec`$ [D.olt](Term.md#d-olt))

**Step 5: $`y_2 \le w_0`$.**
Suppose $`w_0 \lt y_2`$. Then the first disjunct on the right-hand side of
[T.olt_P_P](Term.md#t-olt_P_P) gives
$`\mathsf{P}(w_0, \mathrm{tr}\,R, \mathsf{Z}) \prec \mathsf{P}(y_2, \mathrm{tr}\,R', \mathsf{Z})`$,
contradicting (c2). Hence $`y_2 \le w_0`$. Distinguish the cases $`y_2 \lt w_0`$ and
$`y_2 = w_0`$.

**Step 6: the case $`y_2 \lt w_0`$.**
Take $`m := 1`$. By [T.copies_one](Cnf-3.md#t-copies_one),
$`\mathrm{cp}_0(B, 1) = (v_0,w_0) :: R`$. By Step 1, $`y = (v_0,y_2)`$, so the second disjunct of
the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt) ($`v_0 = v_0`$ and $`y_2 \lt w_0`$) gives
$`y \prec_{\mathrm{p}} (v_0,w_0)`$. The first disjunct of the third clause of the definition of
$`\prec_{\mathrm{lex}}`$ (D.seqlex) then gives
$`y :: Y' \prec_{\mathrm{lex}} (v_0,w_0) :: R`$, and the second disjunct of the definition of
$`\preceq_{\mathrm{lex}}`$ (D.sle) holds.

**Step 7: the case $`y_2 = w_0`$ (preparation).**
By Step 1, $`y = (v_0,w_0)`$. We prepare the following four facts.

1. $`\neg\bigl(\mathrm{tr}\,R \prec \mathrm{tr}\,R'\bigr)`$. If $`\mathrm{tr}\,R \prec \mathrm{tr}\,R'`$
   held, then together with $`w_0 = y_2`$ the second disjunct on the right-hand side of
   [T.olt_P_P](Term.md#t-olt_P_P) would hold, contradicting (c2).
2. $`\mathrm{blockok}(v_0,\ y :: Y')`$. Applying [T.split_block](#t-split_block) to (R) and (hd)
   gives $`\mathrm{dw}_{v_0}(R \mathbin{+\!\!+} Y) = Y`$.
   Applying [T.blockok_tail](Seqlex.md#t-blockok_tail) to (blk) gives
   $`\mathrm{blockok}\bigl(v_0,\ \mathrm{dw}_{v_0}(R \mathbin{+\!\!+} Y)\bigr)`$, which is
   $`\mathrm{blockok}(v_0, Y) = \mathrm{blockok}(v_0,\ y :: Y')`$.
3. $`\mathrm{blockok}(v_0 + 1,\ R)`$. By [T.split_block](#t-split_block),
   $`\mathrm{tw}_{v_0}(R \mathbin{+\!\!+} Y) = R`$, and applying
   [T.blockok_arg](Seqlex.md#t-blockok_arg) to (blk) gives
   $`\mathrm{blockok}\bigl(v_0+1,\ \mathrm{tw}_{v_0}(R \mathbin{+\!\!+} Y)\bigr) = \mathrm{blockok}(v_0+1,\ R)`$.
4. $`\mathrm{blockok}(v_0 + 1,\ R')`$. From 2 and $`y = (v_0,w_0)`$ we get
   $`\mathrm{blockok}\bigl(v_0,\ (v_0,w_0) :: Y'\bigr)`$, and applying
   [T.blockok_arg](Seqlex.md#t-blockok_arg) gives
   $`\mathrm{blockok}\bigl(v_0+1,\ \mathrm{tw}_{v_0} Y'\bigr) = \mathrm{blockok}(v_0+1,\ R')`$.

Distinguish further according to whether $`R' = R`$ or not.

**Step 8: the case $`R' = R`$.**
By Steps 1 and 2 together with $`R' = R`$,

```math
y :: Y' = (v_0,w_0) :: (R' \mathbin{+\!\!+} Y'') = \bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} Y''
  = B \mathbin{+\!\!+} Y''
```

Apply the induction hypothesis $`\Phi(d)`$ with $`Y := Y''`$ and $`v_0, w_0, R`$ unchanged.
Its five antecedents are met as follows.

- (len): $`\lvert R'\rvert + \lvert Y''\rvert = \lvert Y'\rvert`$, and the present (len) reads
  $`\lvert y :: Y'\rvert = \lvert Y'\rvert + 1 \le d + 1`$, that is $`\lvert Y'\rvert \le d`$.
  Hence $`\lvert Y''\rvert \le \lvert Y'\rvert \le d`$.
- (blk): $`(v_0,w_0) :: (R \mathbin{+\!\!+} Y'') = B \mathbin{+\!\!+} Y'' = y :: Y'`$, so this is
  exactly item 2 of Step 7.
- (R): this is the present (R) itself.
- (hd): this is the disjunction about $`Y''`$ established in Step 2.
- (cnf): $`\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} Y'')\bigr) = \mathrm{tr}(y :: Y')`$, and by
  Step 3 this is $`\mathsf{P}(y_2, \mathrm{tr}\,R', \mathrm{tr}\,Y'')`$, so this is (c3).

This yields an $`m`$ with $`1 \le m`$ and $`Y'' \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$.
Take $`m + 1`$ as the required index; indeed $`1 \le m + 1`$.
By [T.copies_succ_cons](Cnf-3.md#t-copies_succ_cons) and
[T.shiftr0_zero](Cnf-2.md#t-shiftr0_zero),

```math
\mathrm{cp}_0(B, m+1) = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} \mathrm{cp}_0(B, m)^{+0}\bigr)
  = B \mathbin{+\!\!+} \mathrm{cp}_0(B, m)
```

($`X^{+d}`$ [D.shiftr0](Cnf-2.md#d-shiftr0)). What has to be shown is therefore
$`B \mathbin{+\!\!+} Y'' \preceq_{\mathrm{lex}} B \mathbin{+\!\!+} \mathrm{cp}_0(B, m)`$, which by
[T.sle_append_cancel](Cofinality.md#t-sle_append_cancel) is equivalent to
$`Y'' \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$. This is exactly what was obtained.

**Step 9: the case $`R' \ne R`$.**
First we show $`R' \prec_{\mathrm{lex}} R`$. By [T.seqlex_total](Seqlex-2.md#t-seqlex_total),
one of $`R' = R`$, $`R' \prec_{\mathrm{lex}} R`$, $`R \prec_{\mathrm{lex}} R'`$ holds.
The first contradicts the case hypothesis. If the third held, then items 3 and 4 of Step 7 let us
apply [T.seqlex_imp_olt](Seqlex-2.md#t-seqlex_imp_olt) with $`d := v_0 + 1`$, $`M := R`$,
$`N := R'`$, giving $`\mathrm{tr}\,R \prec \mathrm{tr}\,R'`$ and contradicting item 1 of Step 7.
Hence the second holds, that is, $`R' \prec_{\mathrm{lex}} R`$.

Take $`m := 2`$; indeed $`1 \le 2`$.
By [T.copies_succ_cons](Cnf-3.md#t-copies_succ_cons), [T.shiftr0_zero](Cnf-2.md#t-shiftr0_zero)
and [T.copies_one](Cnf-3.md#t-copies_one),

```math
\mathrm{cp}_0(B, 2) = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} \mathrm{cp}_0(B,1)^{+0}\bigr)
  = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} B\bigr)
```

By Step 1 and $`y_2 = w_0`$ we have $`y :: Y' = (v_0,w_0) :: Y'`$, so by the second disjunct of the
third clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex) what has to be shown is

```math
Y' \prec_{\mathrm{lex}} R \mathbin{+\!\!+} B
```

Since $`Y' = R' \mathbin{+\!\!+} Y''`$, it suffices to apply
[T.seqlex_splice](#t-seqlex_splice) with $`R'`$ as the smaller sequence, $`R`$ as the larger one,
$`Y''`$ as the sequence appended to the smaller one and $`B`$ as the sequence appended to the
larger one. Its two hypotheses are met as follows.

- $`R' \prec_{\mathrm{lex}} R`$: just shown.
- $`Y'' = () \vee \forall x \in R,\ \mathrm{head}\,Y'' \prec_{\mathrm{p}} x`$:
  distinguish cases by the disjunction about $`Y''`$ from Step 2. If $`Y'' = ()`$, this is
  directly the first disjunct. Otherwise $`\neg\bigl(v_0 \lt (\mathrm{head}\,Y'')_1\bigr)`$, that is
  $`(\mathrm{head}\,Y'')_1 \le v_0`$. For $`x \in R`$, (R) gives $`v_0 \lt x_1`$, hence
  $`(\mathrm{head}\,Y'')_1 \lt x_1`$, and the first disjunct of the definition of
  $`\prec_{\mathrm{p}}`$ (D.pairlt) gives $`\mathrm{head}\,Y'' \prec_{\mathrm{p}} x`$.

This yields $`Y' \prec_{\mathrm{lex}} R \mathbin{+\!\!+} B`$, and the second disjunct of the
definition of $`\preceq_{\mathrm{lex}}`$ (D.sle) holds. ∎

<a id="t-copies_zero_succ"></a>
## Theorem: rear decomposition of exact copies (T.copies_zero_succ)

### Theorem

For $`B \in \mathrm{PairSeq}`$ and $`m \in \mathbb{N}`$,

```math
\mathrm{cp}_0(B, m+1) = \mathrm{cp}_0(B, m) \mathbin{+\!\!+} B .
```

### Proof

By the definition of $`\mathrm{cp}`$ (D.copies),

```math
\mathrm{cp}_d(B, n) = B^{+0 \cdot d} \mathbin{+\!\!+} B^{+1 \cdot d}
  \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d}
```

that is, it is the concatenation obtained by assigning $`B^{+k d}`$ to each $`k`$ of the index
sequence $`(0, 1, \dots, n-1)`$. For $`n := m+1`$ this index sequence is $`(0, 1, \dots, m-1)`$
with $`m`$ appended at the end, so the concatenation splits as

```math
\mathrm{cp}_d(B, m+1) = \mathrm{cp}_d(B, m) \mathbin{+\!\!+} B^{+m d}
```

Taking $`d := 0`$ we have $`m \cdot 0 = 0`$, and
[T.shiftr0_zero](Cnf-2.md#t-shiftr0_zero) gives $`B^{+0} = B`$. ∎

<a id="t-crux_zero"></a>
## Theorem: the crux of the exact-copy branch (T.crux_zero)

### Theorem

Let $`G, R, S \in \mathrm{PairSeq}`$, $`v_0, w_0 \in \mathbb{N}`$ and
$`\ell, q \in \mathbb{N}\times\mathbb{N}`$, and put $`B := (v_0, w_0) :: R`$.
Assume the following four conditions.

```math
\begin{aligned}
&(1)\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S \in \mathrm{ST\_PS}, \cr
&(2)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(3)\ \ell_2 = 0 \ \wedge\ \ell_1 = v_0 + 1, \cr
&(4)\ q \prec_{\mathrm{p}} \ell .
\end{aligned}
```

($`\mathrm{ST\_PS}`$ [D.ST_PS](Pss.md#d-ST_PS))

Then there exists $`m \in \mathbb{N}`$ with $`1 \le m`$ such that

```math
q :: S \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m) .
```

### Proof

**Step 1: $`q_1 \le v_0`$.**
By the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt), hypothesis (4) says
$`q_1 \lt \ell_1`$, or else $`q_1 = \ell_1`$ and $`q_2 \lt \ell_2`$.
In the latter case $`\ell_2 = 0`$ from hypothesis (3) gives $`q_2 \lt 0`$; no natural number is
smaller than $`0`$, so this is a contradiction and the case does not occur. In the former case
$`\ell_1 = v_0 + 1`$ from hypothesis (3) gives
$`q_1 \lt v_0 + 1`$, that is $`q_1 \le v_0`$.

**Step 2: the case $`q_1 \lt v_0`$.**
Take $`m := 1`$. By [T.copies_one](Cnf-3.md#t-copies_one), $`\mathrm{cp}_0(B, 1) = B = (v_0,w_0) :: R`$.
Since $`q_1 \lt v_0`$, the first disjunct of the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt)
gives $`q \prec_{\mathrm{p}} (v_0,w_0)`$, and the first disjunct of the third clause of the
definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex) gives $`q :: S \prec_{\mathrm{lex}} B`$.
The second disjunct of the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle) yields the conclusion.

**Step 3: from here on $`q_1 = v_0`$.**
Step 1 together with $`\neg(q_1 \lt v_0)`$ gives $`q_1 = v_0`$. Define the predicate $`p`$ by
$`p(x) :\equiv v_0 \le x_1`$ and put

```math
Y := \mathrm{tw}_p(q :: S), \qquad V := \mathrm{dw}_p(q :: S)
```

The following four statements hold.

**(i)** $`Y \mathbin{+\!\!+} V = q :: S`$. This is precisely the definition of $`\mathrm{tw}_p`$ and
$`\mathrm{dw}_p`$.

**(ii)** $`Y = q :: \mathrm{tw}_p S`$. Since $`q_1 = v_0`$, the predicate $`p(q)`$ holds, so
$`\mathrm{tw}_p`$ takes in the leading $`q`$. In particular $`Y \ne ()`$ and
$`(\mathrm{head}\,Y)_1 = q_1 = v_0`$.

**(iii)** $`\forall x \in Y,\ v_0 \le x_1`$, because every element of $`\mathrm{tw}_p`$ satisfies $`p`$.

**(iv)** Either $`V = ()`$, or there are $`z, Z`$ with $`V = z :: Z`$ and $`z_1 \lt v_0`$.
Indeed, if $`V \ne ()`$ then its first element $`z`$ satisfies $`\neg p(z)`$, that is
$`\neg(v_0 \le z_1)`$, so $`z_1 \lt v_0`$.

**Step 4: the decomposition through $`B \mathbin{+\!\!+} Y`$.**
By (i) and associativity,

```math
(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S = \bigl(G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)\bigr) \mathbin{+\!\!+} V
```

We write $`N`$ for this sequence.

**Step 5: $`\mathrm{steps}_1(B \mathbin{+\!\!+} Y)`$ ([D.steps1](Seqlex.md#d-steps1)).**
Hypothesis (1) and [T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS) give $`\mathrm{blockok}(0, N)`$,
and the third conjunct of the definition of $`\mathrm{blockok}`$ (D.blockok) gives
$`\mathrm{steps}_1(N)`$. Applying [T.steps1_append](Seqlex.md#t-steps1_append) to the
decomposition of Step 4 yields, as its first conjunct,
$`\mathrm{steps}_1\bigl(G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)\bigr)`$. Applying
[T.steps1_append](Seqlex.md#t-steps1_append) to this again yields, as its second conjunct,
$`\mathrm{steps}_1(B \mathbin{+\!\!+} Y)`$.

**Step 6: $`\mathrm{blockok}(v_0,\ B \mathbin{+\!\!+} Y)`$.**
We check the three conjuncts of the definition of $`\mathrm{blockok}`$ (D.blockok).
The first conjunct says that if the sequence is non-empty then the first entry of its head is
$`v_0`$; the head is $`(v_0,w_0)`$, so it holds.
The second conjunct is $`\forall x \in B \mathbin{+\!\!+} Y,\ v_0 \le x_1`$:
if $`x = (v_0,w_0)`$ then $`x_1 = v_0`$; if $`x \in R`$ then hypothesis (2) gives $`v_0 \lt x_1`$;
if $`x \in Y`$ then (iii) gives $`v_0 \le x_1`$. The third conjunct is Step 5.

**Step 7: $`\mathrm{cnf}`$ for $`(v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$.**
Hypothesis (1) and [T.cnf_ST_PS](Cnf-3.md#t-cnf_ST_PS) give $`\mathrm{cnf}(\mathrm{tr}\,N)`$.
By the decomposition of Step 4 this is
$`\mathrm{cnf}\bigl(\mathrm{tr}\bigl((G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)) \mathbin{+\!\!+} V\bigr)\bigr)`$.
Apply [T.cnf_take](Cnf.md#t-cnf_take) with $`k := \lvert G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y)\rvert`$.
Cutting a concatenation at the length of its left part returns that left part itself, so we obtain

```math
\mathrm{cnf}\bigl(\mathrm{tr}\,(G \mathbin{+\!\!+} (B \mathbin{+\!\!+} Y))\bigr)
```

Since $`B \mathbin{+\!\!+} Y = (v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$, this is the same proposition as
$`\mathrm{cnf}\bigl(\mathrm{tr}\,(G \mathbin{+\!\!+} ((v_0,w_0) :: (R \mathbin{+\!\!+} Y)))\bigr)`$.
Apply [T.cnf_tail](Cnf-2.md#t-cnf_tail) with $`t := (v_0,w_0)`$, $`T' := R \mathbin{+\!\!+} Y`$,
$`G := G`$. Its hypothesis $`\forall x \in R \mathbin{+\!\!+} Y,\ v_0 \le x_1`$ follows from the
second conjunct of Step 6 (since every element of $`R \mathbin{+\!\!+} Y`$ is also an element of
$`B \mathbin{+\!\!+} Y`$). Hence

```math
\mathrm{cnf}\bigl(\mathrm{tr}\,((v_0,w_0) :: (R \mathbin{+\!\!+} Y))\bigr) .
```

**Step 8: domination by exact copies.**
Apply [T.copy_dom_zero](#t-copy_dom_zero) with $`d := \lvert Y\rvert`$, $`Y := Y`$, $`v_0`$,
$`w_0`$, $`R`$. Its five hypotheses are met as follows.

- $`\lvert Y\rvert \le \lvert Y\rvert`$: by equality.
- $`\mathrm{blockok}\bigl(v_0,\ (v_0,w_0) :: (R \mathbin{+\!\!+} Y)\bigr)`$: this is Step 6 rewritten
  via $`B \mathbin{+\!\!+} Y = (v_0,w_0) :: (R \mathbin{+\!\!+} Y)`$.
- $`\forall x \in R,\ v_0 \lt x_1`$: this is hypothesis (2).
- $`Y = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,Y)_1\bigr)`$: by (ii)
  $`(\mathrm{head}\,Y)_1 = v_0`$, so the second disjunct holds.
- $`\mathrm{cnf}\bigl(\mathrm{tr}\,((v_0,w_0) :: (R \mathbin{+\!\!+} Y))\bigr)`$: this is Step 7.

This yields an $`m`$ with $`1 \le m`$ together with $`Y \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$.

**Step 9: conclusion.**
Take $`m + 1`$ as the required index ($`1 \le m + 1`$).
By [T.copies_zero_succ](#t-copies_zero_succ),
$`\mathrm{cp}_0(B, m+1) = \mathrm{cp}_0(B, m) \mathbin{+\!\!+} B`$, and by (i) $`q :: S = Y \mathbin{+\!\!+} V`$,
so what has to be shown is

```math
Y \mathbin{+\!\!+} V \prec_{\mathrm{lex}} \mathrm{cp}_0(B, m) \mathbin{+\!\!+} B
```

(once this is available, the second disjunct of the definition of $`\preceq_{\mathrm{lex}}`$
(D.sle) yields the conclusion). Split the $`\preceq_{\mathrm{lex}}`$ of Step 8 into two cases
according to the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle).

**(a) The case $`Y = \mathrm{cp}_0(B, m)`$.**
What has to be shown is $`Y \mathbin{+\!\!+} V \prec_{\mathrm{lex}} Y \mathbin{+\!\!+} B`$.
By [T.seqlex_append_cancel](Seqlex.md#t-seqlex_append_cancel) it suffices to show
$`V \prec_{\mathrm{lex}} B`$. Distinguish cases by (iv).

- Case $`V = ()`$. By the first clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex) it
  suffices to show $`B \ne ()`$, and $`B = (v_0,w_0) :: R`$ is non-empty.
- Case $`V = z :: Z`$ with $`z_1 \lt v_0`$. The first disjunct of the definition of
  $`\prec_{\mathrm{p}}`$ (D.pairlt) gives $`z \prec_{\mathrm{p}} (v_0,w_0)`$, and the first
  disjunct of the third clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex) gives
  $`z :: Z \prec_{\mathrm{lex}} (v_0,w_0) :: R`$.

**(b) The case $`Y \prec_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$.**
Apply [T.seqlex_splice](#t-seqlex_splice) with $`Y`$ as the smaller sequence,
$`\mathrm{cp}_0(B, m)`$ as the larger one, $`V`$ as the sequence appended to the smaller one and
$`B`$ as the sequence appended to the larger one. The remaining hypothesis is that
$`V = ()`$, or $`\forall x \in \mathrm{cp}_0(B,m),\ \mathrm{head}\,V \prec_{\mathrm{p}} x`$.
Distinguish cases by (iv).

- Case $`V = ()`$. This is the first disjunct.
- Case $`V = z :: Z`$ with $`z_1 \lt v_0`$. By hypothesis (2) every element $`y`$ of $`R`$
  satisfies $`v_0 \le y_1`$, so applying [T.copies_v0_le](Cnf-3.md#t-copies_v0_le) with
  $`d := 0`$ and $`n := m`$ gives $`\forall x \in \mathrm{cp}_0(B, m),\ v_0 \le x_1`$.
  Since $`\mathrm{head}\,V = z`$ and $`z_1 \lt v_0 \le x_1`$, the first disjunct of the definition
  of $`\prec_{\mathrm{p}}`$ (D.pairlt) gives $`z \prec_{\mathrm{p}} x`$.

In either case $`Y \mathbin{+\!\!+} V \prec_{\mathrm{lex}} \mathrm{cp}_0(B,m) \mathbin{+\!\!+} B`$ is obtained. ∎

<a id="d-AscCrux"></a>
## Definition: the crux of ascending copies (D.AscCrux)

The proposition $`\mathrm{AscCrux}`$ is defined as follows. Here $`B := (v_0,w_0) :: R`$ and
$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$ are abbreviations ($`(\ell)`$ is the sequence
of length $`1`$ whose only element is $`\ell`$).

```math
\begin{aligned}
\mathrm{AscCrux} :\equiv\ &\forall G, R, S \in \mathrm{PairSeq},\ \forall v_0, w_0, d_0 \in \mathbb{N},\
   \forall \ell, q \in \mathbb{N}\times\mathbb{N}, \cr
&\quad H \in \mathrm{ST\_PS}
  \ \to\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S \in \mathrm{ST\_PS} \cr
&\quad \to\ \bigl(\forall x \in R,\ v_0 \lt x_1\bigr)
  \ \to\ 0 \lt d_0 \ \to\ \ell_2 = w_0 + 1 \ \to\ \ell_1 = v_0 + d_0 \cr
&\quad \to\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert
  \ \to\ q \prec_{\mathrm{p}} \ell \cr
&\quad \to\ \exists m,\ 1 \le m \ \wedge\
   q :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B, m)\bigr)^{+d_0} .
\end{aligned}
```

($`\to^M_1`$ [D.nextrel1](Pss.md#d-nextrel1))

<a id="d-AscCrux1"></a>
## Definition: the crux of ascending copies with the head taken (D.AscCrux1)

The proposition $`\mathrm{AscCrux1}`$ is defined as follows. Here $`B := (v_0,w_0) :: R`$ and
$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr)`$ are abbreviations.

```math
\begin{aligned}
\mathrm{AscCrux1} :\equiv\ &\forall G, R, S \in \mathrm{PairSeq},\ \forall v_0, w_0, d_0 \in \mathbb{N}, \cr
&\quad H \in \mathrm{ST\_PS}
  \ \to\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS} \cr
&\quad \to\ \bigl(\forall x \in R,\ v_0 \lt x_1\bigr) \ \to\ 0 \lt d_0 \cr
&\quad \to\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert \cr
&\quad \to\ \exists m,\ 1 \le m \ \wedge\
   (v_0+d_0,\ w_0) :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B, m)\bigr)^{+d_0} .
\end{aligned}
```

<a id="t-shiftr0_length"></a>
## Theorem: the shift does not change the length (T.shiftr0_length)

### Theorem

For $`d \in \mathbb{N}`$ and $`X \in \mathrm{PairSeq}`$, $`\lvert X^{+d}\rvert = \lvert X\rvert`$.

### Proof

By the definition of $`X^{+d}`$ (D.shiftr0), $`X^{+d}`$ is the sequence obtained by sending each
element $`x`$ of $`X`$ to $`(x_1+d,\ x_2)`$, and applying a map to every element does not change
the length of a sequence. ∎

<a id="t-mem_shiftr0_le"></a>
## Theorem: lower bound on row 0 after the shift (T.mem_shiftr0_le)

### Theorem

Let $`d, e \in \mathbb{N}`$ and $`X \in \mathrm{PairSeq}`$.
If $`\forall x \in X,\ d \le x_1`$ then $`\forall x \in X^{+e},\ d + e \le x_1`$.

### Proof

Let $`x \in X^{+e}`$. By [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) there is a $`y \in X`$ with
$`x = (y_1 + e,\ y_2)`$. The hypothesis gives $`d \le y_1`$, hence
$`d + e \le y_1 + e = x_1`$. ∎

<a id="t-shiftr0_copies"></a>
## Theorem: the shift commutes with the copy tower (T.shiftr0_copies)

### Theorem

For $`d, n \in \mathbb{N}`$ and $`B \in \mathrm{PairSeq}`$,

```math
\bigl(\mathrm{cp}_d(B, n)\bigr)^{+d} = \mathrm{cp}_d\bigl(B^{+d},\ n\bigr) .
```

### Proof

By the definition of $`\mathrm{cp}_d`$ (D.copies),

```math
\mathrm{cp}_d(B, n) = B^{+0\cdot d} \mathbin{+\!\!+} B^{+1\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d}
```

Since $`\cdot^{+d}`$ is the application of a map to every element, it preserves concatenation:
$`(X \mathbin{+\!\!+} Y)^{+d} = X^{+d} \mathbin{+\!\!+} Y^{+d}`$. Iterating this gives

```math
\bigl(\mathrm{cp}_d(B, n)\bigr)^{+d}
  = \bigl(B^{+0\cdot d}\bigr)^{+d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl(B^{+(n-1)d}\bigr)^{+d}
```

On the other hand,

```math
\mathrm{cp}_d\bigl(B^{+d},\ n\bigr)
  = \bigl(B^{+d}\bigr)^{+0\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl(B^{+d}\bigr)^{+(n-1)d}
```

Compare the $`k`$-th terms of the two ($`k = 0, \dots, n-1`$). For $`x \in B`$, the corresponding
element of $`\bigl(B^{+kd}\bigr)^{+d}`$ is $`(x_1 + kd + d,\ x_2)`$ and the corresponding element
of $`\bigl(B^{+d}\bigr)^{+kd}`$ is $`(x_1 + d + kd,\ x_2)`$; by associativity and commutativity of
addition on the natural numbers, $`x_1 + kd + d = x_1 + d + kd`$.
The second entry is $`x_2`$ in both cases and is unchanged. Hence the $`k`$-th terms are equal,
and so are the concatenations. ∎
