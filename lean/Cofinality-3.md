[← README](README.md) | [English](Cofinality-3.md) | [Japanese](Cofinality-3-ja.md) | Cofinality [1](Cofinality.md) [2](Cofinality-2.md) **3**

<a id="d-AscArgDom"></a>
## Definition: argument domination for ascending copies (D.AscArgDom)

Define the proposition $`\mathrm{AscArgDom}`$ as follows, where $`B := (v_0,w_0) :: R`$ and
$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr)`$ are abbreviations.

```math
\begin{aligned}
\mathrm{AscArgDom} :\equiv\ &\forall G, R, S \in \mathrm{PairSeq},\ \forall v_0, w_0, d_0 \in \mathbb{N}, \cr
&\quad H \in \mathrm{ST\_PS}
  \ \to\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS} \cr
&\quad \to\ \bigl(\forall x \in R,\ v_0 \lt x_1\bigr) \ \to\ 0 \lt d_0 \cr
&\quad \to\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert \cr
&\quad \to\ \exists m,\
   \mathrm{tw}_{v_0+d_0} S \preceq_{\mathrm{lex}}
     \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B^{+d_0},\ m)\bigr)^{+d_0} .
\end{aligned}
```

($`\mathrm{PairSeq}`$ [D.PairSeq](Pss.md#d-PairSeq), $`\mathrm{ST\_PS}`$ [D.ST_PS](Pss.md#d-ST_PS),
$`j_0 \to^M_1 j_1`$ [D.nextrel1](Pss.md#d-nextrel1),
$`\mathrm{tw}_a L`$ and $`\mathrm{tr}`$ [D.translate](Term.md#d-translate),
$`\preceq_{\mathrm{lex}}`$ [D.sle](Cofinality.md#d-sle),
$`\mathrm{cp}_d(B,n)`$ [D.copies](Cnf-2.md#d-copies), $`L^{+d}`$ [D.shiftr0](Cnf-2.md#d-shiftr0))

<a id="t-shiftr0_append"></a>
## Theorem: the shift preserves concatenation (T.shiftr0_append)

### Theorem

For $`d \in \mathbb{N}`$ and $`A, B \in \mathrm{PairSeq}`$,
$`(A \mathbin{+\!\!+} B)^{+d} = A^{+d} \mathbin{+\!\!+} B^{+d}`$.

### Proof

By the definition of $`X^{+d}`$ (D.shiftr0), $`X^{+d}`$ is the application of the map
$`x \mapsto (x_1+d,\ x_2)`$ to each element of $`X`$, and applying a map to each element of a
concatenation gives the same result as applying it to each part and then concatenating. ∎

<a id="t-copies_succ_back"></a>
## Theorem: the last copy of the copy tower (T.copies_succ_back)

### Theorem

For $`d, n \in \mathbb{N}`$ and $`B \in \mathrm{PairSeq}`$,

```math
\mathrm{cp}_d(B, n+1) = \mathrm{cp}_d(B, n) \mathbin{+\!\!+} B^{+nd} .
```

### Proof

By the definition of $`\mathrm{cp}_d`$ (D.copies), $`\mathrm{cp}_d(B, n+1)`$ is the concatenation of
the $`B^{+kd}`$ as the index $`k`$ runs from $`0`$ to $`n`$, that is, over an index sequence of
length $`n+1`$. Splitting that index sequence into its first $`n`$ indices and the last one
$`k = n`$ gives

```math
\mathrm{cp}_d(B, n+1)
 = \bigl(B^{+0\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d}\bigr) \mathbin{+\!\!+} B^{+nd}
```

and the part inside the parentheses is $`\mathrm{cp}_d(B, n)`$ itself. ∎

<a id="t-asc_crux1_of_argdom"></a>
## Theorem: the crux with the head removed, from argument domination (T.asc_crux1_of_argdom)

### Theorem

If $`\mathrm{AscArgDom}`$, then $`\mathrm{AscCrux1}`$ ([D.AscCrux1](Cofinality-2.md#d-AscCrux1)).

### Proof

Let $`G, R, S \in \mathrm{PairSeq}`$ and $`v_0, w_0, d_0 \in \mathbb{N}`$, and assume the five
hypotheses of $`\mathrm{AscCrux1}`$:

```math
\begin{aligned}
&(1)\ H \in \mathrm{ST\_PS}
  \quad\bigl(H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} ((v_0+d_0,\ w_0+1)),\ B := (v_0,w_0) :: R\bigr), \cr
&(2)\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS}, \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ 0 \lt d_0, \cr
&(5)\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert
\end{aligned}
```

Applying $`\mathrm{AscArgDom}`$ to these (1)–(5) gives an $`m`$ together with

```math
(\ast)\qquad S_{\mathrm{hi}} \preceq_{\mathrm{lex}}
  \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0},
\qquad
S_{\mathrm{hi}} := \mathrm{tw}_{v_0+d_0} S,\quad B' := B^{+d_0}
```

Setting further $`S_{\mathrm{lo}} := \mathrm{dw}_{v_0+d_0} S`$, we have
$`S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}} = S`$.
Also, by the definition of $`X^{+d}`$ (D.shiftr0),

```math
B' = B^{+d_0} = (v_0 + d_0,\ w_0) :: R^{+d_0}
```

**Step 1: $`\forall x \in R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m),\ v_0 \lt x_1`$.**
For $`x \in R`$ this is (3). For $`x \in \mathrm{cp}_{d_0}(B', m)`$ argue as follows.
By (3) we have $`\forall y \in R,\ v_0 \le y_1`$, so applying
[T.mem_shiftr0_le](Cofinality-2.md#t-mem_shiftr0_le) with $`d := v_0`$ and $`e := d_0`$ gives
$`\forall y \in R^{+d_0},\ v_0 + d_0 \le y_1`$.
Applying [T.copies_v0_le](Cnf-3.md#t-copies_v0_le) with base point $`v_0 + d_0`$, with value
$`w_0`$ in row $`1`$, with tail $`R^{+d_0}`$ (that is, $`B' = (v_0+d_0,\ w_0) :: R^{+d_0}`$), and
with $`d := d_0`$, $`n := m`$, gives $`v_0 + d_0 \le x_1`$. By (4), $`v_0 \lt v_0 + d_0 \le x_1`$.

**Step 2: $`S_{\mathrm{lo}} = ()`$ or $`(\mathrm{head}\,S_{\mathrm{lo}})_1 \le v_0 + d_0`$.**
If $`S_{\mathrm{lo}} = \mathrm{dw}_{v_0+d_0} S`$ is not the empty sequence, then its first element
$`z`$ fails the predicate, that is, satisfies $`\neg(v_0 + d_0 \lt z_1)`$, so
$`z_1 \le v_0 + d_0`$.

**Step 3: unfolding the goal.**
As the index sought we take $`m + 2`$ (indeed $`1 \le m+2`$).
Put $`E := \bigl((B')^{+m d_0}\bigr)^{+d_0}`$.

```math
\begin{aligned}
\bigl(\mathrm{cp}_{d_0}(B,\ m+2)\bigr)^{+d_0}
 &= \mathrm{cp}_{d_0}(B',\ m+2) \cr
 &= B' \mathbin{+\!\!+} \bigl(\mathrm{cp}_{d_0}(B',\ m+1)\bigr)^{+d_0} \cr
 &= B' \mathbin{+\!\!+} \Bigl(\bigl(\mathrm{cp}_{d_0}(B',\ m)\bigr)^{+d_0} \mathbin{+\!\!+} E\Bigr) \cr
 &= (v_0+d_0,\ w_0) :: \Bigl(R^{+d_0} \mathbin{+\!\!+}
      \bigl(\mathrm{cp}_{d_0}(B',\ m)\bigr)^{+d_0} \mathbin{+\!\!+} E\Bigr) \cr
 &= (v_0+d_0,\ w_0) :: \Bigl(\bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',\ m)\bigr)^{+d_0}
      \mathbin{+\!\!+} E\Bigr).
\end{aligned}
```

The first equality is [T.shiftr0_copies](Cofinality-2.md#t-shiftr0_copies) (with $`B' = B^{+d_0}`$),
the second is [T.copies_succ_front](Cnf-3.md#t-copies_succ_front),
the third is [T.copies_succ_back](#t-copies_succ_back) with [T.shiftr0_append](#t-shiftr0_append),
the fourth is $`B' = (v_0+d_0,\ w_0) :: R^{+d_0}`$ with associativity,
and the fifth is [T.shiftr0_append](#t-shiftr0_append).

**Step 4: the shape of $`E`$.**
We have $`B' = (v_0+d_0,\ w_0) :: R^{+d_0} \ne ()`$, and using
[T.shiftr0_length](Cofinality-2.md#t-shiftr0_length) twice gives $`\lvert E\rvert = \lvert B'\rvert \gt 0`$,
that is, $`E \ne ()`$. Moreover the definition of $`X^{+d}`$ (D.shiftr0) sends the first element to
the first element, so the first element of $`E`$, the one corresponding to the first element
$`(v_0+d_0,\ w_0)`$ of $`B'`$, is $`\bigl(v_0 + d_0 + m d_0 + d_0,\ w_0\bigr)`$, and

```math
(\mathrm{head}\,E)_1 = v_0 + d_0 + m d_0 + d_0 .
```

**Step 5: cancelling the head.**
By Step 3, what is to be shown is

```math
(v_0+d_0,\ w_0) :: S \ \preceq_{\mathrm{lex}}\
 (v_0+d_0,\ w_0) :: \Bigl(\bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0} \mathbin{+\!\!+} E\Bigr)
```

Both sides are concatenations having the sequence $`\bigl((v_0+d_0,\ w_0)\bigr)`$ of length $`1`$ as
their common left part, so by [T.sle_append_cancel](Cofinality.md#t-sle_append_cancel) this is
equivalent to

```math
S \ \preceq_{\mathrm{lex}}\
 \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0} \mathbin{+\!\!+} E
```

Distinguish two cases according to the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle) applied to
$`(\ast)`$.

**(a) The case $`S_{\mathrm{hi}} = \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0}`$.**
Since $`S = S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}}`$, what is to be shown is

```math
S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}} \ \preceq_{\mathrm{lex}}\ S_{\mathrm{hi}} \mathbin{+\!\!+} E
```

so by [T.sle_append_cancel](Cofinality.md#t-sle_append_cancel) it suffices to show
$`S_{\mathrm{lo}} \preceq_{\mathrm{lex}} E`$. Distinguish cases according to Step 2.

- The case $`S_{\mathrm{lo}} = ()`$. By Step 4 we have $`E \ne ()`$, so the first clause of the
  definition of $`\prec_{\mathrm{lex}}`$ ([D.seqlex](Seqlex.md#d-seqlex)) gives
  $`() \prec_{\mathrm{lex}} E`$, and the second disjunct of the definition of
  $`\preceq_{\mathrm{lex}}`$ (D.sle) holds.
- The case $`S_{\mathrm{lo}} = z :: Z`$ with $`z_1 \le v_0 + d_0`$. By Step 4 we have $`E \ne ()`$,
  so $`E = e :: E'`$ with $`e_1 = v_0 + d_0 + m d_0 + d_0`$.
  From $`0 \lt d_0`$ in (4) we get $`v_0 + d_0 \lt v_0 + d_0 + m d_0 + d_0`$, hence
  $`z_1 \le v_0 + d_0 \lt e_1`$; by the first disjunct of the definition of
  $`\prec_{\mathrm{p}}`$ ([D.pairlt](Seqlex.md#d-pairlt)) we get $`z \prec_{\mathrm{p}} e`$, and by
  the first disjunct of the third clause of the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex)
  we get $`z :: Z \prec_{\mathrm{lex}} e :: E'`$.

**(b) The case $`S_{\mathrm{hi}} \prec_{\mathrm{lex}} \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0}`$.**
Apply [T.seqlex_splice](Cofinality-2.md#t-seqlex_splice) with $`S_{\mathrm{hi}}`$ as the smaller
sequence, $`\bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0}`$ as the larger one,
$`S_{\mathrm{lo}}`$ as the sequence appended to the smaller one, and $`E`$ as the sequence appended
to the larger one. The hypothesis that remains is the following disjunction.

```math
S_{\mathrm{lo}} = ()
 \quad\vee\quad
\forall x \in \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',m)\bigr)^{+d_0},\
 \mathrm{head}\,S_{\mathrm{lo}} \prec_{\mathrm{p}} x
```

Distinguish cases according to Step 2.

- The case $`S_{\mathrm{lo}} = ()`$. This is the first disjunct.
- The case $`(\mathrm{head}\,S_{\mathrm{lo}})_1 \le v_0 + d_0`$.
  Let $`x \in \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',m)\bigr)^{+d_0}`$. By
  [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) there is $`y \in R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B',m)`$
  with $`x = (y_1 + d_0,\ y_2)`$. By Step 1 we have $`v_0 \lt y_1`$, hence
  $`(\mathrm{head}\,S_{\mathrm{lo}})_1 \le v_0 + d_0 \lt y_1 + d_0 = x_1`$, and the first disjunct
  of the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt) gives
  $`\mathrm{head}\,S_{\mathrm{lo}} \prec_{\mathrm{p}} x`$.

This yields

```math
S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}} \prec_{\mathrm{lex}}
 \bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B', m)\bigr)^{+d_0} \mathbin{+\!\!+} E
```

and since $`S = S_{\mathrm{hi}} \mathbin{+\!\!+} S_{\mathrm{lo}}`$, the goal of Step 5 is obtained as
the second disjunct of the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle). ∎

<a id="t-asc_head_step"></a>
## Theorem: the head step of the ascending-copy crux (T.asc_head_step)

### Theorem

If $`\mathrm{AscCrux1}`$, then $`\mathrm{AscCrux}`$ ([D.AscCrux](Cofinality-2.md#d-AscCrux)).

### Proof

Let $`G, R, S \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0 \in \mathbb{N}`$ and
$`\ell, q \in \mathbb{N}\times\mathbb{N}`$, put $`B := (v_0,w_0) :: R`$ and
$`H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$, and assume the eight hypotheses of
$`\mathrm{AscCrux}`$:

```math
\begin{aligned}
&(1)\ H \in \mathrm{ST\_PS}, \qquad
 (2)\ (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S \in \mathrm{ST\_PS}, \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \qquad
 (4)\ 0 \lt d_0, \cr
&(5)\ \ell_2 = w_0 + 1, \qquad
 (6)\ \ell_1 = v_0 + d_0, \cr
&(7)\ \lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert, \qquad
 (8)\ q \prec_{\mathrm{p}} \ell
\end{aligned}
```

By (5) and (6) both entries of the pair $`\ell`$ are determined, so that
$`\ell = (v_0 + d_0,\ w_0 + 1)`$. Distinguish cases on $`q`$.

**(a) The case $`q = (v_0 + d_0,\ w_0)`$.**
Rewriting (1) and (7) by $`\ell = (v_0+d_0,\ w_0+1)`$ turns them into
$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0+1)\bigr) \in \mathrm{ST\_PS}`$ and
$`\lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert`$ respectively (with $`H`$ rewritten in
the same way). Likewise (2) becomes, by $`q = (v_0+d_0,\ w_0)`$,
$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S \in \mathrm{ST\_PS}`$.
Applying $`\mathrm{AscCrux1}`$ to these together with (3) and (4) gives the required $`m`$ and
$`q :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B,m)\bigr)^{+d_0}`$.

**(b) The case $`q \ne (v_0 + d_0,\ w_0)`$.**
Take $`m := 1`$. By [T.copies_one](Cnf-3.md#t-copies_one) we have
$`\mathrm{cp}_{d_0}(B, 1) = B`$, and by the definition of $`X^{+d}`$ (D.shiftr0)

```math
B^{+d_0} = (v_0 + d_0,\ w_0) :: R^{+d_0}
```

Hence, by the first disjunct of the third clause of the definition of $`\prec_{\mathrm{lex}}`$
(D.seqlex), it suffices to show $`q \prec_{\mathrm{p}} (v_0+d_0,\ w_0)`$.
Substituting $`\ell = (v_0+d_0,\ w_0+1)`$ into (8), the definition of $`\prec_{\mathrm{p}}`$
(D.pairlt) gives

```math
q_1 \lt v_0 + d_0 \quad\text{or}\quad \bigl(q_1 = v_0 + d_0 \ \wedge\ q_2 \lt w_0 + 1\bigr)
```

Also, since equality of pairs is equality of the entries, $`q \ne (v_0+d_0,\ w_0)`$ is equivalent to
$`\neg\bigl(q_1 = v_0 + d_0 \ \wedge\ q_2 = w_0\bigr)`$. Distinguish cases.

- The case $`q_1 \lt v_0 + d_0`$. The first disjunct of the definition of $`\prec_{\mathrm{p}}`$
  (D.pairlt) holds.
- The case $`q_1 = v_0 + d_0`$ and $`q_2 \lt w_0 + 1`$. Then $`q_2 \le w_0`$.
  If $`q_2 = w_0`$, then together with $`q_1 = v_0 + d_0`$ this contradicts the negation above, so
  $`q_2 \ne w_0`$ and therefore $`q_2 \lt w_0`$. The second disjunct of the definition of
  $`\prec_{\mathrm{p}}`$ (D.pairlt) holds.

In either case $`q :: S \prec_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B,1)\bigr)^{+d_0}`$, and the
second disjunct of the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle) gives the conclusion. ∎

<a id="t-seqlex_cof_bad"></a>
## Theorem: cofinality of the fourth branch (T.seqlex_cof_bad)

### Theorem

Assume $`\mathrm{AscCrux}`$. Let $`M, N \in \mathrm{PairSeq}`$ and put
$`j_1 := \lvert M\rvert - 1`$. If

```math
M \in \mathrm{ST\_PS},\quad
N \in \mathrm{ST\_PS},\quad
1 \lt \lvert M\rvert,\quad
\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr),\quad
N \prec_{\mathrm{lex}} M
```

then there is $`n`$ with $`1 \le n`$ such that $`N \preceq_{\mathrm{lex}} M[n]`$.

($`M_{i,j}`$ [D.entry](Pss.md#d-entry), $`M[n]`$ [D.oper](Pss.md#d-oper))

### Proof

**Step 1: block decomposition.**
From $`1 \lt \lvert M\rvert`$ we get $`0 \lt \lvert M\rvert`$, so
[T.hasParent_last_ST_PS](Cofinality.md#t-hasParent_last_ST_PS) gives
$`\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M, j_1),\ j_1\bigr)`$
($`\mathrm{hasParent}`$ [D.hasParent](Pss.md#d-hasParent), $`\mathrm{idx}_1`$ [D.idx1](Pss.md#d-idx1)).
Moreover [T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS) together with the third conjunct of the
definition of $`\mathrm{blockok}`$ ([D.blockok](Seqlex.md#d-blockok)) gives
$`\mathrm{steps}_1(M)`$ ([D.steps1](Seqlex.md#d-steps1)), and
[T.r1ok_ST_PS](Column-3.md#t-r1ok_ST_PS) gives
$`\mathrm{r1ok}(M)`$ ([D.r1ok](Column-2.md#d-r1ok)). Applying [T.oper_bad_blocks_all](Cofinality.md#t-oper_bad_blocks_all) to these
yields $`G, R \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0 \in \mathbb{N}`$ and
$`\ell \in \mathbb{N}\times\mathbb{N}`$ such that, putting $`B := (v_0,w_0) :: R`$,

```math
\begin{aligned}
&(1)\ M = (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell), \cr
&(2)\ \forall n \ge 1,\ M[n] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n), \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ v_0 \lt \ell_1, \cr
&(5)\ \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr) \ \vee\
      \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
            \wedge \lvert G\rvert \to^M_1 j_1\bigr)
\end{aligned}
```

hold.

**Step 2: case distinction on $`N`$.**
By (1) the hypothesis $`N \prec_{\mathrm{lex}} M`$ reads
$`N \prec_{\mathrm{lex}} (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)`$.
Applying [T.seqlex_snoc_cases](Cofinality.md#t-seqlex_snoc_cases) with $`D := G \mathbin{+\!\!+} B`$
splits the situation into the following two cases.

**(a) The case $`N \preceq_{\mathrm{lex}} G \mathbin{+\!\!+} B`$.**
Take $`n := 1`$. By (2) and [T.copies_one](Cnf-3.md#t-copies_one),
$`M[1] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B,1) = G \mathbin{+\!\!+} B`$, so the hypothesis is
exactly the conclusion.

**(b) The case where there are $`q, S`$ with $`N = (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S`$ and
$`q \prec_{\mathrm{p}} \ell`$.**
We first construct an $`m`$ with $`1 \le m`$ satisfying

```math
(\dagger)\qquad q :: S \preceq_{\mathrm{lex}} \bigl(\mathrm{cp}_{d_0}(B, m)\bigr)^{+d_0}
```

Distinguish cases according to the disjunction (5).

**(b-1) The case $`d_0 = 0`$, $`\ell_2 = 0`$, $`\ell_1 = v_0 + 1`$.**
Since $`X^{+0} = X`$ (taking $`d = 0`$ in the definition of $`X^{+d}`$, D.shiftr0, leaves every
element unchanged), $`(\dagger)`$ is the same proposition as
$`q :: S \preceq_{\mathrm{lex}} \mathrm{cp}_0(B, m)`$.
It suffices to apply [T.crux_zero](Cofinality-2.md#t-crux_zero), supplying
$`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S = N \in \mathrm{ST\_PS}`$ as its hypothesis (1),
(3) of the present proof as its hypothesis (2), $`\ell_2 = 0 \wedge \ell_1 = v_0+1`$ as its
hypothesis (3), and $`q \prec_{\mathrm{p}} \ell`$ as its hypothesis (4).

**(b-2) The case $`0 \lt d_0`$, $`\ell_2 = w_0 + 1`$, $`\ell_1 = v_0 + d_0`$,
$`\lvert G\rvert \to^M_1 j_1`$.**
By (1) we have $`\lvert M\rvert = \lvert G \mathbin{+\!\!+} B\rvert + 1`$, hence
$`j_1 = \lvert M\rvert - 1 = \lvert G \mathbin{+\!\!+} B\rvert`$; together with (1) this makes
$`\lvert G\rvert \to^M_1 j_1`$ the same proposition as

```math
\lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert,
\qquad H := (G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)
```

Applying $`\mathrm{AscCrux}`$ with
$`H = M \in \mathrm{ST\_PS}`$, $`(G \mathbin{+\!\!+} B) \mathbin{+\!\!+} q :: S = N \in \mathrm{ST\_PS}`$,
(3) of the present proof, $`0 \lt d_0`$, $`\ell_2 = w_0+1`$, $`\ell_1 = v_0+d_0`$,
the just rewritten $`\lvert G\rvert \to^{H}_1 \lvert G \mathbin{+\!\!+} B\rvert`$ and
$`q \prec_{\mathrm{p}} \ell`$ as its eight hypotheses gives $`(\dagger)`$.

**Step 3: conclusion.**
Take $`n := m + 1`$ (indeed $`1 \le m + 1`$). By (2) and
[T.copies_succ_front](Cnf-3.md#t-copies_succ_front),

```math
M[m+1] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, m+1)
 = G \mathbin{+\!\!+} \Bigl(B \mathbin{+\!\!+} \bigl(\mathrm{cp}_{d_0}(B,m)\bigr)^{+d_0}\Bigr)
```

while the $`N`$ of (b) is, by associativity,
$`N = G \mathbin{+\!\!+} \bigl(B \mathbin{+\!\!+} q :: S\bigr)`$.
Applying [T.sle_append_cancel](Cofinality.md#t-sle_append_cancel) with left part $`G`$, and then
with left part $`B`$, makes the goal $`N \preceq_{\mathrm{lex}} M[m+1]`$ equivalent to
$`(\dagger)`$. ∎

<a id="t-seqlex_cofinality_of_crux"></a>
## Theorem: column-lex cofinality from the crux (T.seqlex_cofinality_of_crux)

### Theorem

If $`\mathrm{AscCrux}`$, then $`\mathrm{SeqlexCofinality}`$ ([D.SeqlexCofinality](Cofinality.md#d-SeqlexCofinality)).

### Proof

Let $`M, N \in \mathrm{PairSeq}`$ and assume $`M \in \mathrm{ST\_PS}`$, $`N \in \mathrm{ST\_PS}`$ and
$`N \prec_{\mathrm{lex}} M`$. Put $`j_1 := \lvert M\rvert - 1`$.
What is sought is an $`n`$ with $`1 \le n`$ satisfying $`N \preceq_{\mathrm{lex}} M[n]`$.

**(a) The case $`j_1 = 0`$.**
Apply [T.seqlex_cof_short](Cofinality.md#t-seqlex_cof_short).

**(b) The case $`j_1 \ne 0`$ and $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$.**
Since subtraction of natural numbers is truncated subtraction, $`\lvert M\rvert - 1 \ne 0`$ is
equivalent to $`1 \lt \lvert M\rvert`$. Apply [T.seqlex_cof_zero](Cofinality.md#t-seqlex_cof_zero).

**(c) The case $`j_1 \ne 0`$ and $`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$.**
As in (b), $`1 \lt \lvert M\rvert`$.
Apply [T.seqlex_cof_bad](#t-seqlex_cof_bad) under the hypothesis $`\mathrm{AscCrux}`$.

The three cases exhaust all possibilities, according to whether $`j_1 = 0`$ or not and whether
$`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ or not. ∎

<a id="t-pss_cofinality_of_crux"></a>
## Theorem: PSS cofinality from the crux (T.pss_cofinality_of_crux)

### Theorem

Assume $`\mathrm{AscCrux1}`$. If $`M, N \in \mathrm{PairSeq}`$ satisfy
$`M \in \mathrm{ST\_PS}`$, $`N \in \mathrm{ST\_PS}`$ and $`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$,
then there is $`n`$ with $`1 \le n`$ such that
$`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$.

($`\prec`$ [D.olt](Term.md#d-olt), $`\preceq`$ [D.ole](Term.md#d-ole))

### Proof

Applying [T.asc_head_step](#t-asc_head_step) to the hypothesis $`\mathrm{AscCrux1}`$ gives $`\mathrm{AscCrux}`$.
Applying [T.seqlex_cofinality_of_crux](#t-seqlex_cofinality_of_crux) to this gives
$`\mathrm{SeqlexCofinality}`$.
Applying [T.pss_cofinality_of_seqlex](Cofinality.md#t-pss_cofinality_of_seqlex) to this, together
with $`M`$, $`N`$ and the three hypotheses $`M \in \mathrm{ST\_PS}`$, $`N \in \mathrm{ST\_PS}`$,
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$, gives the conclusion. ∎

<a id="t-pss_cofinality_of_argdom"></a>
## Theorem: PSS cofinality from argument domination (T.pss_cofinality_of_argdom)

### Theorem

Assume $`\mathrm{AscArgDom}`$. If $`M, N \in \mathrm{PairSeq}`$ satisfy
$`M \in \mathrm{ST\_PS}`$, $`N \in \mathrm{ST\_PS}`$ and $`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$,
then there is $`n`$ with $`1 \le n`$ such that
$`\mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])`$.

### Proof

Applying [T.asc_crux1_of_argdom](#t-asc_crux1_of_argdom) to the hypothesis $`\mathrm{AscArgDom}`$
gives $`\mathrm{AscCrux1}`$. Applying [T.pss_cofinality_of_crux](#t-pss_cofinality_of_crux) to this,
together with $`M`$, $`N`$ and the three hypotheses $`M \in \mathrm{ST\_PS}`$,
$`N \in \mathrm{ST\_PS}`$, $`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$, gives the conclusion. ∎
