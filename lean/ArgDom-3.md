[← README](README.md) | [English](ArgDom-3.md) | [Japanese](ArgDom-3-ja.md) | ArgDom [1](ArgDom.md) [2](ArgDom-2.md) **3** [4](ArgDom-4.md) [5](ArgDom-5.md)

<a id="t-seqlex_of_sle_snoc'"></a>
## Theorem: replacing the trailing column, upper-bound-relative form (T.seqlex_of_sle_snoc')

### Theorem

Let $`X, V, E \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) and $`\ell, q \in \mathbb{N}\times\mathbb{N}`$ satisfy

```math
X \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} E,
\qquad q \prec_{\mathrm{p}} \ell,
\qquad \lvert X\rvert \lt \lvert V\rvert
```

($`\preceq_{\mathrm{lex}}`$ [D.sle](Cofinality.md#d-sle), $`\prec_{\mathrm{p}}`$ [D.pairlt](Seqlex.md#d-pairlt))

Then for all $`S', E' \in \mathrm{PairSeq}`$,

```math
X \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V \mathbin{+\!\!+} E' .
```

($`\prec_{\mathrm{lex}}`$ [D.seqlex](Seqlex.md#d-seqlex))

### Proof

Induction on the constructors of $`X`$ (the variables $`V, E, \ell, q, S', E'`$ stay universally quantified).
Show

```math
\begin{aligned}
&\Phi(X) :\equiv \forall V, E, \ell, q,\
  \bigl(X \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} E \cr
&\qquad \wedge q \prec_{\mathrm{p}} \ell \wedge \lvert X\rvert \lt \lvert V\rvert\bigr) \cr
&\qquad \to \forall S', E',\
  X \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V \mathbin{+\!\!+} E'
\end{aligned}
```

for every $`X`$.

**Base case** $`X = ()`$. Since $`\lvert V\rvert \gt 0`$, we may write $`V = v :: V'`$
(if $`V = ()`$ then $`\lvert V\rvert = 0`$, contradicting $`0 \lt \lvert V\rvert`$).
What is to be shown is $`q :: S' \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E')`$, and by the third clause of
the definition of $`\prec_{\mathrm{lex}}`$ (D.seqlex) it suffices to show its first disjunct $`q \prec_{\mathrm{p}} v`$.
The hypothesis reads $`(\ell) \preceq_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E)`$; distinguish cases by
the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle).

- Case $`(\ell) = v :: (V' \mathbin{+\!\!+} E)`$. Comparing the head elements of the two sides gives $`\ell = v`$.
  The hypothesis $`q \prec_{\mathrm{p}} \ell`$ is then exactly $`q \prec_{\mathrm{p}} v`$.

- Case $`(\ell) \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E)`$. Since $`(\ell) = \ell :: ()`$,
  the third clause of D.seqlex gives $`\ell \prec_{\mathrm{p}} v`$ or
  $`\ell = v \wedge () \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$.
  In the former case, applying [T.pairlt_trans](Cofinality.md#t-pairlt_trans) to
  $`q \prec_{\mathrm{p}} \ell`$ and $`\ell \prec_{\mathrm{p}} v`$ yields $`q \prec_{\mathrm{p}} v`$.
  In the latter case, substituting $`\ell = v`$ into $`q \prec_{\mathrm{p}} \ell`$ yields $`q \prec_{\mathrm{p}} v`$.

**Inductive step** $`X = x :: X'`$. Assume $`\Phi(X')`$.
From $`\lvert x :: X'\rvert \lt \lvert V\rvert`$ we get $`V \ne ()`$, so $`V = v :: V'`$,
and then $`\lvert X'\rvert + 1 \lt \lvert V'\rvert + 1`$, that is, $`\lvert X'\rvert \lt \lvert V'\rvert`$.
The hypothesis reads

```math
x :: \bigl(X' \mathbin{+\!\!+} (\ell)\bigr) \preceq_{\mathrm{lex}} v :: \bigl(V' \mathbin{+\!\!+} E\bigr)
```

and what is to be shown is
$`x :: (X' \mathbin{+\!\!+} q :: S') \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E')`$,
that is, by the third clause of D.seqlex,

```math
x \prec_{\mathrm{p}} v
\quad\text{or}\quad
\bigl(x = v \wedge X' \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E'\bigr)
```

Distinguish cases on the hypothesis by D.sle.

- Case of the equality $`x :: (X' \mathbin{+\!\!+} (\ell)) = v :: (V' \mathbin{+\!\!+} E)`$.
  Comparing the head elements gives $`x = v`$, and comparing the tails gives
  $`X' \mathbin{+\!\!+} (\ell) = V' \mathbin{+\!\!+} E`$.
  By the first disjunct of D.sle the latter yields
  $`X' \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$.
  Applying the induction hypothesis $`\Phi(X')`$ with $`V', E, \ell, q`$ (the remaining hypotheses being
  $`q \prec_{\mathrm{p}} \ell`$ and $`\lvert X'\rvert \lt \lvert V'\rvert`$) gives
  $`X' \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E'`$, so the second disjunct holds.

- Case $`x :: (X' \mathbin{+\!\!+} (\ell)) \prec_{\mathrm{lex}} v :: (V' \mathbin{+\!\!+} E)`$.
  The third clause of D.seqlex splits this into two.

  - Case $`x \prec_{\mathrm{p}} v`$. This is the first disjunct itself.
  - Case $`x = v \wedge X' \mathbin{+\!\!+} (\ell) \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$.
    By the second disjunct of D.sle the second conjunct yields
    $`X' \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V' \mathbin{+\!\!+} E`$.
    Applying the induction hypothesis $`\Phi(X')`$ with $`V', E, \ell, q`$ (the remaining hypotheses being
    $`q \prec_{\mathrm{p}} \ell`$ and $`\lvert X'\rvert \lt \lvert V'\rvert`$) gives
    $`X' \mathbin{+\!\!+} q :: S' \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E'`$, which together with
    $`x = v`$ establishes the second disjunct. ∎

<a id="t-argDomCoreOn_bad_B"></a>
## Theorem: case B of the fourth branch of the expansion (T.argDomCoreOn_bad_B)

### Theorem

Let $`M, G, R \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0, n \in \mathbb{N}`$, $`\ell \in \mathbb{N}\times\mathbb{N}`$,
$`\mathrm{blk} := (v_0,w_0) :: R`$, and assume unchanged the hypotheses
(hM), (hMon), (hMeq), (hRgt), (hlp), (hdisj), (hSTn), (hIH), (hn) of
[T.argDomCoreOn_bad_A1](ArgDom-2.md#t-argDomCoreOn_bad_A1) together with
(heq), (he), (h1), (h2), (h3), (h4), (h5), (h6) concerning $`X, A_1, B, A_2, Z, u, w, e`$.
Assume moreover

```math
\text{(hcase)}\qquad
\lvert X\rvert + (\lvert A_1\rvert + 1) \lt \lvert G\rvert + (\lvert R\rvert + 1)
```

Then

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e} .
```

($`L^{+d}`$ [D.shiftr0](Cnf-2.md#d-shiftr0))

### Proof

By (hn) write $`n = m + 1`$. Put

```math
T := \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0},
\qquad
C_p := X \mathbin{+\!\!+} (u,w) :: \bigl(A_1 \mathbin{+\!\!+} ((u+e,w))\bigr)
```

($`\mathrm{copies}_d(B, n)`$ [D.copies](Cnf-2.md#d-copies))

Here $`C_p`$ is the part of the decomposition running from its front through the deeper marked column
$`(u+e,w)`$, and $`\lvert C_p\rvert = \lvert X\rvert + 1 + (\lvert A_1\rvert + 1)`$.

**Step 1: cut at the common part.**
By [T.copies_succ_front](Cnf-3.md#t-copies_succ_front) and associativity of concatenation,

```math
G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1) = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} T
```

Rearranging the right-hand side of (heq) by associativity also gives

```math
(G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} T
 = C_p \mathbin{+\!\!+} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

The lengths are

```math
\lvert C_p\rvert = \lvert X\rvert + \bigl(\lvert A_1\rvert + 1\bigr) + 1,
\qquad
\lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert = \lvert G\rvert + (\lvert R\rvert + 1)
```

Since in $`\mathbb{N}`$ the statement $`a \lt b`$ is equivalent to $`a + 1 \le b`$, (hcase) gives

```math
\lvert C_p\rvert = \bigl(\lvert X\rvert + (\lvert A_1\rvert + 1)\bigr) + 1
  \le \lvert G\rvert + (\lvert R\rvert + 1) = \lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert
```

Applying [T.split_prefix_left](ArgDom-2.md#t-split_prefix_left) and putting
$`D := \mathrm{drop}_{\lvert C_p\rvert}(G \mathbin{+\!\!+} \mathrm{blk})`$, we obtain

```math
G \mathbin{+\!\!+} \mathrm{blk} = C_p \mathbin{+\!\!+} D,
\qquad
B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} T
```

Combining the first equality with (hMeq), associativity gives

```math
M = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} (\ell)
  = \bigl(C_p \mathbin{+\!\!+} D\bigr) \mathbin{+\!\!+} (\ell)
  = C_p \mathbin{+\!\!+} \bigl(D \mathbin{+\!\!+} (\ell)\bigr)
```

That is, $`M`$ is $`C_p`$ followed on the right by $`D \mathbin{+\!\!+} (\ell)`$.

**Step 2: apply (hMon) to the decomposition of $`M`$.**
We show the following. If $`B', A_2', Z' \in \mathrm{PairSeq}`$ satisfy

```math
D \mathbin{+\!\!+} (\ell) = B' \mathbin{+\!\!+} (A_2' \mathbin{+\!\!+} Z'),
\qquad \forall x \in B',\ u + e \lt x_1,
\qquad \forall x \in A_2',\ u \lt x_1,
```
```math
A_2' = () \ \vee\ (\mathrm{head}\,A_2')_1 \le u+e,
\qquad
Z' = () \ \vee\ (\mathrm{head}\,Z')_1 \le u
```

then

```math
B' \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B'^{+e} .
```

Indeed, substituting the assumed decomposition into the identity $`M = C_p \mathbin{+\!\!+} (D \mathbin{+\!\!+} (\ell))`$
of Step 1 and rearranging with the definition of $`C_p`$ and associativity,

```math
M = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B' \mathbin{+\!\!+} A_2'))\bigr) \mathbin{+\!\!+} Z'
```

This is the shape of decomposition required by [D.ArgDomCoreOn](ArgDom.md#d-ArgDomCoreOn), so applying
(hMon) to this decomposition together with (he), (h1), the four conditions on $`B'`$, $`A_2'`$, $`Z'`$
listed above, and (h6) gives

```math
B' \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+e}
```

By [T.argbound_split](ArgDom-2.md#t-argbound_split) the right-hand side equals

```math
\bigl(A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B'^{+e}\bigr) \mathbin{+\!\!+} A_2'^{+e}
```

and by [T.argbound_len](ArgDom-2.md#t-argbound_len) we have
$`\lvert B'\rvert \le \lvert A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B'^{+e}\rvert`$.
Applying [T.sle_take_of_short](ArgDom.md#t-sle_take_of_short) gives the assertion.

**Step 3: bring the conclusion into the same shape.**
The conclusion follows once

```math
B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}
```

is shown. Indeed, by [T.argbound_split](ArgDom-2.md#t-argbound_split) the right-hand side of the conclusion is
$`(A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}) \mathbin{+\!\!+} A_2^{+e}`$,
so it suffices to apply [T.sle_append_mono](Cofinality.md#t-sle_append_mono) with
$`C := A_2^{+e}`$. The rest of the proof establishes this form.

**Step 4: distinguish cases according to $`\lvert B\rvert`$ and $`\lvert D\rvert`$.**

**(a) The case $`\lvert B\rvert \lt \lvert D\rvert`$.**
Applying [T.split_prefix_right](ArgDom-2.md#t-split_prefix_right) to the identity
$`B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} T`$ of Step 1 and to $`\lvert B\rvert \le \lvert D\rvert`$,
and putting $`D_r := \mathrm{drop}_{\lvert B\rvert} D`$, we obtain

```math
D = B \mathbin{+\!\!+} D_r,
\qquad
A_2 \mathbin{+\!\!+} Z = D_r \mathbin{+\!\!+} T
```

First, $`D_r \ne ()`$. If $`D_r = ()`$ then $`D = B`$, whence
$`\lvert B\rvert \lt \lvert D\rvert = \lvert B\rvert`$, a contradiction.
Therefore $`A_2 \mathbin{+\!\!+} Z = D_r \mathbin{+\!\!+} T \ne ()`$, and
[T.headI_append_left](Seqlex-2.md#t-headI_append_left) gives
$`\mathrm{head}(A_2 \mathbin{+\!\!+} Z) = \mathrm{head}\,D_r`$.

Next we show $`(\mathrm{head}\,D_r)_1 \le u + e`$, distinguishing cases according to whether $`A_2`$ is empty.

- Case $`A_2 = ()`$. Then $`A_2 \mathbin{+\!\!+} Z = Z`$, which is non-empty, so the first disjunct
  $`Z = ()`$ of (h5) is false. Hence the second disjunct gives
  $`(\mathrm{head}\,Z)_1 \le u \le u + e`$, and
  $`\mathrm{head}\,D_r = \mathrm{head}(A_2 \mathbin{+\!\!+} Z) = \mathrm{head}\,Z`$.

- Case $`A_2 \ne ()`$. Then [T.headI_append_left](Seqlex-2.md#t-headI_append_left) gives
  $`\mathrm{head}(A_2 \mathbin{+\!\!+} Z) = \mathrm{head}\,A_2`$, and since the first disjunct of (h4) is false,
  its second disjunct gives $`(\mathrm{head}\,A_2)_1 \le u + e`$.

Apply [T.arg_split](ArgDom-2.md#t-arg_split) with $`L := u`$ and $`E := D_r \mathbin{+\!\!+} (\ell)`$
to obtain $`A_2', Z'`$; that is,

```math
D_r \mathbin{+\!\!+} (\ell) = A_2' \mathbin{+\!\!+} Z',
\qquad \forall x \in A_2',\ u \lt x_1,
\qquad Z' = () \vee (\mathrm{head}\,Z')_1 \le u .
```

We show $`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u+e`$. If $`A_2' = ()`$, the first disjunct holds.
If $`A_2' \ne ()`$, then [T.headI_append_left](Seqlex-2.md#t-headI_append_left) gives
$`\mathrm{head}(D_r \mathbin{+\!\!+} (\ell)) = \mathrm{head}\,A_2'`$, and since
$`D_r \ne ()`$ the same theorem again gives
$`\mathrm{head}(D_r \mathbin{+\!\!+} (\ell)) = \mathrm{head}\,D_r`$.
Hence $`(\mathrm{head}\,A_2')_1 = (\mathrm{head}\,D_r)_1 \le u+e`$.

Apply the assertion of Step 2 with $`B' := B`$, $`A_2'`$, $`Z'`$. The decomposition condition is

```math
D \mathbin{+\!\!+} (\ell) = (B \mathbin{+\!\!+} D_r) \mathbin{+\!\!+} (\ell)
 = B \mathbin{+\!\!+} \bigl(D_r \mathbin{+\!\!+} (\ell)\bigr)
 = B \mathbin{+\!\!+} \bigl(A_2' \mathbin{+\!\!+} Z'\bigr)
```

the condition $`\forall x \in B,\ u+e \lt x_1`$ is (h2), and the remaining three conditions were verified above. Hence

```math
B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}
```

and the conclusion follows by Step 3.

**(b) The case $`\lvert D\rvert \le \lvert B\rvert`$.**
Applying [T.split_prefix_left](ArgDom-2.md#t-split_prefix_left) to
$`B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} T`$
and putting $`B_2 := \mathrm{drop}_{\lvert D\rvert} B`$, we obtain

```math
B = D \mathbin{+\!\!+} B_2,
\qquad
T = B_2 \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)
```

Since every element of $`D`$ is an element of $`B`$, (h2) gives
$`\forall x \in D,\ u+e \lt x_1`$.

**Auxiliary 1 for Step 4 (b): the head of $`B_2`$ when it is non-empty.**
If $`B_2 = q :: B_2'`$, then $`q = (v_0+d_0,\ w_0)`$.
First, $`m \ne 0`$. If $`m = 0`$ then
[T.copies_zero](Cnf-2.md#t-copies_zero) and [T.shiftr0_nil](Cnf-2.md#t-shiftr0_nil) give $`T = ()`$, whereas
the right-hand side of $`T = B_2 \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)`$ contains $`B_2 = q :: B_2'`$ and hence is non-empty, a contradiction.
So write $`m = m' + 1`$.
By [T.copies_succ_cons](Cnf-3.md#t-copies_succ_cons),

```math
\mathrm{copies}_{d_0}(\mathrm{blk}, m'+1)
 = (v_0, w_0) :: \Bigl(R \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m')\bigr)^{+d_0}\Bigr)
```

and by [T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons),

```math
T = (v_0 + d_0,\ w_0) :: \Bigl(R \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m')\bigr)^{+d_0}\Bigr)^{+d_0}
```

On the other hand $`T = B_2 \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = q :: \bigl(B_2' \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)`$,
so injectivity of cons gives $`q = (v_0+d_0,\ w_0)`$.

**Auxiliary 2 for Step 4 (b): comparison of $`q`$ and $`\ell`$.**
When $`B_2 = q :: B_2'`$, the following two statements hold.

- $`q_1 \le \ell_1`$. In the case of the first disjunct of (hdisj) we have $`d_0 = 0`$ and $`\ell_1 = v_0 + 1`$, so
  $`q_1 = v_0 + d_0 = v_0 \le v_0 + 1 = \ell_1`$.
  In the case of the second disjunct, $`\ell_1 = v_0 + d_0 = q_1`$.

- $`q \prec_{\mathrm{p}} \ell`$. In the case of the first disjunct of (hdisj) we have
  $`q_1 = v_0 \lt v_0 + 1 = \ell_1`$, so the first disjunct of the definition of $`\prec_{\mathrm{p}}`$ (D.pairlt) holds.
  In the case of the second disjunct we have $`q_1 = v_0 + d_0 = \ell_1`$ and $`q_2 = w_0 \lt w_0 + 1 = \ell_2`$, so
  the second disjunct of D.pairlt holds.

Distinguish cases according to $`u+e`$ and $`\ell_1`$.

**(b-1) The case $`u + e \lt \ell_1`$.**
Here $`\forall x \in D \mathbin{+\!\!+} (\ell),\ u+e \lt x_1`$
(for $`x \in D`$ by what was shown above, for $`x = \ell`$ by the assumption of the present case).
Apply the assertion of Step 2 with $`B' := D \mathbin{+\!\!+} (\ell)`$, $`A_2' := ()`$, $`Z' := ()`$.
The decomposition condition is $`D \mathbin{+\!\!+} (\ell) = (D \mathbin{+\!\!+} (\ell)) \mathbin{+\!\!+} (() \mathbin{+\!\!+} ())`$;
$`A_2' = ()`$ has no elements and its head condition is the first disjunct; the same holds for $`Z' = ()`$. Hence

```math
D \mathbin{+\!\!+} (\ell)
 \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: \bigl(D \mathbin{+\!\!+} (\ell)\bigr)^{+e} .
```

By [T.shiftr0_append](Cofinality-3.md#t-shiftr0_append) and associativity of concatenation, putting
$`V := A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: D^{+e}`$, the right-hand side equals
$`V \mathbin{+\!\!+} (\ell)^{+e}`$. That is,

```math
(\dagger)\qquad D \mathbin{+\!\!+} (\ell) \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} (\ell)^{+e} .
```

Note that [T.shiftr0_length](Cofinality-2.md#t-shiftr0_length) gives
$`\lvert V\rvert = \lvert A_1\rvert + 1 + \lvert D\rvert`$. Distinguish cases according to $`B_2`$.

**The case $`B_2 = ()`$.** Here $`B = D \mathbin{+\!\!+} () = D`$.
Applying [T.sle_of_append_left](ArgDom.md#t-sle_of_append_left) to $`(\dagger)`$ gives
$`D \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} (\ell)^{+e}`$.
Since $`\lvert D\rvert \le \lvert A_1\rvert + 1 + \lvert D\rvert = \lvert V\rvert`$, applying
[T.sle_take_of_short](ArgDom.md#t-sle_take_of_short) gives $`D \preceq_{\mathrm{lex}} V`$.
As $`B = D`$, this is exactly
$`B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}`$.
The conclusion follows by Step 3.

**The case $`B_2 = q :: B_2'`$.** Here $`\lvert D\rvert \lt \lvert A_1\rvert + 1 + \lvert D\rvert = \lvert V\rvert`$.
Apply [T.seqlex_of_sle_snoc'](#t-seqlex_of_sle_snoc'), matching the sequences and pairs occurring in its statement with
$`D`$, $`V`$, $`(\ell)^{+e}`$, $`\ell`$, $`q`$ in this order.
Its three hypotheses are $`(\dagger)`$, the relation $`q \prec_{\mathrm{p}} \ell`$ of Auxiliary 2, and the inequality $`\lvert D\rvert \lt \lvert V\rvert`$ just shown.
Taking the two universally quantified sequences in the conclusion to be $`B_2'`$ and $`(q_1+e,\ q_2) :: B_2'^{+e}`$ gives

```math
D \mathbin{+\!\!+} q :: B_2'
 \prec_{\mathrm{lex}} V \mathbin{+\!\!+} \bigl((q_1+e,\ q_2) :: B_2'^{+e}\bigr)
```

The left-hand side is $`B = D \mathbin{+\!\!+} B_2 = D \mathbin{+\!\!+} q :: B_2'`$.
By [T.shiftr0_append](Cofinality-3.md#t-shiftr0_append),
[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons) and associativity, the right-hand side equals

```math
\begin{aligned}
&V \mathbin{+\!\!+} \bigl((q_1+e,\ q_2) :: B_2'^{+e}\bigr) \cr
&\qquad = A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) \cr
&\qquad\qquad :: \bigl(D^{+e} \mathbin{+\!\!+} (q_1+e,\ q_2) :: B_2'^{+e}\bigr) \cr
&\qquad = A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}
\end{aligned}
```

Hence the second disjunct of the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle) gives
$`B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}`$, and
the conclusion follows by Step 3.

**(b-2) The case $`\neg(u + e \lt \ell_1)`$.**
First, $`B_2 = ()`$. If $`B_2 = q :: B_2'`$, then $`q`$ is an element of $`B = D \mathbin{+\!\!+} B_2`$, so
(h2) gives $`u + e \lt q_1`$; Auxiliary 2 gives $`q_1 \le \ell_1`$, and the assumption of the present case gives
$`\ell_1 \le u+e`$, whence $`u+e \lt q_1 \le \ell_1 \le u+e`$, a contradiction.
Therefore $`B = D`$, and $`D \mathbin{+\!\!+} (\ell) = B \mathbin{+\!\!+} (\ell)`$.
Distinguish further cases according to $`u`$ and $`\ell_1`$.

- Case $`u \lt \ell_1`$. Apply the assertion of Step 2 with $`B' := B`$, $`A_2' := (\ell)`$, $`Z' := ()`$.
  The decomposition condition is $`B \mathbin{+\!\!+} (\ell) = B \mathbin{+\!\!+} ((\ell) \mathbin{+\!\!+} ())`$;
  $`\forall x \in B,\ u+e \lt x_1`$ is (h2);
  $`\forall x \in (\ell),\ u \lt x_1`$ is the assumption $`u \lt \ell_1`$ of the present case;
  $`(\mathrm{head}(\ell))_1 = \ell_1 \le u+e`$ is the assumption of (b-2);
  and $`Z' = ()`$ is the first disjunct.

- Case $`\neg(u \lt \ell_1)`$, that is, $`\ell_1 \le u`$.
  Apply the assertion of Step 2 with $`B' := B`$, $`A_2' := ()`$, $`Z' := (\ell)`$.
  The decomposition condition is $`B \mathbin{+\!\!+} (\ell) = B \mathbin{+\!\!+} (() \mathbin{+\!\!+} (\ell))`$;
  $`A_2' = ()`$ has no elements and its head condition is the first disjunct;
  and $`(\mathrm{head}(\ell))_1 = \ell_1 \le u`$.

In either case we obtain
$`B \preceq_{\mathrm{lex}} A_1^{+e} \mathbin{+\!\!+} (u+e+e,w) :: B^{+e}`$, and
the conclusion follows by Step 3. ∎

<a id="t-shiftr0_add"></a>
## Theorem: composition of shifts (T.shiftr0_add)

### Theorem

For $`a, b \in \mathbb{N}`$ and $`X \in \mathrm{PairSeq}`$,

```math
X^{+(a+b)} = \bigl(X^{+b}\bigr)^{+a} .
```

### Proof

Since $`L^{+d}`$ replaces each element $`p`$ by $`(p_1 + d,\ p_2)`$,
the left-hand side is the sequence obtained from $`X`$ by replacing each element $`p`$ by $`(p_1 + (a+b),\ p_2)`$,
while the right-hand side is the sequence obtained by replacing $`p`$ first by $`(p_1 + b,\ p_2)`$ and then by $`((p_1 + b) + a,\ p_2)`$.
By associativity and commutativity of addition in $`\mathbb{N}`$,

```math
p_1 + (a+b) = (p_1 + b) + a
```

so the two replacements give the same value at each element. If the elementwise replacements agree,
the whole sequences agree as well. ∎

<a id="t-sle_of_prefix"></a>
## Theorem: a prefix is smaller in the weak sense (T.sle_of_prefix)

### Theorem

Let $`X, Y \in \mathrm{PairSeq}`$, and define $`X \sqsubseteq Y`$ by

```math
X \sqsubseteq Y :\iff \exists t \in \mathrm{PairSeq},\ Y = X \mathbin{+\!\!+} t
```

($`X`$ is a **prefix** of $`Y`$). If $`X \sqsubseteq Y`$ then
$`X \preceq_{\mathrm{lex}} Y`$.

### Proof

Take $`t`$ with $`Y = X \mathbin{+\!\!+} t`$ and distinguish cases according to the constructor of $`t`$.

- Case $`t = ()`$. Then $`Y = X \mathbin{+\!\!+} () = X`$, so
  the first disjunct of the definition of $`\preceq_{\mathrm{lex}}`$ (D.sle) holds.

- Case $`t = a :: t'`$. Then $`t \ne ()`$, so applying
  [T.seqlex_prefix](Seqlex.md#t-seqlex_prefix) with $`v := t`$ and $`u := X`$ gives
  $`X \prec_{\mathrm{lex}} X \mathbin{+\!\!+} t = Y`$. Hence the second disjunct of D.sle holds. ∎

<a id="t-shiftr0_prefix"></a>
## Theorem: shifting preserves the prefix relation (T.shiftr0_prefix)

### Theorem

Let $`d \in \mathbb{N}`$ and $`X, Y \in \mathrm{PairSeq}`$. If $`X \sqsubseteq Y`$ then
$`X^{+d} \sqsubseteq Y^{+d}`$.

### Proof

Take $`t`$ with $`Y = X \mathbin{+\!\!+} t`$.
By [T.shiftr0_append](Cofinality-3.md#t-shiftr0_append),

```math
Y^{+d} = \bigl(X \mathbin{+\!\!+} t\bigr)^{+d} = X^{+d} \mathbin{+\!\!+} t^{+d}
```

Hence $`t^{+d}`$ is a witness for $`X^{+d} \sqsubseteq Y^{+d}`$. ∎

<a id="t-prefix_append_left"></a>
## Theorem: a common left factor and prefixes (T.prefix_append_left)

### Theorem

Let $`P, X, Y \in \mathrm{PairSeq}`$. If $`X \sqsubseteq Y`$ then
$`P \mathbin{+\!\!+} X \sqsubseteq P \mathbin{+\!\!+} Y`$.

### Proof

Take $`t`$ with $`Y = X \mathbin{+\!\!+} t`$. By associativity of concatenation,

```math
P \mathbin{+\!\!+} Y = P \mathbin{+\!\!+} \bigl(X \mathbin{+\!\!+} t\bigr) = \bigl(P \mathbin{+\!\!+} X\bigr) \mathbin{+\!\!+} t
```

Hence $`t`$ is a witness for $`P \mathbin{+\!\!+} X \sqsubseteq P \mathbin{+\!\!+} Y`$. ∎

<a id="t-copies_length"></a>
## Theorem: the length of a copy tower (T.copies_length)

### Theorem

For $`d \in \mathbb{N}`$, $`\mathrm{blk} \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$,

```math
\bigl\lvert \mathrm{copies}_d(\mathrm{blk}, n)\bigr\rvert = n \cdot \lvert \mathrm{blk}\rvert .
```

### Proof

Induction on $`n`$ (with $`d`$ and $`\mathrm{blk}`$ fixed). Show

```math
\Phi(n) :\equiv \bigl\lvert \mathrm{copies}_d(\mathrm{blk}, n)\bigr\rvert = n \cdot \lvert \mathrm{blk}\rvert
```

for every $`n`$.

- **Base case** $`n = 0`$: [T.copies_zero](Cnf-2.md#t-copies_zero) gives
  $`\mathrm{copies}_d(\mathrm{blk}, 0) = ()`$, whose length is $`0`$;
  and $`0 \cdot \lvert \mathrm{blk}\rvert = 0`$.

**Inductive step** $`n = k + 1`$. Assume $`\Phi(k)`$, that is,
$`\lvert \mathrm{copies}_d(\mathrm{blk}, k)\rvert = k \cdot \lvert \mathrm{blk}\rvert`$.
By [T.copies_succ_back](Cofinality-3.md#t-copies_succ_back),

```math
\mathrm{copies}_d(\mathrm{blk}, k+1)
 = \mathrm{copies}_d(\mathrm{blk}, k) \mathbin{+\!\!+} \mathrm{blk}^{+k d}
```

so, the length of a concatenation being the sum of the lengths of its factors,

```math
\bigl\lvert \mathrm{copies}_d(\mathrm{blk}, k+1)\bigr\rvert
 = \bigl\lvert \mathrm{copies}_d(\mathrm{blk}, k)\bigr\rvert + \bigl\lvert \mathrm{blk}^{+k d}\bigr\rvert .
```

By [T.shiftr0_length](Cofinality-2.md#t-shiftr0_length) we have
$`\lvert \mathrm{blk}^{+k d}\rvert = \lvert \mathrm{blk}\rvert`$, and together with the induction hypothesis this gives

```math
\bigl\lvert \mathrm{copies}_d(\mathrm{blk}, k+1)\bigr\rvert
 = k \cdot \lvert \mathrm{blk}\rvert + \lvert \mathrm{blk}\rvert = (k+1) \cdot \lvert \mathrm{blk}\rvert
```

Hence $`\Phi(k+1)`$. ∎

<a id="t-split_append_left"></a>
## Theorem: existential form of the splitting (T.split_append_left)

### Theorem

If $`C, D, E, F \in \mathrm{PairSeq}`$ satisfy $`C \mathbin{+\!\!+} D = E \mathbin{+\!\!+} F`$ and
$`\lvert E\rvert \le \lvert C\rvert`$, then there exists $`K \in \mathrm{PairSeq}`$ with

```math
C = E \mathbin{+\!\!+} K \qquad\text{and}\qquad F = K \mathbin{+\!\!+} D .
```

### Proof

Take $`K := \mathrm{drop}_{\lvert E\rvert} C`$.
The two conclusions of [T.split_prefix_left](ArgDom-2.md#t-split_prefix_left) are exactly the two required equalities. ∎

<a id="t-prefix_cons_append"></a>
## Theorem: a common left factor, a common column, and prefixes (T.prefix_cons_append)

### Theorem

Let $`A, P, Q \in \mathrm{PairSeq}`$ and $`c \in \mathbb{N}\times\mathbb{N}`$. If $`P \sqsubseteq Q`$ then

```math
A \mathbin{+\!\!+} c :: P \ \sqsubseteq\ A \mathbin{+\!\!+} c :: Q .
```

### Proof

Take $`t`$ with $`Q = P \mathbin{+\!\!+} t`$. From the relation
$`c :: (P \mathbin{+\!\!+} t) = (c :: P) \mathbin{+\!\!+} t`$ between cons and concatenation, together with associativity of concatenation,

```math
A \mathbin{+\!\!+} c :: Q = A \mathbin{+\!\!+} \bigl((c :: P) \mathbin{+\!\!+} t\bigr)
 = \bigl(A \mathbin{+\!\!+} c :: P\bigr) \mathbin{+\!\!+} t
```

Hence $`t`$ is the required witness. ∎

<a id="t-spineOK_of_nextrel1_strict"></a>
## Theorem: strong form of the spine condition (T.spineOK_of_nextrel1_strict)

### Theorem

Let $`G, R \in \mathrm{PairSeq}`$ and $`v_0, w_0, d_0 \in \mathbb{N}`$, and put

```math
\ell := (v_0 + d_0,\ w_0 + 1),
\qquad
M := \bigl(G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr) \mathbin{+\!\!+} (\ell),
\qquad
j_1 := \bigl\lvert G \mathbin{+\!\!+} ((v_0,w_0) :: R)\bigr\rvert
```

If $`\lvert G\rvert \to^M_1 j_1`$ ([D.nextrel1](Pss.md#d-nextrel1)), then

```math
\mathrm{SpineOK}\bigl(R,\ v_0 + d_0,\ w_0 + 1\bigr).
```

($`\mathrm{SpineOK}`$ [D.SpineOK](ArgDom.md#d-SpineOK))

### Proof

By the definition of $`\mathrm{SpineOK}`$ (D.SpineOK), it suffices to show $`w_0 + 1 \le x_2`$
whenever $`U, V \in \mathrm{PairSeq}`$ and $`x \in \mathbb{N}\times\mathbb{N}`$ satisfy

```math
R = U \mathbin{+\!\!+} x :: V,
\qquad x_1 \lt v_0 + d_0,
\qquad \forall y \in V,\ x_1 \lt y_1
```

By the definition of $`\to^M_1`$ (D.nextrel1), the hypothesis $`\lvert G\rvert \to^M_1 j_1`$ yields
in particular condition (5),

```math
\lvert G\rvert \le^M_0 j_1
```

and condition (6),

```math
\forall j,\ \bigl(\lvert G\rvert \lt j \wedge j \le^M_0 j_1\bigr) \to M_{1,j_1} \le M_{1,j}
```

($`\le^M_0`$ [D.le0](Pss.md#d-le0), $`M_{i,j}`$ [D.entry](Pss.md#d-entry)).
Put $`A := G \mathbin{+\!\!+} ((v_0,w_0) :: U)`$.

**Step 1: counting positions.**
Substituting $`R = U \mathbin{+\!\!+} x :: V`$ into the definition of $`M`$ and rearranging by associativity of concatenation,

```math
M = A \mathbin{+\!\!+} \bigl(x :: (V \mathbin{+\!\!+} (\ell))\bigr)
```

The lengths are

```math
\lvert A\rvert = \lvert G\rvert + 1 + \lvert U\rvert,
\qquad
j_1 = \lvert G\rvert + 1 + \lvert R\rvert
    = \lvert G\rvert + 1 + \lvert U\rvert + 1 + \lvert V\rvert
    = \lvert A\rvert + 1 + \lvert V\rvert
```

In particular $`\lvert G\rvert \lt \lvert A\rvert`$ and $`\lvert A\rvert \le j_1`$.

Applying [T.getD_append_right'](Cofinality.md#t-getD_append_right') to
$`A`$, $`x :: (V \mathbin{+\!\!+} (\ell))`$ and $`i := 0`$ gives
$`M\langle \lvert A\rvert\rangle = x`$. Hence
[T.entry_zero](Cofinality.md#t-entry_zero) and [T.entry_one](Cofinality.md#t-entry_one) give

```math
M_{0,\lvert A\rvert} = x_1, \qquad M_{1,\lvert A\rvert} = x_2 .
```

**Step 2: every column strictly to the right of position $`\lvert A\rvert`$ and up to $`j_1`$ has a greater row $`0`$ entry.**
That is, we show

```math
\forall y,\ \bigl(\lvert A\rvert \lt y \wedge y \le j_1\bigr) \to M_{0,\lvert A\rvert} \lt M_{0,y}
```

From $`\lvert A\rvert \lt y`$ we may take $`t`$ with $`y = \lvert A\rvert + (t+1)`$.
The decomposition of Step 1 and [T.getD_append_right'](Cofinality.md#t-getD_append_right') give

```math
M\bigl\langle \lvert A\rvert + (t+1)\bigr\rangle
 = \bigl(x :: (V \mathbin{+\!\!+} (\ell))\bigr)\langle t+1\rangle
 = \bigl(V \mathbin{+\!\!+} (\ell)\bigr)\langle t\rangle
```

From $`y \le j_1 = \lvert A\rvert + 1 + \lvert V\rvert`$ we get $`t \le \lvert V\rvert`$;
distinguish cases according to $`t`$.

- Case $`t \lt \lvert V\rvert`$. Then $`(V \mathbin{+\!\!+} (\ell))\langle t\rangle = V\langle t\rangle`$, and
  since $`t \lt \lvert V\rvert`$ this is an element of $`V`$. Applying the hypothesis $`\forall y \in V,\ x_1 \lt y_1`$
  to it gives $`x_1 \lt (V\langle t\rangle)_1`$, that is,
  $`M_{0,\lvert A\rvert} \lt M_{0,y}`$.

- Case $`t = \lvert V\rvert`$. Applying
  [T.getD_append_right'](Cofinality.md#t-getD_append_right') again to $`V`$, $`(\ell)`$ and $`i := 0`$ gives
  $`(V \mathbin{+\!\!+} (\ell))\langle \lvert V\rvert\rangle = \ell`$.
  The hypothesis $`x_1 \lt v_0 + d_0 = \ell_1`$ then gives $`M_{0,\lvert A\rvert} \lt M_{0,y}`$.

**Step 3: $`x`$ is a row-$`0`$ ancestor of the column that is dropped.**
Apply [T.le0_through_pivot](Column-4.md#t-le0_through_pivot) with
$`a := \lvert G\rvert`$, $`\rho := \lvert A\rvert`$, $`b := j_1`$.
Its hypotheses are $`\lvert G\rvert \le^M_0 j_1`$ from condition (5), $`\lvert G\rvert \lt \lvert A\rvert`$ and
$`\lvert A\rvert \le j_1`$ from Step 1, and Step 2. The conclusion is

```math
\lvert A\rvert \le^M_0 j_1 .
```

**Step 4: use the minimality condition.**
Applying [T.getD_append_right'](Cofinality.md#t-getD_append_right') to
$`G \mathbin{+\!\!+} ((v_0,w_0) :: R)`$, $`(\ell)`$ and $`i := 0`$ gives
$`M\langle j_1\rangle = \ell`$. Hence
[T.entry_one](Cofinality.md#t-entry_one) gives $`M_{1,j_1} = \ell_2 = w_0 + 1`$.

Apply condition (6) with $`j := \lvert A\rvert`$. Its antecedent consists of
$`\lvert G\rvert \lt \lvert A\rvert`$ from Step 1 and $`\lvert A\rvert \le^M_0 j_1`$ from Step 3.
Therefore

```math
w_0 + 1 = M_{1,j_1} \le M_{1,\lvert A\rvert} = x_2 . \qquad \blacksquare
```
