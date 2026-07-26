[← README](README.md) | [English](Reduction.md) | [Japanese](Reduction-ja.md)

<a id="d-Acc"></a>
## Definition: the set of accessible elements (D.Acc)

For a relation $`R \subseteq A \times A`$ on a set $`A`$, define $`\mathrm{Acc}_R \subseteq A`$ to be
the least set closed under the following single rule.

```math
\bigl(\forall y \in A,\ y \mathbin{R} x \to y \in \mathrm{Acc}_R\bigr)
\ \Longrightarrow\ x \in \mathrm{Acc}_R .
```

Minimality is used in the form of the following induction principle. If a predicate $`\Phi`$ on
$`A`$ satisfies

```math
\forall x \in A,\
  \Bigl(\bigl(\forall y \in A,\ y \mathbin{R} x \to y \in \mathrm{Acc}_R\bigr)
  \wedge \bigl(\forall y \in A,\ y \mathbin{R} x \to \Phi(y)\bigr)\Bigr)
  \to \Phi(x)
```

then $`\forall x \in \mathrm{Acc}_R,\ \Phi(x)`$ holds. Below we call this the induction on the
derivation of $`\mathrm{Acc}_R`$. Since there is only one rule, this induction has no base case.

<a id="d-WellFounded"></a>
## Definition: well-founded (D.WellFounded)

Define a relation $`R \subseteq A \times A`$ to be **well-founded** if
$`\forall x \in A,\ x \in \mathrm{Acc}_R`$ holds.

<a id="d-NF"></a>
## Definition: the set of normal forms (D.NF)

Define the subset $`\mathrm{NF}`$ of $`\mathrm{Three}`$ ([D.Three](Term.md#d-Three)) to be the image
under $`\mathrm{tr}`$ ([D.translate](Term.md#d-translate)) of those
$`M \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) with
$`M \in \mathrm{ST\_PS}`$ ([D.ST_PS](Pss.md#d-ST_PS)).

```math
\mathrm{NF} := \{\, t \in \mathrm{Three} \mid \exists M,\ M \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,M = t \,\} .
```

The elements of $`\mathrm{NF}`$ are called **normal forms**.

<a id="d-Rnf"></a>
## Definition: the order on normal forms (D.Rnf)

For $`u, v \in \mathrm{Three}`$, define the relation $`R_{\mathrm{NF}}`$ by

```math
v \mathbin{R_{\mathrm{NF}}} u :\iff v \prec u \ \wedge\ u \in \mathrm{NF} \ \wedge\ v \in \mathrm{NF} .
```

($`\prec`$ [D.olt](Term.md#d-olt))

<a id="d-stepRel"></a>
## Definition: the one-step expansion relation on standard forms (D.stepRel)

For $`T, M \in \mathrm{PairSeq}`$, define the relation $`R_{\mathrm{PS}}`$ by

```math
T \mathbin{R_{\mathrm{PS}}} M :\iff M \in \mathrm{ST\_PS} \ \wedge\ M \Rightarrow T .
```

($`M \Rightarrow T`$ [D.step](Pss.md#d-step))

The first argument $`T`$ is the result of the expansion, and the second argument $`M`$ is what is
expanded. This is the same order of the arguments as in the definition of $`R_{\mathrm{NF}}`$ (D.Rnf),
where the first argument $`v`$ is placed on the left-hand side of $`v \prec u`$.

<a id="t-step_terminates_cond"></a>
## Theorem: conditional termination (T.step_terminates_cond)

### Theorem

Assume the following two hypotheses.

**(dec)** For all $`M \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$, if
$`M \in \mathrm{ST\_PS}`$, $`1 \lt \lvert M\rvert`$ and $`1 \le n`$, then

```math
\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M .
```

($`M[n]`$ [D.oper](Pss.md#d-oper))

**(wfimg)** $`R_{\mathrm{NF}}`$ is well-founded.

Under (dec) and (wfimg), $`R_{\mathrm{PS}}`$ is well-founded.

### Proof

Write the inverse image of $`R_{\mathrm{NF}}`$ under $`\mathrm{tr}`$ as

```math
T \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M :\iff \mathrm{tr}\,T \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M
```

The proof is in three steps.

**Step 1: if $`T \mathbin{R_{\mathrm{PS}}} M`$ then $`T \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M`$.**

Suppose $`T \mathbin{R_{\mathrm{PS}}} M`$. By the definition of $`R_{\mathrm{PS}}`$ (D.stepRel) we have
$`M \in \mathrm{ST\_PS}`$ and $`M \Rightarrow T`$. The definition of $`\Rightarrow`$ (D.step) consists of the
single rule (step_oper), so there is an $`n \in \mathbb{N}`$ with

```math
1 \lt \lvert M\rvert, \qquad 1 \le n, \qquad T = M[n]
```

We verify the three conjuncts of the definition of $`R_{\mathrm{NF}}`$ (D.Rnf) in turn.

1. $`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$: apply hypothesis (dec) with $`M`$ and $`n`$.
   Its three antecedents $`M \in \mathrm{ST\_PS}`$, $`1 \lt \lvert M\rvert`$ and $`1 \le n`$ are
   exactly what we have just obtained.
2. $`\mathrm{tr}\,M \in \mathrm{NF}`$: satisfy the existential quantifier in the definition of
   $`\mathrm{NF}`$ (D.NF) with $`M`$ itself. Indeed $`M \in \mathrm{ST\_PS}`$ and $`\mathrm{tr}\,M = \mathrm{tr}\,M`$.
3. $`\mathrm{tr}\,(M[n]) \in \mathrm{NF}`$: applying rule (oper) of the definition of
   $`\mathrm{ST\_PS}`$ (D.ST_PS) to $`M \in \mathrm{ST\_PS}`$ and $`1 \le n`$ gives $`M[n] \in \mathrm{ST\_PS}`$.
   It then suffices to satisfy the existential quantifier in the definition of $`\mathrm{NF}`$ with $`M[n]`$.

That is, $`\mathrm{tr}\,(M[n]) \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M`$.
Since $`T = M[n]`$, this is $`\mathrm{tr}\,T \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M`$,
that is, $`T \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M`$.

**Step 2: $`R^{\mathrm{tr}}_{\mathrm{NF}}`$ is well-founded.**

We argue by induction on the derivation of $`\mathrm{Acc}_{R_{\mathrm{NF}}}`$. The induction predicate is

```math
\Phi(t) :\equiv \forall M \in \mathrm{PairSeq},\
  \mathrm{tr}\,M = t \to M \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}} .
```

**Inductive step.** Let $`t \in \mathrm{Three}`$ and assume the induction hypothesis

```math
\forall s \in \mathrm{Three},\ s \mathbin{R_{\mathrm{NF}}} t \to \Phi(s)
```

(the premise of the rule, $`\forall s \in \mathrm{Three},\ s \mathbin{R_{\mathrm{NF}}} t \to s \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$,
is available at the same time, but it is not used below). Let $`M \in \mathrm{PairSeq}`$ be a sequence with $`\mathrm{tr}\,M = t`$.
To show $`M \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}`$ it suffices, by the rule for $`\mathrm{Acc}`$, to show

```math
\forall N \in \mathrm{PairSeq},\ N \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M \to N \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}
```

So suppose $`N \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M`$. By the definition of the inverse image,
$`\mathrm{tr}\,N \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M`$, and since $`\mathrm{tr}\,M = t`$ this reads
$`\mathrm{tr}\,N \mathbin{R_{\mathrm{NF}}} t`$. Applying the induction hypothesis with $`s := \mathrm{tr}\,N`$ gives
$`\Phi(\mathrm{tr}\,N)`$, and applying that to $`N`$ and $`\mathrm{tr}\,N = \mathrm{tr}\,N`$ gives
$`N \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}`$. Hence $`\Phi(t)`$ holds.

Therefore $`\forall t \in \mathrm{Acc}_{R_{\mathrm{NF}}},\ \Phi(t)`$. By hypothesis (wfimg) every
$`t \in \mathrm{Three}`$ belongs to $`\mathrm{Acc}_{R_{\mathrm{NF}}}`$, so $`\Phi(\mathrm{tr}\,M)`$ holds for every
$`M \in \mathrm{PairSeq}`$, and applying it to $`M`$ and
$`\mathrm{tr}\,M = \mathrm{tr}\,M`$ gives $`M \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}`$.
That is, $`R^{\mathrm{tr}}_{\mathrm{NF}}`$ is well-founded.

**Step 3: $`R_{\mathrm{PS}}`$ is well-founded.**

We argue by induction on the derivation of $`\mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}`$. The induction predicate is

```math
\Psi(M) :\equiv M \in \mathrm{Acc}_{R_{\mathrm{PS}}} .
```

**Inductive step.** Let $`M \in \mathrm{PairSeq}`$ and assume the induction hypothesis

```math
\forall N \in \mathrm{PairSeq},\ N \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M \to \Psi(N)
```

For an arbitrary $`T`$ with $`T \mathbin{R_{\mathrm{PS}}} M`$, Step 1 gives
$`T \mathbin{R^{\mathrm{tr}}_{\mathrm{NF}}} M`$, so the induction hypothesis yields $`\Psi(T)`$, that is,
$`T \in \mathrm{Acc}_{R_{\mathrm{PS}}}`$. Hence

```math
\forall T \in \mathrm{PairSeq},\ T \mathbin{R_{\mathrm{PS}}} M \to T \in \mathrm{Acc}_{R_{\mathrm{PS}}}
```

holds, and the rule for $`\mathrm{Acc}`$ gives $`M \in \mathrm{Acc}_{R_{\mathrm{PS}}}`$, that is, $`\Psi(M)`$.

Therefore $`\forall M \in \mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}},\ \Psi(M)`$. By Step 2 every
$`M \in \mathrm{PairSeq}`$ belongs to $`\mathrm{Acc}_{R^{\mathrm{tr}}_{\mathrm{NF}}}`$, so
$`\forall M \in \mathrm{PairSeq},\ \Psi(M)`$, that is, $`R_{\mathrm{PS}}`$ is well-founded. ∎

<a id="t-no_infinite_expansion_cond"></a>
## Theorem: conditional non-existence of infinite expansion sequences (T.no_infinite_expansion_cond)

### Theorem

Assume the same two hypotheses (dec) and (wfimg) as in [T.step_terminates_cond](#t-step_terminates_cond).
Then there is no $`S : \mathbb{N} \to \mathrm{PairSeq}`$ satisfying the following two conditions.

```math
\forall i \in \mathbb{N},\ S_i \in \mathrm{ST\_PS},
\qquad
\forall i \in \mathbb{N},\ S_i \Rightarrow S_{i+1} .
```

Here $`S_i`$ is the value of $`S`$ at $`i`$.

### Proof

Suppose such an $`S`$ exists, and derive a contradiction.

First, applying [T.step_terminates_cond](#t-step_terminates_cond) to the hypotheses (dec) and (wfimg)
shows that $`R_{\mathrm{PS}}`$ is well-founded.

Next, for every $`i \in \mathbb{N}`$,

```math
(\ast)\qquad S_{i+1} \mathbin{R_{\mathrm{PS}}} S_i
```

holds. Indeed, the two conjuncts of the definition of $`R_{\mathrm{PS}}`$ (D.stepRel) are exactly
$`S_i \in \mathrm{ST\_PS}`$, the first condition on $`S`$ applied to $`i`$, and
$`S_i \Rightarrow S_{i+1}`$, the second condition on $`S`$ applied to $`i`$.

We argue by induction on the derivation of $`\mathrm{Acc}_{R_{\mathrm{PS}}}`$. The induction predicate is

```math
\Theta(x) :\equiv \forall i \in \mathbb{N},\ S_i = x \to \bot .
```

**Inductive step.** Let $`x \in \mathrm{PairSeq}`$ and assume the induction hypothesis

```math
\forall y \in \mathrm{PairSeq},\ y \mathbin{R_{\mathrm{PS}}} x \to \Theta(y)
```

Let $`i \in \mathbb{N}`$ and suppose $`S_i = x`$. By $`(\ast)`$ we have
$`S_{i+1} \mathbin{R_{\mathrm{PS}}} S_i`$, and substituting $`S_i = x`$ gives
$`S_{i+1} \mathbin{R_{\mathrm{PS}}} x`$. Applying the induction hypothesis with $`y := S_{i+1}`$ gives
$`\Theta(S_{i+1})`$, and applying that to $`i + 1`$ and $`S_{i+1} = S_{i+1}`$ gives $`\bot`$.
Hence $`\Theta(x)`$ holds.

Therefore $`\forall x \in \mathrm{Acc}_{R_{\mathrm{PS}}},\ \Theta(x)`$. Since $`R_{\mathrm{PS}}`$ is
well-founded, $`S_0 \in \mathrm{Acc}_{R_{\mathrm{PS}}}`$, and applying $`\Theta(S_0)`$ to $`0`$ and
$`S_0 = S_0`$ gives $`\bot`$. This is the required contradiction. ∎

<a id="t-step_terminates"></a>
## Theorem: termination (T.step_terminates)

### Theorem

If $`R_{\mathrm{NF}}`$ is well-founded, then $`R_{\mathrm{PS}}`$ is well-founded.

### Proof

We verify hypothesis (dec) of [T.step_terminates_cond](#t-step_terminates_cond).
Let $`M \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$, and assume $`M \in \mathrm{ST\_PS}`$,
$`1 \lt \lvert M\rvert`$ and $`1 \le n`$.
The antecedents of [T.m_step_decreases](Decrease.md#t-m_step_decreases) are only the two conditions
$`1 \lt \lvert M\rvert`$ and $`1 \le n`$, and its conclusion is $`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$.
Hence the conclusion is obtained without using the hypothesis $`M \in \mathrm{ST\_PS}`$, and (dec) holds.

It then suffices to give this, together with the well-foundedness of $`R_{\mathrm{NF}}`$ assumed in
the present theorem as (wfimg), to [T.step_terminates_cond](#t-step_terminates_cond). ∎

<a id="t-no_infinite_expansion"></a>
## Theorem: non-existence of infinite expansion sequences (T.no_infinite_expansion)

### Theorem

If $`R_{\mathrm{NF}}`$ is well-founded, then there is no $`S : \mathbb{N} \to \mathrm{PairSeq}`$
satisfying the following two conditions.

```math
\forall i \in \mathbb{N},\ S_i \in \mathrm{ST\_PS},
\qquad
\forall i \in \mathbb{N},\ S_i \Rightarrow S_{i+1} .
```

### Proof

We verify hypothesis (dec) of [T.no_infinite_expansion_cond](#t-no_infinite_expansion_cond).
Let $`M \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$, and assume $`M \in \mathrm{ST\_PS}`$,
$`1 \lt \lvert M\rvert`$ and $`1 \le n`$.
The antecedents of [T.m_step_decreases](Decrease.md#t-m_step_decreases) are only the two conditions
$`1 \lt \lvert M\rvert`$ and $`1 \le n`$, and its conclusion is $`\mathrm{tr}\,(M[n]) \prec \mathrm{tr}\,M`$.
Hence the conclusion is obtained without using the hypothesis $`M \in \mathrm{ST\_PS}`$, and (dec) holds.

It then suffices to give this, together with the well-foundedness of $`R_{\mathrm{NF}}`$ assumed in
the present theorem as (wfimg), to [T.no_infinite_expansion_cond](#t-no_infinite_expansion_cond). ∎
