[← README](README.md) | [English](Final.md) | [Japanese](Final-ja.md)

<a id="t-acc_Rnf_of_acc_PS"></a>
## Theorem: transport of accessibility to the term side (T.acc_Rnf_of_acc_PS)

### Theorem

The relation $`R_{\mathrm{st}}`$ ([D.Rst](Wset.md#d-Rst)) on
$`M \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) is defined (D.Rst) by

```math
a \mathbin{R_{\mathrm{st}}} b :\iff
  a \in \mathrm{ST\_PS} \ \wedge\ b \in \mathrm{ST\_PS} \ \wedge\ \mathrm{tr}\,a \prec \mathrm{tr}\,b
```

($`\mathrm{ST\_PS}`$ [D.ST_PS](Pss.md#d-ST_PS), $`\mathrm{tr}`$ [D.translate](Term.md#d-translate), $`\prec`$ [D.olt](Term.md#d-olt)).

($`\mathrm{Acc}_R`$ [D.Acc](Reduction.md#d-Acc), well-founded [D.WellFounded](Reduction.md#d-WellFounded))

Then, for every $`M \in \mathrm{PairSeq}`$, if $`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ and
$`M \in \mathrm{ST\_PS}`$, then $`\mathrm{tr}\,M \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$.

($`R_{\mathrm{NF}}`$ [D.Rnf](Reduction.md#d-Rnf))

### Proof

Let $`M \in \mathrm{PairSeq}`$ with $`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$ be given, and argue by
induction on the derivation of $`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$. The induction predicate is

```math
\Phi(M_0) :\equiv M_0 \in \mathrm{ST\_PS} \to \mathrm{tr}\,M_0 \in \mathrm{Acc}_{R_{\mathrm{NF}}} .
```

**Inductive step.** Fix $`M_0 \in \mathrm{PairSeq}`$ and assume the induction hypothesis

```math
\forall N \in \mathrm{PairSeq},\ N \mathbin{R_{\mathrm{st}}} M_0 \to \Phi(N)
```

(the other premise of the rule,
$`\forall N,\ N \mathbin{R_{\mathrm{st}}} M_0 \to N \in \mathrm{Acc}_{R_{\mathrm{st}}}`$,
is available as well, but is not used below). Assume $`M_0 \in \mathrm{ST\_PS}`$; we must show
$`\mathrm{tr}\,M_0 \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$. By the rule for $`\mathrm{Acc}`$, it suffices to show

```math
\forall v \in \mathrm{Three},\
  v \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M_0 \to v \in \mathrm{Acc}_{R_{\mathrm{NF}}}
```

($`\mathrm{Three}`$ [D.Three](Term.md#d-Three)).
Let $`v \in \mathrm{Three}`$ with $`v \mathbin{R_{\mathrm{NF}}} \mathrm{tr}\,M_0`$.
By the definition of $`R_{\mathrm{NF}}`$ (D.Rnf) the following three statements hold.

```math
v \prec \mathrm{tr}\,M_0, \qquad
\mathrm{tr}\,M_0 \in \mathrm{NF}, \qquad
v \in \mathrm{NF} .
```

($`\mathrm{NF}`$ [D.NF](Reduction.md#d-NF)) The second conjunct $`\mathrm{tr}\,M_0 \in \mathrm{NF}`$ is not used below.

Applying the definition of $`\mathrm{NF}`$ (D.NF) to the third conjunct $`v \in \mathrm{NF}`$ yields an
$`N \in \mathrm{PairSeq}`$ such that

```math
N \in \mathrm{ST\_PS}, \qquad \mathrm{tr}\,N = v
```

hold. From now on we replace $`v`$ by $`\mathrm{tr}\,N`$. The first conjunct becomes
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M_0`$.

The three conjuncts in the definition of $`R_{\mathrm{st}}`$ (D.Rst) are the $`N \in \mathrm{ST\_PS}`$
just obtained, the assumption $`M_0 \in \mathrm{ST\_PS}`$ of the inductive step, and
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M_0`$, so $`N \mathbin{R_{\mathrm{st}}} M_0`$ holds.
Applying the induction hypothesis to this gives $`\Phi(N)`$, and applying $`\Phi(N)`$ in turn to
$`N \in \mathrm{ST\_PS}`$ gives $`\mathrm{tr}\,N \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$.
This is $`v \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$.

Hence $`\Phi(M_0)`$ holds. By induction,
$`\forall M \in \mathrm{Acc}_{R_{\mathrm{st}}},\ \Phi(M)`$. ∎

<a id="t-wf_Rnf_of_wf_PS"></a>
## Theorem: transport of well-foundedness to the term side (T.wf_Rnf_of_wf_PS)

### Theorem

If $`R_{\mathrm{st}}`$ is well-founded, then $`R_{\mathrm{NF}}`$ is well-founded.

### Proof

Let $`u \in \mathrm{Three}`$; we show $`u \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$.
By the law of excluded middle we distinguish the cases $`u \in \mathrm{NF}`$ and $`u \notin \mathrm{NF}`$.

**(a) The case $`u \in \mathrm{NF}`$.** By the definition of $`\mathrm{NF}`$ (D.NF) there is an
$`M \in \mathrm{PairSeq}`$ with $`M \in \mathrm{ST\_PS}`$ and $`\mathrm{tr}\,M = u`$.
From now on we replace $`u`$ by $`\mathrm{tr}\,M`$. Applying the hypothesis of the present theorem,
that $`R_{\mathrm{st}}`$ is well-founded, to $`M`$ gives $`M \in \mathrm{Acc}_{R_{\mathrm{st}}}`$.
Feeding this and $`M \in \mathrm{ST\_PS}`$ into
[T.acc_Rnf_of_acc_PS](#t-acc_Rnf_of_acc_PS) gives
$`\mathrm{tr}\,M \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$, that is, $`u \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$.

**(b) The case $`u \notin \mathrm{NF}`$.** By the rule for $`\mathrm{Acc}`$ it suffices to show

```math
\forall v \in \mathrm{Three},\ v \mathbin{R_{\mathrm{NF}}} u \to v \in \mathrm{Acc}_{R_{\mathrm{NF}}}
```

Let $`v \in \mathrm{Three}`$ with $`v \mathbin{R_{\mathrm{NF}}} u`$. The second conjunct in the
definition of $`R_{\mathrm{NF}}`$ (D.Rnf) gives $`u \in \mathrm{NF}`$, which contradicts
the case assumption $`u \notin \mathrm{NF}`$. Hence the antecedent is false and the consequent
$`v \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$ follows.

In either case $`u \in \mathrm{Acc}_{R_{\mathrm{NF}}}`$, so $`R_{\mathrm{NF}}`$ is well-founded. ∎

<a id="t-pss_cofinality_holds"></a>
## Theorem: cofinality for PSS (T.pss_cofinality_holds)

### Theorem

Let $`M, N \in \mathrm{PairSeq}`$. If $`M \in \mathrm{ST\_PS}`$, $`N \in \mathrm{ST\_PS}`$ and
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$, then

```math
\exists n \in \mathbb{N},\ 1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n]) .
```

($`M[n]`$ [D.oper](Pss.md#d-oper), $`\preceq`$ [D.ole](Term.md#d-ole))

### Proof

[T.pss_cofinality_of_core](ArgDom.md#t-pss_cofinality_of_core) derives, under the assumption of the
proposition $`\mathrm{ArgDomCore}`$ ([D.ArgDomCore](ArgDom.md#d-ArgDomCore)), the conclusion of the present theorem
for arbitrary $`M, N \in \mathrm{PairSeq}`$ from the three hypotheses $`M \in \mathrm{ST\_PS}`$,
$`N \in \mathrm{ST\_PS}`$ and $`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$.

That assumption $`\mathrm{ArgDomCore}`$ is [T.argDomCore_holds](ArgDom-5.md#t-argDomCore_holds), which
has no hypotheses. Hence feeding
[T.argDomCore_holds](ArgDom-5.md#t-argDomCore_holds) and the three hypotheses of the present theorem
into [T.pss_cofinality_of_core](ArgDom.md#t-pss_cofinality_of_core) yields
the required $`n`$. ∎

<a id="t-wf_olt_ST_PS_holds"></a>
## Theorem: well-foundedness of the order on standard forms (T.wf_olt_ST_PS_holds)

### Theorem

$`R_{\mathrm{st}}`$ is well-founded.

### Proof

[T.wf_olt_ST_PS_of_cofinality](Wset-4.md#t-wf_olt_ST_PS_of_cofinality) derives the well-foundedness of
$`R_{\mathrm{st}}`$ from the hypothesis

```math
\forall M, N \in \mathrm{PairSeq},\
  \bigl(M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,N \prec \mathrm{tr}\,M\bigr)
  \to \exists n,\ 1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])
```

This hypothesis is exactly [T.pss_cofinality_holds](#t-pss_cofinality_holds) universally quantified
over $`M`$ and $`N`$. It therefore suffices to feed it into
[T.wf_olt_ST_PS_of_cofinality](Wset-4.md#t-wf_olt_ST_PS_of_cofinality). ∎

<a id="t-wf_Rnf_holds"></a>
## Theorem: well-foundedness of the order on normal forms (T.wf_Rnf_holds)

### Theorem

$`R_{\mathrm{NF}}`$ is well-founded.

### Proof

[T.wf_Rnf_of_wf_PS](#t-wf_Rnf_of_wf_PS) derives the well-foundedness of $`R_{\mathrm{NF}}`$ from the
well-foundedness of $`R_{\mathrm{st}}`$ as its hypothesis. That hypothesis is
[T.wf_olt_ST_PS_holds](#t-wf_olt_ST_PS_holds), which has no hypotheses. It therefore suffices to feed
[T.wf_olt_ST_PS_holds](#t-wf_olt_ST_PS_holds) into
[T.wf_Rnf_of_wf_PS](#t-wf_Rnf_of_wf_PS). ∎

<a id="t-PSS_terminates_unconditional"></a>
## Theorem: termination of PSS (T.PSS_terminates_unconditional)

### Theorem

$`R_{\mathrm{PS}}`$ is well-founded.

($`R_{\mathrm{PS}}`$ [D.stepRel](Reduction.md#d-stepRel))

### Proof

[T.step_terminates](Reduction.md#t-step_terminates) derives the well-foundedness of
$`R_{\mathrm{PS}}`$ from the well-foundedness of $`R_{\mathrm{NF}}`$ as its hypothesis.
That hypothesis is [T.wf_Rnf_holds](#t-wf_Rnf_holds), which has no hypotheses.
It therefore suffices to feed [T.wf_Rnf_holds](#t-wf_Rnf_holds) into
[T.step_terminates](Reduction.md#t-step_terminates). ∎

<a id="t-no_infinite_expansion_holds"></a>
## Theorem: non-existence of infinite expansion sequences (T.no_infinite_expansion_holds)

### Theorem

There is no $`S : \mathbb{N} \to \mathrm{PairSeq}`$ satisfying the following two conditions.

```math
\forall i \in \mathbb{N},\ S_i \in \mathrm{ST\_PS},
\qquad
\forall i \in \mathbb{N},\ S_i \Rightarrow S_{i+1} .
```

Here $`S_i`$ is the value of $`S`$ at $`i`$ ($`M \Rightarrow N`$ [D.step](Pss.md#d-step)).

### Proof

[T.no_infinite_expansion](Reduction.md#t-no_infinite_expansion) derives, from the well-foundedness of
$`R_{\mathrm{NF}}`$ as its hypothesis, that no $`S`$ satisfying the above two conditions exists.
That hypothesis is [T.wf_Rnf_holds](#t-wf_Rnf_holds), which has no hypotheses. It therefore suffices to feed
[T.wf_Rnf_holds](#t-wf_Rnf_holds) into
[T.no_infinite_expansion](Reduction.md#t-no_infinite_expansion). ∎
