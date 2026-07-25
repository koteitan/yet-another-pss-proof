[← README](README.md) | [English](Cnf-2.md) | [Japanese](Cnf-2-ja.md) | Cnf [1](Cnf.md) **2** [3](Cnf-3.md)

<a id="t-cnf_ctx_cong"></a>
## Theorem: congruence of the condition under a context (T.cnf_ctx_cong)

### Theorem

Let $`z_1, z_2 \in \mathbb{N}\times\mathbb{N}`$ and $`T_1, T_2, G \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)),
and assume the following six conditions.

```math
\begin{aligned}
&\text{(cZ1)}\quad   &&\mathrm{cnf}\bigl(\mathrm{tr}(z_1 :: T_1)\bigr), \cr
&\text{(decr)}\quad  &&\mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2), \cr
&\text{(root)}\quad  &&(z_1)_1 = (z_2)_1, \cr
&\text{(leadle)}\quad&&\exists\, a_1, b_1, c_1, a_2, b_2, c_2,\ \bigl[\
   \mathrm{tr}(z_1 :: T_1) = \mathsf{P}(a_1,b_1,c_1) \cr
& &&\qquad\ \wedge\ \mathrm{tr}(z_2 :: T_2) = \mathsf{P}(a_2,b_2,c_2) \cr
& &&\qquad\ \wedge\ \mathsf{P}(a_1,b_1,\mathsf{Z}) \preceq \mathsf{P}(a_2,b_2,\mathsf{Z})\ \bigr], \cr
&\text{(r1)}\quad    &&\forall x \in T_1,\ (z_1)_1 \le x_1, \cr
&\text{(r2)}\quad    &&\forall x \in T_2,\ (z_2)_1 \le x_1 .
\end{aligned}
```

($`\mathrm{cnf}`$ [D.cnf](Cnf.md#d-cnf), $`\mathrm{tr}`$ [D.translate](Term.md#d-translate),
$`\prec`$ [D.olt](Term.md#d-olt), $`\mathsf{P}`$ and $`\mathsf{Z}`$ [D.Three](Term.md#d-Three),
$`\preceq`$ [D.ole](Term.md#d-ole))

Then $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2)\bigr)`$ implies
$`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} z_1 :: T_1)\bigr)`$.

### Proof

Fix $`z_1, z_2, T_1, T_2`$ and the six hypotheses, and argue by strong induction on $`\lvert G\rvert`$.
The induction predicate is

```math
\Phi(G) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2)\bigr)
  \to \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} z_1 :: T_1)\bigr)
```

and the induction hypothesis is that $`\Phi(G')`$ holds for every $`G'`$ with $`\lvert G'\rvert \lt \lvert G\rvert`$.
In what follows we take $`a_1, b_1, c_1, a_2, b_2, c_2`$ from (leadle), so that

```math
\begin{aligned}
\mathrm{tr}(z_1 :: T_1) &= \mathsf{P}(a_1,b_1,c_1), \quad \cr
\mathrm{tr}(z_2 :: T_2) &= \mathsf{P}(a_2,b_2,c_2), \quad \cr
\mathsf{P}(a_1,b_1,\mathsf{Z}) &\preceq \mathsf{P}(a_2,b_2,\mathsf{Z})
\end{aligned}
```

hold.

**Case $`G = ()`$.** Since $`() \mathbin{+\!\!+} z_1 :: T_1 = z_1 :: T_1`$, the conclusion is exactly (cZ1).

**Case $`G = g :: G'`$.** We distinguish cases according to whether all elements $`x`$ of $`G'`$ satisfy $`g_1 \lt x_1`$.

**(a) Some element $`x`$ of $`G'`$ satisfies $`\neg(g_1 \lt x_1)`$.**
Applying [T.takeWhile_append_not](Term.md#t-takeWhile_append_not) and
[T.dropWhile_append_not](Term.md#t-dropWhile_append_not) with $`xs := G'`$ and $`ys := z_i :: T_i`$,
we obtain, for both $`i = 1, 2`$,

```math
\mathrm{tw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = \mathrm{tw}_{g_1} G',
\qquad
\mathrm{dw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = \mathrm{dw}_{g_1} G' \mathbin{+\!\!+} z_i :: T_i
```

Moreover $`\mathrm{dw}_{g_1} G' \ne ()`$. Indeed, if $`\mathrm{dw}_{g_1} G' = ()`$, then all elements of
$`G'`$ satisfy $`g_1 \lt x_1`$, which contradicts the assumption on $`x`$.
So write $`\mathrm{dw}_{g_1} G' = d :: D'`$. By the definition of $`\mathrm{tr}`$ (D.translate),
for both $`i = 1, 2`$,

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_i :: T_i)\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}(\mathrm{tw}_{g_1} G'),\
      \mathrm{tr}((d :: D') \mathbin{+\!\!+} z_i :: T_i)\bigr)
```

and, since $`(d :: D') \mathbin{+\!\!+} z_i :: T_i = d :: (D' \mathbin{+\!\!+} z_i :: T_i)`$,
the definition gives again

```math
\begin{aligned}
\mathrm{tr}\bigl((d :: D') \mathbin{+\!\!+} z_i :: T_i\bigr)
  &= \mathsf{P}\bigl(d_2,\ A_i,\ \mathrm{tr}(\mathrm{dw}_{d_1}(D' \mathbin{+\!\!+} z_i :: T_i))\bigr),
\qquad \cr
A_i &:= \mathrm{tr}\bigl(\mathrm{tw}_{d_1}(D' \mathbin{+\!\!+} z_i :: T_i)\bigr)
\end{aligned}
```

Applying [T.translate_ctx_cong](Term.md#t-translate_ctx_cong) to the hypotheses (decr), (root), (r1), (r2)
with $`G := d :: D'`$ yields

```math
\mathrm{tr}\bigl((d :: D') \mathbin{+\!\!+} z_1 :: T_1\bigr)
  \prec \mathrm{tr}\bigl((d :: D') \mathbin{+\!\!+} z_2 :: T_2\bigr)
```

Rewriting both sides in the form above and using [T.olt_P_P](Term.md#t-olt_P_P),
one of the following three holds.

- $`d_2 \lt d_2`$. This cannot happen, by the irreflexivity of $`\lt`$.
- $`d_2 = d_2 \wedge A_1 \prec A_2`$.
- $`d_2 = d_2 \wedge A_1 = A_2 \wedge (\cdots)`$.

Hence

```math
(\ast)\qquad A_1 \prec A_2 \ \vee\ A_1 = A_2
```

Next, rewriting the antecedent $`\mathrm{cnf}\bigl(\mathrm{tr}(g :: (G' \mathbin{+\!\!+} z_2 :: T_2))\bigr)`$
in the form above and using [T.cnf_P_P](Cnf.md#t-cnf_P_P), we obtain the following three statements.

1. $`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{tw}_{g_1} G')\bigr)`$.
2. $`\neg\bigl(\mathsf{P}(g_2, \mathrm{tr}(\mathrm{tw}_{g_1} G'), \mathsf{Z}) \prec \mathsf{P}(d_2, A_2, \mathsf{Z})\bigr)`$.
3. $`\mathrm{cnf}\bigl(\mathsf{P}(d_2, A_2, \mathrm{tr}(\mathrm{dw}_{d_1}(D' \mathbin{+\!\!+} z_2 :: T_2)))\bigr)`$,
   that is, $`\mathrm{cnf}\bigl(\mathrm{tr}((d :: D') \mathbin{+\!\!+} z_2 :: T_2)\bigr)`$.

Since $`d :: D' = \mathrm{dw}_{g_1} G'`$ is a subsequence of $`G'`$, we have
$`\lvert d :: D'\rvert \le \lvert G'\rvert \lt \lvert g :: G'\rvert`$, so the induction hypothesis
applies with $`G' := d :: D'`$. Together with 3 it gives

```math
\mathrm{cnf}\bigl(\mathrm{tr}((d :: D') \mathbin{+\!\!+} z_1 :: T_1)\bigr)
```

Next we show

```math
\neg\bigl(\mathsf{P}(g_2,\ \mathrm{tr}(\mathrm{tw}_{g_1} G'),\ \mathsf{Z})
  \prec \mathsf{P}(d_2,\ A_1,\ \mathsf{Z})\bigr)
```

Suppose the inner relation holds. Then by [T.olt_P_P](Term.md#t-olt_P_P) one of the following three holds.

- $`g_2 \lt d_2`$. In this case the first disjunct on the right-hand side of [T.olt_P_P](Term.md#t-olt_P_P) gives
  $`\mathsf{P}(g_2, \mathrm{tr}(\mathrm{tw}_{g_1} G'), \mathsf{Z}) \prec \mathsf{P}(d_2, A_2, \mathsf{Z})`$,
  which contradicts 2.
- $`g_2 = d_2 \wedge \mathrm{tr}(\mathrm{tw}_{g_1} G') \prec A_1`$. Distinguish cases by $`(\ast)`$.
  If $`A_1 \prec A_2`$, then [T.olt_trans](Term.md#t-olt_trans) gives
  $`\mathrm{tr}(\mathrm{tw}_{g_1} G') \prec A_2`$. If $`A_1 = A_2`$, rewriting gives the same conclusion.
  In either case the second disjunct on the right-hand side of [T.olt_P_P](Term.md#t-olt_P_P) gives
  $`\mathsf{P}(g_2, \mathrm{tr}(\mathrm{tw}_{g_1} G'), \mathsf{Z}) \prec \mathsf{P}(d_2, A_2, \mathsf{Z})`$,
  which contradicts 2.
- $`g_2 = d_2 \wedge \mathrm{tr}(\mathrm{tw}_{g_1} G') = A_1 \wedge \mathsf{Z} \prec \mathsf{Z}`$.
  This contradicts [T.not_olt_Z](Term.md#t-not_olt_Z).

Finally, the two identities above with $`i = 1`$ give

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_1 :: T_1)\bigr)
  = \mathsf{P}\Bigl(g_2,\ \mathrm{tr}(\mathrm{tw}_{g_1} G'),\
      \mathsf{P}\bigl(d_2,\ A_1,\ \mathrm{tr}(\mathrm{dw}_{d_1}(D' \mathbin{+\!\!+} z_1 :: T_1))\bigr)\Bigr)
```

Hence, feeding [T.cnf_P_P](Cnf.md#t-cnf_P_P) with 1, the negation just proved, and
$`\mathrm{cnf}\bigl(\mathrm{tr}((d :: D') \mathbin{+\!\!+} z_1 :: T_1)\bigr)`$ obtained from the induction hypothesis,
we get $`\mathrm{cnf}\bigl(\mathrm{tr}(g :: (G' \mathbin{+\!\!+} z_1 :: T_1))\bigr)`$, that is, the conclusion of $`\Phi(g :: G')`$.

**(b) All elements $`x`$ of $`G'`$ satisfy $`g_1 \lt x_1`$, and $`g_1 \lt (z_1)_1`$.**
By (root), $`g_1 \lt (z_2)_1`$ as well. By (r1), every element $`x`$ of $`T_1`$ satisfies
$`g_1 \lt (z_1)_1 \le x_1`$, so all elements of $`z_1 :: T_1`$ satisfy $`g_1 \lt x_1`$.
Likewise, by (r2) every element $`x`$ of $`T_2`$ satisfies $`g_1 \lt (z_2)_1 \le x_1`$, so
all elements of $`z_2 :: T_2`$ satisfy $`g_1 \lt x_1`$ too. Hence all elements of $`G' \mathbin{+\!\!+} z_i :: T_i`$
satisfy $`g_1 \lt x_1`$, and [T.translate_single_tree](Term.md#t-translate_single_tree) gives,
for both $`i = 1, 2`$,

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_i :: T_i)\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}(G' \mathbin{+\!\!+} z_i :: T_i),\ \mathsf{Z}\bigr)
```

Rewriting the antecedent in this form and using [T.cnf_P_Z](Cnf.md#t-cnf_P_Z), we obtain
$`\mathrm{cnf}\bigl(\mathrm{tr}(G' \mathbin{+\!\!+} z_2 :: T_2)\bigr)`$.
Since $`\lvert G'\rvert \lt \lvert g :: G'\rvert`$, applying the induction hypothesis to $`G'`$ gives
$`\mathrm{cnf}\bigl(\mathrm{tr}(G' \mathbin{+\!\!+} z_1 :: T_1)\bigr)`$.
By [T.cnf_P_Z](Cnf.md#t-cnf_P_Z) again,
$`\mathrm{cnf}\bigl(\mathrm{tr}(g :: (G' \mathbin{+\!\!+} z_1 :: T_1))\bigr)`$ holds.

**(c) All elements $`x`$ of $`G'`$ satisfy $`g_1 \lt x_1`$, and $`\neg\bigl(g_1 \lt (z_1)_1\bigr)`$.**
By (root), $`\neg\bigl(g_1 \lt (z_2)_1\bigr)`$ as well.
By [T.takeWhile_append_all](Term.md#t-takeWhile_append_all) and
[T.dropWhile_append_all](Term.md#t-dropWhile_append_all), for both $`i = 1, 2`$,

```math
\mathrm{tw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = G' \mathbin{+\!\!+} \mathrm{tw}_{g_1}(z_i :: T_i),
\qquad
\mathrm{dw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = \mathrm{dw}_{g_1}(z_i :: T_i)
```

and, since the leading $`z_i`$ violates the predicate, $`\mathrm{tw}_{g_1}(z_i :: T_i) = ()`$ and
$`\mathrm{dw}_{g_1}(z_i :: T_i) = z_i :: T_i`$. Hence the definition of $`\mathrm{tr}`$ (D.translate)
together with the two equalities in (leadle) gives

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_i :: T_i)\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}\,G',\ \mathsf{P}(a_i,b_i,c_i)\bigr)
```

Rewriting the antecedent in this form (with $`i = 2`$) and using [T.cnf_P_P](Cnf.md#t-cnf_P_P),
we obtain the following three statements.

1. $`\mathrm{cnf}(\mathrm{tr}\,G')`$.
2. $`\neg\bigl(\mathsf{P}(g_2, \mathrm{tr}\,G', \mathsf{Z}) \prec \mathsf{P}(a_2,b_2,\mathsf{Z})\bigr)`$.
3. $`\mathrm{cnf}\bigl(\mathsf{P}(a_2,b_2,c_2)\bigr)`$ (which is not used).

We now show

```math
\neg\bigl(\mathsf{P}(g_2,\ \mathrm{tr}\,G',\ \mathsf{Z}) \prec \mathsf{P}(a_1,b_1,\mathsf{Z})\bigr)
```

Suppose the inner relation holds. Then
$`\mathsf{P}(a_1,b_1,\mathsf{Z}) \preceq \mathsf{P}(a_2,b_2,\mathsf{Z})`$ from (leadle) and
[T.olt_ole_trans](Term.md#t-olt_ole_trans) give
$`\mathsf{P}(g_2, \mathrm{tr}\,G', \mathsf{Z}) \prec \mathsf{P}(a_2,b_2,\mathsf{Z})`$, which contradicts 2.

Moreover, (cZ1) and $`\mathrm{tr}(z_1 :: T_1) = \mathsf{P}(a_1,b_1,c_1)`$ give
$`\mathrm{cnf}\bigl(\mathsf{P}(a_1,b_1,c_1)\bigr)`$.
Feeding [T.cnf_P_P](Cnf.md#t-cnf_P_P) with 1, the negation just proved, and this, we get
$`\mathrm{cnf}\bigl(\mathsf{P}(g_2, \mathrm{tr}\,G', \mathsf{P}(a_1,b_1,c_1))\bigr)`$,
that is, $`\mathrm{cnf}\bigl(\mathrm{tr}(g :: (G' \mathbin{+\!\!+} z_1 :: T_1))\bigr)`$.

In all three cases $`\Phi(g :: G')`$ is proved. ∎

<a id="t-cnf_tail"></a>
## Theorem: a re-opening suffix satisfies the condition (T.cnf_tail)

### Theorem

Let $`t \in \mathbb{N}\times\mathbb{N}`$ and $`T', G \in \mathrm{PairSeq}`$, and assume
$`\forall x \in T',\ t_1 \le x_1`$.
Then $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} t :: T')\bigr)`$ implies $`\mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)`$.

### Proof

Fix $`t, T'`$ and the hypothesis $`\forall x \in T',\ t_1 \le x_1`$, and argue by strong induction on $`\lvert G\rvert`$.
The induction predicate is

```math
\Psi(G) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} t :: T')\bigr)
  \to \mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)
```

and the induction hypothesis is that $`\Psi(G')`$ holds for every $`G'`$ with $`\lvert G'\rvert \lt \lvert G\rvert`$.

**Case $`G = ()`$.** Since $`() \mathbin{+\!\!+} t :: T' = t :: T'`$, the conclusion is exactly the antecedent.

**Case $`G = g :: G'`$.** We distinguish cases according to whether all elements $`x`$ of $`G'`$ satisfy $`g_1 \lt x_1`$.

**(a) Some element $`x`$ of $`G'`$ satisfies $`\neg(g_1 \lt x_1)`$.**
Applying [T.takeWhile_append_not](Term.md#t-takeWhile_append_not) and
[T.dropWhile_append_not](Term.md#t-dropWhile_append_not) with $`xs := G'`$ and $`ys := t :: T'`$,
we obtain

```math
\mathrm{tw}_{g_1}(G' \mathbin{+\!\!+} t :: T') = \mathrm{tw}_{g_1} G',
\qquad
\mathrm{dw}_{g_1}(G' \mathbin{+\!\!+} t :: T') = \mathrm{dw}_{g_1} G' \mathbin{+\!\!+} t :: T'
```

Moreover $`\mathrm{dw}_{g_1} G' \ne ()`$ (if $`\mathrm{dw}_{g_1} G' = ()`$, then all elements of
$`G'`$ satisfy $`g_1 \lt x_1`$, which contradicts the assumption on $`x`$).
So write $`\mathrm{dw}_{g_1} G' = d :: D'`$; then the definition of $`\mathrm{tr}`$ (D.translate) gives

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} t :: T')\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}(\mathrm{tw}_{g_1} G'),\
      \mathrm{tr}((d :: D') \mathbin{+\!\!+} t :: T')\bigr),
```
```math
\mathrm{tr}\bigl((d :: D') \mathbin{+\!\!+} t :: T'\bigr)
  = \mathsf{P}\bigl(d_2,\ \mathrm{tr}(\mathrm{tw}_{d_1}(D' \mathbin{+\!\!+} t :: T')),\
      \mathrm{tr}(\mathrm{dw}_{d_1}(D' \mathbin{+\!\!+} t :: T'))\bigr)
```

(in the second identity we used $`(d :: D') \mathbin{+\!\!+} t :: T' = d :: (D' \mathbin{+\!\!+} t :: T')`$).
Rewriting the antecedent in this form and using [T.cnf_P_P](Cnf.md#t-cnf_P_P), we obtain
$`\mathrm{cnf}\bigl(\mathrm{tr}((d :: D') \mathbin{+\!\!+} t :: T')\bigr)`$ as the third conjunct on its right-hand side.
Since $`d :: D' = \mathrm{dw}_{g_1} G'`$ is a subsequence of $`G'`$, we have
$`\lvert d :: D'\rvert \le \lvert G'\rvert \lt \lvert g :: G'\rvert`$, and applying the induction hypothesis
with $`G' := d :: D'`$ gives $`\mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)`$.

**(b) All elements $`x`$ of $`G'`$ satisfy $`g_1 \lt x_1`$, and $`g_1 \lt t_1`$.**
By the hypothesis $`\forall x \in T',\ t_1 \le x_1`$, every element $`x`$ of $`T'`$ satisfies
$`g_1 \lt t_1 \le x_1`$, so all elements of $`t :: T'`$ satisfy $`g_1 \lt x_1`$.
Hence all elements of $`G' \mathbin{+\!\!+} t :: T'`$ satisfy $`g_1 \lt x_1`$, and
[T.translate_single_tree](Term.md#t-translate_single_tree) gives

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} t :: T')\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}(G' \mathbin{+\!\!+} t :: T'),\ \mathsf{Z}\bigr)
```

Rewriting the antecedent in this form and using [T.cnf_P_Z](Cnf.md#t-cnf_P_Z), we obtain
$`\mathrm{cnf}\bigl(\mathrm{tr}(G' \mathbin{+\!\!+} t :: T')\bigr)`$.
Since $`\lvert G'\rvert \lt \lvert g :: G'\rvert`$, applying the induction hypothesis to $`G'`$ gives
$`\mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)`$.

**(c) All elements $`x`$ of $`G'`$ satisfy $`g_1 \lt x_1`$, and $`\neg(g_1 \lt t_1)`$.**
By [T.takeWhile_append_all](Term.md#t-takeWhile_append_all) and
[T.dropWhile_append_all](Term.md#t-dropWhile_append_all),

```math
\mathrm{tw}_{g_1}(G' \mathbin{+\!\!+} t :: T') = G' \mathbin{+\!\!+} \mathrm{tw}_{g_1}(t :: T'),
\qquad
\mathrm{dw}_{g_1}(G' \mathbin{+\!\!+} t :: T') = \mathrm{dw}_{g_1}(t :: T')
```

and, since the leading $`t`$ violates the predicate, $`\mathrm{tw}_{g_1}(t :: T') = ()`$ and
$`\mathrm{dw}_{g_1}(t :: T') = t :: T'`$. Hence the definition of $`\mathrm{tr}`$ (D.translate) gives

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} t :: T')\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}\,G',\ \mathrm{tr}(t :: T')\bigr),
```
```math
\mathrm{tr}(t :: T')
  = \mathsf{P}\bigl(t_2,\ \mathrm{tr}(\mathrm{tw}_{t_1} T'),\ \mathrm{tr}(\mathrm{dw}_{t_1} T')\bigr)
```

Rewriting the antecedent in this form and using [T.cnf_P_P](Cnf.md#t-cnf_P_P), the third conjunct on its
right-hand side is
$`\mathrm{cnf}\bigl(\mathsf{P}(t_2, \mathrm{tr}(\mathrm{tw}_{t_1} T'), \mathrm{tr}(\mathrm{dw}_{t_1} T'))\bigr)`$,
that is, $`\mathrm{cnf}\bigl(\mathrm{tr}(t :: T')\bigr)`$.

In all three cases $`\Psi(g :: G')`$ is proved. ∎

<a id="t-cnf_oper_i1eq0"></a>
## Theorem: preservation of CNF in the exact-copy branch (T.cnf_oper_i1eq0)

### Theorem

Let $`v_0, w_0 \in \mathbb{N}`$, $`R, G \in \mathrm{PairSeq}`$, $`\ell \in \mathbb{N}\times\mathbb{N}`$ and
$`n \in \mathbb{N}`$. Put $`B := (v_0,w_0) :: R`$, and use the notation $`L^{\ast k}`$ for the
concatenation of $`k`$ copies of a sequence as in [T.cnf_replicate_block](Cnf.md#t-cnf_replicate_block).
Assume the following four conditions.

```math
\begin{aligned}
&\text{(hR)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(lpv)}\quad v_0 \lt \ell_1, \cr
&\text{(n1)}\quad 1 \le n, \cr
&\text{(cM)}\quad \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))\bigr).
\end{aligned}
```

Then

```math
\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B^{\ast n})\bigr).
```

### Proof

By (n1) there is $`m \in \mathbb{N}`$ with $`n = m + 1`$ (take $`m := n - 1`$).
In what follows we abbreviate $`T := B^{\ast m}`$.

**Step 1: the shape of the translations of the two sequences.**

First, every element $`x`$ of $`R \mathbin{+\!\!+} (\ell)`$ satisfies $`v_0 \lt x_1`$. Indeed, this is
(hR) when $`x \in R`$, and (lpv) when $`x = \ell`$. Hence applying
[T.translate_single_tree](Term.md#t-translate_single_tree) with $`p := (v_0,w_0)`$ and
$`R := R \mathbin{+\!\!+} (\ell)`$ gives

```math
\text{(A)}\qquad
\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

Next, the definition of $`L^{\ast k}`$ and $`B = (v_0,w_0) :: R`$ give

```math
\text{(B)}\qquad
B^{\ast(m+1)} = B \mathbin{+\!\!+} T = (v_0,w_0) :: (R \mathbin{+\!\!+} T)
```

Furthermore, the following holds for $`T`$.

```math
\text{(C)}\qquad T = () \ \vee\ \neg\bigl(v_0 \lt (\mathrm{head}\,T)_1\bigr).
```

Indeed, if $`m = 0`$ then $`T = B^{\ast 0} = ()`$ and the first disjunct holds.
If $`m = m' + 1`$ then $`T = B \mathbin{+\!\!+} B^{\ast m'}`$, whose head is the head
$`(v_0,w_0)`$ of $`B`$, so $`(\mathrm{head}\,T)_1 = v_0`$, and the irreflexivity of
$`\lt`$ gives $`\neg(v_0 \lt v_0)`$, that is, the second disjunct holds.

Applying [T.translate_block_append](Term.md#t-translate_block_append) to (hR) and (C) gives

```math
\text{(D)}\qquad
\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} T)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T\bigr)
```

**Step 2: CNF of the block body.**

By the associativity of $`\mathbin{+\!\!+}`$ and $`B = (v_0,w_0) :: R`$,

```math
G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell) = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
```

so (cM) is the same proposition as $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell)))\bigr)`$.
We call it (cM').

As shown in Step 1, every element $`x`$ of $`R \mathbin{+\!\!+} (\ell)`$ satisfies $`v_0 \lt x_1`$;
in particular

```math
\text{(rT)}\qquad \forall x \in R \mathbin{+\!\!+} (\ell),\ \bigl((v_0,w_0)\bigr)_1 \le x_1
```

Applying [T.cnf_tail](#t-cnf_tail) with $`t := (v_0,w_0)`$, $`T' := R \mathbin{+\!\!+} (\ell)`$ and $`G := G`$
to (rT) and (cM') gives

```math
\mathrm{cnf}\bigl(\mathrm{tr}((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell)))\bigr)
```

Substituting (A) here yields $`\mathrm{cnf}\bigl(\mathsf{P}(w_0, \mathrm{tr}(R \mathbin{+\!\!+} (\ell)), \mathsf{Z})\bigr)`$,
and [T.cnf_P_Z](Cnf.md#t-cnf_P_Z) gives

```math
\mathrm{cnf}\bigl(\mathrm{tr}(R \mathbin{+\!\!+} (\ell))\bigr)
```

Applying [T.cnf_snoc](Cnf.md#t-cnf_snoc) to this with $`D := R`$ and $`m := \ell`$ gives

```math
\text{(cR)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}\,R\bigr)
```

**Step 3: CNF of the copy sequence itself.**

Applying [T.cnf_replicate_block](Cnf.md#t-cnf_replicate_block) to (hR), (cR) and $`n := m+1`$ gives

```math
\text{(cZ1)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}(B^{\ast(m+1)})\bigr)
```

By (B) this is the same proposition as $`\mathrm{cnf}\bigl(\mathrm{tr}((v_0,w_0) :: (R \mathbin{+\!\!+} T))\bigr)`$.

**Step 4: the strict decrease and the comparison of the leading principal terms.**

Applying [T.translate_snoc_increase](Decrease.md#t-translate_snoc_increase) with $`C := R`$ and
$`m := \ell`$ gives

```math
\text{(E)}\qquad \mathrm{tr}\,R \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell))
```

Applying [T.olt_P_b](Term.md#t-olt_P_b) to (E) with $`a := w_0`$, $`c_1 := \mathrm{tr}\,T`$ and
$`c_2 := \mathsf{Z}`$ gives

```math
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T\bigr)
  \prec \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

and substituting (D) and (A) gives

```math
\text{(decr)}\qquad
\mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} T)\bigr)
  \prec \mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
```

Applying [T.olt_P_b](Term.md#t-olt_P_b) to (E) likewise with $`c_1 := \mathsf{Z}`$ and $`c_2 := \mathsf{Z}`$
gives

```math
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathsf{Z}\bigr)
  \prec \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

so the first disjunct of the definition of $`\preceq`$ (D.ole) yields

```math
\text{(leadle)}\qquad
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathsf{Z}\bigr)
  \preceq \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

The subscript and the argument on the right-hand side of (D) are $`w_0`$ and $`\mathrm{tr}\,R`$, and those
on the right-hand side of (A) are $`w_0`$ and $`\mathrm{tr}(R \mathbin{+\!\!+} (\ell))`$; hence (leadle) has the
form of the hypothesis (leadle) of [T.cnf_ctx_cong](#t-cnf_ctx_cong).

**Step 5: congruence under the context.**

Every element of $`T = B^{\ast m}`$ is an element of $`B`$. Indeed, $`T`$ is the concatenation of $`m`$
copies of $`B`$, so if $`x \in T`$ then $`x`$ is an element of one of those copies, and that copy is $`B`$
in each case. Since $`B = (v_0,w_0) :: R`$, either $`x = (v_0,w_0)`$ or $`x \in R`$; in the former case
$`x_1 = v_0`$, and in the latter case (hR) gives $`v_0 \lt x_1`$. In both cases $`v_0 \le x_1`$.
Combining this with (hR) gives

```math
\text{(r1)}\qquad \forall x \in R \mathbin{+\!\!+} T,\ \bigl((v_0,w_0)\bigr)_1 \le x_1
```

We apply [T.cnf_ctx_cong](#t-cnf_ctx_cong) with

```math
z_1 := (v_0,w_0),\quad T_1 := R \mathbin{+\!\!+} T,\quad
z_2 := (v_0,w_0),\quad T_2 := R \mathbin{+\!\!+} (\ell),\quad G := G
```

Its seven hypotheses are satisfied as follows.

- $`\mathrm{cnf}(\mathrm{tr}(z_1 :: T_1))`$: (cZ1) of Step 3 (via (B)).
- $`\mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2)`$: (decr) of Step 4.
- $`(z_1)_1 = (z_2)_1`$: both sides are $`v_0`$, so this is the reflexivity of $`=`$.
- (leadle): the (leadle) of Step 4 combined with (D) and (A).
- $`\forall x \in T_1,\ (z_1)_1 \le x_1`$: (r1) of Step 5.
- $`\forall x \in T_2,\ (z_2)_1 \le x_1`$: (rT) of Step 2.
- $`\mathrm{cnf}(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2))`$: (cM') of Step 2.

The conclusion is $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} (v_0,w_0) :: (R \mathbin{+\!\!+} T))\bigr)`$.
By (B) we have $`(v_0,w_0) :: (R \mathbin{+\!\!+} T) = B^{\ast(m+1)} = B^{\ast n}`$, so this is the required
$`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B^{\ast n})\bigr)`$. ∎

<a id="d-shiftr0"></a>
## Definition: shift of row 0 (D.shiftr0)

For $`d \in \mathbb{N}`$ and $`M \in \mathrm{PairSeq}`$, write $`M^{+d}`$ for the sequence obtained by
adding $`d`$ uniformly to the first entry of every pair of $`M`$. That is, for
$`M = (M_0, \dots, M_{X-1})`$ with $`X = \lvert M\rvert`$,

```math
M^{+d} := \bigl(\,(M_{0,0} + d,\ M_{1,0}),\ \dots,\ (M_{0,X-1} + d,\ M_{1,X-1})\,\bigr).
```

<a id="d-copies"></a>
## Definition: ascending copy sequence (D.copies)

For $`d, n \in \mathbb{N}`$ and $`B \in \mathrm{PairSeq}`$ put

```math
\mathrm{cp}_d(B, n) := B^{+0\cdot d} \mathbin{+\!\!+} B^{+1\cdot d} \mathbin{+\!\!+} \cdots
  \mathbin{+\!\!+} B^{+(n-1)d}
```

Precisely, this is the sequence obtained by mapping each element $`k`$ of
$`\mathrm{range}(n) := (0, 1, \dots, n-1)`$ to the sequence $`B^{+kd}`$ and concatenating the resulting
$`n`$ sequences from left to right. For $`n = 0`$ we have $`\mathrm{range}(0) = ()`$,
so $`\mathrm{cp}_d(B,0) = ()`$.

<a id="t-shiftr0_zero"></a>
## Theorem: a shift by 0 is the identity (T.shiftr0_zero)

### Theorem

For every $`M \in \mathrm{PairSeq}`$, $`M^{+0} = M`$.

### Proof

By the definition of $`M^{+d}`$ (D.shiftr0), the $`i`$-th element of $`M^{+0}`$ is $`(M_{0,i} + 0,\ M_{1,i})`$.
In $`\mathbb{N}`$ we have $`M_{0,i} + 0 = M_{0,i}`$, so this equals $`(M_{0,i},\ M_{1,i}) = M_i`$,
the $`i`$-th element of $`M`$. The lengths agree as well, $`\lvert M^{+0}\rvert = \lvert M\rvert`$. ∎

<a id="t-shiftr0_nil"></a>
## Theorem: shift of the empty sequence (T.shiftr0_nil)

### Theorem

For every $`d \in \mathbb{N}`$, $`()^{+d} = ()`$.

### Proof

The definition of $`M^{+d}`$ (D.shiftr0) maps each element of $`M`$, and $`M = ()`$ has no elements,
so the result has no elements either. ∎

<a id="t-shiftr0_eq_nil"></a>
## Theorem: when a shift is the empty sequence (T.shiftr0_eq_nil)

### Theorem

For $`d \in \mathbb{N}`$ and $`M \in \mathrm{PairSeq}`$,
$`M^{+d} = () \iff M = ()`$.

### Proof

By the definition of $`M^{+d}`$ (D.shiftr0), $`\lvert M^{+d}\rvert = \lvert M\rvert`$.
A sequence is empty if and only if its length is $`0`$, hence

```math
M^{+d} = () \iff \lvert M^{+d}\rvert = 0 \iff \lvert M\rvert = 0 \iff M = () . \qquad \blacksquare
```

<a id="t-translate_shiftr0"></a>
## Theorem: a shift does not change the translation (T.translate_shiftr0)

### Theorem

For $`d \in \mathbb{N}`$ and $`M \in \mathrm{PairSeq}`$,
$`\mathrm{tr}\,(M^{+d}) = \mathrm{tr}\,M`$.

### Proof

This is exactly [T.translate_shift](Term.md#t-translate_shift). ∎

<a id="t-shiftr0_cons"></a>
## Theorem: shift of a sequence with a head element (T.shiftr0_cons)

### Theorem

For $`d \in \mathbb{N}`$, $`p \in \mathbb{N}\times\mathbb{N}`$ and $`M \in \mathrm{PairSeq}`$,

```math
(p :: M)^{+d} = (p_1 + d,\ p_2) :: M^{+d} .
```

### Proof

The definition of $`M^{+d}`$ (D.shiftr0) maps each element by $`q \mapsto (q_1 + d, q_2)`$.
Applying this operation to $`p :: M`$ maps the head $`p`$ to $`(p_1 + d, p_2)`$ and the remaining
sequence $`M`$ to $`M^{+d}`$. ∎

<a id="t-mem_shiftr0"></a>
## Theorem: membership in a shifted sequence (T.mem_shiftr0)

### Theorem

For $`d \in \mathbb{N}`$, $`M \in \mathrm{PairSeq}`$ and $`x \in \mathbb{N}\times\mathbb{N}`$,

```math
x \in M^{+d} \iff \exists p \in M,\ (p_1 + d,\ p_2) = x .
```

### Proof

By the definition of $`M^{+d}`$ (D.shiftr0), $`M^{+d}`$ is the sequence obtained by mapping each element
$`p`$ of $`M`$ to $`(p_1+d, p_2)`$. Being an element of the mapped sequence is equivalent to the existence
of a preimage in the sequence before the mapping. ∎

<a id="t-copies_zero"></a>
## Theorem: zero copies (T.copies_zero)

### Theorem

For $`d \in \mathbb{N}`$ and $`B \in \mathrm{PairSeq}`$, $`\mathrm{cp}_d(B, 0) = ()`$.

### Proof

In the definition of $`\mathrm{cp}`$ (D.copies) we have $`\mathrm{range}(0) = ()`$, and the sequence obtained
by mapping the elements of the empty sequence and concatenating the results is the empty sequence. ∎
