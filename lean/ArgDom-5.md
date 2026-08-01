[← README](README.md) | [English](ArgDom-5.md) | [Japanese](ArgDom-5-ja.md) | ArgDom [1](ArgDom.md) [2](ArgDom-2.md) [3](ArgDom-3.md) [4](ArgDom-4.md) **5**

<a id="t-argDomCoreOn_bad"></a>
## Theorem: preservation of ArgDomCoreOn in the fourth branch (T.argDomCoreOn_bad)

### Theorem

Let $`M, G, R \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)), $`v_0, w_0, d_0, n \in \mathbb{N}`$ and
$`\ell \in \mathbb{N}\times\mathbb{N}`$, and put $`\mathrm{blk} := (v_0,w_0) :: R`$.
Assume hypotheses (hM) through (hSTn) of [T.argDomCoreOn_bad_A2](ArgDom-4.md#t-argDomCoreOn_bad_A2) together with (hn), that is,

```math
\begin{aligned}
&\text{(hM)}\quad M \in \mathrm{ST\_PS}, \qquad
 \text{(hMon)}\quad \mathrm{ArgDomCoreOn}(M), \cr
&\text{(hMeq)}\quad M = G \mathbin{+\!\!+} \mathrm{blk} \mathbin{+\!\!+} (\ell), \cr
&\text{(hRgt)}\quad \forall x \in R,\ v_0 \lt x_1, \qquad
 \text{(hlp)}\quad v_0 \lt \ell_1, \cr
&\text{(hdisj)}\quad \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr)
   \ \vee\ \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 (\lvert M\rvert - 1)\bigr), \cr
&\text{(hSTn)}\quad \forall m,\ 1 \le m \to G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m) \in \mathrm{ST\_PS}, \cr
&\text{(hn)}\quad 1 \le n
\end{aligned}
```

($`\mathrm{ST\_PS}`$ [D.ST_PS](Pss.md#d-ST_PS), $`\mathrm{ArgDomCoreOn}`$ [D.ArgDomCoreOn](ArgDom.md#d-ArgDomCoreOn),
$`\to^M_1`$ [D.nextrel1](Pss.md#d-nextrel1), $`\mathrm{copies}_{d_0}`$ [D.copies](Cnf-2.md#d-copies)).

Then $`\mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n)\bigr)`$.

### Proof

By strong induction on $`n`$. Show

```math
\Phi(n) :\equiv \Bigl(1 \le n \to
  \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n)\bigr)\Bigr)
```

for every $`n`$.

(the hypothesis $`1 \le n`$ is put back into the antecedent of the conclusion before quantifying).
The inductive step of strong induction reads: for an arbitrary $`n`$, assuming $`\forall m \lt n,\ \Phi(m)`$, prove $`\Phi(n)`$.
The base case is contained in that step as the case $`n = 0`$, where the antecedent $`1 \le 0`$ is false
and hence $`\Phi(0)`$ holds.

**Inductive step.** Fix $`n`$ and assume the induction hypothesis

```math
\text{(IH)}\qquad \forall m,\ m \lt n \to
  \Bigl(1 \le m \to \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)\Bigr)
```

Suppose $`1 \le n`$. Following the definition of $`\mathrm{ArgDomCoreOn}`$, let
$`X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$ and $`u, w, e \in \mathbb{N}`$ be given together with
hypotheses (heq) through (h6) of [T.argDomCoreOn_bad_A2](ArgDom-4.md#t-argDomCoreOn_bad_A2); we must show

```math
B \preceq_{\mathrm{lex}}
  \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

($`\preceq_{\mathrm{lex}}`$ [D.sle](Cofinality.md#d-sle), $`L^{+e}`$ [D.shiftr0](Cnf-2.md#d-shiftr0)).

Rewritten, (IH) becomes

```math
\forall m,\ 1 \le m \to m \lt n \to
  \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)
```

which is exactly hypothesis (hIH) of [T.argDomCoreOn_bad_A2](ArgDom-4.md#t-argDomCoreOn_bad_A2).

Put $`i := \lvert X\rvert`$, $`j := \lvert X\rvert + (\lvert A_1\rvert + 1)`$ and
$`p := \lvert G\rvert + (\lvert R\rvert + 1)`$. Since the order on the natural numbers is total,
either $`j \lt p`$ or $`p \le j`$, and in the latter case either $`i \lt p`$ or $`p \le i`$.
These three cases are pairwise disjoint and exhaust all possibilities.

- Case $`j \lt p`$. Apply [T.argDomCoreOn_bad_B](ArgDom-3.md#t-argDomCoreOn_bad_B) to
  (hM) through (hSTn), to (hIH), (hn), (heq) through (h6), and to
  its case condition (hcase) $`j \lt p`$.
- Case $`p \le j`$ and $`i \lt p`$. Apply [T.argDomCoreOn_bad_A2](ArgDom-4.md#t-argDomCoreOn_bad_A2) to
  (hM) through (hSTn), to (hIH), (hn), (heq) through (h6), and to
  its case conditions (hcaseL) $`i \lt p`$ and (hcaseR) $`p \le j`$.
- Case $`p \le j`$ and $`p \le i`$. Apply [T.argDomCoreOn_bad_A1](ArgDom-2.md#t-argDomCoreOn_bad_A1) to
  (hM) through (hSTn), to (hIH), (hn), (heq) through (h6), and to
  its case condition (hcase) $`p \le i`$.

In each case the conclusion follows. ∎

<a id="t-argDomCoreOn_oper"></a>
## Theorem: preservation of ArgDomCoreOn under expansion (T.argDomCoreOn_oper)

### Theorem

If $`M \in \mathrm{ST\_PS}`$, $`\mathrm{ArgDomCoreOn}(M)`$ and $`1 \le n`$, then
$`\mathrm{ArgDomCoreOn}(M[n])`$ ($`M[n]`$ [D.oper](Pss.md#d-oper)).

### Proof

Write $`j_1 := \lvert M\rvert - 1`$. We distinguish cases along the branches of the definition of $`M[n]`$ (D.oper).

**(a) Case $`j_1 = 0`$.**
By [T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) we have $`M[n] = M`$, so the
hypothesis $`\mathrm{ArgDomCoreOn}(M)`$ is itself the conclusion.

**(b) Case $`j_1 \ne 0`$ and $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ ([D.entry](Pss.md#d-entry)).**
By [T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) we have
$`M[n] = \mathrm{Pred}\,M`$ ([D.Pred](Pss.md#d-Pred)). From $`j_1 = \lvert M\rvert - 1 \ne 0`$ it follows that
$`2 \le \lvert M\rvert`$, that is, $`\neg(\lvert M\rvert \le 1)`$, so the second case in the definition of
$`\mathrm{Pred}`$ (D.Pred) is selected and
$`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$.

Moreover $`M \ne ()`$ (if $`M = ()`$ then $`\lvert M\rvert = 0`$, contradicting $`2 \le \lvert M\rvert`$).
Also, by the definition of $`M_{i,j}`$ (D.entry), the hypothesis says
$`(M\langle j_1\rangle)_1 = 0`$ and $`(M\langle j_1\rangle)_2 = 0`$, that is,
$`M\langle j_1\rangle = (0,0)`$.
By [T.dropLast_snoc_getD](Cofinality.md#t-dropLast_snoc_getD),

```math
\mathrm{dropLast}\,M \mathbin{+\!\!+} \bigl((0,0)\bigr) = M
```

and therefore the hypothesis $`\mathrm{ArgDomCoreOn}(M)`$ is nothing but
$`\mathrm{ArgDomCoreOn}\bigl(\mathrm{dropLast}\,M \mathbin{+\!\!+} ((0,0))\bigr)`$.
Since the first entry of $`(0,0)`$ is $`0`$,
[T.argDomCoreOn_snoc_zero](ArgDom-2.md#t-argDomCoreOn_snoc_zero) applies and yields
$`\mathrm{ArgDomCoreOn}(\mathrm{dropLast}\,M) = \mathrm{ArgDomCoreOn}(M[n])`$.

**(c) Case $`j_1 \ne 0`$ and $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$.**
From $`2 \le \lvert M\rvert`$ we get $`0 \lt \lvert M\rvert`$, so by
[T.hasParent_last_ST_PS](Cofinality.md#t-hasParent_last_ST_PS) the search row
$`\mathrm{idx}_1(M,j_1)`$ ([D.idx1](Pss.md#d-idx1)) satisfies
$`\mathrm{hasParent}(M, \mathrm{idx}_1(M,j_1), j_1)`$ ([D.hasParent](Pss.md#d-hasParent)).

By [T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS) we have $`\mathrm{blockok}(0, M)`$ ([D.blockok](Seqlex.md#d-blockok)),
whose third conjunct is $`\mathrm{steps}_1(M)`$ ([D.steps1](Seqlex.md#d-steps1)).
Also, by [T.r1ok_ST_PS](Column-3.md#t-r1ok_ST_PS) we have
$`\mathrm{r1ok}(M)`$ ([D.r1ok](Column-2.md#d-r1ok)). Applying
[T.oper_bad_blocks_all](Cofinality.md#t-oper_bad_blocks_all) to $`1 \lt \lvert M\rvert`$ and to these,
we obtain $`G, R \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0 \in \mathbb{N}`$ and $`\ell \in \mathbb{N}\times\mathbb{N}`$
such that, putting $`\mathrm{blk} := (v_0,w_0) :: R`$,

```math
\begin{aligned}
&M = G \mathbin{+\!\!+} \mathrm{blk} \mathbin{+\!\!+} (\ell), \cr
&\forall k,\ 1 \le k \to M[k] = G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, k), \cr
&\forall x \in R,\ v_0 \lt x_1, \qquad v_0 \lt \ell_1, \cr
&\bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr)
   \ \vee\ \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 (\lvert M\rvert - 1)\bigr)
\end{aligned}
```

hold.

For each $`k \ge 1`$ we have
$`G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, k) = M[k]`$, and applying the constructor
$`\mathrm{oper}`$ of the definition of $`\mathrm{ST\_PS}`$ (D.ST_PS) to $`M \in \mathrm{ST\_PS}`$ and to
$`1 \le k`$ gives $`M[k] \in \mathrm{ST\_PS}`$; hence

```math
\forall k,\ 1 \le k \to G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, k) \in \mathrm{ST\_PS}
```

holds. Finally, rewrite $`M[n] = G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n)`$ and apply
[T.argDomCoreOn_bad](#t-argDomCoreOn_bad). ∎

<a id="t-argDomCoreOn_ST_PS"></a>
## Theorem: ArgDomCoreOn on standard forms (T.argDomCoreOn_ST_PS)

### Theorem

If $`N \in \mathrm{ST\_PS}`$, then $`\mathrm{ArgDomCoreOn}(N)`$.

### Proof

By [T.ST_PS.rec](Pss.md#t-ST_PS.rec). Show

```math
\Phi(N) :\equiv \mathrm{ArgDomCoreOn}(N)
```

for every $`N`$.

There are two constructors, so it suffices to prove the following two cases.

**Base case (constructor $`\mathrm{diag}`$).** This is the case $`N = \Delta_0^v`$ ([D.diagSeq](Pss.md#d-diagSeq)).
Here [T.argDomCoreOn_diag](ArgDom-2.md#t-argDomCoreOn_diag) is literally
$`\Phi(\Delta_0^v)`$.

**Inductive step (constructor $`\mathrm{oper}`$).** This is the case $`N = M[n]`$,
derived by this constructor from $`M \in \mathrm{ST\_PS}`$ and $`1 \le n`$.
Assume $`\Phi(M) = \mathrm{ArgDomCoreOn}(M)`$.
Applying [T.argDomCoreOn_oper](#t-argDomCoreOn_oper) to $`M \in \mathrm{ST\_PS}`$, to the
induction hypothesis $`\mathrm{ArgDomCoreOn}(M)`$ and to $`1 \le n`$ yields
$`\mathrm{ArgDomCoreOn}(M[n]) = \Phi(N)`$. ∎

<a id="t-argDomCore_holds"></a>
## Theorem: ArgDomCore holds (T.argDomCore_holds)

### Theorem

$`\mathrm{ArgDomCore}`$ ([D.ArgDomCore](ArgDom.md#d-ArgDomCore)).

### Proof

[T.argDomCore_of_on](ArgDom.md#t-argDomCore_of_on) derives
$`\mathrm{ArgDomCore}`$ from
$`\forall N,\ N \in \mathrm{ST\_PS} \to \mathrm{ArgDomCoreOn}(N)`$. Its premise is exactly
[T.argDomCoreOn_ST_PS](#t-argDomCoreOn_ST_PS). ∎
