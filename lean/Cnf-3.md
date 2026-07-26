[← README](README.md) | [English](Cnf-3.md) | [Japanese](Cnf-3-ja.md) | Cnf [1](Cnf.md) [2](Cnf-2.md) **3**

<a id="t-copies_succ_front"></a>
## Theorem: decomposition of a copy sequence from the front (T.copies_succ_front)

### Theorem

For $`d, n \in \mathbb{N}`$ and $`B \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)),

```math
\mathrm{cp}_d(B, n+1) = B \mathbin{+\!\!+} \bigl(\mathrm{cp}_d(B, n)\bigr)^{+d} .
```

($`\mathrm{cp}`$ [D.copies](Cnf-2.md#d-copies), $`B^{+d}`$ [D.shiftr0](Cnf-2.md#d-shiftr0))

### Proof

We have $`\mathrm{range}(n+1) = (0, 1, \dots, n)`$, and splitting off the leading $`0`$ gives

```math
\mathrm{range}(n+1) = (0) \mathbin{+\!\!+} \bigl(\,k+1\,\bigr)_{k \in \mathrm{range}(n)}
```

Hence, by the definition of $`\mathrm{cp}`$ (D.copies),

```math
\mathrm{cp}_d(B, n+1)
  = B^{+0\cdot d} \mathbin{+\!\!+} \bigl(B^{+(k+1)d}\bigr)_{k \in \mathrm{range}(n)}
    \text{ concatenated}
```

We show the following two points.

**Point 1: $`B^{+0\cdot d} = B`$.**
Since $`0 \cdot d = 0`$, [T.shiftr0_zero](Cnf-2.md#t-shiftr0_zero) gives $`B^{+0} = B`$.

**Point 2: the concatenation of $`B^{+(k+1)d}`$ over $`k \in \mathrm{range}(n)`$ equals
$`\bigl(\mathrm{cp}_d(B,n)\bigr)^{+d}`$.**
First, for each $`k`$,

```math
\bigl(B^{+kd}\bigr)^{+d} = B^{+(k+1)d}
```

Indeed, an element $`p`$ of $`B`$ is sent by the left-hand side to $`((p_1 + kd) + d,\ p_2)`$, and by
associativity of addition on $`\mathbb{N}`$ together with $`kd + d = (k+1)d`$ we have
$`(p_1 + kd) + d = p_1 + (k+1)d`$, so this agrees with $`(p_1 + (k+1)d,\ p_2)`$ on the right-hand side.

Next, $`(\cdot)^{+d}`$ acts on each element separately, hence commutes with concatenation: for
sequences $`L_0, \dots, L_{n-1}`$,

```math
\bigl(L_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} L_{n-1}\bigr)^{+d}
  = L_0^{+d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} L_{n-1}^{+d} .
```

Applying this with $`L_k := B^{+kd}`$, and using
$`\mathrm{cp}_d(B,n) = L_0 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} L_{n-1}`$ from the definition of
$`\mathrm{cp}`$ (D.copies), we obtain

```math
\bigl(\mathrm{cp}_d(B,n)\bigr)^{+d}
  = \bigl(B^{+0\cdot d}\bigr)^{+d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \bigl(B^{+(n-1)d}\bigr)^{+d}
  = B^{+1\cdot d} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+n\,d}
```

which is the required concatenation.

Combining Points 1 and 2, $`\mathrm{cp}_d(B,n+1) = B \mathbin{+\!\!+} (\mathrm{cp}_d(B,n))^{+d}`$. ∎

<a id="t-copies_one"></a>
## Theorem: a single copy (T.copies_one)

### Theorem

For $`d \in \mathbb{N}`$ and $`B \in \mathrm{PairSeq}`$, $`\mathrm{cp}_d(B, 1) = B`$.

### Proof

Applying [T.copies_succ_front](#t-copies_succ_front) with $`n := 0`$ gives

```math
\mathrm{cp}_d(B, 1) = B \mathbin{+\!\!+} \bigl(\mathrm{cp}_d(B, 0)\bigr)^{+d}
```

By [T.copies_zero](Cnf-2.md#t-copies_zero) we have $`\mathrm{cp}_d(B,0) = ()`$, and by
[T.shiftr0_nil](Cnf-2.md#t-shiftr0_nil) we have $`()^{+d} = ()`$.
Since $`B \mathbin{+\!\!+} () = B`$, the conclusion follows. ∎

<a id="t-copies_succ_cons"></a>
## Theorem: decomposition of a copy sequence with its head (T.copies_succ_cons)

### Theorem

For $`d, v_0, w_0, n \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$, putting $`B := (v_0,w_0) :: R`$,

```math
\mathrm{cp}_d(B, n+1) = (v_0,w_0) :: \bigl(R \mathbin{+\!\!+} (\mathrm{cp}_d(B, n))^{+d}\bigr).
```

### Proof

By [T.copies_succ_front](#t-copies_succ_front),
$`\mathrm{cp}_d(B, n+1) = B \mathbin{+\!\!+} (\mathrm{cp}_d(B,n))^{+d}`$.
Since $`B = (v_0,w_0) :: R`$, the definition of concatenation gives

```math
\bigl((v_0,w_0) :: R\bigr) \mathbin{+\!\!+} S = (v_0,w_0) :: (R \mathbin{+\!\!+} S)
```

for every sequence $`S`$. Taking $`S := (\mathrm{cp}_d(B,n))^{+d}`$ gives the claim. ∎

<a id="t-copies_v0_le"></a>
## Theorem: lower bound on row 0 of a copy sequence (T.copies_v0_le)

### Theorem

Let $`v_0, w_0, d, n \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$, and assume
$`\forall x \in R,\ v_0 \le x_1`$. Then

```math
\forall x \in \mathrm{cp}_d\bigl((v_0,w_0) :: R,\ n\bigr),\ v_0 \le x_1 .
```

### Proof

Let $`x \in \mathrm{cp}_d((v_0,w_0) :: R,\ n)`$. By the definition of $`\mathrm{cp}`$ (D.copies),
$`\mathrm{cp}_d((v_0,w_0)::R, n)`$ is the concatenation of $`((v_0,w_0)::R)^{+kd}`$ over
$`k \in \mathrm{range}(n)`$, so there is some $`k \in \mathrm{range}(n)`$ with
$`x \in ((v_0,w_0)::R)^{+kd}`$.
By [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) there is some $`p \in (v_0,w_0) :: R`$ with
$`x = (p_1 + kd,\ p_2)`$.

We distinguish cases on $`p \in (v_0,w_0) :: R`$.

- Case $`p = (v_0,w_0)`$. Then $`p_1 = v_0`$, hence $`v_0 \le p_1`$.
- Case $`p \in R`$. By hypothesis, $`v_0 \le p_1`$.

In either case $`v_0 \le p_1`$. Since $`x_1 = p_1 + kd`$ and $`p_1 \le p_1 + kd`$ in
$`\mathbb{N}`$, transitivity of $`\le`$ gives $`v_0 \le x_1`$. ∎

<a id="t-copies_tl_gt"></a>
## Theorem: strict lower bound on row 0 of the tail of a copy sequence (T.copies_tl_gt)

### Theorem

Let $`v_0, w_0, d, n \in \mathbb{N}`$ and $`R \in \mathrm{PairSeq}`$, and put $`B := (v_0,w_0) :: R`$.
Assume $`\forall x \in R,\ v_0 \lt x_1`$, $`0 \lt d`$ and $`1 \le n`$. Then

```math
\forall x \in R \mathbin{+\!\!+} \bigl(\mathrm{cp}_d(B,\ n-1)\bigr)^{+d},\ v_0 \lt x_1 .
```

### Proof

Let $`x \in R \mathbin{+\!\!+} (\mathrm{cp}_d(B, n-1))^{+d}`$, and distinguish cases according to which
side $`x`$ belongs to.

- Case $`x \in R`$. This is the hypothesis $`\forall x \in R,\ v_0 \lt x_1`$ itself.

- Case $`x \in (\mathrm{cp}_d(B, n-1))^{+d}`$. By [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) there is
  some $`p \in \mathrm{cp}_d(B, n-1)`$ with $`x = (p_1 + d,\ p_2)`$.
  The hypothesis $`\forall x \in R,\ v_0 \lt x_1`$ implies $`\forall x \in R,\ v_0 \le x_1`$, so
  applying [T.copies_v0_le](#t-copies_v0_le) with $`n := n-1`$ gives $`v_0 \le p_1`$.
  Since $`0 \lt d`$ we have $`p_1 \lt p_1 + d`$, and $`v_0 \le p_1 \lt p_1 + d = x_1`$ gives
  $`v_0 \lt x_1`$. ∎

<a id="t-cnf_copies"></a>
## Theorem: ascending copy sequences are CNF (T.cnf_copies)

### Theorem

Let $`v_0, w_0, d_0 \in \mathbb{N}`$, $`R \in \mathrm{PairSeq}`$ and
$`\ell \in \mathbb{N}\times\mathbb{N}`$, and put $`B := (v_0,w_0) :: R`$. Assume the following five
conditions.

```math
\begin{aligned}
&\text{(hR)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(d0pos)}\quad 0 \lt d_0, \cr
&\text{(w0lt)}\quad w_0 \lt \ell_2, \cr
&\text{(lphd)}\quad \ell_1 = v_0 + d_0, \cr
&\text{(cBlp)}\quad \mathrm{cnf}\bigl(\mathrm{tr}(B \mathbin{+\!\!+} (\ell))\bigr).
\end{aligned}
```

($`\mathrm{cnf}`$ [D.cnf](Cnf.md#d-cnf), $`\mathrm{tr}`$ [D.translate](Term.md#d-translate))

Then, for every $`n \in \mathbb{N}`$,

```math
\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{cp}_{d_0}(B, n))\bigr).
```

### Proof

Induction on the natural number $`n`$. The induction predicate is

```math
\Phi(n) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{cp}_{d_0}(B, n))\bigr).
```

**Base case** $`n = 0`$.
By [T.copies_zero](Cnf-2.md#t-copies_zero), $`\mathrm{cp}_{d_0}(B,0) = ()`$, and by the definition of
$`\mathrm{tr}`$ (D.translate), $`\mathrm{tr}\,() = \mathsf{Z}`$ ([D.Three](Term.md#d-Three)).
By [T.cnf_Z](Cnf.md#t-cnf_Z), $`\mathrm{cnf}(\mathsf{Z})`$ holds. Hence $`\Phi(0)`$.

**Inductive step** $`n \to n+1`$: assume $`\Phi(n)`$, that is,
$`\mathrm{cnf}(\mathrm{tr}(\mathrm{cp}_{d_0}(B,n)))`$. We distinguish cases on $`n`$.

**(i) Case $`n = 0`$.** What is to be shown is $`\Phi(1)`$.
By [T.copies_one](#t-copies_one), $`\mathrm{cp}_{d_0}(B,1) = B`$.
Moreover, dropping the last element of $`B \mathbin{+\!\!+} (\ell)`$ returns $`B`$, so
$`B = \mathrm{dropLast}\,(B \mathbin{+\!\!+} (\ell))`$.
Since $`\ell`$ is an element of $`B \mathbin{+\!\!+} (\ell)`$, that sequence is not the empty sequence.
Applying [T.cnf_dropLast](Cnf.md#t-cnf_dropLast) with $`C := B \mathbin{+\!\!+} (\ell)`$, hypothesis
(cBlp) yields $`\mathrm{cnf}(\mathrm{tr}(B))`$, that is, $`\Phi(1)`$.

**(ii) Case $`n = m + 1`$.** What is to be shown is $`\Phi(m+2)`$, and we assume
$`\Phi(m+1)`$, that is, $`\mathrm{cnf}(\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1)))`$.
In what follows we abbreviate $`Q := \mathrm{cp}_{d_0}(B, m)`$ and $`S := R \mathbin{+\!\!+} Q^{+d_0}`$.

**Step 1: the form of $`\mathrm{cp}_{d_0}(B, m+1)`$ and of its shift.**
By [T.copies_succ_cons](#t-copies_succ_cons),

```math
\text{(F)}\qquad \mathrm{cp}_{d_0}(B, m+1) = (v_0,w_0) :: S
```

Applying [T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons) to this gives

```math
\text{(G)}\qquad \bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)^{+d_0} = (v_0 + d_0,\ w_0) :: S^{+d_0}
```

**Step 2: the form of the translations.**
Applying [T.copies_tl_gt](#t-copies_tl_gt) with (hR), (d0pos) and $`n := m+1`$ (so that
$`1 \le m+1`$), and noting $`n - 1 = m`$, we obtain

```math
\text{(tlgt)}\qquad \forall x \in S,\ v_0 \lt x_1
```

By (F) and [T.translate_single_tree](Term.md#t-translate_single_tree),

```math
\text{(st1)}\qquad \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
```

Also, by (G) and [T.translate_shiftr0](Cnf-2.md#t-translate_shiftr0),

```math
\mathrm{tr}\bigl((v_0+d_0,\ w_0) :: S^{+d_0}\bigr) = \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)
```

so together with (st1) we obtain

```math
\text{(tZ1)}\qquad \mathrm{tr}\bigl((v_0+d_0,\ w_0) :: S^{+d_0}\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
```

Furthermore, applying the definition of $`\mathrm{tr}`$ (D.translate) with $`p := \ell`$ and
$`L := ()`$, and using $`\mathrm{tw}_{\ell_1}() = ()`$ and $`\mathrm{dw}_{\ell_1}() = ()`$,

```math
\text{(tlp)}\qquad \mathrm{tr}\,(\ell) = \mathsf{P}(\ell_2,\ \mathsf{Z},\ \mathsf{Z}).
```

**Step 3: strict decrease and comparison of the leading principal terms.**
From (tZ1), (tlp) and the first disjunct $`w_0 \lt \ell_2`$ ((w0lt)) of the right-hand side of
[T.olt_P_P](Term.md#t-olt_P_P),

```math
\text{(decr)}\qquad \mathrm{tr}\bigl((v_0+d_0,\ w_0) :: S^{+d_0}\bigr) \prec \mathrm{tr}\,(\ell).
```

($`\prec`$ [D.olt](Term.md#d-olt))

By the same first disjunct, $`\mathsf{P}(w_0, \mathrm{tr}\,S, \mathsf{Z}) \prec \mathsf{P}(\ell_2, \mathsf{Z}, \mathsf{Z})`$,
so the first disjunct of the definition of $`\preceq`$ ([D.ole](Term.md#d-ole)) gives

```math
\text{(leadle)}\qquad
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
  \preceq \mathsf{P}\bigl(\ell_2,\ \mathsf{Z},\ \mathsf{Z}\bigr)
```

The subscript and the argument on the right-hand side of (tZ1) are $`w_0`$ and $`\mathrm{tr}\,S`$,
and those on the right-hand side of (tlp) are $`\ell_2`$ and $`\mathsf{Z}`$; hence (leadle) has the
shape of the hypothesis (leadle) of [T.cnf_ctx_cong](Cnf-2.md#t-cnf_ctx_cong).

**Step 4: CNF of $`(v_0+d_0, w_0) :: S^{+d_0}`$.**
By (G) and [T.translate_shiftr0](Cnf-2.md#t-translate_shiftr0),
$`\mathrm{tr}\bigl((v_0+d_0,w_0) :: S^{+d_0}\bigr) = \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B,m+1)\bigr)`$,
so the induction hypothesis $`\Phi(m+1)`$ directly yields

```math
\text{(cZ1)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}((v_0+d_0,\ w_0) :: S^{+d_0})\bigr)
```

**Step 5: congruence in a context.**
Let $`x \in S^{+d_0}`$. By [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) there is some $`p \in S`$ with
$`x = (p_1 + d_0,\ p_2)`$. By (tlgt) we have $`v_0 \lt p_1`$, in particular $`v_0 \le p_1`$, hence

```math
\bigl((v_0+d_0,\ w_0)\bigr)_1 = v_0 + d_0 \le p_1 + d_0 = x_1 .
```

That is,

```math
\text{(r1)}\qquad \forall x \in S^{+d_0},\ \bigl((v_0+d_0,\ w_0)\bigr)_1 \le x_1 .
```

Also, by (lphd), $`\bigl((v_0+d_0, w_0)\bigr)_1 = v_0 + d_0 = \ell_1`$.

We apply [T.cnf_ctx_cong](Cnf-2.md#t-cnf_ctx_cong) with

```math
z_1 := (v_0+d_0,\ w_0),\quad T_1 := S^{+d_0},\quad
z_2 := \ell,\quad T_2 := (),\quad G := B
```

Its seven hypotheses are met as follows.

- $`\mathrm{cnf}(\mathrm{tr}(z_1 :: T_1))`$: this is (cZ1) of Step 4.
- $`\mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2)`$: here $`z_2 :: T_2 = (\ell)`$, and this is
  (decr) of Step 3.
- $`(z_1)_1 = (z_2)_1`$: this is $`v_0 + d_0 = \ell_1`$ by (lphd).
- (leadle): this is (leadle) of Step 3 combined with (tZ1) and (tlp).
- $`\forall x \in T_1,\ (z_1)_1 \le x_1`$: this is (r1) of Step 5.
- $`\forall x \in T_2,\ (z_2)_1 \le x_1`$: since $`T_2 = ()`$ has no element, the antecedent is false
  and the statement holds.
- $`\mathrm{cnf}(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2))`$: here
  $`G \mathbin{+\!\!+} z_2 :: T_2 = B \mathbin{+\!\!+} (\ell)`$, and this is hypothesis (cBlp).

We conclude

```math
\mathrm{cnf}\Bigl(\mathrm{tr}\bigl(B \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S^{+d_0}\bigr)\Bigr)
```

On the other hand, [T.copies_succ_front](#t-copies_succ_front) and (G) give

```math
\mathrm{cp}_{d_0}(B, m+2) = B \mathbin{+\!\!+} \bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)^{+d_0}
  = B \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: S^{+d_0}
```

so this is exactly $`\Phi(m+2)`$. ∎

<a id="t-cnf_oper_i1eq1"></a>
## Theorem: preservation of CNF in the ascending-copy branch (T.cnf_oper_i1eq1)

### Theorem

Let $`v_0, w_0, d_0, n \in \mathbb{N}`$, $`R, G \in \mathrm{PairSeq}`$ and
$`\ell \in \mathbb{N}\times\mathbb{N}`$, and put $`B := (v_0,w_0) :: R`$. Assume the following six
conditions.

```math
\begin{aligned}
&\text{(hR)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(d0pos)}\quad 0 \lt d_0, \cr
&\text{(w0lt)}\quad w_0 \lt \ell_2, \cr
&\text{(lphd)}\quad \ell_1 = v_0 + d_0, \cr
&\text{(n1)}\quad 1 \le n, \cr
&\text{(cM)}\quad \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))\bigr).
\end{aligned}
```

Then

```math
\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n))\bigr).
```

### Proof

By (n1) we may take $`m \in \mathbb{N}`$ with $`n = m+1`$.
In what follows we abbreviate $`Q := \mathrm{cp}_{d_0}(B, m)`$ and $`S := R \mathbin{+\!\!+} Q^{+d_0}`$.

First, (lphd) and (d0pos) give $`\ell_1 = v_0 + d_0`$ and $`0 \lt d_0`$, hence

```math
\text{(lpv)}\qquad v_0 \lt \ell_1 .
```

Moreover every element $`x`$ of $`R \mathbin{+\!\!+} (\ell)`$ satisfies $`v_0 \lt x_1`$
(by (hR) if $`x \in R`$, by (lpv) if $`x = \ell`$). We call this (Rlp).

**Step 1: the strict decrease $`\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1)) \prec \mathrm{tr}(B \mathbin{+\!\!+} (\ell))`$.**

We distinguish cases on $`m`$.

**(i) Case $`m = 0`$.** By [T.copies_one](#t-copies_one) we have
$`\mathrm{cp}_{d_0}(B,1) = B`$, so applying
[T.translate_snoc_increase](Decrease.md#t-translate_snoc_increase) with $`C := B`$ and
$`m := \ell`$ gives $`\mathrm{tr}\,B \prec \mathrm{tr}(B \mathbin{+\!\!+} (\ell))`$.

**(ii) Case $`m = m' + 1`$.**
Put $`Q' := \mathrm{cp}_{d_0}(B, m')`$ and $`S' := R \mathbin{+\!\!+} Q'^{+d_0}`$.
By [T.copies_succ_cons](#t-copies_succ_cons),
$`\mathrm{cp}_{d_0}(B, m'+1) = (v_0,w_0) :: S'`$, and by
[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons),

```math
\text{(G')}\qquad \bigl(\mathrm{cp}_{d_0}(B, m'+1)\bigr)^{+d_0} = (v_0+d_0,\ w_0) :: S'^{+d_0} .
```

Applying [T.copies_tl_gt](#t-copies_tl_gt) with (hR), (d0pos) and $`n := m'+1`$ gives

```math
\text{(tlgt')}\qquad \forall x \in S',\ v_0 \lt x_1
```

Let $`x \in S'^{+d_0}`$. By [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) there is some $`p \in S'`$ with
$`x = (p_1+d_0,\ p_2)`$, and (tlgt') gives $`v_0 \le p_1`$; therefore

```math
\text{(Cge)}\qquad \forall x \in S'^{+d_0},\ v_0 + d_0 \le x_1 .
```

We now apply [T.core_i1](Decrease.md#t-core_i1) with

```math
v_0 := v_0,\quad w_0 := w_0,\quad R := R,\quad
c := (v_0+d_0,\ w_0),\quad C' := S'^{+d_0},\quad \ell := \ell
```

Its five hypotheses are met as follows.

- $`\forall x \in R,\ v_0 \lt x_1`$: this is (hR).
- $`\forall x \in C',\ c_1 \le x_1`$: this is (Cge) (here $`c_1 = v_0 + d_0`$).
- $`c_1 = \ell_1`$: this is (lphd).
- $`v_0 \lt \ell_1`$: this is (lpv).
- $`c_2 \lt \ell_2`$: here $`c_2 = w_0`$, and this is (w0lt).

We conclude

```math
\mathrm{tr}\bigl(B \mathbin{+\!\!+} ((v_0+d_0,\ w_0) :: S'^{+d_0})\bigr)
  \prec \mathrm{tr}\bigl(B \mathbin{+\!\!+} (\ell)\bigr)
```

On the other hand, [T.copies_succ_front](#t-copies_succ_front) and (G') give

```math
\mathrm{cp}_{d_0}(B, m'+2) = B \mathbin{+\!\!+} \bigl(\mathrm{cp}_{d_0}(B, m'+1)\bigr)^{+d_0}
  = B \mathbin{+\!\!+} \bigl((v_0+d_0,\ w_0) :: S'^{+d_0}\bigr)
```

so this is exactly $`\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1)) \prec \mathrm{tr}(B \mathbin{+\!\!+} (\ell))`$.

By (i) and (ii) together,

```math
\text{(decr)}\qquad
\mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr) \prec \mathrm{tr}\bigl(B \mathbin{+\!\!+} (\ell)\bigr).
```

**Step 2: the form of the translations of both sides.**
By [T.copies_succ_cons](#t-copies_succ_cons),

```math
\text{(cpcons)}\qquad \mathrm{cp}_{d_0}(B, m+1) = (v_0,w_0) :: S
```

Applying [T.copies_tl_gt](#t-copies_tl_gt) with (hR), (d0pos) and $`n := m+1`$ gives

```math
\text{(tlgt)}\qquad \forall x \in S,\ v_0 \lt x_1
```

hence, by [T.translate_single_tree](Term.md#t-translate_single_tree),

```math
\text{(st1)}\qquad \mathrm{tr}\bigl(\mathrm{cp}_{d_0}(B, m+1)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr).
```

Moreover $`B \mathbin{+\!\!+} (\ell) = (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))`$ and (Rlp) holds, so
[T.translate_single_tree](Term.md#t-translate_single_tree) gives once more

```math
\text{(st2)}\qquad \mathrm{tr}\bigl(B \mathbin{+\!\!+} (\ell)\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr).
```

**Step 3: CNF of the block.**
By associativity of $`\mathbin{+\!\!+}`$ we have
$`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell) = G \mathbin{+\!\!+} \bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)`$,
so (cM) is the same proposition as

```math
\text{(cM')}\qquad
\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell)))\bigr)
```

By (Rlp),

```math
\text{(rT)}\qquad \forall x \in R \mathbin{+\!\!+} (\ell),\ \bigl((v_0,w_0)\bigr)_1 \le x_1
```

so applying [T.cnf_tail](Cnf-2.md#t-cnf_tail) with $`t := (v_0,w_0)`$,
$`T' := R \mathbin{+\!\!+} (\ell)`$ and $`G := G`$ gives

```math
\text{(cBlp)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}(B \mathbin{+\!\!+} (\ell))\bigr)
```

(using $`B \mathbin{+\!\!+} (\ell) = (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))`$).

**Step 4: CNF of the copy sequence itself.**
Applying [T.cnf_copies](#t-cnf_copies) with (hR), (d0pos), (w0lt), (lphd), (cBlp) and $`n := m+1`$
gives

```math
\text{(cCopies)}\qquad \mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{cp}_{d_0}(B, m+1))\bigr)
```

By (cpcons) this is the same proposition as $`\mathrm{cnf}\bigl(\mathrm{tr}((v_0,w_0) :: S)\bigr)`$.

**Step 5: strict decrease between the arguments.**
Substituting (st1) and (st2) into (decr) gives

```math
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
  \prec \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

By [T.olt_P_P](Term.md#t-olt_P_P), one of the three disjuncts on the right-hand side holds.

- First disjunct $`w_0 \lt w_0`$: this contradicts irreflexivity of $`\lt`$.
- Second disjunct $`w_0 = w_0 \wedge \mathrm{tr}\,S \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell))`$:
  this is exactly the desired conclusion.
- Third disjunct $`w_0 = w_0 \wedge \mathrm{tr}\,S = \mathrm{tr}(R \mathbin{+\!\!+} (\ell)) \wedge \mathsf{Z} \prec \mathsf{Z}`$:
  the last conjunct contradicts [T.not_olt_Z](Term.md#t-not_olt_Z).

Hence only the second disjunct is possible, and

```math
\text{(argA)}\qquad \mathrm{tr}\,S \prec \mathrm{tr}(R \mathbin{+\!\!+} (\ell)).
```

**Step 6: congruence in a context.**
Applying [T.olt_P_b](Term.md#t-olt_P_b) to (argA) with $`a := w_0`$, $`c_1 := \mathsf{Z}`$ and
$`c_2 := \mathsf{Z}`$ gives

```math
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
  \prec \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

so the first disjunct of the definition of $`\preceq`$ (D.ole) gives

```math
\text{(leadle)}\qquad
\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,S,\ \mathsf{Z}\bigr)
  \preceq \mathsf{P}\bigl(w_0,\ \mathrm{tr}(R \mathbin{+\!\!+} (\ell)),\ \mathsf{Z}\bigr)
```

Rewriting (st1) by (cpcons), and (st2) by
$`B \mathbin{+\!\!+} (\ell) = (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))`$, we see that
(leadle) has the shape of the hypothesis (leadle) of [T.cnf_ctx_cong](Cnf-2.md#t-cnf_ctx_cong).

Also, rewriting (decr) by (cpcons) and by
$`B \mathbin{+\!\!+} (\ell) = (v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))`$ gives

```math
\text{(decr')}\qquad
\mathrm{tr}\bigl((v_0,w_0) :: S\bigr) \prec \mathrm{tr}\bigl((v_0,w_0) :: (R \mathbin{+\!\!+} (\ell))\bigr)
```

From (tlgt) we also obtain

```math
\text{(r1)}\qquad \forall x \in S,\ \bigl((v_0,w_0)\bigr)_1 \le x_1
```

We apply [T.cnf_ctx_cong](Cnf-2.md#t-cnf_ctx_cong) with

```math
z_1 := (v_0,w_0),\quad T_1 := S,\quad
z_2 := (v_0,w_0),\quad T_2 := R \mathbin{+\!\!+} (\ell),\quad G := G
```

Its seven hypotheses are met as follows.

- $`\mathrm{cnf}(\mathrm{tr}(z_1 :: T_1))`$: this is (cCopies) of Step 4 (via (cpcons)).
- $`\mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2)`$: this is (decr').
- $`(z_1)_1 = (z_2)_1`$: both sides are $`v_0`$, so this holds by reflexivity of $`=`$.
- (leadle): this is (leadle) of Step 6.
- $`\forall x \in T_1,\ (z_1)_1 \le x_1`$: this is (r1).
- $`\forall x \in T_2,\ (z_2)_1 \le x_1`$: this is (rT) of Step 3.
- $`\mathrm{cnf}(\mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2))`$: this is (cM') of Step 3.

We conclude $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} (v_0,w_0) :: S)\bigr)`$.
By (cpcons), $`(v_0,w_0) :: S = \mathrm{cp}_{d_0}(B, m+1) = \mathrm{cp}_{d_0}(B, n)`$, so this is the
desired $`\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n))\bigr)`$. ∎

<a id="t-copies_replicate"></a>
## Theorem: a copy sequence with shift 0 is a plain replication (T.copies_replicate)

### Theorem

For $`B \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$,

```math
\mathrm{cp}_0(B, n) = B^{\ast n}
```

Here $`B^{\ast n}`$ is, as in [T.cnf_replicate_block](Cnf.md#t-cnf_replicate_block), the sequence
obtained by concatenating $`n`$ copies of $`B`$.

### Proof

For every $`k \in \mathbb{N}`$ we have $`k \cdot 0 = 0`$, and
[T.shiftr0_zero](Cnf-2.md#t-shiftr0_zero) gives $`B^{+k\cdot 0} = B^{+0} = B`$.
That is, in the definition of $`\mathrm{cp}`$ (D.copies) the sequence assigned to an element $`k`$
of $`\mathrm{range}(n)`$ is $`B`$, independently of $`k`$.

Therefore $`\mathrm{cp}_0(B,n)`$ is the concatenation of the list obtained by mapping each element
of $`\mathrm{range}(n)`$ to $`B`$. Since $`\lvert \mathrm{range}(n)\rvert = n`$, that list consists
of $`n`$ copies of $`B`$, and its concatenation is $`B^{\ast n}`$. ∎

<a id="t-cnf_oper"></a>
## Theorem: expansion preserves CNF (T.cnf_oper)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$, and assume $`1 \le n`$ and
$`\mathrm{cnf}(\mathrm{tr}\,M)`$. Then $`\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)`$ ([D.oper](Pss.md#d-oper)).

### Proof

In what follows we write $`j_1 := \lvert M\rvert - 1`$ and $`i_1 := \mathrm{idx}_1(M, j_1)`$
([D.idx1](Pss.md#d-idx1)) (subtraction of natural numbers is truncated subtraction).
We distinguish cases according to whether $`j_1 = 0`$.

**(a) Case $`j_1 = 0`$.**
By [T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short), $`M[n] = M`$.
Hence what is to be shown is the hypothesis $`\mathrm{cnf}(\mathrm{tr}\,M)`$ itself.

From now on assume $`j_1 \ne 0`$. Then $`\lvert M\rvert - 1 \ne 0`$, hence
$`1 \lt \lvert M\rvert`$. In particular $`M \ne ()`$ (if $`M = ()`$ then $`\lvert M\rvert = 0`$,
contradicting $`1 \lt \lvert M\rvert`$). Moreover $`\neg(\lvert M\rvert \le 1)`$, so the second case
in the definition of $`\mathrm{Pred}`$ ([D.Pred](Pss.md#d-Pred)) is selected, and

```math
\text{(hPred)}\qquad \mathrm{Pred}\,M = \mathrm{dropLast}\,M
```

**(b) Case $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$ ([D.entry](Pss.md#d-entry)).**
By [T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) we have
$`M[n] = \mathrm{Pred}\,M`$, and by (hPred), $`M[n] = \mathrm{dropLast}\,M`$.
Applying [T.cnf_dropLast](Cnf.md#t-cnf_dropLast) to $`M \ne ()`$ and the hypothesis
$`\mathrm{cnf}(\mathrm{tr}\,M)`$ gives $`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,M)\bigr)`$.

From now on assume $`\neg\bigl(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0\bigr)`$.
We divide further according to whether $`\mathrm{hasParent}(M, i_1, j_1)`$
([D.hasParent](Pss.md#d-hasParent)) holds.

**(c) Case $`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$.**
By [T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) we have
$`M[n] = \mathrm{Pred}\,M`$, and by (hPred), $`M[n] = \mathrm{dropLast}\,M`$.
Applying [T.cnf_dropLast](Cnf.md#t-cnf_dropLast) to $`M \ne ()`$ and the hypothesis
$`\mathrm{cnf}(\mathrm{tr}\,M)`$ gives $`\mathrm{cnf}\bigl(\mathrm{tr}(\mathrm{dropLast}\,M)\bigr)`$.

**(d) Case $`\mathrm{hasParent}(M, i_1, j_1)`$.**
Since $`1 \lt \lvert M\rvert`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$,
$`\mathrm{hasParent}(M, i_1, j_1)`$ and $`1 \le n`$ are all available, we apply
[T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks).
It yields $`G, R \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0 \in \mathbb{N}`$ and
$`\ell \in \mathbb{N}\times\mathbb{N}`$ such that, putting $`B := (v_0,w_0) :: R`$, the following
hold (of the assertions of that theorem we list only those used below; the last conjunct of each of
the two disjuncts of $`(5)`$ is not used).

```math
\begin{aligned}
&(1)\ M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell), \cr
&(2)\ M[n] = G \mathbin{+\!\!+} B^{+0\cdot d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}, \cr
&(3)\ \forall x \in R,\ v_0 \lt x_1, \cr
&(4)\ v_0 \lt \ell_1, \cr
&(5)\ \bigl(d_0 = 0 \wedge \cdots\bigr) \ \vee\
        \bigl(0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0 \wedge \cdots\bigr).
\end{aligned}
```

The part of the right-hand side of (2) after $`G`$ is exactly the definition of $`\mathrm{cp}`$
(D.copies), so

```math
\text{(2')}\qquad M[n] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n)
```

Also, (1) and the hypothesis $`\mathrm{cnf}(\mathrm{tr}\,M)`$ give

```math
\text{(cM')}\qquad \mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))\bigr)
```

We distinguish cases on the disjunction (5).

**(d-1) The first disjunct, in particular $`d_0 = 0`$.**
Since $`d_0 = 0`$, [T.copies_replicate](#t-copies_replicate) gives
$`\mathrm{cp}_{d_0}(B,n) = \mathrm{cp}_0(B,n) = B^{\ast n}`$.
Applying [T.cnf_oper_i1eq0](Cnf-2.md#t-cnf_oper_i1eq0) to (3) (its hypothesis (hR)), (4) (its
hypothesis (lpv)), $`1 \le n`$ (its hypothesis (n1)) and (cM') (its hypothesis (cM)) gives

```math
\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} B^{\ast n})\bigr)
```

By (2') this is $`\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)`$.

**(d-2) The second disjunct, in particular
$`0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0`$.**
Applying [T.cnf_oper_i1eq1](#t-cnf_oper_i1eq1) to (3) (its hypothesis (hR)), $`0 \lt d_0`$ (its
hypothesis (d0pos)), $`w_0 \lt \ell_2`$ (its hypothesis (w0lt)), $`\ell_1 = v_0 + d_0`$ (its
hypothesis (lphd)), $`1 \le n`$ (its hypothesis (n1)) and (cM') (its hypothesis (cM)) gives

```math
\mathrm{cnf}\bigl(\mathrm{tr}(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(B, n))\bigr)
```

By (2') this is $`\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)`$.

The cases (a) to (d) exhaust all possibilities. ∎

<a id="t-cnf_ST_PS"></a>
## Theorem: the translation of a standard form is CNF (T.cnf_ST_PS)

### Theorem

If $`M \in \mathrm{ST\_PS}`$ ([D.ST_PS](Pss.md#d-ST_PS)), then $`\mathrm{cnf}(\mathrm{tr}\,M)`$.

### Proof

Induction on the derivation of $`\mathrm{ST\_PS}`$. The induction predicate is

```math
\Phi(M) :\equiv \mathrm{cnf}\bigl(\mathrm{tr}\,M\bigr).
```

Corresponding to the two rules in the definition of $`\mathrm{ST\_PS}`$ (D.ST_PS), it suffices to
show the following.

- **Rule (diag)**: $`\forall v \in \mathbb{N},\ \Phi(\Delta_0^v)`$ ([D.diagSeq](Pss.md#d-diagSeq)).
  [T.cnf_diag](Cnf.md#t-cnf_diag) is exactly this.

- **Rule (oper)**: assuming $`M \in \mathrm{ST\_PS}`$, $`1 \le n`$ and the induction hypothesis
  $`\Phi(M)`$, that is $`\mathrm{cnf}(\mathrm{tr}\,M)`$, we show $`\Phi(M[n])`$.
  Applying [T.cnf_oper](#t-cnf_oper) to $`1 \le n`$ and the induction hypothesis
  $`\mathrm{cnf}(\mathrm{tr}\,M)`$ gives $`\mathrm{cnf}\bigl(\mathrm{tr}(M[n])\bigr)`$, that is
  $`\Phi(M[n])`$.

Hence $`\forall M \in \mathrm{ST\_PS},\ \Phi(M)`$ holds. ∎
