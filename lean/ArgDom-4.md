[← README](README.md) | [English](ArgDom-4.md) | [Japanese](ArgDom-4-ja.md) | ArgDom [1](ArgDom.md) [2](ArgDom-2.md) [3](ArgDom-3.md) **4** [5](ArgDom-5.md)

<a id="t-argDomCoreOn_bad_A2"></a>
## Theorem: case A2 of the fourth branch (the cross case) (T.argDomCoreOn_bad_A2)

### Theorem

Let $`M, G, R, X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)),
$`v_0, w_0, d_0, n, u, w, e \in \mathbb{N}`$ and
$`\ell \in \mathbb{N}\times\mathbb{N}`$, and put $`\mathrm{blk} := (v_0,w_0) :: R`$.
Assume the following.

```math
\begin{aligned}
&\text{(hM)}\quad M \in \mathrm{ST\_PS}, \cr
&\text{(hMon)}\quad \mathrm{ArgDomCoreOn}(M), \cr
&\text{(hMeq)}\quad M = G \mathbin{+\!\!+} \mathrm{blk} \mathbin{+\!\!+} (\ell), \cr
&\text{(hRgt)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hlp)}\quad v_0 \lt \ell_1, \cr
&\text{(hdisj)}\quad \bigl(d_0 = 0 \wedge \ell_2 = 0 \wedge \ell_1 = v_0 + 1\bigr) \cr
&\qquad\qquad\quad\ \vee\ \bigl(0 \lt d_0 \wedge \ell_2 = w_0 + 1 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 (\lvert M\rvert - 1)\bigr), \cr
&\text{(hSTn)}\quad \forall m,\ 1 \le m \to G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m) \in \mathrm{ST\_PS}, \cr
&\text{(hIH)}\quad \forall m,\ 1 \le m \to m \lt n \to
   \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr), \cr
&\text{(hn)}\quad 1 \le n, \cr
&\text{(heq)}\quad G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n)
   = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr)
     \mathbin{+\!\!+} Z, \cr
&\text{(he)}\quad 0 \lt e, \cr
&\text{(h1)}\quad \forall x \in A_1,\ u \lt x_1, \cr
&\text{(h2)}\quad \forall x \in B,\ u + e \lt x_1, \cr
&\text{(h3)}\quad \forall x \in A_2,\ u \lt x_1, \cr
&\text{(h4)}\quad A_2 = () \ \vee\ (\mathrm{head}\,A_2)_1 \le u + e, \cr
&\text{(h5)}\quad Z = () \ \vee\ (\mathrm{head}\,Z)_1 \le u, \cr
&\text{(h6)}\quad \mathrm{SpineOK}(A_1,\ u+e,\ w), \cr
&\text{(hcaseL)}\quad \lvert X\rvert \lt \lvert G\rvert + (\lvert R\rvert + 1), \cr
&\text{(hcaseR)}\quad \lvert G\rvert + (\lvert R\rvert + 1) \le \lvert X\rvert + (\lvert A_1\rvert + 1).
\end{aligned}
```

($`\mathrm{ST\_PS}`$ [D.ST_PS](Pss.md#d-ST_PS), $`\mathrm{ArgDomCoreOn}`$ [D.ArgDomCoreOn](ArgDom.md#d-ArgDomCoreOn),
$`\to^M_1`$ [D.nextrel1](Pss.md#d-nextrel1), $`\mathrm{copies}_{d_0}`$ [D.copies](Cnf-2.md#d-copies),
$`\mathrm{SpineOK}`$ [D.SpineOK](ArgDom.md#d-SpineOK))

Then

```math
B \preceq_{\mathrm{lex}}
  \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e} .
```

($`\preceq_{\mathrm{lex}}`$ [D.sle](Cofinality.md#d-sle), $`L^{+e}`$ [D.shiftr0](Cnf-2.md#d-shiftr0))

### Proof

**Notation.** In what follows we write

```math
L := \lvert R\rvert + 1 = \lvert\mathrm{blk}\rvert, \quad
p := \lvert G\rvert + L, \quad
N := G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n), \quad
i := \lvert X\rvert, \quad
j := \lvert X\rvert + (\lvert A_1\rvert + 1)
```

Hypothesis (hcaseL) reads $`i \lt p`$, and hypothesis (hcaseR) reads $`p \le j`$.

**Step 0: $`2 \le n`$.**
Applying [T.argdom_pos](ArgDom-2.md#t-argdom_pos) to (heq) gives $`j \lt \lvert N\rvert`$.
On the other hand, [T.copies_length](ArgDom-3.md#t-copies_length) gives
$`\lvert \mathrm{copies}_{d_0}(\mathrm{blk}, n)\rvert = n \cdot L`$, so

```math
\lvert N\rvert = \lvert G\rvert + n \cdot L .
```

If $`n = 1`$, then $`\lvert N\rvert = \lvert G\rvert + L = p`$, hence $`j \lt p`$, which
contradicts $`p \le j`$ from (hcaseR). Since $`1 \le n`$ by (hn), we get $`2 \le n`$.
From now on we write $`n = m + 1`$ with $`1 \le m`$.

**Step 1: peel off copy $`0`$ and cut at the boundary $`p`$.**
By [T.copies_succ_front](Cnf-3.md#t-copies_succ_front),

```math
N = G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1)
  = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0}
```

Combining this with (heq) and re-bracketing by associativity gives

```math
\begin{aligned}
&(\ast)\qquad
  &&(G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0} \cr
& &&= \bigl(X \mathbin{+\!\!+} ((u,w))\bigr)
   \mathbin{+\!\!+} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))\bigr)
\end{aligned}
```

By (hcaseL) we have $`\lvert X \mathbin{+\!\!+} ((u,w))\rvert = i + 1 \le p = \lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert`$,
so applying [T.split_append_left](ArgDom-3.md#t-split_append_left) to $`(\ast)`$ yields
$`C \in \mathrm{PairSeq}`$ with

```math
\begin{aligned}
&\text{(C1)}\ &&G \mathbin{+\!\!+} \mathrm{blk} = \bigl(X \mathbin{+\!\!+} ((u,w))\bigr) \mathbin{+\!\!+} C,
\qquad \cr
&\text{(C2)}\ &&A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)) \cr
& &&= C \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0} .
\end{aligned}
```

Comparing the lengths of the two sides of (C1) gives $`\lvert C\rvert = p - (i+1)`$.
Hypothesis (hcaseR) says $`p \le i + \lvert A_1\rvert + 1`$, that is, $`\lvert C\rvert \le \lvert A_1\rvert`$, so
applying [T.split_append_left](ArgDom-3.md#t-split_append_left) to (C2) again yields $`D \in \mathrm{PairSeq}`$ with

```math
\text{(D1)}\ A_1 = C \mathbin{+\!\!+} D,
\qquad
\text{(D2)}\ \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0}
  = D \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)) .
```

Comparing the lengths in (D1) gives $`\lvert A_1\rvert = \lvert C\rvert + \lvert D\rvert`$.

Every element of a $`d_0`$-shifted sequence has first entry at least $`d_0`$. Indeed, if
$`y \in \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0}`$, then by
[T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) it has the form $`y = (z_1 + d_0,\ z_2)`$, whence
$`d_0 \le z_1 + d_0 = y_1`$. Applying this to the element $`(u+e,w)`$ of the right-hand side of (D2) gives

```math
(\dagger)\qquad d_0 \le u + e
```

For the same reason, $`\forall y \in D,\ d_0 \le y_1`$.

**Step 2: shift back and write down the smaller tower.**
Applying $`(\cdot)^{-d_0}`$ ([D.shiftl0](ArgDom-2.md#d-shiftl0)) to both sides of (D2) and using [T.shiftl0_shiftr0](ArgDom-2.md#t-shiftl0_shiftr0),
[T.shiftl0_append](ArgDom-2.md#t-shiftl0_append) and [T.shiftl0_cons](ArgDom-2.md#t-shiftl0_cons) gives

```math
\text{(S)}\qquad \mathrm{copies}_{d_0}(\mathrm{blk}, m)
  = D^{-d_0} \mathbin{+\!\!+} (u+e-d_0,\ w) ::
      \bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
```

**Step 3: trichotomy between $`\lvert X\rvert`$ and $`\lvert G\rvert + \lvert D\rvert`$.**
By trichotomy for the natural numbers, exactly one of the following three cases holds.

**(a) The case $`\lvert X\rvert \lt \lvert G\rvert + \lvert D\rvert`$.**
Since $`1 \le m`$, we may write $`m = m'' + 1`$.
By [T.copies_succ_front](Cnf-3.md#t-copies_succ_front),
$`\mathrm{copies}_{d_0}(\mathrm{blk}, m) = \mathrm{blk} \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m'')^{+d_0}`$,
so $`\mathrm{blk} \sqsubseteq \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$.
Also (S) gives $`D^{-d_0} \sqsubseteq \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$, and
$`\lvert D^{-d_0}\rvert = \lvert D\rvert`$.

By (C1), $`X \mathbin{+\!\!+} ((u,w)) \sqsubseteq G \mathbin{+\!\!+} \mathrm{blk}`$, and by
[T.prefix_append_left](ArgDom-3.md#t-prefix_append_left) both
$`G \mathbin{+\!\!+} \mathrm{blk} \sqsubseteq G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$ and
$`G \mathbin{+\!\!+} D^{-d_0} \sqsubseteq G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$ hold.
Of two prefixes of one and the same sequence, the shorter one is a prefix of the longer one. Here the lengths
satisfy $`i + 1 \le \lvert G\rvert + \lvert D\rvert`$ (the condition of case (a)), so

```math
X \mathbin{+\!\!+} ((u,w)) \sqsubseteq G \mathbin{+\!\!+} D^{-d_0}
```

and hence there is $`A_1' \in \mathrm{PairSeq}`$ with

```math
\text{(A1')}\qquad G \mathbin{+\!\!+} D^{-d_0} = \bigl(X \mathbin{+\!\!+} ((u,w))\bigr) \mathbin{+\!\!+} A_1',
\qquad \lvert A_1'\rvert = \lvert G\rvert + \lvert D\rvert - (i+1)
```

Combining (S) with (A1'), the smaller tower can be written as

```math
\begin{aligned}
&\text{(Nm)}\qquad &&G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m) \cr
& &&= \bigl((X \mathbin{+\!\!+} ((u,w))) \mathbin{+\!\!+} A_1'\bigr) \mathbin{+\!\!+} (u+e-d_0,\ w) \cr
& &&\qquad ::
      \bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
\end{aligned}
```

On the other hand, [T.copies_succ_back](Cofinality-3.md#t-copies_succ_back) gives

```math
G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1)
  = \bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr) \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}
```

Combining this with (Nm) and with $`(\ast)`$ gives two presentations that share the left factor
$`X \mathbin{+\!\!+} ((u,w))`$. Cancelling that left factor gives

```math
\begin{aligned}
&\text{(K)}\qquad
  &&A_1 \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr) \cr
& &&= A_1' \mathbin{+\!\!+} (u+e-d_0,\ w) \cr
& &&\qquad ::
   \Bigl(\bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
     \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}\Bigr)
\end{aligned}
```

Now $`\lvert A_1'\rvert \le \lvert A_1\rvert`$
(by $`\lvert A_1\rvert = \lvert C\rvert + \lvert D\rvert`$, $`\lvert C\rvert = p - (i+1)`$,
$`\lvert A_1'\rvert = \lvert G\rvert + \lvert D\rvert - (i+1)`$ and $`\lvert G\rvert \le p`$), so
applying [T.split_append_left](ArgDom-3.md#t-split_append_left) to (K) yields $`W`$ with

```math
A_1 = A_1' \mathbin{+\!\!+} W,
\qquad
(u+e-d_0,\ w) :: \Bigl(\cdots\Bigr) = W \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr).
```

Comparing lengths gives $`\lvert W\rvert = \lvert A_1\rvert - \lvert A_1'\rvert = L`$, and $`1 \le L`$, so
$`W \ne ()`$, that is, $`W = W_0 :: W'`$. Comparing the heads of the second equation gives
$`W_0 = (u+e-d_0,\ w)`$, and comparing the remainders gives

```math
\text{(W)}\qquad
\bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr) \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}
 = W' \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

Therefore

```math
\text{(A1dec)}\qquad A_1 = A_1' \mathbin{+\!\!+} (u+e-d_0,\ w) :: W' .
```

Since $`(u+e-d_0,\ w) \in A_1`$, (h1) gives $`u \lt u+e-d_0`$, that is,

```math
(\ddagger)\qquad d_0 \lt e, \qquad u + e - d_0 = u + (e - d_0) .
```

**(a-1) The decomposition for the smaller tower.** Put

```math
A_2' := \mathrm{tw}_u\bigl(A_2^{-d_0}\bigr), \qquad
Z_2 := \mathrm{dw}_u\bigl(A_2^{-d_0}\bigr) \mathbin{+\!\!+} Z^{-d_0}
```

The following five statements hold.

- $`A_2' \mathbin{+\!\!+} Z_2 = A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0}`$:
  the concatenation of $`\mathrm{tw}_u`$ and $`\mathrm{dw}_u`$ is the original sequence.
- $`A_2' \sqsubseteq A_2^{-d_0}`$: $`\mathrm{tw}_u L`$ is a prefix of $`L`$.
- $`\forall x \in A_2',\ u \lt x_1`$: every element $`x`$ of $`\mathrm{tw}_u L`$ satisfies $`u \lt x_1`$.
- $`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u + (e-d_0)`$:
  if $`A_2 = ()`$ then $`A_2^{-d_0} = ()`$ and $`A_2' = ()`$.
  If $`A_2 = a :: A_2''`$ then the second disjunct of (h4) gives $`a_1 \le u+e`$, and
  $`A_2^{-d_0} = (a_1 - d_0,\ a_2) :: (A_2'')^{-d_0}`$.
  If $`u \lt a_1 - d_0`$ then the head of $`A_2'`$ is $`(a_1-d_0,\ a_2)`$ and
  $`a_1 - d_0 \le u + e - d_0 = u + (e-d_0)`$ (by $`(\ddagger)`$).
  If $`\neg(u \lt a_1 - d_0)`$ then $`A_2' = ()`$.
- $`Z_2 = () \vee (\mathrm{head}\,Z_2)_1 \le u`$:
  if $`\mathrm{dw}_u(A_2^{-d_0}) = z :: Z''`$ then the definition of $`\mathrm{dw}`$ gives $`\neg(u \lt z_1)`$, that is, $`z_1 \le u`$.
  If $`\mathrm{dw}_u(A_2^{-d_0}) = ()`$ then $`Z_2 = Z^{-d_0}`$; if $`Z = ()`$ then $`Z_2 = ()`$, and
  if $`Z = z :: Z''`$ then the second disjunct of (h5) gives $`z_1 \le u`$, whence $`z_1 - d_0 \le u`$.

Together with (Nm) this gives

```math
\begin{aligned}
&\text{(eq')}\qquad &&G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m) \cr
& &&= \Bigl(X \mathbin{+\!\!+} (u,w) :: \bigl(A_1' \mathbin{+\!\!+} (u + (e-d_0),\ w) \cr
& &&\qquad ::
     (B^{-d_0} \mathbin{+\!\!+} A_2')\bigr)\Bigr) \mathbin{+\!\!+} Z_2
\end{aligned}
```

In order to apply (hIH) to $`m`$ (note $`1 \le m`$ and $`m \lt m+1 = n`$), we check the remaining
hypotheses of $`\mathrm{ArgDomCoreOn}`$.

- $`0 \lt e - d_0`$: by $`(\ddagger)`$.
- $`\forall x \in A_1',\ u \lt x_1`$: by (A1dec) every element of $`A_1'`$ is an element of $`A_1`$, so this is (h1).
- $`\forall x \in B^{-d_0},\ u + (e-d_0) \lt x_1`$: such an $`x`$ is of the form $`x = (y_1 - d_0,\ y_2)`$ with $`y \in B`$.
  By (h2), $`u + e \lt y_1`$, and together with $`d_0 \le u+e`$ from $`(\dagger)`$ this gives
  $`y_1 - d_0 \gt u + e - d_0 = u + (e-d_0)`$.
- $`\forall x \in A_2',\ u \lt x_1`$, $`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u+(e-d_0)`$ and
  $`Z_2 = () \vee (\mathrm{head}\,Z_2)_1 \le u`$: shown above.

**(a-2) $`\mathrm{SpineOK}`$ for the smaller tower.**
It remains to prove $`\mathrm{SpineOK}(A_1',\ u+(e-d_0),\ w)`$.
Let $`U, V \in \mathrm{PairSeq}`$ and $`x \in \mathbb{N}\times\mathbb{N}`$ satisfy

```math
A_1' = U \mathbin{+\!\!+} x :: V, \qquad x_1 \lt u + (e-d_0), \qquad \forall y \in V,\ x_1 \lt y_1
```

We must show $`w \le x_2`$. Put $`Y := (X \mathbin{+\!\!+} ((u,w))) \mathbin{+\!\!+} U`$; then (A1') gives

```math
\text{(GSD)}\qquad Y \mathbin{+\!\!+} x :: V = G \mathbin{+\!\!+} D^{-d_0}
```

We distinguish cases according to how $`\lvert Y\rvert`$ and $`\lvert G\rvert`$ compare.

**The case $`\lvert Y\rvert \lt \lvert G\rvert`$.**
Here $`\lvert Y \mathbin{+\!\!+} (x)\rvert \le \lvert G\rvert`$, so applying
[T.split_append_left](ArgDom-3.md#t-split_append_left) to (GSD) yields $`V_3`$ with

```math
G = \bigl(Y \mathbin{+\!\!+} (x)\bigr) \mathbin{+\!\!+} V_3, \qquad V = V_3 \mathbin{+\!\!+} D^{-d_0} .
```

Substituting this into (C1) and cancelling the common left factor $`X \mathbin{+\!\!+} ((u,w))`$ gives

```math
C = \bigl(U \mathbin{+\!\!+} (x)\bigr) \mathbin{+\!\!+} \bigl(V_3 \mathbin{+\!\!+} \mathrm{blk}\bigr)
```

and together with (D1) this gives

```math
A_1 = U \mathbin{+\!\!+} x :: \bigl((V_3 \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} D\bigr)
```

Next we show $`x_1 \lt v_0`$. Since $`\mathrm{blk} \ne ()`$ and $`1 \le m`$,
[T.copies_headI](ArgDom-2.md#t-copies_headI) gives
$`\mathrm{head}\,\mathrm{copies}_{d_0}(\mathrm{blk}, m) = \mathrm{head}\,\mathrm{blk} = (v_0,w_0)`$.
We distinguish cases according to the head of the right-hand side of (S).

- The case $`D^{-d_0} = ()`$. The head of the right-hand side of (S) is $`(u+e-d_0,\ w)`$, so
  $`u + e - d_0 = v_0`$. By $`(\ddagger)`$, $`u+(e-d_0) = v_0`$, and the hypothesis
  $`x_1 \lt u+(e-d_0)`$ gives $`x_1 \lt v_0`$.
- The case $`D^{-d_0} = s :: S'`$. The head of the right-hand side of (S) is $`s`$, so $`s = (v_0,w_0)`$.
  From $`V = V_3 \mathbin{+\!\!+} D^{-d_0}`$ we get $`s \in V`$, and the hypothesis $`\forall y \in V,\ x_1 \lt y_1`$
  gives $`x_1 \lt s_1 = v_0`$.

We now apply (h6) with $`U`$, $`(V_3 \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} D`$ and $`x`$. Its three conditions are checked as follows.

- The decomposition $`A_1 = U \mathbin{+\!\!+} x :: ((V_3 \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} D)`$: shown above.
- $`x_1 \lt u + e`$: $`x_1 \lt u + (e-d_0) \le u + e`$.
- $`\forall y \in (V_3 \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} D,\ x_1 \lt y_1`$: distinguish cases according to the part $`y`$ lies in.
  If $`y \in V_3`$ then $`y \in V`$, so this is the hypothesis.
  If $`y = (v_0,w_0)`$ then $`x_1 \lt v_0 = y_1`$.
  If $`y \in R`$ then (hRgt) gives $`v_0 \lt y_1`$, which together with $`x_1 \lt v_0`$ gives $`x_1 \lt y_1`$.
  If $`y \in D`$ then (D2) gives $`y \in \mathrm{copies}_{d_0}(\mathrm{blk}, m)^{+d_0}`$, so by
  [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) we may write $`y = (z_1+d_0,\ z_2)`$ with
  $`z \in \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$. Since (hRgt) gives $`\forall x \in R,\ v_0 \le x_1`$,
  [T.copies_v0_le](Cnf-3.md#t-copies_v0_le) applies and yields $`v_0 \le z_1 \le z_1 + d_0 = y_1`$,
  hence $`x_1 \lt v_0 \le y_1`$.

This gives $`w \le x_2`$.

**The case $`\lvert G\rvert \le \lvert Y\rvert`$.**
Applying [T.split_append_left](ArgDom-3.md#t-split_append_left) to (GSD) yields $`U_2`$ with

```math
Y = G \mathbin{+\!\!+} U_2, \qquad D^{-d_0} = U_2 \mathbin{+\!\!+} x :: V .
```

Step 1 showed $`\forall y \in D,\ d_0 \le y_1`$, so
[T.shiftr0_shiftl0](ArgDom-2.md#t-shiftr0_shiftl0) gives $`(D^{-d_0})^{+d_0} = D`$.
Applying $`(\cdot)^{+d_0}`$ to both sides of the second equation and using
[T.shiftr0_append](Cofinality-3.md#t-shiftr0_append) and
[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons) gives

```math
D = U_2^{+d_0} \mathbin{+\!\!+} (x_1 + d_0,\ x_2) :: V^{+d_0}
```

We apply (h6) with $`C \mathbin{+\!\!+} U_2^{+d_0}`$, $`V^{+d_0}`$ and $`(x_1+d_0,\ x_2)`$.

- The decomposition: by (D1),
  $`A_1 = C \mathbin{+\!\!+} D = (C \mathbin{+\!\!+} U_2^{+d_0}) \mathbin{+\!\!+} (x_1+d_0,\ x_2) :: V^{+d_0}`$.
- $`x_1 + d_0 \lt u+e`$: from $`x_1 \lt u+(e-d_0)`$ and $`d_0 \lt e`$ of $`(\ddagger)`$ we get
  $`x_1 + d_0 \lt u + (e-d_0) + d_0 = u + e`$.
- $`\forall y \in V^{+d_0},\ x_1 + d_0 \lt y_1`$: such a $`y`$ is of the form $`y = (z_1+d_0,\ z_2)`$ with $`z \in V`$, and
  the hypothesis $`x_1 \lt z_1`$ gives $`x_1 + d_0 \lt z_1 + d_0 = y_1`$.

This gives $`w \le (x_1+d_0,\ x_2)_2 = x_2`$. This completes the proof of
$`\mathrm{SpineOK}(A_1',\ u+(e-d_0),\ w)`$.

**(a-3) Lifting the conclusion.**
Applying (hIH) to $`m`$ and supplying (eq') together with the hypotheses checked in (a-1) and (a-2) gives

```math
\text{(core)}\qquad B^{-d_0} \preceq_{\mathrm{lex}}
  \bigl(A_1' \mathbin{+\!\!+} (u+(e-d_0),\ w) :: (B^{-d_0} \mathbin{+\!\!+} A_2')\bigr)^{+(e-d_0)}
```

We first show

```math
B^{-d_0} \mathbin{+\!\!+} A_2' \ \sqsubseteq\ W' \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)
```

By (W) and $`A_2' \mathbin{+\!\!+} Z_2 = A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0}`$,

```math
\bigl(B^{-d_0} \mathbin{+\!\!+} A_2'\bigr) \mathbin{+\!\!+}
  \bigl(Z_2 \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}\bigr)
 = W' \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

so $`B^{-d_0} \mathbin{+\!\!+} A_2'`$ is a prefix of the right-hand side. Moreover
$`W' \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)`$ is a prefix of
$`W' \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))`$. As for the lengths,
$`\lvert A_2'\rvert \le \lvert A_2^{-d_0}\rvert = \lvert A_2\rvert`$ gives

```math
\lvert B^{-d_0} \mathbin{+\!\!+} A_2'\rvert = \lvert B\rvert + \lvert A_2'\rvert
 \le \lvert W'\rvert + 1 + \lvert B\rvert + \lvert A_2\rvert
 = \lvert W' \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\rvert
```

and since of two prefixes of one and the same sequence the shorter one is a prefix of the longer one, the claim follows.
Using (A1dec) and $`(\ddagger)`$ and applying [T.prefix_cons_append](ArgDom-3.md#t-prefix_cons_append) to this, we obtain

```math
A_1' \mathbin{+\!\!+} (u+(e-d_0),\ w) :: (B^{-d_0} \mathbin{+\!\!+} A_2')
 \ \sqsubseteq\ A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)
```

Applying [T.shiftr0_prefix](ArgDom-3.md#t-shiftr0_prefix) with $`e-d_0`$, this prefix relation is preserved by
$`(\cdot)^{+(e-d_0)}`$, so for some $`T`$

```math
\begin{aligned}
&\bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+(e-d_0)} \cr
&\qquad = \bigl(A_1' \mathbin{+\!\!+} (u+(e-d_0),\ w) :: (B^{-d_0} \mathbin{+\!\!+} A_2')\bigr)^{+(e-d_0)}
   \mathbin{+\!\!+} T
\end{aligned}
```

Applying [T.sle_append_mono](Cofinality.md#t-sle_append_mono) to (core) gives

```math
B^{-d_0} \preceq_{\mathrm{lex}}
  \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+(e-d_0)}
```

By (h2) and $`(\dagger)`$ we have $`\forall x \in B,\ d_0 \le u + e \lt x_1`$, so
[T.shiftr0_shiftl0](ArgDom-2.md#t-shiftr0_shiftl0) gives $`(B^{-d_0})^{+d_0} = B`$.
Applying [T.sle_shiftr0](ArgDom.md#t-sle_shiftr0) with $`d_0`$ and using
[T.shiftr0_add](ArgDom-3.md#t-shiftr0_add) together with $`d_0 + (e-d_0) = e`$ (by $`(\ddagger)`$) gives

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

This is the desired conclusion.

**(b) The case $`\lvert X\rvert = \lvert G\rvert + \lvert D\rvert`$.**
By (S),

```math
\begin{aligned}
&\text{(Nm)}\qquad &&G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m) \cr
& &&= \bigl(G \mathbin{+\!\!+} D^{-d_0}\bigr) \mathbin{+\!\!+} (u+e-d_0,\ w) \cr
& &&\qquad ::
      \bigl(B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})\bigr)
\end{aligned}
```

and [T.copies_succ_back](Cofinality-3.md#t-copies_succ_back) gives

```math
G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1)
  = \bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr) \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}
```

Together with $`(\ast)`$, these give

```math
\begin{aligned}
&\text{(key)}\qquad
  &&\bigl(X \mathbin{+\!\!+} ((u,w))\bigr) \mathbin{+\!\!+}
  \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))\bigr) \cr
& &&= \bigl(G \mathbin{+\!\!+} D^{-d_0}\bigr) \mathbin{+\!\!+}
  \Bigl((u+e-d_0,\ w) :: \bigl(\Sigma \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}\bigr)\Bigr)
\end{aligned}
```

Here we abbreviate $`\Sigma := B^{-d_0} \mathbin{+\!\!+} (A_2^{-d_0} \mathbin{+\!\!+} Z^{-d_0})`$.
By the condition of case (b),

```math
\lvert G \mathbin{+\!\!+} D^{-d_0}\rvert = \lvert G\rvert + \lvert D\rvert = \lvert X\rvert
 \le \lvert X \mathbin{+\!\!+} ((u,w))\rvert
```

so applying [T.split_append_left](ArgDom-3.md#t-split_append_left) to (key) yields $`K`$ with

```math
\begin{aligned}
&X \mathbin{+\!\!+} ((u,w)) = \bigl(G \mathbin{+\!\!+} D^{-d_0}\bigr) \mathbin{+\!\!+} K,
\qquad \cr
&(u+e-d_0,\ w) :: \bigl(\Sigma \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}\bigr) \cr
&\qquad = K \mathbin{+\!\!+} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))\bigr).
\end{aligned}
```

From the length of the first equation, $`\lvert K\rvert = (\lvert X\rvert + 1) - (\lvert G\rvert + \lvert D\rvert) = 1`$,
so we may write $`K = (k)`$. The two sides of the first equation agree in the length
$`\lvert X\rvert = \lvert G \mathbin{+\!\!+} D^{-d_0}\rvert`$, so splitting both sides into the part of length
$`\lvert X\rvert`$ and the single element after it and comparing them gives

```math
X = G \mathbin{+\!\!+} D^{-d_0}, \qquad k = (u,w)
```

Comparing the heads of the second equation gives $`k = (u+e-d_0,\ w)`$. Comparing first entries gives
$`u = u + e - d_0`$, which together with $`d_0 \le u+e`$ from $`(\dagger)`$ gives $`e = d_0`$.
Comparing the remainders of the second equation gives

```math
\text{(RW)}\qquad \Sigma \mathbin{+\!\!+} \mathrm{blk}^{+(m d_0)}
 = A_1 \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

Since $`B^{-d_0}`$ is a prefix of $`\Sigma`$, (RW) gives

```math
B^{-d_0} \ \sqsubseteq\ A_1 \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

Moreover

```math
A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)
 \ \sqsubseteq\ A_1 \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

and the lengths satisfy
$`\lvert B^{-d_0}\rvert = \lvert B\rvert \le \lvert A_1\rvert + 1 + \lvert B\rvert + \lvert A_2\rvert`$.
Since of two prefixes of one and the same sequence the shorter one is a prefix of the longer one, we obtain

```math
B^{-d_0} \ \sqsubseteq\ A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)
```

By (h2) and $`(\dagger)`$ we have $`\forall x \in B,\ d_0 \le x_1`$, and $`e = d_0`$, so
[T.shiftr0_shiftl0](ArgDom-2.md#t-shiftr0_shiftl0) gives $`(B^{-d_0})^{+e} = B`$.
Applying [T.shiftr0_prefix](ArgDom-3.md#t-shiftr0_prefix) with $`e`$ gives

```math
B \ \sqsubseteq\ \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

and [T.sle_of_prefix](ArgDom-3.md#t-sle_of_prefix) yields the conclusion.

**(c) The case $`\lvert G\rvert + \lvert D\rvert \lt \lvert X\rvert`$.**
We show that this case cannot occur. Since $`1 \le m`$, we may write $`m = m' + 1`$.

**(c-1) $`(u,w)`$ lies inside $`R`$.**
Interchanging the two sides of (C1) gives
$`(X \mathbin{+\!\!+} ((u,w))) \mathbin{+\!\!+} C = G \mathbin{+\!\!+} \mathrm{blk}`$; applying
[T.split_append_left](ArgDom-3.md#t-split_append_left) to it under
$`\lvert G\rvert \le \lvert X\rvert \lt \lvert X \mathbin{+\!\!+} ((u,w))\rvert`$ yields $`K`$ with

```math
X \mathbin{+\!\!+} ((u,w)) = G \mathbin{+\!\!+} K, \qquad \mathrm{blk} = K \mathbin{+\!\!+} C .
```

Here $`\lvert K\rvert = \lvert X\rvert + 1 - \lvert G\rvert`$, and the condition of case (c) gives
$`\lvert G\rvert \lt \lvert X\rvert`$, so $`\lvert K\rvert \ge 2 \gt 0`$, that is, $`K = k_0 :: K_1`$.
Comparing the tails in $`\mathrm{blk} = (v_0,w_0) :: R`$ gives $`R = K_1 \mathbin{+\!\!+} C`$.
The first equation can be rewritten as $`X \mathbin{+\!\!+} ((u,w)) = (G \mathbin{+\!\!+} (k_0)) \mathbin{+\!\!+} K_1`$, and
$`\lvert G \mathbin{+\!\!+} (k_0)\rvert = \lvert G\rvert + 1 \le \lvert X\rvert`$, so applying
[T.split_append_left](ArgDom-3.md#t-split_append_left) again yields $`T`$ with

```math
X = \bigl(G \mathbin{+\!\!+} (k_0)\bigr) \mathbin{+\!\!+} T, \qquad K_1 = T \mathbin{+\!\!+} ((u,w)) .
```

Hence

```math
\text{(Rdec)}\qquad R = T \mathbin{+\!\!+} (u,w) :: C
```

Since $`(u,w) \in R`$, (hRgt) gives $`v_0 \lt u`$.

**(c-2) The head of copy $`1`$ gives $`u \lt v_0 + d_0`$ and $`w \le w_0`$.**
By [T.copies_succ_cons](Cnf-3.md#t-copies_succ_cons) and
[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons),

```math
\text{(SC)}\qquad \mathrm{copies}_{d_0}(\mathrm{blk}, m'+1)^{+d_0}
 = (v_0+d_0,\ w_0) :: \Bigl(R \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m')^{+d_0}\Bigr)^{+d_0}
```

This is the left-hand side of (D2), so we distinguish cases on $`D`$.

**The case $`D = ()`$.** Comparing the heads of (D2) and (SC) gives
$`(v_0+d_0,\ w_0) = (u+e,\ w)`$, that is, $`v_0 + d_0 = u + e`$ and $`w_0 = w`$.
From $`0 \lt e`$ of (he) we get $`u \lt u + e = v_0 + d_0`$, and $`w \le w_0`$ holds as well.

**The case $`D = d_1 :: D'`$.** Comparing the heads of (D2) and (SC) gives $`d_1 = (v_0+d_0,\ w_0)`$,
and comparing the remainders gives

```math
\text{(rest)}\qquad
\Bigl(R \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m')^{+d_0}\Bigr)^{+d_0}
 = D' \mathbin{+\!\!+} (u+e,w) :: \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
```

By (D1), $`A_1 = C \mathbin{+\!\!+} (v_0+d_0,\ w_0) :: D'`$.
Applying (h1) to $`(v_0+d_0,\ w_0) \in A_1`$ gives $`u \lt v_0 + d_0`$, which together with
$`v_0 \lt u`$ from (c-1) gives $`0 \lt d_0`$.
Applying [T.copies_tl_gt](Cnf-3.md#t-copies_tl_gt) to (hRgt), $`0 \lt d_0`$ and $`1 \le m'+1`$
gives

```math
\forall y \in R \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m')^{+d_0},\ v_0 \lt y_1
```

and by [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) every element $`y`$ of the sequence obtained by shifting
this one by $`d_0`$ (that is, of the left-hand side of (rest)) satisfies $`v_0 + d_0 \lt y_1`$.
The right-hand side of (rest) contains $`(u+e,w)`$ and all elements of $`D'`$, so

```math
v_0 + d_0 \lt u + e, \qquad \forall y \in D',\ v_0 + d_0 \lt y_1
```

Hence (h6) applies with $`C`$, $`D'`$ and $`(v_0+d_0,\ w_0)`$
(the decomposition being $`A_1 = C \mathbin{+\!\!+} (v_0+d_0,w_0) :: D'`$), and gives $`w \le w_0`$.

In either case $`u \lt v_0 + d_0`$ and $`w \le w_0`$.
Together with $`v_0 \lt u`$ from (c-1) this gives $`0 \lt d_0`$.

**(c-3) Contradiction with the minimality condition.**
We distinguish cases on (hdisj). The first disjunct contains $`d_0 = 0`$, which contradicts $`0 \lt d_0`$ from (c-2).
In the case of the second disjunct, $`\ell_1 = v_0 + d_0`$ and $`\ell_2 = w_0 + 1`$ give
$`\ell = (v_0+d_0,\ w_0+1)`$. By (hMeq), $`\lvert M\rvert - 1 = \lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert`$,
so the fourth conjunct of the second disjunct reads

```math
\lvert G\rvert \to^{(G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} ((v_0+d_0,\,w_0+1))}_1
  \lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert
```

Applying [T.spineOK_of_nextrel1_strict](ArgDom-3.md#t-spineOK_of_nextrel1_strict) to it gives
$`\mathrm{SpineOK}(R,\ v_0+d_0,\ w_0+1)`$. Applying this to the decomposition
$`R = T \mathbin{+\!\!+} (u,w) :: C`$ of (Rdec), to $`u \lt v_0+d_0`$ ((c-2)) and to
$`\forall y \in C,\ u \lt y_1`$ (by (D1) every element of $`C`$ is an element of $`A_1`$, so this is (h1))
gives $`w_0 + 1 \le w`$. This contradicts $`w \le w_0`$ from (c-2).

Hence case (c) cannot occur. ∎
