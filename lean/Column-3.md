[← README](README.md) | [English](Column-3.md) | [Japanese](Column-3-ja.md) | Column [1](Column.md) [2](Column-2.md) **3** [4](Column-4.md)

<a id="t-getD_mem"></a>
## Theorem: an entry within range is a member (T.getD_mem)

### Theorem

Let $`L`$ be a sequence of pairs and suppose $`i \lt \lvert L\rvert`$. Then $`L\langle i\rangle \in L`$ ([D.entry](Pss.md#d-entry)).

### Proof

Since $`i \lt \lvert L\rvert`$, the first case of the definition of $`L\langle i\rangle`$ (D.entry) is selected,
so $`L\langle i\rangle`$ is the $`i`$-th element of $`L`$. The $`i`$-th element of a sequence is
a member of that sequence (as long as $`i`$ is within range). ∎

<a id="t-dominated_PM_zero"></a>
## Theorem: in a dominated block, row 0 is minimal only at the head (T.dominated_PM_zero)

### Theorem

Let $`v_0, w_0 \in \mathbb{N}`$, $`R \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) and $`q \in \mathbb{N}`$, and put
$`B := (v_0,w_0) :: R`$. Assume the following three conditions.

```math
\begin{aligned}
&\text{(hdom)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hq)}\quad q \lt \lvert B\rvert, \cr
&\text{(hPM)}\quad \forall r \lt q,\ B_{0,q} \le B_{0,r} .
\end{aligned}
```

Then $`q = 0`$.

### Proof

Suppose $`q \ne 0`$ and derive a contradiction. Since $`q \ne 0`$, we may write $`q = q' + 1`$.
As $`\lvert B\rvert = \lvert R\rvert + 1`$, (hq) gives $`q' \lt \lvert R\rvert`$.
By [T.getD_mem](#t-getD_mem) we have $`R\langle q'\rangle \in R`$, so (hdom) gives

```math
v_0 \lt R_{0,q'} .
```

On the other hand, applying (hPM) with $`r := 0`$ (note $`0 \lt q`$) yields $`B_{0,q} \le B_{0,0}`$.
Since $`B = (v_0,w_0) :: R`$, we have $`B\langle 0\rangle = (v_0,w_0)`$, that is, $`B_{0,0} = v_0`$,
and since $`B\langle q' + 1\rangle = R\langle q'\rangle`$, we have $`B_{0,q} = R_{0,q'}`$.
Hence $`R_{0,q'} \le v_0`$, contradicting $`v_0 \lt R_{0,q'}`$. ∎

<a id="t-r1ok_min_d0zero"></a>
## Theorem: a witness in the copied part (the case $`d_0 = 0`$) (T.r1ok_min_d0zero)

### Theorem

Let $`G, R \in \mathrm{PairSeq}`$, $`\ell \in \mathbb{N}\times\mathbb{N}`$, $`n, v_0, w_0 \in \mathbb{N}`$, and put
$`B := (v_0,w_0) :: R`$ and $`E := \mathrm{copyExp}(G,B,0,n)`$ ([D.copyExp](Column-2.md#d-copyExp)). Assume the following.

```math
\begin{aligned}
&\text{(hdom)}\quad \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hr)}\quad \mathrm{r1ok}\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr), \cr
&\text{(hk1)}\quad 0 \lt k, \qquad
 \text{(hk)}\quad k \lt n, \qquad
 \text{(hq)}\quad q \lt \lvert B\rvert, \cr
&\text{(hPM)}\quad \forall r \lt q,\ B_{0,q} \le B_{0,r}, \cr
&\text{(hpos)}\quad 0 \lt B_{0,q} + k \cdot 0 .
\end{aligned}
```

($`\mathrm{r1ok}`$ [D.r1ok](Column-2.md#d-r1ok))

Then there exists $`p`$ satisfying the following.

```math
\begin{aligned}
&p \lt \lvert G\rvert + (k\lvert B\rvert + q), \cr
&E_{0,p} + 1 = B_{0,q} + k \cdot 0, \cr
&\forall l,\ \bigl(p \lt l \wedge l \lt \lvert G\rvert + (k\lvert B\rvert + q)\bigr)
   \to B_{0,q} + k \cdot 0 \le E_{0,l}, \cr
&B_{1,q} \le E_{1,p} + 1 .
\end{aligned}
```

### Proof

Put $`H := G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$.
Applying [T.dominated_PM_zero](#t-dominated_PM_zero) to (hdom), (hq), (hPM) gives $`q = 0`$.
From now on let $`q = 0`$. Since $`B\langle 0\rangle = (v_0,w_0)`$, we have $`B_{0,0} = v_0`$ and $`B_{1,0} = w_0`$,
and since $`k \cdot 0 = 0`$, (hpos) yields $`0 \lt v_0`$.

Since $`0 \lt \lvert B\rvert`$, applying [T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) with $`q := 0`$ gives
$`H\langle \lvert G\rvert\rangle = B\langle 0\rangle = (v_0,w_0)`$.
By [T.hostM_length](Column-2.md#t-hostM_length) we have
$`\lvert G\rvert \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$, and
$`H_{0,\lvert G\rvert} = v_0 \gt 0`$.
Applying the hypothesis (hr) at the index $`\lvert G\rvert`$ yields a witness $`p`$ for column $`\lvert G\rvert`$ of $`H`$;
that is,

```math
\begin{aligned}
&p \lt \lvert G\rvert, \cr
&H_{0,p} + 1 = v_0, \cr
&\forall l\ \bigl(p \lt l \wedge l \lt \lvert G\rvert \to v_0 \le H_{0,l}\bigr), \cr
&w_0 \le H_{1,p} + 1 .
\end{aligned}
```

Since $`p \lt \lvert G\rvert`$, [T.hostM_getD_pre](Column-2.md#t-hostM_getD_pre) gives
$`H\langle p\rangle = G\langle p\rangle`$, so the second and the fourth of these become

```math
G_{0,p} + 1 = v_0, \qquad w_0 \le G_{1,p} + 1
```

We show that this $`p`$ is as required.
By [T.copyExp_getD_pre](Column-2.md#t-copyExp_getD_pre) we have $`E\langle p\rangle = G\langle p\rangle`$.

**The first condition.** $`p \lt \lvert G\rvert \le \lvert G\rvert + (k\lvert B\rvert + 0)`$.

**The second condition.** $`E_{0,p} + 1 = G_{0,p} + 1 = v_0 = v_0 + k \cdot 0 = B_{0,0} + k \cdot 0`$.

**The third condition.** Take $`l`$ with $`p \lt l`$ and $`l \lt \lvert G\rvert + (k\lvert B\rvert + 0)`$.
What has to be shown is $`v_0 + k \cdot 0 \le E_{0,l}`$, that is, $`v_0 \le E_{0,l}`$. Distinguish cases according to the position of $`l`$.

**(a) The case $`l \lt \lvert G\rvert`$.**
By [T.copyExp_getD_pre](Column-2.md#t-copyExp_getD_pre) we have $`E\langle l\rangle = G\langle l\rangle`$, and
the third condition above together with [T.hostM_getD_pre](Column-2.md#t-hostM_getD_pre) gives
$`v_0 \le H_{0,l} = G_{0,l} = E_{0,l}`$.

**(b) The case $`\lvert G\rvert \le l`$.**
By (hk) we have $`k \le n`$, hence $`k\lvert B\rvert \le n\lvert B\rvert`$, and
$`l \lt \lvert G\rvert + k\lvert B\rvert`$ gives $`l - \lvert G\rvert \lt n\lvert B\rvert`$.
Since $`0 \lt \lvert B\rvert`$, [T.index_decomp](Column-2.md#t-index_decomp) yields $`k', r`$ with
$`k' \lt n`$, $`r \lt \lvert B\rvert`$ and $`l - \lvert G\rvert = k'\lvert B\rvert + r`$,
so that $`l = \lvert G\rvert + (k'\lvert B\rvert + r)`$.
By [T.copyExp_getD_copy](Column-2.md#t-copyExp_getD_copy) we have
$`E_{0,l} = B_{0,r} + k' \cdot 0 = B_{0,r}`$.
We show $`v_0 \le B_{0,r}`$ by distinguishing cases on $`r`$.

- The case $`r = 0`$. Since $`B_{0,0} = v_0`$, we have $`v_0 \le v_0`$.
- The case $`r = r' + 1`$. Here $`B\langle r' + 1\rangle = R\langle r'\rangle`$, and
  $`r \lt \lvert B\rvert = \lvert R\rvert + 1`$ gives $`r' \lt \lvert R\rvert`$, so
  [T.getD_mem](#t-getD_mem) gives $`R\langle r'\rangle \in R`$, and
  (hdom) gives $`v_0 \lt R_{0,r'} = B_{0,r}`$.

**The fourth condition.** $`B_{1,0} = w_0 \le G_{1,p} + 1 = E_{1,p} + 1`$. ∎

<a id="t-r1ok_min_d0pos"></a>
## Theorem: a witness in the copied part (the case $`0 \lt d_0`$) (T.r1ok_min_d0pos)

### Theorem

Let $`G, R \in \mathrm{PairSeq}`$, $`\ell \in \mathbb{N}\times\mathbb{N}`$, $`n, v_0, w_0, d_0 \in \mathbb{N}`$, and put
$`B := (v_0,w_0) :: R`$ and $`E := \mathrm{copyExp}(G,B,d_0,n)`$. Assume the following.

```math
\begin{aligned}
&\text{(hdom)}\quad     &&\forall x \in R,\ v_0 \lt x_1, \cr
&\text{(hd0)}\quad      &&0 \lt d_0, \cr
&\text{(hlp)}\quad      &&\ell_1 = v_0 + d_0, \cr
&\text{(hstep)}\quad    &&\forall r,\ r + 1 \lt \lvert B\rvert \to B_{0,r+1} \le B_{0,r} + 1, \cr
&\text{(hlpstep)}\quad  &&\ell_1 \le B_{0,\lvert B\rvert - 1} + 1, \cr
&\text{(hclimb)}\quad   &&\forall r' \lt \lvert B\rvert,\
   \Bigl(B_{0,r'} = v_0 + d_0 - 1 \cr
& &&\qquad \wedge \bigl(\forall rr,\ r' \lt rr \wedge rr \lt \lvert B\rvert
   \to v_0 + d_0 \le B_{0,rr}\bigr)\Bigr) \cr
& &&\qquad \to w_0 \le B_{1,r'} + 1, \cr
&\text{(hk1)}\quad      &&0 \lt k, \qquad
 \text{(hk)}\quad k \lt n, \qquad
 \text{(hq)}\quad q \lt \lvert B\rvert, \cr
&\text{(hPM)}\quad      &&\forall r \lt q,\ B_{0,q} \le B_{0,r}, \cr
&\text{(hpos)}\quad     &&0 \lt B_{0,q} + k d_0 .
\end{aligned}
```

Then there exists $`p`$ satisfying the following.

```math
\begin{aligned}
&p \lt \lvert G\rvert + (k\lvert B\rvert + q), \cr
&E_{0,p} + 1 = B_{0,q} + k d_0, \cr
&\forall l,\ \bigl(p \lt l \wedge l \lt \lvert G\rvert + (k\lvert B\rvert + q)\bigr)
   \to B_{0,q} + k d_0 \le E_{0,l}, \cr
&B_{1,q} \le E_{1,p} + 1 .
\end{aligned}
```

### Proof

Applying [T.dominated_PM_zero](#t-dominated_PM_zero) to (hdom), (hq), (hPM) gives $`q = 0`$.
From now on let $`q = 0`$. Since $`B = (v_0,w_0) :: R`$, we have
$`0 \lt \lvert B\rvert`$ and $`B\langle 0\rangle = (v_0,w_0)`$, that is,
$`B_{0,0} = v_0`$ and $`B_{1,0} = w_0`$.

**A candidate witness.** Define the predicate $`P`$ by

```math
P(r) :\equiv B_{0,r} \le v_0 + d_0 - 1
```

By (hd0) we have $`d_0 \ge 1`$, hence $`v_0 \le v_0 + d_0 - 1`$, and since
$`B_{0,0} = v_0`$, the statement $`P(0)`$ holds.
The set $`\{\, r \le \lvert B\rvert - 1 \mid P(r)\,\}`$ contains $`0`$, hence is non-empty, and it is
bounded above by $`\lvert B\rvert - 1`$, hence has a greatest element. Call it $`r'`$; that is,

```math
P(r'), \qquad r' \le \lvert B\rvert - 1, \qquad
\forall rr,\ \bigl(r' \lt rr \wedge rr \le \lvert B\rvert - 1\bigr) \to \neg P(rr) .
```

From $`0 \lt \lvert B\rvert`$ we get $`r' \lt \lvert B\rvert`$.
Also, since $`0 \lt \lvert B\rvert`$, the conditions $`rr \lt \lvert B\rvert`$ and $`rr \le \lvert B\rvert - 1`$ are equivalent.
Now $`\neg P(rr)`$ says $`v_0 + d_0 - 1 \lt B_{0,rr}`$, and since $`d_0 \ge 1`$ gives
$`(v_0 + d_0 - 1) + 1 = v_0 + d_0`$, this is equivalent to $`v_0 + d_0 \le B_{0,rr}`$. Therefore

```math
(\dagger)\qquad \forall rr,\ \bigl(r' \lt rr \wedge rr \lt \lvert B\rvert\bigr)
  \to v_0 + d_0 \le B_{0,rr} .
```

**The row 0 value at the witness.** We show $`B_{0,r'} = v_0 + d_0 - 1`$.
From $`P(r')`$ we have $`B_{0,r'} \le v_0 + d_0 - 1`$. The reverse inequality is proved by
distinguishing cases according to the comparison of $`r'`$ with $`\lvert B\rvert - 1`$.

**(a) The case $`r' \lt \lvert B\rvert - 1`$.**
Since $`r' \lt r' + 1 \le \lvert B\rvert - 1`$, we have $`\neg P(r'+1)`$, that is,
$`v_0 + d_0 - 1 \lt B_{0,r'+1}`$. Moreover $`r' + 1 \lt \lvert B\rvert`$, so
(hstep) gives $`B_{0,r'+1} \le B_{0,r'} + 1`$. Hence

```math
v_0 + d_0 - 1 \lt B_{0,r'} + 1,
```

that is, $`v_0 + d_0 - 1 \le B_{0,r'}`$.

**(b) The case $`r' = \lvert B\rvert - 1`$.**
By (hlp) and (hlpstep) we have $`v_0 + d_0 = \ell_1 \le B_{0,\lvert B\rvert - 1} + 1 = B_{0,r'} + 1`$, hence
$`v_0 + d_0 - 1 \le B_{0,r'}`$.

In both cases $`v_0 + d_0 - 1 \le B_{0,r'}`$, and together with the upper bound

```math
(\ddagger)\qquad B_{0,r'} = v_0 + d_0 - 1 .
```

**Rewriting the products.** By (hk1) we have $`k \ge 1`$, so we may write $`k = (k-1) + 1`$, and

```math
k\lvert B\rvert = (k-1)\lvert B\rvert + \lvert B\rvert, \qquad
k d_0 = (k-1) d_0 + d_0
```

Moreover (hk) gives $`k - 1 \lt n`$.

**The witness.** Take $`p^{*} := \lvert G\rvert + \bigl((k-1)\lvert B\rvert + r'\bigr)`$.
By $`k - 1 \lt n`$ and $`r' \lt \lvert B\rvert`$,
[T.copyExp_getD_copy](Column-2.md#t-copyExp_getD_copy) applies and gives

```math
E\langle p^{*}\rangle = \bigl(B_{0,r'} + (k-1)d_0,\ B_{1,r'}\bigr)
```

We check the four conditions.

**The first condition.** From $`r' \lt \lvert B\rvert`$ we get
$`(k-1)\lvert B\rvert + r' \lt (k-1)\lvert B\rvert + \lvert B\rvert = k\lvert B\rvert`$, hence
$`p^{*} \lt \lvert G\rvert + (k\lvert B\rvert + 0)`$.

**The second condition.** By $`(\ddagger)`$ and $`d_0 \ge 1`$,

```math
E_{0,p^{*}} + 1 = (v_0 + d_0 - 1) + (k-1)d_0 + 1 = v_0 + d_0 + (k-1)d_0 = v_0 + k d_0
  = B_{0,0} + k d_0 .
```

**The third condition.** Take $`l`$ with $`p^{*} \lt l`$ and $`l \lt \lvert G\rvert + (k\lvert B\rvert + 0)`$.
Then $`\lvert G\rvert \le p^{*} \lt l`$. By (hk) we have $`k\lvert B\rvert \le n\lvert B\rvert`$, hence
$`l - \lvert G\rvert \lt k\lvert B\rvert \le n\lvert B\rvert`$, and
[T.index_decomp](Column-2.md#t-index_decomp) yields $`k'', rr`$ with $`k'' \lt n`$, $`rr \lt \lvert B\rvert`$ and
$`l - \lvert G\rvert = k''\lvert B\rvert + rr`$.
We show $`k'' = k - 1`$ by trichotomy.

- If $`k'' \lt k - 1`$, then $`k'' + 1 \le k - 1`$, hence
  $`(k''+1)\lvert B\rvert \le (k-1)\lvert B\rvert`$, that is,
  $`k''\lvert B\rvert + \lvert B\rvert \le (k-1)\lvert B\rvert`$.
  Since $`rr \lt \lvert B\rvert`$, we get
  $`l - \lvert G\rvert = k''\lvert B\rvert + rr \lt (k-1)\lvert B\rvert \le (k-1)\lvert B\rvert + r'`$,
  contradicting $`p^{*} \lt l`$.
- If $`k - 1 \lt k''`$, then $`k \le k''`$, hence $`k\lvert B\rvert \le k''\lvert B\rvert`$ and
  $`l - \lvert G\rvert = k''\lvert B\rvert + rr \ge k\lvert B\rvert`$, contradicting
  $`l - \lvert G\rvert \lt k\lvert B\rvert`$.

Hence $`k'' = k - 1`$. Then $`p^{*} \lt l`$ gives
$`(k-1)\lvert B\rvert + r' \lt (k-1)\lvert B\rvert + rr`$, that is, $`r' \lt rr`$.
By [T.copyExp_getD_copy](Column-2.md#t-copyExp_getD_copy) we have
$`E_{0,l} = B_{0,rr} + (k-1)d_0`$, and $`(\dagger)`$ gives $`v_0 + d_0 \le B_{0,rr}`$, hence

```math
B_{0,0} + k d_0 = v_0 + k d_0 = (v_0 + d_0) + (k-1)d_0 \le B_{0,rr} + (k-1)d_0 = E_{0,l} .
```

**The fourth condition.** Since $`E_{1,p^{*}} = B_{1,r'}`$, what has to be shown is
$`B_{1,0} = w_0 \le B_{1,r'} + 1`$. This is (hclimb) applied to $`r'`$, whose
premises are given by $`r' \lt \lvert B\rvert`$, $`(\ddagger)`$ and $`(\dagger)`$. ∎

<a id="t-hostM_getD_lp"></a>
## Theorem: the last entry of the concatenation $`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ (T.hostM_getD_lp)

### Theorem

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)
  \bigl\langle \lvert G\rvert + \lvert B\rvert\bigr\rangle = \ell .
```

### Proof

Since $`\lvert G \mathbin{+\!\!+} B\rvert = \lvert G\rvert + \lvert B\rvert`$, we have
$`\lvert G \mathbin{+\!\!+} B\rvert \le \lvert G\rvert + \lvert B\rvert`$, so applying
[T.getD_append_right](Column-2.md#t-getD_append_right) with $`G := G \mathbin{+\!\!+} B`$ and $`X := (\ell)`$ gives

```math
\bigl((G \mathbin{+\!\!+} B) \mathbin{+\!\!+} (\ell)\bigr)\bigl\langle \lvert G\rvert + \lvert B\rvert\bigr\rangle
  = (\ell)\bigl\langle (\lvert G\rvert + \lvert B\rvert) - (\lvert G\rvert + \lvert B\rvert)\bigr\rangle
  = (\ell)\langle 0\rangle
```

Since $`0 \lt 1 = \lvert (\ell)\rvert`$, we have $`(\ell)\langle 0\rangle = \ell`$. ∎

<a id="t-r1ok_Pred"></a>
## Theorem: the row 1 discipline is inherited by the predecessor (T.r1ok_Pred)

### Theorem

If $`\mathrm{r1ok}(M)`$, then $`\mathrm{r1ok}(\mathrm{Pred}\,M)`$ ([D.Pred](Pss.md#d-Pred)).

### Proof

By the case distinction in the definition of $`\mathrm{Pred}`$ (D.Pred).

- The case $`\lvert M\rvert \le 1`$. Then $`\mathrm{Pred}\,M = M`$, and the claim is the hypothesis itself.
- The case $`\lvert M\rvert \ge 2`$. Then $`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$, and it suffices to apply
  [T.r1ok_dropLast](Column-2.md#t-r1ok_dropLast). ∎

<a id="t-climb_bound"></a>
## Theorem: an upper bound on the row 1 value at the head of a block (T.climb_bound)

### Theorem

Let $`M, G, R \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0 \in \mathbb{N}`$ and $`\ell \in \mathbb{N}\times\mathbb{N}`$, and put
$`B := (v_0,w_0) :: R`$. Assume the following.

```math
\begin{aligned}
&\text{(hM)}\quad M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell), \cr
&\text{(hd0)}\quad 0 \lt d_0, \cr
&\text{(hlp1)}\quad \ell_1 = v_0 + d_0, \cr
&\text{(hwlt)}\quad w_0 \lt \ell_2, \cr
&\text{(hnl1)}\quad \lvert G\rvert \to^M_1 (\lvert M\rvert - 1), \cr
&\text{(hr')}\quad r' \lt \lvert B\rvert, \cr
&\text{(hlev)}\quad B_{0,r'} = v_0 + d_0 - 1, \cr
&\text{(hafter)}\quad \forall rr,\ \bigl(r' \lt rr \wedge rr \lt \lvert B\rvert\bigr)
   \to v_0 + d_0 \le B_{0,rr} .
\end{aligned}
```

($`\to^M_1`$ [D.nextrel1](Pss.md#d-nextrel1))

Then $`w_0 \le B_{1,r'} + 1`$.

### Proof

Distinguish cases according to whether $`r'`$ is $`0`$.

**(a) The case $`r' = 0`$.** From $`B = (v_0,w_0) :: R`$ we have $`B\langle 0\rangle = (v_0,w_0)`$,
that is, $`B_{1,0} = w_0`$. So what has to be shown is $`w_0 \le w_0 + 1`$, which holds.

**(b) The case $`0 \lt r'`$.**
In what follows we write $`M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$, by (hM).
By [T.hostM_length](Column-2.md#t-hostM_length) we have
$`\lvert M\rvert = \lvert G\rvert + \lvert B\rvert + 1`$, hence

```math
\lvert M\rvert - 1 = \lvert G\rvert + \lvert B\rvert .
```

First we compute two entries. By the definition of $`M_{0,j}`$ (D.entry) and
[T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) (using $`r' \lt \lvert B\rvert`$),

```math
M_{0,\lvert G\rvert + r'} = B_{0,r'} = v_0 + d_0 - 1 ,
```

and by [T.hostM_getD_lp](#t-hostM_getD_lp) and (hlp1),

```math
M_{0,\lvert G\rvert + \lvert B\rvert} = \ell_1 = v_0 + d_0 .
```

**The row 0 parent relation.** We show $`\lvert G\rvert + r' \to^M_0 \lvert G\rvert + \lvert B\rvert`$ ([D.nextrel0](Pss.md#d-nextrel0)).
We check the five conditions of the definition of $`\to^M_0`$ (D.nextrel0).

**(1)** From $`r' \lt \lvert B\rvert`$ we get
$`\lvert G\rvert + r' \lt \lvert G\rvert + \lvert B\rvert \lt \lvert M\rvert`$.

**(2)** $`\lvert G\rvert + \lvert B\rvert \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert M\rvert`$.

**(3)** From $`r' \lt \lvert B\rvert`$ we get $`\lvert G\rvert + r' \lt \lvert G\rvert + \lvert B\rvert`$.

**(4)** By (hd0) we have $`d_0 \ge 1`$, hence
$`M_{0,\lvert G\rvert + r'} = v_0 + d_0 - 1 \lt v_0 + d_0 = M_{0,\lvert G\rvert + \lvert B\rvert}`$.

**(5)** Take $`j`$ with $`\lvert G\rvert + r' \lt j`$ and $`j \lt \lvert G\rvert + \lvert B\rvert`$.
Put $`rr := j - \lvert G\rvert`$; then $`j = \lvert G\rvert + rr`$, $`r' \lt rr`$ and $`rr \lt \lvert B\rvert`$.
By [T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) we have $`M_{0,j} = B_{0,rr}`$, and
(hafter) gives $`v_0 + d_0 \le B_{0,rr}`$, that is,
$`M_{0,\lvert G\rvert + \lvert B\rvert} \le M_{0,j}`$.

**The row 0 ancestor relation.** Of the three conditions of the definition of $`\le^M_0`$ ([D.le0](Pss.md#d-le0)), (1) and (2) are (1) and (2) above, and
(3) is obtained as a chain consisting of a single $`\to^M_0`$ step. Hence

```math
\lvert G\rvert + r' \le^M_0 \lvert G\rvert + \lvert B\rvert = \lvert M\rvert - 1 .
```

**Applying maximality.** We apply condition (6) of the definition of $`\to^M_1`$ (D.nextrel1) for
(hnl1), that is, for $`\lvert G\rvert \to^M_1 (\lvert M\rvert - 1)`$, with $`j := \lvert G\rvert + r'`$.
Its premises are $`\lvert G\rvert \lt \lvert G\rvert + r'`$ (by $`0 \lt r'`$) and
$`\lvert G\rvert + r' \le^M_0 \lvert M\rvert - 1`$, just proved. Hence

```math
M_{1,\lvert M\rvert - 1} \le M_{1,\lvert G\rvert + r'} .
```

By the definition of $`M_{1,j}`$ (D.entry) and [T.hostM_getD_lp](#t-hostM_getD_lp) we have
$`M_{1,\lvert M\rvert - 1} = M_{1,\lvert G\rvert + \lvert B\rvert} = \ell_2`$, and by
[T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) we have $`M_{1,\lvert G\rvert + r'} = B_{1,r'}`$.
Therefore $`\ell_2 \le B_{1,r'}`$, and together with $`w_0 \lt \ell_2`$ from (hwlt),

```math
w_0 \lt \ell_2 \le B_{1,r'} \le B_{1,r'} + 1 . \qquad \blacksquare
```

<a id="t-r1ok_oper"></a>
## Theorem: the row 1 discipline is preserved by expansion (T.r1ok_oper)

### Theorem

If $`1 \le n`$, $`\mathrm{r1ok}(M)`$ and $`\mathrm{steps}_1(M)`$ ([D.steps1](Seqlex.md#d-steps1)), then
$`\mathrm{r1ok}(M[n])`$ ([D.oper](Pss.md#d-oper)).

### Proof

Put $`j_1 := \lvert M\rvert - 1`$ and $`i_1 := \mathrm{idx}_1(M, j_1)`$ ([D.idx1](Pss.md#d-idx1)).
Distinguish cases according to the four branches of the definition of $`M[n]`$ (D.oper).

**(a) The case $`j_1 = 0`$.**
By [T.oper_eq_self_of_short](Decrease.md#t-oper_eq_self_of_short) we have $`M[n] = M`$, and
the conclusion is the hypothesis $`\mathrm{r1ok}(M)`$ itself.

**(b) The case $`j_1 \ne 0`$ and $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$.**
By [T.oper_eq_pred_of_zero](Decrease.md#t-oper_eq_pred_of_zero) we have
$`M[n] = \mathrm{Pred}\,M`$, so it suffices to apply
[T.r1ok_Pred](#t-r1ok_Pred) to the hypothesis $`\mathrm{r1ok}(M)`$.

**(c) The case $`j_1 \ne 0`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$ ([D.hasParent](Pss.md#d-hasParent)).**
By [T.oper_eq_pred_of_noParent](Decrease.md#t-oper_eq_pred_of_noParent) we have
$`M[n] = \mathrm{Pred}\,M`$, so it suffices to apply [T.r1ok_Pred](#t-r1ok_Pred).

**(d) The case $`j_1 \ne 0`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and
$`\mathrm{hasParent}(M, i_1, j_1)`$.**
We have $`1 \lt \lvert M\rvert`$. Indeed, if $`\lvert M\rvert \le 1`$, then, since subtraction of natural numbers is
truncated at $`0`$, we would have $`j_1 = \lvert M\rvert - 1 = 0`$, contradicting the hypothesis
$`j_1 \ne 0`$ of this case.
Applying [T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks), we obtain
$`G, R \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0 \in \mathbb{N}`$ and $`\ell \in \mathbb{N}\times\mathbb{N}`$
satisfying the following. Put $`B := (v_0,w_0) :: R`$.

```math
\begin{aligned}
&\text{(1)}\ M = G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell), \cr
&\text{(2)}\ M[n] = G \mathbin{+\!\!+} B^{+0\cdot d_0} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B^{+(n-1)d_0}, \cr
&\text{(3)}\ \forall x \in R,\ v_0 \lt x_1, \cr
&\text{(5)}\ \bigl(d_0 = 0 \wedge i_1 = 0\bigr) \ \vee\
   \bigl(0 \lt d_0 \wedge w_0 \lt \ell_2 \wedge \ell_1 = v_0 + d_0
     \wedge \lvert G\rvert \to^M_1 j_1\bigr).
\end{aligned}
```

(Of the six assertions of [T.oper_bad_blocks](Decrease.md#t-oper_bad_blocks),
the four used below are listed with the same numbering. Also, by the definition of $`\mathrm{copyExp}`$ (D.copyExp),
the right-hand side of (2) is $`\mathrm{copyExp}(G,B,d_0,n)`$.)
By (1), the hypotheses give $`\mathrm{r1ok}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$ and
$`\mathrm{steps}_1(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$.

**The step condition.** For $`r`$ with $`r + 1 \lt \lvert B\rvert`$ we show
$`B_{0,r+1} \le B_{0,r} + 1`$.
By [T.hostM_length](Column-2.md#t-hostM_length) we have
$`\lvert G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\rvert = \lvert G\rvert + \lvert B\rvert + 1`$, and
$`r + 1 \lt \lvert B\rvert`$ gives
$`(\lvert G\rvert + r) + 1 \lt \lvert G\rvert + \lvert B\rvert + 1`$.
Applying [T.steps1_iff](Seqlex.md#t-steps1_iff) to
$`G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$ at the index $`\lvert G\rvert + r`$ gives

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + (r+1)}
  \le \bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + r} + 1
```

Applying [T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) to $`r + 1 \lt \lvert B\rvert`$ and
$`r \lt \lvert B\rvert`$, this is
$`B_{0,r+1} \le B_{0,r} + 1`$.

**The step condition at the end.** We show $`\ell_1 \le B_{0,\lvert B\rvert - 1} + 1`$.
Since $`0 \lt \lvert B\rvert`$, we have

```math
\bigl(\lvert G\rvert + (\lvert B\rvert - 1)\bigr) + 1 = \lvert G\rvert + \lvert B\rvert
  \lt \lvert G\rvert + \lvert B\rvert + 1
```

Applying [T.steps1_iff](Seqlex.md#t-steps1_iff) at the index $`\lvert G\rvert + (\lvert B\rvert - 1)`$ gives

```math
\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + \lvert B\rvert}
  \le \bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)_{0,\ \lvert G\rvert + (\lvert B\rvert - 1)} + 1
```

By [T.hostM_getD_lp](#t-hostM_getD_lp) the left-hand side is $`\ell_1`$, and by
[T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) (using $`\lvert B\rvert - 1 \lt \lvert B\rvert`$) the right-hand side is
$`B_{0,\lvert B\rvert - 1} + 1`$.

**Assembling.** We apply [T.r1ok_copyExp](Column-2.md#t-r1ok_copyExp) to
$`G, B, \ell, n, d_0`$. Its hypothesis (hr) is
$`\mathrm{r1ok}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$. To prove its hypothesis (hmin), take
$`0 \lt k`$, $`k \lt n`$, $`q \lt \lvert B\rvert`$, $`\forall r \lt q,\ B_{0,q} \le B_{0,r}`$ and
$`0 \lt B_{0,q} + k d_0`$, and distinguish cases according to the disjunction (5).

**The case of the first disjunct $`d_0 = 0 \wedge i_1 = 0`$.**
It suffices to apply [T.r1ok_min_d0zero](#t-r1ok_min_d0zero) to (3) and
$`\mathrm{r1ok}(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell))`$.

**The case of the second disjunct.** That is, the case where

```math
0 \lt d_0 \ \wedge\ w_0 \lt \ell_2 \ \wedge\ \ell_1 = v_0 + d_0
  \ \wedge\ \lvert G\rvert \to^M_1 j_1
```

holds. We apply [T.r1ok_min_d0pos](#t-r1ok_min_d0pos). Its hypothesis (hdom) is (3);
(hd0) and (hlp) are the first and third conjuncts of this disjunct; (hstep) and (hlpstep) are the
two step conditions proved above. The remaining hypothesis (hclimb) is the statement that, assuming
$`r' \lt \lvert B\rvert`$, $`B_{0,r'} = v_0 + d_0 - 1`$ and

```math
\forall rr,\ \bigl(r' \lt rr \wedge rr \lt \lvert B\rvert\bigr) \to v_0 + d_0 \le B_{0,rr}
```

one has $`w_0 \le B_{1,r'} + 1`$; it is obtained by applying
[T.climb_bound](#t-climb_bound) to (1) and to the first, second, third and fourth conjuncts of
this disjunct.

It follows that [T.r1ok_copyExp](Column-2.md#t-r1ok_copyExp) applies and gives
$`\mathrm{r1ok}(\mathrm{copyExp}(G,B,d_0,n))`$. By (2) this is
$`\mathrm{r1ok}(M[n])`$. ∎

<a id="t-r1ok_ST_PS"></a>
## Theorem: standard forms satisfy $`\mathrm{r1ok}`$ (T.r1ok_ST_PS)

### Theorem

If $`M \in \mathrm{ST\_PS}`$ ([D.ST_PS](Pss.md#d-ST_PS)), then $`\mathrm{r1ok}(M)`$.

### Proof

Induction on the derivation of $`\mathrm{ST\_PS}`$ ([T.ST_PS.rec](Pss.md#t-ST_PS.rec)). The induction predicate is

```math
\Phi(M) :\equiv \mathrm{r1ok}(M).
```

- **Base case** (rule (diag)): $`M = \Delta_0^v`$ ([D.diagSeq](Pss.md#d-diagSeq)).
  [T.r1ok_diagSeq](Column-2.md#t-r1ok_diagSeq) is exactly $`\Phi(\Delta_0^v)`$.

- **Inductive step** (rule (oper)): let $`N \in \mathrm{ST\_PS}`$ and $`1 \le n`$. Assume
  $`\Phi(N)`$, that is, $`\mathrm{r1ok}(N)`$; what has to be shown is $`\mathrm{r1ok}(N[n])`$.
  Applying [T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS) to $`N \in \mathrm{ST\_PS}`$ gives
  $`\mathrm{blockok}(0, N)`$ ([D.blockok](Seqlex.md#d-blockok)). The definition of $`\mathrm{blockok}`$ (D.blockok) is
  a conjunction of three statements, whose third conjunct is $`\mathrm{steps}_1(N)`$.
  Applying [T.r1ok_oper](#t-r1ok_oper) to $`1 \le n`$, $`\mathrm{r1ok}(N)`$ and $`\mathrm{steps}_1(N)`$
  gives $`\mathrm{r1ok}(N[n])`$. ∎

<a id="t-nextrel0_bound"></a>
## Theorem: the target of a row 0 parent step is within range (T.nextrel0_bound)

### Theorem

If $`a \to^M_0 b`$, then $`b \lt \lvert M\rvert`$.

### Proof

This is exactly the second condition of the definition of $`\to^M_0`$ (D.nextrel0). ∎

<a id="t-le0_le"></a>
## Theorem: the row 0 ancestor relation is contained in the index order (T.le0_le)

### Theorem

If $`a \le^M_0 b`$, then $`a \le b`$.

### Proof

By the third condition of the definition of $`\le^M_0`$ (D.le0) we have $`a \mathbin{(\to^M_0)^{*}} b`$.
Induction on the construction of the chain $`a \mathbin{(\to^M_0)^{*}} b`$. The induction predicate is

```math
\Phi(j) :\equiv a \le j .
```

- **Base case** ($`j = a`$, chain of length $`0`$): $`a \le a`$ holds by reflexivity of $`\le`$.

- **Inductive step** (from $`a \mathbin{(\to^M_0)^{*}} y`$ and $`y \to^M_0 z`$ to $`a \mathbin{(\to^M_0)^{*}} z`$):
  assume $`\Phi(y)`$, that is, $`a \le y`$.
  By [T.nextrel0_lt](Column.md#t-nextrel0_lt) we have $`y \lt z`$, hence $`a \le y \le z`$,
  that is, $`\Phi(z)`$. ∎

<a id="d-z0ok"></a>
## Definition: the discipline of columns whose row 0 is 0 (D.z0ok)

For $`M \in \mathrm{PairSeq}`$,

```math
\mathrm{z0ok}(M) :\iff \forall j,\ j \lt \lvert M\rvert \to \bigl(M_{0,j} = 0 \to M_{1,j} = 0\bigr).
```

That is, it reads: a column whose value in row $`0`$ is $`0`$ has value $`0`$ in row $`1`$ as well.

<a id="t-z0ok_diagSeq"></a>
## Theorem: the diagonal sequence satisfies $`\mathrm{z0ok}`$ (T.z0ok_diagSeq)

### Theorem

For every $`v \in \mathbb{N}`$, $`\mathrm{z0ok}(\Delta_0^v)`$.

### Proof

Take $`j`$ with $`j \lt \lvert \Delta_0^v\rvert`$ and $`(\Delta_0^v)_{0,j} = 0`$.
By [T.diagSeq0_length](Column-2.md#t-diagSeq0_length) we have $`\lvert \Delta_0^v\rvert = v + 1`$, hence
$`j \lt v + 1`$, and by [T.diagSeq0_getD](Column-2.md#t-diagSeq0_getD) we have
$`\Delta_0^v\langle j\rangle = (j, j)`$. By the definition of $`M_{i,j}`$ (D.entry),

```math
(\Delta_0^v)_{0,j} = j, \qquad (\Delta_0^v)_{1,j} = j
```

The hypothesis $`(\Delta_0^v)_{0,j} = 0`$ gives $`j = 0`$, hence
$`(\Delta_0^v)_{1,j} = j = 0`$. ∎

<a id="t-z0ok_take"></a>
## Theorem: prefixes satisfy $`\mathrm{z0ok}`$ (T.z0ok_take)

### Theorem

If $`\mathrm{z0ok}(M)`$, then for every $`m \in \mathbb{N}`$ we have
$`\mathrm{z0ok}(\mathrm{take}_m M)`$.

### Proof

Take $`j`$ with $`j \lt \lvert \mathrm{take}_m M\rvert`$ and $`(\mathrm{take}_m M)_{0,j} = 0`$.
Since $`\lvert \mathrm{take}_m M\rvert = \min(m, \lvert M\rvert)`$, we have
$`j \lt m`$ and $`j \lt \lvert M\rvert`$.

Applying [T.getD_take](Column-2.md#t-getD_take) to $`j \lt m`$ gives
$`(\mathrm{take}_m M)\langle j\rangle = M\langle j\rangle`$, hence

```math
(\mathrm{take}_m M)_{0,j} = M_{0,j}, \qquad (\mathrm{take}_m M)_{1,j} = M_{1,j}
```

By hypothesis $`M_{0,j} = 0`$, so applying the definition of $`\mathrm{z0ok}(M)`$ (D.z0ok) at
$`j \lt \lvert M\rvert`$ gives $`M_{1,j} = 0`$.
This is the same as $`(\mathrm{take}_m M)_{1,j} = 0`$. ∎

<a id="t-z0ok_Pred"></a>
## Theorem: the predecessor satisfies $`\mathrm{z0ok}`$ (T.z0ok_Pred)

### Theorem

If $`\mathrm{z0ok}(M)`$, then $`\mathrm{z0ok}(\mathrm{Pred}\,M)`$.

### Proof

By the case distinction in the definition of $`\mathrm{Pred}`$ (D.Pred).

- The case $`\lvert M\rvert \le 1`$. Then $`\mathrm{Pred}\,M = M`$, and the claim is the hypothesis itself.

- The case $`\lvert M\rvert \ge 2`$. Then
  $`\mathrm{Pred}\,M = \mathrm{dropLast}\,M = \mathrm{take}_{\lvert M\rvert - 1} M`$
  (each of these is the sequence consisting of the first $`\lvert M\rvert - 1`$ elements of $`M`$).
  Hence it suffices to apply [T.z0ok_take](#t-z0ok_take) with $`m := \lvert M\rvert - 1`$. ∎

<a id="t-z0ok_copyExp"></a>
## Theorem: the copy expansion satisfies $`\mathrm{z0ok}`$ (T.z0ok_copyExp)

### Theorem

Let $`G, B \in \mathrm{PairSeq}`$, $`\ell \in \mathbb{N}\times\mathbb{N}`$ and $`d_0, n \in \mathbb{N}`$.
If $`\mathrm{z0ok}\bigl(G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)\bigr)`$, then
$`\mathrm{z0ok}\bigl(\mathrm{copyExp}(G, B, d_0, n)\bigr)`$.

### Proof

Put $`E := \mathrm{copyExp}(G, B, d_0, n)`$ and $`H := G \mathbin{+\!\!+} B \mathbin{+\!\!+} (\ell)`$.
By [T.hostM_length](Column-2.md#t-hostM_length) we have
$`\lvert H\rvert = \lvert G\rvert + \lvert B\rvert + 1`$.

Take $`j`$ with $`j \lt \lvert E\rvert`$ and $`E_{0,j} = 0`$.
By [T.copyExp_length](Column-2.md#t-copyExp_length) we have
$`\lvert E\rvert = \lvert G\rvert + n \lvert B\rvert`$, hence
$`j \lt \lvert G\rvert + n \lvert B\rvert`$. Distinguish cases according to the comparison of $`j`$ with $`\lvert G\rvert`$.

**(a) The case $`j \lt \lvert G\rvert`$.**
By [T.copyExp_getD_pre](Column-2.md#t-copyExp_getD_pre) we have $`E\langle j\rangle = G\langle j\rangle`$, and by
[T.hostM_getD_pre](Column-2.md#t-hostM_getD_pre) we have $`H\langle j\rangle = G\langle j\rangle`$.
Since $`j \lt \lvert G\rvert \le \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$,
the definition of $`\mathrm{z0ok}(H)`$ (D.z0ok) can be applied at the index $`j`$. Its antecedent holds because
$`H_{0,j} = G_{0,j} = E_{0,j} = 0`$, so we obtain $`H_{1,j} = 0`$, that is,
$`E_{1,j} = G_{1,j} = H_{1,j} = 0`$.

**(b) The case $`\lvert G\rvert \le j`$.**
First we show $`0 \lt \lvert B\rvert`$. If $`\lvert B\rvert = 0`$, then
$`n \lvert B\rvert = 0`$ and hence $`j \lt \lvert G\rvert`$, contradicting the hypothesis of this case.

Since $`j - \lvert G\rvert \lt n \lvert B\rvert`$,
applying [T.index_decomp](Column-2.md#t-index_decomp) with $`L := \lvert B\rvert`$ yields
$`k, q`$ with $`k \lt n`$, $`q \lt \lvert B\rvert`$ and $`j - \lvert G\rvert = k \lvert B\rvert + q`$.
From $`\lvert G\rvert \le j`$ we get
$`j = \lvert G\rvert + (k \lvert B\rvert + q)`$.

By [T.copyExp_getD_copy](Column-2.md#t-copyExp_getD_copy),

```math
E\langle j\rangle = \bigl(\pi_1(B\langle q\rangle) + k d_0,\ \pi_2(B\langle q\rangle)\bigr)
```

and by the definition of $`M_{i,j}`$ (D.entry) we have
$`E_{0,j} = B_{0,q} + k d_0`$ and $`E_{1,j} = B_{1,q}`$.
The hypothesis $`E_{0,j} = 0`$ gives $`B_{0,q} + k d_0 = 0`$, hence $`B_{0,q} = 0`$.

Applying [T.hostM_getD_blk](Column-2.md#t-hostM_getD_blk) to $`q \lt \lvert B\rvert`$ gives
$`H\langle \lvert G\rvert + q\rangle = B\langle q\rangle`$.
Since $`\lvert G\rvert + q \lt \lvert G\rvert + \lvert B\rvert + 1 = \lvert H\rvert`$,
the definition of $`\mathrm{z0ok}(H)`$ (D.z0ok) can be applied at the index $`\lvert G\rvert + q`$. Its antecedent holds because
$`H_{0,\lvert G\rvert + q} = B_{0,q} = 0`$, so we obtain
$`B_{1,q} = H_{1,\lvert G\rvert + q} = 0`$, that is, $`E_{1,j} = 0`$. ∎
