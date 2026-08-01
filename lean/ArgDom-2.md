[← README](README.md) | [English](ArgDom-2.md) | [Japanese](ArgDom-2-ja.md) | ArgDom [1](ArgDom.md) **2** [3](ArgDom-3.md) [4](ArgDom-4.md) [5](ArgDom-5.md)

<a id="t-argdom_pos"></a>
## Theorem: positions of the two marked columns (T.argdom_pos)

### Theorem

If
$`N = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z`$,
then

```math
N\bigl\langle \lvert X\rvert \bigr\rangle = (u,w), \qquad
N\bigl\langle \lvert X\rvert + (\lvert A_1\rvert + 1) \bigr\rangle = (u+e,\ w), \qquad
\lvert X\rvert + (\lvert A_1\rvert + 1) \lt \lvert N\rvert .
```

($`N\langle j\rangle`$ [D.entry](Pss.md#d-entry))

### Proof

By associativity, $`N`$ can be written as

```math
N = X \mathbin{+\!\!+} \Bigl((u,w) :: \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: ((B \mathbin{+\!\!+} A_2) \mathbin{+\!\!+} Z)\bigr)\Bigr)
```

Set $`T := A_1 \mathbin{+\!\!+} (u+e,w) :: ((B \mathbin{+\!\!+} A_2) \mathbin{+\!\!+} Z)`$.

**First claim.** Applying [T.getD_append_right'](Cofinality.md#t-getD_append_right') to $`X`$ and $`(u,w) :: T`$ with index $`0`$ gives

```math
N\bigl\langle \lvert X\rvert + 0 \bigr\rangle = \bigl((u,w) :: T\bigr)\langle 0\rangle = (u,w) .
```

**Second claim.** Applying the same lemma to $`X`$ and $`(u,w) :: T`$ with index $`\lvert A_1\rvert + 1`$ gives

```math
N\bigl\langle \lvert X\rvert + (\lvert A_1\rvert + 1) \bigr\rangle
  = \bigl((u,w) :: T\bigr)\bigl\langle \lvert A_1\rvert + 1 \bigr\rangle
  = T\bigl\langle \lvert A_1\rvert \bigr\rangle
```

and applying the same lemma once more to $`A_1`$ and $`(u+e,w) :: ((B \mathbin{+\!\!+} A_2) \mathbin{+\!\!+} Z)`$ with
index $`0`$ yields $`T\langle \lvert A_1\rvert \rangle = (u+e,\ w)`$.

**Third claim.** The decomposition above gives

```math
\lvert N\rvert = \lvert X\rvert + 1 + \bigl(\lvert A_1\rvert + 1
  + (\lvert B\rvert + \lvert A_2\rvert + \lvert Z\rvert)\bigr)
```

which is at least $`\lvert X\rvert + \lvert A_1\rvert + 2`$, hence
$`\lvert X\rvert + (\lvert A_1\rvert + 1) \lt \lvert N\rvert`$. ∎

<a id="t-argDomCoreOn_diag"></a>
## Theorem: the core on the diagonal sequence (T.argDomCoreOn_diag)

### Theorem

For every $`v \in \mathbb{N}`$,
$`\mathrm{ArgDomCoreOn}(\Delta_0^v)`$ ($`\mathrm{ArgDomCoreOn}`$ [D.ArgDomCoreOn](ArgDom.md#d-ArgDomCoreOn), $`\Delta_0^v`$ [D.diagSeq](Pss.md#d-diagSeq)).

### Proof

Following D.ArgDomCoreOn, take $`X, A_1, B, A_2, Z`$ and $`u, w, e`$ and assume
conditions (1) through (8). Applying [T.argdom_pos](#t-argdom_pos) to condition (1) gives

```math
\Delta_0^v\bigl\langle \lvert X\rvert \bigr\rangle = (u,w), \qquad
\Delta_0^v\bigl\langle \lvert X\rvert + (\lvert A_1\rvert + 1) \bigr\rangle = (u+e,\ w), \qquad
\lvert X\rvert + (\lvert A_1\rvert + 1) \lt \bigl\lvert \Delta_0^v \bigr\rvert
```

By [T.diagSeq0_length](Column-2.md#t-diagSeq0_length),
$`\lvert \Delta_0^v\rvert = v + 1`$, hence

```math
\lvert X\rvert \le \lvert X\rvert + (\lvert A_1\rvert + 1) \lt v + 1
```

so [T.diagSeq0_getD](Column-2.md#t-diagSeq0_getD) applies with the indices $`\lvert X\rvert`$ and
$`\lvert X\rvert + (\lvert A_1\rvert + 1)`$, giving

```math
\Delta_0^v\bigl\langle \lvert X\rvert \bigr\rangle = \bigl(\lvert X\rvert,\ \lvert X\rvert\bigr),
\qquad
\Delta_0^v\bigl\langle \lvert X\rvert + (\lvert A_1\rvert + 1) \bigr\rangle
  = \bigl(\lvert X\rvert + (\lvert A_1\rvert + 1),\ \lvert X\rvert + (\lvert A_1\rvert + 1)\bigr)
```

Comparing the second entries of the first equation gives $`\lvert X\rvert = w`$, and
comparing the second entries of the second equation gives $`\lvert X\rvert + (\lvert A_1\rvert + 1) = w`$.
Together these give $`\lvert A_1\rvert + 1 = 0`$, which contradicts $`\lvert A_1\rvert + 1 \ge 1`$.

Hence no decomposition satisfies conditions (1) through (8), and conclusion (9) holds vacuously. ∎

<a id="t-argDomCoreOn_snoc_zero"></a>
## Theorem: removing a trailing column whose row 0 is 0 (T.argDomCoreOn_snoc_zero)

### Theorem

Let $`N \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) and $`p \in \mathbb{N}\times\mathbb{N}`$ with
$`p_1 = 0`$.
If $`\mathrm{ArgDomCoreOn}(N \mathbin{+\!\!+} (p))`$, then $`\mathrm{ArgDomCoreOn}(N)`$.

### Proof

Following D.ArgDomCoreOn, take $`X, A_1, B, A_2, Z`$ and $`u, w, e`$ and assume
conditions (1) through (8) for $`N`$.
Apply the hypothesis $`\mathrm{ArgDomCoreOn}(N \mathbin{+\!\!+} (p))`$ with the same
$`X, A_1, B, A_2, u, w, e`$ and with $`Z := Z \mathbin{+\!\!+} (p)`$.

- Condition (1): appending $`(p)`$ on the right of both sides of condition (1) for $`N`$ and
  regrouping by associativity gives

```math
N \mathbin{+\!\!+} (p)
  = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr)
    \mathbin{+\!\!+} \bigl(Z \mathbin{+\!\!+} (p)\bigr)
```

  as required.
- Conditions (2) through (6), and condition (8): identical to those for $`N`$.
- Condition (7): we must show $`Z \mathbin{+\!\!+} (p) = () \vee (\mathrm{head}(Z \mathbin{+\!\!+} (p)))_1 \le u`$.
  If $`Z = ()`$, then $`Z \mathbin{+\!\!+} (p) = (p)`$ and
  $`(\mathrm{head}(p))_1 = p_1 = 0 \le u`$, so the second disjunct holds.
  If $`Z = z :: Z'`$, then $`\mathrm{head}(Z \mathbin{+\!\!+} (p)) = \mathrm{head}\,Z`$, and since
  the first disjunct $`Z = ()`$ of condition (7) for $`N`$ is false, the second disjunct
  $`(\mathrm{head}\,Z)_1 \le u`$ holds, which is what is required.

Hence conclusion (9)

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

is obtained ($`\preceq_{\mathrm{lex}}`$ [D.sle](Cofinality.md#d-sle),
$`L^{+d}`$ [D.shiftr0](Cnf-2.md#d-shiftr0)). This is exactly conclusion (9) for $`N`$. ∎

<a id="t-argDomCoreOn_drop_left"></a>
## Theorem: the columns on the left are invisible (T.argDomCoreOn_drop_left)

### Theorem

Let $`P, S \in \mathrm{PairSeq}`$. If $`\mathrm{ArgDomCoreOn}(P \mathbin{+\!\!+} S)`$, then
$`\mathrm{ArgDomCoreOn}(S)`$.

### Proof

Following D.ArgDomCoreOn, take $`X, A_1, B, A_2, Z`$ and $`u, w, e`$ and assume
conditions (1) through (8) for $`S`$.
Apply the hypothesis $`\mathrm{ArgDomCoreOn}(P \mathbin{+\!\!+} S)`$ with $`X := P \mathbin{+\!\!+} X`$ and
the same $`A_1, B, A_2, Z, u, w, e`$.

Condition (1) is the identity obtained by prepending $`P`$ to both sides of condition (1)
for $`S`$ and regrouping by associativity:

```math
P \mathbin{+\!\!+} S
  = \bigl((P \mathbin{+\!\!+} X) \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z
```

Conditions (2) through (8) do not involve $`X`$, so they are identical to those for $`S`$.
Hence conclusion (9) is obtained, and since it too does not involve $`X`$, it is identical to conclusion (9) for $`S`$. ∎

<a id="d-shiftl0"></a>
## Definition: left shift of row 0 (D.shiftl0)

For $`d \in \mathbb{N}`$ and $`L \in \mathrm{PairSeq}`$, write $`L^{-d}`$ for the sequence obtained by
subtracting $`d`$ uniformly from the first entry of every pair of $`L`$. That is, for
$`L = (L_0, \dots, L_{\lvert L\rvert - 1})`$,

```math
L^{-d} := \Bigl(\,\bigl((L_0)_1 - d,\ (L_0)_2\bigr),\ \dots,\
  \bigl((L_{\lvert L\rvert - 1})_1 - d,\ (L_{\lvert L\rvert - 1})_2\bigr)\,\Bigr).
```

Here $`-`$ is truncated subtraction on the natural numbers.

<a id="t-shiftl0_cons"></a>
## Theorem: left shift and the head (T.shiftl0_cons)

### Theorem

For $`d \in \mathbb{N}`$, $`p \in \mathbb{N}\times\mathbb{N}`$ and $`A \in \mathrm{PairSeq}`$,

```math
(p :: A)^{-d} = (p_1 - d,\ p_2) :: A^{-d} .
```

### Proof

The definition of $`(\cdot)^{-d}`$ (D.shiftl0) is a map applied to each element, and
the image of the head is $`(p_1-d,\ p_2)`$ while the image of the rest is $`A^{-d}`$; hence
the two sides are the same sequence by definition. ∎

<a id="t-shiftl0_append"></a>
## Theorem: left shift and concatenation (T.shiftl0_append)

### Theorem

For $`d \in \mathbb{N}`$ and $`A, B \in \mathrm{PairSeq}`$,

```math
(A \mathbin{+\!\!+} B)^{-d} = A^{-d} \mathbin{+\!\!+} B^{-d} .
```

### Proof

A map applied to each element commutes with concatenation: the sequence of the images of the
elements of $`A \mathbin{+\!\!+} B`$ is the concatenation of the sequence of the images of the elements of
$`A`$ with the sequence of the images of the elements of $`B`$. ∎

<a id="t-mem_shiftl0"></a>
## Theorem: elements of a left shift (T.mem_shiftl0)

### Theorem

For $`d \in \mathbb{N}`$, $`M \in \mathrm{PairSeq}`$ and $`x \in \mathbb{N}\times\mathbb{N}`$,

```math
x \in M^{-d} \iff \exists p \in M,\ (p_1 - d,\ p_2) = x .
```

### Proof

By D.shiftl0, $`M^{-d}`$ is the sequence obtained from $`M`$ by replacing each element $`p`$ with
$`(p_1-d,\ p_2)`$, so being an element of it is equivalent to being the image of some element $`p`$ of $`M`$. ∎

<a id="t-shiftl0_shiftr0"></a>
## Theorem: the left shift is a left inverse of the right shift (T.shiftl0_shiftr0)

### Theorem

For $`d \in \mathbb{N}`$ and $`X \in \mathrm{PairSeq}`$,
$`(X^{+d})^{-d} = X`$.

### Proof

Induction on the length of $`X`$. Show

```math
\Lambda(X) :\equiv (X^{+d})^{-d} = X
```

for every $`X`$.

- **Base case** $`X = ()`$: since $`()^{+d} = ()`$ and $`()^{-d} = ()`$, both sides
  are $`()`$.

- **Inductive step** $`X = p :: X'`$: assume $`\Lambda(X')`$, that is,
  $`(X'^{+d})^{-d} = X'`$. By [T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons) and
  [T.shiftl0_cons](#t-shiftl0_cons),

```math
\bigl((p :: X')^{+d}\bigr)^{-d}
  = \bigl((p_1 + d,\ p_2) :: X'^{+d}\bigr)^{-d}
  = \bigl((p_1 + d) - d,\ p_2\bigr) :: (X'^{+d})^{-d}
```

  Since $`(p_1 + d) - d = p_1`$ and, by the induction hypothesis,
  $`(X'^{+d})^{-d} = X'`$, the right-hand side equals
  $`(p_1,\ p_2) :: X' = p :: X'`$. ∎

<a id="t-shiftr0_shiftl0"></a>
## Theorem: if row 0 is at least $`d`$, the right shift inverts the left shift (T.shiftr0_shiftl0)

### Theorem

Let $`d \in \mathbb{N}`$ and $`L \in \mathrm{PairSeq}`$ with $`\forall x \in L,\ d \le x_1`$.
Then $`(L^{-d})^{+d} = L`$.

### Proof

Induction on the length of $`L`$. Show

```math
\Upsilon(L) :\equiv
  \bigl(\forall x \in L,\ d \le x_1\bigr) \to (L^{-d})^{+d} = L
```

for every $`L`$.

- **Base case** $`L = ()`$: since $`()^{-d} = ()`$ and $`()^{+d} = ()`$, both sides
  are $`()`$.

- **Inductive step** $`L = p :: L'`$: assume $`\Upsilon(L')`$.
  From the assumption $`\forall x \in p :: L',\ d \le x_1`$, taking $`p`$ gives $`d \le p_1`$, and
  taking each element of $`L'`$ gives $`\forall x \in L',\ d \le x_1`$.
  Applying the induction hypothesis $`\Upsilon(L')`$ to the latter yields
  $`(L'^{-d})^{+d} = L'`$.
  By [T.shiftl0_cons](#t-shiftl0_cons) and [T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons),

```math
\bigl((p :: L')^{-d}\bigr)^{+d}
  = \bigl((p_1 - d,\ p_2) :: L'^{-d}\bigr)^{+d}
  = \bigl((p_1 - d) + d,\ p_2\bigr) :: (L'^{-d})^{+d}
```

  Since $`d \le p_1`$, truncated subtraction gives $`(p_1 - d) + d = p_1`$, and
  $`(L'^{-d})^{+d} = L'`$; hence the right-hand side equals
  $`(p_1,\ p_2) :: L' = p :: L'`$. ∎

<a id="t-shiftr0_comm"></a>
## Theorem: right shifts commute with each other (T.shiftr0_comm)

### Theorem

For $`d, e \in \mathbb{N}`$ and $`L \in \mathrm{PairSeq}`$,

```math
(L^{+d})^{+e} = (L^{+e})^{+d} .
```

### Proof

By the definition of $`(\cdot)^{+d}`$ (D.shiftr0), the left-hand side is the sequence obtained from
$`L`$ by replacing each element $`p`$ with $`\bigl((p_1 + d) + e,\ p_2\bigr)`$, and the right-hand side is
the sequence obtained by replacing each element $`p`$ with $`\bigl((p_1 + e) + d,\ p_2\bigr)`$.
By associativity and commutativity of addition on the natural numbers, $`(p_1 + d) + e = (p_1 + e) + d`$;
hence the two maps take the same value at every $`p`$, and therefore the two sequences are equal. ∎

<a id="t-argDomCoreOn_shiftr0"></a>
## Theorem: the core commutes with a uniform right shift (T.argDomCoreOn_shiftr0)

### Theorem

Let $`W \in \mathrm{PairSeq}`$ and $`d \in \mathbb{N}`$. If $`\mathrm{ArgDomCoreOn}(W)`$, then
$`\mathrm{ArgDomCoreOn}(W^{+d})`$.

### Proof

Following D.ArgDomCoreOn, take $`X, A_1, B, A_2, Z`$ and $`u, w, e`$ and assume
conditions (1) through (8) for $`W^{+d}`$; that is,

```math
W^{+d}
  = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z
```

together with $`0 \lt e`$, $`\forall x \in A_1,\ u \lt x_1`$, $`\forall x \in B,\ u+e \lt x_1`$,
$`\forall x \in A_2,\ u \lt x_1`$, $`A_2 = () \vee (\mathrm{head}\,A_2)_1 \le u+e`$,
$`Z = () \vee (\mathrm{head}\,Z)_1 \le u`$ and $`\mathrm{SpineOK}(A_1,\ u+e,\ w)`$ ([D.SpineOK](ArgDom.md#d-SpineOK)).

**Row 0 of every column is at least $`d`$.** Every element $`x`$ of the right-hand side of
condition (1) is an element of $`W^{+d}`$, so by [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) there is
an element $`q`$ of $`W`$ with $`x = (q_1 + d,\ q_2)`$, whence $`d \le x_1`$.
Since every element of $`X`$, $`A_1`$, $`B`$, $`A_2`$, $`Z`$, as well as the column $`(u,w)`$, is an element of the right-hand side,

```math
\forall x \in X,\ d \le x_1, \quad
\forall x \in A_1,\ d \le x_1, \quad
\forall x \in B,\ d \le x_1, \quad
\forall x \in A_2,\ d \le x_1, \quad
\forall x \in Z,\ d \le x_1, \quad
d \le u
```

all hold.

**Pulling the decomposition back before the shift.** Set

```math
X' := X^{-d}, \quad A_1' := A_1^{-d}, \quad B' := B^{-d}, \quad
A_2' := A_2^{-d}, \quad Z' := Z^{-d}
```

By the lower bounds on row 0 just established and [T.shiftr0_shiftl0](#t-shiftr0_shiftl0),

```math
X'^{+d} = X, \quad A_1'^{+d} = A_1, \quad B'^{+d} = B, \quad
A_2'^{+d} = A_2, \quad Z'^{+d} = Z
```

Applying $`(\cdot)^{-d}`$ to both sides of condition (1), the left-hand side is
$`W`$ by [T.shiftl0_shiftr0](#t-shiftl0_shiftr0), and the right-hand side becomes, by
[T.shiftl0_append](#t-shiftl0_append) and [T.shiftl0_cons](#t-shiftl0_cons),

```math
W = \bigl(X' \mathbin{+\!\!+} (u-d,\ w) :: (A_1' \mathbin{+\!\!+} (u+e-d,\ w) :: (B' \mathbin{+\!\!+} A_2'))\bigr) \mathbin{+\!\!+} Z'
```

Since $`d \le u`$, truncated subtraction gives $`u + e - d = (u-d) + e`$, so this can be written as

```math
W = \bigl(X' \mathbin{+\!\!+} (u-d,\ w) :: (A_1' \mathbin{+\!\!+} ((u-d)+e,\ w) :: (B' \mathbin{+\!\!+} A_2'))\bigr) \mathbin{+\!\!+} Z'
```

This is condition (1) for $`W`$.

**Pulling back the remaining conditions.** In what follows write $`u' := u - d`$; recall $`d \le u`$.

**(2)** $`0 \lt e`$ is the hypothesis itself.

**(3)** $`\forall x \in A_1',\ u' \lt x_1`$. Let $`x \in A_1'`$. By
[T.mem_shiftl0](#t-mem_shiftl0) there is an element $`q`$ of $`A_1`$ with
$`x = (q_1 - d,\ q_2)`$. From $`u \lt q_1`$, $`d \le q_1`$ and $`d \le u`$,
truncated subtraction gives $`u - d \lt q_1 - d`$, that is, $`u' \lt x_1`$.

**(4)** $`\forall x \in B',\ u' + e \lt x_1`$. Let $`x \in B'`$. By
[T.mem_shiftl0](#t-mem_shiftl0) there is an element $`q`$ of $`B`$ with
$`x = (q_1 - d,\ q_2)`$, and from $`u + e \lt q_1`$, $`d \le q_1`$ and $`d \le u`$ we get
$`u' + e = u + e - d \lt q_1 - d = x_1`$.

**(5)** $`\forall x \in A_2',\ u' \lt x_1`$. Let $`x \in A_2'`$. By
[T.mem_shiftl0](#t-mem_shiftl0) there is an element $`q`$ of $`A_2`$ with
$`x = (q_1 - d,\ q_2)`$, and from $`u \lt q_1`$, $`d \le q_1`$ and $`d \le u`$ we get
$`u' \lt x_1`$.

**(6)** $`A_2' = () \vee (\mathrm{head}\,A_2')_1 \le u' + e`$.
If $`A_2 = ()`$, then $`A_2' = ()^{-d} = ()`$ and the first disjunct holds.
If $`A_2 = a :: A_2''`$, then the first disjunct of condition (6) is false, so
$`(\mathrm{head}\,A_2)_1 = a_1 \le u + e`$; moreover $`d \le a_1`$.
By [T.shiftl0_cons](#t-shiftl0_cons), $`\mathrm{head}\,A_2' = (a_1 - d,\ a_2)`$, and
together with $`d \le u`$ this gives $`a_1 - d \le u + e - d = u' + e`$.

**(7)** $`Z' = () \vee (\mathrm{head}\,Z')_1 \le u'`$.
If $`Z = ()`$, then $`Z' = ()`$ and the first disjunct holds.
If $`Z = z :: Z''`$, then the first disjunct of condition (7) is false, so
$`(\mathrm{head}\,Z)_1 = z_1 \le u`$. By [T.shiftl0_cons](#t-shiftl0_cons),
$`\mathrm{head}\,Z' = (z_1 - d,\ z_2)`$, and $`z_1 - d \le u - d = u'`$.

**(8)** $`\mathrm{SpineOK}(A_1',\ u' + e,\ w)`$. Following D.SpineOK, take
$`U', V' \in \mathrm{PairSeq}`$ and $`x' \in \mathbb{N}\times\mathbb{N}`$, assume

```math
A_1' = U' \mathbin{+\!\!+} x' :: V', \qquad x'_1 \lt u' + e, \qquad \forall y \in V',\ x'_1 \lt y_1
```

and show $`w \le x'_2`$. Applying $`(\cdot)^{+d}`$ to both sides of this decomposition, the
left-hand side is $`A_1'^{+d} = A_1`$ and the right-hand side is, by [T.shiftr0_append](Cofinality-3.md#t-shiftr0_append) and [T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons),

```math
A_1 = U'^{+d} \mathbin{+\!\!+} (x'_1 + d,\ x'_2) :: V'^{+d}
```

Apply $`\mathrm{SpineOK}(A_1,\ u+e,\ w)`$ with
$`U := U'^{+d}`$, $`V := V'^{+d}`$ and $`x := (x'_1 + d,\ x'_2)`$.
Its three conditions are met as follows.

- The decomposition is the one obtained above.
- $`x'_1 + d \lt u + e`$: this follows from $`x'_1 \lt u' + e = u + e - d`$ and $`d \le u \le u + e`$.
- $`\forall y \in V'^{+d},\ x'_1 + d \lt y_1`$: by [T.mem_shiftr0](Cnf-2.md#t-mem_shiftr0) there is
  an element $`q`$ of $`V'`$ with $`y = (q_1 + d,\ q_2)`$, and
  $`x'_1 \lt q_1`$ by assumption, so $`x'_1 + d \lt q_1 + d = y_1`$.

Hence $`w \le \bigl((x'_1 + d,\ x'_2)\bigr)_2 = x'_2`$.

**Applying the core and pushing the conclusion forward.** Applying the hypothesis $`\mathrm{ArgDomCoreOn}(W)`$ with
$`X := X'`$, $`A_1 := A_1'`$, $`B := B'`$, $`A_2 := A_2'`$, $`Z := Z'`$,
$`u := u'`$ and the original $`w`$, $`e`$ yields conclusion (9)

```math
B' \preceq_{\mathrm{lex}} \bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+e}
```

Here, using [T.shiftr0_comm](#t-shiftr0_comm) together with
$`A_1'^{+d} = A_1`$, $`B'^{+d} = B`$, $`A_2'^{+d} = A_2`$
and $`(u'+e)+d = u+e`$ (which holds since $`d \le u`$),

```math
\begin{aligned}
&\Bigl(\bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+e}\Bigr)^{+d} \cr
&\qquad = \Bigl(\bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+d}\Bigr)^{+e} \cr
&\qquad = \bigl(A_1 \mathbin{+\!\!+} (u+e,\ w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
\end{aligned}
```

Therefore the conclusion (9) to be shown,

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,\ w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

is, after substituting $`B = B'^{+d}`$, the same assertion as

```math
B'^{+d} \preceq_{\mathrm{lex}}
  \Bigl(\bigl(A_1' \mathbin{+\!\!+} (u'+e,\ w) :: (B' \mathbin{+\!\!+} A_2')\bigr)^{+e}\Bigr)^{+d}
```

By the right-to-left direction of [T.sle_shiftr0](ArgDom.md#t-sle_shiftr0),
this follows from the conclusion (9) obtained above. ∎

<a id="t-split_prefix_left"></a>
## Theorem: splitting by a shorter left factor (T.split_prefix_left)

### Theorem

If $`C, D, E, F \in \mathrm{PairSeq}`$ satisfy

```math
C \mathbin{+\!\!+} D = E \mathbin{+\!\!+} F, \qquad \lvert E\rvert \le \lvert C\rvert
```

then

```math
C = E \mathbin{+\!\!+} \mathrm{drop}_{\lvert E\rvert} C
\qquad\text{and}\qquad
F = \mathrm{drop}_{\lvert E\rvert} C \mathbin{+\!\!+} D .
```

Here $`\mathrm{drop}_k L`$ is the sequence obtained from $`L`$ by dropping its first $`k`$ elements, and
$`\mathrm{take}_k L`$ is the sequence consisting of the first $`k`$ elements of $`L`$ (for $`k \ge \lvert L\rvert`$ these are $`()`$ and $`L`$ respectively).

### Proof

Set $`K := \mathrm{drop}_{\lvert E\rvert} C`$ and $`P := \mathrm{take}_{\lvert E\rvert} C`$.

**Step 1: rewrite the hypothesis so that $`P`$ is the left factor.**
For every sequence $`L`$ and every $`k`$ we have $`L = \mathrm{take}_k L \mathbin{+\!\!+} \mathrm{drop}_k L`$.
Taking $`L := C`$ and $`k := \lvert E\rvert`$ gives $`C = P \mathbin{+\!\!+} K`$. Hence the left-hand side of the hypothesis is
$`(P \mathbin{+\!\!+} K) \mathbin{+\!\!+} D`$, which by associativity of concatenation equals $`P \mathbin{+\!\!+} (K \mathbin{+\!\!+} D)`$. That is,

```math
P \mathbin{+\!\!+} (K \mathbin{+\!\!+} D) = E \mathbin{+\!\!+} F .
```

**Step 2: match the lengths of the left factors.**
We have $`\lvert \mathrm{take}_k L\rvert = \min(k, \lvert L\rvert)`$, and the hypothesis $`\lvert E\rvert \le \lvert C\rvert`$ gives
$`\lvert P\rvert = \min(\lvert E\rvert, \lvert C\rvert) = \lvert E\rvert`$.

**Step 3: uniqueness of the splitting of a concatenation.**
If two concatenations satisfy $`s_1 \mathbin{+\!\!+} t_1 = s_2 \mathbin{+\!\!+} t_2`$ and $`\lvert s_1\rvert = \lvert s_2\rvert`$, then
$`s_1 = s_2`$ and $`t_1 = t_2`$. Indeed, for each $`i`$ with $`i \lt \lvert s_1\rvert`$ the
$`i`$-th elements of the two sides are the $`i`$-th element of $`s_1`$ and the $`i`$-th element of $`s_2`$ respectively, so
$`s_1 = s_2`$ follows; removing this common left factor from the front of both sides then gives $`t_1 = t_2`$.

Applying this to the equation of Step 1, together with the equality of lengths from Step 2, gives

```math
P = E, \qquad K \mathbin{+\!\!+} D = F
```

Substituting the first equation into $`C = P \mathbin{+\!\!+} K`$ from Step 1 gives $`C = E \mathbin{+\!\!+} K`$, and
the second equation is the second half of the conclusion. ∎

<a id="t-split_prefix_right"></a>
## Theorem: splitting by a longer left factor (T.split_prefix_right)

### Theorem

If $`C, D, E, F \in \mathrm{PairSeq}`$ satisfy

```math
C \mathbin{+\!\!+} D = E \mathbin{+\!\!+} F, \qquad \lvert C\rvert \le \lvert E\rvert
```

then

```math
E = C \mathbin{+\!\!+} \mathrm{drop}_{\lvert C\rvert} E
\qquad\text{and}\qquad
D = \mathrm{drop}_{\lvert C\rvert} E \mathbin{+\!\!+} F .
```

### Proof

Swapping the two sides of the hypothesis gives $`E \mathbin{+\!\!+} F = C \mathbin{+\!\!+} D`$.
Apply [T.split_prefix_left](#t-split_prefix_left) to this equation, its four sequences being
instantiated as $`(E, F, C, D)`$ in this order. The length hypothesis required is $`\lvert C\rvert \le \lvert E\rvert`$,
which is the hypothesis of the present theorem. The conclusion obtained is

```math
E = C \mathbin{+\!\!+} \mathrm{drop}_{\lvert C\rvert} E, \qquad
D = \mathrm{drop}_{\lvert C\rvert} E \mathbin{+\!\!+} F
```

which is what is required. ∎

<a id="t-copies_headI"></a>
## Theorem: the head of a copy tower (T.copies_headI)

### Theorem

Let $`d \in \mathbb{N}`$, $`\mathrm{blk} \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$.
If $`\mathrm{blk} \ne ()`$ and $`1 \le n`$, then

```math
\mathrm{head}\bigl(\mathrm{copies}_d(\mathrm{blk}, n)\bigr) = \mathrm{head}\,\mathrm{blk} .
```

($`\mathrm{copies}_d`$ [D.copies](Cnf-2.md#d-copies))

### Proof

Since $`1 \le n`$, we may take $`m`$ with $`n = m + 1`$.
By [T.copies_succ_front](Cnf-3.md#t-copies_succ_front),

```math
\mathrm{copies}_d(\mathrm{blk}, m+1)
  = \mathrm{blk} \mathbin{+\!\!+} \bigl(\mathrm{copies}_d(\mathrm{blk}, m)\bigr)^{+d}
```

We distinguish cases on the constructor of $`\mathrm{blk}`$.

- Case $`\mathrm{blk} = ()`$. This contradicts the hypothesis $`\mathrm{blk} \ne ()`$.

- Case $`\mathrm{blk} = b :: \mathrm{blk}'`$. The right-hand side of the equation above is
  $`b :: \bigl(\mathrm{blk}' \mathbin{+\!\!+} (\mathrm{copies}_d(\mathrm{blk},m))^{+d}\bigr)`$, which is
  non-empty, so its head is $`b`$. On the other hand $`\mathrm{head}\,\mathrm{blk} = b`$. ∎

<a id="t-argbound_split"></a>
## Theorem: splitting the upper bound (T.argbound_split)

### Theorem

For $`e, u, w \in \mathbb{N}`$ and $`A_1, B, A_2 \in \mathrm{PairSeq}`$,

```math
\bigl(A_1 \mathbin{+\!\!+} (u+e,\,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
  = \bigl(A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}\bigr) \mathbin{+\!\!+} A_2^{+e} .
```

### Proof

Since $`L^{+d}`$ is the map replacing each element $`p`$ with $`(p_1 + d,\ p_2)`$, it preserves
concatenation by [T.shiftr0_append](Cofinality-3.md#t-shiftr0_append),
$`(L \mathbin{+\!\!+} L')^{+d} = L^{+d} \mathbin{+\!\!+} L'^{+d}`$, and by
[T.shiftr0_cons](Cnf-2.md#t-shiftr0_cons) we have
$`(p :: L)^{+d} = (p_1+d,\ p_2) :: L^{+d}`$. Using these in turn gives

```math
\begin{aligned}
\bigl(A_1 \mathbin{+\!\!+} (u+e,\,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
&= A_1^{+e} \mathbin{+\!\!+} \bigl((u+e,\,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e} \cr
&= A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: (B \mathbin{+\!\!+} A_2)^{+e} \cr
&= A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: \bigl(B^{+e} \mathbin{+\!\!+} A_2^{+e}\bigr)
\end{aligned}
```

(the second entry $`w`$ is unchanged by the map). Finally, for all $`P, Q, S \in \mathrm{PairSeq}`$ and
$`c \in \mathbb{N}\times\mathbb{N}`$,

```math
P \mathbin{+\!\!+} c :: (Q \mathbin{+\!\!+} S) = P \mathbin{+\!\!+} \bigl((c :: Q) \mathbin{+\!\!+} S\bigr)
  = \bigl(P \mathbin{+\!\!+} c :: Q\bigr) \mathbin{+\!\!+} S
```

follows from associativity of concatenation. It suffices to apply this with $`P := A_1^{+e}`$, $`c := (u+e+e,\,w)`$, $`Q := B^{+e}`$ and
$`S := A_2^{+e}`$. ∎

<a id="t-argbound_len"></a>
## Theorem: the length of the upper bound (T.argbound_len)

### Theorem

For $`e, u, w \in \mathbb{N}`$ and $`A_1, B \in \mathrm{PairSeq}`$,

```math
\lvert B\rvert \lt \bigl\lvert A_1^{+e} \mathbin{+\!\!+} (u+e+e,\,w) :: B^{+e}\bigr\rvert .
```

### Proof

Computing the length of a concatenation and of a cons, the right-hand side is $`\lvert A_1^{+e}\rvert + 1 + \lvert B^{+e}\rvert`$.
By [T.shiftr0_length](Cofinality-2.md#t-shiftr0_length) we have $`\lvert L^{+d}\rvert = \lvert L\rvert`$, so
this equals $`\lvert A_1\rvert + 1 + \lvert B\rvert`$.
In $`\mathbb{N}`$ we have $`\lvert B\rvert \lt \lvert A_1\rvert + 1 + \lvert B\rvert`$. ∎

<a id="t-argDomCoreOn_bad_A1"></a>
## Theorem: case A1 of the fourth branch of the expansion (T.argDomCoreOn_bad_A1)

### Theorem

Let $`M, G, R \in \mathrm{PairSeq}`$, $`v_0, w_0, d_0, n \in \mathbb{N}`$ and $`\ell \in \mathbb{N}\times\mathbb{N}`$, and
set $`\mathrm{blk} := (v_0,w_0) :: R`$. Assume the following.

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
&\text{(hn)}\quad 1 \le n .
\end{aligned}
```

($`\mathrm{ST\_PS}`$ [D.ST_PS](Pss.md#d-ST_PS), $`\to^M_1`$ [D.nextrel1](Pss.md#d-nextrel1))

Assume moreover the following for $`X, A_1, B, A_2, Z \in \mathrm{PairSeq}`$ and $`u, w, e \in \mathbb{N}`$.

```math
\begin{aligned}
&\text{(heq)}\quad   &&G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, n) \cr
& &&\qquad = \bigl(X \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z, \cr
&\text{(he)}\quad    &&0 \lt e, \cr
&\text{(h1)}\quad    &&\forall x \in A_1,\ u \lt x_1, \cr
&\text{(h2)}\quad    &&\forall x \in B,\ u + e \lt x_1, \cr
&\text{(h3)}\quad    &&\forall x \in A_2,\ u \lt x_1, \cr
&\text{(h4)}\quad    &&A_2 = () \ \vee\ (\mathrm{head}\,A_2)_1 \le u + e, \cr
&\text{(h5)}\quad    &&Z = () \ \vee\ (\mathrm{head}\,Z)_1 \le u, \cr
&\text{(h6)}\quad    &&\mathrm{SpineOK}(A_1,\ u+e,\ w), \cr
&\text{(hcase)}\quad &&\lvert G\rvert + (\lvert R\rvert + 1) \le \lvert X\rvert .
\end{aligned}
```

Then

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e} .
```

### Proof

By (hn) we may take $`m`$ with $`n = m + 1`$; below we write $`n`$ in this form.

**Step 1: peel off copy 0.**
By [T.copies_succ_front](Cnf-3.md#t-copies_succ_front) and associativity of concatenation,

```math
\begin{aligned}
&G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m+1) \cr
&\qquad = G \mathbin{+\!\!+} \Bigl(\mathrm{blk} \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}\Bigr) \cr
&\qquad = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}
\end{aligned}
```

Moreover, the right-hand side of (heq) can likewise be regrouped by associativity, so

```math
\begin{aligned}
&(G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} \bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0} \cr
&\qquad = X \mathbin{+\!\!+} \Bigl(\bigl((u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z\Bigr)
\end{aligned}
```

holds.

**Step 2: cut at the boundary.**
We have $`\lvert G \mathbin{+\!\!+} \mathrm{blk}\rvert = \lvert G\rvert + (\lvert R\rvert + 1)`$, and (hcase) says that
this is at most $`\lvert X\rvert`$. Hence
[T.split_prefix_right](#t-split_prefix_right) applies to the equation of Step 1, and
setting $`X' := \mathrm{drop}_{\lvert G\rvert + (\lvert R\rvert + 1)} X`$ we obtain

```math
X = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} X',
```
```math
\bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}
 = X' \mathbin{+\!\!+} \Bigl(\bigl((u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z\Bigr)
```

By associativity, the second equation can be written as

```math
(\ast)\qquad
\bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}
 = \bigl(X' \mathbin{+\!\!+} (u,w) :: (A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z
```

This is the shape of decomposition required by the definition of $`\mathrm{ArgDomCoreOn}`$ (D.ArgDomCoreOn), and
it is identical to (heq) except that $`X`$ has been replaced by $`X'`$. In particular $`A_1, B, A_2, Z, u, w, e`$ are
unchanged, so (he) and (h1)–(h6) can be used as they stand.

**Step 3: distinguish cases on $`m`$.**

**(a) The case $`m = 0`$.** By [T.copies_zero](Cnf-2.md#t-copies_zero),
$`\mathrm{copies}_{d_0}(\mathrm{blk}, 0) = ()`$, and by
[T.shiftr0_nil](Cnf-2.md#t-shiftr0_nil), $`()^{+d_0} = ()`$.
Hence the length of the left-hand side of $`(\ast)`$ is $`0`$. The length of its right-hand side, on the other hand, is

```math
\lvert X'\rvert + 1 + \lvert A_1\rvert + 1 + \lvert B\rvert + \lvert A_2\rvert + \lvert Z\rvert
```

which is at least $`2`$. Since $`(\ast)`$ says that its two sides are the same sequence, their lengths are equal too, giving
$`0 \ge 2`$. This is false in $`\mathbb{N}`$, so this case does not occur.

**(b) The case $`1 \le m`$.** Since $`m \lt m + 1 = n`$, applying (hIH) to $`m`$ yields

```math
\mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)
```

Applying [T.argDomCoreOn_drop_left](#t-argDomCoreOn_drop_left) with $`P := G`$ and
$`S := \mathrm{copies}_{d_0}(\mathrm{blk}, m)`$ gives
$`\mathrm{ArgDomCoreOn}(\mathrm{copies}_{d_0}(\mathrm{blk}, m))`$, and
applying [T.argDomCoreOn_shiftr0](#t-argDomCoreOn_shiftr0) with $`d := d_0`$ gives

```math
\mathrm{ArgDomCoreOn}\Bigl(\bigl(\mathrm{copies}_{d_0}(\mathrm{blk}, m)\bigr)^{+d_0}\Bigr)
```

Applying this to the decomposition $`(\ast)`$ of Step 2 and to (he), (h1), (h2), (h3), (h4), (h5), (h6)
yields, as the very conclusion of D.ArgDomCoreOn,

```math
B \preceq_{\mathrm{lex}} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) :: (B \mathbin{+\!\!+} A_2)\bigr)^{+e}
```

which is what is required. ∎

<a id="t-arg_split"></a>
## Theorem: splitting a sequence by a level (T.arg_split)

### Theorem

For $`L \in \mathbb{N}`$ and $`E \in \mathrm{PairSeq}`$ there exist $`B_p, R_p \in \mathrm{PairSeq}`$ such that

```math
E = B_p \mathbin{+\!\!+} R_p, \qquad
\forall x \in B_p,\ L \lt x_1, \qquad
R_p = () \ \vee\ (\mathrm{head}\,R_p)_1 \le L .
```

### Proof

Induction on the constructors of $`E`$ (with $`L`$ fixed). Show

```math
\Phi(E) :\equiv \exists B_p, R_p \in \mathrm{PairSeq},\
  \Bigl(E = B_p \mathbin{+\!\!+} R_p \wedge (\forall x \in B_p,\ L \lt x_1)
   \wedge \bigl(R_p = () \vee (\mathrm{head}\,R_p)_1 \le L\bigr)\Bigr)
```

for every $`E`$.

- **Base case** $`E = ()`$: take $`B_p := ()`$ and $`R_p := ()`$.
  Then $`() = () \mathbin{+\!\!+} ()`$. Since $`B_p = ()`$ has no elements, the second conjunct holds because its antecedent is false.
  In the third conjunct the first disjunct $`R_p = ()`$ holds.

- **Inductive step** $`E = a :: E'`$: assume $`\Phi(E')`$. We distinguish cases according to whether $`L \lt a_1`$.

  - Case $`L \lt a_1`$. Take $`B_p', R_p'`$ from $`\Phi(E')`$ and set
    $`B_p := a :: B_p'`$ and $`R_p := R_p'`$.
    Then $`a :: E' = a :: (B_p' \mathbin{+\!\!+} R_p') = (a :: B_p') \mathbin{+\!\!+} R_p'`$.
    If $`x \in a :: B_p'`$, then $`x = a`$ or $`x \in B_p'`$; in the former case $`L \lt x_1`$ by the hypothesis $`L \lt a_1`$ of this case,
    in the latter by the second conjunct of $`\Phi(E')`$.
    For the third conjunct we use that of $`\Phi(E')`$ unchanged.

  - Case $`\neg(L \lt a_1)`$. Set $`B_p := ()`$ and $`R_p := a :: E'`$.
    Then $`a :: E' = () \mathbin{+\!\!+} (a :: E')`$, and $`B_p = ()`$ has no elements.
    We have $`\mathrm{head}\,R_p = a`$, and $`\neg(L \lt a_1)`$ is equivalent in $`\mathbb{N}`$ to $`a_1 \le L`$,
    so the second disjunct of the third conjunct holds. ∎
