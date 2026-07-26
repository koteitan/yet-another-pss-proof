[← README](README.md) | [English](Pss.md) | [Japanese](Pss-ja.md)

<a id="d-PairSeq"></a>
## Definition: pair sequence (D.PairSeq)

A finite sequence of pairs of natural numbers is called a **pair sequence**, and the collection of
all of them is written $`\mathrm{PairSeq}`$.

```math
\mathrm{PairSeq} := (\mathbb{N} \times \mathbb{N})^{\lt \omega}
```

For $`M \in \mathrm{PairSeq}`$ we write $`\lvert M\rvert`$ for its length and $`M_j`$ for its
$`j`$-th element (indices are counted from $`0`$). Thus $`M = (M_0, M_1, \dots, M_{\lvert M\rvert - 1})`$.

<a id="d-entry"></a>
## Definition: entry (D.entry)

For $`M \in \mathrm{PairSeq}`$ and $`i, j \in \mathbb{N}`$ put

```math
M_{i,j} := \begin{cases}
\pi_1\bigl(M\langle j\rangle\bigr) & (i = 0) \cr
\pi_2\bigl(M\langle j\rangle\bigr) & (i \ne 0)
\end{cases}
```

Here $`\pi_1, \pi_2`$ are the first and the second entry of a pair, and $`M\langle j\rangle`$ is

```math
M\langle j\rangle := \begin{cases}
M_j & (j \lt \lvert M\rvert) \cr
(0,0) & (j \ge \lvert M\rvert)
\end{cases}
```

That is, an index out of range reads $`(0,0)`$. In particular

```math
j \ge \lvert M\rvert \ \Longrightarrow\ M_{0,j} = M_{1,j} = 0 .
```

We call $`M_{0,j}`$ the **row $`0`$ value** of column $`j`$, and $`M_{1,j}`$ its **row $`1`$ value**.
For $`i \ne 0`$ the second entry is read regardless of the value of $`i`$, so below $`M_{i,j}`$ is
used only for $`i \in \{0,1\}`$.

<a id="d-nextrel0"></a>
## Definition: parent relation in row 0 (D.nextrel0)

For $`M \in \mathrm{PairSeq}`$ and $`j_0, j_1 \in \mathbb{N}`$, define $`j_0 \to^M_0 j_1`$ as the
conjunction of the following five conditions.

```math
\begin{aligned}
&(1)\ j_0 \lt \lvert M\rvert, \cr
&(2)\ j_1 \lt \lvert M\rvert, \cr
&(3)\ j_0 \lt j_1, \cr
&(4)\ M_{0,j_0} \lt M_{0,j_1}, \cr
&(5)\ \forall j\ \bigl(j_0 \lt j \wedge j \lt j_1 \to M_{0,j_1} \le M_{0,j}\bigr).
\end{aligned}
```

Condition (5) says that no row $`0`$ value smaller than $`M_{0,j_1}`$ occurs in the interval
$`(j_0, j_1)`$. When $`j_0 \to^M_0 j_1`$ holds, $`j_0`$ is called the
**parent in row $`0`$** of $`j_1`$.

<a id="d-le0"></a>
## Definition: ancestor relation in row 0 (D.le0)

Define $`j_0 \le^M_0 j_1`$ as the conjunction of the following three conditions.

```math
\begin{aligned}
&(1)\ j_0 \lt \lvert M\rvert, \cr
&(2)\ j_1 \lt \lvert M\rvert, \cr
&(3)\ j_0 \mathbin{(\to^M_0)^{*}} j_1 .
\end{aligned}
```

Here $`(\to^M_0)^{*}`$ is the reflexive transitive closure of $`\to^M_0`$, that is,

```math
j_0 \mathbin{(\to^M_0)^{*}} j_1 \iff
\exists k \ge 0,\ \exists k_0, \dots, k_k,\
k_0 = j_0 \wedge k_k = j_1 \wedge \forall m \lt k,\ k_m \to^M_0 k_{m+1}
```

(this includes the case $`k = 0`$, that is, the case $`j_0 = j_1`$).

<a id="d-nextrel1"></a>
## Definition: parent relation in row 1 (D.nextrel1)

Define $`j_0 \to^M_1 j_1`$ as the conjunction of the following six conditions.

```math
\begin{aligned}
&(1)\ j_0 \lt \lvert M\rvert, \cr
&(2)\ j_1 \lt \lvert M\rvert, \cr
&(3)\ j_0 \lt j_1, \cr
&(4)\ M_{1,j_0} \lt M_{1,j_1}, \cr
&(5)\ j_0 \le^M_0 j_1, \cr
&(6)\ \forall j\ \bigl(j_0 \lt j \wedge j \le^M_0 j_1 \to M_{1,j_1} \le M_{1,j}\bigr).
\end{aligned}
```

By condition (5), the parent relation in row $`1`$ refines the ancestor relation in row $`0`$.
The minimality expressed by condition (6) is imposed only along chains of ancestors in the sense of
condition (5).

<a id="d-nextR"></a>
## Definition: row-indexed parent relation (D.nextR)

For $`i \in \mathbb{N}`$ put

```math
j_0 \to^M_i j_1 :\iff \begin{cases}
j_0 \to^M_0 j_1 & (i = 0) \cr
j_0 \to^M_1 j_1 & (i \ne 0)
\end{cases}
```

<a id="d-Pred"></a>
## Definition: predecessor (D.Pred)

```math
\mathrm{Pred}\,M := \begin{cases}
M & (\lvert M\rvert \le 1) \cr
(M_0, \dots, M_{\lvert M\rvert - 2}) & (\lvert M\rvert \ge 2)
\end{cases}
```

This is the operation that drops the last column; on sequences of length at most $`1`$ it is the
identity.

<a id="d-idx1"></a>
## Definition: search row (D.idx1)

```math
\mathrm{idx}_1(M, j_1) := \begin{cases}
1 & (0 \lt M_{1,j_1}) \cr
0 & (M_{1,j_1} = 0)
\end{cases}
```

This gives the row in which the parent of column $`j_1`$ is to be searched for. Its value is either
$`0`$ or $`1`$.

<a id="d-hasParent"></a>
## Definition: existence of a parent (D.hasParent)

```math
\mathrm{hasParent}(M, i, j_1) :\iff \exists!\, j_0,\ j_0 \to^M_i j_1
```

That is, there exists a $`j_0`$ satisfying $`j_0 \to^M_i j_1`$, and it is unique.

<a id="d-parent"></a>
## Definition: parent (D.parent)

```math
\mathrm{par}^M_i(j_1) := \varepsilon j_0.\ \bigl(j_0 \to^M_i j_1\bigr)
```

Here $`\varepsilon`$ is Hilbert's choice operator. When $`\mathrm{hasParent}(M, i, j_1)`$ holds,
$`\mathrm{par}^M_i(j_1)`$ equals the unique $`j_0`$ satisfying $`j_0 \to^M_i j_1`$. Indeed, such a
$`j_0`$ exists, so $`\varepsilon`$ returns a value satisfying the condition, and by uniqueness that
value can only be $`j_0`$.

<a id="d-oper"></a>
## Definition: fundamental sequence (D.oper)

For $`M \in \mathrm{PairSeq}`$ and $`n \in \mathbb{N}`$, define $`M[n]`$ as follows. Put
$`j_1 := \lvert M\rvert - 1`$ (subtraction of natural numbers is truncated subtraction, so
$`j_1 = 0`$ when $`\lvert M\rvert = 0`$).

**(a) The case $`j_1 = 0`$**, that is, the case $`\lvert M\rvert \le 1`$:

```math
M[n] := M .
```

**(b) The case $`j_1 \ne 0`$ and $`M_{0,j_1} = 0 \wedge M_{1,j_1} = 0`$**, that is, the case where the last column is $`(0,0)`$:

```math
M[n] := \mathrm{Pred}\,M .
```

**(c) The case $`j_1 \ne 0`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$ and
$`\neg\,\mathrm{hasParent}(M, i_1, j_1)`$** (where $`i_1 := \mathrm{idx}_1(M, j_1)`$):

```math
M[n] := \mathrm{Pred}\,M .
```

**(d) Otherwise**, that is, the case $`j_1 \ne 0`$, $`\neg(M_{0,j_1} = 0 \wedge M_{1,j_1} = 0)`$,
$`\mathrm{hasParent}(M, i_1, j_1)`$. Put $`j_0 := \mathrm{par}^M_{i_1}(j_1)`$, define

```math
d_0 := \begin{cases} M_{0,j_1} - M_{0,j_0} & (0 \lt i_1) \cr 0 & (i_1 = 0) \end{cases}
\qquad
d_1 := \begin{cases} M_{1,j_1} - M_{1,j_0} & (1 \lt i_1) \cr 0 & (i_1 \le 1) \end{cases}
```

and set

```math
M[n] := (M_0, \dots, M_{j_0 - 1}) \mathbin{+\!\!+} B_0 \mathbin{+\!\!+} B_1 \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} B_{n-1},
```

```math
B_k := \bigl(\,(M_{0,j} + k\,d_0,\ M_{1,j} + k\,d_1)\,\bigr)_{j = j_0}^{j_1 - 1}
\qquad (k = 0, 1, \dots, n-1) .
```

Here $`B_k`$ is the sequence of length $`j_1 - j_0`$ running through the indices
$`j = j_0, j_0+1, \dots, j_1-1`$ in this order; it does **not** contain $`j_1`$ itself. For
$`n = 0`$ no $`B_k`$ occurs at all, so $`M[0] = (M_0, \dots, M_{j_0-1})`$.

<a id="d-diagSeq"></a>
## Definition: diagonal sequence (D.diagSeq)

For $`a, b \in \mathbb{N}`$ put

```math
\Delta_a^b := \bigl((a,a),\ (a+1,a+1),\ \dots,\ (b,b)\bigr)
```

Its length is $`b + 1 - a`$ (truncated subtraction), and it is the empty sequence when $`a \gt b`$.

<a id="d-ST_PS"></a>
## Definition: standard forms (D.ST_PS)

Define $`Y \subseteq \mathrm{PairSeq}`$ to be **closed** if both of the following hold.

```math
\begin{aligned}
&\text{(diag)}\quad \forall v \in \mathbb{N},\ \Delta_0^v \in Y, \cr
&\text{(oper)}\quad \forall M,\ \forall n \ge 1,\ M \in Y \to M[n] \in Y .
\end{aligned}
```

Then define $`\mathrm{ST\_PS} \subseteq \mathrm{PairSeq}`$ by

```math
\mathrm{ST\_PS} := \bigcap\, \bigl\{\, Y \subseteq \mathrm{PairSeq} \ \bigm|\ Y \text{ is closed} \,\bigr\} .
```

That is, $`M \in \mathrm{ST\_PS}`$ says that $`M \in Y`$ for every closed
$`Y \subseteq \mathrm{PairSeq}`$.

<a id="t-ST_PS.diag"></a>
## Theorem: a diagonal sequence is a standard form (T.ST_PS.diag)

### Theorem

For every $`v \in \mathbb{N}`$, $`\Delta_0^v \in \mathrm{ST\_PS}`$.

### Proof

Let $`Y`$ be an arbitrary closed set. By (diag), $`\Delta_0^v \in Y`$. Since $`Y`$ was arbitrary,
the definition of $`\mathrm{ST\_PS}`$ (D.ST_PS) gives $`\Delta_0^v \in \mathrm{ST\_PS}`$. ∎

<a id="t-ST_PS.oper"></a>
## Theorem: an expansion of a standard form is a standard form (T.ST_PS.oper)

### Theorem

If $`M \in \mathrm{ST\_PS}`$ and $`n \ge 1`$, then $`M[n] \in \mathrm{ST\_PS}`$.

### Proof

Let $`Y`$ be an arbitrary closed set. By the definition of $`\mathrm{ST\_PS}`$ (D.ST_PS), $`M`$
belongs to every closed set, in particular $`M \in Y`$. Applying (oper) to $`M`$ and $`n`$ gives
$`M[n] \in Y`$. Since $`Y`$ was arbitrary, $`M[n] \in \mathrm{ST\_PS}`$. ∎

<a id="t-ST_PS.rec"></a>
## Theorem: induction on the derivation of a standard form (T.ST_PS.rec)

### Theorem

If a predicate $`\Phi`$ on $`\mathrm{PairSeq}`$ satisfies

```math
\forall v,\ \Phi(\Delta_0^v)
\qquad\text{and}\qquad
\forall M,\ \forall n \ge 1,\ \bigl(M \in \mathrm{ST\_PS} \wedge \Phi(M)\bigr) \to \Phi(M[n])
```

then $`\forall M \in \mathrm{ST\_PS},\ \Phi(M)`$ holds.

### Proof

Put

```math
Y := \{\, M \in \mathrm{PairSeq} \mid M \in \mathrm{ST\_PS} \wedge \Phi(M) \,\}
```

and show that $`Y`$ is closed.

For (diag): by [T.ST_PS.diag](#t-ST_PS.diag) we have $`\Delta_0^v \in \mathrm{ST\_PS}`$, and by the
first hypothesis of this theorem $`\Phi(\Delta_0^v)`$. Hence $`\Delta_0^v \in Y`$.

For (oper): assume $`M \in Y`$ and $`n \ge 1`$. By the definition of $`Y`$ we have
$`M \in \mathrm{ST\_PS}`$ and $`\Phi(M)`$. From the former and [T.ST_PS.oper](#t-ST_PS.oper) we get
$`M[n] \in \mathrm{ST\_PS}`$, and giving the two to the second hypothesis of this theorem gives
$`\Phi(M[n])`$. Hence $`M[n] \in Y`$.

So $`Y`$ is closed, and the definition of $`\mathrm{ST\_PS}`$ (D.ST_PS) gives
$`\mathrm{ST\_PS} \subseteq Y`$. Taking $`M \in \mathrm{ST\_PS}`$ gives $`M \in Y`$, that is,
$`\Phi(M)`$. ∎

<a id="d-step"></a>
## Definition: expansion (D.step)

Define a relation $`S`$ on $`\mathrm{PairSeq}`$ to be **closed** if

```math
\text{(step\_oper)}\quad
\forall M,\ \forall n,\ \bigl(1 \lt \lvert M\rvert \wedge 1 \le n\bigr) \to M \mathbin{S} M[n]
```

holds. Then define $`\Rightarrow`$ to be the intersection of all closed relations, that is,
$`M \Rightarrow N`$ says that $`M \mathbin{S} N`$ for every closed $`S`$.

<a id="t-step.step_oper"></a>
## Theorem: the rule generating expansion (T.step.step_oper)

### Theorem

If $`1 \lt \lvert M\rvert`$ and $`1 \le n`$, then $`M \Rightarrow M[n]`$.

### Proof

Let $`S`$ be an arbitrary closed relation. Applying (step_oper) to $`M`$ and $`n`$ gives
$`M \mathbin{S} M[n]`$. Since $`S`$ was arbitrary, the definition of $`\Rightarrow`$ (D.step) gives
$`M \Rightarrow M[n]`$. ∎

<a id="t-step.iff"></a>
## Theorem: the shape of an expansion (T.step.iff)

### Theorem

$`M \Rightarrow N`$ holds if and only if $`1 \lt \lvert M\rvert`$ and there exists $`n \ge 1`$ with
$`N = M[n]`$.

### Proof

($`\Leftarrow`$) This is [T.step.step_oper](#t-step.step_oper).

($`\Rightarrow`$) Put

```math
S := \{\, (M,N) \mid 1 \lt \lvert M\rvert \wedge \exists n \ge 1,\ N = M[n] \,\} .
```

$`S`$ is closed: if $`1 \lt \lvert M\rvert`$ and $`1 \le n`$, then $`n`$ itself witnesses the
existential, so $`M \mathbin{S} M[n]`$. Hence, by the definition of $`\Rightarrow`$ (D.step),
$`M \Rightarrow N`$ gives $`M \mathbin{S} N`$, which is the claim. ∎
