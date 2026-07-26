[← README](README.md) | [English](Column.md) | [Japanese](Column-ja.md) | Column **1** [2](Column-2.md) [3](Column-3.md) [4](Column-4.md)

<a id="t-stps_len_pos"></a>
## Theorem: standard forms are non-empty (T.stps_len_pos)

### Theorem

If $`M \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq)) satisfies $`M \in \mathrm{ST\_PS}`$ ([D.ST_PS](Pss.md#d-ST_PS)),
then $`0 \lt \lvert M\rvert`$.

### Proof

Induction on the derivation of $`\mathrm{ST\_PS}`$ ([T.ST_PS.rec](Pss.md#t-ST_PS.rec)). The induction predicate is

```math
\Phi(M) :\equiv 0 \lt \lvert M\rvert .
```

**Base case (rule diag), $`M = \Delta_0^v`$ ([D.diagSeq](Pss.md#d-diagSeq)).**
Applying [T.diagSeq_cons](Cnf.md#t-diagSeq_cons) with $`u := 0`$ and $`v := v`$
under the hypothesis $`0 \le v`$ yields
$`\Delta_0^v = (0,0) :: \Delta_1^v`$.
Hence $`\lvert \Delta_0^v\rvert = 1 + \lvert \Delta_1^v\rvert`$, so $`0 \lt \lvert \Delta_0^v\rvert`$.

**Inductive step (rule oper), $`M = N[n]`$ ([D.oper](Pss.md#d-oper), $`N \in \mathrm{ST\_PS}`$, $`1 \le n`$).**
Assume $`\Phi(N)`$, that is, $`0 \lt \lvert N\rvert`$.
Distinguish cases on $`\lvert N\rvert`$.

**(a) $`1 \lt \lvert N\rvert`$.**
By [T.oper_eq_dropLast_append](Cnf.md#t-oper_eq_dropLast_append) there is $`R \in \mathrm{PairSeq}`$ with
$`N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R`$. Here $`\mathrm{dropLast}\,N`$ is
$`N`$ with its last element removed, so $`\lvert \mathrm{dropLast}\,N\rvert = \lvert N\rvert - 1`$. Hence

```math
\lvert N[n]\rvert = (\lvert N\rvert - 1) + \lvert R\rvert \ge \lvert N\rvert - 1 \ge 1
```

and therefore $`0 \lt \lvert N[n]\rvert`$.

**(b) $`\neg(1 \lt \lvert N\rvert)`$.**
Then $`\lvert N\rvert \le 1`$, so [T.oper_eq_self_short](Decrease.md#t-oper_eq_self_short) gives
$`N[n] = N`$. Thus $`\Phi(N[n])`$ is exactly the induction hypothesis $`\Phi(N)`$. ∎

<a id="t-stps_head"></a>
## Theorem: a standard form begins with $`(0,0)`$ (T.stps_head)

### Theorem

If $`M \in \mathrm{ST\_PS}`$ then $`\mathrm{head}\,M = (0,0)`$.
Here $`\mathrm{head}\,M`$ is the first element of $`M`$, read as $`(0,0)`$ when $`M = ()`$.

### Proof

Induction on the derivation of $`\mathrm{ST\_PS}`$ ([T.ST_PS.rec](Pss.md#t-ST_PS.rec)). The induction predicate is

```math
\Phi(M) :\equiv \mathrm{head}\,M = (0,0) .
```

**Base case (rule diag), $`M = \Delta_0^v`$.**
Applying [T.diagSeq_cons](Cnf.md#t-diagSeq_cons) with $`u := 0`$, $`v := v`$ and the hypothesis $`0 \le v`$ yields
$`\Delta_0^v = (0,0) :: \Delta_1^v`$. Its first element is $`(0,0)`$.

**Inductive step (rule oper), $`M = N[n]`$ ($`N \in \mathrm{ST\_PS}`$, $`1 \le n`$).**
Assume $`\Phi(N)`$, that is, $`\mathrm{head}\,N = (0,0)`$.
Distinguish cases on $`\lvert N\rvert`$.

**(a) $`1 \lt \lvert N\rvert`$.**
By [T.oper_eq_dropLast_append](Cnf.md#t-oper_eq_dropLast_append) there is $`R`$ with
$`N[n] = \mathrm{dropLast}\,N \mathbin{+\!\!+} R`$.
Since $`1 \lt \lvert N\rvert`$, the sequence $`N`$ has at least two elements
and can be written $`N = a :: b :: u`$. In this case

```math
\mathrm{dropLast}\,(a :: b :: u) = a :: \mathrm{dropLast}\,(b :: u)
```

so that

```math
N[n] = a :: \bigl(\mathrm{dropLast}\,(b :: u) \mathbin{+\!\!+} R\bigr)
```

and hence $`\mathrm{head}\,(N[n]) = a = \mathrm{head}\,N`$.
By the induction hypothesis $`\mathrm{head}\,N = (0,0)`$.

**(b) $`\neg(1 \lt \lvert N\rvert)`$.**
Then $`\lvert N\rvert \le 1`$, so [T.oper_eq_self_short](Decrease.md#t-oper_eq_self_short) gives
$`N[n] = N`$, and $`\Phi(N[n])`$ is exactly the induction hypothesis. ∎

<a id="t-getD_app_right"></a>
## Theorem: reading the right summand of a concatenation (T.getD_app_right)

### Theorem

Let $`A, T \in \mathrm{PairSeq}`$ and $`i \in \mathbb{N}`$ with $`\lvert A\rvert \le i`$. Then

```math
(A \mathbin{+\!\!+} T)\langle i\rangle = T\langle i - \lvert A\rvert\rangle
```

(here $`M\langle j\rangle`$ [D.entry](Pss.md#d-entry) is the read that returns $`(0,0)`$ out of range).

### Proof

We have $`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$. Distinguish cases on the size of $`i`$.

**(a) $`i \lt \lvert A\rvert + \lvert T\rvert`$.**
Then $`i \lt \lvert A \mathbin{+\!\!+} T\rvert`$, so by the first case of the definition of $`M\langle j\rangle`$ (D.entry)
the left-hand side is $`(A \mathbin{+\!\!+} T)_i`$. Since $`\lvert A\rvert \le i`$, the $`i`$-th element of the
concatenation is $`T_{i - \lvert A\rvert}`$. On the other hand $`i - \lvert A\rvert \lt \lvert T\rvert`$, so
by the first case of D.entry again the right-hand side is $`T_{i - \lvert A\rvert}`$ as well.

**(b) $`\lvert A\rvert + \lvert T\rvert \le i`$.**
Then $`\lvert A \mathbin{+\!\!+} T\rvert \le i`$, so by the second case of D.entry the left-hand side is $`(0,0)`$.
Moreover $`\lvert A\rvert \le i`$ together with $`\lvert A\rvert + \lvert T\rvert \le i`$ gives $`\lvert T\rvert \le i - \lvert A\rvert`$,
so the right-hand side is $`(0,0)`$ as well. ∎

<a id="t-entry_append_right"></a>
## Theorem: entries are prefix-invariant (T.entry_append_right)

### Theorem

For $`A, T \in \mathrm{PairSeq}`$ and $`i, j \in \mathbb{N}`$,

```math
(A \mathbin{+\!\!+} T)_{i,\,\lvert A\rvert + j} = T_{i,j}
```

### Proof

Since $`\lvert A\rvert \le \lvert A\rvert + j`$, applying [T.getD_app_right](#t-getD_app_right) with
$`i := \lvert A\rvert + j`$ yields

```math
(A \mathbin{+\!\!+} T)\langle \lvert A\rvert + j\rangle
 = T\langle (\lvert A\rvert + j) - \lvert A\rvert\rangle = T\langle j\rangle
```

By the definition of $`M_{i,j}`$ (D.entry), for $`i = 0`$ the two sides are
$`\pi_1\bigl((A \mathbin{+\!\!+} T)\langle \lvert A\rvert + j\rangle\bigr)`$ and $`\pi_1\bigl(T\langle j\rangle\bigr)`$ respectively,
and for $`i \ne 0`$ they are the corresponding $`\pi_2`$. In either case they are the same entry of the same pair, hence equal. ∎

<a id="t-nextrel0_append_right"></a>
## Theorem: the row-0 parent relation is prefix-invariant (T.nextrel0_append_right)

### Theorem

For $`A, T \in \mathrm{PairSeq}`$ and $`j_0, j_1 \in \mathbb{N}`$,

```math
\lvert A\rvert + j_0 \to^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1
\iff
j_0 \to^{T}_0 j_1
```

($`\to^M_0`$ [D.nextrel0](Pss.md#d-nextrel0)).

### Proof

Note that $`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$, and match up
the five conditions of the definition of $`\to^M_0`$ (D.nextrel0) on the two sides.

**($`\Rightarrow`$)** Write (1)–(5) for the five conditions on the left-hand side.

- (1) From $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$ we get $`j_0 \lt \lvert T\rvert`$.
- (2) From $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$ we get $`j_1 \lt \lvert T\rvert`$.
- (3) From $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j_1`$ we get $`j_0 \lt j_1`$.
- (4) By [T.entry_append_right](#t-entry_append_right) we have
  $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_0} = T_{0,j_0}`$ and
  $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} = T_{0,j_1}`$, so
  (4) reads $`T_{0,j_0} \lt T_{0,j_1}`$.
- (5) Let $`j`$ be a natural number with $`j_0 \lt j`$ and $`j \lt j_1`$.
  Then $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j \lt \lvert A\rvert + j_1`$, so
  (5) applies to $`\lvert A\rvert + j`$ and gives
  $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} \le (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j}`$.
  Rewriting both sides by [T.entry_append_right](#t-entry_append_right) gives $`T_{0,j_1} \le T_{0,j}`$.

**($`\Leftarrow`$)** Write (1')–(5') for the five conditions on the right-hand side.

- (1) Adding $`\lvert A\rvert`$ to (1') $`j_0 \lt \lvert T\rvert`$ gives
  $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$.
- (2) Adding $`\lvert A\rvert`$ to (2') $`j_1 \lt \lvert T\rvert`$ gives
  $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$.
- (3) From (3') $`j_0 \lt j_1`$ we get $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j_1`$.
- (4) Rewriting by [T.entry_append_right](#t-entry_append_right) gives exactly (4').
- (5) Let $`j`$ be a natural number with $`\lvert A\rvert + j_0 \lt j`$ and $`j \lt \lvert A\rvert + j_1`$.
  Since $`\lvert A\rvert \le \lvert A\rvert + j_0 \lt j`$, setting $`j' := j - \lvert A\rvert`$ gives
  $`j = \lvert A\rvert + j'`$ and $`j_0 \lt j' \lt j_1`$.
  Applying (5') to $`j'`$ gives $`T_{0,j_1} \le T_{0,j'}`$, and
  rewriting by [T.entry_append_right](#t-entry_append_right) gives
  $`(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1} \le (A \mathbin{+\!\!+} T)_{0,j}`$. ∎

<a id="t-rtg_nextrel0_lift"></a>
## Theorem: lifting a row-0 chain (T.rtg_nextrel0_lift)

### Theorem

Let $`A, T \in \mathrm{PairSeq}`$ and $`j_0, c \in \mathbb{N}`$.
If $`j_0 \mathbin{(\to^{T}_0)^{*}} c`$ ([D.le0](Pss.md#d-le0)), then

```math
\lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + c .
```

### Proof

Induction on the construction of the chain $`j_0 \mathbin{(\to^{T}_0)^{*}} c`$. Fix $`A`$, $`T`$ and $`j_0`$;
the induction predicate is

```math
\Phi(c) :\equiv \lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + c .
```

**Base case (chain of length $`0`$, $`c = j_0`$).**
The chain of length $`0`$ from $`\lvert A\rvert + j_0`$ to $`\lvert A\rvert + j_0`$ gives $`\Phi(j_0)`$.

**Inductive step (chain of length $`k+1`$).**
The chain splits into a chain $`j_0 \mathbin{(\to^{T}_0)^{*}} b`$ of length $`k`$ and a final step $`b \to^{T}_0 c`$.
Assume $`\Phi(b)`$, that is,
$`\lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + b`$.
Applying the ($`\Leftarrow`$) direction of [T.nextrel0_append_right](#t-nextrel0_append_right) to
$`b \to^{T}_0 c`$ gives
$`\lvert A\rvert + b \to^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + c`$.
Appending this to the end of the chain of the induction hypothesis yields $`\Phi(c)`$. ∎

<a id="t-le0_append_right_of"></a>
## Theorem: lifting the row-0 ancestor relation (T.le0_append_right_of)

### Theorem

Let $`A, T \in \mathrm{PairSeq}`$ and $`j_0, j_1 \in \mathbb{N}`$.
If $`j_0 \le^{T}_0 j_1`$ then
$`\lvert A\rvert + j_0 \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$.

### Proof

We verify the three conditions of the definition of $`\le^M_0`$ (D.le0).
Write (1')(2')(3') for the three conditions of the hypothesis.

- (1) $`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$, and (1') $`j_0 \lt \lvert T\rvert`$ gives
  $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$.
- (2) $`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$, and (2') $`j_1 \lt \lvert T\rvert`$ gives
  $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$.
- (3) (3') is $`j_0 \mathbin{(\to^{T}_0)^{*}} j_1`$, and
  applying [T.rtg_nextrel0_lift](#t-rtg_nextrel0_lift) gives
  $`\lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + j_1`$. ∎

<a id="t-nextrel0_lt"></a>
## Theorem: a row-0 parent edge increases the index (T.nextrel0_lt)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and $`a, b \in \mathbb{N}`$. If $`a \to^{M}_0 b`$ then $`a \lt b`$.

### Proof

The third condition of the definition of $`\to^M_0`$ (D.nextrel0) is exactly $`a \lt b`$. ∎

<a id="t-rtg_nextrel0_unlift"></a>
## Theorem: pulling back a row-0 chain (T.rtg_nextrel0_unlift)

### Theorem

Let $`A, T \in \mathrm{PairSeq}`$ and $`a, c \in \mathbb{N}`$.
If $`\lvert A\rvert + a \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} c`$, then there is $`c'`$ with

```math
c = \lvert A\rvert + c' \qquad\text{and}\qquad a \mathbin{(\to^{T}_0)^{*}} c' .
```

### Proof

Induction on the construction of the chain $`\lvert A\rvert + a \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} c`$.
Fix $`A`$, $`T`$ and $`a`$; the induction predicate is

```math
\Phi(c) :\equiv \exists c',\ c = \lvert A\rvert + c' \wedge a \mathbin{(\to^{T}_0)^{*}} c' .
```

**Base case (chain of length $`0`$, $`c = \lvert A\rvert + a`$).**
Take $`c' := a`$; then $`c = \lvert A\rvert + a`$, and there is a chain of length $`0`$ from $`a`$ to $`a`$.

**Inductive step (chain of length $`k+1`$).**
The chain splits into a chain $`\lvert A\rvert + a \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} d`$ of length $`k`$ and
a final step $`d \to^{A \mathbin{+\!\!+} T}_0 e`$ (with $`c = e`$).
Assume $`\Phi(d)`$; take $`d'`$ with $`d = \lvert A\rvert + d'`$ and
$`a \mathbin{(\to^{T}_0)^{*}} d'`$.
Applying [T.nextrel0_lt](#t-nextrel0_lt) to the final step gives $`d \lt e`$, that is,
$`\lvert A\rvert + d' \lt e`$. In particular $`\lvert A\rvert \le e`$, so setting
$`e' := e - \lvert A\rvert`$ gives $`e = \lvert A\rvert + e'`$.
Applying the ($`\Rightarrow`$) direction of [T.nextrel0_append_right](#t-nextrel0_append_right) to
$`\lvert A\rvert + d' \to^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + e'`$ gives
$`d' \to^{T}_0 e'`$. Appending this to the end of the chain of the induction hypothesis gives
$`a \mathbin{(\to^{T}_0)^{*}} e'`$. Thus $`c' := e'`$ gives $`\Phi(e)`$. ∎

<a id="t-le0_append_right"></a>
## Theorem: the row-0 ancestor relation is prefix-invariant (T.le0_append_right)

### Theorem

For $`A, T \in \mathrm{PairSeq}`$ and $`j_0, j_1 \in \mathbb{N}`$,

```math
\lvert A\rvert + j_0 \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1
\iff
j_0 \le^{T}_0 j_1 .
```

### Proof

**($`\Rightarrow`$)** Write (1)(2)(3) for the three conditions on the left-hand side.
Since $`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$,
(1) gives $`j_0 \lt \lvert T\rvert`$ and (2) gives $`j_1 \lt \lvert T\rvert`$.
Condition (3) is $`\lvert A\rvert + j_0 \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + j_1`$, so
by [T.rtg_nextrel0_unlift](#t-rtg_nextrel0_unlift) there is $`c'`$ with
$`\lvert A\rvert + j_1 = \lvert A\rvert + c'`$ and $`j_0 \mathbin{(\to^{T}_0)^{*}} c'`$.
The first equation gives $`j_1 = c'`$, hence $`j_0 \mathbin{(\to^{T}_0)^{*}} j_1`$.
This completes the three conditions of the definition of $`\le^M_0`$ (D.le0).

**($`\Leftarrow`$)** This is exactly [T.le0_append_right_of](#t-le0_append_right_of). ∎

<a id="t-nextrel0_no_cross"></a>
## Theorem: a row-0 parent edge does not cross the boundary (T.nextrel0_no_cross)

### Theorem

Let $`A, T \in \mathrm{PairSeq}`$ satisfy $`T_{0,0} = 0`$.
If $`k, j \in \mathbb{N}`$ satisfy

```math
k \lt \lvert A\rvert, \qquad
\lvert A\rvert \le j, \qquad
0 \lt (A \mathbin{+\!\!+} T)_{0,j}, \qquad
k \to^{A \mathbin{+\!\!+} T}_0 j
```

then a contradiction follows.

### Proof

First we show $`\lvert A\rvert \lt j`$. By the hypothesis $`\lvert A\rvert \le j`$, either $`j = \lvert A\rvert`$ or
$`\lvert A\rvert \lt j`$. Suppose $`j = \lvert A\rvert`$. Applying
[T.entry_append_right](#t-entry_append_right) with $`i := 0`$ and $`j := 0`$ gives

```math
(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert} = T_{0,0} = 0
```

which contradicts the hypothesis $`0 \lt (A \mathbin{+\!\!+} T)_{0,j}`$. Hence $`\lvert A\rvert \lt j`$.

Next apply condition (5) (D.nextrel0) of $`k \to^{A \mathbin{+\!\!+} T}_0 j`$ to $`\lvert A\rvert`$.
Since $`k \lt \lvert A\rvert`$ and $`\lvert A\rvert \lt j`$, the condition is met and we obtain

```math
(A \mathbin{+\!\!+} T)_{0,j} \le (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert} = 0
```

which contradicts the hypothesis $`0 \lt (A \mathbin{+\!\!+} T)_{0,j}`$. ∎

<a id="t-nextrel0_no_pred_zero"></a>
## Theorem: a column with row-0 value $`0`$ has no row-0 parent (T.nextrel0_no_pred_zero)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and $`a, b \in \mathbb{N}`$.
If $`M_{0,b} = 0`$ and $`a \to^{M}_0 b`$, then a contradiction follows.

### Proof

The fourth condition of the definition of $`\to^M_0`$ (D.nextrel0) is $`M_{0,a} \lt M_{0,b}`$.
Substituting $`M_{0,b} = 0`$ gives $`M_{0,a} \lt 0`$, but no natural number is smaller than $`0`$. ∎

<a id="t-rtg_to_root"></a>
## Theorem: a chain ending at a column with row-0 value $`0`$ is trivial (T.rtg_to_root)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and $`k, b \in \mathbb{N}`$.
If $`M_{0,b} = 0`$ and $`k \mathbin{(\to^{M}_0)^{*}} b`$ then $`k = b`$.

### Proof

Distinguish cases on the length of the chain.

- **Length $`0`$.** The two ends of the chain coincide, so $`k = b`$.
- **Length at least $`1`$.** The chain splits into $`k \mathbin{(\to^{M}_0)^{*}} c`$ and a final step
  $`c \to^{M}_0 b`$. Since $`M_{0,b} = 0`$,
  [T.nextrel0_no_pred_zero](#t-nextrel0_no_pred_zero) yields a contradiction.
  Hence this case does not occur. ∎

<a id="t-le0_no_cross"></a>
## Theorem: the row-0 ancestor relation does not cross the boundary (T.le0_no_cross)

### Theorem

Let $`A, T \in \mathrm{PairSeq}`$ satisfy $`T_{0,0} = 0`$.
If $`k, j_1 \in \mathbb{N}`$ satisfy

```math
k \lt \lvert A\rvert, \qquad
0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}, \qquad
k \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1
```

then a contradiction follows.

### Proof

It suffices to prove the following statement (H).

```math
(H)\quad \forall e,\ \Bigl(k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} e
 \wedge \lvert A\rvert \le e \wedge 0 \lt (A \mathbin{+\!\!+} T)_{0,e}\Bigr)
 \to \lvert A\rvert \le k .
```

Indeed, the third condition (D.le0) of the hypothesis $`k \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$ is
$`k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} \lvert A\rvert + j_1`$, and both
$`\lvert A\rvert \le \lvert A\rvert + j_1`$ and
$`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ hold, so applying (H) with
$`e := \lvert A\rvert + j_1`$ gives $`\lvert A\rvert \le k`$.
This contradicts the hypothesis $`k \lt \lvert A\rvert`$.

We prove (H) by induction on the construction of the chain $`k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} e`$.
Fix $`A`$, $`T`$ and $`k`$; the induction predicate is

```math
\Phi(e) :\equiv \bigl(\lvert A\rvert \le e \wedge 0 \lt (A \mathbin{+\!\!+} T)_{0,e}\bigr)
 \to \lvert A\rvert \le k .
```

**Base case (chain of length $`0`$, $`e = k`$).**
The first conjunct of the antecedent is exactly $`\lvert A\rvert \le k`$, which is the conclusion.

**Inductive step (chain of length $`m+1`$).**
The chain splits into a chain $`k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} c`$ of length $`m`$ and
a final step $`c \to^{A \mathbin{+\!\!+} T}_0 d`$ (with $`e = d`$).
Assume $`\Phi(c)`$.
Assume the antecedent $`\lvert A\rvert \le d`$ and $`0 \lt (A \mathbin{+\!\!+} T)_{0,d}`$.

First we show $`\lvert A\rvert \le c`$. Suppose $`c \lt \lvert A\rvert`$. Then
[T.nextrel0_no_cross](#t-nextrel0_no_cross) applies with $`k := c`$ and $`j := d`$
(its four hypotheses are $`c \lt \lvert A\rvert`$, $`\lvert A\rvert \le d`$,
$`0 \lt (A \mathbin{+\!\!+} T)_{0,d}`$ and $`c \to^{A \mathbin{+\!\!+} T}_0 d`$), a contradiction.

Next distinguish cases on $`(A \mathbin{+\!\!+} T)_{0,c}`$.

- $`0 \lt (A \mathbin{+\!\!+} T)_{0,c}`$.
  Feeding $`\lvert A\rvert \le c`$ and this inequality to the induction hypothesis $`\Phi(c)`$ gives
  $`\lvert A\rvert \le k`$.
- $`(A \mathbin{+\!\!+} T)_{0,c} = 0`$.
  Applying [T.rtg_to_root](#t-rtg_to_root) with $`M := A \mathbin{+\!\!+} T`$ and $`b := c`$
  to the chain $`k \mathbin{(\to^{A \mathbin{+\!\!+} T}_0)^{*}} c`$ gives $`k = c`$.
  Together with $`\lvert A\rvert \le c`$ shown above, $`\lvert A\rvert \le k`$. ∎

<a id="t-nextrel1_append_right"></a>
## Theorem: the row-1 parent relation is prefix-invariant (T.nextrel1_append_right)

### Theorem

For $`A, T \in \mathrm{PairSeq}`$ and $`j_0, j_1 \in \mathbb{N}`$,

```math
\lvert A\rvert + j_0 \to^{A \mathbin{+\!\!+} T}_1 \lvert A\rvert + j_1
\iff
j_0 \to^{T}_1 j_1
```

($`\to^M_1`$ [D.nextrel1](Pss.md#d-nextrel1)).

### Proof

Note that $`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert`$, and match up
the six conditions of the definition of $`\to^M_1`$ (D.nextrel1) on the two sides.

**($`\Rightarrow`$)** Write (1)–(6) for the six conditions on the left-hand side.

- (1) From $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$ we get $`j_0 \lt \lvert T\rvert`$.
- (2) From $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$ we get $`j_1 \lt \lvert T\rvert`$.
- (3) From $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j_1`$ we get $`j_0 \lt j_1`$.
- (4) By [T.entry_append_right](#t-entry_append_right) we have
  $`(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_0} = T_{1,j_0}`$ and
  $`(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} = T_{1,j_1}`$, so
  (4) reads $`T_{1,j_0} \lt T_{1,j_1}`$.
- (5) Applying the ($`\Rightarrow`$) direction of [T.le0_append_right](#t-le0_append_right) to (5) gives
  $`j_0 \le^{T}_0 j_1`$.
- (6) Let $`j`$ be a natural number with $`j_0 \lt j`$ and $`j \le^{T}_0 j_1`$.
  Then $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j`$, and by the ($`\Leftarrow`$) direction of
  [T.le0_append_right](#t-le0_append_right) we have
  $`\lvert A\rvert + j \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$.
  Hence (6) applies to $`\lvert A\rvert + j`$ and gives
  $`(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} \le (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j}`$,
  that is, rewriting by [T.entry_append_right](#t-entry_append_right),
  $`T_{1,j_1} \le T_{1,j}`$.

**($`\Leftarrow`$)** Write (1')–(6') for the six conditions on the right-hand side.

- (1) From (1') $`j_0 \lt \lvert T\rvert`$ we get $`\lvert A\rvert + j_0 \lt \lvert A\rvert + \lvert T\rvert`$.
- (2) Adding $`\lvert A\rvert`$ to (2') $`j_1 \lt \lvert T\rvert`$ gives
  $`\lvert A\rvert + j_1 \lt \lvert A\rvert + \lvert T\rvert`$.
- (3) From (3') $`j_0 \lt j_1`$ we get $`\lvert A\rvert + j_0 \lt \lvert A\rvert + j_1`$.
- (4) Rewriting by [T.entry_append_right](#t-entry_append_right) gives exactly (4').
- (5) Apply the ($`\Leftarrow`$) direction of [T.le0_append_right](#t-le0_append_right) to (5').
- (6) Let $`j`$ be a natural number with $`\lvert A\rvert + j_0 \lt j`$ and
  $`j \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$.
  Since $`\lvert A\rvert \le \lvert A\rvert + j_0 \lt j`$, setting $`j' := j - \lvert A\rvert`$ gives
  $`j = \lvert A\rvert + j'`$ and $`j_0 \lt j'`$.
  By the ($`\Rightarrow`$) direction of [T.le0_append_right](#t-le0_append_right) we have $`j' \le^{T}_0 j_1`$, so
  applying (6') to $`j'`$ gives $`T_{1,j_1} \le T_{1,j'}`$.
  Rewriting by [T.entry_append_right](#t-entry_append_right) gives
  $`(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j_1} \le (A \mathbin{+\!\!+} T)_{1,j}`$. ∎

<a id="t-nextR_append_right"></a>
## Theorem: the row-indexed parent relation is prefix-invariant (T.nextR_append_right)

### Theorem

For $`A, T \in \mathrm{PairSeq}`$ and $`i, j_0, j_1 \in \mathbb{N}`$,

```math
\lvert A\rvert + j_0 \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1
\iff
j_0 \to^{T}_i j_1
```

($`\to^M_i`$ [D.nextR](Pss.md#d-nextR)).

### Proof

By the case distinction in the definition of $`\to^M_i`$ (D.nextR).

- $`i = 0`$. The two sides are
  $`\lvert A\rvert + j_0 \to^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$ and $`j_0 \to^{T}_0 j_1`$ respectively,
  and [T.nextrel0_append_right](#t-nextrel0_append_right) is exactly the claim.
- $`i \ne 0`$. The two sides are
  $`\lvert A\rvert + j_0 \to^{A \mathbin{+\!\!+} T}_1 \lvert A\rvert + j_1`$ and $`j_0 \to^{T}_1 j_1`$ respectively,
  and [T.nextrel1_append_right](#t-nextrel1_append_right) is exactly the claim. ∎

<a id="t-idx1_append_right"></a>
## Theorem: the search row is prefix-invariant (T.idx1_append_right)

### Theorem

For $`A, T \in \mathrm{PairSeq}`$ and $`j \in \mathbb{N}`$,

```math
\mathrm{idx}_1(A \mathbin{+\!\!+} T,\ \lvert A\rvert + j) = \mathrm{idx}_1(T, j)
```

($`\mathrm{idx}_1`$ [D.idx1](Pss.md#d-idx1)).

### Proof

The definition of $`\mathrm{idx}_1`$ (D.idx1) is a case distinction that depends only on the sign of $`M_{1,j_1}`$.
By [T.entry_append_right](#t-entry_append_right) we have
$`(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j} = T_{1,j}`$, so
the conditions $`0 \lt (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + j}`$ and $`0 \lt T_{1,j}`$ are the same proposition,
and the same case is selected on both sides. ∎

<a id="t-nextR_le0"></a>
## Theorem: the parent relation implies the ancestor relation (T.nextR_le0)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and $`i, k, b \in \mathbb{N}`$.
If $`k \to^{M}_i b`$ then $`k \le^{M}_0 b`$.

### Proof

By the case distinction in the definition of $`\to^M_i`$ (D.nextR).

- $`i = 0`$. Then $`k \to^{M}_0 b`$. Among the three conditions of the definition of $`\le^M_0`$ (D.le0),
  (1) $`k \lt \lvert M\rvert`$ and (2) $`b \lt \lvert M\rvert`$ are exactly the first and second conditions of
  the definition of $`\to^M_0`$ (D.nextrel0), and (3) is the chain consisting of the single step $`k \to^{M}_0 b`$.
- $`i \ne 0`$. Then $`k \to^{M}_1 b`$, and the fifth condition of the definition of $`\to^M_1`$ (D.nextrel1)
  is exactly $`k \le^{M}_0 b`$. ∎

<a id="t-nextR_src_in_T"></a>
## Theorem: the parent lies in the right summand (T.nextR_src_in_T)

### Theorem

Let $`A, T \in \mathrm{PairSeq}`$ satisfy $`T_{0,0} = 0`$.
If $`i, k, j_1 \in \mathbb{N}`$ satisfy $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ and
$`k \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$, then $`\lvert A\rvert \le k`$.

### Proof

Negate $`\lvert A\rvert \le k`$ and assume $`k \lt \lvert A\rvert`$.
By [T.nextR_le0](#t-nextR_le0) we have $`k \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$.
The three hypotheses of [T.le0_no_cross](#t-le0_no_cross), namely
$`k \lt \lvert A\rvert`$, $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ and
$`k \le^{A \mathbin{+\!\!+} T}_0 \lvert A\rvert + j_1`$, are now all available, so we get a contradiction. ∎

<a id="t-hasParent_append_right"></a>
## Theorem: existence of a parent is prefix-invariant (T.hasParent_append_right)

### Theorem

Let $`A, T \in \mathrm{PairSeq}`$ satisfy $`T_{0,0} = 0`$, and let
$`i, j_1 \in \mathbb{N}`$ satisfy $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$. Then

```math
\mathrm{hasParent}(A \mathbin{+\!\!+} T,\ i,\ \lvert A\rvert + j_1)
\iff
\mathrm{hasParent}(T,\ i,\ j_1)
```

($`\mathrm{hasParent}`$ [D.hasParent](Pss.md#d-hasParent)).

### Proof

The definition of $`\mathrm{hasParent}`$ (D.hasParent) asserts the existence and the uniqueness of an index
satisfying the condition.

**($`\Rightarrow`$)** Let $`j_0`$ be the unique index with $`j_0 \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$.
By [T.nextR_src_in_T](#t-nextR_src_in_T) we have $`\lvert A\rvert \le j_0`$, so setting
$`j_0' := j_0 - \lvert A\rvert`$ gives $`j_0 = \lvert A\rvert + j_0'`$.
The ($`\Rightarrow`$) direction of [T.nextR_append_right](#t-nextR_append_right) gives
$`j_0' \to^{T}_i j_1`$ (existence).
For uniqueness, suppose $`y`$ satisfies $`y \to^{T}_i j_1`$. Then
the ($`\Leftarrow`$) direction of [T.nextR_append_right](#t-nextR_append_right) gives
$`\lvert A\rvert + y \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$, so
by the uniqueness of $`j_0`$ we get $`\lvert A\rvert + y = \lvert A\rvert + j_0'`$, that is, $`y = j_0'`$.

**($`\Leftarrow`$)** Let $`j_0'`$ be the unique index with $`j_0' \to^{T}_i j_1`$.
The ($`\Leftarrow`$) direction of [T.nextR_append_right](#t-nextR_append_right) gives
$`\lvert A\rvert + j_0' \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$ (existence).
For uniqueness, suppose $`y`$ satisfies $`y \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$. Then
by [T.nextR_src_in_T](#t-nextR_src_in_T) we have $`\lvert A\rvert \le y`$, so setting
$`y' := y - \lvert A\rvert`$ gives $`y = \lvert A\rvert + y'`$.
The ($`\Rightarrow`$) direction of [T.nextR_append_right](#t-nextR_append_right) gives $`y' \to^{T}_i j_1`$, so
by the uniqueness of $`j_0'`$ we get $`y' = j_0'`$, that is, $`y = \lvert A\rvert + j_0'`$. ∎

<a id="t-parent_append_right"></a>
## Theorem: the parent shifts by the length of the prefix (T.parent_append_right)

### Theorem

Let $`A, T \in \mathrm{PairSeq}`$ satisfy $`T_{0,0} = 0`$, and let
$`i, j_1 \in \mathbb{N}`$ satisfy $`0 \lt (A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + j_1}`$ and
$`\mathrm{hasParent}(T, i, j_1)`$. Then

```math
\mathrm{par}^{A \mathbin{+\!\!+} T}_i(\lvert A\rvert + j_1) = \lvert A\rvert + \mathrm{par}^{T}_i(j_1)
```

($`\mathrm{par}^M_i`$ [D.parent](Pss.md#d-parent)).

### Proof

By the ($`\Leftarrow`$) direction of [T.hasParent_append_right](#t-hasParent_append_right),
$`\mathrm{hasParent}(A \mathbin{+\!\!+} T, i, \lvert A\rvert + j_1)`$ holds;
that is, the $`x`$ with $`x \to^{A \mathbin{+\!\!+} T}_i \lvert A\rvert + j_1`$ is unique.
Both of the following satisfy this condition.

- $`x := \mathrm{par}^{A \mathbin{+\!\!+} T}_i(\lvert A\rvert + j_1)`$.
  Apply [T.parent_nextR](Decrease.md#t-parent_nextR) to
  $`\mathrm{hasParent}(A \mathbin{+\!\!+} T, i, \lvert A\rvert + j_1)`$.
- $`x := \lvert A\rvert + \mathrm{par}^{T}_i(j_1)`$.
  Applying [T.parent_nextR](Decrease.md#t-parent_nextR) to $`\mathrm{hasParent}(T, i, j_1)`$ gives
  $`\mathrm{par}^{T}_i(j_1) \to^{T}_i j_1`$; now apply
  the ($`\Leftarrow`$) direction of [T.nextR_append_right](#t-nextR_append_right).

By uniqueness the two are equal. ∎

<a id="t-take_append_right"></a>
## Theorem: prefixes split across a concatenation (T.take_append_right)

### Theorem

For $`A, T \in \mathrm{PairSeq}`$ and $`j \in \mathbb{N}`$,

```math
\mathrm{take}_{\lvert A\rvert + j}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{take}_{j}\,T .
```

Here $`\mathrm{take}_m M`$ is the sequence of the first $`m`$ elements of $`M`$, and equals
$`M`$ itself when $`\lvert M\rvert \le m`$ (its length is $`\min(m, \lvert M\rvert)`$).

### Proof

A prefix of a concatenation satisfies

```math
\mathrm{take}_{p}\,(A \mathbin{+\!\!+} T)
 = \mathrm{take}_{p}\,A \mathbin{+\!\!+} \mathrm{take}_{p - \lvert A\rvert}\,T
```

Setting $`p := \lvert A\rvert + j`$, we have $`\lvert A\rvert \le p`$, hence
$`\mathrm{take}_{p}\,A = A`$, and moreover $`p - \lvert A\rvert = j`$. ∎

<a id="t-copyblock_append"></a>
## Theorem: the copy block is prefix-invariant (T.copyblock_append)

### Theorem

For $`A, T \in \mathrm{PairSeq}`$ and $`a, m, k, d_0, d_1 \in \mathbb{N}`$,

```math
\begin{aligned}
&\Bigl(\bigl((A \mathbin{+\!\!+} T)_{0,j} + k\,d_0,\ \cr
&\qquad (A \mathbin{+\!\!+} T)_{1,j} + k\,d_1\bigr)\Bigr)_{j = \lvert A\rvert + a}^{\lvert A\rvert + a + m - 1} \cr
&= \Bigl(\bigl(T_{0,j} + k\,d_0,\ T_{1,j} + k\,d_1\bigr)\Bigr)_{j = a}^{a + m - 1} .
\end{aligned}
```

Here $`\bigl(f(j)\bigr)_{j = b}^{b + m - 1}`$ is the sequence of length $`m`$ obtained by letting
the index $`j`$ run from $`b`$ upwards in steps of 1, and it is the empty sequence when $`m = 0`$.

### Proof

Both sides are sequences of length $`m`$, so it suffices to show that, for each $`p`$ with $`p \lt m`$,
their $`p`$-th elements agree. The $`p`$-th element of the left-hand side is, for $`j = \lvert A\rvert + a + p`$,

```math
\bigl((A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + a + p} + k\,d_0,\ (A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + a + p} + k\,d_1\bigr)
```

and the $`p`$-th element of the right-hand side is, for $`j = a + p`$,
$`\bigl(T_{0,a+p} + k\,d_0,\ T_{1,a+p} + k\,d_1\bigr)`$.
Since $`\lvert A\rvert + a + p = \lvert A\rvert + (a + p)`$, applying
[T.entry_append_right](#t-entry_append_right) with $`i := 0`$, $`j := a + p`$ and with
$`i := 1`$, $`j := a + p`$ gives

```math
(A \mathbin{+\!\!+} T)_{0,\lvert A\rvert + a + p} = T_{0,a+p},
\qquad
(A \mathbin{+\!\!+} T)_{1,\lvert A\rvert + a + p} = T_{1,a+p}
```

Hence the $`p`$-th elements of the two sides agree. ∎

<a id="t-Pred_append_right"></a>
## Theorem: the predecessor splits across a concatenation (T.Pred_append_right)

### Theorem

If $`A, T \in \mathrm{PairSeq}`$ satisfy $`2 \le \lvert T\rvert`$, then

```math
\mathrm{Pred}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{Pred}\,T
```

($`\mathrm{Pred}`$ [D.Pred](Pss.md#d-Pred)).

### Proof

Since $`\lvert A \mathbin{+\!\!+} T\rvert = \lvert A\rvert + \lvert T\rvert \ge \lvert T\rvert \ge 2`$, we have
$`\neg\bigl(\lvert A \mathbin{+\!\!+} T\rvert \le 1\bigr)`$, so by the second case of the definition of
$`\mathrm{Pred}`$ (D.Pred) we get $`\mathrm{Pred}\,(A \mathbin{+\!\!+} T) = \mathrm{dropLast}\,(A \mathbin{+\!\!+} T)`$.
Likewise the hypothesis $`2 \le \lvert T\rvert`$ gives $`\neg\bigl(\lvert T\rvert \le 1\bigr)`$, so
by the second case of the definition of $`\mathrm{Pred}`$ (D.Pred) we get
$`\mathrm{Pred}\,T = \mathrm{dropLast}\,T`$.

Since $`2 \le \lvert T\rvert`$ gives $`T \ne ()`$, the last element of $`A \mathbin{+\!\!+} T`$ is the last element of $`T`$,
and dropping it leaves $`A`$ concatenated with $`\mathrm{dropLast}\,T`$. That is,

```math
\mathrm{dropLast}\,(A \mathbin{+\!\!+} T) = A \mathbin{+\!\!+} \mathrm{dropLast}\,T . \qquad \blacksquare
```

<a id="t-no_hasParent_of_row0_zero"></a>
## Theorem: a column with row-0 value $`0`$ has no parent (T.no_hasParent_of_row0_zero)

### Theorem

Let $`M \in \mathrm{PairSeq}`$ and $`i, j_1 \in \mathbb{N}`$.
If $`M_{0,j_1} = 0`$ and $`\mathrm{hasParent}(M, i, j_1)`$, then a contradiction follows.

### Proof

By the definition of $`\mathrm{hasParent}`$ (D.hasParent) there is $`j_0`$ with $`j_0 \to^{M}_i j_1`$.
By [T.nextR_le0](#t-nextR_le0) we have $`j_0 \le^{M}_0 j_1`$, whose third condition (D.le0) is
$`j_0 \mathbin{(\to^{M}_0)^{*}} j_1`$.
Since $`M_{0,j_1} = 0`$, applying [T.rtg_to_root](#t-rtg_to_root) gives $`j_0 = j_1`$.
On the other hand [T.nextR_index_lt](Decrease.md#t-nextR_index_lt) gives $`j_0 \lt j_1`$, a contradiction. ∎
