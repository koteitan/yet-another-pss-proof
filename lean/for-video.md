[← README](README.md) | [English](for-video.md) | [Japanese](for-video-ja.md)

# A plan for the video explanation (chapters 4 and 5)

This file is **the design of a script for a video** explaining chapters 4 and 5 of the PSS
termination proof. It is not the proof text. The statements and their proofs live in the `.md`
of each module; what is written here is how they are arranged, which parts are hard, and what
should be drawn.

`Cnf.md` comes in three parts and `ArgDom.md` in five because GitHub stops rendering the
formulas of a page beyond a certain amount. That split is **a matter of display**, not a
mathematical seam. Below the splits are ignored and the material is laid out in units that
carry mathematical meaning.

Where to look in the proof text:

| part here | text |
|---|---|
| Part I | [Column-lex order](Seqlex.md) [2](Seqlex-2.md) |
| Part II | [Cantor normal form condition](Cnf.md) [2](Cnf-2.md) [3](Cnf-3.md), [Column invariants](Column.md) [2](Column-2.md) [3](Column-3.md) [4](Column-4.md) |
| Part III | [Bachmann cofinality](Cofinality.md) [2](Cofinality-2.md) [3](Cofinality-3.md), [The core of cofinality](ArgDom.md) [2](ArgDom-2.md) [3](ArgDom-3.md) [4](ArgDom-4.md) [5](ArgDom-5.md) |
| Part IV | [Iterated inductive set](Wset.md) [2](Wset-2.md) [3](Wset-3.md) [4](Wset-4.md) |

---

## 0. How the pictures are drawn (the UBI model)

**The way hydras are drawn is already fixed by the existing series**, and this document follows
it. Do not invent another way of drawing.

- implementation: `tools/pair_hydra.py` (`PairHydra`, `Tier`) in `googology-manim`
- definitions: `tools/pair.py` there (`p0`, `p1`, `expand`)
- the wording already recorded: `transcripts/pss.md` there

### 0.1 A pair sequence is a two-tier hydra

**One hydra is drawn per row, so a pair sequence gets two tiers.** The height of a node is the
value of that row itself, and **a larger value is drawn higher**. The value is written inside
the dot.

- **upper tier (the row-0 hydra)** — height is the row-0 value; the parent is $`P_0`$. This is
  exactly the hydra of the primitive sequence system
- **lower tier (the row-1 hydra)** — height is the row-1 value; the parent is $`P_1`$

```
P0(x) = the rightmost column left of x whose row-0 value is smaller than x's
P1(x) = the rightmost column among the ancestors of x in the upper tier
        whose row-1 value is smaller than x's
```

That $`P_1`$ **looks only at ancestors** is the heart of the model: a column that is not an
ancestor is skipped even when its row-1 value is smaller. That is where the name
Upper-Branch-Ignoring comes from.

Example: $`(0,0)(1,1)(2,0)(1,1)`$

```
           column 0   column 1   column 2   column 3
upper         0          1          2          1      <- height = row-0 value
lower         0          1          0          1      <- height = row-1 value

upper parent   1 -> 0     2 -> 1     3 -> 0
lower parent   1 -> 0     2 -> none  3 -> 0
```

Look at the lower-tier parent of column 3. Column 2, immediately to its left, has row-1 value
$`0`$, which is smaller than $`1`$, and yet **it cannot be the parent**: following the ancestors
of column 3 in the upper tier jumps straight to column 0, and column 2 sits on a different
branch.

In the proof text these are $`P_0`$ = [D.nextrel0](Pss.md#d-nextrel0) and
$`P_1`$ = [D.nextrel1](Pss.md#d-nextrel1). They are the same thing.

### 0.2 The upper tier is a forest, the lower tier gives the subscripts

Read from the left, the height in the upper tier goes up by at most one
([D.steps1](Seqlex.md#d-steps1), [T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS)), so the upper
tier is **the preorder listing of a forest**. The **subtree** of a column is the run of columns
to its right that stay higher than it.

The translation $`\mathrm{tr}`$ carries this structure straight over to a term.

```
tr(())           = Z
tr(p :: rest)    = P( the lower-tier height of p,
                      tr(the subtree of p in the upper tier),
                      tr(the rest) )
```

In $`p_a(b) + c`$,

- $`a`$ = **the lower-tier height of that column** (its row-1 value)
- $`b`$ = **the subtree of that column in the upper tier**
- $`c`$ = the forest remaining to the right

**Draw: circle one mountain in the upper tier and drop a vertical line from its root to the same
column in the lower tier, pointing at the three things — inside the circle is $`b`$, outside is
$`c`$, and this lower-tier height is the subscript $`a`$.**

### 0.3 The expansion cuts a head and lays down copies of the bad part

Use the words the existing series already uses.

1. **Cut** the rightmost column (both tiers together)
2. If the row-1 value of the cut column is $`0`$, look for its parent in the upper tier;
   otherwise in the lower tier. That parent is the **bad root**
3. Everything left of the bad root is the **good part**; from the bad root up to just before the
   cut column is the **bad part**
4. Lay down copies of the bad part. When the row-1 value was not $`0`$, each copy is raised in
   the upper tier by the **lift** (the row-0 value of the cut column minus the row-0 value of
   the bad root), so the copies form a **staircase**. **The lower tier does not rise**

The dictionary with the proof text:

| the existing series | the proof text |
|---|---|
| the column being cut | the last column $`j_1 = \lvert M\rvert - 1`$ |
| the bad root | the parent $`j_0`$ ([D.parent](Pss.md#d-parent)) |
| the good part | the first $`j_0`$ columns of $`M`$ (`take`) |
| the bad part | the block |
| the lift | $`d_0`$ |
| the staircase | ascending copies (the branch $`i_1 = 1`$) |
| it just disappears | $`\mathrm{Pred}`$ (drop the last column) |

**Only the way copies are counted differs.** The existing series uses the activation function
$`f(n) = n^2`$ and lays down $`f(n)+1`$ copies. The $`M[n]`$ of the proof text is $`n`$ copies
($`n \ge 1`$); it fixes no $`f`$ and handles all $`n \ge 1`$ at once. Mind this when matching a
picture against the text.

**Draw: the column being cut in red, the bad root in another colour, the bad part circled in
blue, and animate the copies appearing to the right. For ascending copies, show the staircase
climbing while the lower tier keeps its heights.**

---

## The overall design

The final goal is

```
the expansion relation step is well-founded (one cannot keep expanding forever)
```

Chapter 3 already gives "one expansion step strictly decreases the measure $`\mathrm{tr}(M)`$".
What is left is that **the order $`\prec`$ on the measure is well-founded on the image of the
standard forms**. That is all of chapters 4 and 5.

Well-foundedness is obtained from two pillars (the method of Buchholz 1987 §2).

```
pillar 1  Bachmann cofinality   : a standard form N with N < M is covered by some M[n]
pillar 2  the iterated inductive set W_u : every standard form lies in W_u for some u
pillar 1 + pillar 2 ==> well-foundedness
```

Chapter 4 is **the scaffolding** for raising those two, chapter 5 is **the pillars themselves**.

---

## Part I. Moving the stage from terms to lists

### The main proposition

> **On standard forms, the order on terms and the column-lex order agree.**
> For standard forms with $`M \ne N`$,
> $`\mathrm{tr}\,M \prec \mathrm{tr}\,N \iff M \prec_{\mathrm{lex}} N`$
> ([T.olt_ST_iff_seqlex](Seqlex-2.md#t-olt_ST_iff_seqlex))

The column-lex order is a naive definition.

```
seqlex(M, N)  :<=>  M is empty and N is not, or
                    if the heads differ, the lexicographic comparison of the head pairs,
                    if the heads agree, the recursion on the tails
```

### Why this is what matters most in chapter 4

From here on **the term $`p_a(b)+c`$ never appears again**. One does not have to look at the
hydra: reading the two sequences from the left and comparing the first column where they differ
decides the order. Everything in chapter 5 happens on lists, so this isomorphism is what sets
the stage.

**Draw: show the same two pair sequences both as two-tier hydras and as sequences (the matrix
form with the pair stacked vertically), and say "either way the comparison is the same". An
animation drawing a vertical line at the first differing column works well.**

### The line of the proof

1. A standard form is a block ([T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS)). A block is
   "the head sits at height $`d`$, every column is at height at least $`d`$, and adjacent steps
   are at most one"
2. For a block $`B`$, the subtree of the head column and the remainder correspond exactly to the
   two arguments of the recursion of $`\mathrm{tr}`$
   ([T.blockok_arg](Seqlex.md#t-blockok_arg), [T.blockok_tail](Seqlex.md#t-blockok_tail))
3. **The first difference between two lists shows up either on the subtree side or on the
   remainder side** ([T.seqlex_arg_or_tail](Seqlex.md#t-seqlex_arg_or_tail)). This is the key
   that keeps the recursion turning
4. Induction on the sum of the lengths gives the isomorphism

### The hard part

- **[T.blockok_oper](Seqlex-2.md#t-blockok_oper) (expansion preserves being a block)** — 179
  lines in Lean and 365 in Isabelle, the largest in this part. The difficulty is showing that
  when $`n`$ copies of the bad part are laid side by side, **the "adjacent step at most one"
  condition does not break at the seams**. At a seam the height jumps from the end of one copy
  to the head of the next, and that jump has to be bounded by one, in terms of the lift $`d_0`$.
  **Zooming in on a single seam of the staircase is the picture to show**

---

## Part II. The shape of a standard form

Part I moved the stage to lists. The arguments of Part III use, in bulk, properties of the form
"a standard form looks like this". Preparing them is this part, and it has **three main
propositions**.

### II-1 The Cantor normal form condition

> **The translation of a standard form satisfies cnf** ([T.cnf_ST_PS](Cnf-3.md#t-cnf_ST_PS))

```
cnf(Z)                 :<=> true
cnf(P(a,b,Z))          :<=> cnf(b)
cnf(P(a,b,P(e,f,g)))   :<=> cnf(b) and not P(a,b,Z) < P(e,f,Z) and cnf(P(e,f,g))
```

The condition says the sum of principal terms is weakly decreasing, which is the decreasing
condition on the exponents of the Cantor normal form
$`\omega^{a_1} + \dots + \omega^{a_k}`$ ($`a_1 \ge \dots \ge a_k`$) of an ordinal.

**Draw: several mountains standing side by side in the upper tier, and reading the roots from
left to right they never grow. Since the comparison is decided by the lower-tier height (the
subscript), point at the lower tier of each root while comparing.**

The proof is by induction on $`\mathrm{ST\_PS}`$: the diagonal (base case) and the expansion
(inductive step). The step is the body, and it divides into the complete-copy branch and the
ascending-copy branch.

### II-2 Prefix invariance

> **Whatever is prepended to a list, nothing inside the second half changes**
> (the group from [T.entry_append_right](Column.md#t-entry_append_right) to
> [T.parent_append_right](Column.md#t-parent_append_right))

The parent relation, the ancestor relation, the existence of a parent, the search row and the
expansion are all invariant under prepending, and moreover **an upper-tier parent edge never
crosses the boundary** between the prefix and the second half
([T.nextrel0_no_cross](Column.md#t-nextrel0_no_cross)).

**Draw: prepend another hydra on the left and show that the mountains on the right keep their
shape and their edges. For "never crosses", draw an edge spanning the boundary and put a cross
on it.**

Because of this, Part III can say "it is enough to look at the bad part we are interested in".
The proof of cofinality gets away with local arguments entirely thanks to this part.

### II-3 The positional invariants r1ok and z0ok

> **A standard form satisfies both of the following**
> ([T.r1ok_ST_PS](Column-3.md#t-r1ok_ST_PS), [T.z0ok_ST_PS](Column-4.md#t-z0ok_ST_PS))

```
r1ok(M) :<=> a column whose upper-tier height is positive always has a parent (the nearest
             preceding column whose upper-tier height is exactly one smaller), and its
             lower-tier height exceeds the parent's lower-tier height by at most one
z0ok(M) :<=> a column whose upper-tier height is 0 has lower-tier height 0 as well
```

**Draw: join a parent and its child in the upper tier with an edge, connect the same two columns
down to the lower tier with vertical lines, and show that the lower-tier difference is at most
one. For z0ok: "a column standing on the ground upstairs stands on the ground downstairs too".**

From these two follow **the existence and the uniqueness of the parent**
([T.parent0_exists](Column-4.md#t-parent0_exists),
[T.parent1_exists](Column-4.md#t-parent1_exists), [T.hp_last](Column-4.md#t-hp_last)). The
definition of the expansion has a branch "if there is no parent, drop the last column", so only
once we know that **a standard form always has a bad root for the column being cut** can that
branch be discharged and the fourth branch be the only one left to handle.

### The hard parts

- **[T.cnf_ctx_cong](Cnf-2.md#t-cnf_ctx_cong) (context congruence of the condition)** — 160
  lines in Lean. What makes it hard is that **the translation $`\mathrm{tr}`$ is not
  compositional for concatenation**. The content of the subtree of the head column is decided by
  what comes after it, so

  ```
  cnf(tr(G ++ X))   and   cnf(tr G) and cnf(tr X)
  ```

  are not equivalent: the very shape of the mountains of the prefix $`G`$ depends on $`X`$. To
  say "replacing the second half keeps the condition", one has to write down everything that
  stays invariant across the replacement, and that takes six hypotheses.
  **To draw it, show the same $`G`$ forming different mountains depending on what is appended: a
  lower column arriving cuts the mountain there, a higher one is swallowed into it**
- **[T.r1ok_copyExp](Column-2.md#t-r1ok_copyExp) (the lower-tier discipline of a replicated
  expansion)** — 118 lines in Lean, 452 in Isabelle. With $`n`$ copies laid down, the parent of
  a column inside the $`k`$-th copy may sit in the same copy or in the previous one, and in the
  latter case every index calculation is offset by the lift $`d_0`$. The proof is built around
  the quotient-remainder decomposition of the index
  ([T.index_decomp](Column-2.md#t-index_decomp)) and works the positions out by hand
- **CNF preservation in the ascending-copy branch**
  ([T.cnf_oper_i1eq1](Cnf-3.md#t-cnf_oper_i1eq1), [T.cnf_copies](Cnf-3.md#t-cnf_copies)) — the
  concept is not hard but the work is long. The nested tower of lifts
  $`\mathrm{cp}_d(B, n+1) = B \mathbin{+\!\!+} \mathrm{sh}_d(\mathrm{cp}_d(B,n))`$ is peeled one
  layer at a time, and at each layer both "this whole list is a single mountain" and "the lower
  bound on the height of the tail" have to be rebuilt

---

## Part III. Bachmann cofinality (pillar 1)

### The main proposition

> **A standard form strictly below $`M`$ is bounded above by one of the terms of the fundamental
> sequence of $`M`$.** If standard forms $`M, N`$ satisfy
> $`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$, then for some $`n \ge 1`$,
> $`\mathrm{tr}\,N \preceq \mathrm{tr}(M[n])`$
> ([T.pss_cofinality_holds](Final.md), whose core is
> [T.pss_cofinality_of_argdom](Cofinality-3.md#t-pss_cofinality_of_argdom))

**Draw: countless standard forms hanging below $`M`$, and show that whichever one is picked, one
of $`M[1], M[2], M[3], \dots`$ covers it from above — animate the covered region growing with
$`n`$. This is the intuition for pillar 1.**

### The staircase of reductions

The proof is five reductions stacked up. The staircase itself is worth one slide.

```
(1) cofinality for the order on terms
      | the order isomorphism of Part I
(2) cofinality for the column-lex order      D.SeqlexCofinality
      | case distinction on the four branches of the expansion
(3) only the fourth branch is left           the other three merely drop the last column
      | split into complete copies and ascending copies
(4) two "cruxes"                             T.crux_zero and D.AscCrux
      | erase the host (the surrounding list)
(5) the host-free core                       D.ArgDomCore
```

### What the crux of the fourth branch says

Let $`N \prec_{\mathrm{lex}} M`$. Since $`M[n]`$ is $`n`$ copies of the bad part laid side by
side, covering $`N`$ uses the fact that "making $`n`$ larger extends the run of copies
arbitrarily far to the right". The problem is that we do not know how far $`N`$ agrees with
$`M`$ or where it drops below.

- **complete copies** ([T.crux_zero](Cofinality-2.md#t-crux_zero)): the copies are all identical,
  so taking enough of them to contain the branching point of $`N`$ covers it
  ([T.copy_dom_zero](Cofinality-2.md#t-copy_dom_zero))
- **ascending copies** ([D.AscCrux](Cofinality-2.md#d-AscCrux)): each copy climbs one step of the
  staircase, so this is not a repetition of one shape. This is the real difficulty, and it is
  reduced to ArgDomCore below

### The host-free core ArgDomCore

> **Inside a single standard form, let two columns with the same lower-tier height $`w`$ stand as
> ancestor and descendant in the upper tier, at heights $`u`$ and $`u+e`$. Then the subtree
> $`B`$ of the higher one is covered, in the column-lex order, by the copy of the subtree $`A`$
> of the lower one raised by $`e`$.**
> ([D.ArgDomCore](ArgDom.md#d-ArgDomCore); it holds by
> [T.argDomCore_holds](ArgDom-5.md#t-argDomCore_holds))

```
upper height u+e   (u+e, w)  <- the higher one; its subtree B
                      |         (ancestor and descendant upstairs, same height w downstairs)
upper height u     (u, w)    <- the lower one; its subtree A = A1 ++ (u+e,w) :: (B ++ A2)
```

The side condition SpineOK says "every right-visible column between the two has lower-tier height
at least $`w`$", that is, **the two are siblings with respect to the lower tier**.

**Draw: light up the two columns that have the same lower-tier height, and trace the edges
upstairs showing that they are ancestor and descendant. Then raise the lower mountain by $`e`$
and superimpose it on the higher one, showing that it fits. This is the showpiece of chapter 5.**

Being "host-free" matters because in this form **the surrounding lists $`X`$ and $`Z`$
disappear**. The prefix invariance of Part II is what makes that erasure possible.

### The proof of ArgDomCore

Induction on $`\mathrm{ST\_PS}`$ ([T.argDomCoreOn_ST_PS](ArgDom-5.md#t-argDomCoreOn_ST_PS)). The
base case, the diagonal, is nearly trivial; the inductive step is the fourth branch of the
expansion, and it splits once more into three cases.

| case | situation | size |
|---|---|---|
| A1 | the two marked columns fall inside one and the same copy | 44 lines in Lean |
| B | the two columns lie outside the bad part | 185 lines in Lean |
| **A2** | **the two columns straddle a copy boundary** | **461 lines in Lean, 1519 in Isabelle** |

### The hard parts

- **[T.argDomCoreOn_bad_A2](ArgDom-4.md#t-argDomCoreOn_bad_A2)** — **the largest single lemma in
  the whole development**, 461 lines in Lean and 1519 in Isabelle. In the proof text it takes a
  page of its own. The difficulty is that when the two marked columns straddle a copy boundary,
  one belongs to the $`k`$-th copy and the other to the $`k'`$-th, so **the two sit on different
  steps of the staircase and are lifted by different amounts**. The conclusion of ArgDomCore is
  a uniform shift "raise by $`e`$", so two fragments carrying different lifts have to be put
  back on a common host before they can be compared. That is done by splitting the list at a
  level ([T.arg_split](ArgDom-2.md#t-arg_split)) and using composition and inversion of lifts
  ([T.shiftl0_shiftr0](ArgDom-2.md#t-shiftl0_shiftr0),
  [T.shiftr0_comm](ArgDom-2.md#t-shiftr0_comm)) over and over.
  **In the video, putting a mark on two different steps of the staircase and showing that no
  single $`e`$ lines both of them up already conveys why this is hard**
- **[T.copy_dom_zero](Cofinality-2.md#t-copy_dom_zero)** — 124 lines in Lean. The crux on the
  complete-copy side: taking $`n`$ large enough covers, proved over a block decomposition that
  is uniform in $`n`$ ([T.oper_bad_blocks_all](Cofinality.md#t-oper_bad_blocks_all))

---

## Part IV. The iterated inductive set $`W_u`$ (pillar 2)

### The main proposition

> **Every standard form lies in $`W_u`$ for some $`u`$**
> ([T.W_membership](Wset-4.md#t-W_membership))

And $`u`$ can be named explicitly: **the maximum lower-tier height** will do
([T.mem_W_maxr1](Wset-4.md#t-mem_W_maxr1)).

### What $`W_u`$ is

The least fixpoint of an operator $`A_u`$ ([D.Aop](Wset.md#d-Aop), [D.W](Wset.md#d-W)). A list
belongs to $`A_u(X)`$ in one of three ways.

```
(1) length at most 1 and lower-tier height 0             -- the bottom
(2) the list is not an orphan, and M[n] is in X for all n -- cutting always lands on
                                                            something already known
(3) for some m < u the list is a "lower-tier orphan", and
    graft(M, z) is in X for every z in W_m that starts from the ground
                                                         -- one can graft from a lower level
```

A "lower-tier orphan" means that the last column has lower-tier height $`m+1`$ and has no parent
in the lower tier ([D.domT](Wset.md#d-domT)). The graft removes that last column and rebuilds
$`z`$ starting from the height it occupied ([D.graft](Wset.md#d-graft)).

**Draw: (1) is "just standing on the ground", (2) is "cutting a head always lands on something
already known", (3) is "grafting a hydra from a lower level onto an end that has no parent
downstairs lands on something already known". Three boxes. For (3), show the last column
vanishing and another hydra growing out of that spot.**

Being a least fixpoint gives two principles.

```
(A1) A_u(W_u) = W_u             the fixpoint equation        T.A1
(A2) A_u(Y) subset Y ==> W_u subset Y   the induction principle   T.A2
```

The definition of $`W_u`$ refers to the $`W_m`$ of smaller levels, so a recursion on $`u`$ and a
least fixpoint at each level are nested. That is what "iterated inductive" means.

### The line of the proof

1. Every list belongs to $`W^{*}`$ ([T.mem_Wstar](Wset-4.md#t-mem_Wstar)), where
   $`W^{*} = \{R \mid \text{if every column of } R \text{ has positive upper-tier height, then } (0,v) :: R \in W_v \text{ for every } v\}`$
2. For that, prove $`A_u(W^{*}) \subseteq W^{*}`$ ([T.Wstar_closed](Wset-4.md#t-Wstar_closed))
   and apply (A2)
3. Taking the level from a bound on the lower-tier height gives the membership
   ([T.mem_W_of_bound](Wset-4.md#t-mem_W_of_bound))

### The hard parts

- **[T.Wstar_closed](Wset-4.md#t-Wstar_closed)** — 104 lines in Lean, 489 in Isabelle. For each
  of the three branches of $`A_u`$, one shows that the list with a root $`(0,v)`$ added at the
  left lies in $`W_v`$. Branch (2) needs the result of cutting the list with the root to be the
  result of cutting the original list with the root put back on
- **[T.oper_cons_nat](Wset-3.md#t-oper_cons_nat)** — 94 lines in Lean, 497 in Isabelle. This is
  the lemma that says "adding a root commutes with the expansion". One extra column shifts every
  index by one, so the upper-tier parent and ancestor relations, the lower-tier parent and the
  search row all have to be tracked through that shift (the group from
  [T.entry_cons](Wset-3.md#t-entry_cons) to [T.nextR_cons_last](Wset-3.md#t-nextR_cons_last) is
  the toolkit for exactly that)
- **The tower $`\mathrm{tow}`$** ([D.tow](Wset-3.md#d-tow)) — the list obtained by grafting $`k`$
  times: $`t_0 = ()`$ and $`t_{k+1} = (0,v) :: \mathrm{graft}(R, t_k)`$.
  **This is a hydra grafted into itself over and over, so it is the easiest thing in the whole
  proof to animate: hydras of the lower level sprouting one after another at the place of the
  lower-tier orphan**

---

## Part V. Where the two meet

Once both pillars stand, the conclusion follows
([T.wf_of_cofinality_and_membership](Wset-4.md#t-wf_of_cofinality_and_membership)).

```
pillar 2 gives M in W_u
  | induction on W_u (A2)
M is accessible (Acc)                    T.acc_of_W
  | pillar 1 (cofinality) covers every standard form below M by some M[n]
the order on standard forms is well-founded
  | the decrease of the measure from chapter 3
the expansion relation step is well-founded; no infinite expansion sequence exists
```

Branch (2) of the induction for $`W_u`$ is "cutting lands on something already known", and
cofinality says "anything smaller is covered once you cut". The two mesh exactly.
**This is the keystone of the whole proof and the closing scene of the video.**

---

## The hard parts at a glance

Line counts are a proxy for difficulty. They are measured independently in the two
formalizations, so an entry that is large in both is genuinely hard.

| lemma | what is hard | Lean | Isabelle |
|---|---|---:|---:|
| [T.argDomCoreOn_bad_A2](ArgDom-4.md#t-argDomCoreOn_bad_A2) | the marks straddle a copy boundary, so the two lifts differ | 461 | 1519 |
| [T.argDomCoreOn_bad_B](ArgDom-3.md#t-argDomCoreOn_bad_B) | the marks lie outside the bad part | 185 | 613 |
| [T.blockok_oper](Seqlex-2.md#t-blockok_oper) | the adjacent-step bound survives the seams of the staircase | 179 | 365 |
| [T.cnf_ctx_cong](Cnf-2.md#t-cnf_ctx_cong) | the translation is not compositional for concatenation | 160 | 174 |
| [T.copy_dom_zero](Cofinality-2.md#t-copy_dom_zero) | the crux on the complete-copy side | 124 | 325 |
| [T.r1ok_copyExp](Column-2.md#t-r1ok_copyExp) | index arithmetic for parents across copies | 118 | 452 |
| [T.cnf_oper_i1eq1](Cnf-3.md#t-cnf_oper_i1eq1) | the nested tower of lifts | 108 | 259 |
| [T.Wstar_closed](Wset-4.md#t-Wstar_closed) | the list with a root added lands in the lower level | 104 | 489 |
| [T.oper_cons_nat](Wset-3.md#t-oper_cons_nat) | the index shift caused by one extra root | 94 | 497 |
| [T.crux_zero](Cofinality-2.md#t-crux_zero) | the crux of the complete-copy branch | 92 | 297 |

The difficulties are of two kinds.

- **Conceptual** — [T.cnf_ctx_cong](Cnf-2.md#t-cnf_ctx_cong) (the translation is not
  compositional) and [T.argDomCoreOn_bad_A2](ArgDom-4.md#t-argDomCoreOn_bad_A2) (the lift is not
  uniform). The obstacle can be put into words, so it is worth explaining in the video
- **Sheer length** — the index calculations. Following one column through the picture is enough;
  there is no need to follow them all

---

## A suggested order for the video

1. **Recall how the pictures work** (section 0) — the two tiers, height, that $`P_1`$ looks only
   at ancestors, and cut / bad root / good part / bad part / lift / staircase. For someone who
   has seen the earlier series this is a recap; for anyone else it is the way in
2. **The overall design** — the goal and the two pillars, on one slide
3. **Part I** — comparing hydras and comparing sequences give the same answer; the stage moves
   to lists
4. **Part II** — the shape of a standard form. Emphasize prefix invariance (adding on the left
   changes nothing on the right). Do not enumerate the small lemmas
5. **Part III** — cofinality. Show the staircase of reductions on one slide, then spend the time
   on the picture for ArgDomCore (the ancestor and descendant with the same lower-tier height,
   and the raised subtree)
6. **Part IV** — the three branches of $`W_u`$, and the tower. The grafting animation
7. **Part V** — the two pillars mesh and well-foundedness comes out

Part II has many lemmas, but **in the video only its three main propositions (cnf, prefix
invariance, r1ok and z0ok) need to be shown; the proofs can be skipped**. The time is better
spent on the order isomorphism of Part I, ArgDomCore in Part III, and the tower in Part IV.
