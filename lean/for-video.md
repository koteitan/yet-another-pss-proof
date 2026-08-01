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

## 0. The hydra dictionary

The video explains everything through pictures of hydras (forests). Fix the dictionary between
pair sequences and hydras first. **The correspondence is not a metaphor; it follows from the
definitions.**

### 0.1 A pair sequence is the depth-first listing of a forest

A pair sequence $`M`$ is a finite list of pairs (row 0, row 1). In a standard form,

- **row 0 is the depth of a node**. Reading left to right, the depth goes up by at most one
  ([D.steps1](Seqlex.md#d-steps1), [T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS))
- hence the whole list is exactly the **depth-first (preorder) listing of a forest**
- **row 1 is a label attached to that node**. It is information separate from the tree shape,
  and it becomes the subscript $`a`$ of $`p_a(b)`$

```
list    (0,0) (1,1) (2,2) (1,0) (2,1)

depth    0     1     2     1     2
        ●
        └── ●
            └── ●
        ●             <- back to depth 1: the second child of the first ●
            └── ●
```

The parent is "the nearest node to the left whose depth is exactly one smaller"
([D.nextrel0](Pss.md#d-nextrel0)).

### 0.2 Row 1 is a second parent relation

Row 1 carries a parent relation of the same shape ([D.nextrel1](Pss.md#d-nextrel1)), which
searches only among the row-0 ancestors. **In the hydra picture, draw the tree edges (row 0)
solid and overlay the row-1 parent as a dashed arrow.**

### 0.3 The translation tr sends a forest to a term

```
tr(())          = Z
tr(p :: rest)   = P( row 1 of p,
                     tr(the block of descendants of p),
                     tr(the rest) )
```

So in $`p_a(b) + c`$,

- $`a`$ = the label of the node (row 1)
- $`b`$ = the subtree of that node
- $`c`$ = the forest of the siblings to its right and beyond

**Draw: circle the leftmost tree of the forest and colour three regions — inside the circle is
$`b`$, outside is $`c`$, the label of the root is $`a`$.**

### 0.4 The expansion M[n] cuts a head off the hydra

Look at the last node $`j_1`$ ([D.oper](Pss.md#d-oper)).

| case | what happens |
|---|---|
| length at most 1 | nothing |
| the last node is $`(0,0)`$ | drop that last node |
| it has no parent | drop that last node |
| **otherwise (the fourth branch)** | lay down $`n`$ copies of the block from the parent up to just before the end |

The fourth branch is the hydra proper. It splits again into two.

- **complete copies** (the label of the last node is $`0`$): the block is repeated $`n`$ times
  unchanged
- **ascending copies** (the label is positive): the $`k`$-th copy is pushed $`k \cdot d_0`$
  deeper, where $`d_0`$ is the depth difference between the node that was cut and its parent

**Draw: circle the head being cut in red and the block being copied in blue, and animate the
$`n`$ copies appearing to the right. For ascending copies, show the copies stepping deeper one
after another.**

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

From here on **the term $`p_a(b)+c`$ never appears again**. One does not have to look at trees:
reading the two lists from the left and comparing the first position where they differ decides
the order. Everything in chapter 5 happens on lists, so this isomorphism is what sets the stage.

**Draw: show the same two forests both as trees and as lists, and say "either way the comparison
is the same". An animation drawing a vertical line at the first difference works well.**

### The line of the proof

1. A standard form is a block ([T.blockok_ST_PS](Seqlex-2.md#t-blockok_ST_PS)). A block is
   "the head sits at depth $`d`$, every element is at depth at least $`d`$, and adjacent steps
   are at most one"
2. For a block $`B`$, the subtree of the head node and the remainder correspond exactly to the
   two arguments of the recursion of $`\mathrm{tr}`$
   ([T.blockok_arg](Seqlex.md#t-blockok_arg), [T.blockok_tail](Seqlex.md#t-blockok_tail))
3. **The first difference between two lists shows up either on the subtree side or on the
   remainder side** ([T.seqlex_arg_or_tail](Seqlex.md#t-seqlex_arg_or_tail)). This is the key
   that keeps the recursion turning
4. Induction on the sum of the lengths gives the isomorphism

### The hard part

- **[T.blockok_oper](Seqlex-2.md#t-blockok_oper) (expansion preserves being a block)** — 179
  lines in Lean and 365 in Isabelle, the largest in this part. The difficulty is showing that
  when $`n`$ blocks are laid side by side in the fourth branch, **the "adjacent step at most
  one" condition does not break at the seams**. At the seam the depth jumps from the depth of
  the end of one copy to the depth of the head of the next, and that jump has to be bounded by
  one, in terms of the lift $`d_0`$ of the ascending copies

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

**Draw: put several trees side by side with roots of decreasing size, showing that the roots
never grow as one reads to the right.**

The proof is by induction on $`\mathrm{ST\_PS}`$: the diagonal (base case) and the expansion
(inductive step). The step is the body, and it divides into the complete-copy branch and the
ascending-copy branch.

### II-2 Prefix invariance

> **Whatever is prepended to a list, nothing inside the second half changes**
> (the group from [T.entry_append_right](Column.md#t-entry_append_right) to
> [T.parent_append_right](Column.md#t-parent_append_right))

The parent relation, the ancestor relation, the existence of a parent, the search row and the
expansion are all invariant under prepending, and moreover **a row-0 parent edge never crosses
the boundary** between the prefix and the second half
([T.nextrel0_no_cross](Column.md#t-nextrel0_no_cross)).

**Draw: prepend another forest on the left and show that the trees on the right keep their shape
and their edges. For "never crosses", put a cross on an edge that would span the boundary.**

Because of this, Part III can say "it is enough to look at the block we are interested in". The
proof of cofinality gets away with local arguments entirely thanks to this part.

### II-3 The positional invariants r1ok and z0ok

> **A standard form satisfies both of the following**
> ([T.r1ok_ST_PS](Column-3.md#t-r1ok_ST_PS), [T.z0ok_ST_PS](Column-4.md#t-z0ok_ST_PS))

```
r1ok(M) :<=> a node at positive depth always has a parent (the nearest preceding node whose
             depth is exactly one smaller), and its row 1 exceeds the parent's row 1 by at
             most one
z0ok(M) :<=> a node at depth 0 carries label 0
```

**Draw: write the label on every node and show "child label <= parent label + 1" with an arrow.
Roots are pinned to label 0.**

From these two follow **the existence and the uniqueness of the parent**
([T.parent0_exists](Column-4.md#t-parent0_exists),
[T.parent1_exists](Column-4.md#t-parent1_exists), [T.hp_last](Column-4.md#t-hp_last)). The
definition of the expansion has a branch "if there is no parent, drop the last node", so only
once we know that **a standard form always has a parent at its end** can that branch be
discharged and the fourth branch be the only one left to handle.

### The hard parts

- **[T.cnf_ctx_cong](Cnf-2.md#t-cnf_ctx_cong) (context congruence of the condition)** — 160
  lines in Lean. What makes it hard is that **the translation $`\mathrm{tr}`$ is not
  compositional for concatenation**. The content of the subtree of the head node is decided by
  what comes after it, so

  ```
  cnf(tr(G ++ X))   and   cnf(tr G) and cnf(tr X)
  ```

  are not equivalent: the very shape of the tree of the prefix $`G`$ depends on $`X`$. To say
  "replacing the second half keeps the condition", one has to write down everything that stays
  invariant across the replacement, and that takes six hypotheses.
  **To draw it, show the same $`G`$ turning into different trees depending on what is appended**
- **[T.r1ok_copyExp](Column-2.md#t-r1ok_copyExp) (the row-1 discipline of a replicated
  expansion)** — 118 lines in Lean, 452 in Isabelle. With $`n`$ copies laid down, the parent of
  a node inside the $`k`$-th copy may sit in the same copy or in the previous one, and in the
  latter case every index calculation is offset by the lift $`d_0`$. The proof is built around
  the quotient-remainder decomposition of the index
  ([T.index_decomp](Column-2.md#t-index_decomp)) and works the positions out by hand
- **CNF preservation in the ascending-copy branch**
  ([T.cnf_oper_i1eq1](Cnf-3.md#t-cnf_oper_i1eq1), [T.cnf_copies](Cnf-3.md#t-cnf_copies)) — the
  concept is not hard but the work is long. The nested tower of shifts
  $`\mathrm{cp}_d(B, n+1) = B \mathbin{+\!\!+} \mathrm{sh}_d(\mathrm{cp}_d(B,n))`$ is peeled one
  layer at a time, and at each layer both "this whole list is a single tree" and "the lower
  bound on the depth of the tail" have to be rebuilt

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
(3) only the fourth branch is left           the other three merely drop the last node
      | split into complete copies and ascending copies
(4) two "cruxes"                             T.crux_zero and D.AscCrux
      | erase the host (the surrounding list)
(5) the host-free core                       D.ArgDomCore
```

### What the crux of the fourth branch says

Let $`N \prec_{\mathrm{lex}} M`$. Since $`M[n]`$ is $`n`$ copies of a block laid side by side,
covering $`N`$ uses the fact that "making $`n`$ larger extends the run of copies arbitrarily far
to the right". The problem is that we do not know how far $`N`$ agrees with $`M`$ or where it
drops below.

- **complete copies** ([T.crux_zero](Cofinality-2.md#t-crux_zero)): the copies are all identical,
  so taking enough of them to contain the branching point of $`N`$ covers it
  ([T.copy_dom_zero](Cofinality-2.md#t-copy_dom_zero))
- **ascending copies** ([D.AscCrux](Cofinality-2.md#d-AscCrux)): each copy sinks deeper, so this
  is not a repetition of one shape. This is the real difficulty, and it is reduced to ArgDomCore
  below

### The host-free core ArgDomCore

> **Inside a single standard form, let two nodes carrying the same row-1 value $`w`$ sit in line
> at depths $`u`$ and $`u+e`$. Then the subtree $`B`$ of the deeper one is covered, in the
> column-lex order, by the $`e`$-deep shift of the subtree $`A`$ of the shallower one.**
> ([D.ArgDomCore](ArgDom.md#d-ArgDomCore); it holds by
> [T.argDomCore_holds](ArgDom-5.md#t-argDomCore_holds))

```
        depth u     (u, w)   <- the shallow one; its subtree A = A1 ++ (u+e,w) :: (B ++ A2)
                       |
        depth u+e   (u+e, w) <- the deep one, same label w; its subtree B
```

The side condition SpineOK says "every right-visible node between the two carries a label at
least $`w`$", that is, **the two are siblings with respect to row 1**.

**Draw: light up an ancestor-descendant pair with the same label inside a tree, and animate
superimposing the two subtrees to show that the deeper subtree fits inside the sunk copy of the
shallower one. This is the showpiece of chapter 5.**

Being "host-free" matters because in this form **the surrounding lists $`X`$ and $`Z`$
disappear**. The prefix invariance of Part II is what makes that erasure possible.

### The proof of ArgDomCore

Induction on $`\mathrm{ST\_PS}`$ ([T.argDomCoreOn_ST_PS](ArgDom-5.md#t-argDomCoreOn_ST_PS)). The
base case, the diagonal, is nearly trivial; the inductive step is the fourth branch of the
expansion, and it splits once more into three cases.

| case | situation | size |
|---|---|---|
| A1 | the two marked columns fall inside one and the same copy | 44 lines in Lean |
| B | the two columns lie outside the block | 185 lines in Lean |
| **A2** | **the two columns straddle a copy boundary** | **461 lines in Lean, 1519 in Isabelle** |

### The hard parts

- **[T.argDomCoreOn_bad_A2](ArgDom-4.md#t-argDomCoreOn_bad_A2)** — **the largest single lemma in
  the whole development**, 461 lines in Lean and 1519 in Isabelle. In the proof text it takes a
  page of its own. The difficulty is that when the two marked nodes straddle a copy boundary,
  one belongs to the $`k`$-th copy and the other to the $`k'`$-th, so **the two are lifted by
  different amounts**. The conclusion of ArgDomCore is a uniform shift "sink by $`e`$", so two
  fragments carrying different lifts have to be put back on a common host before they can be
  compared. That is done by splitting the list at a level
  ([T.arg_split](ArgDom-2.md#t-arg_split)) and using composition and inversion of shifts
  ([T.shiftl0_shiftr0](ArgDom-2.md#t-shiftl0_shiftr0),
  [T.shiftr0_comm](ArgDom-2.md#t-shiftr0_comm)) over and over.
  **In the video, colouring the two marks that straddle the boundary and showing that their
  copies sit at different depths already conveys why this is hard**
- **[T.copy_dom_zero](Cofinality-2.md#t-copy_dom_zero)** — 124 lines in Lean. The crux on the
  complete-copy side: taking $`n`$ large enough covers, proved over a block decomposition that
  is uniform in $`n`$ ([T.oper_bad_blocks_all](Cofinality.md#t-oper_bad_blocks_all))

---

## Part IV. The iterated inductive set $`W_u`$ (pillar 2)

### The main proposition

> **Every standard form lies in $`W_u`$ for some $`u`$**
> ([T.W_membership](Wset-4.md#t-W_membership))

And $`u`$ can be named explicitly: **the maximum row-1 value of the list** will do
([T.mem_W_maxr1](Wset-4.md#t-mem_W_maxr1)).

### What $`W_u`$ is

The least fixpoint of an operator $`A_u`$ ([D.Aop](Wset.md#d-Aop), [D.W](Wset.md#d-W)). A list
belongs to $`A_u(X)`$ in one of three ways.

```
(1) length at most 1 and the head carries label 0        -- the bottom
(2) the list is not an orphan, and M[n] is in X for all n -- one can descend by the
                                                            fundamental sequence
(3) for some m < u the list is a "row-1 orphan", and
    graft(M, z) is in X for every z in W_m that is anchored at depth 0
                                                         -- one can graft from a lower level
```

**Draw: (2) is "cutting a head always lands on something already known", (3) is "grafting a
forest from a lower level onto the parentless end lands on something already known". Three boxes
in the hydra picture.**

Being a least fixpoint gives two principles.

```
(A1) A_u(W_u) = W_u             the fixpoint equation        T.A1
(A2) A_u(Y) subset Y ==> W_u subset Y   the induction principle   T.A2
```

The definition of $`W_u`$ refers to the $`W_m`$ of smaller levels, so a recursion on $`u`$ and a
least fixpoint at each level are nested. That is what "iterated inductive" means.

### The line of the proof

1. Every list belongs to $`W^{*}`$ ([T.mem_Wstar](Wset-4.md#t-mem_Wstar)), where
   $`W^{*} = \{R \mid \text{if every element of } R \text{ has positive depth, then } (0,v) :: R \in W_v \text{ for every } v\}`$
2. For that, prove $`A_u(W^{*}) \subseteq W^{*}`$ ([T.Wstar_closed](Wset-4.md#t-Wstar_closed))
   and apply (A2)
3. Taking the level from a bound on row 1 gives the membership
   ([T.mem_W_of_bound](Wset-4.md#t-mem_W_of_bound))

### The hard parts

- **[T.Wstar_closed](Wset-4.md#t-Wstar_closed)** — 104 lines in Lean, 489 in Isabelle. For each
  of the three branches of $`A_u`$, one shows that the list with a root $`(0,v)`$ put in front
  lies in $`W_v`$. Branch (2) needs the expansion of the list with the root to be the expansion
  of the original list with the root put back in front
- **[T.oper_cons_nat](Wset-3.md#t-oper_cons_nat)** — 94 lines in Lean, 497 in Isabelle. This is
  the lemma that says "putting a head in front commutes with the expansion". One extra head
  shifts every index by one, so the parent relation, the ancestor relation and the search row
  all have to be tracked through that shift (the group from
  [T.entry_cons](Wset-3.md#t-entry_cons) to [T.nextR_cons_last](Wset-3.md#t-nextR_cons_last) is
  the toolkit for exactly that)
- **The tower $`\mathrm{tow}`$** ([D.tow](Wset-3.md#d-tow)) — the list obtained by grafting $`k`$
  times: $`t_0 = ()`$ and $`t_{k+1} = (0,v) :: \mathrm{graft}(R, t_k)`$.
  **This is a hydra grafted into itself over and over, so it is the easiest thing in the whole
  proof to animate: what plays the role of $`\Omega`$ swallowing the forests of the lower levels
  without end**

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

Branch (2) of the induction for $`W_u`$ is "descend by the fundamental sequence", and cofinality
says "anything smaller is covered by the fundamental sequence". The two mesh exactly.
**This is the keystone of the whole proof and the closing scene of the video.**

---

## The hard parts at a glance

Line counts are a proxy for difficulty. They are measured independently in the two
formalizations, so an entry that is large in both is genuinely hard.

| lemma | what is hard | Lean | Isabelle |
|---|---|---:|---:|
| [T.argDomCoreOn_bad_A2](ArgDom-4.md#t-argDomCoreOn_bad_A2) | the marks straddle a copy boundary, so the two lifts differ | 461 | 1519 |
| [T.argDomCoreOn_bad_B](ArgDom-3.md#t-argDomCoreOn_bad_B) | the marks lie outside the block | 185 | 613 |
| [T.blockok_oper](Seqlex-2.md#t-blockok_oper) | the adjacent-step bound survives the seams between copies | 179 | 365 |
| [T.cnf_ctx_cong](Cnf-2.md#t-cnf_ctx_cong) | the translation is not compositional for concatenation | 160 | 174 |
| [T.copy_dom_zero](Cofinality-2.md#t-copy_dom_zero) | the crux on the complete-copy side | 124 | 325 |
| [T.r1ok_copyExp](Column-2.md#t-r1ok_copyExp) | index arithmetic for parents across copies | 118 | 452 |
| [T.cnf_oper_i1eq1](Cnf-3.md#t-cnf_oper_i1eq1) | the nested tower of shifts | 108 | 259 |
| [T.Wstar_closed](Wset-4.md#t-Wstar_closed) | the list with a root added lands in the lower level | 104 | 489 |
| [T.oper_cons_nat](Wset-3.md#t-oper_cons_nat) | the index shift caused by one extra head | 94 | 497 |
| [T.crux_zero](Cofinality-2.md#t-crux_zero) | the crux of the complete-copy branch | 92 | 297 |

The difficulties are of two kinds.

- **Conceptual** — [T.cnf_ctx_cong](Cnf-2.md#t-cnf_ctx_cong) (the translation is not
  compositional) and [T.argDomCoreOn_bad_A2](ArgDom-4.md#t-argDomCoreOn_bad_A2) (the shift is
  not uniform). The obstacle can be put into words, so it is worth explaining in the video
- **Sheer length** — the index calculations. Following one node through the picture is enough;
  there is no need to follow them all

---

## A suggested order for the video

1. **The hydra dictionary** (section 0) — that lists and forests are the same thing, and that
   the expansion cuts a head. Spending time here means everything after it can be followed in
   pictures
2. **The overall design** — the goal and the two pillars, on one slide
3. **Part I** — comparing trees and comparing lists give the same answer; the stage moves to
   lists
4. **Part II** — the shape of a standard form. Emphasize prefix invariance (adding on the left
   changes nothing on the right). Do not enumerate the small lemmas
5. **Part III** — cofinality. Show the staircase of reductions on one slide, then spend the time
   on the picture for ArgDomCore (the same-label ancestor and descendant, and the sunk subtree)
6. **Part IV** — the three branches of $`W_u`$, and the tower. The grafting animation
7. **Part V** — the two pillars mesh and well-foundedness comes out

Part II has many lemmas, but **in the video only its three main propositions (cnf, prefix
invariance, r1ok and z0ok) need to be shown; the proofs can be skipped**. The time is better
spent on the order isomorphism of Part I, ArgDomCore in Part III, and the tower in Part IV.
