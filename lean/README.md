[← README](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Proof of PSS termination

Pair sequences carry an expansion operation $`M \Rightarrow N`$. What is proved here is that
**this operation always terminates**, that is, that no infinite expansion sequence starts from a
standard form.

The proof has three stages.

**Stage 1.** A pair sequence $`M`$ is mapped to a term $`\mathrm{tr}(M)`$ of the ternary-tree
notation $`p_a(b)+c`$. Terms are equipped with the subscript-first lexicographic order $`\prec`$.

**Stage 2.** One expansion step strictly decreases this measure: $`\mathrm{tr}(M[n]) \prec \mathrm{tr}(M)`$.
Hence expansion terminates as soon as $`\prec`$ is well-founded on the image of the standard forms.

**Stage 3.** That well-foundedness is proved **without ordinals**, and without any translation into
Buchholz's notation system. Only the following two ingredients are used.

- **Bachmann cofinality** — every standard form strictly below $`M`$ is bounded above by some
  term $`M[n]`$ of the fundamental sequence.
- **The iterated inductive set** $`W_u`$ — defined as a least fixpoint; by its induction principle,
  every standard form belongs to $`W_u`$.

Combining these two yields well-foundedness. This is the method of Buchholz (1987) §2, where the
well-foundedness of Buchholz's notation system $`\mathrm{OT}_B`$ is obtained **syntactically** from
the sets $`W_v`$ and the fundamental sequences, rather than from an evaluation into the ordinals.
The route above transplants that method directly to pair sequences.

## Structure of the proof

| | What is proved | Text |
|---|---|---|
| Definitions | pair sequences $`M`$, fundamental sequences $`M[n]`$, standard forms $`\mathrm{ST\_PS}`$, expansion $`M \Rightarrow N`$ | [Pair sequence system](Pss.md) |
| Stage 1 | the notation $`p_a(b)+c`$, the order $`\prec`$, the translation $`\mathrm{tr}`$ | [Three-branch notation](Term.md) |
| Stage 2 | decomposition into the branches of expansion, and $`\mathrm{tr}(M[n]) \prec \mathrm{tr}(M)`$ | [Decrease of the measure](Decrease.md) |
| | if $`\prec`$ is well-founded on the image of $`\mathrm{tr}`$, then expansion terminates | [Reduction to termination](Reduction.md) |
| Preliminaries | the Cantor normal form condition $`\mathrm{cnf}`$, and the copy decomposition $`\mathrm{sh}_d`$ / $`\mathrm{cp}_d`$ | [Cantor normal form condition](Cnf.md) [2](Cnf-2.md) [3](Cnf-3.md) |
| | that $`\mathrm{tr}`$ is an order isomorphism onto the column-lex order on the standard forms | [Column-lex order](Seqlex.md) [2](Seqlex-2.md) |
| | prefix invariance of the parent relation, and the positional invariants $`\mathrm{r1ok}`$ / $`\mathrm{z0ok}`$ | [Column invariants](Column.md) [2](Column-2.md) [3](Column-3.md) [4](Column-4.md) |
| Stage 3 | if $`N \prec M`$, then $`N \preceq M[n]`$ for some $`n`$ | [Bachmann cofinality](Cofinality.md) [2](Cofinality-2.md) [3](Cofinality-3.md) |
| | reducing cofinality to the host-free core $`\mathrm{ArgDomCore}`$, and proving that core | [The core of cofinality](ArgDom.md) [2](ArgDom-2.md) [3](ArgDom-3.md) [4](ArgDom-4.md) [5](ArgDom-5.md) |
| | the least fixpoint $`W_u`$ and its induction principle; that every standard form belongs to $`W_u`$ | [Iterated inductive set](Wset.md) [2](Wset-2.md) [3](Wset-3.md) [4](Wset-4.md) |
| Conclusion | well-foundedness of the expansion relation, and non-existence of infinite expansion sequences | [Main theorem](Final.md) |

The table can be read from top to bottom. Each section uses only what the preceding sections prove.

Sections with many formulas continue in a part 2 and beyond. GitHub stops rendering the formulas of
a page once their total exceeds a certain amount, so each file is cut before that point.

For the current state and the history of the proof see [`PROOF-STATUS.md`](PROOF-STATUS.md); for the
editorial policy of the text see [`requirement.md`](requirement.md).

## Correspondence with Lean

For each section `<module>.md` of the table above, **the formal proof is in the `<module>.lean` of
the same name**. For instance, the formal proof of [Bachmann cofinality](Cofinality.md) [2](Cofinality-2.md) [3](Cofinality-3.md) is
[`Cofinality.lean`](Cofinality.lean).

The two correspond one to one. In a heading of `<module>.md`

```
## Theorem: standard forms are non-empty (T.stps_len_pos)
## Definition: order on normal forms (D.Rnf)
```

what stands inside the parentheses is a declaration name of `<module>.lean` (the namespace
`YAPSS.` is omitted), and the order of the sections is the same as the order of the declarations in
`<module>.lean`. There is no proposition and no definition present on one side and absent on the
other.
