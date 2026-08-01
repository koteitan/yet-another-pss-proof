[日本語](README-ja.md)

# yet-another-pss-proof

Version: **v1.3.4**

An independent proof that the **pair sequence system** (PSS, the 2-rowed Bashicu matrix
system) terminates, together with its formalization in Lean 4 / Mathlib and in
Isabelle/HOL.

PSS was devised by Bashicu, and its termination was first proved by P進大好きbot using
Buchholz's collapsing functions $\psi$. This repository gives a **different proof**: pair
sequences are translated into a three-branch tree notation $p_a(b)+c$ of our own, and
termination is derived on that notation.

The termination theorem is complete: no hypotheses and no `sorry`.
`#print axioms YAPSS.PSS_terminates_unconditional` reports
`[propext, Classical.choice, Quot.sound]`, and `lake build` is green over the whole
project. No ordinals occur anywhere in the route, and this is checked mechanically
rather than asserted: after `import Final` the constant `Ordinal` does not exist in
the Lean environment at all, and no Mathlib ordinal or cardinal module is in the
import closure.

The same proof is formalized a second time in Isabelle/HOL, in `isabelle/`: the same
eleven modules, the same definitions and theorems in the same order, proved again over
plain `HOL` with no `sorry`.

The proof-theoretic strength of PSS is believed to be $\psi_0(\psi_\omega(0))$
(the Buchholz ordinal), which corresponds to taking the subscript $a$ of $p_a(b)$ to
range over the natural numbers.

## The proof

[`lean/README.md`](lean/README.md)

## The graph

[`lean/graph/index.html`](lean/graph/index.html) — the 440 definitions and theorems as nodes,
the 2360 citations as arrows. GitHub serves an `.html` file as source, so open it from a
local copy of the repository.

## Build

```sh
cd lean && lake build
```

Lean 4 with Mathlib `v4.30.0`.

```sh
cd isabelle && isabelle build -d . YAPSS
```

Isabelle2025-2.

## Repository layout

```
lean/                 the Lean 4 / Mathlib formalization
  README.md           index of the 11 modules, in dependency order
  requirement.md      editing policy for lean/*.md
  Pss.lean/.md        the pair sequence system itself
  Term.lean/.md       the notation p_a(b)+c, the order, the translation
  Decrease.lean/.md   every expansion step strictly decreases the measure
  Reduction.lean/.md  termination reduced to well-foundedness
  Cnf.lean/.md        the Cantor normal form condition and the copy decomposition
  Seqlex.lean/.md     the translation is an order isomorphism onto the column-lex order
  Column.lean/.md     prefix invariance and the positional invariants of standard forms
  Cofinality.lean/.md Bachmann cofinality
  ArgDom.lean/.md     its host-free core
  Wset.lean/.md       the iterated inductive set W_u
  Final.lean/.md      the main theorems
  lakefile.toml       the eleven modules as roots, in dependency order
  graph/              index.html — the reference graph, and what builds it
  memo/               verification code that is not part of the proof
  tools/              DeadCode.lean — declarations no proof term reaches
isabelle/             the Isabelle/HOL formalization of the same proof
  ROOT                the session YAPSS, the eleven theories in dependency order
  Pss.thy … Final.thy one theory per lean/ module, same name, same declaration order
tools/                the executable PSS model and the probes that check a statement
                      against it before it is formalized
task.md               progress tree
```

## Reference

- Bashicu, "[BASIC 言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=15603&useskin=oasis)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) user blog, 2015.8.21. (the first definition of the pair sequence system, in pseudo-BASIC)
- koteitan, "[バシク行列の亜種ルールの分類](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E4%BA%9C%E7%A8%AE%E3%83%AB%E3%83%BC%E3%83%AB%E3%81%AE%E5%88%86%E9%A1%9E)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) user blog, 2018.6.2. (classification of Bashicu matrix rule variants)
- P進大好きbot, "[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) user blog, 2018.11.11. (the first termination proof; the definition of PSS used here follows it)
- W. Buchholz, "[A new system of proof-theoretic ordinal functions](https://www.sciencedirect.com/science/article/pii/0168007286900527)", Annals of Pure and Applied Logic, Volume 32, 1986, pp. 195–207. (the collapsing functions $\psi_v$ and the notation system $\mathrm{OT}$)
- W. Buchholz, "[An independence result for $(\Pi^1_1\text{-}\mathrm{CA})+\mathrm{BI}$](https://www.sciencedirect.com/science/article/pii/0168007287900780)", Annals of Pure and Applied Logic, Volume 33, 1987, pp. 131–155. (§2: the iterated inductive sets $W_v$ and the **syntactic** well-foundedness proof for $\mathrm{OT}$ — the method transplanted here in `Wset.lean` and `Cofinality.lean`)
