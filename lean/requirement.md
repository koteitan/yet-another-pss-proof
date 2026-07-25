[← README](README.md) | [English](requirement.md) | [Japanese](requirement-ja.md)

# Editing policy for `lean/*.md`

The **human-readable body of the proof**, in one-to-one correspondence with the formal proof
in `lean/*.lean`, is written in `lean/*.md`. `lean/Foo.lean` ↔ `lean/Foo.md`. Markdown + MathJax. The language is English.

---

## 1. Shape of a file

### 1.1 The head of a file

The first line is nothing but a back link to [`README.md`](README.md).

```markdown
[← README](README.md)
```

In a file that has been split (§1.4), a list of the parts follows. The current part is set in bold and is not a link.

```markdown
[← README](README.md) | Wset **1** [2](Wset-2.md) [3](Wset-3.md) [4](Wset-4.md)
```

**Nothing else is placed at the head of a file.** No summary of the chapter, no table of notation, no count of the declarations, no heading such as "this chapter consists of three parts". The reader starts from the first proposition.

### 1.2 The body

Propositions and definitions are arranged in the order in which they occur in `lean/Foo.lean`. No other running text is placed there.

### 1.3 Write nothing that is not a proof

Design decisions, relations to other routes, history, implementation circumstances and numbers from model checking are written **neither in the md nor in `lean/*.lean`**, because they are not proofs.

Lean code that one wants to keep for verification (such as an `example` that confirms a definition is as intended) is placed in `lean/memo/*.lean`. That code is not part of the proof, so no `lean/*.md` is created for it.

### 1.4 Amount of math in one file

**Keep the math source of one file within 20000 characters.**

Once the total amount of math on one page exceeds a certain budget, GitHub turns **every formula after that point into `Unable to render expression`**. In measurements, 1200 small formulas (6096 characters in total) were all rendered, whereas formulas of 140 characters were cut off at the 181st (25956 characters in total), and `Cnf.md` at the 804th (28588 characters in total). This is a budget on **rendering cost** rather than on the number of formulas, and if it is a time budget then the boundary moves with the reader's machine, so we take 20000 with a margin of safety.

A module that exceeds this is split at a declaration boundary, and the parts are named `Wset.md` / `Wset-2.md` / `Wset-3.md` … . The split preserves the one-to-one correspondence between the Lean declarations and the sections (§6.6). A citation of a proposition across parts carries the file name, as in `[T.foo](Wset-3.md#t-foo)`. The link for a symbol defined in another file (§3.3) is attached **per part**, at the one place where that symbol first occurs in that part.

The split, and the rewriting of the links that comes with it, is carried out by `tools/split_md.py`.

```sh
python3 tools/split_md.py --dry-run   # proposed split
python3 tools/split_md.py             # run it
```

---

## 2. Format of propositions and definitions

### 2.1 Theorems

```markdown
<a id="t-stps_len_pos"></a>
## Theorem: standard forms are non-empty (T.stps_len_pos)

### Theorem

If $`M \in \mathrm{ST\_PS}`$ then $`0 \lt \lvert M\rvert`$.

### Proof

(the body of the proof)
```

### 2.2 Definitions

A definition carries no subheadings.

```markdown
<a id="d-Rnf"></a>
## Definition: the order on normal forms (D.Rnf)

$`v \mathbin{R_{\mathrm{NF}}} u :\iff v \prec u \wedge u \in \mathrm{NF} \wedge v \in \mathrm{NF}`$.
```

### 2.3 Identifiers and anchors

For `<name>`, the declaration name in `lean/*.lean` is used verbatim (`stps_len_pos`, `Rnf`, and so on). The namespace `YAPSS.` is not prefixed.

An **invisible anchor** is placed immediately before the heading. Its name is `t-<name>` / `d-<name>`
(the identifier verbatim; the case is not changed either). Since a heading contains natural-language text and parentheses, the anchors that GitHub generates automatically cannot be relied upon.

---

## 3. How to cite

### 3.1 Using a proposition

**Always** cite by the label, and attach a hyperlink.

- Within the same file : `by [T.olt_trans](#t-olt_trans),`
- In another file      : `by [T.m_step_decreases](Decrease.md#t-m_step_decreases),`

**A reference without a link is forbidden**, such as "by the preceding lemma" or "as shown above".

### 3.2 Symbols defined in the same file

No hyperlink is attached to a symbol that the file itself defines. The reader has only to look inside the same file, and a link would be noise. When a definition is cited as a justification, it is called by the name of the symbol, as in "by the first clause of the definition of $`\prec`$ (D.olt)".

**The unit is the file, not the module.** Even inside one module, if the definition lies in another part
(§1.4) then that is another file, and a link is attached according to §3.3.

A citation of a proposition (a theorem) carries a link even within the same file (§3.1). **It is only definitions (symbols) whose links are dropped.**

### 3.3 Symbols defined in another file

Inside file A, a symbol defined in file B **may be used as it stands**. No remark such as
"$`\mathrm{ST\_PS}`$ is defined in [D.ST_PS](Pss.md#d-ST_PS)" is written.

Instead, **at exactly the one place where that symbol first occurs in file A**,
**a parenthesized link to its label is placed immediately after that formula**.

It is "in file A", not "in the module". The parts of a split (§1.4) are counted independently of one another. The reader may start from any part, so a symbol that occurs only in part 3 cannot be traced unless it is linked in part 3.

- ⭕️ `$`M \in \mathrm{PairSeq}`$ ([D.PairSeq](Pss.md#d-PairSeq))`
- ❌ `[$`M \in \mathrm{PairSeq}`$](Pss.md#d-PairSeq)`

**A formula itself must never be made into a link.** GitHub does not create math inside a link (§5.1). When one is already inside parentheses (inside a `(…)`), parentheses are not nested; a space separates them instead (`($`\prec`$ [D.olt](Term.md#d-olt))`).

From the second occurrence on, neither a link nor parentheses are attached, and the bare symbol is written. When a definition is cited as a justification, it is called by the name of the symbol just as in §3.2
("by branch (a) of the definition of $`M[n]`$ (D.oper)").

A reader who meets an unknown symbol can jump to its definition by going back to the first occurrence of that symbol inside the file.

---

## 4. How to write a proof

### 4.1 Do not summarize

**This is a proof.** "This can be shown by induction", "similarly", "obviously" will not do. Each step comes with enough justification for the reader to verify it independently.

The only exception is when writing it out **makes the text harder to read instead**.

### 4.2 Write induction as induction

Wherever induction is used, the following four items are written **explicitly**.

1. **What the induction is on** (a natural number, the length of a list, the structure of a term, a derivation of `ST_PS`, or well-founded induction on a well-founded relation)
2. **The induction predicate** (written as a formula, $`\Phi(t) :\equiv \dots`$)
3. The proof of the **base case**
4. The proof of the **inductive step** (with the **induction hypothesis** stated explicitly as a predicate, and with the place where it is used indicated)

### 4.3 Do not use undefined natural-language words

The natural language that may be used is limited to **words already defined in this repository** and **the standard vocabulary of mathematics** ("therefore", "contradiction", "case distinction", "unique", and the like).

- ❌ "this set is **closed** under expansion"
- ⭕️ "$`\forall M \in X,\ \forall n \ge 1,\ M[n] \in X`$ holds for $`X`$"

Whenever a word whose meaning is not uniquely determined is about to be used, **rewrite it as a formula on the spot**. "almost", "roughly", "nicely", "naturally" are forbidden in the same way.

### 4.4 Do not write the names of tactics

A computation that is left to `omega` / `simp` / `decide` on the Lean side is **written out as a formula** in the md. Do not write "by `omega`".

### 4.5 Do not write what the proof does not use

Propositions, symbols and files that are not used in the termination proof are not treated. Such things are deleted from the `lean` side as well (they remain in the history, so they can be recovered). No md is created for them either.

Unused declarations are detected by `lean/tools/DeadCode.lean`:

```sh
cd lean && lake env lean tools/DeadCode.lean
```

---

## 5. How to write formulas

Where Lean notation differs from mathematical notation, **the md uses the mathematical notation**.
`M⟦n⟧` is $`M[n]`$, `olt` is $`\prec`$, `sle` is $`\preceq_{\mathrm{lex}}`$.
Sequences are written with indices ($`M = (M_0,\dots,M_{X-1})`$, $`X = \lvert M\rvert`$).

### 5.1 How to write so that GitHub does not break it

GitHub renders math with KaTeX, and runs Markdown's escaping in front of it.
The following five points are observed. All of them are results measured on the real site.

- **Display math is written in a ```` ```math ```` fence, not as `$$ ... $$`.**
  The contents of `$$ ... $$` undergo the escaping, which collapses `\{` to `{` and `\,` to `,`.
  The contents of a code fence do not.
- **A ```` ```math ```` fence is always written from the beginning of a line. It must not be indented.**
  GitHub converts only a fence at the beginning of a line into `<math-renderer>`, and **a fence that is
  indented, for instance inside a bullet list, stays a `<pre lang="math">`**. That is, it is not
  rendered as math (measured on the real site: in one file the 60 fences at the beginning of a line were
  rendered, while the 47 indented ones were not). Moreover, since the client side picks it up again as
  `$$…$$` in the body text, `\tag` can turn into an error saying that it can only be used in display math.
  When display math is wanted inside a bullet list, abandon the list, make it a paragraph such as
  `**(a) In the case … .**`, and move the fence out to the beginning of a line.
- **The line separator is `\cr`, not `\\`.** When GitHub hands the math to the client it turns
  `\\` into `\\\` (in a ```` ```math ```` fence as well as in `$$`).
  As a result the line separators of `\begin{aligned}` are lost and one gets `Missing \end{aligned}`.
  `\cr` is passed through untouched and is interpreted as a line separator in `aligned`, `cases` and `array` alike.
- **Inline math is written as `` $`...`$ `` (a bare `$...$` is not used).**
  The contents of a bare `$...$` are escaped too: `\{x\}` becomes `{x}` and `\,` becomes `,`.
- **Inside inline math, `<` and `>` are not written directly; `\lt` and `\gt` are written instead.**
  In inline math, `<` arrives **doubly** escaped as `&amp;lt;`.
  Inside a ```` ```math ```` fence the escaping is single, so `<` may be left as it is.
- **Never write `$` inside math** (not inside `\text{...}`, nor inside `\tag{...}`).
  Since GitHub escapes `$` to `\$` even inside a fence, `\text{$x$}` arrives as
  `\text{\$x\$}` and KaTeX rejects math commands in text mode.
  The math is moved outside the `\text{}`.
- **Do not let inline math straddle a line break.** A long formula is put into a ```` ```math ```` fence.
- **Do not use `\hphantom` / `\phantom`.** GitHub runs KaTeX behind its own **macro allow-list**,
  and rejects the whole formula, saying `The following macros are not allowed: hphantom`.
  Plain KaTeX accepts them, so this shows up **neither in the local check nor in `check-github.js`**
  (the rejection happens inside the browser, so the delivered string looks sound).
  Their relatives `\vphantom` / `\smash`, the definition commands `\def` / `\newcommand` / `\let` / `\gdef`,
  and `\htmlClass` are of the same kind.
  To align columns, use the **second alignment point** `&&` of `\begin{aligned}`.
  ```` &\text{(cZ1)}\quad &&\ldots \cr &\text{(decr)}\quad &&\ldots ````
  A continuation line can be written as `& &&\qquad \ldots`.
- **Do not put math inside a link.** If one writes `[$`a+b`$](Foo.md#d-x)`, GitHub does not create a
  `<math-renderer>` inside the link. If that is the only formula on the line, it comes out as
  `$<code>a+b</code>$` and **does not look like math**. If another formula follows in the same paragraph,
  the opening `$` of that one is wrongly paired with it, producing a broken formula that swallows the `<a>`
  tag, hence **`Unable to render expression`**. Writing raw HTML `<a href=...>` and writing
  `$…$` come to the same thing (the result of measuring seven variants on the real site).
  The link is moved outside the math (§3.3).

### 5.2 Checking

```sh
node ~/.claude/skills/github-math-check/scripts/check-local.js lean    # before push
node ~/.claude/skills/github-math-check/scripts/check-github.js <URL>  # after push; this is the final verdict
```

That something renders locally does not mean that it renders on GitHub. **Always measure on the real site after pushing.**

Note that this GitHub-specific notation is not rendered by a standard MathJax viewer.
To view it locally, use the patched markdown-viewer (`~/code/markdown-viewer`).

---

## 6. Points of doubt when writing

### 6.1 Introducing notation

Since no table of notation is placed at the head of a file (§1.1), **a symbol is introduced inside the definition that first needs it**. For example `takeWhile` / `dropWhile` are fixed immediately before `D.translate` as

> $`\mathrm{tw}_a L`$ := (the maximal prefix of $`L`$, taken from its head, along which the first entry stays greater than $`a`$)

and used from there on. In a lemma that needs the version for a general predicate, that lemma states that
"here $`\mathrm{tw}_p`$ is written for a general predicate $`p`$".

### 6.2 Write nothing but the definition in a definition section

A consequence that follows from a definition is not written in the definition section. **If it is used, state it as a theorem** (there should be a declaration on the Lean side as well). **If it is not used, do not write it** (§4.5).

This cannot be detected mechanically. `lean/tools/DeadCode.lean` is a tool that traces the proof terms of Lean constants, and the running text of an md is not in that graph at all. It can only be found by reading.

### 6.3 What may be written in a definition section

What a recursive or an inductive definition **needs in order to be well defined** is part of the definition.

- Injectivity of the constructors of an `inductive` and the fact that their images are pairwise disjoint (Lean generates `noConfusion` / `inj` automatically)
- Minimality of an `inductive`, that is, its induction principle (Lean generates `rec` automatically)
- Termination of the recursion (whether Lean accepts it as structural recursion, or a `termination_by` / `decreasing_by` is written)

These exist in Lean, and the proofs that follow use them as justifications.

### 6.4 Anonymous `example`s

An anonymous `example` in Lean cannot be given a label, so it cannot be written in the md. If it is useful for verification, move it to `lean/memo/*.lean` (§1.3).

### 6.5 Exhaust the case distinction

For a $`3 \times 3`$ case distinction, write out all nine cases. It suffices to make a table and to give the justification of each entry in one line. Do not settle for "it suffices to exhaust the nine cases" (§4.1).

### 6.6 Verification

- A proposition written in the md must be **the same statement** as the corresponding Lean declaration.
  Do not rewrite it so as to drop or to strengthen a hypothesis.
- Check that each step of the proof corresponds to the proof on the Lean side.
- Check that the declarations of `lean/*.lean` and the headings of `lean/*.md` are in one-to-one correspondence.

---

## 7. Procedure for turning one file into md

1. **Read `lean/Foo.lean` through.**
2. List the declarations in order of occurrence.

   ```sh
   cd lean && python3 -c "
   import sys; sys.path.insert(0,'../tools')
   from prune_lean import blocks
   for k,a,b,n in blocks(open('Foo.lean').read().split('\n')):
       if k=='decl' and n: print(a+1, n)"
   ```

3. Write `lean/Foo.md` in that order.
4. If `lean/Foo.lean` contains descriptions that are not proofs (design decisions, history, implementation circumstances, numbers from model checking), **delete them from the Lean side** (§1.3). Check that the build passes.
5. Check it.

   ```sh
   node ~/.claude/skills/github-math-check/scripts/check-local.js lean/Foo.md
   grep -n '^[ ]\+```math' lean/Foo.md          # must be 0 (§5.1)
   ```

6. Check that the declarations and the headings are in one-to-one correspondence.

   ```sh
   cd lean && python3 -c "
   import re,sys; sys.path.insert(0,'../tools')
   from prune_lean import blocks
   d=[n for k,a,b,n in blocks(open('Foo.lean').read().split('\n')) if k=='decl' and n]
   a=re.findall(r'<a id=\"[td]-([^\"]+)\"></a>', open('Foo.md').read())
   print('missing',[x for x in d if x not in a],'extra',[x for x in a if x not in d])"
   ```

7. After pushing, check the rendering on the real site with `check-github.js` (§5.2).
