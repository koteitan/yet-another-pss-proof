# Buchholz §1 mechanization PLAN — proving `psi_proj`

Design/architecture document (NO Isabelle code here). Target:

```
psi_proj :  wf3 b  ⟹  psi (oV b) a = psi (oV (proj a b)) a
```

Builds on `psi_proj_design.md` 続89(16)(17)(18)(19). This file is the
lemma-by-lemma reconstruction of the **Buchholz 1986 §1 simultaneous transfinite
induction** that breaks the circularity *canonical-rep ↔ C-membership (1.9) ↔
injectivity (1.4)*, mapped onto OUR definitions (`psi.thy`, `otembed.thy`,
`collapsing.thy`, `necessity.thy`, `nrm.thy`).

Sources for the Buchholz reconstruction (Part 1):
- W. Buchholz, *A new system of proof-theoretic ordinal functions*, APAL 32
  (1986) 195–207. Original PDF: https://epub.ub.uni-muenchen.de/3841/1/3841.pdf
  (scanned image — not machine-readable; lemma numbering below follows the
  paper's standard citation as used throughout our `.thy` headers).
- cantors-attic, *Buchholz's ψ functions*:
  https://neugierde.github.io/cantors-attic/Buchholz's_%CF%88_functions
  (gives the closure definition with the generator side-condition `ξ∈C_μ(ξ)`).
- Googology Wiki, *Buchholz's function*:
  https://googology.fandom.com/wiki/Buchholz%27s_function

---

## PART 1 — Faithful reconstruction of Buchholz 1986 §1

### 1.0 The objects

Buchholz fixes, for each `ν ≤ ω`, a regular cardinal `Ω_ν` (`Ω_0 = 1`,
`Ω_ν = ℵ_ν` for `ν>0`). He defines simultaneously, by recursion on `α`, the
**closure set** `C_ν(α)` and the **collapsing value** `ψ_ν(α)`:

```
C_ν^0(α)     = Ω_ν
C_ν^{n+1}(α) = C_ν^n(α)
              ∪ { ξ+η      | ξ,η ∈ C_ν^n(α) }
              ∪ { ψ_μ(ξ)   | μ ≤ ω,  ξ ∈ α ∩ C_ν^n(α),  ξ ∈ C_μ(ξ) }   (*)
C_ν(α)       = ⋃_{n<ω} C_ν^n(α)
ψ_ν(α)       = min { γ : γ ∉ C_ν(α) }
```

The recursion is well-founded because `ψ_μ(ξ)` is only ever invoked for `ξ < α`,
so the value `ψ_ν(α)` depends only on `ψ_μ(ξ)` for `ξ < α`. (This is exactly our
`transrec` in `psi.thy:62`.)

**THE side-condition (\*) `ξ ∈ C_μ(ξ)`** is the canonicity condition Buchholz
puts on every generator. It says: only *canonical* arguments `ξ` are allowed to
generate. Buchholz remarks (the "Remark" cited in `psi.thy:50`) that one may
drop it without changing `C_ν(α)` — but proving that equivalence is itself part
of §1. **Our `Cstep` (`psi.thy:54-57`) OMITS (\*)** — it generates `ψ_μ(ξ)` for
*every* `ξ ∈ X ∩ α`. This is the single structural divergence we must reconcile
(see §1.6 below and Part 2 lemma group D).

### 1.1 The coefficient function `G` (= our `Gterm` on the term side)

Buchholz defines, for an ordinal `γ` in normal form, the finite set `G_u γ` of
its `≥u`-subscripted *sub-arguments*. On the ordinal side this is read off the
canonical (Cantor + ψ) normal form; on the term side it is the structural
`Gterm` of `otembed.thy:77`. The membership characterization (1.9 below) is
stated in terms of `G`.

### 1.2 The standard/normal-form term system `T` and canonical rep

Buchholz builds a term notation system `T` (closed terms over `0, +, ψ_μ`) and a
predicate "is in normal form". An ordinal term `ψ_ν(β)` is `=_{NF}` iff
`β ∈ C_ν(β)` (the argument is canonical). Each ordinal `< ψ_0(ε_{Ω_ω+1})` has a
**unique** normal-form term — the *canonical representation*. Existence +
uniqueness of canonical reps is the backbone result of §1.

### 1.3 Lemma 1.2 (basic properties) — ALL ALREADY DONE in `psi.thy`

- `Ω_ν ⊆ C_ν(α)`              → `Om_subset_Cset`
- `Ω_ν ≤ ψ_ν(α)`             → `Om_le_psi`
- `ψ_ν(α)` additive principal → `psi_addprinc`, `psi_add_principal`
- `ψ_ν(α) < Ω_{ν+1}`          → `psi_lt_Om_Suc`
- weak monotonicity in α      → `psi_mono_arg`

### 1.4 Lemma 1.3 (strict monotonicity) — DONE (conditionally)

`α < β ∧ α ∈ C_ν(α) ⟹ ψ_ν(α) < ψ_ν(β)`  →  `psi_strict_mono_arg`
(needs the canonicity hypothesis `α ∈ C_ν(α)` — exactly Buchholz's).

### 1.5 Lemma 1.4 (injectivity / NF characterization)

Buchholz 1.4(a): `ψ_ν(α) = ψ_μ(β)` with `α,β` canonical ⟹ `ν=μ ∧ α=β`.
→ DONE as `psi_inj_canonical` (`necessity.thy:134`), built from
`psi_inj_subscript` + `psi_inj_arg_canonical`.

Buchholz 1.4(b) — **the canonical-representation existence step**: every
`γ ∈ C_ν(α)` that is a ψ-value `ψ_μ(ξ)` equals `ψ_μ(ξ°)` for a *canonical*
`ξ°` (`ξ° ∈ C_μ(ξ°)`). I.e. non-canonical generators are *redundant*: the
collapse identifies `ψ_μ(ξ) = ψ_μ(ξ°)`. **This is the missing piece** and the
exact place where our omitted side-condition (\*) matters: with (\*), only
canonical generators ever entered `C`; without (\*), we must *prove* the
non-canonical ones add nothing (group D).

### 1.6 Lemma 1.9 (the C-membership characterization = necessity)

```
γ ∈ C_ν(α)  ⟺  every coefficient (G-sub-argument) of γ is < α.
```
The ⟸ direction (sufficiency) is our `C_build` (`otembed.thy:206`). The ⟹
direction (**necessity**) is the hard one and what `psi_proj` ultimately needs:
if `ψ_μ(ξ)` (a leading generator of `γ`) lies in `C_ν(α)` then `ξ < α`.

The necessity proof's **generator case** runs: `γ = ψ_μ(ξ) ∈ C_ν(α)` means
`ξ ∈ α ∩ C_ν(...)` *for the canonical witness producing it* — but to read off
`ξ < α` we must know the producing argument is the *canonical* `ξ`, i.e. we need
1.4(b). Hence the **circularity**:

```
   1.9 necessity ── needs ──▶ 1.4(b) canonical witness
        ▲                              │
        └────── needs ◀── canonical-rep existence (uses 1.9 to bound coeffs)
```

### 1.7 How Buchholz BREAKS the circularity — the simultaneous induction

Buchholz proves, **simultaneously by transfinite induction on the ordinal `α`**
(equivalently, our `Cset` is a union over the closure rank `n` = the `Citer`
index, so the inner induction is on `n`), the conjunction:

> **P(α)** ≡  for all `ν`:
>   (i) [canonical-rep / 1.4b] every `ψ`-generator that fires into `C_ν(α)`
>       may be taken with a canonical argument `< α`; AND
>   (ii) [1.9 necessity, restricted to `< α` data] `γ ∈ C_ν(α)` ⟹ all
>        coefficients of `γ` are `< α`; AND
>   (iii) [1.3/1.4a strictness+injectivity restricted to `< α`] used inside the
>        step to identify collapsed values.

The key is that all three are stated **relative to arguments `< α`**, so the IH
"P holds for all `α' < α`" supplies (i)–(iii) for the *generators* `ψ_μ(ξ)`
(`ξ < α`) that build `C_ν(α)`, before P(α) itself is concluded. Concretely:

- the **closure-rank `n`** is the inner induction (finite): membership in
  `C_ν(α)` is "appeared at some stage `n`"; each new element at stage `n+1` is a
  sum or a generator `ψ_μ(ξ)` with `ξ < α`;
- for a generator, `ξ < α` so the **outer IH P(ξ)/P at `<α`** gives the
  canonical witness `ξ°` (1.4b at `ξ`) and injectivity (1.4a at `ξ`), letting us
  rewrite `ψ_μ(ξ) = ψ_μ(ξ°)` and conclude its coefficients are `< α`.

So the induction **measure is the pair `(α, n)` ordered lexicographically**:
outer transfinite on `α`, inner finite on the closure rank `n` (= `Citer`
index). The conjunction `(i)∧(ii)∧(iii)` is what is carried.

This is the irreducible core flagged in `psi_proj_design.md` 続89(17).

---

## PART 2 — Concrete Isabelle lemma-by-lemma plan onto OUR definitions

Notation reminder (`psi.thy`): `Cv α v ≡ Cset (λξ∈elts α. psi ξ) α v`
(abbrev from `collapsing.thy:17`). `acanon a δ ≡ δ ∈ elts (Cv δ a)`
(`necessity.thy:48`). All `ψ` are `psi α v` (arg-first). `oV` from `otembed.thy`.

We avoid duplicating proven assets. Below, **[DONE]** marks existing lemmas,
**[NEW]** marks lemmas to add.

The plan offers **two routes** for the canonicity gap. We commit to **Route D-eq**
(prove full-gen `Cset` = canonical-gen `Cset`) as the primary, because it lets us
reuse `collapse_grow`/`Cset_grow_eq` machinery and keeps `psi` definitionally
fixed; **Route D-coef** (define a coefficient function on V and prove 1.9
directly) is the fallback, sketched in §D'.

### Group A — Per-maxo-step reduction (the scaffolding; mostly mechanical)

**A1 [NEW] `psi_proj_step`** (the irreducible core, isolated):
```
assumes wf3 b,
        bad = {g ∈ Gterm a b. ¬ olt g b},  bad ≠ {},
        m = (the olt-maximum of bad)
shows   psi (oV b) a = psi (oV m) a
```
Dependencies: B-group (oV b ≤ oV m and oV b non-canonical), C-group (collapse).
Proof sketch: from C2 get `Cv (oV b) a = Cv (oV m) a`, then `psi_eq_of_Cset_eq`
(`collapsing.thy:104`). Feasibility: trivial *given* B+C.

**A2 [NEW] `psi_proj`** (final assembly):
```
wf3 b ⟹ psi (oV b) a = psi (oV (proj a b)) a
```
Proof: `proj.induct` (the induction principle generated by `nrm.thy:43`). Base
case `proj_id` (`nrm.thy:64`): bad empty, both sides equal. Step case
`proj_rec` (`nrm.thy:68`): IH gives `psi(oV m) a = psi(oV(proj a m)) a`; compose
with A1. Need `wf3 m` (have `Gterm_wf3`, `nrm.thy:74`) and `m ∈ Gterm a b`
(have `maxo_hdtl_in` + `set_Glist`). Feasibility: mechanical, ~40 lines.
This realizes 続89(16). **No risk** once A1 holds.

Bridge lemma needed by A1/A2 to talk about "the maxo as an element with the
right properties":

**A0 [NEW] `maxo_bad_props`**: package `nrm.thy`'s `filter (¬olt · b) (Glist a b)`
nonempty ⟹ `m := maxo(hd)(tl) ∈ Gterm a b`, `¬ olt m b`, and (with `wf3 b`)
`wf3 m`. Pure restatement of existing `nrm.thy` lemmas. Trivial.

### Group B — Non-canonicity of `oV b` (drives the collapse)

**B1 [NEW] `bad_imp_oV_ge`** (the clean empirical fact 続89(9), 72942/72942):
```
wf3 b ⟹ g ∈ Gterm a b ⟹ ¬ olt g b ⟹ oV b ≤ oV g
```
Proof: contrapositive of `oV_order_pres` (`otembed.thy:347`). If `oV g < oV b`
then... no — careful: `oV_order_pres` gives `olt v u ⟹ oV v < oV u` only one
direction. We need: `¬ olt g b` with `g,b` wf3 ⟹ `¬(oV g < oV b)`. Use
`olt`-totality (`olt_total`) + `oV_order_pres`: `¬olt g b` ⟹ `olt b g ∨ g=b`;
if `olt b g` then `oV b < oV g` (so `≤`); if `g=b` then `=`. Need `wf3 g` via
`Gterm_wf3`. Feasibility: easy, ~10 lines. **Risk: LOW.** Sanity: matches the
72942/72942 empirical fact — TRUE as stated.

**B2 [NEW] `bad_imp_not_acanon`** (`oV b` is non-canonical at level `a`):
```
wf3 b ⟹ g ∈ Gterm a b ⟹ ¬ olt g b ⟹ ¬ acanon a (oV b)
```
i.e. `oV b ∉ elts (Cv (oV b) a)`. **This is the heart of the necessity side and
the hardest non-core lemma.** Intuition: `oV b` has a coefficient `ψ_a(oV g)`
(or `oV g`) that is `≥ oV b` (B1), so `oV b` cannot lie in its own closure
`C_a(oV b)` whose generators only fire on arguments `< oV b`. **This is exactly
where 1.9 necessity is required** (続89(17),(11)): to turn "a coefficient is
`≥ oV b`" into "`oV b ∉ C_a(oV b)`" we need the converse of `C_build`. See
group D. **Risk: this is the circularity locus.** Flagged as a sub-case of the
single hardest lemma (the simultaneous induction D1).

  - Note the `g`-vs-`m` subtlety from 続89(9): the *per-step for arbitrary g*
    `ψ_a(oV b)=ψ_a(oV g)` is FALSE (64262/72942). B2 must NOT claim that; it only
    claims non-canonicity of `oV b`, which is compatible (collapse to the
    *maxo*, not to an arbitrary g). The collapse target (group C) uses `m`=maxo.

### Group C — The argument-side collapse `Cv(oV b) a = Cv(oV m) a`

**C1 [NEW] `gap_non_acanon`** (every ordinal in `[oV b, oV m)` is non-canonical
at `a`, i.e. ∉ `Cv (oV b) a`):
```
assumes (oV b non-canonical at a, from B2),  oV b ≤ oV m,
        proj-fixpoint canonicity at the far end (oV m's side via proj_canonical)
shows   ∀ξ. ξ ∈ elts (oV m) ⟹ ξ ∉ elts (oV b) ⟹ ξ ∉ elts (Cv (oV b) a)
```
This is the hypothesis shape demanded by `collapse_grow` / `Cset_grow_eq`
(`collapsing.thy:71,114`). Proof sketch: the only ordinals between `oV b` and
`oV m` that could be *canonical* would have to re-enter `C_a(oV b)`; but they all
contain the offending coefficient `≥ oV b`, so by 1.9-necessity they are absent.
**Risk: HIGH** — this is the second projection of the core (group D). Depends on
D1.

**C2 [NEW] `Cv_collapse_b_m`**:
```
psi (oV b) a — argument-collapses to — psi (oV m) a
i.e.  elts (Cv (oV b) a) = elts (Cv (oV m) a)
```
Proof: `Cset_grow_eq` (`collapsing.thy:71`) with gap hypothesis C1 and
`elts (oV b) ⊆ elts (oV m)` (from B1 `oV b ≤ oV m` + `Ord` + `less_eq_V_def`).
Feasibility: mechanical *given* C1. This is the direct input to A1 via
`psi_eq_of_Cset_eq`. **Risk: LOW given C1.**

  ⚠ Sanity check vs `collapse_grow`'s actual signature: `collapse_grow` already
  yields `psi α v = psi β v` directly from the gap+subset hypotheses, so A1 can
  call `collapse_grow` instead of going through `Cset_grow_eq`+`psi_eq_of_Cset_eq`.
  Prefer `collapse_grow` — fewer steps. C2 then becomes a one-liner wrapper or is
  inlined into A1.

### Group D — Breaking the circularity (THE CORE): simultaneous induction

This is the Buchholz §1 machine (Part 1 §1.7). Everything above (B2, C1) reduces
to **1.9 necessity**, whose generator case needs **1.4(b) canonical witnesses**,
which needs **canonical-rep existence** — all proved together.

#### Route D-eq (PRIMARY): full-gen `Cset` = canonical-gen `Cset`

Define a *canonical-generator* closure that includes Buchholz's side-condition
(\*), and prove it equals our `Cset`. Then 1.9 necessity transfers from the
canonical version (where generators are canonical by construction, so 1.4a
applies directly).

**D-eq-0 [NEW] `Cstep_c` / `Cset_c`** (canonical-gen variants): same as
`Cstep`/`Cset` (`psi.thy:54,59`) but the generator image restricted to
`ξ ∈ elts X ∩ elts α ∩ {ξ. acanon u ξ}` (the (\*) condition; note acanon's
subscript is the generator's `u`, matching Buchholz `ξ ∈ C_μ(ξ)`). Definitions +
the analogues of `elts_Cstep`, `Cset_mem_iff`, monotonicity. Mechanical
boilerplate (~mirror of `psi.thy:110-235`), ~150 lines. **Risk: LOW but tedious.**

**D-eq-1 [NEW] `Cset_eq_Cset_c`** (Buchholz's Remark, the redundancy of
non-canonical generators):
```
elts (Cv α v) = elts (Cset_c (λξ∈elts α. psi ξ) α v)
```
`⊇` is `Cset_mono_param`-style (canonical-gen ⊆ full-gen), trivial. `⊆` is the
content: a full-gen step `ψ_u(ξ)` with `ξ` non-canonical must already be present
via a canonical generator. Proof: induction on the closure rank `n` (`Citer`
index) — the inner induction of §1.7 — *simultaneously with* the statement
"non-canonical `ξ` produces `ψ_u(ξ) = ψ_u(ξ°)` with `ξ°` canonical, `ξ° < ξ ≤
…`". The canonical witness `ξ°` comes from **D1** at the smaller argument.
**This IS the simultaneous-induction lemma.** See D1.

**D1 [NEW, THE CORE] `section1_simult`** — the simultaneous transfinite
induction. Statement (the carried conjunction, Part 1 §1.7), by
`(α, n)` lexicographic = transfinite on `α` (`Ord_induct` / well-founded
`VWF`-style) with inner `Citer`-rank `n` induction:
```
Ord α ⟹
  (∀ν. ∀x ∈ elts (Citer (λξ∈elts α. psi ξ) α ν n).
        ⟦ canonical-witness: x is a ψ-value ψ_μ(ξ) ⟹
            ∃ξ°. acanon μ ξ° ∧ ξ° < α ∧ psi ξ μ = psi ξ° μ ⟧          (i = 1.4b)
   ∧  ⟦ necessity: every G-coefficient of x is < α ⟧                  (ii = 1.9)
   ∧  ⟦ (used internally) injectivity/strictness on args < α ⟧)       (iii = 1.4a)
```
**Induction structure** (the answer to "induct on what"):
- **OUTER**: transfinite on `α` via `Ord_induct` (well-founded on `Ord`). The IH
  gives the full conjunction for every `α' < α` — crucially for the generator
  arguments `ξ < α`.
- **INNER**: finite induction on the `Citer` rank `n` (the union index from
  `Cset_mem_iff`, `psi.thy:162`). Base `n=0`: `x ∈ Om v`, no coefficients,
  trivial. Step `n+1`: `x` is old (IH on `n`), a sum (coefficients = union of
  parts' coefficients, IH on `n`), or a generator `ψ_μ(ξ)` with `ξ < α` and
  `ξ ∈ Citer … n`:
    * by INNER IH, `ξ`'s own coefficients are `< α` so `ξ ∈ C_μ(...)`-buildable;
    * by OUTER IH at `ξ (<α)`, get canonical witness `ξ°` (i) and injectivity
      (iii) ⟹ `ψ_μ(ξ) = ψ_μ(ξ°)`, `ξ°` canonical, `ξ° ≤ ξ < α` ⟹ its single
      coefficient `< α` (ii). 
**This single lemma yields D-eq-1, B2, C1** as corollaries (their necessity
content is exactly (ii); B2 is the contrapositive at `α = oV b` using B1).
**Risk: VERY HIGH — this is THE single hardest lemma**, multi-session,
the irreducible Buchholz §1 core. Everything else is scaffolding.

  Sub-risks within D1:
  - Defining "G-coefficient of an ordinal `x`" purely on V (no term side) is
    itself nontrivial — Buchholz reads it off the canonical rep. **Mitigation**:
    state (ii) not as "coefficients of x" but in the *generator-trace* form that
    the `Citer` induction naturally produces: "if `x` arose as `ψ_μ(ξ)` at some
    stage, then `ξ < α`". This is the form B2/C1 actually consume and avoids
    needing a standalone V-coefficient function. **Strongly recommended.**
  - The outer `Ord_induct` must thread `ν`/`v` universally (the conjunction is
    "∀ν"), and the canonical predicate `acanon μ` couples different subscripts;
    keep the statement schematic in the subscript.

**D2 [NEW] `oV_in_Cv_iff_coeff`** (1.9 specialized to term values, the consumable
form): from D1(ii) in generator-trace form,
```
wf3 t ⟹ oV t ∈ elts (Cv α v) ⟹ ∀x ∈ Gterm v t. oV x < α
```
the converse of `C_build`. Proof: `Cset_mem_iff` gives a `Citer` stage; apply D1
generator-trace necessity; bridge ordinal generators back to `Gterm` via the
`oV (P a b c) = psi (oV b) a + oV c` structure (`otembed.thy:18`) and
`indecomposable_psi` (`necessity.thy:89`) to split sums (this part is the (A)
"leading component extraction" of `necessity.thy` header). **Risk: MEDIUM**
(sum-splitting is routine with `Cantor_NF`; the generator case is D1).

Then **B2** = D2 at `α := oV b`, `t := b`, `v := a`, contradiction with B1
(`oV b ≤ oV g` but D2 would force `oV g < oV b`). And **C1** = D2 applied across
the gap. Clean.

#### Route D-coef (FALLBACK): coefficient function on V + direct 1.9

If D-eq-0/D-eq-1 boilerplate proves too heavy, instead define
`coeffs :: nat ⇒ V ⇒ V set` directly on ordinals via `Cantor_NF` +
`indecomposable_psi` decomposition (`ψ_μ(ξ)` summands), and prove 1.9 necessity
`x ∈ Cv α v ⟹ ∀c ∈ coeffs v x. c < α` by the same `(α,n)` induction. Skips the
`Cset_c` duplication but pays for it in the `coeffs` well-definedness (needs the
canonical-rep uniqueness, i.e. 1.4 — same circularity, same D1). **Net: D1 is
unavoidable either way.** Recommend Route D-eq because `collapse_grow` and
`acanon` already exist.

### Group E — already-DONE assets to reuse (no work)

- `psi_eq_of_Cset_eq`, `Cset_succ_eq`, `collapse_succ`(1.6a), `Cset_grow_eq`,
  `collapse_grow` — `collapsing.thy`.
- `psi_inj_subscript`, `psi_inj_arg_canonical`, `psi_inj_canonical`(1.4a),
  `indecomposable_psi`, `indec_psi_mult*`, `acanon`/`acanon_of_lt_psi`/
  `psi_le_of_not_acanon` — `necessity.thy`.
- `C_build`(1.9 sufficiency), `Ccond_of_lt`, `oV_order_pres`(2.2c),
  `wf3_Gterm`, `Gterm_size` — `otembed.thy`.
- `proj_G`, `proj_wf3`, `proj_canonical`, `maxo_hdtl_in`, `set_Glist` — `nrm.thy`.

---

## PART 3 — Feasibility / risk table and FALSE-lemma sanity checks

| Lemma | Depends on | Risk | Notes |
|-------|-----------|------|-------|
| A0 maxo_bad_props | nrm.thy | trivial | restatement |
| A1 psi_proj_step | B1,B2,C2/collapse_grow | trivial given B,C | core wrapper |
| A2 psi_proj | A1, proj.induct | low | mechanical assembly (続89(16)) |
| B1 bad_imp_oV_ge | oV_order_pres, olt_total | LOW | TRUE (72942/72942 empirical) |
| B2 bad_imp_not_acanon | **D1/D2** | **HIGH (=core)** | the necessity locus |
| C1 gap_non_acanon | **D1/D2** | **HIGH (=core)** | second projection of core |
| C2 Cv_collapse_b_m | C1, Cset_grow_eq | low given C1 | prefer collapse_grow |
| D-eq-0 Cstep_c/Cset_c | psi.thy boilerplate | LOW-tedious | ~150 lines mirror |
| D-eq-1 Cset_eq_Cset_c | **D1** | HIGH | Buchholz Remark; corollary of D1 |
| **D1 section1_simult** | Ord_induct, Citer, 1.4a, acanon | **VERY HIGH** | **THE single hardest; multi-session** |
| D2 oV_in_Cv_iff_coeff | D1, Cantor_NF, indecomposable_psi | MEDIUM | sum-splitting routine |

### THE single hardest lemma
**D1 `section1_simult`** — the simultaneous transfinite induction
(outer `Ord_induct` on `α`, inner finite induction on `Citer` rank `n`) carrying
canonical-witness (1.4b) ∧ necessity (1.9) ∧ injectivity-on-`<α` (1.4a). This is
the irreducible Buchholz §1 core identified in 続89(17); both this proof and
lean-yapss stall here. Everything else is scaffolding around it.

### Lemmas that might be FALSE as stated — sanity vs empirical facts in the design note

1. **⚠ ARBITRARY-`g` per-step is FALSE** (do NOT introduce it). 続89(9):
   `ψ_a(oV b)=ψ_a(oV g)` for arbitrary `g∈Gterm a b, ¬olt g b` is false
   (64262/72942). The plan never states this; A1/C use the **maxo** `m` only.
   Any temptation to prove B2/C1 via "collapse to each bad g" must be resisted.

2. **B1 is TRUE** as stated (`oV b ≤ oV g`, 72942/72942). Good.

3. **psi_proj (full proj, maxo discipline) is TRUE** (46033 principals, 0
   counterexamples, 続89(9)). A2's target is sound.

4. **⚠ Watch the direction of B2's necessity.** B2 claims `oV b ∉ C_a(oV b)`
   (non-canonical), NOT `oV b ∈` anything. It is consistent with B1
   (a coefficient `≥ oV b` blocks self-membership). If a future step accidentally
   tries to prove `oV b` *canonical* it would be FALSE. The whole point is
   non-canonicity. Keep the polarity.

5. **⚠ `oltRwF`/`omfree`/`cntbl`-style targets are ILL-FOUNDED** (MEMORY
   pss-wf-target-nneg): the WF target must stay in the nonneg-subscript fragment.
   `psi_proj` itself is a *value equality*, not a WF claim, so it is safe; but
   D1's "necessity" must be stated about coefficients/generators, never as a
   global descent on subscripts. Avoid any reformulation of D1 that quantifies a
   descending subscript chain.

6. **acanon auto-loop hazard** (続89(18)): never expose `acanon_def` /
   `Cset`/`Citer` unfoldings to `auto`/`simp` (1.5h spin incident). All of
   D-group must be **structured** proofs; `acanon` stays folded except in
   explicit single `unfolding` steps.

### Build discipline (carry-over, not part of the proof)
Use **isbman** only (never raw `isabelle build`); incremental rebuilds of the
PSI image after the first full build (続89(18)(19)). The plan adds to
`necessity.thy` (groups A,B,D2), a small `collapsing`/new file for D-eq (D-eq-0/1),
and `nrm.thy` is untouched except A2 may live near `proj`.

---

## Summary of the route

```
psi_proj  (A2)
  └─ psi_proj_step (A1)               [maxo step]
       ├─ B1 bad_imp_oV_ge            [DONE-ish, from oV_order_pres]   ✅ low
       ├─ collapse_grow               [DONE, collapsing.thy]           ✅
       ├─ C1 gap_non_acanon ──┐
       └─ B2 bad_imp_not_acanon ─┤
                                 └─▶ D2 oV_in_Cv_iff_coeff  (1.9 necessity, consumable)
                                       └─▶ D1 section1_simult  ★ THE CORE
                                             (simultaneous transfinite induction:
                                              1.4b canonical-rep + 1.9 + 1.4a,
                                              outer Ord_induct on α, inner Citer-rank n)
```
Build the scaffolding (A,B1,C2) first against a *sorried* D1/D2 to validate the
assembly compiles, then attack D1 (multi-session). D1 is the whole game.

---

## UPDATE 続89(21-29) — 実装の確定事項と route 訂正(2026-06-14)

今セッションで PART 2 の大部分を緑で実装し、route を訂正した。

### 緑で完成した部品(necessity.thy / collapsing.thy / nrm.thy, 全 sorry 無)
- **A2 psi_proj 実証明**(modulo 単一 sorry)・**A1 psi_proj_step 実証明**(psi_eq_of_not_mem 経由)・
  **B1 bad_imp_oV_ge**・**oV_le_proj**(proj は値を上げる)。
- **psi_eq_of_not_mem**(collapsing.thy): α≤β ∧ psi α v∉Cv β v ⟹ psi α v=psi β v。
  ★collapse_grow より弱仮定。A1 はこれで「単一非帰属」に還元。
- **indec_Cset_generator**: 閉包の indecomposable 元は generator(Citer 帰納・同時帰納不要)。
- **psi_in_Cset_same_sub_generator**: 同 subscript ψ値∈閉包 ⟹ generator 由来。
- **band_lt_psi**: Cv(δ)a の Om(Suc a)-band 内元 < psi δ a。
- **D-eq-0 完成**: Cstep_c/Cset_c + small_Cstep_c_gen/elts_Cstep_c/Cstep_c_subset_Cstep/
  Citer_c_subset_Citer/Cset_c_subset_Cset/Cset_c_mem_iff/Om_subset_Cset_c/
  **Cset_c_add_closed**/**Cset_c_gen_closed**。D-eq-1 の easy cases は全てこれで緑化可能。

### ★route 訂正(PART 2 の誤りを実装で発見)
1. **collapse_grow は A1 に使えない**(C1/C2 ルート破棄): A1 で collapse する ψ_a の引数
   oV b, oV m は band 外になり得る(値 psi(oV b)a だけが band 内)。gap [oV b,oV m) は
   clean でない。⟹ A1 は **psi_eq_of_not_mem による単一非帰属** psi(oV b)a∉Cv(oV m)a に還元
   (= **psi_proj_nonmem**, nrm.thy:166, 唯一の sorry)。これが正しい 1.9 necessity 形。
2. **A1⟺nonmem 完全同値**(psi_notin で逆も)。A1 実測真 6677/0 ⟹ nonmem 真(sorry 健全)。
3. **band_lt_psi は refutation 不可**(consistency のみ): ∈⟹< を言うだけ。

### ★★ D1 の本質 = 循環性、A2 と nonmem は同時帰納必須(最重要)
- nonmem を D-eq-1(Cset=Cset_c)で割るには、canonical ξ<oV m を oV(proj a b) と同一視する
  injectivity が要るが、それには **psi(oV(proj a b))a=psi(oV b)a = A2 自身**が要る。A2 は
  nonmem 依存。⟹ **A2 と nonmem は線形分離不能**。
- proj recursion は oV を**増やす**(A1: oV m≥oV b)ので oV b 下降帰納も効かない。
- ⟹ **D1 = A2+nonmem(+1.4b canonical-rep 存在)を Buchholz の (α,n)同時超限帰納で同時証明**。
  これが §1 の hard core(lean も同地点で停滞)。D-eq-1 単独の sorry 化は孤立債務ゆえ非推奨。
- **次セッションの D1 設計**: 抽象順序数 δ 上の transfinite induction で「δ の canonical-rep
  存在(1.4b)∧ necessity(1.9)」を同時に carry。generator の arg は <δ ゆえ IH 適用可。
  term 側(oV b, proj)はその系として A2/nonmem を得る。measure 設計が山。
  Cset_c ツールキットは全て揃った。canonical_witness(1.4b)が唯一の未証明 primitive。

---

## ROADMAP 続89(30) — Buchholz 1986 原論文精読で残作業を確定(2026-06-14)

原論文(PDF p.197-201, §1.2-1.9 + §2.2)を精読。**残作業 = Buchholz の短い補題の port**と判明。

### psi_proj_nonmem の正しい証明(Buchholz 1.9 necessity 経由)
nonmem: ψ_a(oV b)∉Cv(oV m)a。
1. 仮定 ψ_a(oV b)∈Cv(oV m)a。
2. **1.9 necessity**(γ∈C_u(α)⟹G_u γ⊆α)で **G_a(ψ_a(oV b))⊆oV m**。
3. G_a の定義(Buchholz §2 G3 / 2.2b 橋): G_a(ψ_a(oV b))={oV b}∪G_a(oV b)(a≤a ゆえ)。
   さらに 2.2b: G_a(oV b)={oV x : x∈Gterm a b}(term↔ordinal 橋)。
4. bad 係数 m∈Gterm a b, oV m≥oV b(B1)⟹ oV m∈G_a(oV b)⊆oV m ⟹ oV m<oV m。**矛盾**。✓

### ★1.9 necessity には Cset_c(canonical-generator 閉包)が必須
- 非canonical generator ψ_w ξ(ξ∉C_w(ξ), ξ<α)では G_u ξ が α を超え得る(ξ の係数は ξ で
  bound されない)⟹ **unrestricted Cset では 1.9 は偽**。band_lt_psi(=1.5)は値bound だけで
  済むので unrestricted でも真だったが、1.9 は係数構造ゆえ canonicity 必須。
- ⟹ **Cset_c(続89(28) で定義済)に対し 1.9 を証明**。Buchholz の証明は短い:
  - **1.4(c)**: Ω_v≤ψ_u ξ∈C_v(α) ∧ ξ∈C_u(ξ) ⟹ ξ∈α∩C_v(α)。(canonical 前提込み・1.4b 経由)
  - **1.4(b)**: γ∈C_v(α) ∧ Ω_v≤γ∈P ⟹ ∃u,ξ(γ=ψ_u ξ ∧ ξ∈α∩C_v(α)∩C_u(ξ))。
    Cset_c では generator step が ξ∈C_u(ξ) を**定義に含む**ので **ほぼ自明**(続89 の indec_Cset_generator
    + canonical-gen 帰属で出る)。← これが unrestricted で苦労していた所、Cset_c なら無料。
  - **1.9**: min{n: γ∈C_0^n(ε)} 帰納 + 1.4(c) + 1.2(e)。
- G_u をオーダー数上に定義(Buchholz §1末: γ∉P⟹G_u γ=∪{G_u ξ:ξ∈P(γ)}; γ=ψ_v ξ(ξ∈C_v(ξ))⟹
  G_u γ=({ξ}∪G_u ξ if u≤v else ∅))。Cantor_NF(P(γ)分解)で形式化。

### Remark(Cv=Cv_c)で私の psi に転送
- psi は unrestricted Cv で定義済。nonmem は Cv(unrestricted)についてなので **Cv=Cv_c が要る**
  (Buchholz Remark「(*)省略は C を変えない」)。⊇自明、⊆が核(非canonical generator の redundancy)。
  ⊆: 非canonical ξ の ψ_w ξ は collapse_succ(=1.6a, 済)で canonical 化。collapse 機械で port。
- 代替: psi を Cset_c で再定義(Buchholz 忠実)。ただし C_build/Ccond/oV_order_pres 等の
  green 証明への影響要確認(C_build は sufficiency なので Cset_c でも通る可能性)。**Remark 経由が低risk**。

### 既に持っている Buchholz 補題(緑)
1.2(b)psi_addprinc / 1.2(c)Om_le_psi+psi_lt_Om_Suc / 1.2(d)psi_mono_arg / 1.2(h)collapse_grow /
1.3 psi_strict_mono_arg / 1.4(a)psi_inj_canonical / 1.5 band_lt_psi(⊆)+below_psi_in_Cset(⊇) /
1.6(a)collapse_succ / 2.2(c)oV_order_pres / indec_Cset_generator / Cset_c ツールキット全部。

### 次セッションの実行順(全て Buchholz の短い証明の port)
(1) G_u をオーダー数上に定義(Cantor_NF P分解利用)+ 2.2b 橋(G_a(oV t)={oV x:x∈Gterm a t})。
(2) Cset_c に対し 1.4(b)(canonical-gen 帰属、ほぼ自明)→ 1.4(c) → 1.9 necessity。
(3) Remark Cv=Cv_c(collapse_succ で非canonical generator redundancy)。
(4) nonmem を上記チェーンで discharge → psi_proj 完成 → oV_mono_NF へ。
