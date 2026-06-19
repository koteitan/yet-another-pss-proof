# PSS termination — proof status (Lean 4 / Mathlib v4.30.0)

Project `YAPSS`: well-foundedness of the PSS one-step relation
`stepRel T M := ST_PS M ∧ step M T` (equivalently `stepR` in `Wtt`).

**Bottom line.** PSS termination is proven **modulo a single project-central
residual**, now isolated in two equivalent characterizations, plus two alternate
parametric routes whose residuals are the same content in a different guise.
Everything else — the route assembly, the structural leaves, and (new this cycle)
the entire arg-zone / forest machinery — is proven and `sorryAx`-free. Ten+
separate attempts to *bypass* or *localize* the core have each been disproven by
an explicit counterexample (recorded below); the core is irreducible.

The two characterizations of the single core are **dual / sibling**:

| characterization | guise | endpoint | residual |
|---|---|---|---|
| **§1 ordinal-collapse** (original) | Buchholz ψ-value collapse | `PSS_terminates_nrm_final` | `CollapseResidueMaxo` + `HeadFamilyNF` |
| **arg-zone ORDER / term-level forest** (live path) | head-`0` OT3 forest clause | `proj0_olt_NF` chain / `H0clause_translate` | `H0clause_oper_step` = `not_pfire0_lead1max1_NF` = `Rdesc_hstep` |

```
#print axioms YAPSS.PSS_terminates_nrm_final
  -- [propext, Classical.choice, Quot.sound]      (NO sorryAx — modulo CRM+HF)
#print axioms YAPSS.H0clause_translate            -- [.. , sorryAx, ..]  via H0clause_oper_step only
#print axioms YAPSS.proj0_olt_NF                  -- [.. , sorryAx, ..]  via the 3 forest-core sorries
#print axioms YAPSS.ST_PS_desc                    -- [propext, Classical.choice, Quot.sound]  (sorryAx-free)
#print axioms YAPSS.proj_keystone                 -- [propext, Classical.choice, Quot.sound]  (sorryAx-free)
#print axioms YAPSS.Gterm_translate_subblock      -- [propext, Classical.choice, Quot.sound]  (sorryAx-free)
```

---

## (a) What is proven

### Three independent parametric termination routes (each `sorryAx`-free)

All three live in `YAPSS/Reduction.lean`, each re-derived parametrically on its
explicit residual hypotheses so the `_modulo`/`_final` theorem itself carries no
`sorry`:

| route        | endpoint theorem                | residual hypothesis it rests on              |
|--------------|---------------------------------|----------------------------------------------|
| nrm-order    | `PSS_terminates_nrm_final`      | `CollapseResidueMaxo` + `HeadFamilyNF`       |
| pure-lex     | `PSS_terminates_modulo_wfArgsA` | `wf_ArgsA` (WF of `<o` on each `ArgsA m`)    |
| W=T direct   | `PSS_terminates_modulo_diag`    | `diag_acc` (diagonal-tower accessibility)    |

Each route's residual is the same §1 content in a different guise (maxo-collapse /
multiset / hydra); the project needs only ONE of the three discharged. The
nrm-order route has the smallest, sharpest residual and is the designated endpoint.

### Structural leaves — all proven (`sorryAx`-free)

- `wf3_nrm` : every `nrm`-image is a Buchholz OT term (`wf3`).
- `wf_olt_wf3` : `<o` is well-founded on the `wf3` class (Buchholz Lemma 2.2,
  via the `oV` embedding, strictly monotone on `wf3`).
- `ST_PS_suffix` : `dropWhile`-tail closure of standard pair-sequences.
- **`ST_PS_desc` + `ST_PS_desc_oper` + `ST_PS_desc_caseB`** (new): the `takeWhile`
  *dual* of `ST_PS_suffix` — the descendant block `(0,0) :: rest.takeWhile (0<·.1)`
  of a standard form is again `ST_PS`. Built directly from the closed
  `oper_tail_cases` machinery (`dropWhile_rest_caseB` / `dropWhile_rest_tiling` /
  `oper_caseB_form` / `oper_eq_pred_*` / `interior_pos` / `dropLast_interior_pos`),
  mirroring its `|tail|≤1` branch split (predzero / noparent / d0>0 / j0≥1 / Case-B).
- `step_terminates` : `WellFounded Rnf ⟹ WellFounded stepRel` (decrease discharged).
- the `proj` toolkit: `proj_id`, `proj_rec`, `proj_wf3`, `proj_G`, `proj_nofire`,
  `pfire_iff`, `proj_submono`, `Gterm_trans`.
- the structural NF order facts feeding `oV_nf_order_pres` (`oV_order_pres`,
  `oV_order_refl`, `oV_nrm_eq_*`), `maxr1 ≤ 1` fragment, and the sub-`ε` lever.

### Arg-zone ORDER / term-level forest machinery — all proven (`sorryAx`-free)

Ported from ya-pss 続90 and developed in Lean (`Nrmstep.lean`, `Wttone.lean`); this
reduces `nrm_order_pres` / `proj0_olt_NF` to the term-level forest core without the
ordinal-collapse detour. All of the following have complete, `sorryAx`-free bodies:

- **`proj_keystone`** : the chain-descent engine
  `1 ≤ L < lead x ∧ maxsub x = climb x ∧ maxsub y < maxsub x ⟹ proj 0 (P L x y) = proj 0 x`
  (the novel side-condition `maxsub x = climb x`, i.e. on the leading spine).
- **`mvstep` recursion** : `mvstep` (greatest level-`0` violator's `proj 1` step) with
  `proj_mvstep`, `tsize_mvstep_lt`, `lead_mvstep_eq_maxsub`, `maxsub_mvstep`,
  `maxsub_climb_mvstep` — the strict `tsize`-descent recursion.
- **`Rdesc` / `Rdesc_match`** : the inductive descent-pair relation and its
  lead/maxsub/climb-matching invariant; `Rdesc_firing_char` characterizes firing on
  the descent class; `proj0_olt_of_mvstep_olt` is the relation-carrying strict
  recursion (tie-zero strict STEP, lockstep firing descent).
- **SubBlock positional correspondence** : `SubBlock` (the takeWhile/dropWhile
  reflexive-transitive sub-block relation), `SubBlock_sndSet` (`sndSet` ⊆), and
  **`Gterm_translate_subblock`** — every `g ∈ Gterm 0 (translate M)` is `translate K`
  for a `SubBlock M K` (model-verified 2241/2241). This is the bridge that turns the
  forest core into a statement purely about contiguous sub-blocks.
- **carrier decomposition** : `proj_ole_of_critembed`, `proj_bothfire_witness_eq_final`
  (assembly modulo the forest core), `Gterm_translate_lead_le`,
  `maxsub_translate_eq_maxr1`.
- **H0clause ST_PS-induction** (`Wttone.lean`) : `H0clause_diagSeq_le1` (diag base,
  `sorryAx`-free), the `H0clause_translate` skeleton (`tsize` strong recursion: root
  clause + descendant + sibling, the descendant lifted via `ST_PS_desc`, the sibling
  via `ST_PS_suffix` + self-recursion), `z_dropWhile` / `z_takeWhile_cons`,
  `wf3_of_cnf_subs1`, `OT3all1_head1`, `OT3all0_okH`.
- **dseg / fbseg attack infrastructure** : `dseg`, `fbseg`, `dseg_fbseg`,
  `fbseg_K_desc`, `fbseg_T_desc`, `fbseg_hd_level` (the dominated-segment descent +
  forest-boundary level-squeeze) — the proof scaffold aimed at the forest core's
  `olt (translate K) (translate B)` conclusion.

---

## (b) The single genuine residual — the §1 firing wall, two faces

### Face 1 — term-level head-`0` OT3 forest clause (live path)

Consolidated to the single Wttone residual **`H0clause_oper_step`**:

> For a forest node whose descendant block is `B` with `(0,0) :: B ∈ ST_PS` and
> row-`1` `≤ 1`, the `(0,0)`-rooted translate `P 0 (translate B) Z` satisfies
> `H0clause` — equivalently `∀ x ∈ Gterm 0 (translate B), olt x (translate B)`
> together with `H0clause (translate B)`.

Via `Gterm_translate_subblock` each coefficient `x ∈ Gterm 0 (translate B)` is
`translate K` for the **canonical** witness `K` the recursion produces (a contiguous
infix `K = B[i:j]`), so the clause is:

> for the canonical `Gterm`-`0` witness `K = B[i:j]`, `olt (translate K) (translate B)`.

(NB the *un-restricted* `∀ K, SubBlock B K ⟹ olt (translate K)(translate B)` is
**FALSE** — 74 violations at closure+5/+6 over all SubBlocks; only the canonical
`Gterm`-`0` witnesses are dominated. Do not use the all-SubBlock form.)

It is the SAME content as the two existing Nrmstep residuals, all on the same forest
core:

- `not_pfire0_lead1max1_NF` : a lead-`1`, `maxsub`-`1` head-`0` `NF` argument does
  not fire (`¬ pfire 0 b ⟺ ∀ g ∈ Gterm 0 b, olt g b`) — the fire-propagation half.
- `Rdesc_hstep` : the strict STEP `Rdesc x y → olt x y → olt (mvstep x) (mvstep y)` —
  the both-fire half.

**Why it is not local.** The clause splits by `lead (translate B)`: coefficients of
strictly smaller head are auto-`olt` (18235/0); but EQUAL-head coefficients are
head-`0`-nested head-`1` coefficients that are NOT in `Gterm 1` (5609/6461), so
`OT3all1_head1` does not reach them — their `olt` depends on the forest position,
i.e. full `ST_PS`-reachability. Concretely it needs the `oper` copy/tiling structure
(`oper_bad_blocks`; the `d0 = 0 ∧ idx1 = 0` tiling copy non-firing). Model-verified
TRUE (head-`0` clause 25061/0 at every head-`0` node; descendant `H0clause` 1481/0;
whole-image `H0clause(translate M)` on the `maxr1 ≤ 1` fragment 0/671 with the
Buchholz `Gterm` semantics).

**Seqlex/depth-shift route — investigated, reduces to a non-positional core.**
The clean engine is `seqlex_imp_olt` (`Seqlex.lean`): `olt (translate K)(translate B)`
follows from `seqlex (shift K) B` once `K` is shifted (via `translate_shift`) to align
its head row-0 with `B`'s. The canonical witness is a contiguous infix `K = B[i:j]`
with `B[i].1 ≥ dB` so the shift `δ = dB − B[i].1 ≤ 0` (model-verified). `seqlex (shift K) B`
is TRUE at top level (0 viol +5/+6/+7): at the first column where `shift K` and `B`
differ, `shift K` is strictly lower (row-0 or row-1), never higher — the ascending-copy
domination (`core_i1` content). **But this divergence-downward fact is NOT capturable
by any column-local invariant of B**: it is TRUE for `translate`-of-`ST_PS` blocks yet
FALSE for arbitrary `steps1` sequences (25887 viol), and adding `z0ok` + `row1≤1` +
`row1-rises-with-row0` still leaves 14174 viol. It needs the full `ST_PS`
parent/ascent forest-reachability, NOT steps1/per-column data. Every structural
recursion to prove it (term arg-descent, tsize-x, `translate.induct`, SubBlock
derivation, strengthen-`Gterm_translate_subblock`) is FALSIFIED — the clause/seqlex
fact is FALSE at intermediate recursion nodes (e.g. blockok sub-blocks: 169/417/1158
clause-viol). So the residual is genuinely **non-inductive / globally
forest-reachability-bound** — the signal that closing it needs heavier machinery
(`dseg`/`fbseg` full build, or the Towsner distinguished-set route), not a structural
induction. Deposited GREEN assets toward it: `YAPSS/Gterm0Olt.lean`
(`translate_take_le : translate (L.take m) ≤o translate L`, `translate_append_ge`,
`ole_trans`).

### Face 2 — Buchholz §1 ordinal-collapse (original)

Two TRUE faces, both irreducible (the closure structure alone does not force them):

**Collapse face — `CollapseResidueMaxo`** (`Residue.lean`). For an OT3-violator that
`proj` actually selects (the `olt`-greatest `g ∈ Gterm a b'` with `¬ olt g b'`), the
projected value equals the original — the gap carries no new ψ-value:
`ψ_a(oV b') = ψ_a(oV g)` with `g = maxo ((Glist a b').filter (¬ olt · b'))`.
Empirically TRUE (278/278). (The un-restricted `CollapseResidue` over arbitrary
violators is FALSE — only the maxo-selected one collapses; see bypass #4.)

**Head face — `HeadFamilyNF`** (`Reduction.lean`). The dual non-collapse statement:
the lead-`0` NF argument family is strictly ψ-ordered (`ψ_0(oV x) < ψ_0(oV f)`).
Genuine Ω-band §1 content; per-element it reduces to `CollapseResidueMaxo` + the
proj-side order (`psi0_head_of_CRM`).

**The two faces are dual/sibling.** Face 1 is the term-level statement (the head-`0`
OT3 clause on `translate`-images, via the `oV` embedding and the forest-position /
SubBlock structure); Face 2 is the same fact read on the `oV`-values as the
ψ-collapse over the maxo gap. The `oV`-monotone bridge (`oV_nf_arg_lt` modulo its
`hheadfam` hypothesis) is what links the two; both bottom out in the same Buchholz §1
omitted simultaneous induction.

---

## (c) Disproven bypass / localization attempts — the rigor record (11)

Each was a proposed way to make the core vacuous, cheap, or term-local. Each is
**FALSE**, with an explicit counterexample. The ordinal-collapse ones are retained in
source as valid implications with *unsatisfiable* hypotheses, clearly labelled DEAD.

**Ordinal-collapse bypasses (1–7):**

| # | attempt (residual)        | counterexample                                                                 |
|---|---------------------------|--------------------------------------------------------------------------------|
| 1 | `AcanonLtValue`           | `δ = Ω_{w+1}` is `w`-canonical but `δ ≥ psiSelf δ w` (not `δ < value`).        |
| 2 | `PsiValueAcanon`          | `ζ = Ω_1` is `0`-canonical, but `psiSelf Ω_1 0` is NOT a canonical value.      |
| 3 | `CanonRep` (`δ < c`)      | when `psiSelf ζ w ≤ ζ` there is no canonical witness `δ < c`.                  |
| 4 | `CollapseResidue` (arbitrary `g`) | non-maxo violators do NOT collapse; only the maxo-selected one does.   |
| 5 | `IntervalNoncanon`        | Ω-crossing: gap `[oV b', oV g)` contains `Ω_k = ψ_k(0)`, which IS `a`-canonical. |
| 6 | `ProjFixesNrm`            | `proj` fires on `nrm`-images: `proj 0 (p₁(p₂(0))) = p₂(0) ≠ p₁(p₂(0))`; ~5% of P-nodes the `oV_nrm` induction reaches fire (314/7108 @ closure+8). |
| 7 | `NFwf3` (NF ⊆ wf3)        | `translate(diagSeq 0 2) = P 0 (P 1 (P 2 Z Z) Z) Z ∈ NF` is NOT `wf3` (maxr1=2 images fail OT3, 8314/8314). |

**Term-level / forest-localization bypasses (8–11), this cycle:**

| #  | attempt (local carrier for the head-`0` clause / firing-exclusion)            | refutation |
|----|--------------------------------------------------------------------------------|-----------|
| 8  | NO local term predicate captures firing-exclusion: `r1ok`, `r1okRel`, `maxsub = climb`, `descok`, `okH`, "shifted-descendant is `ST_PS`" — all refuted. | the cter `(0,0)(1,0)(2,1) ↦ p₀(p₀(p₁0))` is `r1ok` ∧ reduced yet `translate` fires and is NOT `ST_PS`; `descok` fails hereditarily at depth 4 `p₁(p₀(p₁(p₁0)))`; `okH` is FALSE on the image (`p₀(p₁0)` is OT3-valid but `okH`-illegal). |
| 9  | general `proj0`-monotone (without NF discipline)                               | FALSE ~25% (`p₁(0)+p₀(p₁(0)+p₁(0))` is `cnf`, `lead = maxsub = 1`, yet fires). |
| 10 | relative `r1ok` (block-local minimum-row-0 anchor) suffices for non-firing     | descendant blocks are forest-interior **copies** with positive root row-`1`, not standalone standard forms — the node-relative lift `(0,0)::(argblock − x) ∈ ST_PS` is FALSE (304/13105; even shifted only 702/12801 — the shift fixes the order but not the row-`1` climbing). Only the **root**-threshold lift `(0,0)::takeWhile(0<·)` is `ST_PS` (`ST_PS_desc`, 13105/0). |
| 11 | `wf3 ⟹ H0clause` (read OT3 well-formedness off as the head-`0` clause)         | FALSE: `wf3 (P a b c)` gives the `Gterm a b` clause, but `H0clause` needs `Gterm 0 b`; the gap is exactly the head-`0`-nested head-`1` coefficients, model-confirmed. |

Common shape of all failures: the bypass tries to derive the equality / non-firing
from closure / canonicity / a term-local invariant, but those only yield the *weak*
inequality (`oV b' ≤ oV g`) or fail on a forest-position-sensitive instance. The core
is an extra, genuine §1 fact about the specific maxo gap / forest position.

---

## (d) Current `sorry` inventory (7 sites)

The three **forest-core** sorries (all the SAME content — Face 1):

- `Wttone.H0clause_oper_step` — the consolidated head-`0` OT3 forest clause.
- `Nrmstep.not_pfire0_lead1max1_NF` — fire-propagation half.
- `Nrmstep.Rdesc_hstep` — both-fire strict STEP half.

The **§1 ordinal** sorries (Face 2 / off-path):

- `Nrm.psi_proj_notmem` — collapse face (`CollapseResidueMaxo`'s leaf).
- `Residue.alpha_step_residue` — necessity-face joint induction, 4 model-verified
  sub-sorries (`subA_le`, `subA_nm`, `caseB`, `caseSum`); OFF every termination path
  (necessity does not feed the nrm route — kept for the closure-side record).

The **alternate-route** leaves (each is the same §1 content in another guise; only one
route need be discharged, and the nrm route does not use these):

- `Wfsum.wf_ArgsA` — pure-lex route leaf.
- `Wtt.diag_acc` — W=T route leaf (closes by level-induction once the core is in).

`oV_nf_arg_lt` (`Nrm.lean`) is **proven** modulo its `hheadfam` hypothesis (the §1
head over a down-set), i.e. it carries no own `sorry`; `hheadfam` is the
`HeadFamilyNF` content.

---

## (e) Cross-project note

The sibling project `ya-pss` is stuck on the *identical* core: its `psi_proj_nonmem`
(equivalently the maxo-collapse `psi_proj`, and on the live path the same oper
copy-tiling head-`0` fact) is the same Buchholz §1 wall. The two independent
formalizations — one ordinal (`ya-pss`), one term-level forest (`lean` arg-zone) —
have converged on the same irreducible residual, strong evidence that it is the
genuine mathematical content of PSS termination (Buchholz §1) and not a formalization
artifact. The two projects are complementary: the Lean proj0/lead-spine work reduces
ya-pss's `harg` residuals, and ya-pss's arg-zone reframe lets Lean bypass the ordinal
wall — both live paths land on the same forest core.
