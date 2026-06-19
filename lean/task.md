# PSS termination — task / terminal status (Lean 4 / Mathlib v4.30.0)

## Bottom line
PSS termination (`YAPSS.PSS_terminates_nrm_final : WellFounded stepRel`) is proven
**`sorryAx`-free MODULO the single Buchholz §1 collapse core** (`CollapseResidueMaxo` +
`HeadFamilyNF`, supplied as explicit hypotheses).  Everything else — the route assembly,
all structural leaves, the arg-zone/forest machinery, the §2 embedding half, and the §1
simultaneous-induction BASE + skeleton — is GREEN.

```
#print axioms YAPSS.PSS_terminates_nrm_final
  -- [propext, Classical.choice, Quot.sound]   (NO sorryAx; modulo CRM + HF hypotheses)
```

## The single remaining core
The Buchholz §1 **simultaneous transfinite induction** carrying the **value-identity**
`ψ_u(δ) = ψ_u(ξ)` (for the canonical rep `δ`) through the deep generators.  Equivalent
guises (all the same content): `CollapseResidueMaxo` / `Nrm.psi_proj_notmem` (collapse
face), `Residue.alpha_step_residue` / `NoncanonValueMem` 4 leaves (necessity face, `subA_nm`
= the no-realizer deep core), the live-path `Wttone.H0clause_oper_step` forest clause.
See `PROOF-STATUS.md` §(a0) for the terminal characterization.

## The finest obstruction: REP-AT-THE-BOUND
The collapse `ψ_u(ψ_w η) = ψ_u η` needs the `≥` half `ψ_u η ≤ ψ_u(ψ_w η)` (the `≤` is free
by `psiSelf_mono_arg`).  The canonical rep of the value `ψ_u(ψ_w η)` is `η` ITSELF (`η` is
`u`-canonical, `ψ_u η = ψ_u(ψ_w η)` if the collapse holds, `η ≥ η`) — so the rep sits AT the
bound `η`, NOT strictly below it.  Buchholz's simultaneous-induction IH `P(ξ')` is for
`ξ' < α` (strict-below), so it CANNOT supply the rep `η` (= the current point).  This is the
precise irreducible content: rep-at-the-bound, unreachable by the strict-below IH.

## Why it is irreducible (campaign 2026-06-20, every route disproven/circular)
- ordinal joint induction, term `tsize`-induction, `C_u`-set-agreement — circular.
- value-bound `hVB` — FALSE in true ordinals (term-model `lt_term` unfaithful).
- fixpoint tower / saturation, set-membership (`deepgen_arg/value_not_mem`) — reduce cleanly
  (via Lemma 1.5) to the same value-identity; every internal measure (ordinal-WF, `crank`,
  `tsize`) recurses back to it.
- §2 term-surjection `OVSurjective` — FALSE (cardinality); §2 does not break the core
  (ya-pss has the full term system + `term_nec` GREEN and stalls identically).
- regularity/cofinality — gives the band bound, not the value-identity.
- injectivity-in-joint — VACUOUS (`psiSelf_canonical_inj` already unconditional; pins
  uniqueness `ζ = δ`, not the rep's position).
- Lemma 1.6(b) / 1.9⟸ — reduce to "no canonical in `(c,η)`" = the same core (fixpoint gap).
- single-closure re-architecture — DEAD: lean's `CsetSelf`/`psiSelf` IS already Buchholz's
  single canonical-closure world; the collapse is already stated in it; `ψ_u η` never fires
  into `CsetSelf η u` in ANY closure (`η ⊀ η`), so the rep `η` is at the bound regardless.
- Buchholz's `C_v` IS `CsetSelf` (canonicity built-in); he never needs `Cset = Cset_c`.

6 soundness catches this campaign (no false `sorry` ever introduced): `subA_nm`-uncond, `hVB`,
tower-goal, naive `PsiValueAcanon`, `OVSurjective`, injectivity-vacuity.

## GREEN substrate (the simultaneous-induction base + skeleton, `sorryAx`-free)
`YAPSS/Crank.lean`: `crank` + `crank_arg_lt` (C-rank strict-drop), `CsetSelf_crank_induction`,
`Gset` (= Buchholz `G_uγ`) + `Gset_gen` + `Gset_gen_subeps`, `psiValue_mem_imp_arg_lt` (Lemma
1.9 generator), `deepgen_arg_not_mem` + `deepgen_value_not_mem` + `psiSelf_w_arg_not_mem`.
`YAPSS/Residue.lean` (`EpsLvlFixpoint` + skeleton): `psiSelf_eq_opow_some`,
`psiSelf_fixpoint_of_below_saturated`, `psiSelf_epsLvl_fixpoint` (first deep ψ-fixpoint,
`ε`-boundary), `fixpoint_iff_saturated`, `subA_nm_collapse_of_noRealizer`, `realizer_imp_strict`
+ `realizer_eq_rep`, `mem_CsetSelf_lvl` + `subA_nm_subeps_vacuous`, `noncanonValueMem_joint`
(4-leaf skeleton), `CsetSelf_lt_psiSelf_of_lt_Om` (1.5).
§1 self-lemmas (GREEN): 1.2c/1.2d/1.3/1.4a/1.4b/M1/1.6a/1.7/`acanon_sub_mono`.
§2 embedding (GREEN, Lemma 2.2): `Otembed.oV`, `oV_order_pres`, `wf_olt_wf3`, `Gterm`,
`Gterm_tsize`, `NEC_of_canonWitness` (= ya-pss `term_nec`), `Nrm.proj`.

## What would close it
The full Buchholz §1 simultaneous transfinite induction (outer on the bound `α`, inner on
closure-rank `n`, carrying `ψ_v` mono + injective + the value-identity collapse TOGETHER) — BUT
with a NEW idea for the rep-at-the-bound step (the strict-below IH structurally cannot supply
the deep-generator rep `η`).  Both projects (lean term-level, ya-pss ordinal) stall here
identically — strong evidence it is the real mathematical content, not a formalization
artifact.  The campaign's `crank`/`Gset`/fixpoint infra + the 9 §1 self-lemmas + the §2
embedding half are the complete correct substrate; the missing ingredient is the
rep-at-the-bound argument, which no tested sub-reduction supplies.
