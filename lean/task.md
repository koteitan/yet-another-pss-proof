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

## Why it is irreducible (campaign 2026-06-20, all routes disproven/circular)
- ordinal joint induction, term `tsize`-induction, `C_u`-set-agreement — circular.
- value-bound `hVB` — FALSE in true ordinals (term-model `lt_term` unfaithful).
- fixpoint tower / saturation — stalls at the deep generator (every internal measure:
  ordinal-WF, `crank`, `tsize` recurses back to the same value-identity).
- §2 term-surjection `OVSurjective` — FALSE (cardinality); and §2 does not break the core
  (ya-pss has the full term system + `term_nec` GREEN and stalls identically).
- regularity/cofinality — gives the band bound, not the value-identity.
- Buchholz's `C_v` IS `CsetSelf` (canonicity built-in); he never needs `Cset = Cset_c`.

5 soundness catches this campaign (each Lean-proven false / re-sounded): `subA_nm`-uncond,
`hVB`, tower-goal, naive `PsiValueAcanon`, `OVSurjective`.

## GREEN substrate (the simultaneous-induction base + skeleton, `sorryAx`-free)
`YAPSS/Crank.lean`: `crank` + `crank_arg_lt` (C-rank strict-drop), `CsetSelf_crank_induction`,
`Gset` (= Buchholz `G_uγ`) + `Gset_gen`, `psiValue_mem_imp_arg_lt` (Lemma 1.9 generator).
`YAPSS/Residue.lean` (`EpsLvlFixpoint` + skeleton): `psiSelf_eq_opow_some`,
`psiSelf_fixpoint_of_below_saturated`, `psiSelf_epsLvl_fixpoint` (first deep ψ-fixpoint,
`ε`-boundary), `fixpoint_iff_saturated`, `subA_nm_collapse_of_noRealizer`,
`noncanonValueMem_joint` (4-leaf skeleton).
§2 embedding (GREEN): `Otembed.oV`, `oV_order_pres`, `wf_olt_wf3` (Lemma 2.2), `Gterm`,
`Gterm_tsize`, `NEC_of_canonWitness` (= ya-pss `term_nec`), `Nrm.proj`.

## What would close it
The full Buchholz §1 simultaneous transfinite induction (outer on the bound `α`, inner on
closure-rank, carrying `ψ_v` mono + injective + the value-identity collapse TOGETHER).
This is the genuine multi-month foundational item; both projects (lean, ya-pss) stall here
identically — strong evidence it is the real mathematical content, not a formalization
artifact.  The campaign's `crank`/`Gset`/fixpoint infra is the correct substrate for it.
