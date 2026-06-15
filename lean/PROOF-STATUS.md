# PSS termination — proof status (Lean 4 / Mathlib v4.30.0)

Project `YAPSS`: well-foundedness of the PSS one-step relation
`stepRel T M := ST_PS M ∧ step M T` (equivalently `stepR` in `Wtt`).

**Bottom line.** PSS termination is proven **modulo a single genuine residual: the
Buchholz §1 ordinal-collapse**, in two TRUE faces `{CollapseResidueMaxo,
HeadFamilyNF}`. Everything else — all structural leaves and the route assembly — is
proven and `sorryAx`-free. Seven separate attempts to *bypass* the §1 collapse have
each been disproven by an explicit counterexample (recorded below); the collapse is
irreducible.

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

Each route's residual is the same §1 collapse content in a different guise
(maxo-collapse / multiset / hydra); the project needs only ONE of the three
discharged. The nrm-order route has the smallest, sharpest residual and is the
designated endpoint.

```
#print axioms YAPSS.PSS_terminates_nrm_final
  -- [propext, Classical.choice, Quot.sound]   (NO sorryAx)
```

### Structural leaves — all proven

- `wf3_nrm` : every `nrm`-image is a Buchholz OT term (`wf3`).
- `wf_olt_wf3` : `<o` is well-founded on the `wf3` class (Buchholz Lemma 2.2,
  via the `oV` embedding, strictly monotone on `wf3`).
- `ST_PS_suffix` : tail-`NF`-closure of standard pair-sequences (discharges `hSuf`).
- the structural NF order facts feeding `oV_nf_order_pres` (`oV_order_pres`,
  `oV_order_refl`, `oV_nrm_eq_*`), `maxr1 ≤ 1`, and the sub-`ε` lever.
- `step_terminates` : `WellFounded Rnf ⟹ WellFounded stepRel` (decrease discharged).
- the `proj` toolkit: `proj_id`, `proj_rec`, `proj_wf3`, `proj_G`, `proj_nofire`,
  `pfire_iff`, `proj_submono`, `Gterm_trans`.

---

## (b) The single genuine residual — Buchholz §1 ordinal-collapse

Two TRUE faces, both irreducible (the closure structure alone does not force them):

**Collapse face — `CollapseResidueMaxo`** (`Residue.lean`). For an OT3-violator
that `proj` actually selects (the `olt`-greatest `g ∈ Gterm a b'` with `¬ olt g b'`),
the projected value equals the original value — the gap carries no new ψ-value:

> **ψ_a(oV b') = ψ_a(oV g)**,  where `g = maxo ((Glist a b').filter (¬ olt · b'))`.

Empirically TRUE (278/278). (The un-restricted `CollapseResidue` over *arbitrary*
violators `g` is FALSE — only the maxo-selected violator collapses.)

**Head face — `HeadFamilyNF`** (`Reduction.lean`). The dual *non-collapse* statement:
the lead-0 NF argument family is strictly ψ-ordered (`ψ_0(oV x) < ψ_0(oV f)`). Genuine
Ω-band §1 content (the head args have lead ≥ 1, so `oV ≥ Ω_1 > ε(0)` — the collapse
region; it does not trivialize via sub-`ε` or proj-to-sub-`Ω`). Per-element it reduces
to `CollapseResidueMaxo` + the proj-side order (`psi0_head_of_CRM`).

This is exactly Buchholz Remark p197 ("omitting a condition does not change C_v(α)")
applied to the collapse region.

---

## (c) Disproven bypass attempts — the rigor record (7)

Each of these was a proposed way to make the §1 collapse vacuous or cheap. Each is
**FALSE**, with an explicit counterexample. They are retained in the source as valid
implications with *unsatisfiable* hypotheses, clearly labelled DEAD — kept so the
record shows the collapse cannot be dodged.

| # | attempt (residual)        | counterexample                                                                 |
|---|---------------------------|--------------------------------------------------------------------------------|
| 1 | `AcanonLtValue`           | `δ = Ω_{w+1}` is `w`-canonical but `δ ≥ psiSelf δ w` (not `δ < value`).        |
| 2 | `PsiValueAcanon`          | `ζ = Ω_1` is `0`-canonical, but `psiSelf Ω_1 0` is NOT a canonical value.      |
| 3 | `CanonRep` (`δ < c`)      | when `psiSelf ζ w ≤ ζ` there is no canonical witness `δ < c`.                  |
| 4 | `CollapseResidue` (arbitrary `g`) | non-maxo violators `g` do NOT collapse; only the maxo-selected one does. |
| 5 | `IntervalNoncanon`        | Ω-crossing: the gap `[oV b', oV g)` contains `Ω_k = ψ_k(0)`, which IS `a`-canonical (163/208 wf3-instances). |
| 6 | `ProjFixesNrm`            | `proj` fires on `nrm`-images: `proj 0 (p_1(p_2(0))) = p_2(0) ≠ p_1(p_2(0))`; ~5% of the P-nodes the `oV_nrm` induction reaches fire (314/7108 at closure+8). See `tools/audit_projfix_*.py`. |
| 7 | `NFwf3` (NF ⊆ wf3)        | `translate(diagSeq 0 2) = P 0 (P 1 (P 2 Z Z) Z) Z ∈ NF` is NOT `wf3` (maxr1 = 2 translate-images never satisfy the OT3 clause; 8314/8314 fail). |

Common shape of the failures: the bypass tries to derive the collapse equality from
the closure/canonicity structure, but that structure only yields `oV b' < oV g`
(consistent with `oV b' ≤ oV g`), never the equality. The equality is an extra,
genuine §1 fact about the specific maxo gap.

---

## (d) Cross-project note

The sibling project `ya-pss` is stuck on the *identical* core: its `psi_proj_notmem`
(equivalently the maxo-collapse `psi_proj`) is the same Buchholz §1 collapse equality.
The two independent formalizations have converged on the same irreducible residual,
which is strong evidence that it is the genuine mathematical content of PSS
termination — Buchholz §1 — and not a formalization artifact.
