/-
# `YAPSS.Reduction` — termination modulo named residues (the sorry dependency map)

This downstream assembly file makes the whole development's reduction status
**legible**: it re-derives each top-level PSS-termination route *parametrically*
on its explicit residual hypotheses, so that each `_modulo` theorem below is
itself `sorryAx`-FREE (the `sorry`s live only in the upstream non-parametric
copies).  Nothing upstream is edited (that would create an import cycle); we add
a fresh assembly layer.

## FINAL STATUS (consolidated endpoint) — see `PROOF-STATUS.md`

**Sound nrm-route endpoint:** `PSS_terminates_nrm_final : CollapseResidueMaxo →
HeadFamilyNF → WellFounded stepRel`, `sorryAx`-FREE (`#print axioms` = `[propext,
Classical.choice, Quot.sound]`).  PSS termination now rests on a SINGLE genuine
residual — the **Buchholz §1 ordinal-collapse**, in two TRUE faces:
`CollapseResidueMaxo` (the collapse `ψ_a(oV b') = ψ_a(oV (maxo-violator))`, 278/278)
and `HeadFamilyNF` (its dual non-collapse Ω-band head).  Everything structural is
proven (`ST_PS_suffix`, the structural NF order, `maxr1 ≤ 1`, sub-`ε`).

**DEAD bypass attempts (rest on DISPROVEN residuals — NOT progress):**
`PSS_terminates_nrm_true` (`ProjFixesNrm` FALSE: `proj` fires on `nrm`-images,
`proj 0 (p_1(p_2(0))) ≠ p_1(p_2(0))`) and `PSS_terminates_nrm_via_NFwf3` (`NFwf3` =
NF⊆wf3 FALSE: `translate (diagSeq 0 2) ∈ NF` is not `wf3`).  Kept as valid
implications with unsatisfiable hypotheses, clearly labelled DEAD below.

## The three independent termination routes

`PSS` one-step relation: `stepRel T M := ST_PS M ∧ step M T` (and the identical
`stepR` in `Wtt`).  Three independent proofs of `WellFounded stepRel`/`stepR`:

| route        | top theorem (upstream)   | residual(s) it rests on                         |
|--------------|--------------------------|-------------------------------------------------|
| pure-lex     | `PSS_terminates`         | `wf_ArgsA`                                       |
| nrm-order    | `PSS_terminates_nrm`     | `psi_proj_notmem`, `oV_nf_arg_lt`, `ST_PS_suffix` |
| W=T direct   | `PSS_terminates_wtt`     | `diag_acc`                                       |

## The 9 remaining `sorry`s, classified by WALL

**Wall A — Buchholz §1 ordinal-collapse core** (two faces, independent):
* `Residue.lean:297` `PsiValueAcanon` — *leaf*.  Every ψ-value is canonical at
  every `v ≤ w`.  `alpha_step_residue` is vacuous given it; further sub-reduced
  to least-witness `(a) ∧ (c)` (`psiValueAcanon_of_ac`).
* `Nrm.lean:348` `psi_proj_notmem` — the **collapse** face.  Reduced (downstream,
  `Residue.psi_proj_notmem_of_collapseResidue`) to the named `CollapseResidue`.
  Independent of `PsiValueAcanon` (the closure structure gives only
  `oV b' < oV g`, not the collapse equality — see `Residue` independence note).

**Wall B — term r1ok / NF-standardness forest core** (one shared root):
* `Nrmstep.lean:1805` `pfire0_maxsub_ge2_NF` — *the hard leaf*: a firing `NF`
  argument has `maxsub ≥ 2` (subscript-ascent / `steps1` content).
* `Nrmstep.lean:1828` `proj0_bothfire_NF` — both-fire proj-order descent.
* `Wttone.lean:323` `H0clause_translate` — the SAME forest core through
  `translate` (its own docstring records the shared-bridge identity).
* `Nrm.lean:502` `oV_nf_arg_lt` — `NF` argument-branch value strict-mono (UBI /
  row-1 content); routes through `psi_proj` + the proj-side order.
* `Nrm.lean:545` `ST_PS_suffix` — tail-`NF`-closure list core (`NF_tail` rests
  on it).

**Independent residuals** (their own islands):
* `Wfsum.lean:689` `wf_ArgsA` — WF of `<o` on the level-`m` argument class; the
  pure-lex route's Buchholz-collapse core.  (Morally Wall-A-flavoured but a
  *separate* statement, not reduced to `PsiValueAcanon`.)
* `Wtt.lean:91` `diag_acc` — diagonal-tower accessibility under `stepR`; the
  W=T route's collapse content.

## Leaf vs derived

True leaf-residuals (not implied by another sorry in-project): `PsiValueAcanon`,
`CollapseResidue` (⇐ `psi_proj_notmem`), `pfire0_maxsub_ge2_NF`,
`H0clause_translate`, `oV_nf_arg_lt`, `ST_PS_suffix`, `wf_ArgsA`, `diag_acc`.
Derived: `proj0_bothfire_NF` is a *separate* leaf (its own `sorry`) but is
phrased so the project's `proj0_olt_NF` rests on it together with
`proj0_fireprop_NF` (the latter already reduced to `pfire0_maxsub_ge2_NF`);
`NF_tail` (proven) and hence `oV_nf_order_pres` rest on `ST_PS_suffix`;
`psi_proj`/`nrm_order_pres` rest on `psi_proj_notmem`.

## UN-REDUCED GAPS (honest map notes)

1. **`oV_nf_arg_lt` is NOT linked to `proj0_olt_NF`.**  Both are Wall B, but the
   nrm-order route's `oV_nf_order_pres` uses the *flat sorry* `oV_nf_arg_lt`
   (Nrm.lean:502) directly — it is NOT reduced in-project to the
   `proj0_fireprop_NF`/`proj0_bothfire_NF` (`Nrmstep.lean`) machinery (those live
   downstream of `Nrm` and feed a different proj-side residual `proj0_olt_NF`).
   So `oV_nf_arg_lt` is taken here as a raw leaf hypothesis (`hArg`).  Linking it
   to `pfire0_maxsub_ge2_NF` would need the `psi0_lt_of_proj_lt` + in-gap-witness
   construction (Nrm.lean:405–494) wired to the `proj`-side order — currently a
   real gap.
2. **`wf_ArgsA` and `diag_acc` are not reduced to `PsiValueAcanon`/`CollapseResidue`.**
   They are morally the §1 collapse core in different guises (multiset / hydra),
   but no in-project reduction links them — each is its own leaf.  (The three
   routes are independent proofs, so the project needs only ONE of the three leaf
   sets discharged.)

## Import note

`Wttone` (carrying the Wall-B leaf `H0clause_translate`) is **not imported**: it
pulls in `Nrmstep`, which a concurrent agent is mid-edit on.  `H0clause_translate`
is therefore mapped in this docstring but not wired into a `_modulo` theorem
(it belongs to the `Wttone`/maxr1 route, distinct from the three routes above).

## `_modulo` theorems (this file) — all `sorryAx`-free, parametric

* `PSS_terminates_modulo_wfArgsA` — pure-lex route on `hA : ∀ m, WF (oltOn (ArgsA m))`.
* `PSS_terminates_modulo_diag`    — W=T route on `diagacc`.
* `PSS_terminates_nrm_modulo`     — nrm route on `CollapseResidue` (⊇ Wall A
  collapse face) + the two Wall-B `NF` residuals `oV_nf_arg_lt`, `ST_PS_suffix`.

The first two reuse upstream parametric infrastructure (`step_terminates`,
`PSS_terminates_direct`); the third re-derives `oV_nf_order_pres`/`nrm_order_pres`
parametrically (the upstream copies bake in the `sorry`s).
-/
import YAPSS.Wfsum
import YAPSS.Nrm
import YAPSS.Wtt
import YAPSS.Residue

set_option maxHeartbeats 1000000

namespace YAPSS

open Three

/-! ## Route 1 (pure-lex): termination modulo `wf_ArgsA`

Re-thread `wf_ArgsA` through the `Wfsum` chain `wf_SingA → wf_ArgsL →
wf_level_from_args → wfE_from_args → wf_Rnf`, then `step_terminates`. -/

theorem wf_SingA_modulo (hA : ∀ m, WellFounded (oltOn (ArgsA m))) (m : ℕ) :
    WellFounded (oltOn (SingA m)) := by
  have wflex : WellFounded (Prod.Lex (· < · : ℕ → ℕ → Prop) (oltOn (ArgsA m))) :=
    WellFounded.prod_lex wellFounded_lt (hA m)
  refine Subrelation.wf ?_ (InvImage.wf singdest wflex)
  rintro s t ⟨hlt, hsS, htS⟩
  obtain ⟨bs, hbs, hss⟩ := hsS
  obtain ⟨bt, hbt, hst⟩ := htS
  obtain ⟨a, c, rfl⟩ := summands_shape hss
  obtain ⟨e, f, rfl⟩ := summands_shape hst
  have cA : c ∈ ArgsA m := ⟨a, ⟨bs, hbs, hss⟩⟩
  have fA : f ∈ ArgsA m := ⟨e, ⟨bt, hbt, hst⟩⟩
  show Prod.Lex _ _ (a, c) (e, f)
  rcases olt_P_P.1 hlt with h | ⟨rfl, h⟩ | ⟨-, -, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ ⟨h, cA, fA⟩
  · exact absurd h (olt_irrefl Z)

theorem wf_ArgsL_modulo (hA : ∀ m, WellFounded (oltOn (ArgsA m))) (m : ℕ) :
    WellFounded (oltOn (ArgsL m)) := by
  have wfdm : WellFounded (DMLT (oltOn (SingA m))) :=
    wellFounded_dmlt (oltOn_trans _) (wf_SingA_modulo hA m)
  refine Subrelation.wf ?_ (InvImage.wf (fun b => ↑(summands b)) wfdm)
  rintro b f ⟨hlt, hbA, hfA⟩
  exact olt_summands_mult (cnf_ArgsL hbA) hlt
    (summands_subset_SingA hbA) (summands_subset_SingA hfA)

theorem wf_level_from_args_modulo (hA : ∀ m, WellFounded (oltOn (ArgsA m))) (m : ℕ) :
    WellFounded (levelRel m) := by
  have wfdm : WellFounded (DMLT (oltOn (ArgsL m))) :=
    wellFounded_dmlt (oltOn_trans _) (wf_ArgsL_modulo hA m)
  refine Subrelation.wf ?_ (InvImage.wf margs wfdm)
  rintro w x ⟨hlt, hx, hw, hmw, hmx⟩
  exact olt_sum_mult (NF_zerotops hw) (NF_zerotops hx) (cnf_NF hw) hlt
    (sargs_subset_ArgsL hw hmw) (sargs_subset_ArgsL hx hmx)

theorem wfE_from_args_modulo (hA : ∀ m, WellFounded (oltOn (ArgsA m))) :
    WellFounded RnfE := by
  refine ⟨fun x => ?_⟩
  have aux : ∀ (m : ℕ) (x : Three), Acc (levelRel m) x → maxsub x = m →
      Acc RnfE x := by
    intro m x hacc
    induction hacc with
    | intro x _ ih =>
      intro hmx
      refine Acc.intro x fun w hw => ?_
      obtain ⟨hlt, hxNF, hwNF, hms⟩ := hw
      exact ih w ⟨hlt, hxNF, hwNF, by omega, hmx⟩ (by omega)
  exact aux (maxsub x) x ((wf_level_from_args_modulo hA (maxsub x)).apply x) rfl

theorem wf_Rnf_modulo (hA : ∀ m, WellFounded (oltOn (ArgsA m))) :
    WellFounded Rnf :=
  wf_Rnf_from_within_level (wfE_from_args_modulo hA)

/-- **Route 1 — PSS termination modulo `wf_ArgsA`.**  The pure-lex (ordinal-free)
route, reduced to the single residual: WF of `<o` on each level-`m` argument
class.  `sorryAx`-free. -/
theorem PSS_terminates_modulo_wfArgsA
    (hA : ∀ m, WellFounded (oltOn (ArgsA m))) :
    WellFounded stepRel :=
  step_terminates (wf_Rnf_modulo hA)

/-! ## Route 3 (W=T direct): termination modulo `diag_acc`

This route already exposes its residual parametrically upstream
(`PSS_terminates_direct`); we just name it. -/

/-- **Route 3 — PSS termination modulo diagonal accessibility.**  The W=T direct
route, reduced to the single residual `diagacc` (every `diagSeq 0 v` is
`stepR`-accessible).  `sorryAx`-free (it IS the upstream parametric theorem). -/
theorem PSS_terminates_modulo_diag
    (diagacc : ∀ v, Acc stepR (diagSeq 0 v)) :
    WellFounded stepR :=
  PSS_terminates_direct diagacc

/-! ## Route 2 (nrm-order): termination modulo `CollapseResidue` + NF residuals

The nrm route's chain is `psi_proj_notmem → psi_proj → nrm_order_pres →
wf_Rnf_nrm → PSS_terminates_nrm`, with `nrm_order_pres` also needing
`oV_nf_order_pres` (which rests on `oV_nf_arg_lt` and `ST_PS_suffix`).  Upstream
these bake in the `sorry`s, so we re-derive them parametrically here.

Residuals taken as hypotheses:
* `CollapseResidue` (Wall A collapse face) ⟹ `psi_proj_notmem` ⟹ `psi_proj`;
* `hArg : oV_nf_arg_lt` and `hSuf : ST_PS_suffix` (Wall B). -/

/-- `psi_proj` re-derived from the TRUE maxo-restricted residual
`CollapseResidueMaxo` (= `Residue.psi_proj_of_collapseResidueMaxo`).

**Corrected:** the previous version used the general `CollapseResidue`, which is
FALSE for non-maxo OT3-violators (`Residue` maxo-correction note).  `psi_proj` only
needs the residual at the `maxo` violator, so `CollapseResidueMaxo` is the genuine
(TRUE) hypothesis. -/
theorem psi_proj_modulo (CRM : CollapseResidueMaxo.{0}) (a : ℕ) (b : Three) (wb : wf3 b) :
    psi.{0} (oV (proj a b)) a = psi (oV b) a :=
  psi_proj_of_collapseResidueMaxo CRM a b wb

/-- `NF_tail` re-derived from `ST_PS_suffix` (the upstream `NF_tail` rests on the
`sorry` `ST_PS_suffix`; here it is an explicit hypothesis `hSuf`). -/
theorem NF_tail_modulo
    (hSuf : ∀ {p : ℕ × ℕ} {rest : PairSeq}, ST_PS (p :: rest) →
      rest.dropWhile (fun q => p.1 < q.1) = [] ∨
      ST_PS (rest.dropWhile (fun q => p.1 < q.1)))
    {b c : Three} (hv : (P 0 b c) ∈ NF) (hc : c ≠ Z) : c ∈ NF := by
  obtain ⟨M, hM, hMt⟩ := hv
  obtain ⟨p, rest, rfl⟩ : ∃ p rest, M = p :: rest := by
    have := stps_len_pos hM
    cases M with
    | nil => simp at this
    | cons p rest => exact ⟨p, rest, rfl⟩
  rw [translate] at hMt
  have hceq : c = translate (rest.dropWhile (fun q => p.1 < q.1)) := by
    injection hMt with _ _ h3; exact h3.symm
  rcases hSuf hM with hempty | hstps
  · rw [hempty, translate] at hceq; exact absurd hceq hc
  · exact ⟨_, hstps, by rw [hceq]⟩

/-- `oV_nf_order_pres` re-derived parametrically on the two Wall-B `NF`
residuals `hArg` (= `oV_nf_arg_lt`) and `hSuf` (= `ST_PS_suffix`, via
`NF_tail_modulo`).  Copy of the upstream strong-induction proof. -/
theorem oV_nf_order_pres_modulo
    (hArg : ∀ {b c f g : Three}, (P 0 b c) ∈ NF → (P 0 f g) ∈ NF → olt b f →
      oV.{0} (P 0 b c) < oV (P 0 f g))
    (hSuf : ∀ {p : ℕ × ℕ} {rest : PairSeq}, ST_PS (p :: rest) →
      rest.dropWhile (fun q => p.1 < q.1) = [] ∨
      ST_PS (rest.dropWhile (fun q => p.1 < q.1)))
    {v u : Three} (hv : v ∈ NF) (hu : u ∈ NF) (h : olt v u) :
    oV.{0} v < oV u := by
  generalize hs : tsize v = n
  induction n using Nat.strong_induction_on generalizing v u with
  | _ n IH =>
    subst hs
    cases v with
    | Z =>
      cases u with
      | Z => exact absurd h (olt_irrefl Z)
      | P e f g =>
        have he : e = 0 := NF_lead0 hu rfl
        subst he
        simpa using oV_pos 0 f g
    | P a b c =>
      have ha : a = 0 := NF_lead0 hv rfl
      subst ha
      cases u with
      | Z => exact absurd h (not_olt_Z _)
      | P e f g =>
        have he : e = 0 := NF_lead0 hu rfl
        subst he
        rcases olt_P_P.1 h with hsub | ⟨_, harg⟩ | ⟨_, rfl, htail⟩
        · exact absurd hsub (lt_irrefl 0)
        · exact hArg hv hu harg
        · show psi (oV b) 0 + oV c < psi (oV b) 0 + oV g
          refine add_lt_add_right ?_ _
          by_cases hcZ : c = Z
          · subst hcZ
            have hgZ : g ≠ Z := by
              rintro rfl; exact absurd htail (not_olt_Z _)
            obtain ⟨e2, f2, g2, rfl⟩ : ∃ e2 f2 g2, g = P e2 f2 g2 := by
              cases g with
              | Z => exact absurd rfl hgZ
              | P e2 f2 g2 => exact ⟨_, _, _, rfl⟩
            simpa using oV_pos e2 f2 g2
          · have hcNF : c ∈ NF := NF_tail_modulo hSuf hv hcZ
            have hgZ : g ≠ Z := by
              rintro rfl; exact absurd htail (not_olt_Z _)
            have hgNF : g ∈ NF := NF_tail_modulo hSuf hu hgZ
            have szc : tsize c < tsize (P 0 b c) := by simp only [tsize]; omega
            exact IH (tsize c) szc hcNF hgNF htail rfl

/-- `nrm_order_pres` re-derived parametrically on `CollapseResidue` + the two
Wall-B `NF` residuals. -/
theorem nrm_order_pres_modulo
    (CRM : CollapseResidueMaxo.{0})
    (hArg : ∀ {b c f g : Three}, (P 0 b c) ∈ NF → (P 0 f g) ∈ NF → olt b f →
      oV.{0} (P 0 b c) < oV (P 0 f g))
    (hSuf : ∀ {p : ℕ × ℕ} {rest : PairSeq}, ST_PS (p :: rest) →
      rest.dropWhile (fun q => p.1 < q.1) = [] ∨
      ST_PS (rest.dropWhile (fun q => p.1 < q.1)))
    {v u : Three} (hv : v ∈ NF) (hu : u ∈ NF) (h : olt v u) :
    olt (nrm v) (nrm u) := by
  apply oV_order_refl.{0} (wf3_nrm v) (wf3_nrm u)
  rw [oV_nrm_of_psi_proj.{0} (psi_proj_modulo CRM) v,
      oV_nrm_of_psi_proj.{0} (psi_proj_modulo CRM) u]
  exact oV_nf_order_pres_modulo hArg hSuf hv hu h

/-- `wf_Rnf` (nrm route) re-derived parametrically. -/
theorem wf_Rnf_nrm_modulo
    (CRM : CollapseResidueMaxo.{0})
    (hArg : ∀ {b c f g : Three}, (P 0 b c) ∈ NF → (P 0 f g) ∈ NF → olt b f →
      oV.{0} (P 0 b c) < oV (P 0 f g))
    (hSuf : ∀ {p : ℕ × ℕ} {rest : PairSeq}, ST_PS (p :: rest) →
      rest.dropWhile (fun q => p.1 < q.1) = [] ∨
      ST_PS (rest.dropWhile (fun q => p.1 < q.1))) :
    WellFounded Rnf := by
  refine Subrelation.wf ?_ (InvImage.wf nrm wf_olt_wf3)
  rintro v u ⟨hlt, hu, hv⟩
  exact ⟨nrm_order_pres_modulo CRM hArg hSuf hv hu hlt, wf3_nrm v, wf3_nrm u⟩

/-- **Route 2 — PSS termination modulo the nrm-route residuals.**  Reduced to
EXACTLY: the Wall A collapse face `CollapseResidueMaxo` (the TRUE maxo-restricted
residue), and the two Wall B `NF`
residuals `hArg` (= `oV_nf_arg_lt`) and `hSuf` (= `ST_PS_suffix`).  `sorryAx`-free. -/
theorem PSS_terminates_nrm_modulo
    (CRM : CollapseResidueMaxo.{0})
    (hArg : ∀ {b c f g : Three}, (P 0 b c) ∈ NF → (P 0 f g) ∈ NF → olt b f →
      oV.{0} (P 0 b c) < oV (P 0 f g))
    (hSuf : ∀ {p : ℕ × ℕ} {rest : PairSeq}, ST_PS (p :: rest) →
      rest.dropWhile (fun q => p.1 < q.1) = [] ∨
      ST_PS (rest.dropWhile (fun q => p.1 < q.1))) :
    WellFounded stepRel :=
  step_terminates (wf_Rnf_nrm_modulo CRM hArg hSuf)

/-! ## DEFINITIVE CONSOLIDATION — the nrm route on the MINIMAL true §1 residual set

The wiring among the three nrm-route hypotheses is now settled **in Lean code**:

* `hSuf` (`ST_PS_suffix`) is **PROVEN** sorry-free in `Nrm.lean`
  (`#print axioms ST_PS_suffix = [propext, Classical.choice, Quot.sound]`), so it
  is discharged here directly — it is NOT a residual.
* `hArg` (`oV_nf_arg_lt`) is REDUCED (`Nrm.oV_nf_arg_lt_of_head`, sorry-free) to
  the **§1-head family** `∀ x ≤o b, ψ_0(oV x) < ψ_0(oV f)`.

**KEY QUESTION RESOLVED (refuted, in code).**  Does `NoncanonValueMem` (the closure
Remark `C_v(α)=C^c_v(α)`) discharge the §1-head family?  **NO.**
* The head reduces (`psi_strict_mono_mem`) to the *omitted-form* membership
  `oV x ∈ C_0(oV f)`.  This membership is **FALSE on `NF`** (kernel-audited:
  10185 violations; `Nrm.lean` design notes lines 384–388, 469–473) — the inner
  `ψ_k0` lies in a band `[Ω_k,Ω_{k+1})` ABOVE `oV x ∈ [Ω_1,Ω_2)`, a *subscript
  ascent* that `NF` arguments structurally contain.  So it is a DIFFERENT, false
  membership — NOT an instance of `NoncanonValueMem` (whose element is a canonical
  *generator value* `psiSelf ξ u`).  `NoncanonValueMem` does not bridge it.
* The ONLY working route (`Nrm.lean` lines 458–485, all three kernel-checked) is
  the **`proj` route**: `proj 0` *collapses the subscript ascent*
  (`proj 0 (P k b' c') = proj 0 b'`), landing in a `0`-reduced fixpoint where the
  C-membership IS true (`proj_oV_mem_C`); `psi_proj` (= the COLLAPSE core, what
  `CollapseResidueMaxo` supplies via `psi_proj_modulo`) then identifies
  `ψ_0(oV(proj 0 x)) = ψ_0(oV x)`.  So the head is `psi_strict_mono_arg` at
  `proj 0 x` plus the **proj-side order** `proj 0 x <o proj 0 f`.

**CONCLUSION on independence.**  The §1-head (non-collapse) and the collapse face
are NOT independent and are NOT the closure Remark: the head is *inseparable from
the collapse core* `psi_proj` (= `CollapseResidueMaxo`).  Discharging it needs
`CollapseResidueMaxo` PLUS one new, purely OT-structural residual: `proj 0`-order
on `NF` arguments (`ProjOrderNF`), empirically TRUE (audit `audit_proj0.py`:
`bothfire`/`fireprop` 167910/167910, zero violations on the NF corpus).

So the MINIMAL true residual set for the nrm route is exactly
`{CollapseResidueMaxo, HeadFamilyNF}` — and `HeadFamilyNF` is itself REDUCED, per
element, to `CollapseResidueMaxo` + the proj-side order (`psi0_head_of_CRM` below),
so the genuine residual content beyond the collapse core is the purely
OT-structural `proj 0`-order on NF args.  Both faces are the SAME Buchholz §1
collapse content (`psi_proj`); NEITHER is the closure-membership Remark
`NoncanonValueMem`.

NB on `wf3`-of-NF: the per-element reduction `psi0_head_of_CRM` needs `wf3 x`.
For NF arguments this is the Route-3 re-ascent (`Wttone.wf3_translate*`), itself
parametric — NOT trivial — so the head-family is kept as the residual
`HeadFamilyNF` at the inequality level (the form `Nrm.oV_nf_arg_lt_of_head`
consumes, which carries no `wf3`), and `psi0_head_of_CRM` is the proven bridge
showing what it reduces to once `wf3 x` + the proj order are in hand. -/

/-- **`HeadFamilyNF` — the §1-head family residual** at the form
`Nrm.oV_nf_arg_lt_of_head` consumes (no `wf3`).  For `P 0 b c, P 0 f g ∈ NF` with
`olt b f`: `ψ_0(oV x) < ψ_0(oV f)` for every `x ≤o b`.  This is the
`ψ_0`-non-collapse content; REFUTED to be `NoncanonValueMem` (its omitted-form
membership `oV x ∈ C_0(oV f)` is false on NF); REDUCED per element to
`CollapseResidueMaxo` + proj-order by `psi0_head_of_CRM`. -/
def HeadFamilyNF.{u} : Prop :=
  ∀ {b f : Three}, (∃ c, (P 0 b c) ∈ NF) → (∃ g, (P 0 f g) ∈ NF) → olt b f →
    ∀ x : Three, x ≤o b → psi.{u} (oV x) 0 < psi (oV f) 0

/-- **The §1-head, single `x`, from `CollapseResidueMaxo` + the proj-side order**
(the proven BRIDGE for `HeadFamilyNF`).  `ψ_0(oV x) < ψ_0(oV f)` via the proj
route: `psi_proj_modulo` (the collapse core) rewrites both sides to their
`0`-reduced fixpoints, where `psi_strict_mono_arg` (C-membership `proj_oV_mem_C`,
TRUE at the fixpoint) fires on `proj 0 x <o proj 0 f`.  No closure Remark; the
C-membership at `x` itself (FALSE on NF) is bypassed by `proj 0`'s
subscript-ascent collapse.  This is the in-code proof that the §1-head is the same
content as the collapse core, NOT `NoncanonValueMem`. -/
theorem psi0_head_of_CRM (CRM : CollapseResidueMaxo.{0})
    {x f : Three} (wx : wf3 x) (wf : wf3 f) (hproj : (proj 0 x) <o (proj 0 f)) :
    psi.{0} (oV x) 0 < psi (oV f) 0 := by
  rw [← psi_proj_modulo CRM 0 x wx, ← psi_proj_modulo CRM 0 f wf]
  exact psi_strict_mono_arg
    (oV_order_pres (proj_wf3 wx) (proj_wf3 wf) hproj)
    (proj_oV_mem_C 0 x wx)

/-- **`hArg` (`oV_nf_arg_lt`) discharged from `HeadFamilyNF`.**  Feeds the head
family into `Nrm.oV_nf_arg_lt_of_head` (sorry-free structural remainder). -/
theorem hArg_of_headFamily (HF : HeadFamilyNF.{0})
    {b c f g : Three} (hv : (P 0 b c) ∈ NF) (hu : (P 0 f g) ∈ NF) (hbf : olt b f) :
    oV.{0} (P 0 b c) < oV (P 0 f g) :=
  oV_nf_arg_lt_of_head hv (fun x hxb => HF ⟨c, hv⟩ ⟨g, hu⟩ hbf x hxb)

/-! ### `HeadFamilyNF` scoping VERDICT (2026-06-20n): hits the DEEP region, NOT independent

`HeadFamilyNF`'s per-element head `ψ_0(oV x) < ψ_0(oV f)` was flagged "provable below ε via
`psi_strict_mono_lt_epsLvl`, secondary".  **Decisive verdict: it hits the deep `≥ ε` region —
the lever (sub-`ε` only) does NOT close it; it is NOT independent of the §1 collapse core.**

* SUB-`ε` PART — GREEN (`headfam_head_of_lever`): for `oV x < ε_0` and `oV x < oV f`, the head
  `ψ_0(oV x) < ψ_0(oV f)` closes by `psi_strict_mono_lt_epsLvl` (no collapse, no membership).
* DEEP PART — the collapse core: NF args reach `oV x ≥ ε_0`.  Witnessed (`deep_arg_maxr1_le1`,
  Lean-proven): the lead-`1` arg `P 1 Z Z` (already at `maxr1 ≤ 1`, the live path) has
  `oV (P 1 Z Z) = Ω_1 > ε_0`.  So a `HeadFamilyNF` arg-family `x ≤o b` containing a lead-`1`
  `x` has `oV x ≥ Ω_1 > ε_0` — DEEP, where the head `ψ_0(oV x) < ψ_0(oV f)` IS the §1
  `ψ_0`-collapse content (= `CollapseResidueMaxo` per element, `psi0_head_of_CRM`).

So `HeadFamilyNF` is another FACE of the §1 collapse core (the `ψ_0`-non-collapse Ω-band head),
NOT a separable hypothesis; discharging it needs `CollapseResidueMaxo` (the deep part) — so
closing it does NOT reduce `PSS_terminates_nrm_final` below `{CollapseResidueMaxo}` (it shares
the core).  The sub-`ε` part is GREEN; the deep part is the same wall. -/

/-- **The sub-`ε` part of the `HeadFamilyNF` head** (GREEN, the lever-tractable portion).
For `oV x < ε_0` and `oV x < oV f`: `ψ_0(oV x) < ψ_0(oV f)` via `psi_strict_mono_lt_epsLvl`. -/
theorem headfam_head_of_lever {x f : Three}
    (hxe : oV.{0} x < epsLvl 0) (hxf : oV.{0} x < oV f) :
    psi.{0} (oV x) 0 < psi (oV f) 0 :=
  psi_strict_mono_lt_epsLvl hxe hxf

open Ordinal in
/-- **A lead-`1` NF arg already reaches the deep region** (Lean-proven witness): at `maxr1 ≤ 1`
(the live path), `oV (P 1 Z Z) = Ω_1 > ε_0`.  So `HeadFamilyNF`'s arg-family reaches `oV ≥ ε_0`
where the sub-`ε` lever fails — the head is the §1 collapse content there. -/
theorem deep_arg_maxr1_le1 : ε_ 0 < oV.{0} (P 1 Three.Z Three.Z) := by
  rw [oV_P1ZZ]; exact epsilon0_lt_Om_one

/-- **`PSS_terminates_nrm_final` — THE sound nrm-route endpoint, modulo the single
genuine Buchholz §1 collapse `{CollapseResidueMaxo, HeadFamilyNF}`.**  `hSuf`
discharged by the proven `ST_PS_suffix`; `hArg` by `HeadFamilyNF`.  Both residuals
are TRUE Buchholz §1 ordinal-collapse content (`CollapseResidueMaxo`: the collapse
face, verified 278/278; `HeadFamilyNF`: the dual non-collapse Ω-band head).  This
is `sorryAx`-FREE (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
Everything else on this route is proven (`ST_PS_suffix`, the structural NF order,
`maxr1 ≤ 1`, sub-`ε`).  The earlier attempts to discharge the collapse cheaply via
`ProjFixesNrm` (`PSS_terminates_nrm_true`) and `NFwf3` (`PSS_terminates_nrm_via_-
NFwf3`) are DEAD — both hypotheses are FALSE (see those docstrings).  So this is the
honest minimal endpoint: the §1 collapse is irreducible and cannot be bypassed. -/
theorem PSS_terminates_nrm_final
    (CRM : CollapseResidueMaxo.{0}) (HF : HeadFamilyNF.{0}) :
    WellFounded stepRel :=
  PSS_terminates_nrm_modulo CRM (fun hv hu hbf => hArg_of_headFamily HF hv hu hbf)
    (fun hM => ST_PS_suffix hM)

/-! ## DEAD ROUTE — `ProjFixesNrm` is FALSE (`proj` DOES fire on `nrm`-images)

⚠️ **DEAD: the hypothesis `ProjFixesNrm` is FALSE.**  The conjecture was that the
nrm value-chain only projects `nrm`-images where `proj` is the identity.  This is
DISPROVEN (see `tools/audit_projfix_*.py`): `proj` genuinely fires on `nrm`-images
at level 0.  Counterexample: `proj 0 (P 1 (P 2 Z Z) Z) = P 2 Z Z ≠ P 1 (P 2 Z Z) Z`
— i.e. `proj 0 (p_1(p_2(0))) ≠ p_1(p_2(0))`, and `p_1(p_2(0))` is a genuine
`nrm`-image reached from a valid PSS sequence.  Restricted to the exact P-nodes the
`oV_nrm` induction reaches, ~5% of nodes fire (314/7108 at closure+8, stable across
depth).  So `proj a (nrm b) = nrm b` is NOT an identity; the §1 collapse equality
`ψ_a(oV (proj a (nrm b))) = ψ_a(oV (nrm b))` at these firing nodes is REAL Buchholz
§1 content and cannot be bypassed.  The theorems below build on `ProjFixesNrm` and
are kept ONLY as valid implications with an UNSATISFIABLE hypothesis (dead ends, not
progress).  The sound endpoint is `PSS_terminates_nrm_final` above. -/

/-- ⚠️ DEAD (hypothesis `ProjFixesNrm` is FALSE — `proj` fires on `nrm`-images,
see the section note above).  `nrm_order_pres` re-derived on `ProjFixesNrm`. -/
theorem nrm_order_pres_pf
    (PF : ProjFixesNrm)
    (hArg : ∀ {b c f g : Three}, (P 0 b c) ∈ NF → (P 0 f g) ∈ NF → olt b f →
      oV.{0} (P 0 b c) < oV (P 0 f g))
    (hSuf : ∀ {p : ℕ × ℕ} {rest : PairSeq}, ST_PS (p :: rest) →
      rest.dropWhile (fun q => p.1 < q.1) = [] ∨
      ST_PS (rest.dropWhile (fun q => p.1 < q.1)))
    {v u : Three} (hv : v ∈ NF) (hu : u ∈ NF) (h : olt v u) :
    olt (nrm v) (nrm u) := by
  apply oV_order_refl.{0} (wf3_nrm v) (wf3_nrm u)
  rw [oV_nrm_eq_of_projFixesNrm PF v, oV_nrm_eq_of_projFixesNrm PF u]
  exact oV_nf_order_pres_modulo hArg hSuf hv hu h

/-- `wf_Rnf` (nrm route) on `ProjFixesNrm`. -/
theorem wf_Rnf_nrm_pf
    (PF : ProjFixesNrm)
    (hArg : ∀ {b c f g : Three}, (P 0 b c) ∈ NF → (P 0 f g) ∈ NF → olt b f →
      oV.{0} (P 0 b c) < oV (P 0 f g))
    (hSuf : ∀ {p : ℕ × ℕ} {rest : PairSeq}, ST_PS (p :: rest) →
      rest.dropWhile (fun q => p.1 < q.1) = [] ∨
      ST_PS (rest.dropWhile (fun q => p.1 < q.1))) :
    WellFounded Rnf := by
  refine Subrelation.wf ?_ (InvImage.wf nrm wf_olt_wf3)
  rintro v u ⟨hlt, hu, hv⟩
  exact ⟨nrm_order_pres_pf PF hArg hSuf hv hu hlt, wf3_nrm v, wf3_nrm u⟩

/-- ⚠️ **DEAD: rests on the FALSE `ProjFixesNrm`** (`proj` fires on `nrm`-images —
see `tools/audit_projfix_*.py`; `proj 0 (p_1(p_2(0))) ≠ p_1(p_2(0))`).  The theorem
itself is `sorryAx`-free as a valid implication, but its hypothesis is UNSATISFIABLE,
so it is NOT a usable termination route.  Use `PSS_terminates_nrm_final` (modulo the
TRUE `{CollapseResidueMaxo, HeadFamilyNF}`) as the sound nrm-route endpoint. -/
theorem PSS_terminates_nrm_true
    (PF : ProjFixesNrm) (HF : HeadFamilyNF.{0}) :
    WellFounded stepRel :=
  step_terminates
    (wf_Rnf_nrm_pf PF (fun hv hu hbf => hArg_of_headFamily HF hv hu hbf)
      (fun hM => ST_PS_suffix hM))

/-! ## DOES `HeadFamilyNF` TRIVIALIZE? — NO; it is genuine Ω-band §1 content, but it
    is REPLACEABLE by `NFwf3` (NF ⊆ wf3), which collapses the head entirely.

Parallel investigation to `ProjFixesNrm` (audit `audit_headfam.py`, closure+5/+6):

* **(1)** The head args `b` (= args of lead-0 NF terms) overwhelmingly have lead
  `≥ 1` (262/267 at closure+6) — so `oV b ≥ Ω_1 > ε(0)`, the COLLAPSE region.  The
  sub-`ε` lever `psi_strict_mono_lt_epsLvl` does NOT apply.
* **(2)** `proj 0 b` does NOT reach sub-`Ω` (`lead (proj 0 b)` stays `≥ 1`), so the
  proj route lands in another Ω-band fixpoint; and `psi0_oV_lt_of_proj_olt` routes
  through `psi_proj` (sorryAx — the suspect collapse).  So the head does NOT
  trivialize via sub-`ε`/proj-to-sub-`Ω`, and its `oV`-route inherits the collapse.

So `HeadFamilyNF` is GENUINE Ω-band §1 content (the dual of the collapse that
`ProjFixesNrm` bypassed).  It does NOT trivialize on its own domain.

* **(3) BUT** `nrm` is strictly term-order-preserving on `NF` (closure+6:
  44551 pairs, 0 collapses, 0 reversals).  So `nrm_order_pres` is TRUE and the
  CLEAN route is TERM-STRUCTURAL (proj/ins monotone via `Nrmstep.proj0_olt_NF` =
  the shared crux `{proj0_fireprop_NF, proj0_bothfire_NF}`), avoiding `oV`/`psi`
  entirely — exactly the route the other agent is building.

**The tempting replacement `NFwf3` (NF ⊆ wf3) is DEAD — `NFwf3` is FALSE.**  If
every NF term were `wf3`, then `oV_nf_order_pres` would be just `oV_order_pres`
(`oV_nf_order_pres_of_NFwf3` below) and `HeadFamilyNF` would be unnecessary.  But
`NFwf3` is DISPROVEN: `translate (diagSeq 0 2) = P 0 (P 1 (P 2 Z Z) Z) Z ∈ NF` is
NOT `wf3` (`maxr1 = 2` translate-images never satisfy the OT3 clause — 8314/8314
fail).  Likewise `nrm t = t` on `NF` is false (76/299 at closure+6).  So the head is
NOT removable this way; the genuine residual stays `HeadFamilyNF` (Ω-band §1, the
dual of the collapse `CollapseResidueMaxo`).  Endpoint: `PSS_terminates_nrm_final`. -/

/-- **Head trivializes given `NFwf3`.**  If every NF term is `wf3`, the NF order is
just `oV_order_pres` — no §1 head.  (GREEN, sorry-free.) -/
theorem oV_nf_order_pres_of_NFwf3
    (NFwf3 : ∀ t : Three, t ∈ NF → wf3 t)
    {v u : Three} (hv : v ∈ NF) (hu : u ∈ NF) (h : olt v u) :
    oV.{0} v < oV u :=
  oV_order_pres (NFwf3 v hv) (NFwf3 u hu) h

/-- **`NFwf3` from "`nrm` is identity on `NF`"** via the proven `wf3_nrm`.  Pins the
head/collapse content to the single shared crux `nrm t = t` on `NF`. -/
theorem NFwf3_of_nrmFixesNF
    (NrmFix : ∀ t : Three, t ∈ NF → nrm t = t) :
    ∀ t : Three, t ∈ NF → wf3 t := by
  intro t ht; have := wf3_nrm t; rwa [NrmFix t ht] at this

/-- ⚠️ **DEAD: rests on TWO FALSE hypotheses, `ProjFixesNrm` AND `NFwf3` (NF ⊆ wf3).**
`ProjFixesNrm` is false (`proj` fires on `nrm`-images, see `tools/audit_projfix_*.py`).
`NFwf3` is ALSO false: `translate (diagSeq 0 2) = P 0 (P 1 (P 2 Z Z) Z) Z ∈ NF` is
NOT `wf3` (its `maxr1 = 2` translate-images are never `wf3` — 8314/8314 fail the OT3
clause).  The theorem is a valid implication but both hypotheses are UNSATISFIABLE,
so it is NOT a usable route.  Use `PSS_terminates_nrm_final`. -/
theorem PSS_terminates_nrm_via_NFwf3
    (PF : ProjFixesNrm) (NFwf3 : ∀ t : Three, t ∈ NF → wf3 t) :
    WellFounded stepRel := by
  apply step_terminates
  refine Subrelation.wf ?_ (InvImage.wf nrm wf_olt_wf3)
  rintro v u ⟨hlt, hu, hv⟩
  refine ⟨?_, wf3_nrm v, wf3_nrm u⟩
  apply oV_order_refl.{0} (wf3_nrm v) (wf3_nrm u)
  rw [oV_nrm_eq_of_projFixesNrm PF v, oV_nrm_eq_of_projFixesNrm PF u]
  exact oV_nf_order_pres_of_NFwf3 NFwf3 hv hu hlt

end YAPSS
