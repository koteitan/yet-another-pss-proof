/-
# `YAPSS.Reduction` — termination modulo named residues (the sorry dependency map)

This downstream assembly file makes the whole development's reduction status
**legible**: it re-derives each top-level PSS-termination route *parametrically*
on its explicit residual hypotheses, so that each `_modulo` theorem below is
itself `sorryAx`-FREE (the `sorry`s live only in the upstream non-parametric
copies).  Nothing upstream is edited (that would create an import cycle); we add
a fresh assembly layer.

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

/-- `psi_proj` re-derived from `CollapseResidue` (= `Residue` glue + `Nrm`'s
`psi_proj_of_notmem`). -/
theorem psi_proj_modulo (CR : CollapseResidue.{0}) (a : ℕ) (b : Three) (wb : wf3 b) :
    psi.{0} (oV (proj a b)) a = psi (oV b) a :=
  psi_proj_of_collapseResidue CR a b wb

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
    (CR : CollapseResidue.{0})
    (hArg : ∀ {b c f g : Three}, (P 0 b c) ∈ NF → (P 0 f g) ∈ NF → olt b f →
      oV.{0} (P 0 b c) < oV (P 0 f g))
    (hSuf : ∀ {p : ℕ × ℕ} {rest : PairSeq}, ST_PS (p :: rest) →
      rest.dropWhile (fun q => p.1 < q.1) = [] ∨
      ST_PS (rest.dropWhile (fun q => p.1 < q.1)))
    {v u : Three} (hv : v ∈ NF) (hu : u ∈ NF) (h : olt v u) :
    olt (nrm v) (nrm u) := by
  apply oV_order_refl.{0} (wf3_nrm v) (wf3_nrm u)
  rw [oV_nrm_of_psi_proj.{0} (psi_proj_modulo CR) v,
      oV_nrm_of_psi_proj.{0} (psi_proj_modulo CR) u]
  exact oV_nf_order_pres_modulo hArg hSuf hv hu h

/-- `wf_Rnf` (nrm route) re-derived parametrically. -/
theorem wf_Rnf_nrm_modulo
    (CR : CollapseResidue.{0})
    (hArg : ∀ {b c f g : Three}, (P 0 b c) ∈ NF → (P 0 f g) ∈ NF → olt b f →
      oV.{0} (P 0 b c) < oV (P 0 f g))
    (hSuf : ∀ {p : ℕ × ℕ} {rest : PairSeq}, ST_PS (p :: rest) →
      rest.dropWhile (fun q => p.1 < q.1) = [] ∨
      ST_PS (rest.dropWhile (fun q => p.1 < q.1))) :
    WellFounded Rnf := by
  refine Subrelation.wf ?_ (InvImage.wf nrm wf_olt_wf3)
  rintro v u ⟨hlt, hu, hv⟩
  exact ⟨nrm_order_pres_modulo CR hArg hSuf hv hu hlt, wf3_nrm v, wf3_nrm u⟩

/-- **Route 2 — PSS termination modulo the nrm-route residuals.**  Reduced to
EXACTLY: the Wall A collapse face `CollapseResidue`, and the two Wall B `NF`
residuals `hArg` (= `oV_nf_arg_lt`) and `hSuf` (= `ST_PS_suffix`).  `sorryAx`-free. -/
theorem PSS_terminates_nrm_modulo
    (CR : CollapseResidue.{0})
    (hArg : ∀ {b c f g : Three}, (P 0 b c) ∈ NF → (P 0 f g) ∈ NF → olt b f →
      oV.{0} (P 0 b c) < oV (P 0 f g))
    (hSuf : ∀ {p : ℕ × ℕ} {rest : PairSeq}, ST_PS (p :: rest) →
      rest.dropWhile (fun q => p.1 < q.1) = [] ∨
      ST_PS (rest.dropWhile (fun q => p.1 < q.1))) :
    WellFounded stepRel :=
  step_terminates (wf_Rnf_nrm_modulo CR hArg hSuf)

end YAPSS
