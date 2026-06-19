/-
**[B] The C-rank measure (Buchholz §1 canonical-representation construction).**

The deep-region §1 residue (gap-cleanness, the honest residue from the prior
soundness fix) is to be established via Buchholz's `G_uγ` device + Lemma 1.9
(`γ ∈ C_u(α) ⟺ G_uγ ⊆ α`).  `G_u` is defined by recursion on the **C-rank**
`min{n : γ ∈ (CstepSelf')^[n] (Iio (Om v))}` — NOT on the ordinal `γ`, because in
the deep collapse region a generator argument `η` can satisfy `η ≥ ψ_v η = ξ` as an
ordinal (`AcanonLtValue` is FALSE there), so ordinal well-foundedness fails.  The
C-rank strictly drops on generator arguments (`crank_arg_lt`), which is THE
well-founded measure for the `G_u` recursion and the Lemma-1.9 induction.

This file builds [B]: `crank`, its spec/minimality, and the strict-drop.  All
sorryAx-free.  Soundness note: every fact here is about the genuine ordinal closure
`CsetSelf`, proven in Lean — NO `lt_term`/term-model input (which is unfaithful to
`psiSelf` order, the standing law from the hVB soundness fix).
-/
import YAPSS.Residue

namespace YAPSS
open Ordinal Classical

theorem self_subset_CstepSelf' (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u})
    (X : Set Ordinal.{u}) : X ⊆ CstepSelf' p α X :=
  fun _ hx => Set.mem_union_left _ (Set.mem_union_left _ hx)

theorem CiterSelf_le_succ (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v n : ℕ) :
    (CstepSelf' p α)^[n] (Set.Iio (Om v)) ⊆ (CstepSelf' p α)^[n+1] (Set.Iio (Om v)) := by
  rw [Function.iterate_succ_apply']; exact self_subset_CstepSelf' p α _

theorem CiterSelf_mono_index (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ)
    {m n : ℕ} (hmn : m ≤ n) :
    (CstepSelf' p α)^[m] (Set.Iio (Om v)) ⊆ (CstepSelf' p α)^[n] (Set.Iio (Om v)) := by
  induction hmn with
  | refl => exact subset_rfl
  | step h ih => exact subset_trans ih (CiterSelf_le_succ p α v _)

def crankPred (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ)
    (γ : Ordinal.{u}) (n : ℕ) : Prop :=
  γ ∈ (CstepSelf' p α)^[n] (Set.Iio (Om v))

noncomputable def crank (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ)
    (γ : Ordinal.{u}) : ℕ :=
  if h : ∃ n, crankPred p α v γ n then Nat.find h else 0

theorem crank_spec {p : Ordinal.{u} → ℕ → Ordinal.{u}} {α : Ordinal.{u}} {v : ℕ}
    {γ : Ordinal.{u}} (h : γ ∈ CsetSelf p α v) :
    γ ∈ (CstepSelf' p α)^[crank p α v γ] (Set.Iio (Om v)) := by
  have hex : ∃ n, crankPred p α v γ n := CsetSelf_mem_iff.1 h
  rw [crank, dif_pos hex]; exact Nat.find_spec hex

theorem crank_min {p : Ordinal.{u} → ℕ → Ordinal.{u}} {α : Ordinal.{u}} {v : ℕ}
    {γ : Ordinal.{u}} {m : ℕ} (hm : γ ∈ (CstepSelf' p α)^[m] (Set.Iio (Om v))) :
    crank p α v γ ≤ m := by
  have hex : ∃ n, crankPred p α v γ n := ⟨m, hm⟩
  rw [crank, dif_pos hex]; exact Nat.find_le hm

theorem crank_not_lt {p : Ordinal.{u} → ℕ → Ordinal.{u}} {α : Ordinal.{u}} {v : ℕ}
    {γ : Ordinal.{u}} {m : ℕ} (hm : m < crank p α v γ) :
    γ ∉ (CstepSelf' p α)^[m] (Set.Iio (Om v)) :=
  fun hmem => absurd (crank_min hmem) (not_le.2 hm)

theorem crank_arg_lt {α η : Ordinal.{u}} {v w : ℕ}
    (hηα : η < α)
    (hlo : Om v ≤ psiSelf η w)
    (hξ : psiSelf η w ∈ CsetSelf (psiResSelf α) α v)
    (hηc : η ∈ CsetSelf (psiResSelf η) η w) :
    crank (psiResSelf α) α v η < crank (psiResSelf α) α v (psiSelf η w) := by
  set ξ := psiSelf η w with hξdef
  have hk : ∃ k, crank (psiResSelf α) α v ξ = k + 1 := by
    rcases Nat.eq_zero_or_pos (crank (psiResSelf α) α v ξ) with h0 | hpos
    · exfalso
      have := crank_spec hξ
      rw [h0, Function.iterate_zero, id_eq] at this
      exact absurd this (not_lt.2 hlo)
    · exact ⟨crank (psiResSelf α) α v ξ - 1, by omega⟩
  obtain ⟨k, hkeq⟩ := hk
  have hξk1 : ξ ∈ (CstepSelf' (psiResSelf α) α)^[k+1] (Set.Iio (Om v)) := by
    have := crank_spec hξ; rwa [hkeq] at this
  have hξnk : ξ ∉ (CstepSelf' (psiResSelf α) α)^[k] (Set.Iio (Om v)) :=
    crank_not_lt (by omega)
  rw [Function.iterate_succ_apply'] at hξk1
  -- the goal: crank η < crank ξ = k+1, i.e. crank η ≤ k, i.e. η ∈ iterate^[k]
  suffices hηk : η ∈ (CstepSelf' (psiResSelf α) α)^[k] (Set.Iio (Om v)) by
    have : crank (psiResSelf α) α v η ≤ k := crank_min hηk
    omega
  rcases hξk1 with (h1 | h2) | h3
  · exact absurd h1 hξnk
  · -- add step: ξ = a + b additively principal ⟹ contradiction
    exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_image2.1 h2
    have hane : a ≠ ξ := fun he => hξnk (he ▸ ha)
    have hbne : b ≠ ξ := fun he => hξnk (he ▸ hb)
    have hale : a ≤ ξ := hab ▸ le_self_add
    have hble : b ≤ ξ := hab ▸ le_add_self
    have halt : a < ξ := lt_of_le_of_ne hale hane
    have hblt : b < ξ := lt_of_le_of_ne hble hbne
    have : a + b < ξ := (psiSelf_addprinc η w).2 a b halt hblt
    rw [hab] at this; exact lt_irrefl _ this
  · -- generator step
    obtain ⟨u, hu⟩ := Set.mem_iUnion.1 h3
    obtain ⟨η', ⟨hη'k, ⟨hη'α, hη'c⟩⟩, hη'x⟩ := hu
    simp only [psiResSelf, if_pos hη'α] at hη'x
    -- hη'x : psiSelf η' u = ξ = psiSelf η w
    have hval : psiSelf η' u = psiSelf η w := hη'x
    -- band forces u = w
    have hu_w : u = w := by
      have h1u : Om u ≤ psiSelf η w := by rw [← hval]; exact Om_le_psiSelf η' u
      have h2u : psiSelf η w < Om (u + 1) := by rw [← hval]; exact psiSelf_lt_Om_succ η' u
      have h1w : Om w ≤ psiSelf η w := Om_le_psiSelf η w
      have h2w : psiSelf η w < Om (w + 1) := psiSelf_lt_Om_succ η w
      by_contra hne
      rcases Nat.lt_or_ge u w with huw | hwu
      · exact absurd (lt_of_le_of_lt h1w h2u) (not_lt.2 (Om_mono (by omega)))
      · have : w < u := by omega
        exact absurd (lt_of_le_of_lt h1u h2w) (not_lt.2 (Om_mono (by omega)))
    subst hu_w
    -- now psiSelf η' u = psiSelf η u with both canonical ⟹ η' = η
    have hη'c_self : η' ∈ CsetSelf (psiResSelf η') η' u :=
      CsetSelf_mono_param _ _ η' u
        (fun ζ uu hζ => by rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hη'α)]) hη'c
    have : η' = η := psiSelf_canonical_inj hη'c_self hηc hval
    subst this
    exact hη'k

/-- **Crank-strong-induction structural principle for `CsetSelf` members.**  To prove
a predicate `Q ξ` for every `ξ ∈ CsetSelf (psiResSelf α) α v`, handle each closure
constructor with the IH available at STRICTLY SMALLER C-rank (iterate stage):
  - base: `ξ < Om v`;
  - sum: `ξ = a + b`, both already in the closure (`Q a`, `Q b`);
  - generator: `ξ = psiSelf η w`, `η < α`, `η` `w`-canonical, in the closure (`Q η`)
    — the strict drop is the generator's argument appearing one stage earlier
    (`crank_arg_lt` is the explicit-measure form of this).
This is the engine for Lemma 1.9 / gap-cleanness, founded on the C-rank (NOT ordinal
order, which fails in the deep region: `η ≥ ψ_v η` possible there). -/
theorem CsetSelf_crank_induction {α : Ordinal.{u}} {v : ℕ}
    (Q : Ordinal.{u} → Prop)
    (hbase : ∀ ξ, ξ < Om v → Q ξ)
    (hsum : ∀ a b, a ∈ CsetSelf (psiResSelf α) α v → b ∈ CsetSelf (psiResSelf α) α v →
      Q a → Q b → Q (a + b))
    (hgen : ∀ η w, η < α → η ∈ CsetSelf (psiResSelf α) α v →
      η ∈ CsetSelf (psiResSelf η) η w → Q η → Q (psiSelf η w)) :
    ∀ ξ, ξ ∈ CsetSelf (psiResSelf α) α v → Q ξ := by
  intro ξ hξ
  obtain ⟨N, hN⟩ := CsetSelf_mem_iff.1 hξ
  clear hξ
  induction N using Nat.strong_induction_on generalizing ξ with
  | _ N IH =>
    cases N with
    | zero =>
      simp only [Function.iterate_zero, id_eq] at hN
      exact hbase ξ hN
    | succ n =>
      rw [Function.iterate_succ_apply'] at hN
      rcases hN with (h1 | h2) | h3
      · exact IH n (Nat.lt_succ_self n) ξ h1
      · obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_image2.1 h2
        subst hab
        have haC : a ∈ CsetSelf (psiResSelf α) α v := CiterSelf_subset_CsetSelf ha
        have hbC : b ∈ CsetSelf (psiResSelf α) α v := CiterSelf_subset_CsetSelf hb
        exact hsum a b haC hbC (IH n (Nat.lt_succ_self n) a ha) (IH n (Nat.lt_succ_self n) b hb)
      · obtain ⟨w, hu⟩ := Set.mem_iUnion.1 h3
        obtain ⟨η, ⟨hηn, ⟨hηα, hηc⟩⟩, hηx⟩ := hu
        simp only [psiResSelf, if_pos hηα] at hηx
        subst hηx
        have hηC : η ∈ CsetSelf (psiResSelf α) α v := CiterSelf_subset_CsetSelf hηn
        have hηc_self : η ∈ CsetSelf (psiResSelf η) η w :=
          CsetSelf_mono_param _ _ η w
            (fun ζ uu hζ => by rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hηα)]) hηc
        exact hgen η w hηα hηC hηc_self (IH n (Nat.lt_succ_self n) η hηn)

/-! ### [D] Lemma 1.9 generator case — the bound-checkable membership of a ψ-value -/

/-- **Lemma 1.9 generator-case NECESSITY** (self-form, Buchholz 1.4(c)/1.9): if the
`u`-canonical value `ψ^s_u η` (`η` `u`-canonical) lies in `CsetSelf (psiResSelf β) β v`
with `v ≤ u`, then its argument `η < β` and `η ∈ CsetSelf (psiResSelf β) β v`.  This is
the bound-checkable membership of a ψ-value (the `G_uγ ⊆ α` content at the generator
node).  Proof: `CsetSelf_witness_canonical` (1.4b) extracts a canonical generator
`ξ < β` with `ψ_{u'}ξ = ψ_u η`; the band forces `u' = u`; injectivity
(`psiSelf_canonical_inj`) forces `ξ = η`. -/
theorem psiValue_mem_imp_arg_lt {β η : Ordinal.{u}} {u v : ℕ} (hvu : v ≤ u)
    (hηc : η ∈ CsetSelf (psiResSelf η) η u)
    (hmem : psiSelf η u ∈ CsetSelf (psiResSelf β) β v) :
    η < β ∧ η ∈ CsetSelf (psiResSelf β) β v := by
  have hlo : Om v ≤ psiSelf η u := le_trans (Om_mono hvu) (Om_le_psiSelf η u)
  have hap : Ordinal.IsPrincipal (· + ·) (psiSelf η u) :=
    fun {x y} hx hy => (psiSelf_addprinc η u).2 x y hx hy
  obtain ⟨u', ξ, heq, hξβ, hξmem, hξc⟩ := CsetSelf_witness_canonical hap hlo hmem
  rw [psiResSelf, if_pos hξβ] at heq
  have hu' : u' = u := by
    have h1 : Om u' ≤ psiSelf η u := heq ▸ Om_le_psiSelf ξ u'
    have h2 : psiSelf η u < Om (u' + 1) := heq ▸ psiSelf_lt_Om_succ ξ u'
    have hle1 : u' ≤ u := by
      by_contra hc
      exact absurd (lt_of_le_of_lt h1 (psiSelf_lt_Om_succ η u)) (not_lt.2 (Om_mono (by omega)))
    have hle2 : u ≤ u' := by
      by_contra hc
      exact absurd (lt_of_le_of_lt (Om_le_psiSelf η u) h2) (not_lt.2 (Om_mono (by omega)))
    omega
  subst hu'
  have hξc_self : ξ ∈ CsetSelf (psiResSelf ξ) ξ u' :=
    CsetSelf_mono_param _ _ ξ u'
      (fun ζ uu hζ => by rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hξβ)]) hξc
  have hξη : ξ = η := psiSelf_canonical_inj hξc_self hηc heq.symm
  subst hξη
  exact ⟨hξβ, hξmem⟩

/-! ### [C\'] The bound-free `Gset` (Buchholz `G_uγ`) and Lemma 1.9

`Gset u γ` = Buchholz's `G_uγ` (Def. before 1.9): the finite-support set of canonical
generator arguments whose values build `γ`, defined bound-FREE.  Well-founded by
ORDINAL recursion: for a self-canonical principal `γ = psiSelf ξ w` the witness `ξ < γ`
(`CsetSelf_witness_canonical`), and additive components are `< γ` — so ordinal order
suffices HERE (the deep-region `η ≥ ψ_v η` failure is at the OUTER bound, not the
self-bound; `Gset` reads off the self-bound derivation).  Lemma 1.9
`γ ∈ C_u(α) ⟺ Gset u γ ⊆ Iio α` then makes membership bound-checkable. -/

open Classical in
/-- **Buchholz `G_uγ`** (bound-free), by ordinal WF recursion.  Principal
`γ = psiSelf ξ w` (witness `ξ < γ`): `insert ξ (Gset u ξ)` if `u ≤ w` else `∅`.
Non-principal `γ ≠ 0`: union of the two additive components' `Gset`.  `γ = 0` or no
witness: `∅`. -/
noncomputable def Gset (u : ℕ) : Ordinal.{v} → Set Ordinal.{v} :=
  Ordinal.lt_wf.fix fun γ IH =>
    if hpr : Ordinal.IsPrincipal (· + ·) γ then
      if hex : ∃ (w : ℕ) (ξ : Ordinal.{v}), γ = psiSelf ξ w ∧ ξ < γ ∧
                 ξ ∈ CsetSelf (psiResSelf ξ) ξ w then
        let pf := hex.choose_spec
        let pf2 := pf.choose_spec
        if u ≤ hex.choose then insert pf.choose (IH pf.choose pf2.2.1) else ∅
      else ∅
    else
      if hne : γ ≠ 0 then
        let dec := Ordinal.exists_lt_add_of_not_isPrincipal_add hpr
        let pa := dec.choose_spec
        let pb := pa.2.choose_spec
        IH dec.choose pa.1 ∪ IH pa.2.choose pb.1
      else ∅

open Classical in
theorem Gset_unfold (u : ℕ) (γ : Ordinal.{v}) :
    Gset u γ =
    (if hpr : Ordinal.IsPrincipal (· + ·) γ then
      if hex : ∃ (w : ℕ) (ξ : Ordinal.{v}), γ = psiSelf ξ w ∧ ξ < γ ∧
                 ξ ∈ CsetSelf (psiResSelf ξ) ξ w then
        (if u ≤ hex.choose then insert hex.choose_spec.choose (Gset u hex.choose_spec.choose)
          else ∅)
      else ∅
    else
      if hne : γ ≠ 0 then
        (let dec := Ordinal.exists_lt_add_of_not_isPrincipal_add hpr
         Gset u dec.choose ∪ Gset u dec.choose_spec.2.choose)
      else ∅) := by
  conv_lhs => rw [Gset, Ordinal.lt_wf.fix_eq]
  rfl

/-- Uniqueness of the canonical ψ-representation: `psiSelf ξ w = psiSelf ξ' w'` with both
args self-canonical ⟹ `w = w'` and `ξ = ξ'`. -/
theorem psiSelf_rep_unique {γ ξ ξ' : Ordinal.{v}} {w w' : ℕ}
    (h1 : γ = psiSelf ξ w) (h2 : γ = psiSelf ξ' w')
    (hξc : ξ ∈ CsetSelf (psiResSelf ξ) ξ w) (hξ'c : ξ' ∈ CsetSelf (psiResSelf ξ') ξ' w') :
    w = w' ∧ ξ = ξ' := by
  have hval : psiSelf ξ w = psiSelf ξ' w' := by rw [← h1, h2]
  have hww : w = w' := by
    have b2 : γ < Om (w+1) := h1 ▸ psiSelf_lt_Om_succ ξ w
    have b1 : Om w ≤ γ := h1 ▸ Om_le_psiSelf ξ w
    have b4 : γ < Om (w'+1) := h2 ▸ psiSelf_lt_Om_succ ξ' w'
    have b3 : Om w' ≤ γ := h2 ▸ Om_le_psiSelf ξ' w'
    by_contra hne
    rcases Nat.lt_or_ge w w' with h | h
    · exact absurd (lt_of_le_of_lt b3 b2) (not_lt.2 (Om_mono (by omega)))
    · have : w' < w := by omega
      exact absurd (lt_of_le_of_lt b1 b4) (not_lt.2 (Om_mono (by omega)))
  subst hww
  exact ⟨rfl, psiSelf_canonical_inj hξc hξ'c hval⟩

open Classical in
/-- **`Gset` generator case** (clean): `γ = psiSelf ξ w` principal, `ξ < γ`
self-canonical ⟹ `Gset u γ = insert ξ (Gset u ξ)` if `u ≤ w`, else `∅`. -/
theorem Gset_gen {u w : ℕ} {ξ γ : Ordinal.{v}} (hpr : Ordinal.IsPrincipal (·+·) γ)
    (heq : γ = psiSelf ξ w) (hξγ : ξ < γ) (hξc : ξ ∈ CsetSelf (psiResSelf ξ) ξ w) :
    Gset u γ = if u ≤ w then insert ξ (Gset u ξ) else ∅ := by
  rw [Gset_unfold, dif_pos hpr]
  have hex : ∃ (w : ℕ) (ξ : Ordinal.{v}), γ = psiSelf ξ w ∧ ξ < γ ∧
               ξ ∈ CsetSelf (psiResSelf ξ) ξ w := ⟨w, ξ, heq, hξγ, hξc⟩
  rw [dif_pos hex]
  have spec := hex.choose_spec.choose_spec
  obtain ⟨hwval, hceq⟩ := psiSelf_rep_unique spec.1 heq spec.2.2 hξc
  rw [hceq, hwval]

/-! ### [D\'] Lemma 1.9 sub-ε generator + the no-realizer reduction of the collapse

`Gset` faithfully reads the canonical generator structure precisely WHERE the canonical
witness sits below the value (`ξ < γ`).  That holds unconditionally in the sub-ε region
(`AcanonLtValue_lt_epsLvl`: `η < ψ_u η`), so `Gset_gen` fires there with `ξ = η`.  In the
DEEP region (`η ≥ ψ_w η`) the witness of the value `ψ_w η` is its canonical REP `< ψ_w η`,
whose existence is `CanonRep` — the session-1 open core.  So `Gset` cleanly LOCALISES the
obstruction: it is exactly canonical-representation existence in the deep region.

The subA_nm collapse `ψ_u(ψ_w η) = ψ_u η` therefore reduces (sorry-free) to the
NO-REALIZER condition below — the genuine, soundly-characterised deep-region core
(no `u`-canonical `ζ < η` realises the value), the dual of `CanonRep`. -/

open Classical in
/-- **`Gset` generator case in the sub-ε region** (GREEN, unconditional witness `ξ = η`).
When `η < psiSelf η w` (`AcanonLtValue`, automatic for `η < epsLvl`), the value's own
canonical witness IS `η`, so `Gset u (psiSelf η w) = insert η (Gset u η)` (for `u ≤ w`). -/
theorem Gset_gen_subeps {u w : ℕ} {η : Ordinal.{v}} (hlt : η < psiSelf η w)
    (hηc : η ∈ CsetSelf (psiResSelf η) η w) (hwu : u ≤ w) :
    Gset u (psiSelf η w) = insert η (Gset u η) := by
  have hpr : Ordinal.IsPrincipal (·+·) (psiSelf η w) :=
    fun {x y} hx hy => (psiSelf_addprinc η w).2 x y hx hy
  rw [Gset_gen hpr rfl hlt hηc, if_pos hwu]

/- `subA_nm_collapse_of_noRealizer` lives in `Residue.lean` (it consumes only §1
machinery, not the C-rank, and `Residue` is imported by — so cannot import — `Crank`). -/

/-! ### SET-MEMBERSHIP framing of the deep generator — DECISIVELY closed (2026-06-20k)

The distinct set-membership path: `C_u(c)` is a closure that CAN contain ordinals `≥ c` as
set members, so a `u`-canonical `ξ' ∈ [c,η)` (ordinally `≥ c`) might be `∈ C_u(c)`, firing
`ψ_u ξ' ∈ C_u(c)` directly (membership, not value-bound, not `ξ' < c` firing).  **Verdict:
it does NOT hold — cleanly (via Lemma 1.5), not circularly.**

`deepgen_arg_not_mem`: a `u`-canonical `ξ' ≥ c` with `ξ' < Ω_{u+1}` is NOT in `C_u(c)`
(when `c` is `u`-non-canonical).  Reason: Lemma 1.5 (`CsetSelf_lt_psiSelf_of_lt_Om`) forces
any `C_u(c)`-member `< Ω_{u+1}` to be `< ψ_u c`; but `ψ_u c ≤ c ≤ ξ'` gives `ξ' ≥ ψ_u c`,
contradiction.  So the deep-generator arg is NOT a closure member — the membership path
cannot fire it.  And the deep-generator VALUE `δ = ψ_u ξ'` itself: `ξ' ≥ c ⟹ ψ_u ξ' ≥ ψ_u c`
(mono), so `δ ≥ ψ_u c`, hence `δ ∉ C_u(c)` too (1.5).  Thus `δ < c` but `δ ∉ C_u(c)`: the
downward-saturation FAILS at the deep generator UNLESS no such `δ` exists (= the fixpoint).
`fixpoint ⟺ no-deep-gen ⟺ saturation` — the set-membership framing reduces to the SAME
value-identity core, cleanly.  No separate escape. -/
theorem deepgen_arg_not_mem {c ξ' : Ordinal.{u}} {u : ℕ}
    (hcanon_c : c ∉ CsetSelf (psiResSelf c) c u)
    (hcξ' : c ≤ ξ') (hband : ξ' < Om (u+1)) :
    ξ' ∉ CsetSelf (psiResSelf c) c u := by
  intro hmem
  have hlt : ξ' < psiSelf c u := CsetSelf_lt_psiSelf_of_lt_Om hmem hband
  have hpc : psiSelf c u ≤ c := psiSelf_le_self_of_not_canon hcanon_c
  exact absurd (lt_of_lt_of_le hlt (le_trans hpc hcξ')) (lt_irrefl _)

/-- **The deep-generator VALUE is not a closure member either** (GREEN, the saturation-fails
witness).  `δ = ψ^s_u ξ'` with `ξ' ≥ c` has `δ ≥ ψ^s_u c` (mono), so by Lemma 1.5
`δ ∉ C^s_u(c)` (when `δ < Ω_{u+1}`) — even though `δ < c` is possible.  So downward-saturation
of `C^s_u(c)` FAILS at the deep generator unless no such `δ` exists (the fixpoint).  This
confirms the set-membership framing reduces to the value-identity core. -/
theorem deepgen_value_not_mem {c ξ' : Ordinal.{u}} {u : ℕ}
    (hcanon_c : c ∉ CsetSelf (psiResSelf c) c u)
    (hcξ' : c ≤ ξ') :
    psiSelf ξ' u ∉ CsetSelf (psiResSelf c) c u := by
  intro hmem
  have hlt : psiSelf ξ' u < psiSelf c u :=
    CsetSelf_lt_psiSelf_of_lt_Om hmem (psiSelf_lt_Om_succ ξ' u)
  exact absurd (psiSelf_mono_arg hcξ' u) (not_le.2 hlt)

/-! ### The generator-value-arg `ψ^s_w η` is not in `C^s_u(η)` — via subscript-canonicity-mono

In sub-case A (`η` `u`-canonical, `u ≤ w`), `acanon_sub_mono` gives `η` `w`-canonical.
Then the generator's arg-value `ψ^s_w η` is NOT in `C^s_u(η)`: a witness would give
`ψ^s_w η = ψ^s_w ζ` with `ζ < η` `w`-canonical, and injectivity (`η` `w`-canonical too)
forces `ζ = η`, contradicting `ζ < η`.  This is a genuine §1 monolith piece.  NOTE it does
NOT close the value-collapse `ψ^s_u(ψ^s_w η) = ψ^s_u η` (that is about the VALUE `ψ^s_u c`,
whose realizer `ζ` is `u`-canonical and pairs only with the non-canonical `ψ^s_w η` — the
irreducible deep-generator value-identity). -/
theorem psiSelf_w_arg_not_mem {η : Ordinal.{u}} {w u : ℕ} (hwu : u ≤ w)
    (hηu : η ∈ CsetSelf (psiResSelf η) η u) :
    psiSelf η w ∉ CsetSelf (psiResSelf η) η u := by
  have hηw : η ∈ CsetSelf (psiResSelf η) η w := acanon_sub_mono hηu hwu
  intro hmem
  have hlo : Om u ≤ psiSelf η w := le_trans (Om_mono hwu) (Om_le_psiSelf η w)
  have hap : Ordinal.IsPrincipal (·+·) (psiSelf η w) :=
    fun {x y} hx hy => (psiSelf_addprinc η w).2 x y hx hy
  obtain ⟨u', ζ, heq, hζη, hζmem, hζc⟩ := CsetSelf_witness_canonical hap hlo hmem
  rw [psiResSelf, if_pos hζη] at heq
  have hu' : u' = w := by
    have h1 : Om u' ≤ psiSelf η w := heq ▸ Om_le_psiSelf ζ u'
    have h2 : psiSelf η w < Om (u'+1) := heq ▸ psiSelf_lt_Om_succ ζ u'
    have hle1 : u' ≤ w := by
      by_contra hc; exact absurd (lt_of_le_of_lt h1 (psiSelf_lt_Om_succ η w)) (not_lt.2 (Om_mono (by omega)))
    have hle2 : w ≤ u' := by
      by_contra hc; exact absurd (lt_of_le_of_lt (Om_le_psiSelf η w) h2) (not_lt.2 (Om_mono (by omega)))
    omega
  subst hu'
  have hζc_self : ζ ∈ CsetSelf (psiResSelf ζ) ζ u' :=
    CsetSelf_mono_param _ _ ζ u'
      (fun ρ ww hρ => by rw [psiResSelf, psiResSelf, if_pos hρ, if_pos (lt_trans hρ hζη)]) hζc
  exact absurd (psiSelf_canonical_inj hζc_self hηw heq.symm) (ne_of_lt hζη)

end YAPSS
