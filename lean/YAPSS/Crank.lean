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

end YAPSS
