/-
**Buchholz 1986 §1, Lemma 1.7** prerequisites: `ε₀` is countable, giving the
band-0 bound `ω^α < Ω_1` for `α < ε₀` needed by 1.7(a).  Uses Mathlib
ordinal-arithmetic (`card_opow_le`, regularity of `ℵ₁`, `ε_`/Veblen).
-/
import YAPSS.Otembed
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Veblen

namespace YAPSS

open Cardinal Ordinal Set

/-- `ε₀ < ω_1`: `ε₀ = nfp(ω^·)0` and `ω_1` (regular) is closed under `ω^·`
(`card(ω^i) ≤ ℵ₀ ⊔ card i`). -/
theorem epsilon0_lt_omega1 : ε_ 0 < (ℵ_ 1).ord := by
  have h01 : ℵ₀ < ℵ_ 1 := by rw [← aleph_zero]; exact aleph_lt_aleph.2 zero_lt_one
  rw [epsilon_zero_eq_nfp]
  refine nfp_lt_ord_of_isRegular isRegular_aleph_one h01.ne' ?_ ?_
  · intro i hi
    rw [lt_ord] at hi ⊢
    calc (ω ^ i).card ≤ max ℵ₀ (max (ω : Ordinal).card i.card) := card_opow_le ω i
      _ < ℵ_ 1 := by rw [card_omega0]; exact max_lt h01 (max_lt h01 hi)
  · rw [lt_ord, Ordinal.card_zero]; exact aleph0_pos.trans h01

/-- The same, with `Ω_1` (the codebase's `Om 1 = (ℵ_1).ord`). -/
theorem epsilon0_lt_Om_one : ε_ 0 < Om 1 := by
  rw [Om_of_pos one_pos, Nat.cast_one]; exact epsilon0_lt_omega1

/-- For `α < ε₀`, `α < ω^α` (`α` is not an `ω`-power fixpoint, since `ε₀` is the
least such).  Gives canonicity `α ∈ C_0(α)` via `below_psi_mem_Cset` once
`ψ_0 α = ω^α` is known. -/
theorem lt_opow_self_of_lt_epsilon0 {α : Ordinal} (hα : α < ε_ 0) : α < ω ^ α := by
  by_contra h
  push Not at h
  exact absurd (epsilon_zero_le_of_omega0_opow_le h) (not_le.2 hα)

/-- For `α < ε₀`, `ω^α < Ω_1` (band 0): `α < ε₀ < ω_1` so `α` is countable, hence
`ω^α` is countable (`card_opow_le`).  Lets `psi_form_of_mem` (M1) apply at band 0. -/
theorem opow_lt_Om_one_of_lt_epsilon0 {α : Ordinal} (hα : α < ε_ 0) : ω ^ α < Om 1 := by
  have hαω1 : α < (ℵ_ 1).ord := hα.trans epsilon0_lt_omega1
  rw [Om_of_pos one_pos, Nat.cast_one, lt_ord]
  rw [lt_ord] at hαω1
  have h01 : ℵ₀ < ℵ_ 1 := by rw [← aleph_zero]; exact aleph_lt_aleph.2 zero_lt_one
  calc (ω ^ α).card ≤ max ℵ₀ (max (ω : Ordinal).card α.card) := card_opow_le ω α
    _ < ℵ_ 1 := by rw [card_omega0]; exact max_lt h01 (max_lt h01 hαω1)

/-- **Buchholz Lemma 1.7(a)**: for `α < ε₀`, `α` is `0`-canonical and `ψ_0 α = ω^α`.
Transfinite induction.  `hsub` (`Iio (ω^α) ⊆ C_0(α)`) by cases: `0` (base), succ
(`Iio_opow_succ_subset`), limit (`lt_opow_of_isSuccLimit` + `below_psi_mem_Cset`).
Then `ψ_0 α ≤ ω^α` (M1: `ω^α ∈ C_0(α)` ⟹ `ω^α = ω^ξ`, `ξ<α`, ⊥) and `ω^α ≤ ψ_0 α`
(`hsub`).  Canonicity is free: `α < ω^α = ψ_0 α` (`lt_opow_self_of_lt_epsilon0`) ⟹
`α ∈ C_0(α)` by `below_psi_mem_Cset`. -/
theorem psi_zero_eq_opow : ∀ α : Ordinal, α < ε_ 0 →
    α ∈ Cset (psiRes α) α 0 ∧ psi α 0 = ω ^ α := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro hα
    have hsub : ∀ γ, γ < ω ^ α → γ ∈ Cset (psiRes α) α 0 := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨δ, hδ⟩ | hlim
      · intro γ hγ
        rw [opow_zero] at hγ
        exact Iio_Om_subset_Cset (lt_of_lt_of_le hγ (one_le_Om 0))
      · obtain ⟨δ, rfl⟩ : ∃ δ', α = δ' + 1 := ⟨δ, by rw [← hδ, Order.succ_eq_add_one]⟩
        have hδe : δ < ε_ 0 := (lt_add_one δ).trans hα
        obtain ⟨hδc, hδf⟩ := IH δ (lt_add_one δ) hδe
        have hω : ω ^ δ ∈ Cset (psiRes (δ + 1)) (δ + 1) 0 := by
          have := Cset_psi_closed (CC_mono (lt_add_one δ).le 0 hδc) (lt_add_one δ) 0
          rwa [psiRes, if_pos (lt_add_one δ), hδf] at this
        have hbelow : ∀ s, s < ω ^ δ → s ∈ Cset (psiRes (δ + 1)) (δ + 1) 0 := by
          intro s hs
          rw [← hδf] at hs
          exact CC_mono (lt_add_one δ).le 0 (below_psi_mem_Cset hs)
        exact Iio_opow_succ_subset δ hω hbelow
      · intro γ hγ
        rw [lt_opow_of_isSuccLimit (by simp) hlim] at hγ
        obtain ⟨β, hβα, hγβ⟩ := hγ
        have hβe : β < ε_ 0 := hβα.trans hα
        obtain ⟨hβc, hβf⟩ := IH β hβα hβe
        rw [← hβf] at hγβ
        exact CC_mono hβα.le 0 (below_psi_mem_Cset hγβ)
    have hle : psi α 0 ≤ ω ^ α := by
      rw [psi_unfold]
      apply csInf_le'
      intro hmem
      obtain ⟨ξ, hξC, hξα, hξeq⟩ := psi_form_of_mem (isPrincipal_add_omega0_opow α)
        (by rw [Om_zero, ← opow_zero ω]; exact opow_le_opow_right omega0_pos bot_le)
        (opow_lt_Om_one_of_lt_epsilon0 hα) hmem
      have hξe0 : ξ < ε_ 0 := hξα.trans hα
      rw [(IH ξ hξα hξe0).2] at hξeq
      exact absurd hξeq (ne_of_lt ((opow_lt_opow_iff_right one_lt_omega0).2 hξα))
    have hge : ω ^ α ≤ psi α 0 := by
      by_contra hlt
      push Not at hlt
      exact psi_notMem α 0 (hsub _ hlt)
    have hform : psi α 0 = ω ^ α := le_antisymm hle hge
    exact ⟨below_psi_mem_Cset (hform ▸ lt_opow_self_of_lt_epsilon0 hα), hform⟩

/-- Level-0 canonicity for `α < ε₀` (the part of 1.7(a) used by `argExtract`). -/
theorem mem_Cself_zero_of_lt_epsilon0 {α : Ordinal} (hα : α < ε_ 0) :
    α ∈ Cset (psiRes α) α 0 := (psi_zero_eq_opow α hα).1

end YAPSS
