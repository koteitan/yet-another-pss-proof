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

end YAPSS
