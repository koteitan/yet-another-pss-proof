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

universe u

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

/-! ### Toward Buchholz 1.7(b) (level `v ≠ 0`): `Ω_v` arithmetic -/

/-- `ω < Ω_v` for `v ≥ 1` (`Ω_v = ℵ_v.ord` is uncountable). -/
theorem omega_lt_Om {v : ℕ} (hv : 0 < v) : (ω : Ordinal) < Om v := by
  rw [Om_of_pos hv, lt_ord, card_omega0, ← aleph_zero]
  exact aleph_lt_aleph.2 (by exact_mod_cast hv)

/-- `Ω_v` (`v ≥ 1`) is an `ω`-power fixpoint: `ω^{Ω_v} = Ω_v`.  (`Ω_v = ℵ_v.ord` is
`opow`-principal and a succ-limit, so `ω^{Ω_v} = sup_{b<Ω_v} ω^b = Ω_v`.)  Gives
`ω^{Ω_v+α} = Ω_v · ω^α`, the level-`v` band base for 1.7(b). -/
theorem omega_opow_Om {v : ℕ} (hv : 0 < v) : ω ^ Om v = Om v := by
  refine le_antisymm ?_ (right_le_opow _ one_lt_omega0)
  rw [Om_of_pos hv, opow_le_of_isSuccLimit omega0_pos.ne' (isSuccLimit_ord (aleph0_le_aleph _))]
  intro b hb
  have hω : (ω : Ordinal) < (ℵ_ (v : Ordinal)).ord := by rw [← Om_of_pos hv]; exact omega_lt_Om hv
  exact le_of_lt ((isPrincipal_opow_ord (aleph0_le_aleph _)) hω hb)

/-- `ε_{Ω_v+1} < Ω_{v+1}` (the level-`v` formula bound stays below band `v+1`):
`ε_ = deriv (ω^·)` stays below the regular `ℵ_{v+1}` by `deriv_lt_ord` (since
`ω^·` does, by `isPrincipal_opow_ord`), and `Ω_v + 1 < Ω_{v+1}`.  This is the
correct bound for 1.7(b) (consistent with `ψ_v α < Ω_{v+1}`); the global
`ε_{Ω_ω+1}` is only the 1.8(a) `C`-bound. -/
theorem epsilon_Om_succ_lt_Om {v : ℕ} : ε_ (Om v + 1) < Om (v + 1) := by
  have hOm : Om (v + 1) = (ℵ_ ((v : Ordinal) + 1)).ord := by
    rw [Om_of_pos (Nat.succ_pos v), Nat.cast_succ]
  have hpos : (0 : Ordinal) < (v : Ordinal) + 1 := lt_of_le_of_lt bot_le (lt_add_one _)
  have hω : (ω : Ordinal) < (ℵ_ ((v : Ordinal) + 1)).ord := by
    rw [lt_ord, card_omega0, ← aleph_zero]; exact aleph_lt_aleph.2 hpos
  rw [epsilon_eq_deriv, hOm]
  refine deriv_lt_ord (isRegular_aleph_add_one _) ?_ ?_ ?_
  · rw [← aleph_zero]; exact (aleph_lt_aleph.2 hpos).ne'
  · intro i hi; exact (isPrincipal_opow_ord (aleph0_le_aleph _)) hω hi
  · have hlt : Om v < Om (v + 1) := Om_lt_succ v
    rw [hOm] at hlt
    rw [← Order.succ_eq_add_one]
    exact (isSuccLimit_ord (aleph0_le_aleph _)).succ_lt hlt

/-- `ω^i < Ω_{v+1}` for `i < Ω_{v+1}` (band `v+1` is closed under `ω^·`). -/
theorem opow_lt_Om_succ {v : ℕ} {i : Ordinal} (hi : i < Om (v + 1)) : ω ^ i < Om (v + 1) := by
  have hOm : Om (v + 1) = (ℵ_ ((v : Ordinal) + 1)).ord := by
    rw [Om_of_pos (Nat.succ_pos v), Nat.cast_succ]
  rw [hOm] at hi ⊢
  have hω : (ω : Ordinal) < (ℵ_ ((v : Ordinal) + 1)).ord := by
    rw [lt_ord, card_omega0, ← aleph_zero]
    exact aleph_lt_aleph.2 (lt_of_le_of_lt bot_le (lt_add_one _))
  exact (isPrincipal_opow_ord (aleph0_le_aleph _)) hω hi

/-- **Canonicity helper for 1.7(b):** `α < ω^{Ω_v+α}` for `α < ε_{Ω_v+1}` (`v ≥ 1`).
Non-absorbed case `α < Ω_v+α` is immediate; the absorbed case `Ω_v+α=α` needs
`α < ω^α`, i.e. `α` is not an `ω`-fixpoint (ε-number): if it were, `α = ε_β` with
`Ω_v < α` (so `β > β'` where `ε_{β'}=Ω_v`, since `Ω_v` is itself an ε-number by
`omega_opow_Om`) and `α < ε_{Ω_v+1}` (so `β ≤ Ω_v`), giving `β' < Ω_v`, yet
`ε_{β'}=Ω_v` contradicts `deriv_lt_ord` (`ε_{β'} < Ω_v` for `β' < Ω_v`). -/
theorem lt_opow_Om_add {v : ℕ} (hv : 0 < v) {α : Ordinal} (hα : α < ε_ (Om v + 1)) :
    α < ω ^ (Om v + α) := by
  rcases eq_or_lt_of_le (le_add_self : α ≤ Om v + α) with he | hlt
  · rw [← he]
    by_contra hc
    push Not at hc
    have hfix : ω ^ α = α := le_antisymm hc (right_le_opow α one_lt_omega0)
    have hεderiv : (ε_ : Ordinal → Ordinal) = deriv (fun a => ω ^ a) := funext epsilon_eq_deriv
    obtain ⟨β, hβ⟩ : α ∈ Set.range (ε_ : Ordinal → Ordinal) := by
      rw [hεderiv, mem_range_deriv (isNormal_opow one_lt_omega0)]; exact hfix
    obtain ⟨β', hβ'⟩ : Om v ∈ Set.range (ε_ : Ordinal → Ordinal) := by
      rw [hεderiv, mem_range_deriv (isNormal_opow one_lt_omega0)]; exact omega_opow_Om hv
    have hαpos : 0 < α := by
      by_contra h; push Not at h
      rw [le_antisymm h bot_le, add_zero] at he
      exact absurd he.symm (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_Om v)))
    have hOmlt : Om v < α := by
      have h := lt_add_of_pos_right (Om v) hαpos
      rwa [← he] at h
    have hlt2 : ε_ β' < ε_ β := by rw [hβ', hβ]; exact hOmlt
    have hββ' : β' < β := (veblen_right_strictMono 1).lt_iff_lt.1 hlt2
    have hβbd : β ≤ Om v := by
      have hlt3 : ε_ β < ε_ (Om v + 1) := by rw [hβ]; exact hα
      have hβlt : β < Om v + 1 := (veblen_right_strictMono 1).lt_iff_lt.1 hlt3
      rwa [← Order.succ_eq_add_one, Order.lt_succ_iff] at hβlt
    have hβ'lt : β' < Om v := lt_of_lt_of_le hββ' hβbd
    obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    have hOmeq : Om (w + 1) = (ℵ_ ((w : Ordinal) + 1)).ord := by
      rw [Om_of_pos (Nat.succ_pos w), Nat.cast_succ]
    have hpos : (0 : Ordinal) < (w : Ordinal) + 1 := lt_of_le_of_lt bot_le (lt_add_one _)
    have hεlt : ε_ β' < Om (w + 1) := by
      rw [epsilon_eq_deriv, hOmeq]
      refine deriv_lt_ord (isRegular_aleph_add_one _) (by rw [← aleph_zero]; exact (aleph_lt_aleph.2 hpos).ne') ?_ ?_
      · intro i hi
        have hω : (ω : Ordinal) < (ℵ_ ((w : Ordinal) + 1)).ord := by
          rw [lt_ord, card_omega0, ← aleph_zero]; exact aleph_lt_aleph.2 hpos
        exact (isPrincipal_opow_ord (aleph0_le_aleph _)) hω hi
      · rw [← hOmeq]; exact hβ'lt
    rw [hβ'] at hεlt
    exact absurd hεlt (lt_irrefl _)
  · exact lt_of_lt_of_le hlt (right_le_opow _ one_lt_omega0)

/-- **Buchholz Lemma 1.7(b)**: for `v ≥ 1` and `α < ε_{Ω_v+1}`, `α` is `v`-canonical
and `ψ_v α = ω^{Ω_v+α}`.  Transfinite induction mirroring 1.7(a) with the `Ω_v`
offset: band-`v` bounds `Ω_v = ω^{Ω_v} ≤ ω^{Ω_v+α} < Ω_{v+1}`; `hsub` by cases
(base/succ via `Iio_opow_succ_subset`/limit via `isSuccLimit_add` split on `β < Ω_v`);
`≤` via M1; canonicity via `lt_opow_Om_add` + `below_psi_mem_Cset`. -/
theorem psi_eq_opow_add (v : ℕ) (hv : 0 < v) : ∀ α : Ordinal, α < ε_ (Om v + 1) →
    α ∈ Cset (psiRes α) α v ∧ psi α v = ω ^ (Om v + α) := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro hα
    have hαΩ : α < Om (v + 1) := hα.trans epsilon_Om_succ_lt_Om
    have hΩα : Om v + α < Om (v + 1) := (Om_isPrincipal (v + 1)) (Om_lt_succ v) hαΩ
    have hbandhi : ω ^ (Om v + α) < Om (v + 1) := opow_lt_Om_succ hΩα
    have hbandlo : Om v ≤ ω ^ (Om v + α) := by
      calc Om v = ω ^ Om v := (omega_opow_Om hv).symm
        _ ≤ ω ^ (Om v + α) := opow_le_opow_right omega0_pos le_self_add
    have hsub : ∀ γ, γ < ω ^ (Om v + α) → γ ∈ Cset (psiRes α) α v := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨δ, hδ⟩ | hlim
      · intro γ hγ
        rw [add_zero, omega_opow_Om hv] at hγ
        exact Iio_Om_subset_Cset hγ
      · obtain ⟨δ, rfl⟩ : ∃ δ', α = δ' + 1 := ⟨δ, by rw [← hδ, Order.succ_eq_add_one]⟩
        have hδe : δ < ε_ (Om v + 1) := (lt_add_one δ).trans hα
        obtain ⟨hδc, hδf⟩ := IH δ (lt_add_one δ) hδe
        have hω : ω ^ (Om v + δ) ∈ Cset (psiRes (δ + 1)) (δ + 1) v := by
          have := Cset_psi_closed (CC_mono (lt_add_one δ).le v hδc) (lt_add_one δ) v
          rwa [psiRes, if_pos (lt_add_one δ), hδf] at this
        have hbelow : ∀ s, s < ω ^ (Om v + δ) → s ∈ Cset (psiRes (δ + 1)) (δ + 1) v := by
          intro s hs; rw [← hδf] at hs; exact CC_mono (lt_add_one δ).le v (below_psi_mem_Cset hs)
        have heq : Om v + (δ + 1) = (Om v + δ) + 1 := by rw [add_assoc]
        rw [heq]; exact Iio_opow_succ_subset (Om v + δ) hω hbelow
      · intro γ hγ
        have hlimΩ : Order.IsSuccLimit (Om v + α) := Ordinal.isSuccLimit_add _ hlim
        rw [lt_opow_of_isSuccLimit (by simp) hlimΩ] at hγ
        obtain ⟨β, hβ, hγβ⟩ := hγ
        rcases lt_or_ge β (Om v) with hβlo | hβhi
        · have : γ < Om v := by
            calc γ < ω ^ β := hγβ
              _ < ω ^ Om v := (opow_lt_opow_iff_right one_lt_omega0).2 hβlo
              _ = Om v := omega_opow_Om hv
          exact Iio_Om_subset_Cset this
        · obtain ⟨α', rfl⟩ := exists_add_of_le hβhi
          have hα'α : α' < α := (add_lt_add_iff_left (Om v)).1 hβ
          obtain ⟨hα'c, hα'f⟩ := IH α' hα'α (hα'α.trans hα)
          rw [← hα'f] at hγβ
          exact CC_mono hα'α.le v (below_psi_mem_Cset hγβ)
    have hle : psi α v ≤ ω ^ (Om v + α) := by
      rw [psi_unfold]; apply csInf_le'; intro hmem
      obtain ⟨ξ, hξC, hξα, hξeq⟩ := psi_form_of_mem (isPrincipal_add_omega0_opow _) hbandlo hbandhi hmem
      rw [(IH ξ hξα (hξα.trans hα)).2] at hξeq
      exact absurd hξeq (ne_of_lt ((opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left (Om v)).2 hξα)))
    have hge : ω ^ (Om v + α) ≤ psi α v := by
      by_contra hlt; push Not at hlt; exact psi_notMem α v (hsub _ hlt)
    have hform : psi α v = ω ^ (Om v + α) := le_antisymm hle hge
    exact ⟨below_psi_mem_Cset (by rw [hform]; exact lt_opow_Om_add hv hα), hform⟩

/-- Level-`v` canonicity for `α < ε_{Ω_v+1}` (`v ≥ 1`), the part of 1.7(b) used by
the necessity argument. -/
theorem mem_Cself_of_lt_epsilon {v : ℕ} (hv : 0 < v) {α : Ordinal} (hα : α < ε_ (Om v + 1)) :
    α ∈ Cset (psiRes α) α v := (psi_eq_opow_add v hv α hα).1


/-! ## Buchholz 1.8(a): the global `C`-bound `ε_{Ω_ω+1}` -/

noncomputable def Omω : Ordinal := (ℵ_ (ω : Ordinal)).ord
noncomputable def epsB : Ordinal := ε_ (Omω + 1)

theorem Om_lt_Omω (v : ℕ) : Om v < Omω := by
  unfold Omω
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [Om_zero]
    exact lt_of_lt_of_le one_lt_omega0 (omega0_le_ord.2 (aleph0_le_aleph _))
  · rw [Om_of_pos hv]
    exact (Cardinal.ord_lt_ord).2 (aleph_lt_aleph.2 (natCast_lt_omega0 v))

theorem Omω_lt_epsB : Omω < epsB := by
  unfold epsB
  exact lt_of_lt_of_le (lt_add_one _) (veblen_right_strictMono 1).le_apply

theorem psi_lt_epsB (ξ : Ordinal) (u : ℕ) : psi ξ u < epsB := by
  calc psi ξ u < Om (u + 1) := psi_lt_Om_succ ξ u
    _ < Omω := Om_lt_Omω (u + 1)
    _ < epsB := Omω_lt_epsB

theorem epsB_principal : Ordinal.IsPrincipal (· + ·) epsB := by
  unfold epsB
  have h := omega0_opow_epsilon (Omω + 1)
  rw [← h]; exact isPrincipal_add_omega0_opow _

theorem Cset_subset_epsB {α : Ordinal} {v : ℕ} : Cset (psiRes α) α v ⊆ Set.Iio epsB := by
  intro x hx
  obtain ⟨n, hn⟩ := Cset_mem_iff.1 hx
  clear hx
  induction n generalizing x with
  | zero =>
    rw [Citer, Function.iterate_zero, id_eq] at hn
    exact lt_trans (lt_of_lt_of_le hn (le_of_lt (Om_lt_Omω v))) Omω_lt_epsB
  | succ n IH =>
    rw [Citer_succ, Cstep] at hn
    rcases hn with (h1 | h2) | h3
    · exact IH h1
    · obtain ⟨y, hy, z, hz, hyz⟩ := h2
      dsimp only at hyz
      rw [← hyz]
      exact epsB_principal (IH hy) (IH hz)
    · obtain ⟨u, ⟨ξ, ⟨hξC, hξα⟩, hξx⟩⟩ := Set.mem_iUnion.1 h3
      have hξα' : ξ < α := hξα
      simp only [psiRes, if_pos hξα'] at hξx
      rw [← hξx]
      exact psi_lt_epsB ξ u

/-! ## Buchholz 1.4(b) (canonical witness) reduced to the collapse region

The proven `1.7` makes every argument below `ε(w)` canonical, so the canonical-
witness lemma `CW` (and hence the entire necessity direction `NEC`) is reduced to
the *collapse region* `ξ ≥ ε(w)` alone — the genuine remaining Buchholz core
(`CC` below).  Mathematically `CC` is true: the omitted-canonicity `Cstep`
generates a non-canonical argument `ξ` only after its (unique, by `1.4(a)`)
canonical representative has already entered `C_v(α)` below `α` (bootstrapping:
`ψ_w ξ` cannot fire without `ξ ∈ C`, and a collapsed `ξ` is reachable only via
its representative).  This is Buchholz's "it can be shown that omitting the
condition does not change the sets `C_v(α)`" (Remark, p197), left unproved there. -/

/-- Level-`w` non-collapse threshold `ε(w)`: `ε_0` for `w = 0`, `ε_{Ω_w+1}` for
`w ≥ 1`.  Below it, `1.7` makes every argument `w`-canonical. -/
noncomputable def epsLvl (w : ℕ) : Ordinal.{u} := if w = 0 then ε_ 0 else ε_ (Om w + 1)

/-- Unified `1.7` canonicity: `ξ < ε(w) ⟹ ξ` is `w`-canonical (`ξ ∈ C_w(ξ)`). -/
theorem mem_Cself_lvl {w : ℕ} {ξ : Ordinal.{u}} (h : ξ < epsLvl w) :
    ξ ∈ Cset (psiRes ξ) ξ w := by
  unfold epsLvl at h
  cases w with
  | zero => simpa using mem_Cself_zero_of_lt_epsilon0 (by simpa using h)
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k)] at h
    exact mem_Cself_of_lt_epsilon (Nat.succ_pos k) h

/-- **General witness extraction.**  Any additive-principal `γ ∈ C_v(α)` with
`Ω_v ≤ γ` is `ψ_{u'} ξ` for some `ξ ∈ C_v(α) ∩ Iio α` (level `u'` read off the
generator).  Like `psi_form_of_mem` but without band hypotheses — keeps the actual
generator level instead of forcing it to `v`. -/
theorem psi_witness_of_mem {α γ : Ordinal.{u}} {v : ℕ}
    (hap : Ordinal.IsPrincipal (· + ·) γ) (hlo : Om v ≤ γ)
    (hmem : γ ∈ Cset (psiRes α) α v) :
    ∃ (u' : ℕ) (ξ : Ordinal.{u}), γ = psi ξ u' ∧ ξ < α ∧ ξ ∈ Cset (psiRes α) α v := by
  obtain ⟨n, hn⟩ := Cset_mem_iff.1 hmem
  clear hmem
  induction n generalizing γ with
  | zero =>
    rw [Citer, Function.iterate_zero, id_eq] at hn
    exact absurd hn (not_lt.2 hlo)
  | succ n IH =>
    rw [Citer_succ, Cstep] at hn
    rcases hn with (h1 | h2) | h3
    · exact IH hap hlo h1
    · obtain ⟨x, hx, y, hy, hxy⟩ := h2
      have hmemn : γ ∈ Citer (psiRes α) α v n := by
        rcases eq_or_lt_of_le (show x ≤ γ from hxy ▸ le_self_add) with hxe | hxlt
        · exact hxe ▸ hx
        · rcases eq_or_lt_of_le (show y ≤ γ from hxy ▸ le_add_self) with hye | hylt
          · exact hye ▸ hy
          · exact absurd hxy.symm (ne_of_gt (hap hxlt hylt))
      exact IH hap hlo hmemn
    · obtain ⟨u, ⟨ξ, ⟨hξC, hξα⟩, hξδ⟩⟩ := Set.mem_iUnion.1 h3
      have hξα : ξ < α := hξα
      simp only [psiRes, if_pos hξα] at hξδ
      exact ⟨u, ξ, hξδ.symm, hξα, Citer_subset_Cset hξC⟩

/-- **CW reduced to the collapse region** (Buchholz 1.4(b) modulo the genuine core).
The witness `ξ` from `psi_witness_of_mem` is canonicalized by `1.7` when
`ξ < ε(u')` (non-collapse); only the collapse region `ε(u') ≤ ξ` needs the
hypothesis `CC` (canonical-rep existence for collapsed arguments).  This isolates
the entire remaining Buchholz necessity core to `CC`. -/
theorem CW_of_collapseCanon
    (CC : ∀ (v u' : ℕ) (ξ α : Ordinal.{u}), v ≤ u' → ξ ∈ Cset (psiRes α) α v → ξ < α →
       epsLvl u' ≤ ξ → ∃ ξ'' : Ordinal.{u}, psi ξ'' u' = psi ξ u' ∧ ξ'' < α ∧
         ξ'' ∈ Cset (psiRes α) α v ∧ ξ'' ∈ Cset (psiRes ξ'') ξ'' u') :
    ∀ (v : ℕ) (γ α : Ordinal.{u}), γ ∈ Cset (psiRes α) α v → Om v ≤ γ →
       Ordinal.IsPrincipal (· + ·) γ → ∃ (u' : ℕ) (ξ : Ordinal.{u}),
         γ = psi ξ u' ∧ ξ < α ∧ ξ ∈ Cset (psiRes α) α v ∧ ξ ∈ Cset (psiRes ξ) ξ u' := by
  intro v γ α hmem hlo hap
  obtain ⟨u', ξ, hγ, hξα, hξC⟩ := psi_witness_of_mem hap hlo hmem
  -- the band forces `v ≤ u'`: `Ω_v ≤ γ = ψ_{u'} ξ < Ω_{u'+1}`
  have hvu' : v ≤ u' := by
    by_contra hlt
    have hle : Om (u' + 1) ≤ Om v := Om_mono (by omega)
    exact absurd (lt_of_le_of_lt (hγ ▸ hlo) (psi_lt_Om_succ ξ u')) (not_lt.2 hle)
  by_cases hc : ξ < epsLvl u'
  · exact ⟨u', ξ, hγ, hξα, hξC, mem_Cself_lvl hc⟩
  · obtain ⟨ξ'', hψ, hξ''α, hξ''C, hξ''can⟩ := CC v u' ξ α hvu' hξC hξα (not_lt.1 hc)
    exact ⟨u', ξ'', hγ.trans hψ.symm, hξ''α, hξ''C, hξ''can⟩

/-- **`wf3`-necessity reduced to the collapse-region canonical-rep core `CC`.**
Combines `CW_of_collapseCanon` with `NEC_of_canonWitness`: the entire Buchholz 1.9
necessity direction follows from `CC` alone (the proven `1.7` discharges the
non-collapse region). -/
theorem NEC_of_collapseCanon
    (CC : ∀ (v u' : ℕ) (ξ α : Ordinal.{u}), v ≤ u' → ξ ∈ Cset (psiRes α) α v → ξ < α →
       epsLvl u' ≤ ξ → ∃ ξ'' : Ordinal.{u}, psi ξ'' u' = psi ξ u' ∧ ξ'' < α ∧
         ξ'' ∈ Cset (psiRes α) α v ∧ ξ'' ∈ Cset (psiRes ξ'') ξ'' u')
    {t : Three} (ht : wf3 t) {v : ℕ} {α : Ordinal.{u}}
    (hm : oV t ∈ Cset (psiRes α) α v) : ∀ x ∈ Gterm v t, oV x < α :=
  NEC_of_canonWitness (CW_of_collapseCanon CC) ht hm

/-! ## Sharper reduction: necessity from the minimal non-canonical-arg kernel `K`

`CW_of_collapseCanon`/`CC` bundle four obligations on the canonical representative
`ξ''` (value equality, `ξ'' < α`, `ξ'' ∈ C_v(α)`, `ξ''` canonical).  Two of those
are *free*:

* `ξ'' < α` follows from `psi_arg_lt_of_mem_cross` (the value `ψ_{u'} ξ'' ∈ C_v(α)`
  with `v ≤ u'` already forces the argument below `α`) — no bootstrap needed; and
* in the only consumer (`argExtract_of_canonWitness` / `NEC_of_argExtract`) the
  canonical witness is pinned by `psi_canonical_inj` to the *given* canonical `β`,
  so the representative is `β` itself.

Eliminating those, the entire `wf3`-necessity direction reduces to a single
minimal kernel `K`: a NON-canonical argument `ξ ∈ C_v(α)` whose `ψ_a`-value equals
that of a canonical `β` forces `β ∈ C_v(α)`.  This is exactly Buchholz's Remark
(p197) "omitting the condition `ξ ∈ C_u(ξ)` does not change `C_v(α)`" restricted to
its genuine residue: the omitted-canonicity `Cstep` may admit a non-canonical
generator `ξ`, and `K` says its canonical representative is admitted too.  `1.7`
(`mem_Cself_lvl`) already discharges every `ξ < ε(a)`, so `K` only bites in the
collapse region `ξ ≥ ε(a)`. -/

/-- **Arg-extraction reduced to the non-canonical-arg kernel `K`.**  Stage
induction on `ψ_a β ∈ C_v(α)`: the base case is vacuous (`ψ_a β ≥ Ω_v`), the `+`
case is absorbed (the value is additive-principal), and the `ψ`-generator case
yields `ψ_u ξ = ψ_a β` with `ξ ∈ C_v(α) ∩ Iio α`; the band forces `u = a`.  If the
generator argument `ξ` is canonical, `psi_canonical_inj` gives `ξ = β`; otherwise
`K` supplies `β ∈ C_v(α)`.  (0 sorry — the whole reduction is kernel-checked; only
`K` itself remains, the genuine Buchholz core.) -/
theorem argExt_of_kernel
    (K : ∀ (v a : ℕ) (ξ β α : Ordinal.{u}), v ≤ a →
      ξ ∈ Cset (psiRes α) α v → ξ < α → ξ ∉ Cset (psiRes ξ) ξ a →
      β ∈ Cset (psiRes β) β a → psi ξ a = psi β a → β ∈ Cset (psiRes α) α v)
    {v a : ℕ} {β α : Ordinal.{u}} (hva : v ≤ a)
    (hβc : β ∈ Cset (psiRes β) β a) (hmem : psi β a ∈ Cset (psiRes α) α v) :
    β ∈ Cset (psiRes α) α v := by
  obtain ⟨n, hn⟩ := Cset_mem_iff.1 hmem
  clear hmem
  induction n generalizing β with
  | zero =>
    rw [Citer, Function.iterate_zero, id_eq] at hn
    exact absurd (lt_of_lt_of_le hn (le_trans (Om_mono hva) (Om_le_psi β a))) (lt_irrefl _)
  | succ n IH =>
    rw [Citer_succ, Cstep] at hn
    rcases hn with (h1 | h2) | h3
    · exact IH hβc h1
    · obtain ⟨x, hx, y, hy, hxy⟩ := h2
      have hap : Ordinal.IsPrincipal (· + ·) (psi β a) :=
        fun {p q} hp hq => (psi_addprinc β a).2 p q hp hq
      have : psi β a ∈ Citer (psiRes α) α v n := by
        rcases eq_or_lt_of_le (show x ≤ psi β a from hxy ▸ le_self_add) with hxe | hxlt
        · exact hxe ▸ hx
        · rcases eq_or_lt_of_le (show y ≤ psi β a from hxy ▸ le_add_self) with hye | hylt
          · exact hye ▸ hy
          · exact absurd hxy.symm (ne_of_gt (hap hxlt hylt))
      exact IH hβc this
    · obtain ⟨u, ⟨ξ, ⟨hξC, hξα⟩, hξx⟩⟩ := Set.mem_iUnion.1 h3
      have hξα : ξ < α := hξα
      simp only [psiRes, if_pos hξα] at hξx
      have hua : u = a := by
        have h1 : Om u ≤ psi β a := hξx ▸ Om_le_psi ξ u
        have h2 : psi β a < Om (u + 1) := hξx ▸ psi_lt_Om_succ ξ u
        have hua1 : u ≤ a := by
          by_contra hc
          exact absurd (lt_of_le_of_lt h1 (psi_lt_Om_succ β a)) (not_lt.2 (Om_mono (by omega)))
        have hua2 : a ≤ u := by
          by_contra hc
          exact absurd (lt_of_le_of_lt (Om_le_psi β a) h2) (not_lt.2 (Om_mono (by omega)))
        omega
      subst hua
      by_cases hξcanon : ξ ∈ Cset (psiRes ξ) ξ u
      · exact (psi_canonical_inj hξcanon hβc hξx) ▸ Citer_subset_Cset hξC
      · exact K v u ξ β α hva (Citer_subset_Cset hξC) hξα hξcanon hβc hξx

/-- **`wf3`-necessity (Buchholz 1.9) from the minimal kernel `K`.**  Wires
`argExt_of_kernel` through `NEC_of_argExtract`.  The whole necessity direction
follows from `K` alone — strictly sharper than `NEC_of_collapseCanon`/`CC`
(the `ξ'' < α` bootstrap and the `ξ''` construction are eliminated). -/
theorem NEC_of_kernel
    (K : ∀ (v a : ℕ) (ξ β α : Ordinal.{u}), v ≤ a →
      ξ ∈ Cset (psiRes α) α v → ξ < α → ξ ∉ Cset (psiRes ξ) ξ a →
      β ∈ Cset (psiRes β) β a → psi ξ a = psi β a → β ∈ Cset (psiRes α) α v)
    {t : Three} (ht : wf3 t) {v : ℕ} {α : Ordinal.{u}}
    (hm : oV t ∈ Cset (psiRes α) α v) : ∀ x ∈ Gterm v t, oV x < α :=
  NEC_of_argExtract (fun hva hβc hmem => argExt_of_kernel K hva hβc hmem) ht hm

/-! ## Reduction of the kernel `K` to ordinal-level Buchholz 1.9 sufficiency

The kernel `K` carries five hypotheses, of which the non-canonicity of `ξ`
(`ξ ∉ C_a(ξ)`) and the membership `ξ ∈ C_v(α)` serve *only* to deliver `β < α`
for free (via `Cset_psi_closed` ⟶ `psi_arg_lt_of_mem_cross`).  Once `β < α` is
in hand, the remaining content of `K` is exactly the **sufficiency direction of
Buchholz 1.9 at the ordinal level**:

> `SUFF`:  `v ≤ a → β` is `a`-canonical (`β ∈ C_a(β)`) → `β < α → β ∈ C_v(α)`.

`SUFF` is the genuine residual hard core.  It is *not* circular with the
necessity machinery: necessity (`NEC_of_kernel`) is reduced **to** `K`, and `K`
is reduced here **to** `SUFF`, a pure closure/sufficiency statement whose own
proof (Buchholz 1.9, induction on the `C_a(β)`-rank, generators handled by the
`with-C` canonicity witness) never invokes necessity.  The chain
`SUFF ⟹ K ⟹ NEC` is a DAG, not a cycle. -/

/-- **`K` from ordinal-level 1.9 sufficiency `SUFF`.**  The two `ξ`-hypotheses of
`K` are consumed solely to produce `β < α` (free, via `Cset_psi_closed` and
`psi_arg_lt_of_mem_cross`); the goal `β ∈ C_v(α)` is then `SUFF` applied to the
canonical `β`.  (0 sorry — `K` is fully reduced to `SUFF`.) -/
theorem kernel_of_suff
    (SUFF : ∀ (v a : ℕ) (β α : Ordinal.{u}), v ≤ a →
      β ∈ Cset (psiRes β) β a → β < α → β ∈ Cset (psiRes α) α v) :
    ∀ (v a : ℕ) (ξ β α : Ordinal.{u}), v ≤ a →
      ξ ∈ Cset (psiRes α) α v → ξ < α → ξ ∉ Cset (psiRes ξ) ξ a →
      β ∈ Cset (psiRes β) β a → psi ξ a = psi β a → β ∈ Cset (psiRes α) α v := by
  intro v a ξ β α hva hξC hξα _hξnc hβc heq
  have hβα : β < α := by
    have hpsi_in : psi ξ a ∈ Cset (psiRes α) α v := by
      have := Cset_psi_closed hξC hξα a
      rwa [psiRes, if_pos hξα] at this
    rw [heq] at hpsi_in
    exact psi_arg_lt_of_mem_cross hva hpsi_in
  exact SUFF v a β α hva hβc hβα

/-- **`wf3`-necessity (Buchholz 1.9) from ordinal-level 1.9 sufficiency `SUFF`
alone.**  Composes `kernel_of_suff` with `NEC_of_kernel`.  This pins the entire
remaining Buchholz necessity direction to the single sufficiency core `SUFF`. -/
theorem NEC_of_suff
    (SUFF : ∀ (v a : ℕ) (β α : Ordinal.{u}), v ≤ a →
      β ∈ Cset (psiRes β) β a → β < α → β ∈ Cset (psiRes α) α v)
    {t : Three} (ht : wf3 t) {v : ℕ} {α : Ordinal.{u}}
    (hm : oV t ∈ Cset (psiRes α) α v) : ∀ x ∈ Gterm v t, oV x < α :=
  NEC_of_kernel (kernel_of_suff SUFF) ht hm

/-! ## Collapsing (Buchholz 1.6) for `ψ^s` (self-referential with-C)

`psi_proj_notmem`'s tool, ported to the residue-free self with-C set.  The
canonicity test in `CstepSelf` is bound-independent (and param-invariant below the
bound via `CsetSelf_param_eq`), so the omitted collapse proofs translate. -/

theorem psiSelf_eq_of_notMem {α β : Ordinal.{u}} {v : ℕ} (hαβ : α ≤ β)
    (hnm : psiSelf α v ∉ CsetSelf (psiResSelf β) β v) : psiSelf α v = psiSelf β v := by
  refine le_antisymm (psiSelf_mono_arg hαβ v) ?_
  rw [psiSelf_unfold β v]
  exact csInf_le' hnm

theorem psiSelf_notMem_iff_eq {α β : Ordinal.{u}} {v : ℕ} (hαβ : α ≤ β) :
    psiSelf α v ∉ CsetSelf (psiResSelf β) β v ↔ psiSelf α v = psiSelf β v := by
  refine ⟨psiSelf_eq_of_notMem hαβ, fun he => ?_⟩
  rw [he]; exact psiSelf_notMem β v

theorem psiSelf_eq_of_CsetSelf_eq {α β : Ordinal.{u}} {v : ℕ}
    (h : CsetSelf (psiResSelf α) α v = CsetSelf (psiResSelf β) β v) :
    psiSelf α v = psiSelf β v := by
  rw [psiSelf_unfold α v, psiSelf_unfold β v, h]

/-- **1.6(a) C-set part for `ψ^s`**: if `α ∉ C^s_v(α)` then `C^s_v(α+1) = C^s_v(α)`.
Stage induction; the generator's `ξ < α+1` collapses to `ξ < α` (`α` never enters
the closure), and the canonicity test `ξ ∈ CsetSelf p ξ u` (bound ξ < α) is
param-invariant between `psiResSelf (α+1)` and `psiResSelf α` (`CsetSelf_param_eq`). -/
theorem CsetSelf_succ_eq {α : Ordinal.{u}} {v : ℕ}
    (hα : α ∉ CsetSelf (psiResSelf α) α v) :
    CsetSelf (psiResSelf (α + 1)) (α + 1) v = CsetSelf (psiResSelf α) α v := by
  have key : ∀ n, (CstepSelf' (psiResSelf (α + 1)) (α + 1))^[n] (Set.Iio (Om v))
                = (CstepSelf' (psiResSelf α) α)^[n] (Set.Iio (Om v)) := by
    intro n
    induction n with
    | zero => rfl
    | succ n IH =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', IH]
      have hαn : α ∉ (CstepSelf' (psiResSelf α) α)^[n] (Set.Iio (Om v)) :=
        fun h => hα (CiterSelf_subset_CsetSelf h)
      show CstepSelf (psiResSelf (α+1)) (α+1) _ _ = CstepSelf (psiResSelf α) α _ _
      unfold CstepSelf
      congr 1
      apply Set.iUnion_congr
      intro u
      ext y
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨ξ, ⟨hξX, ⟨hξα1, hξc⟩⟩, rfl⟩
        have hξα : ξ < α := by
          rcases lt_or_eq_of_le (Order.lt_succ_iff.1 hξα1) with h | h
          · exact h
          · exact absurd (h ▸ hξX) hαn
        refine ⟨ξ, ⟨hξX, ⟨hξα, ?_⟩⟩, ?_⟩
        · rwa [CsetSelf_param_eq (fun ζ uu hζ => psiResSelf_eq_below (lt_add_one α).le (lt_trans hζ hξα))] at hξc
        · rw [psiResSelf_eq_below (lt_add_one α).le hξα]
      · rintro ⟨ξ, ⟨hξX, ⟨hξα, hξc⟩⟩, rfl⟩
        refine ⟨ξ, ⟨hξX, ⟨lt_of_lt_of_le hξα le_self_add, ?_⟩⟩, ?_⟩
        · rwa [CsetSelf_param_eq (fun ζ uu hζ => psiResSelf_eq_below (lt_add_one α).le (lt_trans hζ hξα))]
        · rw [psiResSelf_eq_below (lt_add_one α).le hξα]
  ext x
  rw [CsetSelf_mem_iff, CsetSelf_mem_iff]
  exact exists_congr (fun n => by rw [key n])

/-- **Buchholz 1.6(a) for `ψ^s`**: `α ∉ C^s_v(α) → ψ^s_v α = ψ^s_v(α+1)`. -/
theorem collapseSelf_succ {α : Ordinal.{u}} {v : ℕ}
    (hα : α ∉ CsetSelf (psiResSelf α) α v) : psiSelf α v = psiSelf (α + 1) v :=
  psiSelf_eq_of_CsetSelf_eq (CsetSelf_succ_eq hα).symm

/-- **C^s-set continuity from below** at a positive succ-limit bound. -/
theorem CsetSelf_limit_sub {β : Ordinal.{u}} {v : ℕ}
    (hβ : Order.IsSuccLimit β) (hβ0 : 0 < β)
    {x : Ordinal.{u}} (hx : x ∈ CsetSelf (psiResSelf β) β v) :
    ∃ δ, δ < β ∧ x ∈ CsetSelf (psiResSelf δ) δ v := by
  obtain ⟨n, hn⟩ := CsetSelf_mem_iff.1 hx
  clear hx
  induction n generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hn
    exact ⟨0, hβ0, Iio_Om_subset_CsetSelf hn⟩
  | succ n IH =>
    rw [Function.iterate_succ_apply'] at hn
    rcases hn with (h1 | h2) | h3
    · exact IH h1
    · obtain ⟨y, hy, z, hz, hyz⟩ := h2
      obtain ⟨δ1, hδ1, hy'⟩ := IH hy
      obtain ⟨δ2, hδ2, hz'⟩ := IH hz
      refine ⟨max δ1 δ2, max_lt hδ1 hδ2, ?_⟩
      have hy2 := CCSelf_mono (le_max_left δ1 δ2) v hy'
      have hz2 := CCSelf_mono (le_max_right δ1 δ2) v hz'
      rw [← hyz]
      exact CsetSelf_add_closed hy2 hz2
    · obtain ⟨u, ⟨ξ, ⟨hξX, ⟨hξβ, hξc⟩⟩, hξx⟩⟩ := Set.mem_iUnion.1 h3
      have hξβ' : ξ < β := hξβ
      obtain ⟨δ0, hδ0, hξ'⟩ := IH hξX
      have hξ1 : ξ + 1 < β := by rw [← Order.succ_eq_add_one]; exact hβ.succ_lt hξβ'
      refine ⟨max δ0 (ξ + 1), max_lt hδ0 hξ1, ?_⟩
      have hξδ : ξ < max δ0 (ξ + 1) :=
        lt_of_lt_of_le (lt_add_one ξ) (le_max_right δ0 (ξ + 1))
      have hδle : max δ0 (ξ + 1) ≤ β := le_of_lt (max_lt hδ0 hξ1)
      have hξmem := CCSelf_mono (le_max_left δ0 (ξ + 1)) v hξ'
      -- canonicity of ξ at bound ξ: param-invariant psiResSelf β → psiResSelf (max ..)
      have hξc0 : ξ ∈ CsetSelf (psiResSelf β) ξ u := hξc
      have hξc' : ξ ∈ CsetSelf (psiResSelf (max δ0 (ξ + 1))) ξ u := by
        rwa [CsetSelf_param_eq (p := psiResSelf β) (q := psiResSelf (max δ0 (ξ + 1)))
          (fun ζ uu hζ => by
            rw [psiResSelf, psiResSelf, if_pos (lt_trans hζ hξβ'),
              if_pos (lt_trans hζ hξδ)])] at hξc0
      have hclosed := CsetSelf_psi_closed hξmem hξδ u hξc'
      rw [psiResSelf, if_pos hξδ] at hclosed
      have hxv : x = psiSelf ξ u := by
        have : psiResSelf β ξ u = x := hξx
        rw [← this, psiResSelf, if_pos hξβ']
      rw [hxv]; exact hclosed

/-- **Buchholz general collapse (plateau) for `ψ^s`**: if every ordinal in `[α,β)`
is non-`a`-canonical, then `ψ^s_a` is constant on `[α,β]`. -/
theorem collapseSelf_le {a : ℕ} :
    ∀ β α : Ordinal.{u}, α ≤ β →
      (∀ γ, α ≤ γ → γ < β → γ ∉ CsetSelf (psiResSelf γ) γ a) →
      psiSelf α a = psiSelf β a := by
  intro β
  induction β using WellFoundedLT.induction with
  | _ β IHβ =>
    intro α hαβ hnc
    rcases eq_or_lt_of_le hαβ with rfl | hlt
    · rfl
    · have hβ0 : 0 < β := lt_of_le_of_lt bot_le hlt
      rcases Ordinal.zero_or_succ_or_isSuccLimit β with hz | ⟨δ, hδ⟩ | hl
      · rw [hz] at hβ0; exact absurd hβ0 (lt_irrefl 0)
      · obtain ⟨δ, rfl⟩ : ∃ δ', β = δ' + 1 := ⟨δ, by rw [← hδ, Order.succ_eq_add_one]⟩
        have hδβ : δ < δ + 1 := lt_add_one δ
        have hαδ : α ≤ δ :=
          Order.lt_succ_iff.1 (by rw [Order.succ_eq_add_one]; exact hlt)
        have e1 : psiSelf α a = psiSelf δ a :=
          IHβ δ hδβ α hαδ (fun γ hγ hγδ => hnc γ hγ (lt_trans hγδ hδβ))
        rw [e1]
        exact collapseSelf_succ (hnc δ hαδ hδβ)
      · refine le_antisymm (psiSelf_mono_arg hαβ a) ?_
        have hnotin : psiSelf α a ∉ CsetSelf (psiResSelf β) β a := by
          intro hin
          obtain ⟨δ, hδβ, hmem⟩ := CsetSelf_limit_sub hl hβ0 hin
          rcases lt_or_ge δ α with hδα | hαδ
          · exact psiSelf_notMem α a (CCSelf_mono hδα.le a hmem)
          · have e1 : psiSelf α a = psiSelf δ a :=
              IHβ δ hδβ α hαδ (fun γ hγ hγδ => hnc γ hγ (lt_trans hγδ hδβ))
            rw [e1] at hmem
            exact psiSelf_notMem δ a hmem
        rw [psiSelf_unfold β a]
        exact csInf_le' hnotin

end YAPSS
