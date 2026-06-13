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

end YAPSS
