/-
**Buchholz `ψ_v` collapsing functions on the Mathlib ordinals** (route A).
Lean port of `ord/psi.thy`.

Faithful transcription of Buchholz 1986 §1.  The PSS notation `Three` uses
only *finite* subscripts, so we index the collapsing functions by `ℕ`
(`v ∈ ℕ`); `ψ_ω` occurs only as the cofinal limit, never inside a term.
`Ω_v = ℵ_v` (`v > 0`), `Ω_0 = 1`.

Port conventions (Isabelle ZFC_in_HOL → Lean Mathlib):
  * the type `V` of sets, restricted to ordinals → `Ordinal.{0}`
  * `x ∈ elts α` (for ordinals)               → `x < α`
  * V-sets of ordinals                         → `Set Ordinal` + `Small.{u}`
  * `transrec`                                 → `WellFounded.fix lt_wf`
  * `LEAST`                                    → `sInf`
  * `vcard`/`gcard` arithmetic                 → `Cardinal.{1}` with `lift`
    (a `Set Ordinal.{0}` lives in `Type 1`)
-/
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Principal

namespace YAPSS

open Cardinal Ordinal Set

universe u

/-! ## The cardinals `Ω_v` -/

/-- `Ω_v`: `1` for `v = 0`, else `ℵ_v` (as an ordinal). -/
noncomputable def Om (v : ℕ) : Ordinal.{u} := if v = 0 then 1 else (ℵ_ v).ord

@[simp] theorem Om_zero : Om 0 = 1 := by simp [Om]

theorem Om_of_pos {v : ℕ} (hv : 0 < v) : Om v = (ℵ_ v).ord := by
  simp [Om, Nat.pos_iff_ne_zero.1 hv]

/-- Strictly increasing: `Ω_v < Ω_{v+1}` (needed so that `ψ_v α < Ω_{v+1}`). -/
theorem Om_lt_succ (v : ℕ) : Om v < Om (v + 1) := by
  cases v with
  | zero =>
    rw [Om_zero, Om_of_pos (by omega)]
    rw [Cardinal.lt_ord]
    simp only [Ordinal.card_one]
    calc (1 : Cardinal) < ℵ₀ := one_lt_aleph0
      _ ≤ ℵ_ (0 + 1 : ℕ) := aleph0_le_aleph _
  | succ k =>
    rw [Om_of_pos (by omega), Om_of_pos (by omega)]
    rw [Cardinal.ord_lt_ord, Cardinal.aleph_lt_aleph]
    exact_mod_cast Nat.lt_succ_self (k + 1)

/-! ## The sets `C_v(α)` and the collapsing functions `ψ_v(α)` (Buchholz §1)

`C_v(α)` = least set `⊇ Ω_v` closed under `+` and under `ξ ↦ ψ_u ξ` for
`ξ < α`, `u ∈ ℕ` (Buchholz's condition `ξ ∈ C_u(ξ)` omitted per his Remark).
Built as the countable union of the finite closure iterates of `Cstep` from
`Iio (Om v)`. -/

def Cstep (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (X : Set Ordinal.{u}) : Set Ordinal.{u} :=
  X ∪ Set.image2 (· + ·) X X ∪ ⋃ u : ℕ, (fun ξ => p ξ u) '' (X ∩ Set.Iio α)

def Citer (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) (n : ℕ) : Set Ordinal.{u} :=
  (Cstep p α)^[n] (Set.Iio (Om v))

def Cset (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) : Set Ordinal.{u} :=
  ⋃ n : ℕ, Citer p α v n

/-! ### Smallness -/

theorem small_Citer (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v n : ℕ) :
    Small.{u} (Citer p α v n) := by
  induction n with
  | zero => exact Ordinal.small_Iio _
  | succ n ih =>
    rw [Citer, Function.iterate_succ_apply']
    have h1 : Small.{u} ((Cstep p α)^[n] (Set.Iio (Om v))) := ih
    have h2 : Small.{u} (Set.image2 (· + ·) ((Cstep p α)^[n] (Set.Iio (Om v)))
        ((Cstep p α)^[n] (Set.Iio (Om v)))) := by
      rw [← Set.image_prod]
      have : Small.{u} (((Cstep p α)^[n] (Set.Iio (Om v)))
          ×ˢ ((Cstep p α)^[n] (Set.Iio (Om v))) : Set (Ordinal × Ordinal)) := by
        have e := Equiv.Set.prod ((Cstep p α)^[n] (Set.Iio (Om v)))
          ((Cstep p α)^[n] (Set.Iio (Om v)))
        exact small_of_injective e.injective
      exact small_image _ _
    have h3 : Small.{u} (⋃ u : ℕ, (fun ξ => p ξ u) ''
        (((Cstep p α)^[n] (Set.Iio (Om v))) ∩ Set.Iio α)) := by
      have : ∀ u : ℕ, Small.{u} ((fun ξ => p ξ u) ''
          (((Cstep p α)^[n] (Set.Iio (Om v))) ∩ Set.Iio α)) := by
        intro u
        have : Small.{u} (((Cstep p α)^[n] (Set.Iio (Om v))) ∩ Set.Iio α : Set Ordinal) :=
          small_subset Set.inter_subset_left
        exact small_image _ _
      exact small_iUnion _
    exact small_union _ _

theorem small_Cset (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) :
    Small.{u} (Cset p α v) := by
  have : ∀ n : ℕ, Small.{u} (Citer p α v n) := small_Citer p α v
  exact small_iUnion _

/-! ### `ψ` is well defined -/

/-- `C_v(α)` is small, so it cannot contain all ordinals. -/
theorem exists_notMem_Cset (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) :
    ∃ γ, γ ∉ Cset p α v := by
  have hsm : Small.{u} (Cset p α v) := small_Cset p α v
  have hbdd : BddAbove (Cset p α v) := Ordinal.bddAbove_iff_small.2 hsm
  refine ⟨sSup (Cset p α v) + 1, fun h => ?_⟩
  have := le_csSup hbdd h
  rw [Order.add_one_le_iff] at this
  exact lt_irrefl _ this

noncomputable def psi : Ordinal.{u} → ℕ → Ordinal.{u} :=
  Ordinal.lt_wf.fix (C := fun _ => ℕ → Ordinal.{u}) fun α IH v =>
    sInf {γ | γ ∉ Cset (fun ξ u => if h : ξ < α then IH ξ h u else 0) α v}

/-- `ψ` restricted below `α` (Isabelle's `(λξ∈elts α. psi ξ)`). -/
noncomputable def psiRes (α : Ordinal.{u}) : Ordinal.{u} → ℕ → Ordinal.{u} :=
  fun ξ u => if ξ < α then psi ξ u else 0

/-- `ψ_v(α)` with the conventional argument order. -/
noncomputable def Psi (v : ℕ) (α : Ordinal) : Ordinal := psi α v

/-- The defining equation of `psi`. -/
theorem psi_unfold (α : Ordinal.{u}) (v : ℕ) :
    psi α v = sInf {γ | γ ∉ Cset (psiRes α) α v} := by
  unfold psi
  rw [WellFounded.fix_eq]
  rfl

theorem psi_notMem (α : Ordinal) (v : ℕ) : psi α v ∉ Cset (psiRes α) α v := by
  rw [psi_unfold]
  exact csInf_mem (exists_notMem_Cset (psiRes α) α v)

/-! ## Closure properties of `C_v(α)` (Buchholz §1, conditions C1–C3) -/

theorem Citer_succ (p : Ordinal → ℕ → Ordinal) (α : Ordinal) (v n : ℕ) :
    Citer p α v (n + 1) = Cstep p α (Citer p α v n) := by
  rw [Citer, Citer, Function.iterate_succ_apply']

theorem Cstep_subset {p : Ordinal → ℕ → Ordinal} {α : Ordinal} {X : Set Ordinal} :
    X ⊆ Cstep p α X :=
  fun _ hx => Set.mem_union_left _ (Set.mem_union_left _ hx)

theorem Citer_mono_le {p : Ordinal → ℕ → Ordinal} {α : Ordinal} {v : ℕ} {m n : ℕ}
    (hmn : m ≤ n) : Citer p α v m ⊆ Citer p α v n := by
  induction n with
  | zero =>
    rw [Nat.le_zero.1 hmn]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · have := ih (by omega)
      rw [Citer_succ]
      exact this.trans Cstep_subset
    · rw [Nat.le_antisymm hmn h]

theorem Citer_subset_Cset {p : Ordinal → ℕ → Ordinal} {α : Ordinal} {v n : ℕ} :
    Citer p α v n ⊆ Cset p α v :=
  Set.subset_iUnion (Citer p α v) n

/-- C1: `Ω_v ⊆ C_v(α)`. -/
theorem Iio_Om_subset_Cset {p : Ordinal → ℕ → Ordinal} {α : Ordinal} {v : ℕ} :
    Set.Iio (Om v) ⊆ Cset p α v :=
  Citer_subset_Cset (n := 0)

theorem Cset_mem_iff {p : Ordinal → ℕ → Ordinal} {α x : Ordinal} {v : ℕ} :
    x ∈ Cset p α v ↔ ∃ n, x ∈ Citer p α v n := Set.mem_iUnion

theorem sum_mem_Cstep {p : Ordinal → ℕ → Ordinal} {α ξ η : Ordinal} {X : Set Ordinal}
    (hξ : ξ ∈ X) (hη : η ∈ X) : ξ + η ∈ Cstep p α X :=
  Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_image2_of_mem hξ hη))

theorem psiarg_mem_Cstep {p : Ordinal → ℕ → Ordinal} {α ξ : Ordinal} {X : Set Ordinal}
    (hξ : ξ ∈ X) (hα : ξ < α) (u : ℕ) : p ξ u ∈ Cstep p α X :=
  Set.mem_union_right _ (Set.mem_iUnion.2 ⟨u, Set.mem_image_of_mem _ ⟨hξ, hα⟩⟩)

/-- C2: closed under `+`. -/
theorem Cset_add_closed {p : Ordinal → ℕ → Ordinal} {α ξ η : Ordinal} {v : ℕ}
    (hξ : ξ ∈ Cset p α v) (hη : η ∈ Cset p α v) : ξ + η ∈ Cset p α v := by
  obtain ⟨m, hm⟩ := Cset_mem_iff.1 hξ
  obtain ⟨n, hn⟩ := Cset_mem_iff.1 hη
  have hm' : ξ ∈ Citer p α v (max m n) := Citer_mono_le (le_max_left m n) hm
  have hn' : η ∈ Citer p α v (max m n) := Citer_mono_le (le_max_right m n) hn
  have : ξ + η ∈ Citer p α v (max m n + 1) := by
    rw [Citer_succ]
    exact sum_mem_Cstep hm' hn'
  exact Citer_subset_Cset this

/-- C3: closed under `ξ ↦ p ξ u` for `ξ < α`. -/
theorem Cset_psi_closed {p : Ordinal → ℕ → Ordinal} {α ξ : Ordinal} {v : ℕ}
    (hξ : ξ ∈ Cset p α v) (hα : ξ < α) (u : ℕ) : p ξ u ∈ Cset p α v := by
  obtain ⟨n, hn⟩ := Cset_mem_iff.1 hξ
  have : p ξ u ∈ Citer p α v (n + 1) := by
    rw [Citer_succ]
    exact psiarg_mem_Cstep hn hα u
  exact Citer_subset_Cset this

/-! ## Basic properties of `ψ_v` (Buchholz Lemma 1.2) -/

/-- `Ω_v ≤ ψ_v(α)`: since `Ω_v ⊆ C_v(α)`, the least ordinal not in `C_v(α)`
is `≥ Ω_v`. -/
theorem Om_le_psi (α : Ordinal) (v : ℕ) : Om v ≤ psi α v := by
  by_contra h
  push Not at h
  exact psi_notMem α v (Iio_Om_subset_Cset h)

/-- `Ω_v` is additive principal (`1` for `v=0`, an infinite cardinal's `ord`
otherwise). -/
theorem Om_isPrincipal (v : ℕ) : Ordinal.IsPrincipal (· + ·) (Om v) := by
  rcases Nat.eq_zero_or_pos v with h | h
  · subst h; rw [Om_zero]; exact isPrincipal_add_one
  · rw [Om_of_pos h]
    intro a b ha hb
    rw [lt_ord] at ha hb
    show a + b < (ℵ_ (v : Ordinal)).ord
    rw [lt_ord, card_add]
    exact add_lt_of_lt (aleph0_le_aleph _) ha hb

/-- At bound `0`, `C_v(0) = Iio Ω_v`: the `ψ`-generators are vacuous (`X ∩ Iio 0
= ∅`) and `Iio Ω_v` is closed under `+` (`Om_isPrincipal`). -/
theorem Cset_zero (v : ℕ) : Cset (psiRes 0) 0 v = Set.Iio (Om v) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Cset_mem_iff.1 hx
    clear hx
    induction n generalizing x with
    | zero => rwa [Citer, Function.iterate_zero, id_eq] at hn
    | succ n IH =>
      rw [Citer_succ, Cstep] at hn
      rcases hn with (h1 | h2) | h3
      · exact IH h1
      · obtain ⟨y, hy, z, hz, hyz⟩ := h2
        dsimp only at hyz
        rw [← hyz]
        exact (Om_isPrincipal v) (IH hy) (IH hz)
      · obtain ⟨u, hu⟩ := Set.mem_iUnion.1 h3
        obtain ⟨ξ, ⟨_, hξ0⟩, _⟩ := hu
        simp at hξ0
  · exact Iio_Om_subset_Cset

/-- **Buchholz Lemma 1.2(a)**: `ψ_v 0 = Ω_v`. -/
theorem psi_zero (v : ℕ) : psi 0 v = Om v := by
  refine le_antisymm ?_ (Om_le_psi 0 v)
  rw [psi_unfold, Cset_zero]
  exact csInf_le' (show Om v ∈ {γ | γ ∉ Set.Iio (Om v)} by simp)

/-! ## Monotonicity of `C_v(α)` and `ψ_v(α)` in `α` (Buchholz Lemma 1.2(d)) -/

theorem Cstep_mono_param {p q : Ordinal.{u} → ℕ → Ordinal.{u}} {α β : Ordinal.{u}}
    {X Y : Set Ordinal.{u}} (hαβ : α ≤ β) (hpq : ∀ ξ u, ξ < α → p ξ u = q ξ u)
    (hXY : X ⊆ Y) : Cstep p α X ⊆ Cstep q β Y := by
  intro x hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · exact Set.mem_union_left _ (Set.mem_union_left _ (hXY hx))
    · obtain ⟨ξ, hξ, η, hη, rfl⟩ := Set.mem_image2.1 hx
      exact Set.mem_union_left _
        (Set.mem_union_right _ (Set.mem_image2_of_mem (hXY hξ) (hXY hη)))
  · obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hx
    obtain ⟨ξ, ⟨hξX, hξα⟩, rfl⟩ := hw
    show p ξ w ∈ Cstep q β Y
    rw [hpq ξ w hξα]
    exact Set.mem_union_right _ (Set.mem_iUnion.2
      ⟨w, Set.mem_image_of_mem _ ⟨hXY hξX, lt_of_lt_of_le hξα hαβ⟩⟩)

theorem Citer_mono_param {p q : Ordinal → ℕ → Ordinal} {α β : Ordinal} {v : ℕ}
    (hαβ : α ≤ β) (hpq : ∀ ξ u, ξ < α → p ξ u = q ξ u) (n : ℕ) :
    Citer p α v n ⊆ Citer q β v n := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rw [Citer_succ, Citer_succ]
    exact Cstep_mono_param hαβ hpq ih

theorem Cset_mono_param {p q : Ordinal → ℕ → Ordinal} {α β : Ordinal} {v : ℕ}
    (hαβ : α ≤ β) (hpq : ∀ ξ u, ξ < α → p ξ u = q ξ u) :
    Cset p α v ⊆ Cset q β v := by
  intro x hx
  obtain ⟨n, hn⟩ := Cset_mem_iff.1 hx
  exact Cset_mem_iff.2 ⟨n, Citer_mono_param hαβ hpq n hn⟩

/-- Specialised to `p = q = ψ`: `α ≤ β → C_v(α) ⊆ C_v(β)`. -/
theorem CC_mono {α β : Ordinal} (hαβ : α ≤ β) (v : ℕ) :
    Cset (psiRes α) α v ⊆ Cset (psiRes β) β v := by
  apply Cset_mono_param hαβ
  intro ξ u hξ
  rw [psiRes, psiRes, if_pos hξ, if_pos (lt_of_lt_of_le hξ hαβ)]

/-- Weak monotonicity in the argument (Buchholz 1.2(d)). -/
theorem psi_mono_arg {α β : Ordinal.{u}} (hαβ : α ≤ β) (v : ℕ) :
    psi α v ≤ psi β v := by
  by_contra h
  push Not at h
  have hmem : psi β v ∈ Cset (psiRes α) α v := by
    by_contra nin
    have hle : psi α v ≤ psi β v := by
      rw [psi_unfold]
      exact csInf_le' nin
    exact absurd hle (not_le.2 h)
  exact psi_notMem β v (CC_mono hαβ v hmem)

/-- **Strict monotonicity (Buchholz Lemma 1.3)**: if `α < β` and `α ∈ C_v(α)`
then `ψ_v(α) < ψ_v(β)`. -/
theorem psi_strict_mono_arg {α β : Ordinal} (hαβ : α < β)
    {v : ℕ} (hα : α ∈ Cset (psiRes α) α v) : psi α v < psi β v := by
  have le : α ≤ β := hαβ.le
  have aβ : α ∈ Cset (psiRes β) β v := CC_mono le v hα
  have hmem : psi α v ∈ Cset (psiRes β) β v := by
    have := Cset_psi_closed aβ hαβ v
    rwa [psiRes, if_pos hαβ] at this
  have hne : psi α v ≠ psi β v := fun he => psi_notMem β v (he ▸ hmem)
  exact lt_of_le_of_ne (psi_mono_arg le v) hne

/-! ## `ψ_v(α)` is additive principal (Buchholz Lemma 1.2(b)) -/

/-- Every ordinal below `ψ_v(α)` already lies in `C_v(α)` (because `ψ_v(α)`
is the *least* ordinal outside it). -/
theorem below_psi_mem_Cset {α δ : Ordinal} {v : ℕ} (hδ : δ < psi α v) :
    δ ∈ Cset (psiRes α) α v := by
  by_contra nin
  have : psi α v ≤ δ := by
    rw [psi_unfold]
    exact csInf_le' nin
  exact absurd hδ (not_lt.2 this)

/-- **Lemma 1.2(b)**: `ψ_v(α)` is additive principal — a sum of two ordinals
below it stays below it.  Proof by transfinite induction on the second
summand. -/
theorem psi_add_principal {α β γ : Ordinal} {v : ℕ}
    (hβ : β < psi α v) (hγ : γ < psi α v) : β + γ < psi α v := by
  have betaC : β ∈ Cset (psiRes α) α v := below_psi_mem_Cset hβ
  have main : ∀ γ, γ < psi α v → β + γ < psi α v := by
    intro γ
    induction γ using WellFoundedLT.induction with
    | _ γ IH =>
      intro hγ
      rcases Ordinal.zero_or_succ_or_isSuccLimit γ with rfl | ⟨η, hη⟩ | hl
      · simpa using hβ
      · obtain ⟨η, rfl⟩ : ∃ η', γ = η' + 1 := ⟨η, by rw [← hη, Order.succ_eq_add_one]⟩
        have ηγ : η < η + 1 := lt_add_one η
        have ed : η < psi α v := lt_trans ηγ hγ
        have bh : β + η < psi α v := IH η ηγ ed
        have bhC : β + η ∈ Cset (psiRes α) α v := below_psi_mem_Cset bh
        have d1 : (1 : Ordinal) < psi α v := by
          have h1γ : (1 : Ordinal) ≤ η + 1 := le_add_self
          exact lt_of_le_of_lt h1γ hγ
        have oneC : (1 : Ordinal) ∈ Cset (psiRes α) α v := below_psi_mem_Cset d1
        have bg : β + (η + 1) = (β + η) + 1 := by rw [add_assoc]
        have inC : β + (η + 1) ∈ Cset (psiRes α) α v := by
          rw [bg]
          exact Cset_add_closed bhC oneC
        have le : β + (η + 1) ≤ psi α v := by
          rw [bg, Order.add_one_le_iff]
          exact bh
        exact lt_of_le_of_ne le fun he => psi_notMem α v (he ▸ inC)
      · have le : β + γ ≤ psi α v := by
          rw [Ordinal.add_le_iff_of_isSuccLimit hl]
          intro z hz
          exact (IH z hz (lt_trans hz hγ)).le
        have gC : γ ∈ Cset (psiRes α) α v := below_psi_mem_Cset hγ
        have inC : β + γ ∈ Cset (psiRes α) α v := Cset_add_closed betaC gC
        exact lt_of_le_of_ne le fun he => psi_notMem α v (he ▸ inC)
  exact main γ hγ

/-! ## The cardinality bound (Buchholz Lemma 1.2(c)): `ψ_v(α) < Ω_{v+1}`

`|C_v(α)| ≤ Ω_v ⊔ ω < Ω_{v+1}`, since `C_v(α)` is the closure of `Iio (Om v)`
under `+` and the countably many maps `ψ_u`.  All cardinality arithmetic is
done in `Cardinal.{1}` (a `Set Ordinal.{0}` lives in `Type 1`). -/

/-- `κ = Ω_v ⊔ ω`, lifted one universe up. -/
noncomputable def OmKappa (v : ℕ) : Cardinal.{u + 1} :=
  Cardinal.lift.{u + 1, u} ((Om v).card ⊔ ℵ₀)

theorem aleph0_le_OmKappa (v : ℕ) : ℵ₀ ≤ OmKappa.{u} v := by
  rw [OmKappa, show (ℵ₀ : Cardinal.{u + 1}) = Cardinal.lift.{u + 1, u} ℵ₀ from
    (Cardinal.lift_aleph0).symm, Cardinal.lift_le]
  exact le_sup_right

theorem mk_Iio_le_OmKappa (v : ℕ) : #(Set.Iio (Om.{u} v)) ≤ OmKappa.{u} v := by
  rw [Cardinal.mk_Iio_ordinal, OmKappa, Cardinal.lift_le]
  exact le_sup_left

private theorem iUnion_nat_eq_ulift {f : ℕ → Set Ordinal.{u}} :
    (⋃ u : ℕ, f u) = ⋃ u : ULift.{u + 1} ℕ, f u.down := by
  ext x
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨u, h⟩ => ⟨⟨u⟩, h⟩, fun ⟨u, h⟩ => ⟨u.down, h⟩⟩

theorem mk_Citer_le (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v n : ℕ) :
    #(Citer p α v n) ≤ OmKappa.{u} v := by
  have infk : ℵ₀ ≤ OmKappa v := aleph0_le_OmKappa v
  induction n with
  | zero => exact mk_Iio_le_OmKappa v
  | succ n IH =>
    rw [Citer_succ]
    set X := Citer p α v n with hX
    have hA : #(X : Set Ordinal) ≤ OmKappa v := IH
    have hB : #(Set.image2 (· + ·) X X : Set Ordinal) ≤ OmKappa v := by
      calc #(Set.image2 (· + ·) X X : Set Ordinal) ≤ #X * #X := Cardinal.mk_image2_le
        _ ≤ OmKappa v * OmKappa v := mul_le_mul' hA hA
        _ = OmKappa v := Cardinal.mul_eq_self infk
    have hC : #(⋃ u : ℕ, (fun ξ => p ξ u) '' (X ∩ Set.Iio α) : Set Ordinal)
        ≤ OmKappa v := by
      rw [iUnion_nat_eq_ulift]
      calc #(⋃ u : ULift.{u + 1} ℕ, (fun ξ => p ξ u.down) '' (X ∩ Set.Iio α) : Set Ordinal)
          ≤ #(ULift.{u + 1} ℕ) * ⨆ u : ULift.{u + 1} ℕ, #((fun ξ => p ξ u.down) '' (X ∩ Set.Iio α) : Set Ordinal) :=
            Cardinal.mk_iUnion_le _
        _ ≤ ℵ₀ * OmKappa v := by
            apply mul_le_mul'
            · rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
            · apply ciSup_le'
              intro u
              calc #((fun ξ => p ξ u.down) '' (X ∩ Set.Iio α) : Set Ordinal)
                  ≤ #(X ∩ Set.Iio α : Set Ordinal) := Cardinal.mk_image_le
                _ ≤ #(X : Set Ordinal) := Cardinal.mk_le_mk_of_subset Set.inter_subset_left
                _ ≤ OmKappa v := hA
        _ ≤ OmKappa v * OmKappa v := mul_le_mul' infk le_rfl
        _ = OmKappa v := Cardinal.mul_eq_self infk
    calc #(Cstep p α X) ≤ #((X ∪ Set.image2 (· + ·) X X : Set Ordinal))
          + #(⋃ u : ℕ, (fun ξ => p ξ u) '' (X ∩ Set.Iio α) : Set Ordinal) :=
        Cardinal.mk_union_le _ _
      _ ≤ (#(X : Set Ordinal) + #(Set.image2 (· + ·) X X : Set Ordinal))
          + #(⋃ u : ℕ, (fun ξ => p ξ u) '' (X ∩ Set.Iio α) : Set Ordinal) := by
        exact add_le_add (Cardinal.mk_union_le _ _) le_rfl
      _ ≤ (OmKappa v + OmKappa v) + OmKappa v := by
        exact add_le_add (add_le_add hA hB) hC
      _ = OmKappa v := by
        rw [Cardinal.add_eq_self infk, Cardinal.add_eq_self infk]

theorem mk_Cset_le (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) :
    #(Cset p α v) ≤ OmKappa.{u} v := by
  have infk : ℵ₀ ≤ OmKappa v := aleph0_le_OmKappa v
  rw [Cset, iUnion_nat_eq_ulift]
  calc #(⋃ n : ULift.{u + 1} ℕ, Citer p α v n.down : Set Ordinal)
      ≤ #(ULift.{u + 1} ℕ) * ⨆ n : ULift.{u + 1} ℕ, #(Citer p α v n.down : Set Ordinal) :=
        Cardinal.mk_iUnion_le _
    _ ≤ ℵ₀ * OmKappa v := by
        apply mul_le_mul'
        · rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
        · exact ciSup_le' fun n => mk_Citer_le p α v n.down
    _ ≤ OmKappa v * OmKappa v := mul_le_mul' infk le_rfl
    _ = OmKappa v := Cardinal.mul_eq_self infk

theorem OmKappa_lt_aleph_succ (v : ℕ) :
    OmKappa.{u} v < Cardinal.lift.{u + 1, u} (ℵ_ (v + 1 : ℕ)) := by
  rw [OmKappa, Cardinal.lift_lt]
  have h0 : ℵ₀ < ℵ_ (v + 1 : ℕ) := by
    calc ℵ₀ = ℵ_ (0 : Ordinal) := (Cardinal.aleph_zero).symm
      _ < ℵ_ (v + 1 : ℕ) := by
        rw [Cardinal.aleph_lt_aleph]
        exact_mod_cast Nat.pos_of_ne_zero (by omega)
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp only [Om_zero, Ordinal.card_one]
    rw [sup_lt_iff]
    exact ⟨lt_trans one_lt_aleph0 h0, h0⟩
  · rw [Om_of_pos hv, Cardinal.card_ord, sup_lt_iff]
    constructor
    · rw [Cardinal.aleph_lt_aleph]
      exact_mod_cast Nat.lt_succ_self v
    · exact h0

/-- **Buchholz Lemma 1.2(c)**: `ψ_v(α) < Ω_{v+1}`. -/
theorem psi_lt_Om_succ (α : Ordinal.{u}) (v : ℕ) : psi α v < Om (v + 1) := by
  by_contra hge
  push Not at hge
  have allin : Set.Iio (Om (v + 1)) ⊆ Cset (psiRes α) α v := by
    intro δ hδ
    exact below_psi_mem_Cset (lt_of_lt_of_le hδ hge)
  have hcard : Cardinal.lift.{u + 1, u} (ℵ_ (v + 1 : ℕ)) ≤ OmKappa.{u} v := by
    calc Cardinal.lift.{u + 1, u} (ℵ_ (v + 1 : ℕ))
        = Cardinal.lift.{u + 1, u} (Om (v + 1)).card := by
          rw [Om_of_pos (by omega), Cardinal.card_ord]
      _ = #(Set.Iio (Om (v + 1))) := (Cardinal.mk_Iio_ordinal _).symm
      _ ≤ #(Cset (psiRes α) α v) := Cardinal.mk_le_mk_of_subset allin
      _ ≤ OmKappa v := mk_Cset_le _ _ _
  exact absurd hcard (not_le.2 (OmKappa_lt_aleph_succ v))

/-- **Subscript jump**: a strictly larger subscript dominates regardless of
arguments (`ψ_a(α) < Ω_{a+1} ≤ Ω_e ≤ ψ_e(β)`).  This is the engine of the
subscript-first order (Buchholz Lemma 2.2(c), subscript case). -/
theorem one_le_Om (b : ℕ) : (1 : Ordinal) ≤ Om b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · rw [Om_of_pos hb]
    have h : (1 : Ordinal) < (ℵ_ (b : ℕ)).ord := by
      rw [Cardinal.lt_ord, Ordinal.card_one]
      exact lt_of_lt_of_le one_lt_aleph0 (aleph0_le_aleph _)
    exact h.le

/-- `1 = ψ_0 0 ∈ C_v(α)` whenever `α > 0` (so `0 < α` is a valid generator arg). -/
theorem one_mem_Cset {α : Ordinal} {v : ℕ} (hα : 0 < α) :
    (1 : Ordinal) ∈ Cset (psiRes α) α v := by
  have h0 : (0 : Ordinal) ∈ Cset (psiRes α) α v :=
    Iio_Om_subset_Cset (lt_of_lt_of_le zero_lt_one (one_le_Om v))
  have := Cset_psi_closed h0 hα 0
  rwa [psiRes, if_pos hα, psi_zero, Om_zero] at this

/-- **Canonical predecessor ⟹ canonical successor**: `δ ∈ C_a(δ) → δ+1 ∈ C_a(δ+1)`
(add `δ` and `1`).  The successor step of Buchholz 1.7's canonicity. -/
theorem canon_succ {a : ℕ} {δ : Ordinal} (hδ : δ ∈ Cset (psiRes δ) δ a) :
    δ + 1 ∈ Cset (psiRes (δ + 1)) (δ + 1) a := by
  have hδ' : δ ∈ Cset (psiRes (δ + 1)) (δ + 1) a := CC_mono (lt_add_one δ).le a hδ
  have h1 : (1 : Ordinal) ∈ Cset (psiRes (δ + 1)) (δ + 1) a :=
    one_mem_Cset (lt_of_lt_of_le zero_lt_one le_add_self)
  exact Cset_add_closed hδ' h1

/-- `C_v(α)` is closed under multiplication by a natural (`x·n` = `n` copies of
`x` summed).  Used to build `Iio (ω^{α+1}) ⊆ C` for Buchholz 1.7. -/
theorem Cset_mul_nat {α : Ordinal} {v : ℕ} {x : Ordinal}
    (hx : x ∈ Cset (psiRes α) α v) (n : ℕ) :
    x * (n : Ordinal) ∈ Cset (psiRes α) α v := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, mul_zero]
    exact Iio_Om_subset_Cset (lt_of_lt_of_le zero_lt_one (one_le_Om v))
  | succ n IH =>
    rw [Nat.cast_succ, mul_add, mul_one]
    exact Cset_add_closed IH hx

/-- `Iio (ω^{α+1}) ⊆ C_0(α+1)`, given `ω^α ∈ C_0(α+1)` and `Iio (ω^α) ⊆ C_0(α+1)`:
every `γ < ω^{α+1}` is `< ω^α · n` (`lt_omega0_opow_succ`), so `γ = ω^α·k + s`
with `s < ω^α`; `ω^α·k ∈ C` (`Cset_mul_nat`) and `s ∈ C`, closed under `+`.
The `≥`-direction of Buchholz 1.7(a)'s successor step. -/
theorem Iio_opow_succ_subset (α : Ordinal)
    (hω : ω ^ α ∈ Cset (psiRes (α + 1)) (α + 1) 0)
    (hbelow : ∀ s, s < ω ^ α → s ∈ Cset (psiRes (α + 1)) (α + 1) 0) :
    ∀ γ, γ < ω ^ (α + 1) → γ ∈ Cset (psiRes (α + 1)) (α + 1) 0 := by
  intro γ hγ
  rw [show (α + 1) = Order.succ α from (Order.succ_eq_add_one α).symm] at hγ
  obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 hγ
  clear hγ
  induction n generalizing γ with
  | zero => simp at hn
  | succ n IH =>
    rw [Nat.cast_succ, mul_add, mul_one] at hn
    rcases lt_or_ge γ (ω ^ α * (n : Ordinal)) with hlt | hge
    · exact IH γ hlt
    · obtain ⟨s, rfl⟩ := exists_add_of_le hge
      have hs : s < ω ^ α := (add_lt_add_iff_left _).1 hn
      exact Cset_add_closed (Cset_mul_nat hω n) (hbelow s hs)

theorem Om_mono {a b : ℕ} (hab : a ≤ b) : Om a ≤ Om b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Om_zero]
    exact one_le_Om b
  · have hb : 0 < b := lt_of_lt_of_le ha hab
    rw [Om_of_pos ha, Om_of_pos hb]
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · rw [Cardinal.ord_le_ord, Cardinal.aleph_le_aleph]
      exact_mod_cast hab

theorem psi_subscript_jump {a e : ℕ} (hae : a < e) (α β : Ordinal.{u}) :
    psi α a < psi β e := by
  calc psi α a < Om (a + 1) := psi_lt_Om_succ α a
    _ ≤ Om e := Om_mono (by omega)
    _ ≤ psi β e := Om_le_psi β e

/-! ## Additive-principal abstraction -/

/-- An ordinal `δ` is additive principal when it is positive and a sum of two
ordinals below it stays below it. -/
def addprinc (δ : Ordinal) : Prop :=
  0 < δ ∧ ∀ β γ, β < δ → γ < δ → β + γ < δ

theorem psi_addprinc (α : Ordinal) (v : ℕ) : addprinc (psi α v) := by
  constructor
  · calc (0 : Ordinal) < 1 := zero_lt_one
      _ ≤ Om v := one_le_Om v
      _ ≤ psi α v := Om_le_psi α v
  · exact fun β γ hβ hγ => psi_add_principal hβ hγ

end YAPSS
