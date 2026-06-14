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

/-- `Iio (ω^{β+1}) ⊆ C_v(δ)`, given `ω^β ∈ C_v(δ)` and `Iio (ω^β) ⊆ C_v(δ)`:
every `γ < ω^{β+1}` is `< ω^β · n` (`lt_omega0_opow_succ`), so `γ = ω^β·k + s`
with `s < ω^β`; `ω^β·k ∈ C` (`Cset_mul_nat`) and `s ∈ C`, closed under `+`.
The `≥`-direction of Buchholz 1.7's successor step (level/bound-generic). -/
theorem Iio_opow_succ_subset {v : ℕ} {δ : Ordinal} (β : Ordinal)
    (hω : ω ^ β ∈ Cset (psiRes δ) δ v)
    (hbelow : ∀ s, s < ω ^ β → s ∈ Cset (psiRes δ) δ v) :
    ∀ γ, γ < ω ^ (β + 1) → γ ∈ Cset (psiRes δ) δ v := by
  intro γ hγ
  rw [show (β + 1) = Order.succ β from (Order.succ_eq_add_one β).symm] at hγ
  obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 hγ
  clear hγ
  induction n generalizing γ with
  | zero => simp at hn
  | succ n IH =>
    rw [Nat.cast_succ, mul_add, mul_one] at hn
    rcases lt_or_ge γ (ω ^ β * (n : Ordinal)) with hlt | hge
    · exact IH γ hlt
    · obtain ⟨s, rfl⟩ := exists_add_of_le hge
      have hs : s < ω ^ β := (add_lt_add_iff_left _).1 hn
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

/-! ## With-condition collapsing functions `ψ^w_v` (Buchholz's *faithful* §1)

Buchholz 1986 defines `C_v(α)` with the generator side-condition `ξ ∈ C_u(ξ)`
(canonicity).  The omitted-condition port above drops it (his Remark p197).  The
with-condition version makes Buchholz 1.4(b) (the canonical-witness lemma, the
genuine core of the necessity direction) hold *by definition* — the generator
carries canonicity, so any extracted witness is canonical.

We add `ψ^w` (`psiW`) **additively**, in parallel with `psi`, so the existing
omitted development stays green.  `CstepW` = `Cstep` with the generator clause
intersected by the canonicity test `{ξ | ξ ∈ Cset p ξ u}`.  Since `ψ^w` fires a
*subset* of the omitted generators, `CsetW ⊆ Cset`, which gives smallness (hence
well-definedness) for free. -/

/-- With-condition closure step: the `ψ`-generator fires only for `u`-canonical
arguments (`ξ ∈ Cset p ξ u`). -/
def CstepW (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (X : Set Ordinal.{u}) :
    Set Ordinal.{u} :=
  X ∪ Set.image2 (· + ·) X X ∪
    ⋃ u : ℕ, (fun ξ => p ξ u) '' (X ∩ Set.Iio α ∩ {ξ | ξ ∈ Cset p ξ u})

def CiterW (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) (n : ℕ) :
    Set Ordinal.{u} :=
  (CstepW p α)^[n] (Set.Iio (Om v))

def CsetW (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) : Set Ordinal.{u} :=
  ⋃ n : ℕ, CiterW p α v n

theorem CiterW_succ (p : Ordinal → ℕ → Ordinal) (α : Ordinal) (v n : ℕ) :
    CiterW p α v (n + 1) = CstepW p α (CiterW p α v n) := by
  rw [CiterW, CiterW, Function.iterate_succ_apply']

theorem CiterW_subset_CsetW {p : Ordinal.{u} → ℕ → Ordinal.{u}} {α : Ordinal.{u}}
    {v n : ℕ} : CiterW p α v n ⊆ CsetW p α v := Set.subset_iUnion (CiterW p α v) n

theorem CsetW_mem_iff {p : Ordinal → ℕ → Ordinal} {α x : Ordinal} {v : ℕ} :
    x ∈ CsetW p α v ↔ ∃ n, x ∈ CiterW p α v n := Set.mem_iUnion

/-- with-C fires a subset of omitted generators: `CstepW ⊆ Cstep`. -/
theorem CstepW_subset_Cstep (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u})
    {X : Set Ordinal.{u}} : CstepW p α X ⊆ Cstep p α X := by
  intro x hx
  rcases hx with (h | h) | h
  · exact Set.mem_union_left _ (Set.mem_union_left _ h)
  · exact Set.mem_union_left _ (Set.mem_union_right _ h)
  · obtain ⟨u, hu⟩ := Set.mem_iUnion.1 h
    obtain ⟨ξ, ⟨⟨hξX, hξα⟩, _hcanon⟩, hξx⟩ := hu
    exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨u, ⟨ξ, ⟨hξX, hξα⟩, hξx⟩⟩)

theorem CiterW_subset_Citer (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u})
    (v n : ℕ) : CiterW p α v n ⊆ Citer p α v n := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rw [CiterW_succ, Citer_succ]
    exact (CstepW_subset_Cstep p α).trans (Cstep_mono_param (le_refl α)
      (fun _ _ _ => rfl) ih)

/-- **`CsetW ⊆ Cset`**: the with-condition set is contained in the omitted one. -/
theorem CsetW_subset_Cset (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u})
    (v : ℕ) : CsetW p α v ⊆ Cset p α v := by
  intro x hx
  obtain ⟨n, hn⟩ := CsetW_mem_iff.1 hx
  exact Citer_subset_Cset (CiterW_subset_Citer p α v n hn)

/-- well-definedness input: `CsetW` is small (subset of the small `Cset`). -/
theorem small_CsetW (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) :
    Small.{u} (CsetW p α v) :=
  have : Small.{u} (Cset p α v) := small_Cset p α v
  small_subset (CsetW_subset_Cset p α v)

theorem exists_notMem_CsetW (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u})
    (v : ℕ) : ∃ γ, γ ∉ CsetW p α v := by
  have hsm : Small.{u} (CsetW p α v) := small_CsetW p α v
  have hbdd : BddAbove (CsetW p α v) := Ordinal.bddAbove_iff_small.2 hsm
  refine ⟨sSup (CsetW p α v) + 1, fun h => ?_⟩
  have := le_csSup hbdd h
  rw [Order.add_one_le_iff] at this
  exact lt_irrefl _ this

/-- With-condition collapsing function `ψ^w_v(α)` = least ordinal not in
`C^w_v(α)`.  Defined by transfinite recursion in parallel with `psi`. -/
noncomputable def psiW : Ordinal.{u} → ℕ → Ordinal.{u} :=
  Ordinal.lt_wf.fix (C := fun _ => ℕ → Ordinal.{u}) fun α IH v =>
    sInf {γ | γ ∉ CsetW (fun ξ u => if h : ξ < α then IH ξ h u else 0) α v}

/-- `ψ^w` restricted below `α`. -/
noncomputable def psiResW (α : Ordinal.{u}) : Ordinal.{u} → ℕ → Ordinal.{u} :=
  fun ξ u => if ξ < α then psiW ξ u else 0

theorem psiW_unfold (α : Ordinal.{u}) (v : ℕ) :
    psiW α v = sInf {γ | γ ∉ CsetW (psiResW α) α v} := by
  unfold psiW
  rw [WellFounded.fix_eq]
  rfl

theorem psiW_notMem (α : Ordinal) (v : ℕ) : psiW α v ∉ CsetW (psiResW α) α v := by
  rw [psiW_unfold]
  exact csInf_mem (exists_notMem_CsetW (psiResW α) α v)

/-! ### §1 port for `ψ^w` (with-condition).  Buchholz 1.2–1.4(a). -/

/-- C1 for with-C: `Iio Ω_v ⊆ C^w_v(α)`. -/
theorem Iio_Om_subset_CsetW {p : Ordinal → ℕ → Ordinal} {α : Ordinal} {v : ℕ} :
    Set.Iio (Om v) ⊆ CsetW p α v := by
  intro x hx
  exact CiterW_subset_CsetW (n := 0) (by simpa [CiterW] using hx)

/-- C2 for with-C: closed under `+` (no canonicity needed). -/
theorem CsetW_add_closed {p : Ordinal → ℕ → Ordinal} {α ξ η : Ordinal} {v : ℕ}
    (hξ : ξ ∈ CsetW p α v) (hη : η ∈ CsetW p α v) : ξ + η ∈ CsetW p α v := by
  obtain ⟨m, hm⟩ := CsetW_mem_iff.1 hξ
  obtain ⟨n, hn⟩ := CsetW_mem_iff.1 hη
  have mono : ∀ {a b : ℕ}, a ≤ b → CiterW p α v a ⊆ CiterW p α v b := by
    intro a b hab
    induction b with
    | zero => rw [Nat.le_zero.1 hab]
    | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · rw [CiterW_succ]
        exact (ih (by omega)).trans
          (fun _ hx => Set.mem_union_left _ (Set.mem_union_left _ hx))
      · rw [Nat.le_antisymm hab h]
  have hm' : ξ ∈ CiterW p α v (max m n) := mono (le_max_left m n) hm
  have hn' : η ∈ CiterW p α v (max m n) := mono (le_max_right m n) hn
  refine CiterW_subset_CsetW (n := max m n + 1) ?_
  rw [CiterW_succ]
  exact Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_image2_of_mem hm' hn'))

/-- C3 for with-C: closed under `ξ ↦ p ξ u` for `ξ < α` **canonical** (`ξ ∈ Cset
p ξ u`).  This is the only closure clause that gains a hypothesis over the
omitted version. -/
theorem CsetW_psi_closed {p : Ordinal → ℕ → Ordinal} {α ξ : Ordinal} {v : ℕ}
    (hξ : ξ ∈ CsetW p α v) (hα : ξ < α) (u : ℕ) (hcanon : ξ ∈ Cset p ξ u) :
    p ξ u ∈ CsetW p α v := by
  obtain ⟨n, hn⟩ := CsetW_mem_iff.1 hξ
  refine CiterW_subset_CsetW (n := n + 1) ?_
  rw [CiterW_succ]
  exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨u,
    Set.mem_image_of_mem _ ⟨⟨hn, hα⟩, hcanon⟩⟩)

/-- with-C parameter-monotonicity.  The canonicity test `ξ ∈ Cset p ξ u` is
invariant under swapping `p`/`q` that agree below `α`, because that set only
references arguments `< ξ < α`. -/
theorem CstepW_mono_param {p q : Ordinal.{u} → ℕ → Ordinal.{u}} {α β : Ordinal.{u}}
    {X Y : Set Ordinal.{u}} (hαβ : α ≤ β) (hpq : ∀ ξ u, ξ < α → p ξ u = q ξ u)
    (hXY : X ⊆ Y) : CstepW p α X ⊆ CstepW q β Y := by
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact Set.mem_union_left _ (Set.mem_union_left _ (hXY hx))
  · obtain ⟨ξ, hξ, η, hη, rfl⟩ := Set.mem_image2.1 hx
    exact Set.mem_union_left _
      (Set.mem_union_right _ (Set.mem_image2_of_mem (hXY hξ) (hXY hη)))
  · obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hx
    obtain ⟨ξ, ⟨⟨hξX, hξα⟩, hξcanon⟩, rfl⟩ := hw
    show p ξ w ∈ CstepW q β Y
    rw [hpq ξ w hξα]
    refine Set.mem_union_right _ (Set.mem_iUnion.2 ⟨w, Set.mem_image_of_mem _
      ⟨⟨hXY hξX, lt_of_lt_of_le hξα hαβ⟩, ?_⟩⟩)
    exact Cset_mono_param (le_refl ξ) (fun ζ uu hζ => hpq ζ uu (lt_trans hζ hξα)) hξcanon

theorem CiterW_mono_param {p q : Ordinal → ℕ → Ordinal} {α β : Ordinal} {v : ℕ}
    (hαβ : α ≤ β) (hpq : ∀ ξ u, ξ < α → p ξ u = q ξ u) (n : ℕ) :
    CiterW p α v n ⊆ CiterW q β v n := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => rw [CiterW_succ, CiterW_succ]; exact CstepW_mono_param hαβ hpq ih

theorem CsetW_mono_param {p q : Ordinal → ℕ → Ordinal} {α β : Ordinal} {v : ℕ}
    (hαβ : α ≤ β) (hpq : ∀ ξ u, ξ < α → p ξ u = q ξ u) :
    CsetW p α v ⊆ CsetW q β v := by
  intro x hx
  obtain ⟨n, hn⟩ := CsetW_mem_iff.1 hx
  exact CiterW_subset_CsetW (CiterW_mono_param hαβ hpq n hn)

/-- **Buchholz 1.2(d) for with-C**: `α ≤ β → C^w_v(α) ⊆ C^w_v(β)`. -/
theorem CCW_mono {α β : Ordinal} (hαβ : α ≤ β) (v : ℕ) :
    CsetW (psiResW α) α v ⊆ CsetW (psiResW β) β v := by
  apply CsetW_mono_param hαβ
  intro ξ u hξ
  rw [psiResW, psiResW, if_pos hξ, if_pos (lt_of_lt_of_le hξ hαβ)]

/-- `Ω_v ≤ ψ^w_v(α)` (from C1). -/
theorem Om_le_psiW (α : Ordinal) (v : ℕ) : Om v ≤ psiW α v := by
  by_contra h
  push Not at h
  exact psiW_notMem α v (Iio_Om_subset_CsetW h)

/-- Every ordinal below `ψ^w_v(α)` lies in `C^w_v(α)` (sInf-minimality). -/
theorem below_psiW_mem_CsetW {α δ : Ordinal} {v : ℕ} (hδ : δ < psiW α v) :
    δ ∈ CsetW (psiResW α) α v := by
  by_contra nin
  have : psiW α v ≤ δ := by
    rw [psiW_unfold]
    exact csInf_le' nin
  exact absurd hδ (not_lt.2 this)

/-- **Buchholz 1.2(c) for with-C**: `ψ^w_v(α) < Ω_{v+1}`.  Reuses the omitted
`psi_lt_Om_succ` cardinality bound via `CsetW ⊆ Cset`. -/
theorem psiW_lt_Om_succ (α : Ordinal.{u}) (v : ℕ) : psiW α v < Om (v + 1) := by
  by_contra hge
  push Not at hge
  -- Iio (Ω_{v+1}) ⊆ CsetW ⊆ Cset, contradicting psi_lt_Om_succ's cardinality bound
  have allinW : Set.Iio (Om (v + 1)) ⊆ CsetW (psiResW α) α v :=
    fun δ hδ => below_psiW_mem_CsetW (lt_of_lt_of_le hδ hge)
  have allin : Set.Iio (Om (v + 1)) ⊆ Cset (psiResW α) α v :=
    allinW.trans (CsetW_subset_Cset (psiResW α) α v)
  -- mimic psi_lt_Om_succ's contradiction directly
  have hcard : Cardinal.lift.{u + 1, u} (ℵ_ (v + 1 : ℕ)) ≤ OmKappa.{u} v := by
    calc Cardinal.lift.{u + 1, u} (ℵ_ (v + 1 : ℕ))
        = Cardinal.lift.{u + 1, u} (Om (v + 1)).card := by
          rw [Om_of_pos (by omega), Cardinal.card_ord]
      _ = #(Set.Iio (Om (v + 1))) := (Cardinal.mk_Iio_ordinal _).symm
      _ ≤ #(Cset (psiResW α) α v) := Cardinal.mk_le_mk_of_subset allin
      _ ≤ OmKappa v := mk_Cset_le _ _ _
  exact absurd hcard (not_le.2 (OmKappa_lt_aleph_succ v))

/-- **Buchholz 1.2(d) for with-C**: weak monotonicity `α ≤ β → ψ^w_v(α) ≤ ψ^w_v(β)`. -/
theorem psiW_mono_arg {α β : Ordinal.{u}} (hαβ : α ≤ β) (v : ℕ) :
    psiW α v ≤ psiW β v := by
  by_contra h
  push Not at h
  have hmem : psiW β v ∈ CsetW (psiResW α) α v := by
    by_contra nin
    have hle : psiW α v ≤ psiW β v := by
      rw [psiW_unfold]
      exact csInf_le' nin
    exact absurd hle (not_le.2 h)
  exact psiW_notMem β v (CCW_mono hαβ v hmem)

/-- `psiResW` agrees with itself across different bounds on arguments below the
smaller bound: lifts the self-canonicity set `Cset (psiResW ξ) ξ a` to
`Cset (psiResW β) ξ a` for `ξ ≤ β`. -/
theorem CsetW_self_canon_lift {ξ β : Ordinal} {a : ℕ} (hξβ : ξ ≤ β)
    (hcan : ξ ∈ Cset (psiResW ξ) ξ a) : ξ ∈ Cset (psiResW β) ξ a := by
  refine Cset_mono_param (le_refl ξ) (fun ζ uu hζ => ?_) hcan
  rw [psiResW, psiResW, if_pos (lt_of_lt_of_le hζ hξβ), if_pos hζ]

/-- **Buchholz 1.3 for with-C (strict monotonicity)**: `α < β`, `α` canonical in
`C^w_v(α)` and omitted-self-canonical (`α ∈ Cset (psiResW α) α v`, exactly what
the with-C generator records) ⟹ `ψ^w_v(α) < ψ^w_v(β)`. -/
theorem psiW_strict_mono_arg {α β : Ordinal} (hαβ : α < β)
    {v : ℕ} (hα : α ∈ CsetW (psiResW α) α v) (hαcanon : α ∈ Cset (psiResW α) α v) :
    psiW α v < psiW β v := by
  have le : α ≤ β := hαβ.le
  have aβ : α ∈ CsetW (psiResW β) β v := CCW_mono le v hα
  have hmem : psiW α v ∈ CsetW (psiResW β) β v := by
    have := CsetW_psi_closed aβ hαβ v (CsetW_self_canon_lift le hαcanon)
    rwa [psiResW, if_pos hαβ] at this
  have hne : psiW α v ≠ psiW β v := fun he => psiW_notMem β v (he ▸ hmem)
  exact lt_of_le_of_ne (psiW_mono_arg le v) hne

/-- **Buchholz 1.4(a) for with-C (canonical-rep uniqueness / injectivity)**: two
`a`-canonical arguments with equal `ψ^w_a`-value are equal.  Canonicity here is
the omitted-C self-canonicity `ξ ∈ Cset (psiResW ξ) ξ a`, exactly what the
with-C generator clause records. -/
theorem psiW_canonical_inj {a : ℕ} {ξ ξ' : Ordinal.{u}}
    (hξ : ξ ∈ CsetW (psiResW ξ) ξ a) (hξcan : ξ ∈ Cset (psiResW ξ) ξ a)
    (hξ' : ξ' ∈ CsetW (psiResW ξ') ξ' a) (hξ'can : ξ' ∈ Cset (psiResW ξ') ξ' a)
    (he : psiW ξ a = psiW ξ' a) : ξ = ξ' := by
  rcases lt_trichotomy ξ ξ' with h | h | h
  · exact absurd he (ne_of_lt (psiW_strict_mono_arg h hξ hξcan))
  · exact h
  · exact absurd he.symm (ne_of_lt (psiW_strict_mono_arg h hξ' hξ'can))

/-- **Buchholz Lemma 1.4(b) for with-C is FREE (the payoff of the switch).**
Any additive-principal `γ ∈ C^w_v(α)` with `Ω_v ≤ γ` is `p ξ u'` for an argument
`ξ` that is `< α`, in `C^w_v(α)`, AND canonical (`ξ ∈ Cset p ξ u'`).  The
canonicity is read straight off the with-C generator clause — no omitted=with
Remark, no bootstrap.  This is exactly the canonical-witness hypothesis that the
omitted-C necessity proof had to *assume* (`CW`/`argExtract_of_canonWitness`). -/
theorem CsetW_witness_canonical {α γ : Ordinal.{u}} {v : ℕ}
    {p : Ordinal.{u} → ℕ → Ordinal.{u}}
    (hap : Ordinal.IsPrincipal (· + ·) γ) (hlo : Om v ≤ γ)
    (hmem : γ ∈ CsetW p α v) :
    ∃ (u' : ℕ) (ξ : Ordinal.{u}),
      γ = p ξ u' ∧ ξ < α ∧ ξ ∈ CsetW p α v ∧ ξ ∈ Cset p ξ u' := by
  obtain ⟨n, hn⟩ := CsetW_mem_iff.1 hmem
  clear hmem
  induction n generalizing γ with
  | zero =>
    simp only [CiterW, Function.iterate_zero, id_eq] at hn
    exact absurd hn (not_lt.2 hlo)
  | succ n IH =>
    rw [CiterW_succ] at hn
    rcases hn with (h1 | h2) | h3
    · exact IH hap hlo h1
    · obtain ⟨x, hx, y, hy, hxy⟩ := h2
      have hxmem : γ ∈ CiterW p α v n := by
        rcases eq_or_lt_of_le (show x ≤ γ from hxy ▸ le_self_add) with hxe | hxlt
        · exact hxe ▸ hx
        · rcases eq_or_lt_of_le (show y ≤ γ from hxy ▸ le_add_self) with hye | hylt
          · exact hye ▸ hy
          · exact absurd hxy.symm (ne_of_gt (hap hxlt hylt))
      exact IH hap hlo hxmem
    · obtain ⟨u, ⟨ξ, ⟨⟨⟨hξC, hξα⟩, hξcanon⟩, hξγ⟩⟩⟩ := Set.mem_iUnion.1 h3
      exact ⟨u, ξ, hξγ.symm, hξα, CiterW_subset_CsetW hξC, hξcanon⟩

/-- **1.3 (strict mono) for `ψ^w`, given the with-C membership of the smaller
canonical argument at the larger bound.**  The omitted `psi_strict_mono_arg`
obtained `α ∈ Cset (psiResW β) β v` for free via `CC_mono` (the omitted set needs
no canonicity); the with-C set requires *membership*, so it is taken here as the
explicit hypothesis `aβ : α ∈ CsetW (psiResW β) β v`.  Everything else is the
omitted proof transcribed. -/
theorem psiW_strict_mono_arg_of_mem {α β : Ordinal} (hαβ : α < β)
    {v : ℕ} (aβ : α ∈ CsetW (psiResW β) β v) (hαcanon : α ∈ Cset (psiResW α) α v) :
    psiW α v < psiW β v := by
  have le : α ≤ β := hαβ.le
  have hmem : psiW α v ∈ CsetW (psiResW β) β v := by
    have := CsetW_psi_closed aβ hαβ v (CsetW_self_canon_lift le hαcanon)
    rwa [psiResW, if_pos hαβ] at this
  have hne : psiW α v ≠ psiW β v := fun he => psiW_notMem β v (he ▸ hmem)
  exact lt_of_le_of_ne (psiW_mono_arg le v) hne

/-! ### `ψ^w` additive-principality and arg-extraction (necessity payoff) -/

/-- **Lemma 1.2(b) for with-C**: `ψ^w_v(α)` is additive-principal.  Same proof
shape as the omitted `psi_add_principal`, with `below_psiW_mem_CsetW` /
`CsetW_add_closed` / `psiW_notMem`. -/
theorem psiW_add_principal {α β γ : Ordinal} {v : ℕ}
    (hβ : β < psiW α v) (hγ : γ < psiW α v) : β + γ < psiW α v := by
  have betaC : β ∈ CsetW (psiResW α) α v := below_psiW_mem_CsetW hβ
  have main : ∀ γ, γ < psiW α v → β + γ < psiW α v := by
    intro γ
    induction γ using WellFoundedLT.induction with
    | _ γ IH =>
      intro hγ
      rcases Ordinal.zero_or_succ_or_isSuccLimit γ with rfl | ⟨η, hη⟩ | hl
      · simpa using hβ
      · obtain ⟨η, rfl⟩ : ∃ η', γ = η' + 1 := ⟨η, by rw [← hη, Order.succ_eq_add_one]⟩
        have ηγ : η < η + 1 := lt_add_one η
        have ed : η < psiW α v := lt_trans ηγ hγ
        have bh : β + η < psiW α v := IH η ηγ ed
        have bhC : β + η ∈ CsetW (psiResW α) α v := below_psiW_mem_CsetW bh
        have d1 : (1 : Ordinal) < psiW α v := lt_of_le_of_lt (le_add_self) hγ
        have oneC : (1 : Ordinal) ∈ CsetW (psiResW α) α v := below_psiW_mem_CsetW d1
        have bg : β + (η + 1) = (β + η) + 1 := by rw [add_assoc]
        have inC : β + (η + 1) ∈ CsetW (psiResW α) α v := by
          rw [bg]; exact CsetW_add_closed bhC oneC
        have le : β + (η + 1) ≤ psiW α v := by
          rw [bg, Order.add_one_le_iff]; exact bh
        exact lt_of_le_of_ne le fun he => psiW_notMem α v (he ▸ inC)
      · have le : β + γ ≤ psiW α v := by
          rw [Ordinal.add_le_iff_of_isSuccLimit hl]
          intro z hz
          exact (IH z hz (lt_trans hz hγ)).le
        have gC : γ ∈ CsetW (psiResW α) α v := below_psiW_mem_CsetW hγ
        have inC : β + γ ∈ CsetW (psiResW α) α v := CsetW_add_closed betaC gC
        exact lt_of_le_of_ne le fun he => psiW_notMem α v (he ▸ inC)
  exact main γ hγ

theorem psiW_addprinc (α : Ordinal) (v : ℕ) : addprinc (psiW α v) := by
  refine ⟨lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (one_le_Om v)) (Om_le_psiW α v), ?_⟩
  exact fun β γ hβ hγ => psiW_add_principal hβ hγ

/-- **Arg-extraction for `ψ^w` from `ψ^w`-injectivity-on-canonical (`INJ`).**
The 1.4(b) canonical-witness lemma is now FREE (`CsetW_witness_canonical`), so the
band logic that pins the witness `ξ` to `β` is *unconditional*; the only residual
is that equal `ψ^w_a`-values of two `a`-canonical arguments force equality
(`INJ` = with-C Buchholz 1.4(a)).  `INJ` itself reduces to `ψ^w` strict
monotonicity (`psiW_strict_mono_arg_of_mem`) modulo the one residual membership
`smaller-canonical ∈ C^w` at the larger bound — the with-C residue of the
omitted=with equivalence, surfacing in 1.3/1.4(a) rather than 1.4(b).

This theorem records that **once `INJ` holds, the necessity arg-extraction closes
unconditionally** — the 1.4(b)-free payoff is genuine; the gap moved to 1.4(a). -/
theorem argExtract_W
    (INJ : ∀ (a : ℕ) (ξ ξ' : Ordinal.{u}),
      ξ ∈ Cset (psiResW ξ) ξ a → ξ' ∈ Cset (psiResW ξ') ξ' a →
      psiW ξ a = psiW ξ' a → ξ = ξ')
    {v a : ℕ} {β α : Ordinal.{u}} (hva : v ≤ a)
    (hβc : β ∈ Cset (psiResW β) β a)
    (hmem : psiW β a ∈ CsetW (psiResW α) α v) :
    β ∈ CsetW (psiResW α) α v := by
  have hlo : Om v ≤ psiW β a := le_trans (Om_mono hva) (Om_le_psiW β a)
  have hpr : Ordinal.IsPrincipal (· + ·) (psiW β a) :=
    fun {x y} hx hy => (psiW_addprinc β a).2 x y hx hy
  obtain ⟨u', ξ, heq, hξα, hξvW, hξc⟩ := CsetW_witness_canonical hpr hlo hmem
  rw [psiResW, if_pos hξα] at heq
  have hua : u' = a := by
    have h1 : Om u' ≤ psiW β a := heq ▸ Om_le_psiW ξ u'
    have h2 : psiW β a < Om (u' + 1) := heq ▸ psiW_lt_Om_succ ξ u'
    have hua1 : u' ≤ a := by
      by_contra hc
      exact absurd (lt_of_le_of_lt h1 (psiW_lt_Om_succ β a)) (not_lt.2 (Om_mono (by omega)))
    have hua2 : a ≤ u' := by
      by_contra hc
      exact absurd (lt_of_le_of_lt (Om_le_psiW β a) h2) (not_lt.2 (Om_mono (by omega)))
    omega
  rw [hua] at heq hξc
  have hξc_self : ξ ∈ Cset (psiResW ξ) ξ a :=
    Cset_mono_param (le_refl ξ)
      (fun ζ uu hζ => by rw [psiResW, psiResW, if_pos hζ, if_pos (lt_trans hζ hξα)]) hξc
  have hξβ : ξ = β := INJ a ξ β hξc_self hβc heq.symm
  rwa [← hξβ]

/-! ## Self-referential with-condition C-set `C^s_v(α)` (Buchholz's faithful form)

The `ψ^w`/`CsetW` above test canonicity with the *omitted* set (`ξ ∈ Cset p ξ u`),
which leaves an omitted=with residue surfacing in 1.3/1.4(a).  Buchholz's actual
condition is `ξ ∈ C_u(ξ)` referring to the SAME `C` under definition.  Modelled
here as `ξ ∈ CsetSelf p ξ u`: the canonicity test consults `CsetSelf` at the
strictly smaller bound `ξ < α`, so `CsetSelf` is definable by well-founded
recursion on the bound.  Crucially the test is **bound-independent**, which makes
the bound/parameter monotonicities (`CsetSelf_mono_bound`/`_param`/`CCSelf_mono`)
free — dissolving the residue (1.3/1.4(a) need no extra membership hypothesis). -/

/-- Self-referential with-C closure step at bound `α`, given the closure function
`Csub` at all strictly smaller bounds. -/
def CstepSelf (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u})
    (Csub : ∀ ξ, ξ < α → ℕ → Set Ordinal.{u}) (X : Set Ordinal.{u}) : Set Ordinal.{u} :=
  X ∪ Set.image2 (· + ·) X X ∪
    ⋃ u : ℕ, (fun ξ => p ξ u) '' (X ∩ {ξ | ∃ h : ξ < α, ξ ∈ Csub ξ h u})

/-- The full self-referential with-C set at bound `α`, by WF recursion on `α`. -/
noncomputable def CsetSelf (p : Ordinal.{u} → ℕ → Ordinal.{u}) :
    Ordinal.{u} → ℕ → Set Ordinal.{u} :=
  Ordinal.lt_wf.fix fun α IH v =>
    ⋃ n : ℕ, (CstepSelf p α IH)^[n] (Set.Iio (Om v))

theorem CsetSelf_unfold (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) :
    CsetSelf p α v =
      ⋃ n : ℕ, (CstepSelf p α (fun ξ _ => CsetSelf p ξ))^[n] (Set.Iio (Om v)) := by
  rw [CsetSelf, WellFounded.fix_eq]

/-- one closure step at bound `α` with the canonicalisation function plugged in. -/
abbrev CstepSelf' (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) :
    Set Ordinal.{u} → Set Ordinal.{u} :=
  CstepSelf p α (fun ξ _ => CsetSelf p ξ)

theorem CsetSelf_eq (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) :
    CsetSelf p α v = ⋃ n : ℕ, (CstepSelf' p α)^[n] (Set.Iio (Om v)) :=
  CsetSelf_unfold p α v

theorem CsetSelf_mem_iff {p : Ordinal → ℕ → Ordinal} {α x : Ordinal} {v : ℕ} :
    x ∈ CsetSelf p α v ↔ ∃ n, x ∈ (CstepSelf' p α)^[n] (Set.Iio (Om v)) := by
  rw [CsetSelf_eq]; exact Set.mem_iUnion

theorem CiterSelf_subset_CsetSelf {p : Ordinal.{u} → ℕ → Ordinal.{u}} {α : Ordinal.{u}}
    {v n : ℕ} : (CstepSelf' p α)^[n] (Set.Iio (Om v)) ⊆ CsetSelf p α v := by
  rw [CsetSelf_eq]; exact Set.subset_iUnion (fun n => (CstepSelf' p α)^[n] (Set.Iio (Om v))) n

/-! ### bound/parameter monotonicity (the residue-dissolving lemmas) -/

/-- **Bound-monotone**: the self-canonicity test `ζ ∈ CsetSelf p ζ u` is
independent of the outer bound, so enlarging the bound only relaxes `ζ < β`. -/
theorem CstepSelf'_mono_bound (p : Ordinal.{u} → ℕ → Ordinal.{u}) {α β : Ordinal.{u}}
    (hαβ : α ≤ β) {X Y : Set Ordinal.{u}} (hXY : X ⊆ Y) :
    CstepSelf' p α X ⊆ CstepSelf' p β Y := by
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact Set.mem_union_left _ (Set.mem_union_left _ (hXY hx))
  · obtain ⟨ξ, hξ, η, hη, rfl⟩ := Set.mem_image2.1 hx
    exact Set.mem_union_left _
      (Set.mem_union_right _ (Set.mem_image2_of_mem (hXY hξ) (hXY hη)))
  · obtain ⟨u, hu⟩ := Set.mem_iUnion.1 hx
    obtain ⟨ζ, ⟨hζX, ⟨hζα, hζcanon⟩⟩, rfl⟩ := hu
    refine Set.mem_union_right _ (Set.mem_iUnion.2 ⟨u, Set.mem_image_of_mem _
      ⟨hXY hζX, ⟨lt_of_lt_of_le hζα hαβ, hζcanon⟩⟩⟩)

theorem CiterSelf_mono_bound (p : Ordinal.{u} → ℕ → Ordinal.{u}) {α β : Ordinal.{u}}
    (hαβ : α ≤ β) (v n : ℕ) :
    (CstepSelf' p α)^[n] (Set.Iio (Om v)) ⊆ (CstepSelf' p β)^[n] (Set.Iio (Om v)) := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact CstepSelf'_mono_bound p hαβ ih

theorem CsetSelf_mono_bound (p : Ordinal.{u} → ℕ → Ordinal.{u}) {α β : Ordinal.{u}}
    (hαβ : α ≤ β) (v : ℕ) : CsetSelf p α v ⊆ CsetSelf p β v := by
  rw [CsetSelf_eq, CsetSelf_eq]
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨n, CiterSelf_mono_bound p hαβ v n hn⟩

/-- **Parameter-monotone at a fixed bound** (strong induction on the bound; the
self-canonicity test at bound `ζ < α` is lifted by the IH). -/
theorem CsetSelf_mono_param (p q : Ordinal.{u} → ℕ → Ordinal.{u}) :
    ∀ (α : Ordinal.{u}) (v : ℕ), (∀ ξ u, ξ < α → p ξ u = q ξ u) →
      CsetSelf p α v ⊆ CsetSelf q α v := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IHα =>
    intro v hpq
    rw [CsetSelf_eq, CsetSelf_eq]
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    clear hx
    induction n generalizing x with
    | zero => simpa using hn
    | succ n ih =>
      rw [Function.iterate_succ_apply'] at hn ⊢
      rcases hn with (h | h) | h
      · exact Set.mem_union_left _ (Set.mem_union_left _ (ih h))
      · obtain ⟨ξ, hξ, η, hη, rfl⟩ := Set.mem_image2.1 h
        exact Set.mem_union_left _ (Set.mem_union_right _
          (Set.mem_image2_of_mem (ih hξ) (ih hη)))
      · obtain ⟨u, hu⟩ := Set.mem_iUnion.1 h
        obtain ⟨ζ, ⟨hζX, ⟨hζα, hζcanon⟩⟩, rfl⟩ := hu
        show (fun ξ => p ξ u) ζ ∈ _
        simp only
        rw [hpq ζ u hζα]
        refine Set.mem_union_right _ (Set.mem_iUnion.2 ⟨u, Set.mem_image_of_mem _
          ⟨ih hζX, ⟨hζα, ?_⟩⟩⟩)
        exact IHα ζ hζα u (fun ρ uu hρ => hpq ρ uu (lt_trans hρ hζα)) hζcanon

/-! ### well-definedness of `ψ^s` -/

theorem CiterSelf_subset_Citer (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u})
    (v : ℕ) : ∀ n, (CstepSelf' p α)^[n] (Set.Iio (Om v)) ⊆ Citer p α v n := by
  intro n
  induction n with
  | zero => simp [Citer]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Citer_succ]
    intro x hn
    rcases hn with (h | h) | h
    · exact Set.mem_union_left _ (Set.mem_union_left _ (ih h))
    · obtain ⟨ξ, hξ, η, hη, rfl⟩ := Set.mem_image2.1 h
      exact Set.mem_union_left _ (Set.mem_union_right _
        (Set.mem_image2_of_mem (ih hξ) (ih hη)))
    · obtain ⟨u, hu⟩ := Set.mem_iUnion.1 h
      obtain ⟨ζ, ⟨hζX, ⟨hζα, _⟩⟩, rfl⟩ := hu
      exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨u,
        Set.mem_image_of_mem _ ⟨ih hζX, hζα⟩⟩)

/-- **`CsetSelf ⊆ Cset`**: self with-C fires a subset of omitted generators. -/
theorem CsetSelf_subset_Cset (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) :
    CsetSelf p α v ⊆ Cset p α v := by
  rw [CsetSelf_eq]
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  exact Citer_subset_Cset (CiterSelf_subset_Citer p α v n hn)

theorem small_CsetSelf (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) :
    Small.{u} (CsetSelf p α v) :=
  have : Small.{u} (Cset p α v) := small_Cset p α v
  small_subset (CsetSelf_subset_Cset p α v)

theorem exists_notMem_CsetSelf (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) :
    ∃ γ, γ ∉ CsetSelf p α v := by
  have hbdd : BddAbove (CsetSelf p α v) := Ordinal.bddAbove_iff_small.2 (small_CsetSelf p α v)
  refine ⟨sSup (CsetSelf p α v) + 1, fun h => ?_⟩
  have := le_csSup hbdd h
  rw [Order.add_one_le_iff] at this
  exact lt_irrefl _ this

/-- Self-referential with-C collapsing function `ψ^s_v(α)`. -/
noncomputable def psiSelf : Ordinal.{u} → ℕ → Ordinal.{u} :=
  Ordinal.lt_wf.fix (C := fun _ => ℕ → Ordinal.{u}) fun α IH v =>
    sInf {γ | γ ∉ CsetSelf (fun ξ u => if h : ξ < α then IH ξ h u else 0) α v}

noncomputable def psiResSelf (α : Ordinal.{u}) : Ordinal.{u} → ℕ → Ordinal.{u} :=
  fun ξ u => if ξ < α then psiSelf ξ u else 0

theorem psiSelf_unfold (α : Ordinal.{u}) (v : ℕ) :
    psiSelf α v = sInf {γ | γ ∉ CsetSelf (psiResSelf α) α v} := by
  unfold psiSelf; rw [WellFounded.fix_eq]; rfl

theorem psiSelf_notMem (α : Ordinal) (v : ℕ) : psiSelf α v ∉ CsetSelf (psiResSelf α) α v := by
  rw [psiSelf_unfold]; exact csInf_mem (exists_notMem_CsetSelf (psiResSelf α) α v)

/-- **`CCSelf_mono` = bound-lift ∘ param-lift, the with-C analogue of `CC_mono`** —
the lemma that dissolves the omitted=with residue. -/
theorem CCSelf_mono {α β : Ordinal} (hαβ : α ≤ β) (v : ℕ) :
    CsetSelf (psiResSelf α) α v ⊆ CsetSelf (psiResSelf β) β v := by
  have hparam : CsetSelf (psiResSelf α) α v ⊆ CsetSelf (psiResSelf β) α v :=
    CsetSelf_mono_param _ _ α v (fun ξ u hξ => by
      rw [psiResSelf, psiResSelf, if_pos hξ, if_pos (lt_of_lt_of_le hξ hαβ)])
  exact hparam.trans (CsetSelf_mono_bound _ hαβ v)

/-! ### §1 port for `ψ^s` (Buchholz 1.2–1.4), residue-free -/

/-- C1: `Iio Ω_v ⊆ C^s_v(α)`. -/
theorem Iio_Om_subset_CsetSelf {p : Ordinal → ℕ → Ordinal} {α : Ordinal} {v : ℕ} :
    Set.Iio (Om v) ⊆ CsetSelf p α v := by
  intro x hx
  exact CiterSelf_subset_CsetSelf (n := 0) (by simpa using hx)

/-- C2: closed under `+`. -/
theorem CsetSelf_add_closed {p : Ordinal → ℕ → Ordinal} {α ξ η : Ordinal} {v : ℕ}
    (hξ : ξ ∈ CsetSelf p α v) (hη : η ∈ CsetSelf p α v) : ξ + η ∈ CsetSelf p α v := by
  obtain ⟨m, hm⟩ := CsetSelf_mem_iff.1 hξ
  obtain ⟨n, hn⟩ := CsetSelf_mem_iff.1 hη
  have mono : ∀ {a b : ℕ}, a ≤ b →
      (CstepSelf' p α)^[a] (Set.Iio (Om v)) ⊆ (CstepSelf' p α)^[b] (Set.Iio (Om v)) := by
    intro a b hab
    induction b with
    | zero => rw [Nat.le_zero.1 hab]
    | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · rw [Function.iterate_succ_apply']
        exact (ih (by omega)).trans
          (fun _ hx => Set.mem_union_left _ (Set.mem_union_left _ hx))
      · rw [Nat.le_antisymm hab h]
  have hm' := mono (le_max_left m n) hm
  have hn' := mono (le_max_right m n) hn
  refine CiterSelf_subset_CsetSelf (n := max m n + 1) ?_
  rw [Function.iterate_succ_apply']
  exact Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_image2_of_mem hm' hn'))

/-- C3: generator closure with self-referential canonicity `ξ ∈ CsetSelf p ξ u`. -/
theorem CsetSelf_psi_closed {p : Ordinal → ℕ → Ordinal} {α ξ : Ordinal} {v : ℕ}
    (hξ : ξ ∈ CsetSelf p α v) (hα : ξ < α) (u : ℕ) (hcanon : ξ ∈ CsetSelf p ξ u) :
    p ξ u ∈ CsetSelf p α v := by
  obtain ⟨n, hn⟩ := CsetSelf_mem_iff.1 hξ
  refine CiterSelf_subset_CsetSelf (n := n + 1) ?_
  rw [Function.iterate_succ_apply']
  exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨u,
    Set.mem_image_of_mem _ ⟨hn, ⟨hα, hcanon⟩⟩⟩)

/-- `Ω_v ≤ ψ^s_v(α)` (from C1). -/
theorem Om_le_psiSelf (α : Ordinal) (v : ℕ) : Om v ≤ psiSelf α v := by
  by_contra h; push Not at h
  exact psiSelf_notMem α v (Iio_Om_subset_CsetSelf h)

/-- Every ordinal below `ψ^s_v(α)` lies in `C^s_v(α)` (sInf-minimality). -/
theorem below_psiSelf_mem_CsetSelf {α δ : Ordinal} {v : ℕ} (hδ : δ < psiSelf α v) :
    δ ∈ CsetSelf (psiResSelf α) α v := by
  by_contra nin
  have : psiSelf α v ≤ δ := by rw [psiSelf_unfold]; exact csInf_le' nin
  exact absurd hδ (not_lt.2 this)

/-- **Buchholz 1.2(c) for `ψ^s`**: `ψ^s_v(α) < Ω_{v+1}` (reuses the omitted
cardinality bound via `CsetSelf ⊆ Cset`). -/
theorem psiSelf_lt_Om_succ (α : Ordinal.{u}) (v : ℕ) : psiSelf α v < Om (v + 1) := by
  by_contra hge
  push Not at hge
  have allin : Set.Iio (Om (v + 1)) ⊆ Cset (psiResSelf α) α v :=
    Set.Subset.trans (fun δ hδ => below_psiSelf_mem_CsetSelf (lt_of_lt_of_le hδ hge))
      (CsetSelf_subset_Cset (psiResSelf α) α v)
  have hcard : Cardinal.lift.{u + 1, u} (ℵ_ (v + 1 : ℕ)) ≤ OmKappa.{u} v := by
    calc Cardinal.lift.{u + 1, u} (ℵ_ (v + 1 : ℕ))
        = Cardinal.lift.{u + 1, u} (Om (v + 1)).card := by
          rw [Om_of_pos (by omega), Cardinal.card_ord]
      _ = #(Set.Iio (Om (v + 1))) := (Cardinal.mk_Iio_ordinal _).symm
      _ ≤ #(Cset (psiResSelf α) α v) := Cardinal.mk_le_mk_of_subset allin
      _ ≤ OmKappa v := mk_Cset_le _ _ _
  exact absurd hcard (not_le.2 (OmKappa_lt_aleph_succ v))

/-- **Buchholz 1.2(d) for `ψ^s`**: `α ≤ β → ψ^s_v(α) ≤ ψ^s_v(β)`. -/
theorem psiSelf_mono_arg {α β : Ordinal.{u}} (hαβ : α ≤ β) (v : ℕ) :
    psiSelf α v ≤ psiSelf β v := by
  by_contra h; push Not at h
  have hmem : psiSelf β v ∈ CsetSelf (psiResSelf α) α v := by
    by_contra nin
    have hle : psiSelf α v ≤ psiSelf β v := by rw [psiSelf_unfold]; exact csInf_le' nin
    exact absurd hle (not_le.2 h)
  exact psiSelf_notMem β v (CCSelf_mono hαβ v hmem)

/-- **Buchholz 1.3 for `ψ^s` (strict mono), residue-free**: self-canonicity is the
ONLY hypothesis; the `aβ` membership is obtained free via `CCSelf_mono`. -/
theorem psiSelf_strict_mono_arg {α β : Ordinal} (hαβ : α < β)
    {v : ℕ} (hα : α ∈ CsetSelf (psiResSelf α) α v) :
    psiSelf α v < psiSelf β v := by
  have le : α ≤ β := hαβ.le
  have aβ : α ∈ CsetSelf (psiResSelf β) β v := CCSelf_mono le v hα
  have hαcanon : α ∈ CsetSelf (psiResSelf β) α v :=
    CsetSelf_mono_param _ _ α v (fun ξ u hξ => by
      rw [psiResSelf, psiResSelf, if_pos hξ, if_pos (lt_of_lt_of_le hξ le)]) hα
  have hmem : psiSelf α v ∈ CsetSelf (psiResSelf β) β v := by
    have := CsetSelf_psi_closed aβ hαβ v hαcanon
    rwa [psiResSelf, if_pos hαβ] at this
  have hne : psiSelf α v ≠ psiSelf β v := fun he => psiSelf_notMem β v (he ▸ hmem)
  exact lt_of_le_of_ne (psiSelf_mono_arg le v) hne

/-- **Buchholz 1.4(a) for `ψ^s` (injectivity), UNCONDITIONAL** — self-canonicity
is the only hypothesis. -/
theorem psiSelf_canonical_inj {a : ℕ} {ξ ξ' : Ordinal.{u}}
    (hξ : ξ ∈ CsetSelf (psiResSelf ξ) ξ a) (hξ' : ξ' ∈ CsetSelf (psiResSelf ξ') ξ' a)
    (he : psiSelf ξ a = psiSelf ξ' a) : ξ = ξ' := by
  rcases lt_trichotomy ξ ξ' with h | h | h
  · exact absurd he (ne_of_lt (psiSelf_strict_mono_arg h hξ))
  · exact h
  · exact absurd he.symm (ne_of_lt (psiSelf_strict_mono_arg h hξ'))

/-- **Buchholz 1.4(b) for `ψ^s` is FREE, witness SELF-canonical** — the with-C
payoff, residue-free: the extracted witness `ξ` is canonical in its OWN with-C
set (`ξ ∈ CsetSelf p ξ u'`), no omitted form involved. -/
theorem CsetSelf_witness_canonical {α γ : Ordinal.{u}} {v : ℕ}
    {p : Ordinal.{u} → ℕ → Ordinal.{u}}
    (hap : Ordinal.IsPrincipal (· + ·) γ) (hlo : Om v ≤ γ)
    (hmem : γ ∈ CsetSelf p α v) :
    ∃ (u' : ℕ) (ξ : Ordinal.{u}),
      γ = p ξ u' ∧ ξ < α ∧ ξ ∈ CsetSelf p α v ∧ ξ ∈ CsetSelf p ξ u' := by
  obtain ⟨n, hn⟩ := CsetSelf_mem_iff.1 hmem
  clear hmem
  induction n generalizing γ with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hn
    exact absurd hn (not_lt.2 hlo)
  | succ n IH =>
    rw [Function.iterate_succ_apply'] at hn
    rcases hn with (h1 | h2) | h3
    · exact IH hap hlo h1
    · obtain ⟨x, hx, y, hy, hxy⟩ := h2
      have hxmem : γ ∈ (CstepSelf' p α)^[n] (Set.Iio (Om v)) := by
        rcases eq_or_lt_of_le (show x ≤ γ from hxy ▸ le_self_add) with hxe | hxlt
        · exact hxe ▸ hx
        · rcases eq_or_lt_of_le (show y ≤ γ from hxy ▸ le_add_self) with hye | hylt
          · exact hye ▸ hy
          · exact absurd hxy.symm (ne_of_gt (hap hxlt hylt))
      exact IH hap hlo hxmem
    · obtain ⟨u, ⟨ξ, ⟨hξX, ⟨hξα, hξcanon⟩⟩, hξγ⟩⟩ := Set.mem_iUnion.1 h3
      exact ⟨u, ξ, hξγ.symm, hξα, CiterSelf_subset_CsetSelf hξX, hξcanon⟩

/-! ### `ψ^s` additive-principality + UNCONDITIONAL arg-extraction (necessity) -/

/-- **Lemma 1.2(b) for `ψ^s`**: `ψ^s_v(α)` is additive-principal. -/
theorem psiSelf_add_principal {α β γ : Ordinal} {v : ℕ}
    (hβ : β < psiSelf α v) (hγ : γ < psiSelf α v) : β + γ < psiSelf α v := by
  have betaC : β ∈ CsetSelf (psiResSelf α) α v := below_psiSelf_mem_CsetSelf hβ
  have main : ∀ γ, γ < psiSelf α v → β + γ < psiSelf α v := by
    intro γ
    induction γ using WellFoundedLT.induction with
    | _ γ IH =>
      intro hγ
      rcases Ordinal.zero_or_succ_or_isSuccLimit γ with rfl | ⟨η, hη⟩ | hl
      · simpa using hβ
      · obtain ⟨η, rfl⟩ : ∃ η', γ = η' + 1 := ⟨η, by rw [← hη, Order.succ_eq_add_one]⟩
        have ηγ : η < η + 1 := lt_add_one η
        have bh : β + η < psiSelf α v := IH η ηγ (lt_trans ηγ hγ)
        have bhC : β + η ∈ CsetSelf (psiResSelf α) α v := below_psiSelf_mem_CsetSelf bh
        have oneC : (1 : Ordinal) ∈ CsetSelf (psiResSelf α) α v :=
          below_psiSelf_mem_CsetSelf (lt_of_le_of_lt le_add_self hγ)
        have bg : β + (η + 1) = (β + η) + 1 := by rw [add_assoc]
        have inC : β + (η + 1) ∈ CsetSelf (psiResSelf α) α v := by
          rw [bg]; exact CsetSelf_add_closed bhC oneC
        have le : β + (η + 1) ≤ psiSelf α v := by rw [bg, Order.add_one_le_iff]; exact bh
        exact lt_of_le_of_ne le fun he => psiSelf_notMem α v (he ▸ inC)
      · have le : β + γ ≤ psiSelf α v := by
          rw [Ordinal.add_le_iff_of_isSuccLimit hl]
          intro z hz
          exact (IH z hz (lt_trans hz hγ)).le
        have gC : γ ∈ CsetSelf (psiResSelf α) α v := below_psiSelf_mem_CsetSelf hγ
        have inC : β + γ ∈ CsetSelf (psiResSelf α) α v := CsetSelf_add_closed betaC gC
        exact lt_of_le_of_ne le fun he => psiSelf_notMem α v (he ▸ inC)
  exact main γ hγ

theorem psiSelf_addprinc (α : Ordinal) (v : ℕ) : addprinc (psiSelf α v) := by
  refine ⟨lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (one_le_Om v)) (Om_le_psiSelf α v), ?_⟩
  exact fun β γ hβ hγ => psiSelf_add_principal hβ hγ

/-- **Arg-extraction for `ψ^s` is UNCONDITIONAL** (no `INJ` hypothesis): the
1.4(b) witness is free and self-canonical (`CsetSelf_witness_canonical`), and the
self-form 1.4(a) injectivity (`psiSelf_canonical_inj`) is itself unconditional, so
the canonical witness `ξ` is pinned to `β` with no residual.  This is the final
confirmation that the with-C switch makes necessity arg-extraction close
unconditionally. -/
theorem argExtract_Self {v a : ℕ} {β α : Ordinal.{u}} (hva : v ≤ a)
    (hβc : β ∈ CsetSelf (psiResSelf β) β a)
    (hmem : psiSelf β a ∈ CsetSelf (psiResSelf α) α v) :
    β ∈ CsetSelf (psiResSelf α) α v := by
  have hlo : Om v ≤ psiSelf β a := le_trans (Om_mono hva) (Om_le_psiSelf β a)
  have hpr : Ordinal.IsPrincipal (· + ·) (psiSelf β a) :=
    fun {x y} hx hy => (psiSelf_addprinc β a).2 x y hx hy
  obtain ⟨u', ξ, heq, hξα, hξv, hξc⟩ := CsetSelf_witness_canonical hpr hlo hmem
  rw [psiResSelf, if_pos hξα] at heq
  have hua : u' = a := by
    have h1 : Om u' ≤ psiSelf β a := heq ▸ Om_le_psiSelf ξ u'
    have h2 : psiSelf β a < Om (u' + 1) := heq ▸ psiSelf_lt_Om_succ ξ u'
    have hua1 : u' ≤ a := by
      by_contra hc
      exact absurd (lt_of_le_of_lt h1 (psiSelf_lt_Om_succ β a)) (not_lt.2 (Om_mono (by omega)))
    have hua2 : a ≤ u' := by
      by_contra hc
      exact absurd (lt_of_le_of_lt (Om_le_psiSelf β a) h2) (not_lt.2 (Om_mono (by omega)))
    omega
  rw [hua] at heq hξc
  -- ξ self-canonical at bound ξ: lift the witness canonicity (bound ξ, param
  -- psiResSelf α) to param psiResSelf ξ (args < ξ < α agree).
  have hξc_self : ξ ∈ CsetSelf (psiResSelf ξ) ξ a :=
    CsetSelf_mono_param _ _ ξ a
      (fun ζ uu hζ => by rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hξα)]) hξc
  have hξβ : ξ = β := psiSelf_canonical_inj hξc_self hβc heq.symm
  rwa [← hξβ]

end YAPSS
