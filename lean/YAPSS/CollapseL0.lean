/-
# `L₀` accessibility — the `cr_inv = 0` distinguished-set base (door1, M2)

The base of the Towsner distinguished-set ladder (`architect-wf.md` §13–14, M2):
every term in the lowest collapse-stratum `cr_inv t = 0` (the predicative /
ascending forms, `ε₀`/PrSS level) is `olt`-accessible.

`cr_inv t = 0` means at every node `P a b c` the argument never rises above the
head (`maxsub b ≤ a`); equivalently no `ψ₀`-collapse occurs.  This generalises
the `lvl0` (`maxsub = 0`) base of `wf_olt0`: there the head subscript is forced
to `0`; here it can be any `a` provided no argument exceeds it.

The accessibility proof follows the `wf_olt0` Dershowitz–Manna template
(`olt_summands_mult` → `acc_dmlt_of_acc` → sums accessible once summand
multisets are).  The master induction is **lexicographic on `(maxsub t,
tsize t)`**: a predecessor of a single principal `P a b Z` (which has
`maxsub = a` here) is a sum of principals `P a' d Z` with either `a' < a`
(strictly smaller `maxsub` ⇒ outer IH) or `a' = a` with `d <o b` (same `maxsub`,
strictly smaller `tsize` argument ⇒ inner IH).  This is the `L₀` distinguished
set being accessible (`wf_olt0` is the `maxsub = 0` special case).
-/
import YAPSS.CollapseRank
import YAPSS.Wfsum

namespace YAPSS

open Three

/-! ## The `asc` distinguished set (`cr_inv = 0`, in CNF) -/

/-- The `L₀` distinguished set: CNF terms in the lowest collapse-stratum. -/
def asc (t : Three) : Prop := cnf t ∧ cr_inv t = 0

/-- The order restricted to `L₀`. -/
def oltAsc (c f : Three) : Prop := c <o f ∧ asc c ∧ asc f

theorem transp_oltAsc : ∀ ⦃a b c⦄, oltAsc a b → oltAsc b c → oltAsc a c :=
  fun _ _ _ h1 h2 => ⟨olt_trans h1.1 h2.1, h1.2.1, h2.2.2⟩

/-! ## Structural closure of `cr_inv = 0` -/

theorem cr_inv_eq_zero_arg {a : ℕ} {b c : Three} (h : cr_inv (P a b c) = 0) :
    cr_inv b = 0 := by
  have := cr_inv_arg_le a b c; omega

theorem cr_inv_eq_zero_sib {a : ℕ} {b c : Three} (h : cr_inv (P a b c) = 0) :
    cr_inv c = 0 := by
  have := cr_inv_sib_le a b c; omega

/-- At an `asc` node the argument never rises above the head. -/
theorem maxsub_arg_le_head {a : ℕ} {b c : Three} (h : cr_inv (P a b c) = 0) :
    maxsub b ≤ a := by
  by_contra hlt
  have hlt' : a < maxsub b := by omega
  have : cr_inv b < cr_inv (P a b c) := cr_inv_arg_lt_of_inv hlt'
  omega

/-- For a single `asc` principal `P a b Z`, the maximal subscript is the head. -/
theorem maxsub_asc_principal {a : ℕ} {b : Three} (h : cr_inv (P a b Z) = 0) :
    maxsub (P a b Z) = a := by
  have hle : maxsub b ≤ a := maxsub_arg_le_head h
  simp only [maxsub_P, maxsub_Z]
  omega

/-- `cr_inv = 0` is hereditary along the summands. -/
theorem cr_inv_summands {x : Three} (hx : cr_inv x = 0) :
    ∀ s ∈ summands x, cr_inv s = 0 := by
  induction x with
  | Z => intro s hs; simp at hs
  | P a b c ihb ihc =>
    intro s hs
    rw [summands_P] at hs
    have hc : cr_inv c = 0 := cr_inv_eq_zero_sib hx
    rcases List.mem_cons.1 hs with rfl | hs
    · have hb : cr_inv b = 0 := cr_inv_eq_zero_arg hx
      have hle : maxsub b ≤ a := maxsub_arg_le_head hx
      simp only [cr_inv_P, cr_inv_Z]
      rw [if_neg (by omega), hb]; omega
    · exact ihc hc s hs

/-- `asc` is hereditary along the summands. -/
theorem asc_summands {u : Three} (hu : asc u) :
    ∀ s ∈ summands u, asc s :=
  fun s hs => ⟨cnf_summands hu.1 hs, cr_inv_summands hu.2 s hs⟩

/-! ## The Dershowitz–Manna step on `L₀` -/

theorem oltAsc_summands_dmlt {w t : Three} (h : oltAsc w t) :
    DMLT oltAsc ↑(summands w) ↑(summands t) := by
  obtain ⟨wt, lw, lt'⟩ := h
  have base : DMLT (oltOn {s | asc s}) ↑(summands w) ↑(summands t) :=
    olt_summands_mult lw.1 wt (asc_summands lw) (asc_summands lt')
  exact base.mono fun a b ⟨hab, ha, hb⟩ => ⟨hab, ha, hb⟩

theorem Z_accAsc : Acc oltAsc Z :=
  Acc.intro Z fun y hy => absurd hy.1 (not_olt_Z y)

/-- A sum is accessible once its summand multiset is. -/
theorem sum_accAsc {v : Three} (lv : asc v)
    (hacc : Acc (DMLT oltAsc) (↑(summands v) : Multiset Three)) :
    Acc oltAsc v := by
  have aux : ∀ M : Multiset Three, Acc (DMLT oltAsc) M →
      ∀ w, asc w → ↑(summands w) = M → Acc oltAsc w := by
    intro M hM
    induction hM with
    | intro M _ ih =>
      intro w lw hw
      refine Acc.intro w fun v hv => ?_
      have lv' : asc v := hv.2.1
      have step : DMLT oltAsc ↑(summands v) M := hw ▸ oltAsc_summands_dmlt hv
      exact ih _ step v lv' rfl
  exact aux _ hacc v lv rfl

/-! ## The master accessibility — strong induction on the head subscript

`asc t` accessibility is proved by **strong induction on `maxsub t`** (the
collapse-free top subscript), with an inner **strong induction on `tsize`**
that handles the same-`maxsub` arguments.  We package the two layers as a
single statement parameterised by a subscript bound `m`:

  `accUpTo m`: every `asc` term `t` with `maxsub t ≤ m` is accessible.

The base `m = 0` is exactly `wf_olt0`'s class (`lvl0`).  The step `m+1` uses
`accUpTo m` for any strictly-lower-subscript predecessor and a `tsize`
induction for same-subscript arguments. -/

/-- Every summand `s` of a strict `olt`-predecessor `v` of a single principal
`P a b Z` is itself strictly below `P a b Z`.  (Sums are non-increasing, so each
summand is `≤o` the head principal of `v`, which is `≤o v <o P a b Z`.) -/
theorem summand_lt_of_pred {v : Three} (cv : cnf v) (vlt : v <o P a b Z)
    {s : Three} (hs : s ∈ summands v) : s <o P a b Z := by
  cases v with
  | Z => simp at hs
  | P e f g =>
    have hle : s ≤o P e f Z := by
      rw [summands_P] at hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact Or.inr rfl
      · exact summands_le_hd cv hs
    have hhd : P e f Z <o P a b Z := by
      rcases olt_P_P.1 vlt with h | ⟨he', h⟩ | ⟨he', _, h⟩
      · exact olt_P_P.2 (Or.inl h)
      · exact olt_P_P.2 (Or.inr (Or.inl ⟨he', h⟩))
      · exact absurd h (not_olt_Z _)
    exact ole_olt_trans hle hhd

/-- Singleton accessibility at subscript `a`, given every `asc` term of
strictly smaller subscript is accessible (`hlow`).  Inner induction: the
accessibility induction on the argument `b`. -/
theorem sing_accAsc {a : ℕ}
    (hlow : ∀ u : Three, asc u → maxsub u < a → Acc oltAsc u)
    {b : Three} (hb : Acc oltAsc b) (lb : asc (P a b Z)) :
    Acc oltAsc (P a b Z) := by
  induction hb with
  | intro b _ ih =>
    refine Acc.intro _ fun v hv => ?_
    obtain ⟨vlt, lv, _⟩ := hv
    have summacc : ∀ s ∈ (↑(summands v) : Multiset Three), Acc oltAsc s := by
      intro s hs
      have sv : s ∈ summands v := by simpa using hs
      obtain ⟨a', d', he, hd'⟩ := summands_sargs sv
      have ls : asc s := asc_summands lv s sv
      have lsP : asc (P a' d' Z) := he ▸ ls
      have ld' : asc d' := ⟨cnf_P_Z.1 lsP.1, cr_inv_eq_zero_arg lsP.2⟩
      have slt : s <o P a b Z := summand_lt_of_pred lv.1 vlt sv
      have hsP : P a' d' Z <o P a b Z := he ▸ slt
      rw [he]
      rcases olt_P_P.1 hsP with hlt | ⟨heq, hdb⟩ | ⟨heq, _, hz⟩
      · -- a' < a: strictly smaller subscript ⇒ outer hypothesis `hlow`
        refine hlow (P a' d' Z) lsP ?_
        rw [maxsub_asc_principal lsP.2]; exact hlt
      · -- a' = a, d' <o b: same subscript, inner accessibility IH on b
        subst heq
        have lbArg : asc b := ⟨cnf_P_Z.1 lb.1, cr_inv_eq_zero_arg lb.2⟩
        exact ih d' ⟨hdb, ld', lbArg⟩ lsP
      · exact absurd hz (not_olt_Z _)
    exact sum_accAsc lv (acc_dmlt_of_acc transp_oltAsc summacc)

/-- **L₀ accessibility, subscript-bounded form**: every `asc` term whose maximal
subscript is `≤ m` is accessible.  Outer strong induction on `m`; inner the
`tsize` strong induction for the sum decomposition. -/
theorem accUpTo : ∀ (m : ℕ) (t : Three), asc t → maxsub t ≤ m → Acc oltAsc t := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    -- inner: strong induction on tsize for the sum decomposition
    intro t
    induction t using (measure tsize).wf.induction with
    | _ t iht =>
      intro lt' hmle
      cases t with
      | Z => exact Z_accAsc
      | P a b c =>
        refine sum_accAsc lt' (acc_dmlt_of_acc transp_oltAsc ?_)
        intro s hs
        have sv : s ∈ summands (P a b c) := by simpa using hs
        obtain ⟨a', d', he, hd'⟩ := summands_sargs sv
        have ls : asc s := asc_summands lt' s sv
        have lsP : asc (P a' d' Z) := he ▸ ls
        have ld' : asc d' := ⟨cnf_P_Z.1 lsP.1, cr_inv_eq_zero_arg lsP.2⟩
        have hmsS : maxsub (P a' d' Z) = a' := maxsub_asc_principal lsP.2
        have ha'le : a' ≤ m := by
          have := maxsub_summands_le sv
          rw [he, hmsS] at this; omega
        have hszd : tsize d' < tsize (P a b c) := sargs_tsize hd'
        -- accessibility of the argument d'
        have haccd : Acc oltAsc d' :=
          iht d' hszd ld' (by have := maxsub_arg_le_head lsP.2; omega)
        rw [he]
        -- singleton step: every strictly-smaller subscript principal accessible.
        -- such `u` has `maxsub u < a' ≤ m`, so `maxsub u < m`: outer IH `ihm`.
        refine sing_accAsc (fun u lu hlt => ?_) haccd lsP
        exact ihm (maxsub u) (by omega) u lu le_rfl

/-- **M2 — `L₀` accessibility**: every `asc` (`cr_inv = 0`, CNF) term is
`olt`-accessible.  The base of the Towsner distinguished-set ladder. -/
theorem ascAcc {t : Three} (ht : asc t) : Acc oltAsc t :=
  accUpTo (maxsub t) t ht le_rfl

/-- **M2 — well-foundedness of `olt` on the `L₀` stratum.** -/
theorem wf_oltAsc : WellFounded oltAsc := by
  refine ⟨fun x => ?_⟩
  by_cases hx : asc x
  · exact ascAcc hx
  · exact Acc.intro x fun y hy => absurd hy.2.2 hx

/-- A `maxsub = 0` term has collapse-rank `0` (every argument's `maxsub`, being
`≤ maxsub t = 0`, is `≤` the head). -/
theorem cr_inv_eq_zero_of_maxsub_zero {t : Three} (h : maxsub t = 0) :
    cr_inv t = 0 := by
  induction t with
  | Z => rfl
  | P a b c ihb ihc =>
    simp only [maxsub_P] at h
    have hb : maxsub b = 0 := by omega
    have hc : maxsub c = 0 := by omega
    simp only [cr_inv_P]
    rw [if_neg (by omega), ihb hb, ihc hc]; omega

/-- `wf_olt0` (the `maxsub = 0` base) is the special case of M2: `lvl0 t → asc t`.
Thus M2 (`wf_oltAsc`) strictly extends `wf_olt0` from the `maxsub = 0` class to
the whole `cr_inv = 0` (collapse-free) stratum. -/
theorem asc_of_lvl0 {t : Three} (h : lvl0 t) : asc t :=
  ⟨h.1, cr_inv_eq_zero_of_maxsub_zero h.2⟩

end YAPSS
