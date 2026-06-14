/-
**The `maxr1 = 0` base level of the `W = T` route** (Lean port of
`wttbase.thy`).  This is the crux-free bottom of the direct termination
scaffold: a standard form all of whose row-1 entries are `0` translates to a
*genuine Buchholz OT term* (`wf3`), so the `maxr1 = 0` fragment terminates
directly via `wf_olt_wf3` and the strict decrease `m_step_decreases`, with
**no** value-comparison crux.

Consequently this file is FULLY `sorry`-free: the only `sorry` of the whole
route lives in `Wtt.lean` (`diag_acc`), and is not needed here.

The condition "all subscripts zero" is rendered as `subs t ⊆ {0}` on the OT
term side and `∀ p ∈ M, p.2 = 0` on the sequence side; `subs_translate`
links them.
-/
import YAPSS.Wtt

namespace YAPSS

open Three

/-! ## Subscript-`0` bookkeeping for OT terms -/

/-- A principal term with all subscripts `0` has head subscript `0`. -/
theorem subs_P_head0 {a : ℕ} {b c : Three} (h : subs (P a b c) ⊆ {0}) : a = 0 := by
  have : a ∈ subs (P a b c) := by simp [subs]
  simpa using h this

/-- Subscript-`0` is inherited by the argument. -/
theorem subs_P_subL {a : ℕ} {b c : Three} (h : subs (P a b c) ⊆ {0}) :
    subs b ⊆ {0} := by
  intro x hx; exact h (by simp [subs]; tauto)

/-- Subscript-`0` is inherited by the tail. -/
theorem subs_P_subR {a : ℕ} {b c : Three} (h : subs (P a b c) ⊆ {0}) :
    subs c ⊆ {0} := by
  intro x hx; exact h (by simp [subs]; tauto)

/-- CNF is inherited by the tail. -/
theorem cnf_P_tail {a : ℕ} {b c : Three} (h : cnf (P a b c)) : cnf c := by
  cases c with
  | Z => simp
  | P e f g => rw [cnf_P_P] at h; exact h.2.2

/-- CNF is inherited by the argument. -/
theorem cnf_P_arg {a : ℕ} {b c : Three} (h : cnf (P a b c)) : cnf b := by
  cases c with
  | Z => simpa using h
  | P e f g => rw [cnf_P_P] at h; exact h.1

/-! ## The two principal-domination facts -/

/-- In an all-`0`-subscript principal term, the argument is strictly below the
whole term.  Induction on `b`. -/
theorem olt_arg_principal0 :
    ∀ {b c : Three}, subs (P 0 b c) ⊆ {0} → olt b (P 0 b c) := by
  intro b
  induction b with
  | Z => intro c h; simp
  | P f bb bc ihbb _ =>
    intro c h
    have hf : f = 0 := subs_P_head0 (subs_P_subL h)
    subst hf
    exact Or.inr (Or.inl ⟨rfl, ihbb (subs_P_subL h)⟩)

/-- In an all-`0`-subscript CNF principal term, the tail is strictly below the
whole term.  Induction on `c`; the CNF non-domination clause `¬(b <o f)`
together with `olt_total` forces `f <o b` or `f = b`. -/
theorem olt_tail_principal0 :
    ∀ {b c : Three}, cnf (P 0 b c) → subs (P 0 b c) ⊆ {0} → olt c (P 0 b c) := by
  intro b c
  induction c generalizing b with
  | Z => intro _ _; simp
  | P e f g _ ihg =>
    intro hcnf h
    have he : e = 0 := subs_P_head0 (subs_P_subR h)
    subst he
    rw [cnf_P_P] at hcnf
    obtain ⟨_, ndom, cnfc⟩ := hcnf
    have nbf : ¬ (b <o f) := fun hb => ndom (Or.inr (Or.inl ⟨rfl, hb⟩))
    rcases Three.olt_total f b with hfb | hfeqb | hbf
    · exact Or.inr (Or.inl ⟨rfl, hfb⟩)
    · subst hfeqb; exact Or.inr (Or.inr ⟨rfl, rfl, ihg cnfc (subs_P_subR h)⟩)
    · exact absurd hbf nbf

/-- **OT3 for the base fragment.**  In an all-`0`-subscript CNF + `wf3` term,
every coefficient in `Gterm 0 t` is strictly below `t`.  The two principal
facts handle the argument and tail; the induction hypotheses handle the
nested coefficients, glued by `olt_trans`. -/
theorem OT3all :
    ∀ {t : Three}, cnf t → wf3 t → subs t ⊆ {0} → ∀ x ∈ Gterm 0 t, olt x t := by
  intro t
  induction t with
  | Z => intro _ _ _ x hx; simp [Gterm] at hx
  | P a b c ihb ihc =>
    intro hcnf hwf3 hsub x hx
    have ha : a = 0 := subs_P_head0 hsub
    subst ha
    have argb : olt b (P 0 b c) := olt_arg_principal0 hsub
    have tailc : olt c (P 0 b c) := olt_tail_principal0 hcnf hsub
    have subb : subs b ⊆ {0} := subs_P_subL hsub
    have subc : subs c ⊆ {0} := subs_P_subR hsub
    obtain ⟨wfb, wfc, _, _⟩ := (wf3_P).1 hwf3
    rw [mem_Gterm_P] at hx
    rcases hx with ⟨_, hxb⟩ | hxc
    · rcases hxb with rfl | hxg
      · exact argb
      · exact Three.olt_trans (ihb (cnf_P_arg hcnf) wfb subb x hxg) argb
    · exact Three.olt_trans (ihc (cnf_P_tail hcnf) wfc subc x hxc) tailc

/-- **A CNF term with all subscripts `0` is a Buchholz OT term.**  Induction
on `t`; the OT3 clause comes from `OT3all` on the argument, the
non-increasing-spine clause `hdle c (P 0 b Z)` from the CNF non-domination
clause via `olt_total`. -/
theorem wf3_of_cnf_subs0 : ∀ {t : Three}, cnf t → subs t ⊆ {0} → wf3 t := by
  intro t
  induction t with
  | Z => intro _ _; trivial
  | P a b c ihb ihc =>
    intro hcnf hsub
    have ha : a = 0 := subs_P_head0 hsub
    subst ha
    have cnfb : cnf b := cnf_P_arg hcnf
    have cnfc : cnf c := cnf_P_tail hcnf
    have subb : subs b ⊆ {0} := subs_P_subL hsub
    have subc : subs c ⊆ {0} := subs_P_subR hsub
    have wfb : wf3 b := ihb cnfb subb
    have wfc : wf3 c := ihc cnfc subc
    refine (wf3_P).2 ⟨wfb, wfc, OT3all cnfb wfb subb, ?_⟩
    cases c with
    | Z => trivial
    | P e f g =>
      have he : e = 0 := subs_P_head0 subc
      subst he
      rw [cnf_P_P] at hcnf
      obtain ⟨_, ndom, _⟩ := hcnf
      have nbf : ¬ (b <o f) := fun hb => ndom (Or.inr (Or.inl ⟨rfl, hb⟩))
      rw [hdle_P_P]
      rcases Three.olt_total f b with hfb | hfeqb | hbf
      · exact Or.inr ⟨rfl, Or.inl hfb⟩
      · exact Or.inr ⟨rfl, Or.inr hfeqb⟩
      · exact absurd hbf nbf

/-! ## Lifting to pair sequences -/

/-- If every row-1 entry of `M` is `0`, then `sndSet M ⊆ {0}`. -/
theorem sndSet_subs0 {M : PairSeq} (z : ∀ p ∈ M, p.2 = 0) : sndSet M ⊆ {0} := by
  intro y hy
  rw [mem_sndSet] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  simp [z p hp]

/-- **A standard form with all row-1 entries `0` translates to a Buchholz OT
term.**  CNF comes from `cnf_ST_PS`; all subscripts are `0` because
`subs (translate M) ⊆ sndSet M ⊆ {0}`; then `wf3_of_cnf_subs0`. -/
theorem wf3_translate_subs0 {M : PairSeq} (hM : ST_PS M)
    (z : ∀ p ∈ M, p.2 = 0) : wf3 (translate M) := by
  have hsub : subs (translate M) ⊆ {0} :=
    Set.Subset.trans (subs_translate M) (sndSet_subs0 z)
  exact wf3_of_cnf_subs0 (cnf_ST_PS hM) hsub

/-- The base fragment is closed under one step: an all-`0` standard form
expands to an all-`0` standard form.  `step_in_ST_PS` keeps standardness;
`oper_snd_subset` keeps the row-1 entries inside the old ones, hence `0`. -/
theorem subs0_step_closed {M T : PairSeq} (hM : ST_PS M) (z : ∀ p ∈ M, p.2 = 0)
    (st : step M T) : ST_PS T ∧ (∀ p ∈ T, p.2 = 0) := by
  refine ⟨step_in_ST_PS hM st, ?_⟩
  cases st with
  | @step_oper n L hn =>
    intro p hp
    have hmem : p.2 ∈ sndSet (M⟦n⟧) := by rw [mem_sndSet]; exact ⟨p, hp, rfl⟩
    have := oper_snd_subset M n hmem
    rw [mem_sndSet] at this
    obtain ⟨q, hq, hq2⟩ := this
    rw [← hq2]; exact z q hq

/-- The order-decrease on the base fragment: a step strictly decreases the
`olt`-value, with both endpoints in `wf3` — i.e. it is a step of the
well-founded relation `oltWf3`. -/
theorem subs0_step_decreases {M T : PairSeq} (hM : ST_PS M)
    (z : ∀ p ∈ M, p.2 = 0) (st : step M T) :
    oltWf3 (translate T) (translate M) := by
  obtain ⟨hT, zT⟩ := subs0_step_closed hM z st
  refine ⟨?_, wf3_translate_subs0 hT zT, wf3_translate_subs0 hM z⟩
  cases st with
  | @step_oper n L hn => exact m_step_decreases L hn

/-- **Generic accessibility for `wf3`-fragments.**  Any step-closed sub-class
`D` of the standard forms that lands inside `wf3` (under `translate`) is
`stepR`-accessible everywhere.  Proved by well-founded induction on
`translate M` along `wf_olt_wf3`: each successor strictly decreases the
`wf3`-bounded `olt`-value, so the induction hypothesis applies. -/
theorem acc_wf3_fragment
    (D : PairSeq → Prop)
    (_DST : ∀ N, D N → ST_PS N)
    (closed : ∀ N T, D N → step N T → D T)
    (wf3D : ∀ N, D N → wf3 (translate N))
    {M : PairSeq} (MD : D M) : Acc stepR M := by
  have key : ∀ t : Three, ∀ N : PairSeq, translate N = t → D N → Acc stepR N := by
    intro t
    induction t using wf_olt_wf3.induction with
    | _ t ih =>
      intro N hNt hND
      refine Acc.intro N (fun T hT => ?_)
      obtain ⟨_, st⟩ := hT
      have hTD : D T := closed N T hND st
      have dec : translate T <o translate N := by
        cases st with
        | @step_oper n L hn => exact m_step_decreases L hn
      have hrel : oltWf3 (translate T) (translate N) :=
        ⟨dec, wf3D T hTD, wf3D N hND⟩
      rw [hNt] at hrel
      exact ih (translate T) hrel T rfl hTD
  exact key (translate M) M rfl MD

/-- **The base level terminates directly.**  Every all-`0`-subscript standard
form is `stepR`-accessible — crux-free, via `acc_wf3_fragment` with
`D = {N | ST_PS N ∧ all row-1 entries 0}`, whose three obligations are
`subs0_step_closed`, `wf3_translate_subs0`. -/
theorem acc_subs0 {M : PairSeq} (hM : ST_PS M) (z : ∀ p ∈ M, p.2 = 0) :
    Acc stepR M := by
  refine acc_wf3_fragment (fun N => ST_PS N ∧ (∀ p ∈ N, p.2 = 0))
    (fun N hN => hN.1)
    (fun N T hN st => subs0_step_closed hN.1 hN.2 st)
    (fun N hN => wf3_translate_subs0 hN.1 hN.2) ⟨hM, z⟩

end YAPSS
