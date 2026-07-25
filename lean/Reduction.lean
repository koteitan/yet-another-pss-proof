/-
Top-level termination of the Pair Sequence System.

Termination — no infinite expansion chain on the standard form `ST_PS` — is
reduced to two facts about the `p_a(b)+c` measure `translate`:

* `dec`: each expansion step strictly decreases `translate` (`m_step_decreases`);
* `wfimg`: the subscript-first order `<o` is well-founded on the image
  `NF = translate '' ST_PS` (discharged in `Final.lean`).

`step_terminates` discharges `dec` from `m_step_decreases`, so termination
hinges on `wfimg` alone.

In `WellFounded R` the arguments read `R y x` = "`y` below `x`".
-/
import Decrease

namespace YAPSS

open Three

/-- `NF`: the image of the standard forms under `translate`. -/
def NF : Set Three := {t | ∃ M, ST_PS M ∧ translate M = t}

/-- `Rnf`: the order `<o` restricted to `NF` (as a relation; `Rnf v u` reads
"`v` below `u`"). -/
def Rnf (v u : Three) : Prop := v <o u ∧ u ∈ NF ∧ v ∈ NF

/-- The one-step relation on standard forms, as a Lean relation
(the pair `(T, M)` with `M ∈ ST_PS` and `step M T`). -/
def stepRel (T M : PairSeq) : Prop := ST_PS M ∧ step M T

/-- Conditional termination: decrease + well-foundedness on the image give
well-foundedness of the one-step relation on `ST_PS`. -/
theorem step_terminates_cond
    (dec : ∀ M n, ST_PS M → 1 < M.length → 1 ≤ n →
      translate (M⟦n⟧) <o translate M)
    (wfimg : WellFounded Rnf) :
    WellFounded stepRel := by
  have hsub : ∀ {T M}, stepRel T M → InvImage Rnf translate T M := by
    intro T M h
    obtain ⟨hM, hstep⟩ := h
    cases hstep with
    | @step_oper n L hn =>
      have hT : ST_PS (M⟦n⟧) := ST_PS.oper hM hn
      exact ⟨dec M n hM L hn, ⟨M, hM, rfl⟩, ⟨M⟦n⟧, hT, rfl⟩⟩
  exact Subrelation.wf hsub (InvImage.wf translate wfimg)

/-- Equivalent phrasing: there is no infinite expansion sequence within
`ST_PS`. -/
theorem no_infinite_expansion_cond
    (dec : ∀ M n, ST_PS M → 1 < M.length → 1 ≤ n →
      translate (M⟦n⟧) <o translate M)
    (wfimg : WellFounded Rnf) :
    ¬ ∃ S : ℕ → PairSeq, (∀ i, ST_PS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) := by
  rintro ⟨S, hS, hstep⟩
  have wf : WellFounded stepRel := step_terminates_cond dec wfimg
  have chain : ∀ i, stepRel (S (i + 1)) (S i) := fun i => ⟨hS i, hstep i⟩
  -- no infinite descending chain in a well-founded relation
  have key : ∀ x, Acc stepRel x → ∀ i, S i = x → False := by
    intro x hacc
    induction hacc with
    | intro x _ ih =>
      intro i hi
      exact ih (S (i + 1)) (hi ▸ chain i) (i + 1) rfl
  exact key (S 0) (wf.apply (S 0)) 0 rfl

/-!
Discharging `dec` by the proved decrease lemma, termination of the pair
sequence system reduces to well-foundedness of `<o` on `NF` alone.
-/

theorem step_terminates (wfimg : WellFounded Rnf) : WellFounded stepRel :=
  step_terminates_cond (fun _ _ _ L hn => m_step_decreases L hn) wfimg

theorem no_infinite_expansion (wfimg : WellFounded Rnf) :
    ¬ ∃ S : ℕ → PairSeq, (∀ i, ST_PS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion_cond (fun _ _ _ L hn => m_step_decreases L hn) wfimg

end YAPSS
