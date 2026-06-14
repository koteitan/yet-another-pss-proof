/-
**The `W = T` direct termination route** (Lean port of `wtt.thy`).

This is a *second*, order-free termination scaffold for the Pair Sequence
System, complementary to the `Rnf` order route in `Proofs.lean`.  Instead of
reducing well-foundedness to `<o`-accessibility of `translate (diagSeq 0 v)`,
it works directly with the one-step generation relation

  `stepR T M := ST_PS M ∧ step M T`

(Isabelle's `{(T, M). M ∈ ST_PS ∧ step M T}`) and reduces `WellFounded stepR`
to *accessibility of the diagonal seeds* `diagSeq 0 v` under `stepR`.

The reduction (`direct_acc_of_ST_PS`, `PSS_terminates_direct`) is fully
proved; the residual Buchholz crux — accessibility of the diagonals
themselves — is isolated as the single `sorry` `diag_acc`.

Port conventions (Isabelle → Lean):
  * `wf R` (set of pairs)  → `WellFounded R` (`R y x` means "`y` below `x`")
  * `x ∈ acc R`            → `Acc R x`
  * `acc_downward`         → `Acc.inv`
-/
import YAPSS.Proofs
import YAPSS.Otembed
import YAPSS.Wf

namespace YAPSS

open Three

/-- The one-step generation relation on standard forms, as a Lean relation:
`stepR T M` is Isabelle's `(T, M) ∈ stepR`, i.e. `M` is a standard form and
`M` expands to `T` in one step.  `Acc stepR M` therefore means "`M` is
accessible". -/
def stepR (T M : PairSeq) : Prop := ST_PS M ∧ step M T

/-- Short forms (length `≤ 1`) have no successor under `stepR`, so they are
trivially accessible. -/
theorem acc_short {M : PairSeq} (h : M.length ≤ 1) : Acc stepR M := by
  refine Acc.intro M (fun T hT => ?_)
  obtain ⟨_, st⟩ := hT
  cases st with
  | @step_oper n L hn => omega

/-- **The reduction.**  If every diagonal seed `diagSeq 0 v` is accessible
under `stepR`, then *every* standard form is accessible.  Generation
induction on `ST_PS`: diagonals are accessible by hypothesis; for an
expansion `M ↦ M⟦n⟧`, either `M` is short (then `M⟦n⟧ = M` and the IH
applies) or `1 < |M|` and `stepR (M⟦n⟧) M`, so `M⟦n⟧` inherits accessibility
from `M` via `Acc.inv`. -/
theorem direct_acc_of_ST_PS (diagacc : ∀ v, Acc stepR (diagSeq 0 v))
    {M : PairSeq} (hM : ST_PS M) : Acc stepR M := by
  induction hM with
  | diag v => exact diagacc v
  | @oper M n hM hn ih =>
    by_cases L : 1 < M.length
    · have st : step M (M⟦n⟧) := step.step_oper L hn
      exact ih.inv ⟨hM, st⟩
    · rw [oper_eq_self_short n (by omega)]
      exact ih

/-- **Conditional termination.**  Diagonal accessibility implies that the
whole generation relation `stepR` is well-founded.  A non-standard `x` has no
`stepR`-predecessor (the first component of `stepR _ x` requires `ST_PS x`),
so it is accessible vacuously; a standard `x` is accessible by the
reduction. -/
theorem PSS_terminates_direct (diagacc : ∀ v, Acc stepR (diagSeq 0 v)) :
    WellFounded stepR := by
  refine ⟨fun x => ?_⟩
  by_cases hx : ST_PS x
  · exact direct_acc_of_ST_PS diagacc hx
  · exact Acc.intro x (fun T hT => absurd hT.1 hx)

/-- Levels never increase along a step: `maxsub (translate T) ≤ maxsub
(translate M)`.  From the strict decrease `m_step_decreases` and the
subscript-monotonicity `maxsub_mono_NF'` on the image `NF`. -/
theorem step_level_noninc {M T : PairSeq} (hM : ST_PS M) (st : step M T) :
    maxsub (translate T) ≤ maxsub (translate M) := by
  cases st with
  | @step_oper n L hn =>
    have dec : translate (M⟦n⟧) <o translate M := m_step_decreases L hn
    have hmnf : translate M ∈ NF := ⟨M, hM, rfl⟩
    have htnf : translate (M⟦n⟧) ∈ NF := ⟨M⟦n⟧, ST_PS.oper hM hn, rfl⟩
    exact maxsub_mono_NF' htnf hmnf dec

/-- **The Buchholz crux** (the only `sorry` of this route): every diagonal
tower `diagSeq 0 v` is accessible under `stepR`.  This is the ψ-collapsing
content shared with the `Rnf` route — see `Proofs.acc_Rnf_of_ST_PS`'s
`diagacc` hypothesis — and is left open here. -/
theorem diag_acc (v : ℕ) : Acc stepR (diagSeq 0 v) := by
  sorry

/-- **Top-level termination of the PSS via the direct route.**  `stepR` is
well-founded, discharging the diagonal-accessibility hypothesis of
`PSS_terminates_direct` with `diag_acc`. -/
theorem PSS_terminates_wtt : WellFounded stepR :=
  PSS_terminates_direct diag_acc

end YAPSS
