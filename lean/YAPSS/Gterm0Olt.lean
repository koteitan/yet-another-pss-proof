/-
**Assets toward the head-`0` root clause `∀ x ∈ Gterm 0 (translate B), olt x
(translate B)`** (the single residual `H0clause_oper_step`, `Wttone.lean`).

This file collects the *model-verified, GREEN* building blocks of the
seqlex/depth-shift route to that clause.  The residual itself is NOT closed here
(see `Wttone.lean:386` and the campaign notes): its content reduces to the global
positional fact `seqlex (shift K) B` for the canonical `Gterm_translate_subblock`
witness `K = B[i:j]` (a contiguous infix), which is TRUE (model-verified to
closure+7) but whose proof needs a positional `steps1`-driven columnwise
domination argument not yet formalized.  The lemmas below are the parts that ARE
cleanly provable and are needed by that route regardless.
-/
import YAPSS.Mechanized
import Mathlib.Data.List.Induction

namespace YAPSS

open Three

/-- Transitivity of the reflexive order `≤o`. -/
theorem ole_trans {x y z : Three} (h1 : x ≤o y) (h2 : y ≤o z) : x ≤o z := by
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · exact Or.inl (olt_trans h1 h2)
    · exact Or.inl h1
  · exact h2

/-- Appending any block only (weakly) increases the translation.  Iterates
`translate_snoc_increase` over the appended suffix. -/
theorem translate_append_ge (C D : PairSeq) :
    translate C ≤o translate (C ++ D) := by
  induction D using List.reverseRecOn with
  | nil => simp [ole]
  | append_singleton D m ih =>
    rw [← List.append_assoc]
    exact ole_trans ih (Or.inl (translate_snoc_increase (C ++ D) m))

/-- **Taking a prefix only (weakly) decreases the translation.**  (Generalises
`translate_dropLast_decrease` to an arbitrary prefix length; `≤o` because the
prefix may equal the whole list.)  Used to bound a Gterm-`0` witness
`K = B[i:j] = (B.drop i).take (j-i)` by the suffix it starts. -/
theorem translate_take_le (m : ℕ) (L : PairSeq) :
    translate (L.take m) ≤o translate L := by
  conv_rhs => rw [← List.take_append_drop m L]
  exact translate_append_ge (L.take m) (L.drop m)

end YAPSS
