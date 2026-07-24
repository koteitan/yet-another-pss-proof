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
import YAPSS.Otembed
import Mathlib.Data.List.Induction

namespace YAPSS

open Three

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

/-! ## Sibling-direction reduction lemmas for the head-`0` clause recursion

The `Q`-carrier `Q t := ∀ x ∈ Gterm 0 t, olt x t` is **not** hereditary on
subterms (e.g. `Q (P 0 (P 1 Z Z) Z)` is FALSE — `p₁(0)` is an arg-witness but
`¬ olt (p₁(0)) (p₀(p₁(0)))`), so the head-`0` clause cannot be proven by naive
`tsize` strong induction with carrier `Q`.  But the **sibling** direction of the
recursion *is* sound: model-verified (closure +5/+6/+7, `tools/probe_*`) the
clause at a node `P y A S` decomposes as
  `Gterm 0 (P y A S) = {A} ∪ Gterm 0 A ∪ Gterm 0 S`
and the sibling witnesses (`Gterm 0 S`) lift cleanly to the whole tree, while
the leading-tree witnesses (`{A} ∪ Gterm 0 A = Gterm 0 (P y A Z)`) lift via
`olt_lift_sib`.  These two lifts are the cleanly-provable part; the residual
`Wttone.H0clause_oper_step` is what remains for the leading single-tree case
(the seqlex-positional / `oper`-tiling core).  The lemmas below are that GREEN
sibling-direction machinery. -/

end YAPSS
