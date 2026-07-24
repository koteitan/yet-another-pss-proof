/-
Sum-layer reduction.  Lean port of `wfsum.thy`.

Within-level WF reduces to argument-level WF via the multiset extension
(Dershowitz–Manna), as in the PrSS proof.  An `NF` term is a non-increasing
sum `p₀(b₁)+…+p₀(bₖ)` (head subscript `0` by `inv2`, sibling subscripts `≤ 0`
by `cnf_tops_le`, non-increasing by `cnf`); on such sums `<o` is lex on the
argument lists, which embeds into the multiset extension of the argument
order.

Port note: Isabelle's `mult` (transitive closure of one-step) is replaced by
the one-step Dershowitz–Manna order `DMLT` (Mathlib's `IsDershowitzMannaLT`,
made parametric in the relation via a local `Preorder` instance); for a
transitive relation the two have the same well-founded parts, and every use
here exhibits a one-step witness anyway.

`wf_ArgsA` (the Buchholz-collapse core) is the sole `sorry`, exactly as in
the Isabelle source — that route is frozen there in favour of the value
normalisation `nrm` (see `task.md`).
-/
import YAPSS.Wf
import Mathlib.Data.Multiset.DershowitzManna

namespace YAPSS

open Three

/-! ## A parametric Dershowitz–Manna order -/

/-! ## Sum arguments and summands -/

/-- The list of arguments along the sum chain. -/
def sargs : Three → List Three
  | Z => []
  | P _ b c => b :: sargs c

@[simp] theorem sargs_Z : sargs Z = [] := rfl
@[simp] theorem sargs_P (a : ℕ) (b c : Three) : sargs (P a b c) = b :: sargs c := rfl

/-- The argument multiset of a sum. -/
def margs (x : Three) : Multiset Three := ↑(sargs x)

theorem ole_trans {x y z : Three} (h1 : x ≤o y) (h2 : y ≤o z) : x ≤o z := by
  rcases h1 with h1 | rfl
  · exact Or.inl (olt_ole_trans h1 h2)
  · exact h2

/-! ## `NF` terms are zero-top sums -/

/-! ## The general sum peel: `<o` on *any* CNF sums embeds into the multiset
extension of the order on the summand singletons (no zero-tops needed) -/

/-- The summand singletons of a sum. -/
def summands : Three → List Three
  | Z => []
  | P a b c => P a b Z :: summands c

@[simp] theorem summands_Z : summands Z = [] := rfl
@[simp] theorem summands_P (a : ℕ) (b c : Three) :
    summands (P a b c) = P a b Z :: summands c := rfl

theorem summands_shape {x s : Three} (hs : s ∈ summands x) :
    ∃ a c, s = P a c Z := by
  induction x with
  | Z => simp at hs
  | P a b c ihb ihc =>
    rw [summands_P] at hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨a, b, rfl⟩
    · exact ihc hs

/-! ## The level-`m` argument classes and the descent of the residual core -/

/-! ## Level 0: the base of the ladder (PrSS-style accessibility)

At level `0` all subscripts are `0`, so the singleton order never drops a
subscript and the PrSS argument (hereditary multisets, Dershowitz–Manna
accessibility) closes outright: `<o` is WF on the class of CNF terms with
`maxsub = 0`.  This is the base case of the level ladder; the induction step
(level `m` from levels `< m`) is the Buchholz-collapse core, still open. -/

/-- Structural size of a term. -/
def tsize : Three → ℕ
  | Z => 1
  | P _ b c => tsize b + tsize c + 1

/-! ## The residual core, two levels in

WF of `<o` on the arguments (of any subscript) occurring inside the level-`m`
sum arguments.  The level-`0` instance follows from the base theorem
`wf_olt0`; the induction step (level `m` from levels `< m`) is the
Buchholz-collapse core — `sorry` exactly as in the Isabelle source (route
frozen there in favour of the `nrm` value normalisation, see `task.md`). -/

/-! ## Top-level: PSS termination, modulo the argument core -/

end YAPSS
