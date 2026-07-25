/-
**Buchholz's coefficient set `G_u` on three-branch terms.**

`Gterm u t` is the set of arguments `b` occurring in a principal `D_a(b) = P a b _`
of `t` whose subscript satisfies `u ≤ a`, together with the same set computed
inside those arguments.  It is a *syntactic* operation on terms: no ordinal, no
value map, no collapsing function is involved.

Only `Gterm` and the size bound `Gterm_tsize` are used downstream (`Nrm.lean`,
`Nrmstep.lean`); the ordinal value map `oV : Three → Ordinal` and the Buchholz
`OT` predicate `wf3` that used to accompany them belong to the abandoned
ordinal route and are not part of the termination proof.
-/
import YAPSS.Wfsum

namespace YAPSS

open Three

/-- `Gterm u t` = Buchholz's `G_u` on terms: for the principal `D_a(b)`, it
is `{b} ∪ G_u b` when `u ≤ a`, else `∅`; on a sum it is the union. -/
def Gterm (u : ℕ) : Three → Set Three
  | Z => ∅
  | P a b c => (if u ≤ a then insert b (Gterm u b) else ∅) ∪ Gterm u c

@[simp] theorem Gterm_Z (u : ℕ) : Gterm u Z = ∅ := rfl

theorem Gterm_P (u a : ℕ) (b c : Three) :
    Gterm u (P a b c) = (if u ≤ a then insert b (Gterm u b) else ∅) ∪ Gterm u c := rfl

theorem mem_Gterm_P {u a : ℕ} {b c x : Three} :
    x ∈ Gterm u (P a b c) ↔
      (u ≤ a ∧ (x = b ∨ x ∈ Gterm u b)) ∨ x ∈ Gterm u c := by
  rw [Gterm_P]
  by_cases h : u ≤ a <;> simp [h]

/-- Every member of `Gterm v t` is a strictly smaller term than `t`. -/
theorem Gterm_tsize {t x : Three} {v : ℕ} (hx : x ∈ Gterm v t) :
    tsize x < tsize t := by
  induction t with
  | Z => simp at hx
  | P a b c ihb ihc =>
    rcases mem_Gterm_P.1 hx with ⟨-, rfl | hx⟩ | hx
    · simp only [tsize]
      omega
    · have := ihb hx
      simp only [tsize]
      omega
    · have := ihc hx
      simp only [tsize]
      omega

end YAPSS
