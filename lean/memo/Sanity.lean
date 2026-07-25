/-
証明には使わない検査用の `example`。定義が意図どおりであることを確かめるためだけに
置いてある。`lean/requirement.md` §1.3 による。
-/
import Term
import Wset

namespace YAPSS

open Three Wset

/-! ### `translate` が意図どおりか -/

example : translate [(0,0)] = P 0 Z Z := by simp [translate]

/-- `(0,0)(1,0) = p₀(p₀(0))` -/
example : translate [(0,0),(1,0)] = P 0 (P 0 Z Z) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-- `(0,0)(1,1) = p₀(p₁(0))` -/
example : translate [(0,0),(1,1)] = P 0 (P 1 Z Z) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-- `(0,0)(1,0)(1,0) = p₀(p₀(0)+p₀(0))` -/
example : translate [(0,0),(1,0),(1,0)] = P 0 (P 0 Z (P 0 Z Z)) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-- `(0,0)(1,1)(2,2)(3,3) = p₀(p₁(p₂(p₃(0))))` -/
example : translate [(0,0),(1,1),(2,2),(3,3)] = P 0 (P 1 (P 2 (P 3 Z Z) Z) Z) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-! ### `domT` / `graft` が意図どおりか -/

/-! ### 1b. Sanity checks: the `Ω_{m+1}` atom

A lone pair `(x, m+1)` is `Ω_{m+1}`: it satisfies `domT … m`, and its
`T_m`-indexed fundamental sequence is the identity `Ω_{m+1}[z] = z` (re-based),
exactly as in Buchholz. -/

example (x m : ℕ) : domT [(x, m + 1)] m := by
  refine ⟨by simp [entry], ?_⟩
  rintro ⟨j0, hj0, -⟩
  unfold nextR at hj0
  rw [if_neg (by omega)] at hj0
  have := hj0.2.2.1
  simp at this

example (x m : ℕ) (z : PairSeq) :
    graft [(x, m + 1)] z = z.map (fun p => (p.1 + x, p.2)) := by
  simp [graft, entry]

example (m : ℕ) : ¬ domT [((0 : ℕ), (0 : ℕ))] m := by
  rintro ⟨h, -⟩
  simp [entry] at h

/-! ### 1c. Sanity checks: why the `based` side condition is not cosmetic

`M = (0,3)(1,2)(1,1)` is `Ω_1`-cofinal (`domT M 0`): the trailing `(1,1)` is a
row-1 orphan (its only strict row-0 ancestor `(0,3)` carries row-1 `3 > 0`).  So
`translate M = p₃(p₂(0) + p₁(0))` and `M[z]` must be `p₃(p₂(0) + z)`.

The two blocks `[(0,0)]` and `[(2,0)]` have the *same* translate `p₀(0)`, but
only the `based` one grafts correctly: the other turns the grafted node into a
*child* of `(1,2)` instead of its sibling. -/

example : domT [(0, 3), (1, 2), (1, 1)] 0 := by
  rw [domT_iff (by simp)]
  refine ⟨by simp [entry], ?_⟩
  intro j0 h1 _
  have h2 : j0 = 0 ∨ j0 = 1 := by simp at h1; omega
  rcases h2 with rfl | rfl <;> simp [entry]

/-- The two candidate blocks are order-theoretically indistinguishable. -/
example : translate [((0 : ℕ), (0 : ℕ))] = translate [((2 : ℕ), (0 : ℕ))] := by
  simp [translate]

/-- `based` block: grafts to `p₃(p₂(0) + p₀(0))` — the honest substitution. -/
example : graft [(0, 3), (1, 2), (1, 1)] [(0, 0)] = [(0, 3), (1, 2), (1, 0)] := by
  decide

example : translate [((0 : ℕ), (3 : ℕ)), (1, 2), (1, 0)] = P 3 (P 2 Z (P 0 Z Z)) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-- Not `based`: the same `z` grafts to the WRONG term `p₃(p₂(p₀(0)))` — the
node became a *child* of `(1,2)` instead of its sibling. -/
example : graft [(0, 3), (1, 2), (1, 1)] [(2, 0)] = [(0, 3), (1, 2), (3, 0)] := by
  decide

example : translate [((0 : ℕ), (3 : ℕ)), (1, 2), (3, 0)] = P 3 (P 2 (P 0 Z Z) Z) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

end YAPSS
