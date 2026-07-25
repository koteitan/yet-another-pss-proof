/-
PSS definitions, faithful to P進大好きbot's article "ペア数列の停止性"
(pss-original-paper.html).

This file contains only the definitions needed for the termination proof via
the p_a(b)+c notation: the §5 formulation (pair sequences, parent relations,
fundamental sequence `M[n]`) and the §6.7 standard form `ST_PS`.  Variable
names follow the article.  (The §6 reduction machinery `Red`, `Br`, … used by
the Buchholz approach is deliberately omitted; it is not needed here.)

Representation conventions:
  * a pair sequence is `PairSeq := List (ℕ × ℕ)`
  * indexing is total: `M.getD j (0, 0)`, so out-of-range reads give `(0,0)`
    (this default *is* read — see `idx1_shift` in `Nrmstep.lean`)
  * the reflexive-transitive closure is `Relation.ReflTransGen`
  * the definite description is `Classical.epsilon`, used only under the
    `hasParent` uniqueness guard
-/
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic

namespace YAPSS

/-! ## §4 記法 (Notation)

`Lng` is `List.length`; we use `M.length` directly in the port. -/

/-! ## §5 定式化 (Formulation) -/

/-- A pair sequence: a list of pairs of naturals. -/
abbrev PairSeq := List (ℕ × ℕ)

/-- `entry M i j` = `M_{i,j}`: the `i`-th component (row) of the `j`-th pair. -/
def entry (M : PairSeq) (i j : ℕ) : ℕ :=
  if i = 0 then (M.getD j (0, 0)).1 else (M.getD j (0, 0)).2

/-! ### §5.1 親子関係 (Parent-child relations) -/

/-- Row-0 "next" relation: `j1` is the next index after `j0` whose row-0 value
strictly exceeds `entry M 0 j0`, with no index in between below it. -/
def nextrel0 (M : PairSeq) (j0 j1 : ℕ) : Prop :=
  j0 < M.length ∧ j1 < M.length ∧ j0 < j1 ∧
  entry M 0 j0 < entry M 0 j1 ∧
  (∀ j, j0 < j ∧ j < j1 → entry M 0 j1 ≤ entry M 0 j)

/-- Row-0 ancestry: reflexive-transitive closure of `nextrel0`. -/
def le0 (M : PairSeq) (j0 j1 : ℕ) : Prop :=
  j0 < M.length ∧ j1 < M.length ∧ Relation.ReflTransGen (nextrel0 M) j0 j1

/-- Row-1 "next" relation (refines row-0 ancestry). -/
def nextrel1 (M : PairSeq) (j0 j1 : ℕ) : Prop :=
  j0 < M.length ∧ j1 < M.length ∧ j0 < j1 ∧
  entry M 1 j0 < entry M 1 j1 ∧
  le0 M j0 j1 ∧
  (∀ j, j0 < j ∧ le0 M j j1 → entry M 1 j1 ≤ entry M 1 j)

/-- Row-indexed "next" relation. -/
def nextR (M : PairSeq) (i j0 j1 : ℕ) : Prop :=
  if i = 0 then nextrel0 M j0 j1 else nextrel1 M j0 j1

/-! ### §5.2 前者関数 (Predecessor functions) -/

/-- Drop the last pair (identity on sequences of length ≤ 1). -/
def Pred (M : PairSeq) : PairSeq :=
  if M.length ≤ 1 then M else M.dropLast

/-! ### §5.3 基本列 (Fundamental sequence, `M[n]`) -/

/-- The row used to find the parent of the last pair: row 1 if its row-1 value
is positive, else row 0. -/
def idx1 (M : PairSeq) (j1 : ℕ) : ℕ :=
  if 0 < entry M 1 j1 then 1 else 0

/-- The last pair has a (unique) parent in row `i`. -/
def hasParent (M : PairSeq) (i j1 : ℕ) : Prop :=
  ∃! j0, nextR M i j0 j1

/-- The parent of `j1` in row `i` (Hilbert choice; under the `hasParent` guard
this is the unique `j0` with `nextR M i j0 j1`). -/
noncomputable def parent (M : PairSeq) (i j1 : ℕ) : ℕ :=
  Classical.epsilon fun j0 => nextR M i j0 j1

open Classical in
/-- The fundamental sequence `M[n]` (expansion with copy count `n`).

`[j0..<j1]` is rendered as `List.range' j0 (j1 - j0)` and
`concat (map f [0..<n])` as `(List.range n).flatMap f`. -/
noncomputable def oper (M : PairSeq) (n : ℕ) : PairSeq :=
  let j1 := M.length - 1
  if j1 = 0 then M
  else if entry M 0 j1 = 0 ∧ entry M 1 j1 = 0 then Pred M
  else
    let i1 := idx1 M j1
    if ¬ hasParent M i1 j1 then Pred M
    else
      let j0 := parent M i1 j1
      let d0 := if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0
      let d1 := if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0
      M.take j0 ++
        (List.range n).flatMap fun k =>
          (List.range' j0 (j1 - j0)).map fun j =>
            (entry M 0 j + k * d0, entry M 1 j + k * d1)

@[inherit_doc] notation:max M "⟦" n "⟧" => oper M n

/-! ### §6.5 / §6.7 standard form -/

/-- `diagSeq a b`: the diagonal segment `((j,j))_{j=a}^{b}` (length `b - a + 1`). -/
def diagSeq (a b : ℕ) : PairSeq :=
  (List.range' a (b + 1 - a)).map fun j => (j, j)

/-- `ST_PS` (標準形): the least set of *standard forms*, i.e. pair sequences
reachable from the initial diagonal `(0,0)(1,1)…(v,v) = diagSeq 0 v` by the
expansion `M ↦ M⟦n⟧` (`n ≥ 1`).  The base diagonals start at `(0,0)` (the
genuine initial state of a PSS computation); every standard form therefore
begins with `(0,0)`.  (Using `diagSeq u v` with `u > 0` as a base would admit
spurious sequences starting at `(u,u)` that are not reachable and break the
normal-form invariants — CNF sums, subscript-monotone descent.) -/
inductive ST_PS : PairSeq → Prop where
  | diag (v : ℕ) : ST_PS (diagSeq 0 v)
  | oper {M : PairSeq} {n : ℕ} : ST_PS M → 1 ≤ n → ST_PS (M⟦n⟧)

/-- One expansion step of the system: `M → M⟦n⟧` for some copy count `n ≥ 1`,
on sequences of length `> 1`.  Termination (independent of the activation
function) means this relation has no infinite forward chain. -/
inductive step : PairSeq → PairSeq → Prop where
  | step_oper {M : PairSeq} {n : ℕ} :
      1 < M.length → 1 ≤ n → step M (M⟦n⟧)

end YAPSS
