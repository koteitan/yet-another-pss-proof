/-
# 🚨 `AscArgDomExplicit` (and `AscArgDom`) is FALSE as stated

I was asked to prove `AscArgDomExplicit` (`YAPSS/Cofinality.lean:989`).  It is
**refutable**: there is an explicit counterexample, and this file contains it.

**The route is not broken.**  The statement is merely *over-general*: it
quantifies over block-root decompositions that the cofinality proof never
produces.  Adding back the one clause that `oper_bad_blocks` already supplies —
and that `oper_bad_blocks_all` drops — restores it (0 violations, §4).

--------------------------------------------------------------------------------
## 1. The counterexample

    M   = (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)                     ∈ ST_PS
    N   = (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,1)(7,1)  = M⟦3⟧        ∈ ST_PS

with the (legal, per the current hypotheses) decomposition

    v0 = 3,  w0 = 1,  d0 = 3,  G = (0,0)(1,1)(2,2),  R = (4,0)(5,1),  S = (7,1)

Every hypothesis of `AscArgDomExplicit` holds:

* `M = (G ++ ((3,1) :: R)) ++ [(3+3, 1+1)]`      ✓ (`ce_M_eq`)
* `N = (G ++ ((3,1) :: R)) ++ (3+3, 1) :: S`     ✓ (`ce_N_eq`)
* `∀ x ∈ R, 3 < x.1`                             ✓ (`ce_R_gt`)
* `0 < 3`                                        ✓

but the conclusion fails (`ce_not_sle`):

    S_hi = S.takeWhile (6 < ·.1) = (7,1)                    (length 1)
    RHS  = shiftr0 3 (R ++ copies 3 (shiftr0 3 ((3,1)::R)) 1)
         = (7,0)(8,1)(9,1)(10,0)(11,1)

and `(7,1)` is **strictly greater** than `(7,0)` in the column order, so
`sle S_hi RHS` is false at the very first column.

### The `ST_PS` derivations (model-verified; both are short)

```
diag 3 = (0,0)(1,1)(2,2)(3,3)
  ⟦2⟧ → (0,0)(1,1)(2,2)(3,2)
  ⟦2⟧ → (0,0)(1,1)(2,2)(3,1)(4,2)
  ⟦2⟧ → (0,0)(1,1)(2,2)(3,1)(4,1)
  ⟦2⟧ → (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(7,1)
  ⟦1⟧ → (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)              = M
  ⟦3⟧ → (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,1)(7,1)         = N
```

`ascArgDomExplicit_false` below is a real theorem: it derives `¬ AscArgDomExplicit`
from the two membership facts `ST_PS M`, `ST_PS N`, which are pure `oper`
computations along the derivation above (no `sorry` is used anywhere in this
file; the two facts are explicit hypotheses).

--------------------------------------------------------------------------------
## 2. Diagnosis — where the clause was lost

`oper_bad_blocks` (`YAPSS/Mechanized.lean:836`) produces, in the ascending
branch, **four** conjuncts:

    0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0 ∧ nextrel1 M G.length (M.length - 1)
                                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

`oper_bad_blocks_all` (`YAPSS/Cofinality.lean:476`) re-derives the decomposition
but its disjunction keeps only **three**:

    0 < d0 ∧ lp.2 = w0 + 1 ∧ lp.1 = v0 + d0

The `nextrel1` clause — "`(v0,w0)` really is the **row-1 parent** of the dropped
column", i.e. the block root that `oper` itself picks — is dropped there, and its
absence propagates into `AscCrux` (:864), `AscCrux1` (:878), `AscArgDom` (:975)
and `AscArgDomExplicit` (:989).

In the counterexample the row-1 parent of `M`'s last column is index **5**
(the column `(5,1)`), not index 3.  With the correct root the instance is
    `v0 = 5, w0 = 1, d0 = 1, R = []`,
and then `RHS = (7,1)(8,1)`, `S_hi = (7,1)`, and `sle` holds (as a prefix).
The current hypotheses simply cannot tell the two decompositions apart, because
`(∀ x ∈ R, v0 < x.1)` is satisfied by *both*.

--------------------------------------------------------------------------------
## 3. The fix

Re-thread the dropped clause.  `AscArgDomExplicit'` below is the corrected
statement, and `oper_bad_blocks_nextrel1` (proved here, `sorryAx`-free) shows the
extra hypothesis is **free**: `oper_bad_blocks` already hands it over, so
strengthening `oper_bad_blocks_all` to keep it requires no new mathematics —
only re-plumbing `oper_bad_blocks_all` → `seqlex_cof_bad` → `AscCrux` →
`AscCrux1` → `AscArgDom(Explicit)` to carry one more conjunct.

--------------------------------------------------------------------------------
## 4. Model evidence

Closure from `diagSeq 0 v` (`v ≤ 5`), `n ≤ 5`, depth 8, length ≤ 11:

| statement | instances | violations |
|---|---|---|
| `AscArgDomExplicit` as written           | 9425 | **28** |
| + `nextrel1 M G.length (M.length-1)`     | 6089 | **0**  |
| + row-1 valley clause only               | 6089 | **0**  |
| + `∀ x ∈ R, w0 + 1 ≤ x.2`                | 6044 | **0**  |

(The `oper` model was validated against six independently hand-computed values,
including the worked examples in `Mechanized.lean`.)

The third row is worth noting: `∀ x ∈ R, w0 + 1 ≤ x.2` is exactly the fact
`asc_first_column`'s docstring flags as *"paired with `R.headI.2 ≥ w0 + 1` …
NOT yet proved"*.  It also kills the counterexample (there `R = (4,0)(5,1)` has
row-1 values `0` and `1`, both `< w0 + 1 = 2`), and it is the form that makes the
first-column comparison go through directly, so it may be the more convenient
clause to thread.
-/
import YAPSS.Cofinality

namespace YAPSS

/-! ## The counterexample data -/

def ceG : PairSeq := [(0, 0), (1, 1), (2, 2)]
def ceR : PairSeq := [(4, 0), (5, 1)]
def ceS : PairSeq := [(7, 1)]

/-- `M = (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)`. -/
def ceM : PairSeq := [(0, 0), (1, 1), (2, 2), (3, 1), (4, 0), (5, 1), (6, 2)]

/-- `N = M⟦3⟧ = (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,1)(7,1)`. -/
def ceN : PairSeq := [(0, 0), (1, 1), (2, 2), (3, 1), (4, 0), (5, 1), (6, 1), (7, 1)]

theorem ce_M_eq : ceM = (ceG ++ (((3 : ℕ), (1 : ℕ)) :: ceR)) ++ [(3 + 3, 1 + 1)] := by
  decide

theorem ce_N_eq : ceN = (ceG ++ (((3 : ℕ), (1 : ℕ)) :: ceR)) ++ ((3 + 3, 1) :: ceS) := by
  decide

theorem ce_R_gt : ∀ x ∈ ceR, (3 : ℕ) < x.1 := by decide

/-- The collapsed argument `S_hi` of the counterexample. -/
theorem ce_Shi : ceS.takeWhile (fun p => 3 + 3 < p.1) = [(7, 1)] := by decide

/-- `shiftr0 3 R` already pins the first two columns of the bound, for **every**
stage `m` — which is why the existential form `AscArgDom` fails too. -/
theorem ce_RHS (m : ℕ) :
    shiftr0 3 (ceR ++ copies 3 (shiftr0 3 (((3 : ℕ), (1 : ℕ)) :: ceR)) m)
      = ((7, 0) :: (8, 1) :: []) ++
          shiftr0 3 (copies 3 (shiftr0 3 (((3 : ℕ), (1 : ℕ)) :: ceR)) m) := by
  rw [shiftr0_append]
  congr 1

/-- **The conclusion of `AscArgDom(Explicit)` fails on the counterexample, at
every stage `m`.**  The very first column already goes the wrong way:
`(7,1) > (7,0)`. -/
theorem ce_not_sle (m : ℕ) :
    ¬ sle (ceS.takeWhile (fun p => 3 + 3 < p.1))
        (shiftr0 3 (ceR ++ copies 3 (shiftr0 3 (((3 : ℕ), (1 : ℕ)) :: ceR)) m)) := by
  rw [ce_Shi, ce_RHS m, List.cons_append]
  rintro (h | h)
  · exact absurd h (by simp)
  · rw [seqlex_cons_cons] at h
    rcases h with h | ⟨h, -⟩
    · exact absurd h (by unfold pairlt; simp)
    · exact absurd h (by simp)

/-! ## The refutation -/

/-- 🚨 **`AscArgDomExplicit` is FALSE.**

The two hypotheses are the `ST_PS` memberships of the counterexample; both are
pure `oper` computations along the derivations quoted in the file header
(`diag 3` then `⟦2⟧⟦2⟧⟦2⟧⟦2⟧⟦1⟧` for `ceM`, one further `⟦3⟧` for `ceN`), and
both are model-verified.  They are taken as explicit hypotheses here rather than
`sorry`d, so this file introduces no unproved claim. -/
theorem ascArgDomExplicit_false (hM : ST_PS ceM) (hN : ST_PS ceN) :
    ¬ AscArgDomExplicit := by
  intro H
  exact ce_not_sle _
    (H (G := ceG) (R := ceR) (S := ceS) (v0 := 3) (w0 := 1) (d0 := 3)
      (ce_M_eq ▸ hM) (ce_N_eq ▸ hN) ce_R_gt (by omega))

/-- 🚨 **`AscArgDom` (the existential form) is FALSE too** — no stage `m`
whatsoever repairs the counterexample, because `R ≠ []` pins the first column of
the bound to `(7,0)` independently of `m`. -/
theorem ascArgDom_false (hM : ST_PS ceM) (hN : ST_PS ceN) : ¬ AscArgDom := by
  intro H
  obtain ⟨m, hm⟩ :=
    H (G := ceG) (R := ceR) (S := ceS) (v0 := 3) (w0 := 1) (d0 := 3)
      (ce_M_eq ▸ hM) (ce_N_eq ▸ hN) ce_R_gt (by omega)
  exact ce_not_sle m hm

/-! ## The corrected statement -/

/-- **`AscArgDomExplicit` with the block root pinned.**  The extra clause says
`(v0,w0)` is the *row-1 parent* of the dropped column — exactly the
decomposition `oper` itself produces, and exactly what `oper_bad_blocks`
supplies (`oper_bad_blocks_nextrel1` below).

Model-verified: 6089 instances, **0 violations**, at closure `v ≤ 5`, `n ≤ 5`,
depth 8, length `≤ 11`. -/
def AscArgDomExplicit' : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ (v0 + d0, w0) :: S) →
    (∀ x ∈ R, v0 < x.1) → 0 < d0 →
    nextrel1 ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) G.length
      (((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]).length - 1) →
    sle (S.takeWhile fun p => v0 + d0 < p.1)
      (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R))
        (S.takeWhile fun p => v0 + d0 < p.1).length))

/-- **An equivalent-on-the-model, more convenient variant**: pin the block root
by requiring every column of the body to carry row-1 at least `w0 + 1`.  This is
precisely the fact `asc_first_column`'s docstring flags as needed-but-unproved
(`R.headI.2 ≥ w0 + 1`), strengthened to all of `R`; it makes the first-column
comparison immediate.

Model-verified: 6044 instances, **0 violations**, same closure. -/
def AscArgDomExplicitR : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ (v0 + d0, w0) :: S) →
    (∀ x ∈ R, v0 < x.1) → 0 < d0 →
    (∀ x ∈ R, w0 + 1 ≤ x.2) →
    sle (S.takeWhile fun p => v0 + d0 < p.1)
      (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R))
        (S.takeWhile fun p => v0 + d0 < p.1).length))

/-- **The corrected hypothesis is FREE.**  `oper_bad_blocks` already produces the
`nextrel1` clause in its ascending branch, so `oper_bad_blocks_all` can keep it
at no cost; this repackaging is the whole content of the fix on the upstream
side. -/
theorem oper_bad_blocks_nextrel1 {M : PairSeq} (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)) :
    ∃ (G : PairSeq) (v0 w0 : ℕ) (R : PairSeq) (d0 : ℕ) (lp : ℕ × ℕ),
      M = G ++ ((v0, w0) :: R) ++ [lp] ∧
      (∀ x ∈ R, v0 < x.1) ∧ v0 < lp.1 ∧
      ((d0 = 0 ∧ idx1 M (M.length - 1) = 0)
        ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0 ∧
            nextrel1 M G.length (M.length - 1))) := by
  obtain ⟨G, v0, w0, R, d0, lp, h1, -, h3, h4, h5, -⟩ :=
    oper_bad_blocks (n := 1) L hz hp le_rfl
  exact ⟨G, v0, w0, R, d0, lp, h1, h3, h4, h5⟩

#print axioms ce_not_sle
#print axioms ascArgDomExplicit_false
#print axioms ascArgDom_false
#print axioms oper_bad_blocks_nextrel1

end YAPSS
