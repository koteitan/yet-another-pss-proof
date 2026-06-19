/-
**Copy-tile seqlex domination** — the single-step load-bearing unit of the
global copy-tiling seqlex invariant (architecture option (i) for the residual
`Wttone.H0clause_oper_step`).

The `oper` bad-block expansion presents `M⟦n⟧ = G ++ body ++ C` and
`M = G ++ body ++ [lp]`, where `body = (v0,w0) :: R` is the copied block, `C`
is the concatenation of the tail copies (copy indices `k = 1 .. n-1`, the
`k`-th shifted by `(k*d0, 0)` in row-0 only — row-1 is periodic), and `lp` is
the dropped last pair.  `oper_bad_blocks` guarantees the disjunction

    hdisj :  (d0 = 0) ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0)

(plus `v0 < lp.1`).  This file proves the **seqlex form** of the domination

    seqlex (body ++ C) (body ++ [lp])

which is the column-lex statement underlying `core_i0` / `core_i1`
(`Mechanized.lean`).  Stating it directly in `seqlex` (a purely syntactic
predicate on pair-sequences) avoids the `translate` round-trip and is the
reusable unit fed into the SubBlock / `seqlex_imp_olt` route to the residual.

Model-verified 0-viol at closure +5/+6/+7 over the ST_PS row-1≤1 fragment, and
the `hdisj` hypothesis is load-bearing (`tools/probe_arch_global_inv.py`,
STEP A).
-/
import YAPSS.Seqlex

namespace YAPSS

open Three

/-- The head of the first tail copy `c = (v0 + d0, w0)` strictly `pairlt`-precedes
the dropped last pair `lp`, under the `oper_bad_blocks` disjunction.

* `d0 = 0` (exact copies): `c.1 = v0 < lp.1` (first `pairlt` disjunct).
* `0 < d0` (ascending copies): `c.1 = v0 + d0 = lp.1` and `c.2 = w0 < lp.2`
  (second `pairlt` disjunct). -/
theorem pairlt_firstcopy_lp {v0 w0 d0 : ℕ} {lp : ℕ × ℕ}
    (vl : v0 < lp.1)
    (hdisj : (d0 = 0) ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0)) :
    pairlt (v0 + d0, w0) lp := by
  rcases hdisj with hd0 | ⟨_, w0lt, lpfst⟩
  · -- exact copies: row-0 strictly smaller
    left
    simp [hd0]; exact vl
  · -- ascending copies: row-0 equal, row-1 strictly smaller
    right
    refine ⟨?_, ?_⟩
    · simp; omega
    · simpa using w0lt

/-- **Copy-tile seqlex domination (seqlex form of `core_i0` / `core_i1`).**

The tail-copy concatenation `C` (any pair-sequence whose head is the first
copy head `(v0 + d0, w0)`) prepended-common-body-cancelled is `seqlex`-below
the body extended by the dropped last pair `lp`.  Reduces by
`seqlex_append_cancel` to `seqlex C [lp]`, then to `pairlt (head C) lp`. -/
theorem copy_tile_seqlex {v0 w0 d0 : ℕ} {C' : PairSeq} {lp : ℕ × ℕ}
    (body : PairSeq)
    (vl : v0 < lp.1)
    (hdisj : (d0 = 0) ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0)) :
    seqlex (body ++ ((v0 + d0, w0) :: C')) (body ++ [lp]) := by
  rw [seqlex_append_cancel]
  -- `seqlex ((v0+d0,w0) :: C') [lp]` : the head `pairlt`s `lp`
  rw [seqlex_cons_cons]
  exact Or.inl (pairlt_firstcopy_lp vl hdisj)

/-- **Degenerate `n = 1` case** (no tail copies): the bare body is `seqlex`-below
the body extended by `lp` — a pure prefix fact (`seqlex_prefix`). -/
theorem copy_tile_seqlex_nil (body : PairSeq) (lp : ℕ × ℕ) :
    seqlex body (body ++ [lp]) :=
  seqlex_prefix (by simp) body

end YAPSS
