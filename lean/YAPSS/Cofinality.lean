/-
# PSS Bachmann cofinality — the load-bearing statement of the W_u transplant

## Why this file exists (2026-07-24 route change)

`pss-proof` produced an **ordinal-free SYNTACTIC** well-foundedness proof of
Buchholz `OT_B` (sorry-free, named-assumption-free) whose engine is

    Bachmann cofinality  +  the iterated inductive set `W_u` (least fixpoint of `A_u`)

instead of the ordinal evaluation map.  That **falsifies the premise** on which this
project's previous terminal rested — namely that `wf_olt_wf3` (via `oV`/`wf3`) is the
only WF certificate for `olt`, whence `wf3`-membership (= the open `H0clause`) was
"unavoidable".  It is not: there is a second, ordinal-free certificate.

Two further points make this genuinely new rather than a 14th bypass:

* every induction axis this project exhausted (term-local, column-local, forest-LEVEL,
  row-1, oper-derivation, per-level, forest-ancestor) is a **structural** induction, and
  each died the same way — the carrier breaks at an *intermediate node*.  The `W_u`
  least-fixpoint induction is **not structural**: it descends the **fundamental
  sequence** (`oper`, i.e. `M⟦n⟧`) and never visits those intermediate nodes.
* PSS standard forms are **not** Buchholz `OT` terms (bypass #7: `translate (diagSeq 0 2)`
  fails OT3), so the source proof cannot be imported — it must be redone natively.  In
  the source, the coefficient-domination (G) condition is *free* precisely because
  `isOT_BT` is **defined** by it; natively it is not free, which is why we route around
  it via cofinality instead.

## The statement (model-verified TRUE)

`tools/probe_pss_cofinality.py`: **0 violations** over 5778 / 19503 / 79003 pairs at
closure +5/+6/+7 on the `row1 ≤ 1` ST_PS fragment, and non-degenerate (every host has
genuine `M⟦n⟧ ≠ M` expansions; excluding the degenerate case still gives 0 violations).
Re-checked with `n ≥ 1` only (which `ST_PS.oper` requires): still 0 violations.

Crucially the statement **never mentions `Gterm` / coefficient domination**, so it is a
genuinely different obligation from `H0clause_oper_step`.

## Intended assembly

    pss_cofinality  +  (A/W least-fixpoint induction, mirroring the source)
        ⟹  WF (olt on ST_PS images)
        ⟹  PSS termination            (the decrease `m_step_decreases` is already GREEN)

## Where the proof should come from

The GREEN PSS-concrete assets are exactly the right shape here, because they relate an
**expansion to its original** (unlike the cross-level order-lift, where their domain was
empty):  `oper_bad_blocks` (Mechanized.lean:836, the oper copy/tile decomposition),
`core_i0` (:714) and `core_i1` (:737) (ascending-copy domination), together with
`translate_shift`, `translate_take_le`, `translate_append_ge` (Gterm0Olt.lean).
-/
import YAPSS.Mechanized
import YAPSS.Gterm0Olt

namespace YAPSS
open Three

/-- **PSS Bachmann cofinality** (the load-bearing statement of the ordinal-free route).

Every standard form strictly `olt`-below `M` is bounded by some expansion of `M`:
the fundamental sequence `M⟦·⟧` is cofinal below `M`.

Model-verified TRUE: 0 violations / 79003 pairs at closure `+5/+6/+7`, non-degenerate,
with `n ≥ 1`. -/
theorem pss_cofinality {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) := by
  sorry

end YAPSS
