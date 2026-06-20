/-
# Staging-1 de-risk (architect-wf §18.3): the cross-stratum lift `hbelow`

The sole OPEN content of door1 (Towsner ladder) is **`hbelow n`** — the
cross-stratum lift.  `accMn_within n` (Towsner.lean, GREEN) already gives
`hbelow n → (∀ t, Mn (AccBelow n) n t → Acc (oltMn (AccBelow n) n) t)`; the
within-stratum ϑ-closure (collapse direction) is closed forest-fact-FREE.

What is NOT yet proven is `hbelow n` itself:

  hbelow n : ∀ β, AccBelow n β → Acc (oltMn (AccBelow n) n) β
           = every cnf term of `cr_inv < n` is accessible IN the stratum-n order.

This is the cross-stratum lift `L_{n-1} → L_n`.  The forest fact lives here: at
stratum `n` a cr-`<n` term acquires NEW `olt`-predecessors of HIGHER `cr` that
dip below it (the collapse dip), and these must be shown accessible.

## Minimal slice (this file): `hbelow 1` = lift `L_0 → L_1`

`AccBelow 1 β = cnf β ∧ cr_inv β < 1 = cnf β ∧ cr_inv β = 0`.  At stratum 0
(`Accn_zero_of_asc`, GREEN) every cr0 term is accessible, but only against
cr0/critSub-∅ predecessors.  At stratum 1 the SAME cr0 term `P1ZZ` acquires the
new dip predecessor `P0(P1ZZ)Z` (cr1, `critSub = [P1ZZ] ⊆ AccBelow 1`), since
`olt (P0(P1ZZ)Z) (P1ZZ)` (head 0 < 1).  Killing this dip family is the de-risk:
can the PSS-concrete weapons (`core_i0`/`core_i1` ascending-copy monotonicity,
`oper_bad_blocks` copy/tile structure) show the dip's ST_PS-recover original
lives in stratum 0?

If `hbelow_one` closes by PSS-concrete means → method works, lift to general `n`.
If it does NOT → retreat to general Towsner 3.11 bar-induction full port (§18.3).
-/
import YAPSS.Towsner

namespace YAPSS
open Three

/-- **De-risk target** (architect §18.3 staging-1): the cross-stratum lift at
`n = 1`.  Every `cnf` term of `cr_inv = 0` is accessible in the stratum-1 order.
The sole new obstruction vs. stratum 0 is the collapse dip family typified by
`P0(P1ZZ)Z <o P1ZZ`. -/
theorem hbelow_one :
    ∀ β : Three, AccBelow 1 β → Acc (oltMn (AccBelow 1) 1) β := by
  sorry

/-- Derived from the GREEN `accMn_within`: full stratum-1 accessibility once the
lift `hbelow_one` is supplied.  This part is closed (modulo `hbelow_one`). -/
theorem Accn_total_one :
    ∀ t : Three, Mn (AccBelow 1) 1 t → Acc (oltMn (AccBelow 1) 1) t :=
  accMn_within 1 hbelow_one

end YAPSS
