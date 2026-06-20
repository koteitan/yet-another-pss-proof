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

## DE-RISK VERDICT (2026-06-20, staging1 agent): STALLED — domain mismatch

`hbelow_one` reduces (GREEN, `sing_accMn`) to `hbelow_one_dip`, whose sole hard
case sends `Acc(dip P0(P1ZZ)Z)` to `Acc(collapse-arg P1ZZ)`.  But `P1ZZ` has
HEAD 1, and `head_eq_zero_of_NF` ⇒ every NF principal is head-0, so `P1ZZ ∉ NF`:
there is NO `M : PairSeq` with `translate M = P1ZZ`.  The PSS-concrete weapons
(`core_i0`/`core_i1`/`oper_bad_blocks`, `Gterm_translate_subblock`) ALL require a
`translate`/`SubBlock` of an ST_PS sequence as input — their domain here is EMPTY.
So PSS weapons are structurally confined to the head-0 NF fragment, while this
obligation lives on head-≠0 `cnf` terms: `cnf ⊋ NF` exactly along the head
subscript.  ⇒ no PSS-concrete route closes the cnf-level slice.

## REFINEMENT (main, not yet built): NF-restrict the ladder, unify with H0clause

The cnf-level `Mn` is OVER-GENERAL: the GOAL is `WF(olt on NF)` only (Rnf), so we
never need `Acc` of off-NF terms like `P1ZZ`.  Restricting `Mn`/`AccBelow`/`oltMn`
to NF (head-0, ST_PS-reachable) (1) matches the goal and (2) aligns the ladder's
domain with the PSS weapons' domain.  This does NOT eliminate the core (dips
persist on NF — `cr_inv` is not olt-monotone on NF, D_v @+5/+6/+7), but it
COLLAPSES door1's residual onto the SAME H0clause forest-reachability fact rather
than a separate cnf-level general-Towsner port (the agent's recommendation, now
seen as redundant).  ⇒ all three faces (H0clause / door1-NF / door2) converge on
ONE multi-week ST_PS forest build; H0clause is the most isolated face to build.
-/
import YAPSS.Towsner

namespace YAPSS
open Three

/-- **The cr1 collapse-dip obligation** — the genuine non-predicative core of
`hbelow_one`, isolated.  Given an `asc` (cr0) term `β` accessible in the
stratum-0 order, and a predecessor `s <o β` that is a *cr1 dip* (`cr_inv s = 1`,
`Mn (AccBelow 1) 1 s`), show `s` is accessible in the stratum-1 order.  The
typifying instance is `s = P0(P1ZZ)Z <o β = P1ZZ` whose unique collapse argument
`P1ZZ` is `β` itself — so `s`'s accessibility demands `β`'s, which is the very
thing being constructed at the enclosing `Acc.intro β`.  This is the impredicative
loop; no elementary measure breaks it (cr increases 0→1, tsize increases 2→4,
only `lead` drops 1→0, and the witnessing inequality is the ordinal collapse
`ψ₀(ψ₁0) < ψ₁0`).  See report for why PSS-concrete weapons do not reach it. -/
theorem hbelow_one_dip
    (β : Three) (hasc : asc β)
    (ih : ∀ s, oltAsc s β → asc s → Acc (oltMn (AccBelow 1) 1) s)
    (s : Three) (hsβ : s <o β)
    (hMs : Mn (AccBelow 1) 1 s) (hscr1 : cr_inv s = 1) :
    Acc (oltMn (AccBelow 1) 1) s := by
  sorry

theorem hbelow_one :
    ∀ β : Three, AccBelow 1 β → Acc (oltMn (AccBelow 1) 1) β := by
  -- Reduce to stratum-0 accessibility of `β` (`ascAcc`) and induct on it.  The
  -- cr0 predecessors close by the induction hypothesis (they are `oltAsc`-below
  -- `β`); the *only* irreducible case is the cr1 dip, isolated in
  -- `hbelow_one_dip`.
  have aux : ∀ β : Three, Acc oltAsc β → asc β →
      Acc (oltMn (AccBelow 1) 1) β := by
    intro β hAcc
    induction hAcc with
    | intro β _ ih =>
      intro hasc
      refine Acc.intro β fun s hs => ?_
      obtain ⟨hsβ, hMs, _hMβ⟩ := hs
      by_cases hscr : cr_inv s = 0
      · -- cr0 predecessor: `oltAsc s β`, handled by the stratum-0 IH.
        have hsasc : asc s := ⟨hMs.1, hscr⟩
        exact ih s ⟨hsβ, hsasc, hasc⟩ hsasc
      · -- cr1 dip: `Mn` gives `cr_inv s ≤ 1`, with `cr_inv s ≠ 0` ⇒ `= 1`.
        have hscr1 : cr_inv s = 1 := by
          have hle : cr_inv s ≤ 1 := hMs.2.1
          omega
        exact hbelow_one_dip β hasc
          (fun s hso hs' => ih s hso hs') s hsβ hMs hscr1
  intro β hβ
  obtain ⟨hcnf, hcr⟩ := hβ
  have hcr0 : cr_inv β = 0 := Nat.lt_one_iff.1 hcr
  exact aux β (ascAcc ⟨hcnf, hcr0⟩) ⟨hcnf, hcr0⟩

/-- Derived from the GREEN `accMn_within`: full stratum-1 accessibility once the
lift `hbelow_one` is supplied.  This part is closed (modulo `hbelow_one`). -/
theorem Accn_total_one :
    ∀ t : Three, Mn (AccBelow 1) 1 t → Acc (oltMn (AccBelow 1) 1) t :=
  accMn_within 1 hbelow_one

end YAPSS
