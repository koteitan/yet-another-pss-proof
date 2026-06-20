/-
# Collapse rank `cr_inv` — the Towsner FC/G stratifier (door1, M1)

This file defines the **structural collapse-rank** `cr_inv : Three → ℕ`, the
term-side analogue of Towsner's ground/collapse-rank (`2504.02131` §3.1–3.2).
It is the de-risked POSITIVE stratifier for the distinguished-set route to
`WF(olt on ST_PS)` (architect-wf.md §13–14): unlike `maxsub` (which is
collapse-invariant, `maxsub (P 0 (P 1 …) …) = maxsub (P 1 …)`), `cr_inv`
*moves* across a `ψ₀`-collapse and so distinguishes the `olt` dip-recover.

A node `P a b c` is a **collapse inversion** when its argument subtree carries a
subscript strictly greater than the head subscript `a`, i.e. `a < maxsub b`
("the argument rises above the head" = a `ψ₀` collapse).  `cr_inv t` is the
maximal nesting depth of such inversions along the argument direction, taking
the sibling sum into account by `max`.

`cr_inv` is **`olt`-independent** (it reads subscripts only, never calls `olt`),
so using it as a stratifier for an `olt`-WF argument is non-circular.

The exact definition is model-verified against `tools/probe_collapse_rank.py`
and `tools/probe_collapse_rank2.py` (closure +5/+6/+7):
  * the Python `cr_inv` is `max(inv_here + cr_inv b, cr_inv c)` with
    `inv_here = if b ≠ () ∧ maxsub b > a then 1 else 0`; in Lean the guard
    `b ≠ Z` is subsumed by `a < maxsub b` because `maxsub Z = 0 ≤ a`.
-/
import YAPSS.Wf

namespace YAPSS

open Three

/-! ## Definition -/

/-- A node `P a b c` is a **collapse inversion** when the argument subtree `b`
contains a subscript strictly above the head subscript `a` (`a < maxsub b`).
This is exactly `ψ₀`-collapse: the argument rises above the head.  Note `b = Z`
gives `maxsub b = 0 ≤ a`, so `Z`-arguments are never inversions. -/
def isInv (a : ℕ) (b : Three) : Prop := a < maxsub b

instance (a : ℕ) (b : Three) : Decidable (isInv a b) := by
  unfold isInv; infer_instance

/-- The **collapse rank**: the maximal nesting depth of collapse inversions
along the argument direction, `max`-combined with the sibling sum.  Towsner
ground/collapse-rank analogue; `olt`-independent (subscripts only). -/
def cr_inv : Three → ℕ
  | Z => 0
  | P a b c =>
      max ((if a < maxsub b then 1 else 0) + cr_inv b) (cr_inv c)

@[simp] theorem cr_inv_Z : cr_inv Z = 0 := rfl

@[simp] theorem cr_inv_P (a : ℕ) (b c : Three) :
    cr_inv (P a b c) =
      max ((if a < maxsub b then 1 else 0) + cr_inv b) (cr_inv c) := rfl

/-- The list of all principal nodes `P a b c` occurring as subterms of `t`
(including `t` itself when `t = P …`).  Used to state the `cr_inv = 0`
characterisation. -/
def subnodes : Three → List Three
  | Z => []
  | P a b c => P a b c :: subnodes b ++ subnodes c

@[simp] theorem subnodes_Z : subnodes Z = [] := rfl

@[simp] theorem subnodes_P (a : ℕ) (b c : Three) :
    subnodes (P a b c) = P a b c :: subnodes b ++ subnodes c := rfl

/-! ## Basic properties -/

/-- `cr_inv` of the argument is bounded by `cr_inv` of the node. -/
theorem cr_inv_arg_le (a : ℕ) (b c : Three) : cr_inv b ≤ cr_inv (P a b c) := by
  simp only [cr_inv_P]
  have : cr_inv b ≤ (if a < maxsub b then 1 else 0) + cr_inv b := by omega
  omega

/-- `cr_inv` of the sibling sum is bounded by `cr_inv` of the node. -/
theorem cr_inv_sib_le (a : ℕ) (b c : Three) : cr_inv c ≤ cr_inv (P a b c) := by
  simp only [cr_inv_P]; omega

/-- Across a genuine collapse inversion the argument's rank drops strictly:
`cr_inv b < cr_inv (P a b c)` when `a < maxsub b`.  This is the "critical
subterm sits at a strictly lower collapse-stratum" fact (Towsner `K^{<0}`,
probe `cr_inv UP at dip` = the reverse direction from the smaller tree). -/
theorem cr_inv_arg_lt_of_inv {a : ℕ} {b c : Three} (h : a < maxsub b) :
    cr_inv b < cr_inv (P a b c) := by
  simp only [cr_inv_P, h, if_true]
  omega

/-- `cr_inv t = 0` iff `t` carries **no** collapse inversion anywhere (a
predicative / ascending term).  Forward direction: no node `P a b c` reachable
has `a < maxsub b`.  This is the `L₀`/`wf_olt0` base characterisation. -/
theorem cr_inv_eq_zero_iff (t : Three) :
    cr_inv t = 0 ↔ ∀ a b c, P a b c ∈ subnodes t → ¬ a < maxsub b := by
  induction t with
  | Z => simp [subnodes]
  | P a b c ihb ihc =>
    simp only [cr_inv_P]
    constructor
    · intro hmax a' b' c' hmem hinv
      have h1 : (if a < maxsub b then 1 else 0) + cr_inv b = 0 := by omega
      have h2 : cr_inv c = 0 := by omega
      rw [subnodes_P] at hmem
      rcases List.mem_cons.1 hmem with heq | hmemr
      · obtain ⟨rfl, rfl, rfl⟩ := Three.P.inj heq
        rw [if_pos hinv] at h1; omega
      · rcases List.mem_append.1 hmemr with hmemb | hmemc
        · have : cr_inv b = 0 := by omega
          exact (ihb.1 this) a' b' c' hmemb hinv
        · exact (ihc.1 h2) a' b' c' hmemc hinv
    · intro h
      have hb0 : cr_inv b = 0 := ihb.2 fun a' b' c' hm => h a' b' c'
        (by rw [subnodes_P]; exact List.mem_cons_of_mem _
              (List.mem_append.2 (Or.inl hm)))
      have hc0 : cr_inv c = 0 := ihc.2 fun a' b' c' hm => h a' b' c'
        (by rw [subnodes_P]; exact List.mem_cons_of_mem _
              (List.mem_append.2 (Or.inr hm)))
      have hnotinv : ¬ a < maxsub b :=
        h a b c (by rw [subnodes_P]; exact List.mem_cons_self ..)
      rw [if_neg hnotinv, hb0, hc0]; omega

/-! ## Well-foundedness of the `cr_inv` ℕ-measure

`cr_inv` is a `ℕ`-valued measure, hence `InvImage (· < ·) cr_inv` is
well-founded on `Three` (the strata `{t | cr_inv t = n}` form a `WF` ladder).
This is the well-foundedness needed to run the distinguished-set induction
`Acc_n ⟹ Acc_{n+1}` (M3) by induction on the stratum index. -/

/-- The `cr_inv` ℕ-measure relation: `t ≺ s` iff `cr_inv t < cr_inv s`. -/
def crLt (t s : Three) : Prop := cr_inv t < cr_inv s

theorem wf_crLt : WellFounded crLt :=
  InvImage.wf cr_inv (Nat.lt_wfRel.wf)

end YAPSS
