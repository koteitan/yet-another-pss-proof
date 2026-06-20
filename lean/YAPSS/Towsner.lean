/-
# Towsner distinguished sets `M_n` / `Acc_n` (door1, M3 scaffolding)

The genuine Towsner (`2504.02131` §3.2, Def 3.7) distinguished-set ladder, ported
to the PSS term side.  **This is the correct M3 formulation** — NOT a flat
`cr_inv`-stratum induction (that is unsound: `cr_inv` is *not* `olt`-monotone on
`NF`; predecessors can rise in `cr_inv`, and the diagonal `D_v` has higher-`cr`
predecessors — verified @+5/+6/+7).  Towsner's `Acc_n` instead is the
*well-founded part* of `M_n`, and `M_n` constrains only the **critical subterms**
`K^{<0}α` (the collapse arguments), not arbitrary `olt`-predecessors.

Term-side dictionary (`architect-wf.md` §13.3, `door1-towsner-status.md`):
  * `FC(α)` (formal cardinality) ↦ the collapse-rank `cr_inv` reading: a node
    `P a b c` with `a < maxsub b` is a collapse (`ψ₀`) site.
  * `K^{<0}α` (critical subterms) ↦ `critSub t` — the argument subtrees `b` at
    collapse sites `P a b c` (`a < maxsub b`).  Each has `cr_inv b < cr_inv t`
    (`cr_inv_arg_lt_of_inv`, M1) — Towsner's `FC(β) < FC(α)`.
  * `M_n` ↦ `Mn n` : CNF terms with `cr_inv ≤ n` whose critical subterms are all
    in `⋃_{i<n} Acc_i`.
  * `Acc_n` ↦ `Accn n` : the `olt`-accessible members of `Mn n`.
  * `Acc_0` base ↦ M2 `asc` (`cr_inv = 0`, no critical subterms): `wf_oltAsc`.

The genuine `Acc_n` accessibility induction (Lemmas 3.8/3.9/3.10/3.11, Π¹₁
strength) is the residual hard core; this file fixes the definitions, proves the
critical-subterm structural facts and the `Acc_0` base, and states the induction
target precisely.
-/
import YAPSS.CollapseL0

namespace YAPSS

open Three

/-! ## Critical subterms `K^{<0}` -/

/-- The **critical subterms** `K^{<0} t`: the argument subtrees `b` occurring at a
collapse site `P a b c` (a node with `a < maxsub b`, i.e. a `cr_inv` inversion).
These are the `ψ₀`-collapse arguments; each sits at a strictly lower collapse
stratum (`cr_inv b < cr_inv t`). -/
def critSub : Three → List Three
  | Z => []
  | P a b c =>
      (if a < maxsub b then [b] else []) ++ critSub b ++ critSub c

@[simp] theorem critSub_Z : critSub Z = [] := rfl

theorem critSub_P (a : ℕ) (b c : Three) :
    critSub (P a b c) =
      (if a < maxsub b then [b] else []) ++ critSub b ++ critSub c := rfl

/-- A direct critical subterm at a collapse node is at a strictly lower stratum. -/
theorem cr_inv_critSub_lt {t : Three} {β : Three} (hβ : β ∈ critSub t) :
    cr_inv β < cr_inv t := by
  induction t with
  | Z => simp at hβ
  | P a b c ihb ihc =>
    rw [critSub_P] at hβ
    rcases List.mem_append.1 hβ with hβ' | hβc
    · rcases List.mem_append.1 hβ' with hhd | hβb
      · -- β = b at the collapse site
        by_cases hinv : a < maxsub b
        · rw [if_pos hinv] at hhd
          rcases List.mem_singleton.1 hhd with rfl
          exact cr_inv_arg_lt_of_inv hinv
        · rw [if_neg hinv] at hhd; simp at hhd
      · -- β deeper in b
        have := ihb hβb
        have hle : cr_inv b ≤ cr_inv (P a b c) := cr_inv_arg_le a b c
        omega
    · -- β deeper in c
      have := ihc hβc
      have hle : cr_inv c ≤ cr_inv (P a b c) := cr_inv_sib_le a b c
      omega

/-- A `cr_inv = 0` term has no critical subterms. -/
theorem critSub_eq_nil_of_cr_zero {t : Three} (h : cr_inv t = 0) :
    critSub t = [] := by
  induction t with
  | Z => rfl
  | P a b c ihb ihc =>
    have hb : cr_inv b = 0 := cr_inv_eq_zero_arg h
    have hc : cr_inv c = 0 := cr_inv_eq_zero_sib h
    have hnoinv : ¬ a < maxsub b := by
      have := maxsub_arg_le_head h; omega
    rw [critSub_P, if_neg hnoinv, ihb hb, ihc hc]; rfl

/-! ## The distinguished-set ladder `M_n` / `Acc_n`

`Accn` and `Mn` are defined by simultaneous recursion on the stratum index `n`:
`Mn n` references `Accn i` for `i < n`, and `Accn n` is the accessible part of
`Mn n`.  In Lean we break the recursion by defining `Accn` first via strong
recursion on `n`, with `Mn` inlined. -/

/-- `Mn accLow n t`: `t` is a CNF term of collapse-rank `≤ n` all of whose
critical subterms are accessible at a strictly lower stratum.  `accLow β` is the
"`β` is accessible at some stratum `< n`" predicate, supplied to break the mutual
recursion between `M_n` and `Acc_n`. -/
def Mn (accLow : Three → Prop) (n : ℕ) (t : Three) : Prop :=
  cnf t ∧ cr_inv t ≤ n ∧ ∀ β ∈ critSub t, accLow β

/-- The stratum-`n` order: `olt` restricted to `Mn accLow n`. -/
def oltMn (accLow : Three → Prop) (n : ℕ) (s t : Three) : Prop :=
  s <o t ∧ Mn accLow n s ∧ Mn accLow n t

/-- `Accn n t`: `t` is in the well-founded part of `M_n` — accessible under the
stratum-`n` order, where the lower strata `⋃_{i<n} Accn i` are supplied
recursively.  Defined by strong recursion on `n`: the recursor `rec` supplies
`Accn i` for every `i < n` as `rec i (proof i < n)`. -/
def Accn : ℕ → Three → Prop :=
  fun n => Nat.strongRecOn' n fun n rec t =>
    Acc (oltMn (fun β => ∃ i, ∃ h : i < n, rec i h β) n) t

/-- The `accLow` predicate used inside `Accn n`: membership in some lower stratum. -/
def AccBelow (n : ℕ) (β : Three) : Prop := ∃ i, ∃ _ : i < n, Accn i β

theorem AccBelow_iff (n : ℕ) (β : Three) : AccBelow n β ↔ ∃ i < n, Accn i β := by
  unfold AccBelow; exact ⟨fun ⟨i, h, ha⟩ => ⟨i, h, ha⟩, fun ⟨i, h, ha⟩ => ⟨i, h, ha⟩⟩

/-- **Unfolding** `Accn n`: it is `Acc` of the stratum-`n` order whose
critical-subterm side-condition references the lower strata `AccBelow n`. -/
theorem Accn_eq (n : ℕ) (t : Three) :
    Accn n t = Acc (oltMn (AccBelow n) n) t := by
  unfold Accn
  rw [Nat.strongRecOn'_beta]
  rfl

/-! ## The `Acc_0` base: `Accn 0 = asc`-accessibility (from M2) -/

/-- At stratum `0` there are no lower strata, so the side-condition
`∀ β ∈ critSub t, AccBelow 0 β` forces `critSub t = []`, i.e. `cr_inv t = 0`.
Hence `Mn (AccBelow 0) 0 = asc`. -/
theorem Mn_zero_iff (t : Three) : Mn (AccBelow 0) 0 t ↔ asc t := by
  constructor
  · rintro ⟨hcnf, hcr, _⟩
    exact ⟨hcnf, Nat.le_zero.1 hcr⟩
  · rintro ⟨hcnf, hcr⟩
    refine ⟨hcnf, hcr.le, ?_⟩
    intro β hβ
    rw [critSub_eq_nil_of_cr_zero hcr] at hβ
    simp at hβ

/-- The stratum-`0` order coincides with `oltAsc`. -/
theorem oltMn_zero (s t : Three) : oltMn (AccBelow 0) 0 s t ↔ oltAsc s t := by
  unfold oltMn oltAsc
  rw [Mn_zero_iff, Mn_zero_iff]

/-- **`Acc_0` base**: every `asc` (`cr_inv = 0`) term is in `Accn 0` — the M2
distinguished-set accessibility is exactly the bottom of the Towsner ladder. -/
theorem Accn_zero_of_asc {t : Three} (ht : asc t) : Accn 0 t := by
  rw [Accn_eq]
  have hrel : oltMn (AccBelow 0) 0 = oltAsc := by
    funext s t; exact propext (oltMn_zero s t)
  rw [hrel]
  exact ascAcc ht

/-- Conversely, an element of `Accn 0` is `asc`-accessible. -/
theorem asc_acc_of_Accn_zero {t : Three} (h : Accn 0 t) : Acc oltAsc t := by
  rw [Accn_eq] at h
  have hrel : oltMn (AccBelow 0) 0 = oltAsc := by
    funext s t; exact propext (oltMn_zero s t)
  rwa [hrel] at h

end YAPSS
