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

/-! ## `M_n` closure under summands (toward Lemma 3.8)

The critical subterms of a summand `P a b Z` of `t` are critical subterms of `t`,
and `cr_inv (P a b Z) ≤ cr_inv t`.  Hence `Mn accLow n` is closed under taking
summands — the prerequisite for the Dershowitz–Manna `sum_acc` step. -/

/-- The critical subterms of a summand of `t` are critical subterms of `t`. -/
theorem critSub_summands {t : Three} {s : Three} (hs : s ∈ summands t) :
    ∀ β ∈ critSub s, β ∈ critSub t := by
  induction t with
  | Z => simp at hs
  | P a b c ihb ihc =>
    rw [summands_P] at hs
    rcases List.mem_cons.1 hs with rfl | hs
    · -- s = P a b Z : critSub (P a b Z) = (if a<maxsub b then [b]) ++ critSub b ++ []
      intro β hβ
      rw [critSub_P, critSub_Z, List.append_nil] at hβ
      rw [critSub_P]
      rcases List.mem_append.1 hβ with h1 | h2
      · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl h1)))
      · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr h2)))
    · intro β hβ
      rw [critSub_P]
      exact List.mem_append.2 (Or.inr (ihc hs β hβ))

/-- `cr_inv` of a summand is bounded by `cr_inv` of the term. -/
theorem cr_inv_summand_le {t : Three} {s : Three} (hs : s ∈ summands t) :
    cr_inv s ≤ cr_inv t := by
  induction t with
  | Z => simp at hs
  | P a b c ihb ihc =>
    rw [summands_P] at hs
    rcases List.mem_cons.1 hs with rfl | hs
    · -- s = P a b Z
      simp only [cr_inv_P, cr_inv_Z]
      have : cr_inv (P a b c) =
          max ((if a < maxsub b then 1 else 0) + cr_inv b) (cr_inv c) := cr_inv_P a b c
      omega
    · exact le_trans (ihc hs) (cr_inv_sib_le a b c)

/-- `Mn accLow n` is closed under taking summands. -/
theorem Mn_summands {accLow : Three → Prop} {n : ℕ} {t : Three}
    (ht : Mn accLow n t) : ∀ s ∈ summands t, Mn accLow n s := by
  rintro s hs
  obtain ⟨hcnf, hcr, hcrit⟩ := ht
  refine ⟨cnf_summands hcnf hs, le_trans (cr_inv_summand_le hs) hcr, ?_⟩
  intro β hβ
  exact hcrit β (critSub_summands hs β hβ)

/-! ## Stratified Dershowitz–Manna `sum_acc` (Lemma 3.8, `#`-closure) -/

theorem transp_oltMn (accLow : Three → Prop) (n : ℕ) :
    ∀ ⦃a b c⦄, oltMn accLow n a b → oltMn accLow n b c → oltMn accLow n a c :=
  fun _ _ _ h1 h2 => ⟨olt_trans h1.1 h2.1, h1.2.1, h2.2.2⟩

theorem oltMn_summands_dmlt {accLow : Three → Prop} {n : ℕ} {w t : Three}
    (h : oltMn accLow n w t) :
    DMLT (oltMn accLow n) ↑(summands w) ↑(summands t) := by
  obtain ⟨wt, lw, lt'⟩ := h
  have base : DMLT (oltOn {s | Mn accLow n s}) ↑(summands w) ↑(summands t) :=
    olt_summands_mult lw.1 wt (Mn_summands lw) (Mn_summands lt')
  exact base.mono fun a b ⟨hab, ha, hb⟩ => ⟨hab, ha, hb⟩

/-- A sum is `oltMn`-accessible once its summand multiset is `DMLT`-accessible
(Lemma 3.8 closure under the sum constructor `#`). -/
theorem sum_accMn {accLow : Three → Prop} {n : ℕ} {v : Three}
    (lv : Mn accLow n v)
    (hacc : Acc (DMLT (oltMn accLow n)) (↑(summands v) : Multiset Three)) :
    Acc (oltMn accLow n) v := by
  have aux : ∀ M : Multiset Three, Acc (DMLT (oltMn accLow n)) M →
      ∀ w, Mn accLow n w → ↑(summands w) = M → Acc (oltMn accLow n) w := by
    intro M hM
    induction hM with
    | intro M _ ih =>
      intro w lw hw
      refine Acc.intro w fun v hv => ?_
      have lv' : Mn accLow n v := hv.2.1
      have step : DMLT (oltMn accLow n) ↑(summands v) M :=
        hw ▸ oltMn_summands_dmlt hv
      exact ih _ step v lv' rfl
  exact aux _ hacc v lv rfl

/-! ## `M_n` closure under arguments

For the stratified singleton step we need: the argument `d'` of an `Mn`-principal
`P a' d' Z` is itself in `Mn`.  Its critical subterms are critical subterms of the
principal (`critSub d' ⊆ critSub (P a' d' Z)`), and `cr_inv d' ≤ cr_inv (P a' d' Z)`. -/

/-- The critical subterms of the argument `b` are critical subterms of `P a b Z`. -/
theorem critSub_arg_subset (a : ℕ) (b : Three) :
    ∀ β ∈ critSub b, β ∈ critSub (P a b Z) := by
  intro β hβ
  rw [critSub_P, critSub_Z, List.append_nil]
  exact List.mem_append.2 (Or.inr hβ)

/-- `Mn accLow n` is closed under taking the argument of a single principal. -/
theorem Mn_arg {accLow : Three → Prop} {n : ℕ} {a : ℕ} {b : Three}
    (h : Mn accLow n (P a b Z)) : Mn accLow n b := by
  obtain ⟨hcnf, hcr, hcrit⟩ := h
  refine ⟨cnf_P_Z.1 hcnf, le_trans (cr_inv_arg_le a b Z) hcr, ?_⟩
  intro β hβ
  exact hcrit β (critSub_arg_subset a b β hβ)

/-! ## Stratified singleton step (Lemma 3.10, `ϑ`-accessibility)

A single principal `P a b Z ∈ Mn accLow n` is `oltMn`-accessible once its
argument `b` is, PROVIDED every strictly-smaller-head `Mn`-predecessor is already
accessible (`hlow`).  Model-verified (probe_m3_*): for the NF singletons (all
head-0) `hlow` is **vacuous** (no `a' < 0`), and the in-stratum predecessors are
arg-drops (`a' = a`, `b' <o b`) handled by the accessibility induction on `b`. -/

/-- Every summand of an `oltMn`-predecessor `v` of `P a b Z` is `<o P a b Z`. -/
theorem summand_lt_of_predMn {accLow : Three → Prop} {n a : ℕ} {b v : Three}
    (cv : cnf v) (vlt : v <o P a b Z) {s : Three} (hs : s ∈ summands v) :
    s <o P a b Z :=
  summand_lt_of_pred cv vlt hs

/-- The stratified singleton step.  `hlow` supplies accessibility of any
strictly-smaller-head `Mn`-predecessor; `hb` is the (lower-stratum) accessibility
of the argument `b`; the conclusion is accessibility of `P a b Z`. -/
theorem sing_accMn {accLow : Three → Prop} {n a : ℕ}
    (hlow : ∀ a' < a, ∀ d : Three, Mn accLow n (P a' d Z) →
      Acc (oltMn accLow n) (P a' d Z))
    {b : Three} (hb : Acc (oltMn accLow n) b) (lb : Mn accLow n (P a b Z)) :
    Acc (oltMn accLow n) (P a b Z) := by
  induction hb with
  | intro b _ ih =>
    refine Acc.intro _ fun v hv => ?_
    obtain ⟨vlt, lv, _⟩ := hv
    have summacc : ∀ s ∈ (↑(summands v) : Multiset Three),
        Acc (oltMn accLow n) s := by
      intro s hs
      have sv : s ∈ summands v := by simpa using hs
      obtain ⟨a', d', he, hd'⟩ := summands_sargs sv
      have ls : Mn accLow n s := Mn_summands lv s sv
      have lsP : Mn accLow n (P a' d' Z) := he ▸ ls
      have slt : s <o P a b Z := summand_lt_of_pred lv.1 vlt sv
      have hsP : P a' d' Z <o P a b Z := he ▸ slt
      rw [he]
      rcases olt_P_P.1 hsP with hlt | ⟨heq, hdb⟩ | ⟨heq, _, hz⟩
      · exact hlow a' hlt d' lsP
      · subst heq
        have lbArg : Mn accLow n b := Mn_arg lb
        have ld' : Mn accLow n d' := Mn_arg lsP
        exact ih d' ⟨hdb, ld', lbArg⟩ lsP
      · exact absurd hz (not_olt_Z _)
    exact sum_accMn lv (acc_dmlt_of_acc (transp_oltMn accLow n) summacc)

/-! ## The stratum step `Acc_n` (toward Lemma 3.10 + composition)

The main accessibility: a term in `Mn (AccBelow n) n` is `oltMn`-accessible.
The lower strata `AccBelow n` are accessible by the outer stratum induction; the
within-stratum structure is closed by `sum_accMn` (DM on summands) and
`sing_accMn` (arg-induction on a principal).

The genuine remaining obligations are: (i) the singleton `hlow` (smaller-head
predecessors) — for the head-`0` target this is **vacuous** (no `a' < 0`); (ii)
the arg accessibility `Acc (oltMn n) b` for a critical (collapse) arg `b` — `b ∈
AccBelow n` gives `Accn m b` at a lower stratum `m`, which must be **lifted** to
`oltMn n` accessibility.  The lift is where the head-drop predecessors (`lead v <
lead b`, all in lower strata or `hlow`-covered) are absorbed. -/

/-- The head-`0` instantiation of the singleton `hlow`: vacuously true, since no
predecessor head `a' < 0` exists. -/
theorem sing_accMn_head0 {accLow : Three → Prop} {n : ℕ}
    {b : Three} (hb : Acc (oltMn accLow n) b) (lb : Mn accLow n (P 0 b Z)) :
    Acc (oltMn accLow n) (P 0 b Z) :=
  sing_accMn (fun a' ha' _ _ => absurd ha' (Nat.not_lt_zero a')) hb lb

end YAPSS
