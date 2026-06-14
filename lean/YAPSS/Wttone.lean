/-
**The `maxr1 ≤ 1` level of the `W = T` route** (one level above
`Wttbase.lean`).  RESEARCH frontier: the Isabelle peer `ya-pss` has only the
`maxr1 = 0` base (`ord/wttbase.thy`); this level is new.

**Empirical anchor (verified on 2 494 996 standard forms / 137 754 259 OT3
checks, 0 violations).**  A standard form all of whose row-1 entries are `≤ 1`
translates to a *genuine Buchholz OT term* (`wf3`).  The re-ascent crux lives
strictly at `maxr1 ≥ 2`: the smallest violator is `diagSeq 0 2 =
(0,0)(1,1)(2,2)`, whose translate `p₀(p₁(p₂(0)))` already fails OT3.

Structure of the proof, and where the residual sits:
  * `subs (translate M) ⊆ {0,1}` (from `subs_translate` + the row-1 bound)
    plus `cnf` (`cnf_ST_PS`) give every prerequisite of `wf3` EXCEPT the OT3
    clause `∀ x ∈ Gterm a b, olt x b` at each principal `P a b c`.
  * OT3 splits on the head subscript `a ∈ {0,1}` (`subs_P_head01`).
      - **`a = 1`** (head = maximal subscript): FULLY PROVED (`OT3all1_head1`),
        via `olt_arg_principal1` and `olt_tail_of_cnf`.
      - **`a = 0`**: the genuine crux.  The clean term-level half is
        `OT3all0_okH` (FULLY PROVED): with the hereditary discipline `okH`
        ("a head-`0` principal's argument leads with `0`"), the head-`0` clause
        follows by the same argument as `a = 1`.  But `okH` is **provably false
        on the translate image** (a head-`0` principal may carry a head-`1`
        argument, e.g. `p₀(p₁(0))`, which is OT3-valid yet `okH`-illegal): the
        SAME term shape is OT3-valid in some forest positions and invalid in
        others, and ONLY the sequence origin (`r1ok`) distinguishes them.  Term
        level cannot see this.  So the residual is genuinely the `r1ok`-forest
        bridge, isolated as the single `sorry` `H0clause_translate`, whose
        docstring records the exact remaining fact.

`OT3all0_okH`, `OT3all1_head1`, `olt_arg_principal1`, `olt_tail_of_cnf` are all
sorry-free.  `acc_subs1` composes with `acc_wf3_fragment`/`Wtt` as `acc_subs0`
does.
-/
import YAPSS.Wttbase
import YAPSS.Nrmstep

namespace YAPSS

open Three

/-! ## Subscript-`{0,1}` bookkeeping for OT terms -/

/-- A principal term with all subscripts `≤ 1` has head subscript `≤ 1`. -/
theorem subs_P_head01 {a : ℕ} {b c : Three} (h : subs (P a b c) ⊆ {0,1}) :
    a ≤ 1 := by
  have : a ∈ subs (P a b c) := by simp [subs]
  have := h this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  omega

/-- Subscript-`{0,1}` is inherited by the argument. -/
theorem subs_P_subL01 {a : ℕ} {b c : Three} (h : subs (P a b c) ⊆ {0,1}) :
    subs b ⊆ {0,1} := fun x hx => h (by simp [subs]; tauto)

/-- Subscript-`{0,1}` is inherited by the tail. -/
theorem subs_P_subR01 {a : ℕ} {b c : Three} (h : subs (P a b c) ⊆ {0,1}) :
    subs c ⊆ {0,1} := fun x hx => h (by simp [subs]; tauto)

/-! ## Two principal-domination facts (subscript-`≤ 1` / CNF) -/

/-- In a subscript-`≤ 1` term, the argument is strictly below the principal
`P 1 b c`.  Induction on `b`: leading subscript `0` dominates by subscript;
leading subscript `1` (= head) recurses on the argument. -/
theorem olt_arg_principal1 :
    ∀ {b : Three}, subs b ⊆ {0,1} → ∀ c : Three, olt b (P 1 b c) := by
  intro b
  induction b with
  | Z => intro _ c; simp
  | P f bb bc ihbb _ =>
    intro h c
    have hf : f ≤ 1 := subs_P_head01 h
    rcases Nat.lt_or_ge f 1 with hlt | hge
    · exact Or.inl (by omega)
    · have hf1 : f = 1 := by omega
      subst hf1
      exact Or.inr (Or.inl ⟨rfl, ihbb (subs_P_subL01 h) bc⟩)

/-- In any CNF principal term, the tail is strictly below the whole term.
Generalizes `olt_tail_principal0` (drops the all-`0`-subscript hypothesis):
the CNF non-domination clause `¬(P a b Z <o P e f Z)` plus `olt_total` forces
the head comparison `e ≤ a`. -/
theorem olt_tail_of_cnf :
    ∀ {a : ℕ} {b c : Three}, cnf (P a b c) → olt c (P a b c) := by
  intro a b c
  induction c generalizing a b with
  | Z => intro _; simp
  | P e f g _ ihg =>
    intro hcnf
    rw [cnf_P_P] at hcnf
    obtain ⟨_, ndom, cnfc⟩ := hcnf
    rw [olt_P_P] at ndom
    push_neg at ndom
    obtain ⟨hea, hbf_imp, _⟩ := ndom
    rcases Nat.lt_or_ge e a with hlt | hge
    · exact Or.inl hlt
    · have heq : a = e := le_antisymm hge hea
      subst heq
      rcases Three.olt_total f b with hfb | hfb | hbf
      · exact Or.inr (Or.inl ⟨rfl, hfb⟩)
      · subst hfb
        exact Or.inr (Or.inr ⟨rfl, rfl, ihg cnfc⟩)
      · exact absurd hbf (hbf_imp rfl)

/-! ## OT3 by head subscript -/

/-- **Head-`1` OT3** (the clean half).  In a subscript-`≤ 1` CNF + `wf3` term,
every coefficient in `Gterm 1 t` is strictly below `t`.  Mirror of `OT3all`:
`olt_arg_principal1` handles the argument, `olt_tail_of_cnf` the tail, the
induction hypotheses the nested coefficients, glued by `olt_trans`.  (The head
in the `insert b` branch is forced to `1` because `1 ≤ a ≤ 1`.) -/
theorem OT3all1_head1 :
    ∀ {t : Three}, cnf t → wf3 t → subs t ⊆ {0,1} → ∀ x ∈ Gterm 1 t, olt x t := by
  intro t
  induction t with
  | Z => intro _ _ _ x hx; simp [Gterm] at hx
  | P a b c ihb ihc =>
    intro hcnf hwf3 hsub x hx
    obtain ⟨wfb, wfc, _, _⟩ := (wf3_P).1 hwf3
    have subb : subs b ⊆ {0,1} := subs_P_subL01 hsub
    have subc : subs c ⊆ {0,1} := subs_P_subR01 hsub
    have tailc : olt c (P a b c) := olt_tail_of_cnf hcnf
    rw [mem_Gterm_P] at hx
    rcases hx with ⟨h1a, hxb⟩ | hxc
    · have ha : a = 1 := le_antisymm (subs_P_head01 hsub) h1a
      subst ha
      have argb : olt b (P 1 b c) := olt_arg_principal1 subb c
      rcases hxb with rfl | hxg
      · exact argb
      · exact Three.olt_trans (ihb (cnf_P_arg hcnf) wfb subb x hxg) argb
    · exact Three.olt_trans (ihc (cnf_P_tail hcnf) wfc subc x hxc) tailc

/-! ## The hereditary head-`0` discipline `okH` and the clean head-`0` OT3 -/

/-- `okH t`: hereditarily, every head-`0` principal's argument leads with `0`
(`lead b ≤ a` at every node — vacuous at head-`1` nodes since subscripts are
`≤ 1`).  This is the *exact* term-level discipline under which the head-`0` OT3
clause holds (`OT3all0_okH`).  It is FALSE on the translate image — see
`H0clause_translate` — so it is a proof device, not the image invariant. -/
def okH : Three → Prop
  | Z => True
  | P a b c => lead b ≤ a ∧ okH b ∧ okH c

@[simp] theorem okH_Z : okH Z := trivial
@[simp] theorem okH_P {a : ℕ} {b c : Three} :
    okH (P a b c) ↔ lead b ≤ a ∧ okH b ∧ okH c := Iff.rfl

/-- The argument is strictly below its own principal, given the head-`0`
discipline `lead b ≤ a`.  Induction on `b`. -/
theorem olt_arg_okH :
    ∀ {a : ℕ} {b : Three}, lead b ≤ a → okH b → ∀ c, olt b (P a b c) := by
  intro a b
  induction b with
  | Z => intro _ _ c; simp
  | P a' b' c' ihb' _ =>
    intro hlead okb c
    simp only [lead_P] at hlead
    rcases Nat.lt_or_ge a' a with h | h
    · exact Or.inl h
    · have ha' : a' = a := le_antisymm hlead h
      subst ha'
      obtain ⟨hl', okb', _⟩ := okb
      exact Or.inr (Or.inl ⟨rfl, ihb' hl' okb' c'⟩)

/-- **Head-`0` OT3 via the discipline `okH`** (FULLY PROVED).  In a CNF + `wf3`
term with `subs ⊆ {0,1}` satisfying `okH`, every coefficient in `Gterm 0 t` is
strictly below `t`.  Same shape as `OT3all1_head1`/`OT3all`: `olt_arg_okH`
handles the argument, `olt_tail_of_cnf` the tail, IH the nested coefficients,
glued by `olt_trans`. -/
theorem OT3all0_okH :
    ∀ {t : Three}, cnf t → wf3 t → subs t ⊆ {0,1} → okH t →
      ∀ x ∈ Gterm 0 t, olt x t := by
  intro t
  induction t with
  | Z => intro _ _ _ _ x hx; simp [Gterm] at hx
  | P a b c ihb ihc =>
    intro hcnf hwf3 hsub hok x hx
    obtain ⟨wfb, wfc, _, _⟩ := (wf3_P).1 hwf3
    have subb := subs_P_subL01 hsub
    have subc := subs_P_subR01 hsub
    obtain ⟨hlead, okb, okc⟩ := hok
    have argb : olt b (P a b c) := olt_arg_okH hlead okb c
    have tailc : olt c (P a b c) := olt_tail_of_cnf hcnf
    rw [mem_Gterm_P] at hx
    rcases hx with ⟨_, hxb⟩ | hxc
    · rcases hxb with rfl | hxg
      · exact argb
      · exact Three.olt_trans (ihb (cnf_P_arg hcnf) wfb subb okb x hxg) argb
    · exact Three.olt_trans (ihc (cnf_P_tail hcnf) wfc subc okc x hxc) tailc

/-! ## Assembling `wf3 (translate M)`

The head-`0` OT3 obligation cannot be discharged by any term-level lemma on
`Three`: the SAME shape (`p₀(p₁(0))`) is OT3-valid in some forest positions and
escapes `Gterm 0` in others, distinguished only by the sequence origin
(`r1ok`).  We thread it as the predicate `H0clause` ("every head-`0` principal
meets its OT3 clause"), prove `H0clause t → wf3 t` together with the rest, and
discharge `H0clause (translate M)` from the image as the single residual. -/

/-- `H0clause t`: at every head-`0` principal `P 0 b c` occurring in `t`, the
OT3 clause `∀ x ∈ Gterm 0 b, olt x b` holds.  (At head-`1` nodes nothing is
required here — that case is `OT3all1_head1`.)  Hereditary by construction. -/
def H0clause : Three → Prop
  | Z => True
  | P a b c =>
      (a = 0 → ∀ x ∈ Gterm 0 b, olt x b) ∧ H0clause b ∧ H0clause c

@[simp] theorem H0clause_Z : H0clause Z := trivial
@[simp] theorem H0clause_P {a : ℕ} {b c : Three} :
    H0clause (P a b c) ↔
      (a = 0 → ∀ x ∈ Gterm 0 b, olt x b) ∧ H0clause b ∧ H0clause c := Iff.rfl

/-- **A subscript-`≤ 1` CNF term meeting the head-`0` clause is a Buchholz OT
term.**  Structural induction on `t` (mirror of `wf3_of_cnf_subs0`): recursive
parts and the non-increasing-spine clause `hdle` from CNF; the OT3 clause splits
on the head subscript `a ≤ 1` — `OT3all1_head1` for `a = 1`, the supplied
`H0clause` for `a = 0`. -/
theorem wf3_of_cnf_subs1 :
    ∀ {t : Three}, cnf t → subs t ⊆ {0,1} → H0clause t → wf3 t := by
  intro t
  induction t with
  | Z => intro _ _ _; trivial
  | P a b c ihb ihc =>
    intro hcnf hsub hH0
    have ha : a ≤ 1 := subs_P_head01 hsub
    have cnfb : cnf b := cnf_P_arg hcnf
    have cnfc : cnf c := cnf_P_tail hcnf
    have subb : subs b ⊆ {0,1} := subs_P_subL01 hsub
    have subc : subs c ⊆ {0,1} := subs_P_subR01 hsub
    obtain ⟨h0, hHb, hHc⟩ := (H0clause_P).1 hH0
    have wfb : wf3 b := ihb cnfb subb hHb
    have wfc : wf3 c := ihc cnfc subc hHc
    refine (wf3_P).2 ⟨wfb, wfc, ?_, ?_⟩
    · -- OT3 on the argument, by head subscript
      rcases Nat.lt_or_ge a 1 with hlt | hge
      · have ha0 : a = 0 := by omega
        subst ha0
        exact h0 rfl
      · have ha1 : a = 1 := by omega
        subst ha1
        exact OT3all1_head1 cnfb wfb subb
    · -- hdle clause, from CNF (verbatim from `wf3_of_cnf_subs0`)
      cases c with
      | Z => trivial
      | P e f g =>
        rw [cnf_P_P] at hcnf
        obtain ⟨_, ndom, _⟩ := hcnf
        rw [olt_P_P] at ndom
        push_neg at ndom
        obtain ⟨hea, hbf_imp, _⟩ := ndom
        rw [hdle_P_P]
        rcases Nat.lt_or_ge e a with hlt | hge
        · exact Or.inl hlt
        · have heq : a = e := le_antisymm hge hea
          subst heq
          rcases Three.olt_total f b with hfb | hfeqb | hbf
          · exact Or.inr ⟨rfl, Or.inl hfb⟩
          · exact Or.inr ⟨rfl, Or.inr hfeqb⟩
          · exact absurd hbf (hbf_imp rfl)

/-- **THE SINGLE RESIDUAL of this level.**  Every standard form with row-1
entries `≤ 1` translates to a term meeting the head-`0` OT3 clause.

WHY IT IS TRUE: empirically exact — 0 violations over 2 494 996 standard forms
(137 754 259 head-`0` OT3 checks).  The excluding structure is the row-1
discipline `r1ok` (all standard forms satisfy it via `r1ok_ST_PS`) pulled
through `translate`: a row-1 value of `1` has a row-0 parent one level below
with row-1 value `0`, so in the forest a `p₁` node carrying an escaping
argument never sits in the `Gterm 0`-collected position under a `p₀` head.

WHY IT IS NOT TERM-LEVEL: the clean term discipline `okH` (under which the
head-`0` clause IS proved, `OT3all0_okH`) is FALSE on the image — head-`0`
principals may carry head-`1` arguments (`p₀(p₁(0))`) that are OT3-valid yet
`okH`-illegal.  No hereditary predicate on `Three` separates the valid image
positions from the invalid abstract ones; the separation is exactly the
`Gterm`-collection ↔ sequence-index `r1ok`-witness correspondence.

RESIDUAL OBSTRUCTION: build that bridge (via `subs_translate` and the
forest-position machinery of `Mechanized.lean`) and discharge `H0clause`.
Once available, `OT3all0_okH` discharges each head-`0` node where the local
argument satisfies `okH`, and the `r1ok`-bridge supplies the remaining
head-`1`-argument nodes; this is the genuine research core. -/
theorem H0clause_translate {M : PairSeq} (hM : ST_PS M)
    (z : ∀ p ∈ M, p.2 ≤ 1) : H0clause (translate M) := by
  sorry

/-! ## Lifting to pair sequences -/

/-- If every row-1 entry of `M` is `≤ 1`, then `sndSet M ⊆ {0,1}`. -/
theorem sndSet_subs1 {M : PairSeq} (z : ∀ p ∈ M, p.2 ≤ 1) : sndSet M ⊆ {0,1} := by
  intro y hy
  rw [mem_sndSet] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  have := z p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **A standard form with all row-1 entries `≤ 1` translates to a Buchholz OT
term.**  CNF from `cnf_ST_PS`; subscripts `⊆ {0,1}` from
`subs (translate M) ⊆ sndSet M ⊆ {0,1}`; the head-`0` clause from
`H0clause_translate`; then `wf3_of_cnf_subs1`. -/
theorem wf3_translate_subs1 {M : PairSeq} (hM : ST_PS M)
    (z : ∀ p ∈ M, p.2 ≤ 1) : wf3 (translate M) := by
  have hsub : subs (translate M) ⊆ {0,1} :=
    Set.Subset.trans (subs_translate M) (sndSet_subs1 z)
  exact wf3_of_cnf_subs1 (cnf_ST_PS hM) hsub (H0clause_translate hM z)

/-- The `maxr1 ≤ 1` fragment is closed under one step: `step_in_ST_PS` keeps
standardness; `oper_snd_subset` keeps the row-1 entries inside the old ones,
hence `≤ 1`.  Mirror of `subs0_step_closed`. -/
theorem subs1_step_closed {M T : PairSeq} (hM : ST_PS M) (z : ∀ p ∈ M, p.2 ≤ 1)
    (st : step M T) : ST_PS T ∧ (∀ p ∈ T, p.2 ≤ 1) := by
  refine ⟨step_in_ST_PS hM st, ?_⟩
  cases st with
  | @step_oper n L hn =>
    intro p hp
    have hmem : p.2 ∈ sndSet (M⟦n⟧) := by rw [mem_sndSet]; exact ⟨p, hp, rfl⟩
    have := oper_snd_subset M n hmem
    rw [mem_sndSet] at this
    obtain ⟨q, hq, hq2⟩ := this
    rw [← hq2]; exact z q hq

/-- **The `maxr1 ≤ 1` level terminates directly.**  Every standard form with
all row-1 entries `≤ 1` is `stepR`-accessible — via `acc_wf3_fragment` with
`D = {N | ST_PS N ∧ all row-1 entries ≤ 1}`, whose obligations are
`subs1_step_closed` and `wf3_translate_subs1`.  Composes with
`acc_wf3_fragment`/`Wtt` exactly as `acc_subs0`. -/
theorem acc_subs1 {M : PairSeq} (hM : ST_PS M) (z : ∀ p ∈ M, p.2 ≤ 1) :
    Acc stepR M := by
  refine acc_wf3_fragment (fun N => ST_PS N ∧ (∀ p ∈ N, p.2 ≤ 1))
    (fun N hN => hN.1)
    (fun N T hN st => subs1_step_closed hN.1 hN.2 st)
    (fun N hN => wf3_translate_subs1 hN.1 hN.2) ⟨hM, z⟩

end YAPSS

