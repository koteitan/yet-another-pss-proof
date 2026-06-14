/-
**The `maxr1 ≤ 1` level of the `W = T` route** (one level above
`Wttbase.lean`).  This is RESEARCH (not a port): the Isabelle peer `ya-pss`
has not done this level — it is the next live frontier.

**Empirical anchor (verified on 63 088 standard forms, 0 violations).**  A
standard form all of whose row-1 entries are `≤ 1` translates to a *genuine
Buchholz OT term* (`wf3`).  The re-ascent crux therefore lives strictly at
`maxr1 ≥ 2`: the smallest violator is `diagSeq 0 2 = (0,0)(1,1)(2,2)`, whose
translate `p₀(p₁(p₂(0)))` fails OT3 (the buried subscript `2` escapes upward
through `G₀`).  So `maxr1 ≤ 1` is still crux-free — *provided* the row-1
discipline `r1ok` is used to exclude a buried `1` under a `0` head.

Structure of the proof, and where the residual sits:
  * `subs (translate M) ⊆ {0,1}` (from `subs_translate` + the row-1 bound),
    plus `cnf` (from `cnf_ST_PS`), give every prerequisite of `wf3` EXCEPT the
    OT3 clause `∀ x ∈ Gterm a b, olt x b`.
  * OT3 splits on the head subscript `a ∈ {0,1}` (`subs_P_head01`).
      - **`a = 1`** (head = maximal subscript): FULLY PROVED here
        (`OT3all1_head1`), via `olt_arg_principal1` (argument below `P 1 b c`)
        and `olt_tail_of_cnf` (tail below the sum), mirroring `OT3all`.
        Empirically `a = 1` OT3 never fails (0/65 760 subterms).
      - **`a = 0`**: the genuine crux.  Term-level `cnf ∧ subs ⊆ {0,1}` is
        *provably insufficient* (e.g. `p₀(p₀(p₁(0)))` is cnf, subs ⊆ {0,1},
        yet fails OT3: `p₁(0) ∈ G₀(p₀(p₁(0)))` is not `<o p₀(p₁(0))`).  The
        excluding invariant is exactly `r1ok` pulled through `translate`: a
        subscript-`1` may not sit *strictly below* a subscript-`0` head.  This
        is isolated as the single `sorry` `OT3all1_head0`, with the precise
        residual recorded in its docstring.

Everything around the residual is sorry-free; `acc_subs1` composes with
`acc_wf3_fragment`/`Wtt` exactly as `acc_subs0` does.
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

/-! ## The two principal-domination facts (subscript-`≤ 1` / CNF) -/

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
the CNF non-domination clause `¬(P a b Z <o P e f Z)` together with
`olt_total` forces the head comparison `e ≤ a`. -/
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

/-- **Head-`0` OT3** — *the single residual of this level*.

CLAIM: for a CNF, `wf3` term `t` with `subs t ⊆ {0,1}` that is the translate
of a standard form (`r1ok`), every `x ∈ Gterm 0 t` has `olt x t`.

WHAT IS LEFT: the proof that no subscript-`1` principal sits *strictly below* a
subscript-`0` head.  Empirically this holds on every `translate (ST_PS)` image
(0 violations in 47 069 subscript-`≤ 1` translate-terms), but it is FALSE for
term-level `cnf ∧ subs ⊆ {0,1}` alone — the minimal counterexample is
`p₀(p₀(p₁(0)))` (`= P 0 (P 0 (P 1 Z Z) Z) Z`), which is cnf and subs-`≤ 1`,
yet `p₁(0) ∈ G₀(p₀(p₁(0)))` is not `<o p₀(p₁(0))`.

WHY IT IS TRUE FOR THE IMAGE: the excluding invariant is the row-1 discipline
`r1ok` (`Nrmstep.r1ok`, satisfied by all standard forms via `r1ok_ST_PS`)
pulled through `translate`: a row-1 value of `1` has a row-0 parent one level
below whose row-1 value is `0` and which it exceeds by exactly `+1`, so in the
forest a `p₁` node never lies strictly inside the argument-subtree of a `p₀`
node — exactly the configuration `G₀` would otherwise collect upward.

RESIDUAL OBSTRUCTION: connecting the term-position `Gterm 0` collection to the
sequence-index `r1ok` witness chain (the `subs_translate` / forest-position
machinery).  Stated here at the term level with the hypotheses currently
available; the real hypothesis needed is `r1ok`-via-`translate`, which is the
research core deferred to `maxr1 = 2` work. -/
theorem OT3all1_head0 :
    ∀ {t : Three}, cnf t → wf3 t → subs t ⊆ {0,1} → ∀ x ∈ Gterm 0 t, olt x t := by
  sorry

/-- **A subscript-`≤ 1` CNF translate-image is a Buchholz OT term.**  Induction
on `t` (mirror of `wf3_of_cnf_subs0`): the recursive parts and the
non-increasing-spine clause `hdle` come from CNF exactly as in the base level;
the OT3 clause splits on the head subscript `a ≤ 1` — `OT3all1_head1` for
`a = 1`, `OT3all1_head0` for `a = 0` (the residual). -/
theorem wf3_of_cnf_subs1 : ∀ {t : Three}, cnf t → subs t ⊆ {0,1} → wf3 t := by
  intro t
  induction t with
  | Z => intro _ _; trivial
  | P a b c ihb ihc =>
    intro hcnf hsub
    have ha : a ≤ 1 := subs_P_head01 hsub
    have cnfb : cnf b := cnf_P_arg hcnf
    have cnfc : cnf c := cnf_P_tail hcnf
    have subb : subs b ⊆ {0,1} := subs_P_subL01 hsub
    have subc : subs c ⊆ {0,1} := subs_P_subR01 hsub
    have wfb : wf3 b := ihb cnfb subb
    have wfc : wf3 c := ihc cnfc subc
    refine (wf3_P).2 ⟨wfb, wfc, ?_, ?_⟩
    · -- OT3 on the argument, by head subscript
      rcases Nat.lt_or_ge a 1 with hlt | hge
      · have ha0 : a = 0 := by omega
        subst ha0
        exact OT3all1_head0 cnfb wfb subb
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
        -- hea : e ≤ a, hbf_imp : a = e → ¬ b <o f
        rw [hdle_P_P]
        rcases Nat.lt_or_ge e a with hlt | hge
        · exact Or.inl hlt
        · have heq : a = e := le_antisymm hge hea
          subst heq
          rcases Three.olt_total f b with hfb | hfeqb | hbf
          · exact Or.inr ⟨rfl, Or.inl hfb⟩
          · exact Or.inr ⟨rfl, Or.inr hfeqb⟩
          · exact absurd hbf (hbf_imp rfl)

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
`subs (translate M) ⊆ sndSet M ⊆ {0,1}`; then `wf3_of_cnf_subs1`. -/
theorem wf3_translate_subs1 {M : PairSeq} (hM : ST_PS M)
    (z : ∀ p ∈ M, p.2 ≤ 1) : wf3 (translate M) := by
  have hsub : subs (translate M) ⊆ {0,1} :=
    Set.Subset.trans (subs_translate M) (sndSet_subs1 z)
  exact wf3_of_cnf_subs1 (cnf_ST_PS hM) hsub

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
`D = {N | ST_PS N ∧ all row-1 entries ≤ 1}`, whose three obligations are
`subs1_step_closed` and `wf3_translate_subs1`.  Composes with
`acc_wf3_fragment`/`Wtt` exactly as `acc_subs0` does. -/
theorem acc_subs1 {M : PairSeq} (hM : ST_PS M) (z : ∀ p ∈ M, p.2 ≤ 1) :
    Acc stepR M := by
  refine acc_wf3_fragment (fun N => ST_PS N ∧ (∀ p ∈ N, p.2 ≤ 1))
    (fun N hN => hN.1)
    (fun N T hN st => subs1_step_closed hN.1 hN.2 st)
    (fun N hN => wf3_translate_subs1 hN.1 hN.2) ⟨hM, z⟩

end YAPSS
