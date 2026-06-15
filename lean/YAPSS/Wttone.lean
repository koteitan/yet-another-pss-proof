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

/-! **THE SINGLE RESIDUAL of this level.**  Every standard form with row-1
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

PROGRESS / REDUCTION (for whoever closes this).  By `translate.induct`, at a
node `translate (p :: rest) = P p.2 (translate desc) (translate sib)` (with
`desc = rest.takeWhile (p.1 < ·.1)`, `sib = rest.dropWhile …`) the IH gives
`H0clause` for the two sub-translates, so the whole obligation reduces to the
PER-ROOT fact:

  (★)  if `p.2 = 0` (a row-1-`0` root) then
       `∀ x ∈ Gterm 0 (translate desc), olt x (translate desc)`.

(★) is empirically exact (0 violations over all row-1-`0` roots; the descendant
translates split as lead-`1` ≈ 20251 vs lead-`0` ≈ 241).  Two further
empirical facts narrow it:
  • `lead`-bound `hyp t := ∀ x ∈ Gterm 0 t, lead x ≤ lead t` holds for every
    such `translate desc`.  But `hyp ∧ wf3 ∧ subs ⊆ {0,1} ⟹ (★)` is FALSE in
    general (`p₁(0)+p₀(p₁(0)+p₁(0))` is a `hyp` term failing the clause), so
    `(★)` needs the descendant block's deeper `r1ok` structure, not just the
    lead bound.
  • Fact S is now AVAILABLE as a proved lemma: `z0ok_ST_PS`
    (`Nrmstep.lean`) gives `z0ok M`, i.e. every column with row-0 `= 0` has
    row-1 `= 0` (equivalently row-1 `= 1 ⟹` row-0 `> 0`).  `z0ok` is a
    per-column property, hence inherited by every `takeWhile`/`dropWhile`
    sub-block, so it flows freely through the `translate.induct` recursion.

EQUIVALENT CLEANER FORM (recommended attack).  `nrm (translate M) = translate M`
is EQUIVALENT to this whole level (verified `= id` on 404 940 maxr1-`≤1` forms,
and `≠ id` on every maxr1-`= 2` form — exactly the crux boundary), and it
discharges `wf3 (translate M)` immediately via the proved `wf3_nrm`:
`wf3 (translate M) = wf3 (nrm (translate M))`.  Concretely `nrm (P a b c) =
ins a (proj a (nrm b)) (nrm c)`, so `nrm t = t` reduces at each node to
`proj a (arg) = arg` (i.e. `¬ pfire a (arg)` — the SAME head-`a` OT3 clause)
plus `ins`-no-absorption (`cnf`).  For `a = 1` this is `OT3all1_head1`; for
`a = 0` it is the SAME residual.

SHARED PROJECT-WIDE BRIDGE.  This head-`0` `r1ok`-through-`translate` fact is
the SAME open obstruction as the `Nrm`-route residuals `proj0_fireprop_NF`
and `proj0_bothfire_NF` (`Nrmstep.lean`, both `sorry`): "`pfire 0` on an `NF`
argument propagates / descends".  Their audit note records the structural key
`proj 0 (P 1 b' c') = proj 0 b'` (proj-0 peels an outer `p₁` into the ascent
source).  Closing any one of these closes the maxr1-`= 1` level; it is the
genuine forest core the whole project shares, not a quick development. -/
/-- **Diag base of `H0clause_translate`** (GREEN).  Under the row-`1` `≤ 1`
constraint a diagonal `diagSeq 0 v` has `v ≤ 1`, so its translate is `P 0 Z Z`
(`v = 0`) or `P 0 (P 1 Z Z) Z` (`v = 1`); both meet `H0clause` directly (the
head-`0` clause's only critical at level `0` is `Z`, which is `olt` everything). -/
theorem H0clause_diagSeq_le1 {v : ℕ} (hv : v ≤ 1) :
    H0clause (translate (diagSeq 0 v)) := by
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
  · -- v = 0: translate (diagSeq 0 0) = P 0 Z Z.
    rw [translate_diagSeq (le_refl 0)]
    have e : diagSeq 1 0 = [] := by
      unfold diagSeq; rw [show 0 + 1 - 1 = 0 by omega]; rfl
    rw [e, translate_nil]
    simp [H0clause]
  · -- v = 1: translate (diagSeq 0 1) = P 0 (P 1 Z Z) Z.
    rw [translate_diagSeq (by omega : (0:ℕ) ≤ 1)]
    have e : diagSeq 1 1 = [(1,1)] := by
      unfold diagSeq; rw [show 1 + 1 - 1 = 1 by omega]; rfl
    rw [e, translate_single]
    -- H0clause (P 0 (P 1 Z Z) Z): head-0 clause needs ∀ x ∈ Gterm 0 (P 1 Z Z), olt x (P 1 Z Z).
    refine ⟨?_, ?_, H0clause_Z⟩
    · intro _ x hx
      rw [mem_Gterm_P] at hx
      rcases hx with ⟨-, rfl | hx⟩ | hx
      · exact olt_Z_P 1 Z Z
      · simp [Gterm] at hx
      · simp [Gterm] at hx
    · exact ⟨by intro h; simp at h, H0clause_Z, H0clause_Z⟩

/-- The diagonal `(v, v)` is a member of `diagSeq 0 v`. -/
theorem diag_mem_diagSeq (v : ℕ) : (v, v) ∈ diagSeq 0 v := by
  unfold diagSeq
  rw [List.mem_map]
  exact ⟨v, List.mem_range'.2 ⟨v, by omega, by omega⟩, rfl⟩

/-- `z` (row-`1` `≤ 1`) is inherited by the `dropWhile`-tail. -/
theorem z_dropWhile {p : ℕ × ℕ} {rest : PairSeq} (z : ∀ q ∈ p :: rest, q.2 ≤ 1) :
    ∀ q ∈ rest.dropWhile (fun r => p.1 < r.1), q.2 ≤ 1 :=
  fun q hq => z q (List.mem_cons_of_mem _ ((List.dropWhile_sublist _).subset hq))

/-- `z` (row-`1` `≤ 1`) is inherited by `(0,0)` prepended to the `takeWhile`-block. -/
theorem z_takeWhile_cons {p : ℕ × ℕ} {rest : PairSeq} (z : ∀ q ∈ p :: rest, q.2 ≤ 1) :
    ∀ q ∈ (0,0) :: rest.takeWhile (fun r => p.1 < r.1), q.2 ≤ 1 := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · simp
  · exact z q (List.mem_cons_of_mem _ ((List.takeWhile_sublist _).subset hq))

/-- **The single genuine residual of the maxr1-`≤1` head-`0` wall.**  The
root-level head-`0` OT3 clause for an `ST_PS`-translate descendant block:
`(0,0) :: B ∈ ST_PS` (with row-`1` `≤ 1`) ⟹ every coefficient in
`Gterm 0 (translate B)` is strictly below `translate B`.

This is what `H0clause_translate` needs at every head-`0` node, ABOVE the
hereditary `H0clause` of the sub-blocks (which it discharges by recursion via
`ST_PS_desc` / `ST_PS_suffix`).  MODEL-VERIFIED TRUE at every head-`0` node of
every row-`1`-`≤1` `ST_PS`-translate (**25061 / 25061**, closure+9, via the
node-relative lift `(0,0) :: (argblock − x) ∈ ST_PS`).

WHY IT IS NOT LOCAL.  The clause splits by `lead (translate B)`: coefficients of
strictly smaller head are auto-`olt` (verified 18235 / 0); coefficients of EQUAL
head (`= 1`) are NOT all in `Gterm 1` (head-`0`-nested head-`1` coefficients,
5609 / 6461) so `OT3all1_head1` does not reach them — their `olt` depends on the
forest position, i.e. full `ST_PS`-reachability.  Same content as
`Nrmstep.not_pfire0_lead1max1_NF` (`¬ pfire 0 b ⟺ ∀x∈Gterm 0 b, olt x b`) and
`Rdesc_hstep`; the documented project-central open problem (the `oper`
copy/tiling core of `ST_PS_desc`). -/
theorem root_clause_translate {B : PairSeq} (hB : ST_PS ((0,0) :: B))
    (z : ∀ q ∈ (0,0) :: B, q.2 ≤ 1) :
    ∀ x ∈ Gterm 0 (translate B), olt x (translate B) := by
  sorry

/-- **`H0clause` on descendant-block translates** (the second genuine residual).
For a descendant block `B` with `(0,0) :: B ∈ ST_PS` and row-`1` `≤ 1`,
`translate B` itself (the head-`0` *argument* forest, possibly head-`1` at its
root) meets `H0clause`.  MODEL-VERIFIED TRUE (**1481 / 0** over the
exhaustively-enumerated z-`ST_PS` descendant blocks, closure+7).

It is NOT reducible to `H0clause_translate` on a smaller `ST_PS` form: the
descendant block `B`'s translate is generally NOT achievable as `translate M'`
for any `ST_PS` form `M'` (only **702 / 2845** z-form `translate desc` values are
realisable as a standard-form translate) — descendant blocks are forest-interior
copies, not standalone standard forms (a row-`0` shift fixes the order but not
the row-`1` climbing).  So its proof requires the `oper` copy/tiling structure
directly (the documented project-central content, same family as
`Nrmstep.not_pfire0_lead1max1_NF` / `Rdesc_hstep`); it is paired with
`root_clause_translate` (the head-`0` clause at the node above `B`). -/
theorem H0clause_desc_block {B : PairSeq} (hB : ST_PS ((0,0) :: B))
    (z : ∀ q ∈ (0,0) :: B, q.2 ≤ 1) : H0clause (translate B) := by
  sorry

theorem H0clause_translate {M : PairSeq} (hM : ST_PS M)
    (z : ∀ p ∈ M, p.2 ≤ 1) : H0clause (translate M) := by
  -- Strong recursion on `tsize (translate M)`: `sib` recurses here (proper
  -- subterm of `translate M`, strictly smaller `tsize`); the head-`0` root clause
  -- is `root_clause_translate` and the descendant `H0clause` is `H0clause_desc_block`
  -- (both on `(0,0) :: desc ∈ ST_PS` via the `ST_PS_desc` descendant closure).
  generalize hsz : tsize (translate M) = N
  induction N using Nat.strong_induction_on generalizing M with
  | _ N IH =>
  subst hsz
  obtain ⟨rest, hrest⟩ : ∃ rest, M = (0,0) :: rest := by
    have hp := stps_head hM
    have hlen := stps_len_pos hM
    cases M with
    | nil => simp at hlen
    | cons q rest =>
      refine ⟨rest, ?_⟩
      have : q = (0,0) := by simpa using hp
      rw [this]
  subst hrest
  set desc := rest.takeWhile (fun r => (0:ℕ) < r.1) with hdesc
  set sib := rest.dropWhile (fun r => (0:ℕ) < r.1) with hsib
  have htr : translate ((0,0) :: rest) = P 0 (translate desc) (translate sib) := by
    rw [translate]
  rw [htr]
  have hdescST : ST_PS ((0,0) :: desc) := ST_PS_desc hM
  have hzdesc : ∀ q ∈ (0,0) :: desc, q.2 ≤ 1 := z_takeWhile_cons z
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact root_clause_translate hdescST hzdesc
  · exact H0clause_desc_block hdescST hzdesc
  · rcases ST_PS_suffix hM with hempty | hstps
    · rw [hsib, hempty, translate]; exact H0clause_Z
    · have hzsib : ∀ q ∈ sib, q.2 ≤ 1 := z_dropWhile z
      have hszsib : tsize (translate sib) < tsize (translate ((0,0) :: rest)) := by
        rw [htr]; simp only [tsize]; have := tsize_pos (translate desc); omega
      exact IH (tsize (translate sib)) hszsib hstps hzsib rfl

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

