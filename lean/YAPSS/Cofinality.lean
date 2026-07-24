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
import YAPSS.Seqlex
import YAPSS.Nrmstep

namespace YAPSS
open Three

/-! ## Part 0 — `seqlex` plumbing

`olt_ST_iff_seqlex` (Seqlex.lean:709) turns the whole statement into a purely
combinatorial one about the *column-lexicographic* order on pair sequences.
This section collects the list-level facts about `seqlex` that the reduction
needs (they are absent from `Seqlex.lean`, which only needed the two
directions of the iso). -/

theorem pairlt_trans {p q r : ℕ × ℕ} (h1 : pairlt p q) (h2 : pairlt q r) :
    pairlt p r := by
  unfold pairlt at *; omega

theorem pairlt_irrefl (p : ℕ × ℕ) : ¬ pairlt p p := by
  unfold pairlt; omega

theorem pairlt_total (p q : ℕ × ℕ) : pairlt p q ∨ p = q ∨ pairlt q p := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  unfold pairlt
  simp only [Prod.mk.injEq]
  omega

/-- `seqlex` is transitive. -/
theorem seqlex_trans : ∀ {A B C : PairSeq}, seqlex A B → seqlex B C → seqlex A C := by
  intro A
  induction A with
  | nil =>
    intro B C _ h2
    rcases C with _ | ⟨c, C'⟩
    · rcases B with _ | ⟨b, B'⟩
      · exact absurd h2 (by simp)
      · exact absurd h2 (by simp)
    · simp
  | cons a A' ih =>
    intro B C h1 h2
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h1 (by simp)
    rcases C with _ | ⟨c, C'⟩
    · exact absurd h2 (by simp)
    rw [seqlex_cons_cons] at h1 h2 ⊢
    rcases h1 with p1 | ⟨rfl, s1⟩ <;> rcases h2 with p2 | ⟨rfl, s2⟩
    · exact Or.inl (pairlt_trans p1 p2)
    · exact Or.inl p1
    · exact Or.inl p2
    · exact Or.inr ⟨rfl, ih s1 s2⟩

theorem seqlex_irrefl : ∀ (A : PairSeq), ¬ seqlex A A := by
  intro A
  induction A with
  | nil => simp
  | cons a A' ih =>
    rw [seqlex_cons_cons]
    rintro (h | ⟨-, h⟩)
    · exact pairlt_irrefl a h
    · exact ih h

/-- `≤` version of `seqlex`. -/
def sle (M N : PairSeq) : Prop := M = N ∨ seqlex M N

theorem sle_refl (M : PairSeq) : sle M M := Or.inl rfl

theorem sle_seqlex_trans {A B C : PairSeq} (h1 : sle A B) (h2 : seqlex B C) :
    seqlex A C := by
  rcases h1 with rfl | h1
  · exact h2
  · exact seqlex_trans h1 h2

theorem seqlex_sle_trans {A B C : PairSeq} (h1 : seqlex A B) (h2 : sle B C) :
    seqlex A C := by
  rcases h2 with rfl | h2
  · exact h1
  · exact seqlex_trans h1 h2

/-- Extending on the right strictly increases (`seqlex_prefix`, `≤` form). -/
theorem sle_append_right {A B : PairSeq} (h : sle A B) (C : PairSeq) (hC : C ≠ []) :
    seqlex A (B ++ C) :=
  sle_seqlex_trans h (seqlex_prefix hC B)

/-- **Snoc case analysis.**  A sequence below `D ++ [lp]` either stays `≤ D`,
or extends `D` by a first column strictly below `lp`.  This is the shape that
drives every branch of the cofinality proof. -/
theorem seqlex_snoc_cases : ∀ {D : PairSeq} {lp : ℕ × ℕ} {N : PairSeq},
    seqlex N (D ++ [lp]) →
    sle N D ∨ ∃ q S, N = D ++ q :: S ∧ pairlt q lp := by
  intro D
  induction D with
  | nil =>
    intro lp N h
    rcases N with _ | ⟨q, S⟩
    · exact Or.inl (sle_refl _)
    · rw [List.nil_append, seqlex_cons_cons] at h
      rcases h with h | ⟨rfl, h⟩
      · exact Or.inr ⟨q, S, rfl, h⟩
      · exact absurd h (by cases S <;> simp)
  | cons d D' ih =>
    intro lp N h
    rcases N with _ | ⟨q, S⟩
    · exact Or.inl (Or.inr (by simp))
    rw [List.cons_append, seqlex_cons_cons] at h
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl (Or.inr (Or.inl h))
    · rcases ih h with hle | ⟨q', S', rfl, hq'⟩
      · refine Or.inl ?_
        rcases hle with rfl | hle
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨rfl, hle⟩)
      · exact Or.inr ⟨q', S', by simp, hq'⟩

/-! ## Part 1 — the reduction to `seqlex`

`pss_cofinality` follows from its `seqlex` form, because `translate` is an
order isomorphism onto `<o` on standard forms (`olt_ST_iff_seqlex`). -/

/-- The `seqlex` form of PSS Bachmann cofinality. -/
def SeqlexCofinality : Prop :=
  ∀ {M N : PairSeq}, ST_PS M → ST_PS N → seqlex N M →
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧)

theorem pss_cofinality_of_seqlex (H : SeqlexCofinality)
    {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) := by
  have hne : N ≠ M := by
    rintro rfl; exact olt_irrefl _ h
  have hsl : seqlex N M := (olt_ST_iff_seqlex hN hM hne).1 h
  obtain ⟨n, hn, hres⟩ := H hM hN hsl
  refine ⟨n, hn, ?_⟩
  rcases hres with rfl | hlt
  · exact Or.inr rfl
  · by_cases he : N = M⟦n⟧
    · exact Or.inr (by rw [he])
    · exact Or.inl ((olt_ST_iff_seqlex hN (ST_PS.oper hM hn) he).2 hlt)

/-! ## Part 2 — the degenerate branches of `oper` -/

theorem entry_zero (M : PairSeq) (j : ℕ) : entry M 0 j = (M.getD j (0, 0)).1 := by
  unfold entry; rw [if_pos rfl]

theorem entry_one (M : PairSeq) (j : ℕ) : entry M 1 j = (M.getD j (0, 0)).2 := by
  unfold entry; rw [if_neg one_ne_zero]

theorem dropLast_snoc_getD {M : PairSeq} (hne : M ≠ []) :
    M.dropLast ++ [M.getD (M.length - 1) (0, 0)] = M := by
  have hlen : 0 < M.length := List.length_pos_of_ne_nil hne
  have h1 : M.getD (M.length - 1) (0, 0) = M.getLast hne := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      List.getLast_eq_getElem]
    rfl
  rw [h1, List.dropLast_append_getLast]

/-- **Branch `self`**: `M` has length `≤ 1`, so `M⟦n⟧ = M` and the hypothesis
is already the conclusion. -/
theorem seqlex_cof_short {M N : PairSeq} (hL : M.length - 1 = 0) (h : seqlex N M) :
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) :=
  ⟨1, le_rfl, Or.inr (by rw [oper_eq_self_of_short 1 hL]; exact h)⟩

/-- **Branch `zero`**: the last column is `(0,0)`, so `M⟦n⟧ = M.dropLast`.
Nothing can squeeze strictly between `M.dropLast` and `M.dropLast ++ [(0,0)]`
because `(0,0)` is the `pairlt`-minimum. -/
theorem seqlex_cof_zero {M N : PairSeq} (hL : 1 < M.length)
    (hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0)
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
  have hne : M ≠ [] := by intro he; rw [he] at hL; simp at hL
  have hlpz : M.getD (M.length - 1) (0, 0) = (0, 0) := by
    rw [entry_zero] at hz
    rw [entry_one] at hz
    exact Prod.ext hz.1 hz.2
  have hMsplit : M.dropLast ++ [M.getD (M.length - 1) (0, 0)] = M :=
    dropLast_snoc_getD hne
  have hop : M⟦1⟧ = M.dropLast := by
    rw [oper_eq_pred_of_zero 1 (by omega) hz]
    unfold Pred; rw [if_neg (by omega)]
  refine ⟨1, le_rfl, ?_⟩
  rw [hop]
  rcases seqlex_snoc_cases (D := M.dropLast) (lp := M.getD (M.length - 1) (0, 0))
      (N := N) (by rw [hMsplit]; exact h) with hle | ⟨q, S, -, hq⟩
  · exact hle
  · rw [hlpz] at hq
    exact absurd hq (by simp [pairlt])

/-- **The `noparent` branch is empty on `ST_PS`** (`hp_last`, Nrmstep.lean:5990):
every standard form whose last column is not `(0,0)` does have a unique parent. -/
theorem hasParent_last_ST_PS {M : PairSeq} (hM : ST_PS M) (hlen : 0 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0)) :
    hasParent M (idx1 M (M.length - 1)) (M.length - 1) := by
  refine hp_last (blockok_ST_PS hM) (z0ok_ST_PS hM) hlen ?_
  intro he
  exact hz ⟨by rw [entry_zero, he], by rw [entry_one, he]⟩

/-! ## Part 3 — the bad branch: reduction to the copy-tiling crux -/

/-- The `oper_bad_blocks` copy list *is* `Wf.copies` (the `shiftr0`-packaged
form used by the CNF proofs). -/
theorem flatMap_eq_copies (blk : PairSeq) (d0 n : ℕ) :
    (List.range n).flatMap (fun k => blk.map fun p => (p.1 + k * d0, p.2))
      = copies d0 blk n := rfl

theorem sle_append_cancel (A : PairSeq) {u v : PairSeq} :
    sle (A ++ u) (A ++ v) ↔ sle u v := by
  unfold sle
  rw [seqlex_append_cancel]
  constructor
  · rintro (h | h)
    · exact Or.inl (List.append_cancel_left h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem getD_last_of_snoc (D : PairSeq) (lp : ℕ × ℕ) :
    (D ++ [lp]).getD ((D ++ [lp]).length - 1) (0, 0) = lp := by
  have hl : (D ++ [lp]).length - 1 = D.length := by simp
  rw [hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

/-- **The bad-branch decomposition, uniformly in `n`.**  `oper_bad_blocks`
produces its block data per copy count; the parent is unique (`hasParent`), so
the data is in fact the same for every `n`.  This packages it once and for all,
in the `copies`/`shiftr0` form. -/
theorem oper_bad_blocks_all {M : PairSeq} (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)) :
    ∃ (G : PairSeq) (v0 w0 : ℕ) (R : PairSeq) (d0 : ℕ) (lp : ℕ × ℕ),
      M = G ++ ((v0, w0) :: R) ++ [lp] ∧
      (∀ n, 1 ≤ n → M⟦n⟧ = G ++ copies d0 ((v0, w0) :: R) n) ∧
      (∀ x ∈ R, v0 < x.1) ∧ v0 < lp.1 ∧
      ((d0 = 0 ∧ lp.2 = 0) ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0)) := by
  obtain ⟨G, v0, w0, R, d0, lp, hM1, -, R_gt, lp_gt, disj, hnR⟩ :=
    oper_bad_blocks (n := 1) L hz hp le_rfl
  -- the dropped column is the last column of `M`
  have hlpM : lp = M.getD (M.length - 1) (0, 0) := by
    conv_rhs => rw [hM1]
    exact (getD_last_of_snoc _ _).symm
  -- the `idx1 = 0` branch pins `lp.2 = 0`
  have hdisj' : (d0 = 0 ∧ lp.2 = 0) ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0) := by
    rcases disj with ⟨h0, hi⟩ | ⟨h1, h2, h3, -⟩
    · refine Or.inl ⟨h0, ?_⟩
      unfold idx1 at hi
      split at hi
      · exact absurd hi one_ne_zero
      · rw [hlpM, ← entry_one]; omega
    · exact Or.inr ⟨h1, h2, h3⟩
  refine ⟨G, v0, w0, R, d0, lp, hM1, ?_, R_gt, lp_gt, hdisj'⟩
  intro n hn
  obtain ⟨G', v0', w0', R', d0', lp', hM2, hMn2, -, -, disj', hnR'⟩ :=
    oper_bad_blocks (n := n) L hz hp hn
  -- the two decompositions agree: the parent index is unique
  have hlen : G'.length = G.length := hp.unique hnR' hnR
  have heq : (G' ++ ((v0', w0') :: R')) ++ [lp'] = (G ++ ((v0, w0) :: R)) ++ [lp] :=
    hM2.symm.trans hM1
  obtain ⟨hGb, hlpe⟩ := List.append_inj' heq rfl
  obtain ⟨rfl, hblk⟩ := List.append_inj hGb hlen
  have hlp' : lp' = lp := by simpa using hlpe
  obtain ⟨hv, hR'⟩ : (v0', w0') = (v0, w0) ∧ R' = R := by
    exact ⟨by simpa using congrArg (fun l => l.headI) hblk, by
      simpa using congrArg (fun l => l.tail) hblk⟩
  obtain ⟨rfl, rfl⟩ : v0' = v0 ∧ w0' = w0 := ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩
  subst hR'
  -- and so does the shift
  have hd : d0' = d0 := by
    have hi1 : ∀ {e : ℕ}, nextrel1 M e (M.length - 1) → idx1 M (M.length - 1) ≠ 0 := by
      intro e hne he
      have hlt : entry M 1 e < entry M 1 (M.length - 1) := hne.2.2.2.1
      unfold idx1 at he
      split at he
      · exact one_ne_zero he
      · omega
    rcases disj with ⟨h0, hi⟩ | ⟨-, -, h3, hn1⟩ <;>
      rcases disj' with ⟨h0', hi'⟩ | ⟨-, -, h3', hn1'⟩
    · rw [h0, h0']
    · exact absurd hi (hi1 hn1')
    · exact absurd hi' (hi1 hn1)
    · rw [hlp'] at h3'; omega
  rw [hMn2, hd]
  rfl

/-- **The copy-tiling crux.**  The single residual content of PSS Bachmann
cofinality: a standard form `N` that agrees with the host `M` on the *whole*
good prefix `G` and bad block `blk = (v0,w0) :: R`, and then continues with a
column strictly below the dropped column `lp`, is dominated by finitely many
shifted copies of `blk`. -/
def CopyCrux : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ} {lp q : ℕ × ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [lp]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ q :: S) →
    (∀ x ∈ R, v0 < x.1) → v0 < lp.1 →
    ((d0 = 0 ∧ lp.2 = 0) ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0)) →
    pairlt q lp →
    ∃ m, 1 ≤ m ∧ sle (q :: S) (shiftr0 d0 (copies d0 ((v0, w0) :: R) m))

/-- **Branch `bad`**: modulo the copy-tiling crux, the genuine branch. -/
theorem seqlex_cof_bad (H : CopyCrux) {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
  have hp := hasParent_last_ST_PS hM (by omega) hz
  obtain ⟨G, v0, w0, R, d0, lp, hMeq, hMn, R_gt, lp_gt, disj⟩ :=
    oper_bad_blocks_all L hz hp
  rcases seqlex_snoc_cases (D := G ++ ((v0, w0) :: R)) (lp := lp) (N := N)
      (by rw [← hMeq]; exact h) with hle | ⟨q, S, hNeq, hq⟩
  · exact ⟨1, le_rfl, by rw [hMn 1 le_rfl, copies_one]; exact hle⟩
  · obtain ⟨m, hm, hsle⟩ :=
      H (hMeq ▸ hM) (hNeq ▸ hN) R_gt lp_gt disj hq
    refine ⟨m + 1, by omega, ?_⟩
    rw [hMn (m + 1) (by omega), copies_succ_front, hNeq, List.append_assoc]
    exact (sle_append_cancel _).2 ((sle_append_cancel _).2 hsle)

/-- Modulo the crux, the `seqlex` form of cofinality holds. -/
theorem seqlex_cofinality_of_crux (H : CopyCrux) : SeqlexCofinality := by
  intro M N hM hN h
  by_cases hL : M.length - 1 = 0
  · exact seqlex_cof_short hL h
  · by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
    · exact seqlex_cof_zero (by omega) hz h
    · exact seqlex_cof_bad H hM hN (by omega) hz h

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
