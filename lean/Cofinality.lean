/-
# PSS Bachmann 共終性

標準形 `M`, `N` について `translate N <o translate M` ならば、基本列のどれかが `N` を
上から抑える：ある `n ≥ 1` で `translate N ≤o translate (M⟦n⟧)`。
-/
import Term
import Seqlex
import Column

namespace YAPSS
open Three

/-! ## Part 0 — `seqlex` plumbing -/

theorem pairlt_trans {p q r : ℕ × ℕ} (h1 : pairlt p q) (h2 : pairlt q r) :
    pairlt p r := by
  unfold pairlt at *; omega

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

/-- `≤` version of `seqlex`. -/
def sle (M N : PairSeq) : Prop := M = N ∨ seqlex M N

theorem sle_refl (M : PairSeq) : sle M M := Or.inl rfl

theorem seqlex_sle_trans {A B C : PairSeq} (h1 : seqlex A B) (h2 : sle B C) :
    seqlex A C := by
  rcases h2 with rfl | h2
  · exact h1
  · exact seqlex_trans h1 h2

/-- `seqlex` is monotone under extending the *larger* side on the right. -/
theorem seqlex_append_mono : ∀ {A B : PairSeq}, seqlex A B → ∀ (C : PairSeq),
    seqlex A (B ++ C) := by
  intro A
  induction A with
  | nil =>
    intro B h C
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h (by simp)
    · simp
  | cons a A' ih =>
    intro B h C
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h (by simp)
    · rw [seqlex_cons_cons] at h
      rcases h with hp | ⟨rfl, hs⟩
      · exact Or.inl hp
      · exact Or.inr ⟨rfl, ih hs C⟩

/-- `sle` version of `seqlex_append_mono`. -/
theorem sle_append_mono {A B : PairSeq} (h : sle A B) (C : PairSeq) :
    sle A (B ++ C) := by
  rcases h with rfl | h
  · rcases C with _ | ⟨c, C'⟩
    · exact Or.inl (by simp)
    · exact Or.inr (seqlex_prefix (by simp) A)
  · exact Or.inr (seqlex_append_mono h C)

/-- **Snoc case analysis.**  A sequence below `D ++ [lp]` either stays `≤ D`,
or extends `D` by a first column strictly below `lp`. -/
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

/-- **The `noparent` branch is empty on `ST_PS`**: every standard form whose
last column is not `(0,0)` does have a unique parent. -/
theorem hasParent_last_ST_PS {M : PairSeq} (hM : ST_PS M) (hlen : 0 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0)) :
    hasParent M (idx1 M (M.length - 1)) (M.length - 1) := by
  refine hp_last (blockok_ST_PS hM) (z0ok_ST_PS hM) hlen ?_
  intro he
  exact hz ⟨by rw [entry_zero, he], by rw [entry_one, he]⟩

/-! ## Part 3 — the bad branch: reduction to the copy-tiling crux -/

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

theorem getD_append_right' (A B : PairSeq) (i : ℕ) :
    (A ++ B).getD (A.length + i) (0, 0) = B.getD i (0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

theorem getD_last_of_snoc (D : PairSeq) (lp : ℕ × ℕ) :
    (D ++ [lp]).getD ((D ++ [lp]).length - 1) (0, 0) = lp := by
  have hl : (D ++ [lp]).length - 1 = D.length := by simp
  rw [hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

/-- **The row-`1` `+1` discipline at the last column.**  If the last column of
a standard-shaped host has row-`1` parent `j0` (`nextrel1`), then its row-`1`
value is *exactly* one above the parent's.

Proof: take the first `nextrel0`-step `j0 → c` of the row-`0` ancestor chain
`le0 M j0 j1`.  `r1ok` at `c` gives `row1 c ≤ row1 (parent₀ c) + 1`, and the
`nextrel0`-parent is unique, so `parent₀ c = j0`; the `nextrel1` minimality
gives `row1 j1 ≤ row1 c`.  Together with `row1 j0 < row1 j1` this pins the
value. -/
theorem nextrel1_snd_succ {M : PairSeq} (hr : r1ok M) {j0 j1 : ℕ}
    (h : nextrel1 M j0 j1) : entry M 1 j1 = entry M 1 j0 + 1 := by
  obtain ⟨hj0, hj1, hlt, hincr, hle0, hmin⟩ := h
  -- the first step of the row-`0` ancestor chain out of `j0`
  obtain ⟨c, hstep, hchain⟩ :
      ∃ c, nextrel0 M j0 c ∧ Relation.ReflTransGen (nextrel0 M) c j1 := by
    rcases Relation.ReflTransGen.cases_head hle0.2.2 with he | h
    · exact absurd he (by omega)
    · exact h
  have hcj0 : j0 < c := hstep.2.2.1
  have hclen : c < M.length := hstep.2.1
  have hcj1 : le0 M c j1 := ⟨hclen, hj1, hchain⟩
  have h1 : entry M 1 j1 ≤ entry M 1 c := hmin c ⟨hcj0, hcj1⟩
  -- `r1ok` at `c`: its row-`0` climbing parent is the (unique) `nextrel0` parent `j0`
  have hc0 : 0 < (M.getD c (0, 0)).1 := by
    have := hstep.2.2.2.1
    rw [entry_zero, entry_zero] at this
    omega
  obtain ⟨k, hkc, hk1, hkmin, hk2⟩ := hr c hclen hc0
  have hnk : nextrel0 M k c := by
    refine ⟨by omega, hclen, hkc, ?_, ?_⟩
    · rw [entry_zero, entry_zero]; omega
    · intro l hl
      rw [entry_zero, entry_zero]
      exact hkmin l hl.1 hl.2
  have hkj0 : k = j0 := nextrel0_unique hnk hstep
  have h2 : entry M 1 c ≤ entry M 1 j0 + 1 := by
    rw [entry_one, entry_one, ← hkj0]
    exact hk2
  omega

/-- **The bad-branch decomposition, uniformly in `n`.**  The parent is unique
(`hasParent`), so the block data is the same for every `n`. -/
theorem oper_bad_blocks_all {M : PairSeq} (L : 1 < M.length) (hst : steps1 M)
    (hr : r1ok M)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)) :
    ∃ (G : PairSeq) (v0 w0 : ℕ) (R : PairSeq) (d0 : ℕ) (lp : ℕ × ℕ),
      M = G ++ ((v0, w0) :: R) ++ [lp] ∧
      (∀ n, 1 ≤ n → M⟦n⟧ = G ++ copies d0 ((v0, w0) :: R) n) ∧
      (∀ x ∈ R, v0 < x.1) ∧ v0 < lp.1 ∧
      ((d0 = 0 ∧ lp.2 = 0 ∧ lp.1 = v0 + 1)
        ∨ (0 < d0 ∧ lp.2 = w0 + 1 ∧ lp.1 = v0 + d0
            ∧ nextrel1 M G.length (M.length - 1))) := by
  obtain ⟨G, v0, w0, R, d0, lp, hM1, -, R_gt, lp_gt, disj, hnR⟩ :=
    oper_bad_blocks (n := 1) L hz hp le_rfl
  -- the dropped column is the last column of `M`
  have hlpM : lp = M.getD (M.length - 1) (0, 0) := by
    conv_rhs => rw [hM1]
    exact (getD_last_of_snoc _ _).symm
  -- positional data used by the `idx1 = 0` branch
  have hM1' : M = G ++ (((v0, w0) :: R) ++ [lp]) := by rw [hM1, List.append_assoc]
  have hlenM : M.length = G.length + (R.length + 2) := by
    rw [hM1']; simp
  have hGd : M.getD G.length (0, 0) = (v0, w0) := by
    have h := getD_append_right' G (((v0, w0) :: R) ++ [lp]) 0
    rw [← hM1'] at h
    simpa using h
  have hGd1 : M.getD (G.length + 1) (0, 0) = (R ++ [lp]).getD 0 (0, 0) := by
    have h := getD_append_right' G (((v0, w0) :: R) ++ [lp]) 1
    rw [← hM1'] at h
    simpa using h
  -- the `idx1 = 0` branch pins `lp.2 = 0` and `lp.1 = v0 + 1`
  have hdisj' : (d0 = 0 ∧ lp.2 = 0 ∧ lp.1 = v0 + 1)
      ∨ (0 < d0 ∧ lp.2 = w0 + 1 ∧ lp.1 = v0 + d0
          ∧ nextrel1 M G.length (M.length - 1)) := by
    rcases disj with ⟨h0, hi⟩ | ⟨h1, h2, h3, hn1⟩
    · have hlp2 : lp.2 = 0 := by
        unfold idx1 at hi
        split at hi
        · exact absurd hi one_ne_zero
        · rw [hlpM, ← entry_one]; omega
      refine Or.inl ⟨h0, hlp2, ?_⟩
      -- the row-`0` parent is at `G.length`, so no column in between dips below `lp.1`
      have hn0 : nextrel0 M G.length (M.length - 1) := by
        have := hnR
        rw [hi, nextR_zero_iff] at this
        exact this
      have hj1 : M.length - 1 = G.length + 1 + R.length := by omega
      have hstep : entry M 0 (G.length + 1) ≤ entry M 0 G.length + 1 := by
        have := steps1_iff.1 hst G.length (by omega)
        rw [entry_zero, entry_zero]
        exact this
      have hv0 : entry M 0 G.length = v0 := by rw [entry_zero, hGd]
      have hlp1 : lp.1 = entry M 0 (M.length - 1) := by rw [entry_zero, ← hlpM]
      have hmin : entry M 0 (M.length - 1) ≤ entry M 0 (G.length + 1) := by
        rcases Nat.eq_or_lt_of_le (show G.length + 1 ≤ M.length - 1 by omega) with he | hlt
        · rw [← he]
        · exact hn0.2.2.2.2 (G.length + 1) ⟨by omega, hlt⟩
      omega
    · refine Or.inr ⟨h1, ?_, h3, hn1⟩
      have hs := nextrel1_snd_succ hr hn1
      rw [entry_one, entry_one, ← hlpM, hGd] at hs
      exact hs
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

/-! ## Part 4 — the exact-copy (`d0 = 0`) half of the crux

Here the copies are *identical* (`shiftr0 0 = id`), so `M⟦n⟧` repeats the block
`blk = (v0,w0) :: R` verbatim.  The engine is **CNF**: inside a standard form
the level-`v0` siblings are `≤o`-non-increasing, so every further sibling of
the `blk` root either drops strictly below `blk` (done at once) or reproduces
it exactly (recurse on the strictly shorter remainder). -/

/-- **Splice.**  A strictly smaller argument block stays smaller once the
tails are attached, provided the left tail re-opens at or below the block base
while every column of the right block is strictly above it. -/
theorem seqlex_splice : ∀ {A B : PairSeq}, seqlex A B →
    ∀ {U : PairSeq}, (U = [] ∨ ∀ x ∈ B, pairlt (U.headI) x) →
    ∀ (C : PairSeq), seqlex (A ++ U) (B ++ C) := by
  intro A
  induction A with
  | nil =>
    intro B h U hU C
    rcases B with _ | ⟨b0, B'⟩
    · exact absurd h (by simp)
    · rcases U with _ | ⟨u, U'⟩
      · simp
      · refine Or.inl ?_
        rcases hU with h' | h'
        · exact absurd h' (by simp)
        · simpa using h' b0 (by simp)
  | cons a A' ihA =>
    intro B h U hU C
    rcases B with _ | ⟨b0, B'⟩
    · exact absurd h (by simp)
    · rw [seqlex_cons_cons] at h
      rcases h with hp | ⟨rfl, hs⟩
      · exact Or.inl hp
      · refine Or.inr ⟨rfl, ihA hs ?_ C⟩
        rcases hU with h' | h'
        · exact Or.inl h'
        · exact Or.inr (fun x hx => h' x (List.mem_cons_of_mem _ hx))

/-- The block split at the base level: `R` is exactly the leading run above
`v0` and `Y` exactly the rest. -/
theorem split_block {v0 : ℕ} {R Y : PairSeq} (hRgt : ∀ x ∈ R, v0 < x.1)
    (hYhd : Y = [] ∨ ¬ v0 < (Y.headI).1) :
    (R ++ Y).takeWhile (fun q => v0 < q.1) = R ∧
    (R ++ Y).dropWhile (fun q => v0 < q.1) = Y := by
  have hR' : ∀ x ∈ R, (fun q : ℕ × ℕ => decide (v0 < q.1)) x = true := by
    intro x hx; simpa using hRgt x hx
  rcases hYhd with rfl | hY
  · exact ⟨by simpa using List.takeWhile_eq_self_iff.2 hR',
      by simpa using List.dropWhile_eq_nil_iff.2 hR'⟩
  · rcases Y with _ | ⟨y, Y'⟩
    · exact ⟨by simpa using List.takeWhile_eq_self_iff.2 hR',
        by simpa using List.dropWhile_eq_nil_iff.2 hR'⟩
    · simp only [List.headI] at hY
      exact ⟨by rw [takeWhile_append_all hR']; simp [hY],
        by rw [dropWhile_append_all hR']; simp [hY]⟩

/-- **Exact-copy domination (`d0 = 0`).**  The level-`v0` remainder `Y` after a
block `blk = (v0,w0) :: R` of a CNF standard form is dominated by finitely many
verbatim copies of `blk`. -/
theorem copy_dom_zero : ∀ (d : ℕ) (Y : PairSeq) (v0 w0 : ℕ) (R : PairSeq),
    Y.length ≤ d →
    blockok v0 ((v0, w0) :: (R ++ Y)) →
    (∀ x ∈ R, v0 < x.1) →
    (Y = [] ∨ ¬ v0 < (Y.headI).1) →
    cnf (translate ((v0, w0) :: (R ++ Y))) →
    ∃ m, 1 ≤ m ∧ sle Y (copies 0 ((v0, w0) :: R) m) := by
  intro d
  induction d with
  | zero =>
    intro Y v0 w0 R hlen _ _ _ _
    have hY : Y = [] := by
      cases Y with
      | nil => rfl
      | cons y Y' => simp at hlen
    subst hY
    exact ⟨1, le_rfl, Or.inr (by rw [copies_one]; simp)⟩
  | succ d ih =>
    intro Y v0 w0 R hlen hbo hRgt hYhd hcnf
    rcases Y with _ | ⟨y, Y'⟩
    · exact ⟨1, le_rfl, Or.inr (by rw [copies_one]; simp)⟩
    -- the head of `Y` sits exactly at level `v0`
    have hyv : y.1 = v0 := by
      have h1 : v0 ≤ y.1 := hbo.2.1 y (by simp)
      have h2 : ¬ v0 < y.1 := by
        rcases hYhd with h' | h'
        · exact absurd h' (by simp)
        · simpa using h'
      omega
    have hy : y = (v0, y.2) := Prod.ext hyv rfl
    -- split `Y'` into the descendant block `R'` and the remainder `Y''`
    set R' := Y'.takeWhile (fun q => v0 < q.1) with hR'def
    set Y'' := Y'.dropWhile (fun q => v0 < q.1) with hY''def
    have hY'split : R' ++ Y'' = Y' := List.takeWhile_append_dropWhile
    have hR'gt : ∀ x ∈ R', v0 < x.1 := by
      intro x hx
      have := List.mem_takeWhile_imp hx
      simpa using this
    have hY''hd : Y'' = [] ∨ ¬ v0 < (Y''.headI).1 := by
      rcases hd : Y'' with _ | ⟨z, Z⟩
      · exact Or.inl rfl
      · refine Or.inr ?_
        have h := List.head?_dropWhile_not (fun q : ℕ × ℕ => decide (v0 < q.1)) Y'
        rw [← hY''def, hd] at h
        simpa using h
    -- the two `translate` shapes
    have hTy : translate (y :: Y') = P y.2 (translate R') (translate Y'') := by
      rw [hy]
      have : ((v0, y.2) :: R') ++ Y'' = (v0, y.2) :: Y' := by
        rw [List.cons_append, hY'split]
      rw [← this]
      exact translate_block_append hR'gt hY''hd
    have hTall : translate ((v0, w0) :: (R ++ (y :: Y')))
        = P w0 (translate R) (translate (y :: Y')) := by
      have : ((v0, w0) :: R) ++ (y :: Y') = (v0, w0) :: (R ++ (y :: Y')) := by
        rw [List.cons_append]
      rw [← this]
      exact translate_block_append hRgt hYhd
    rw [hTall, hTy] at hcnf
    obtain ⟨cR, hsib, ctail⟩ := cnf_P_P.1 hcnf
    -- CNF at the sibling boundary: `y.2 ≤ w0`
    have hy2 : y.2 ≤ w0 := by
      by_contra hcon
      exact hsib (olt_P_P.2 (Or.inl (by omega)))
    rcases Nat.lt_or_ge y.2 w0 with hlt | hge
    · -- strictly smaller sibling: one copy already dominates
      refine ⟨1, le_rfl, Or.inr ?_⟩
      rw [copies_one, hy]
      exact Or.inl (by unfold pairlt; omega)
    · -- equal subscripts: CNF compares the two bodies
      have hy2eq : y.2 = w0 := by omega
      have hyw : y = (v0, w0) := by rw [hy, hy2eq]
      have hnolt : ¬ (translate R <o translate R') := by
        intro hcon
        exact hsib (olt_P_P.2 (Or.inr (Or.inl ⟨hy2eq.symm, hcon⟩)))
      -- the two bodies are depth-`v0+1` blocks
      have hsp := split_block hRgt hYhd
      have hboY : blockok v0 (y :: Y') := by
        have := blockok_tail (d := v0) (y := w0) (r := R ++ (y :: Y')) hbo
        rwa [hsp.2] at this
      have hboR : blockok (v0 + 1) R := by
        have := blockok_arg (d := v0) (y := w0) (r := R ++ (y :: Y')) hbo
        rwa [hsp.1] at this
      have hboR' : blockok (v0 + 1) R' := by
        have hboY' : blockok v0 ((v0, y.2) :: Y') := by rw [← hy]; exact hboY
        exact blockok_arg hboY'
      by_cases hRR : R' = R
      · -- the sibling reproduces the block: recurse on the remainder
        have hYeq : y :: Y' = ((v0, w0) :: R) ++ Y'' := by
          rw [hyw, List.cons_append, ← hY'split, hRR]
        have hlen'' : Y''.length ≤ d := by
          have h1 : (R' ++ Y'').length = Y'.length := by rw [hY'split]
          simp only [List.length_append] at h1
          simp only [List.length_cons] at hlen
          omega
        have hbo'' : blockok v0 ((v0, w0) :: (R ++ Y'')) := by
          rw [← List.cons_append, ← hYeq]; exact hboY
        have hcnf'' : cnf (translate ((v0, w0) :: (R ++ Y''))) := by
          rw [← List.cons_append, ← hYeq, hTy]
          exact ctail
        obtain ⟨m, hm, hsle⟩ := ih Y'' v0 w0 R hlen'' hbo'' hRgt hY''hd hcnf''
        refine ⟨m + 1, by omega, ?_⟩
        rw [copies_succ_cons, shiftr0_zero, hYeq, ← List.cons_append]
        exact (sle_append_cancel _).2 hsle
      · -- the sibling body is strictly smaller: two copies suffice
        have hslR : seqlex R' R := by
          rcases seqlex_total R' R with he | h | h
          · exact absurd he hRR
          · exact h
          · exact absurd (seqlex_imp_olt (v0 + 1) R R' hboR hboR' h) hnolt
        refine ⟨2, by omega, Or.inr ?_⟩
        rw [show (2 : ℕ) = 1 + 1 from rfl, copies_succ_cons, shiftr0_zero, copies_one,
          hyw]
        refine Or.inr ⟨rfl, ?_⟩
        rw [← hY'split]
        refine seqlex_splice hslR ?_ _
        rcases hY''hd with h | h
        · exact Or.inl h
        · refine Or.inr (fun x hx => ?_)
          have h1 := hRgt x hx
          unfold pairlt; omega

/-! ## Part 5 — the `d0 = 0` half of the crux -/

theorem copies_zero_succ (blk : PairSeq) (m : ℕ) :
    copies 0 blk (m + 1) = copies 0 blk m ++ blk := by
  unfold copies
  rw [List.range_succ, List.flatMap_append]
  simp

/-- When `d0 = 0` the dropped column is `lp = (v0+1, 0)`, so the continuation
`q :: S` of `N` re-opens at or below `v0`; `copy_dom_zero` then bounds its
level-`v0` part by finitely many copies of the block, and the part below `v0`
is `pairlt`-smaller than every column of the copies. -/
theorem crux_zero {G R S : PairSeq} {v0 w0 : ℕ} {lp q : ℕ × ℕ}
    (hN : ST_PS ((G ++ ((v0, w0) :: R)) ++ q :: S))
    (hRgt : ∀ x ∈ R, v0 < x.1)
    (hlp2 : lp.2 = 0) (hlp1 : lp.1 = v0 + 1)
    (hq : pairlt q lp) :
    ∃ m, 1 ≤ m ∧ sle (q :: S) (copies 0 ((v0, w0) :: R) m) := by
  classical
  -- the continuation re-opens at or below `v0`
  have hqv : q.1 ≤ v0 := by
    rcases hq with h | ⟨-, h⟩
    · omega
    · omega
  rcases Nat.lt_or_ge q.1 v0 with hlt | hge
  · exact ⟨1, le_rfl, Or.inr (by
      rw [copies_one]; exact Or.inl (by unfold pairlt; omega))⟩
  have hqv0 : q.1 = v0 := by omega
  -- split the continuation at the first column strictly below `v0`
  set Y := (q :: S).takeWhile (fun p => v0 ≤ p.1) with hYdef
  set V := (q :: S).dropWhile (fun p => v0 ≤ p.1) with hVdef
  have hYV : Y ++ V = q :: S := List.takeWhile_append_dropWhile
  have hYcons : Y = q :: S.takeWhile (fun p => v0 ≤ p.1) := by
    rw [hYdef, List.takeWhile_cons_of_pos (by simpa using hqv0.ge)]
  have hYhead : (Y.headI).1 = v0 := by rw [hYcons]; simpa using hqv0
  have hYge : ∀ x ∈ Y, v0 ≤ x.1 := by
    intro x hx
    have := List.mem_takeWhile_imp hx
    simpa using this
  have hVhd : V = [] ∨ ∃ z Z, V = z :: Z ∧ z.1 < v0 := by
    rcases hd : V with _ | ⟨z, Z⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨z, Z, rfl, ?_⟩
      have h := List.head?_dropWhile_not (fun p : ℕ × ℕ => decide (v0 ≤ p.1)) (q :: S)
      rw [← hVdef, hd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 ≤ z.1) := by simpa using h
      omega
  -- the level-`v0` window `blk ++ Y` is an infix block of `N`
  have hNsplit : (G ++ ((v0, w0) :: R)) ++ q :: S
      = (G ++ (((v0, w0) :: R) ++ Y)) ++ V := by
    rw [← hYV]; simp
  have hstN : steps1 ((G ++ ((v0, w0) :: R)) ++ q :: S) := (blockok_ST_PS hN).2.2
  have hstBY : steps1 (((v0, w0) :: R) ++ Y) := by
    rw [hNsplit] at hstN
    exact (steps1_append.1 (steps1_append.1 hstN).1).2.1
  have hallBY : ∀ x ∈ ((v0, w0) :: R) ++ Y, v0 ≤ x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact le_rfl
      · exact (hRgt x hx).le
    · exact hYge x hx
  have hbo : blockok v0 (((v0, w0) :: R) ++ Y) := ⟨by intro _; rfl, hallBY, hstBY⟩
  -- CNF of the window: prefix-closure plus `cnf_tail`
  have hcnfN : cnf (translate ((G ++ ((v0, w0) :: R)) ++ q :: S)) := cnf_ST_PS hN
  have hcnfW : cnf (translate ((v0, w0) :: (R ++ Y))) := by
    have h1 : cnf (translate ((G ++ (((v0, w0) :: R) ++ Y)) ++ V)) := by
      rw [← hNsplit]; exact hcnfN
    have h2 : cnf (translate (G ++ (((v0, w0) :: R) ++ Y))) := by
      have := cnf_take h1 (G ++ (((v0, w0) :: R) ++ Y)).length
      rwa [List.take_left] at this
    have h3 : cnf (translate (G ++ ((v0, w0) :: (R ++ Y)))) := by
      rwa [List.cons_append] at h2
    exact cnf_tail (t := (v0, w0)) (T' := R ++ Y)
      (fun x hx => hallBY x (by
        rcases List.mem_append.1 hx with h | h
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
        · exact List.mem_append_right _ h)) G h3
  -- the exact-copy domination
  obtain ⟨m, hm, hsle⟩ := copy_dom_zero Y.length Y v0 w0 R le_rfl
    (by rwa [List.cons_append] at hbo) hRgt (Or.inr (by rw [hYhead]; omega))
    hcnfW
  refine ⟨m + 1, by omega, Or.inr ?_⟩
  rw [← hYV, copies_zero_succ]
  rcases hsle with heq | hlt
  · rw [← heq, seqlex_append_cancel]
    rcases hVhd with hV | ⟨z, Z, hV, hz⟩
    · rw [hV]; simp
    · rw [hV]; exact Or.inl (by unfold pairlt; omega)
  · refine seqlex_splice hlt ?_ _
    rcases hVhd with hV | ⟨z, Z, hV, hz⟩
    · exact Or.inl hV
    · refine Or.inr (fun x hx => ?_)
      have := copies_v0_le (fun y hy => (hRgt y hy).le) 0 m x hx
      rw [hV]
      unfold pairlt
      simp only [List.headI]
      omega

/-- A standard form `N` that agrees with the host `M` on the *whole* good
prefix `G` and bad block `blk = (v0,w0) :: R`, and then continues with a column
strictly below the dropped column `lp`, is dominated by finitely many
**ascending** copies of `blk`. -/
def AscCrux : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ} {lp q : ℕ × ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [lp]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ q :: S) →
    (∀ x ∈ R, v0 < x.1) →
    0 < d0 → lp.2 = w0 + 1 → lp.1 = v0 + d0 →
    nextrel1 ((G ++ ((v0, w0) :: R)) ++ [lp]) G.length
      (G ++ ((v0, w0) :: R)).length →
    pairlt q lp →
    ∃ m, 1 ≤ m ∧ sle (q :: S) (shiftr0 d0 (copies d0 ((v0, w0) :: R) m))

/-- By `nextrel1_snd_succ` the dropped column is `lp = (v0+d0, w0+1)`, so a
continuation column `q` with `pairlt q lp` satisfies `q ≤ (v0+d0, w0)` — the
head of the first ascending copy. -/
def AscCrux1 : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ (v0 + d0, w0) :: S) →
    (∀ x ∈ R, v0 < x.1) → 0 < d0 →
    nextrel1 ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) G.length
      (G ++ ((v0, w0) :: R)).length →
    ∃ m, 1 ≤ m ∧ sle ((v0 + d0, w0) :: S) (shiftr0 d0 (copies d0 ((v0, w0) :: R) m))

/-! ## Part 6 — the ascending (`d0 > 0`) half: reduction to ONE `≤o`

Because the ascending copies are **nested** (`blk_{k+1}` sits strictly inside
`blk_k`), matching the first copy already exhausts everything the continuation
of `N` can reach: the next copy root is at level `v0 + 2*d0`, strictly deeper
than any column `S` still has after leaving `q`'s subtree. -/

theorem shiftr0_length (d : ℕ) (X : PairSeq) : (shiftr0 d X).length = X.length := by
  unfold shiftr0; simp

theorem mem_shiftr0_le {d : ℕ} (e : ℕ) {X : PairSeq} (h : ∀ x ∈ X, d ≤ x.1) :
    ∀ x ∈ shiftr0 e X, d + e ≤ x.1 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := mem_shiftr0.1 hx
  have := h p hp
  simp only []
  omega

/-- `shiftr0` commutes with the copy tower (shifting all copies = shifting the
block). -/
theorem shiftr0_copies (d : ℕ) (blk : PairSeq) (n : ℕ) :
    shiftr0 d (copies d blk n) = copies d (shiftr0 d blk) n := by
  unfold copies shiftr0
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_map, List.map_map]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.mk.injEq, and_true]
  omega

/-- `S_hi := S.takeWhile (v0+d0 < ·.1)` is the descendant block of the ascending
copy root `q = (v0+d0, w0)` inside `N`, and `R ++ copies d0 blk' m` is the
descendant block of the *original* block root inside the host expansion `M⟦m+1⟧`
(`blk' = shiftr0 d0 blk`).  The *collapsed argument* is dominated by the shifted
host argument at some stage `m`:

    S_hi  ≤lex  shiftr0 d0 (R ++ copies d0 blk' m). -/
def AscArgDom : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ (v0 + d0, w0) :: S) →
    (∀ x ∈ R, v0 < x.1) → 0 < d0 →
    nextrel1 ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) G.length
      (G ++ ((v0, w0) :: R)).length →
    ∃ m, sle (S.takeWhile fun p => v0 + d0 < p.1)
      (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R)) m))

theorem shiftr0_append (d : ℕ) (A B : PairSeq) :
    shiftr0 d (A ++ B) = shiftr0 d A ++ shiftr0 d B := List.map_append

theorem copies_succ_back (d : ℕ) (blk : PairSeq) (n : ℕ) :
    copies d blk (n + 1) = copies d blk n ++ shiftr0 (n * d) blk := by
  unfold copies
  rw [List.range_succ, List.flatMap_append]
  simp

/-- **The ascending branch needs only ONE extra copy beyond the witness**:
`AscArgDom` at stage `m` closes it at `m + 2` copies. -/
theorem asc_crux1_of_argdom (H : AscArgDom) : AscCrux1 := by
  intro G R S v0 w0 d0 hM hN hRgt hd hnr
  classical
  obtain ⟨m, hdom⟩ := H hM hN hRgt hd hnr
  set Shi := S.takeWhile (fun p => v0 + d0 < p.1) with hShidef
  set Slo := S.dropWhile (fun p => v0 + d0 < p.1) with hSlodef
  have hSsplit : Shi ++ Slo = S := List.takeWhile_append_dropWhile
  set blk' := shiftr0 d0 ((v0, w0) :: R) with hblk'
  have hblk'cons : blk' = (v0 + d0, w0) :: shiftr0 d0 R := by
    rw [hblk', shiftr0_cons]
  -- every column of the host argument is strictly above `v0`
  have hDmGt : ∀ x ∈ R ++ copies d0 blk' m, v0 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hRgt x hx
    · rw [hblk'cons] at hx
      have := copies_v0_le (v0 := v0 + d0) (w0 := w0) (R := shiftr0 d0 R)
        (mem_shiftr0_le d0 (fun y hy => (hRgt y hy).le)) d0 m x hx
      omega
  -- the tail below the copy root
  have hSloHd : Slo = [] ∨ (Slo.headI).1 ≤ v0 + d0 := by
    rcases hdd : Slo with _ | ⟨z, Z⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h := List.head?_dropWhile_not (fun p : ℕ × ℕ => decide (v0 + d0 < p.1)) S
      rw [← hSlodef, hdd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 + d0 < z.1) := by simpa using h
      simp only [List.headI]
      omega
  refine ⟨m + 2, by omega, ?_⟩
  -- unfold the target into: copy root, host argument, one further copy
  have hinner : shiftr0 d0 (copies d0 blk' (m + 1))
      = shiftr0 d0 (copies d0 blk' m) ++ shiftr0 d0 (shiftr0 (m * d0) blk') := by
    rw [copies_succ_back, shiftr0_append]
  have htgt : shiftr0 d0 (copies d0 ((v0, w0) :: R) (m + 2))
      = (v0 + d0, w0) :: (shiftr0 d0 (R ++ copies d0 blk' m)
          ++ shiftr0 d0 (shiftr0 (m * d0) blk')) := by
    rw [shiftr0_copies, ← hblk', copies_succ_front, hinner, shiftr0_append,
      List.append_assoc]
    conv_lhs => rw [hblk'cons]
    rw [List.cons_append, ← hblk'cons]
  rw [htgt]
  have hEne : shiftr0 d0 (shiftr0 (m * d0) blk') ≠ [] := by
    rw [hblk'cons]; simp [shiftr0]
  have hEhd : ((shiftr0 d0 (shiftr0 (m * d0) blk')).headI).1 = v0 + d0 + m * d0 + d0 := by
    rw [hblk'cons, shiftr0_cons, shiftr0_cons]
    simp
  show sle ([((v0 + d0 : ℕ), (w0 : ℕ))] ++ S)
    ([((v0 + d0 : ℕ), (w0 : ℕ))] ++ _)
  rw [sle_append_cancel]
  rcases hdom with heq | hlt
  · -- the argument is reproduced verbatim: one further copy dominates the drop
    have hS : S = shiftr0 d0 (R ++ copies d0 blk' m) ++ Slo := by
      rw [← hSsplit, heq]
    rw [hS]
    refine (sle_append_cancel _).2 ?_
    rcases hSloHd with h | h
    · rw [h]; exact Or.inr (by simpa using hEne)
    · rcases hdd : Slo with _ | ⟨z, Z⟩
      · exact Or.inr (by simpa using hEne)
      · rcases hb : shiftr0 d0 (shiftr0 (m * d0) blk') with _ | ⟨b, B⟩
        · exact absurd hb hEne
        · refine Or.inr (Or.inl ?_)
          rw [hdd] at h
          rw [hb] at hEhd
          simp only [List.headI] at h hEhd
          unfold pairlt
          omega
  · -- strictly smaller argument: splice the sub-`v0+d0` tail past it
    refine Or.inr ?_
    rw [← hSsplit]
    refine seqlex_splice hlt ?_ _
    rcases hSloHd with h | h
    · exact Or.inl h
    · refine Or.inr (fun x hx => ?_)
      obtain ⟨y, hy, rfl⟩ := mem_shiftr0.1 hx
      have := hDmGt y hy
      unfold pairlt
      simp only []
      omega

/-! ## Part 7 — assembly -/

/-- **The head step of the ascending crux**: only the `q = (v0+d0,w0)` case
survives. -/
theorem asc_head_step (H : AscCrux1) : AscCrux := by
  intro G R S v0 w0 d0 lp q hM hN hRgt hd hlp2 hlp1 hnr hq
  have hlpe : lp = (v0 + d0, w0 + 1) := Prod.ext hlp1 hlp2
  by_cases hqe : q = (v0 + d0, w0)
  · subst hqe
    exact H (hlpe ▸ hM) hN hRgt hd (hlpe ▸ hnr)
  · refine ⟨1, le_rfl, Or.inr ?_⟩
    rw [copies_one, shiftr0_cons]
    refine Or.inl ?_
    rw [hlpe] at hq
    have : q.1 < v0 + d0 ∨ (q.1 = v0 + d0 ∧ q.2 < w0 + 1) := hq
    have hne : ¬ (q.1 = v0 + d0 ∧ q.2 = w0) := by
      intro ⟨h1, h2⟩; exact hqe (Prod.ext h1 h2)
    unfold pairlt
    simp only []
    omega

/-- **Branch `bad`**. -/
theorem seqlex_cof_bad (H : AscCrux) {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
  have hp := hasParent_last_ST_PS hM (by omega) hz
  obtain ⟨G, v0, w0, R, d0, lp, hMeq, hMn, R_gt, lp_gt, disj⟩ :=
    oper_bad_blocks_all L (blockok_ST_PS hM).2.2 (r1ok_ST_PS hM) hz hp
  rcases seqlex_snoc_cases (D := G ++ ((v0, w0) :: R)) (lp := lp) (N := N)
      (by rw [← hMeq]; exact h) with hle | ⟨q, S, hNeq, hq⟩
  · exact ⟨1, le_rfl, by rw [hMn 1 le_rfl, copies_one]; exact hle⟩
  · obtain ⟨m, hm, hsle⟩ : ∃ m, 1 ≤ m ∧
        sle (q :: S) (shiftr0 d0 (copies d0 ((v0, w0) :: R) m)) := by
      rcases disj with ⟨rfl, hlp2, hlp1⟩ | ⟨hd, hw, hlpe, hn1⟩
      · simp only [shiftr0_zero]
        exact crux_zero (hNeq ▸ hN) R_gt hlp2 hlp1 hq
      · have hlen : M.length - 1 = (G ++ ((v0, w0) :: R)).length := by
          rw [hMeq]; simp
        have hnr : nextrel1 ((G ++ ((v0, w0) :: R)) ++ [lp]) G.length
            (G ++ ((v0, w0) :: R)).length := by
          rw [← hlen, ← hMeq]; exact hn1
        exact H (hMeq ▸ hM) (hNeq ▸ hN) R_gt hd hw hlpe hnr hq
    refine ⟨m + 1, by omega, ?_⟩
    rw [hMn (m + 1) (by omega), copies_succ_front, hNeq, List.append_assoc]
    exact (sle_append_cancel _).2 ((sle_append_cancel _).2 hsle)

/-- Modulo the crux, the `seqlex` form of cofinality holds. -/
theorem seqlex_cofinality_of_crux (H : AscCrux) : SeqlexCofinality := by
  intro M N hM hN h
  by_cases hL : M.length - 1 = 0
  · exact seqlex_cof_short hL h
  · by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
    · exact seqlex_cof_zero (by omega) hz h
    · exact seqlex_cof_bad H hM hN (by omega) hz h

/-- **PSS Bachmann cofinality, modulo `AscCrux1`.** -/
theorem pss_cofinality_of_crux (H : AscCrux1) {M N : PairSeq}
    (hM : ST_PS M) (hN : ST_PS N) (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  pss_cofinality_of_seqlex (seqlex_cofinality_of_crux (asc_head_step H)) hM hN h

/-- **PSS Bachmann cofinality from `AscArgDom`.** -/
theorem pss_cofinality_of_argdom (H : AscArgDom) {M N : PairSeq}
    (hM : ST_PS M) (hN : ST_PS N) (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  pss_cofinality_of_crux (asc_crux1_of_argdom H) hM hN h

end YAPSS
