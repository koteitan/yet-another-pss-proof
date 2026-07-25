/-
**Every expansion step strictly decreases the measure.**

The branches of `oper` unfolded, the block decomposition `oper_bad_blocks` of
the copy-tiling branch, and the decrease theorem `m_step_decreases`:
`translate (M⟦n⟧) <o translate M` for every `M` with `1 < |M|` and `1 ≤ n`.
-/
import Term

namespace YAPSS

open Three

/-! ### The branches of `oper`, unfolded -/

theorem oper_eq_self_of_short {M : PairSeq} (n : ℕ) (h : M.length - 1 = 0) :
    M⟦n⟧ = M := by
  simp only [oper]
  rw [if_pos h]

/-- `Pred` branch 1: the last pair is `(0,0)`. -/
theorem oper_eq_pred_of_zero {M : PairSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0) :
    M⟦n⟧ = Pred M := by
  simp only [oper]
  rw [if_neg hL, if_pos hz]

/-- `Pred` branch 2: no unique parent in row `i1`. -/
theorem oper_eq_pred_of_noParent {M : PairSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hp : ¬ hasParent M (idx1 M (M.length - 1)) (M.length - 1)) :
    M⟦n⟧ = Pred M := by
  simp only [oper]
  rw [if_neg hL, if_neg hz, if_pos hp]

/-- The bad branch of `M⟦n⟧`, unfolded (`δ1 = 0` since `idx1 ≤ 1`). -/
theorem oper_bad_unfold {M : PairSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)) :
    M⟦n⟧ = M.take (parent M (idx1 M (M.length - 1)) (M.length - 1))
      ++ (List.range n).flatMap fun k =>
          (List.range' (parent M (idx1 M (M.length - 1)) (M.length - 1))
            (M.length - 1 - parent M (idx1 M (M.length - 1)) (M.length - 1))).map
            fun j =>
              (entry M 0 j + k * (if 0 < idx1 M (M.length - 1)
                  then entry M 0 (M.length - 1)
                    - entry M 0 (parent M (idx1 M (M.length - 1)) (M.length - 1))
                  else 0),
               entry M 1 j) := by
  have d1z : ¬ 1 < idx1 M (M.length - 1) := by
    have := idx1_le1 M (M.length - 1); omega
  simp only [oper]
  rw [if_neg hL, if_neg hz, if_neg (not_not_intro hp), if_neg d1z]
  simp

/-- `oper` is the identity on lists of length `≤ 1`. -/
theorem oper_eq_self_short {M : PairSeq} (n : ℕ) (h : M.length ≤ 1) :
    M⟦n⟧ = M :=
  oper_eq_self_of_short n (by omega)

/-! ## Appending a pair strictly increases the measure

The analogue of PrSS `omap_snoc_increase`: extending a pair sequence on the
right strictly increases its translation.  Hence dropping the last pair
strictly decreases it, which covers the two `Pred` branches of `M⟦n⟧`. -/

theorem translate_snoc_increase (C : PairSeq) (m : ℕ × ℕ) :
    translate C <o translate (C ++ [m]) := by
  induction C using translate.induct with
  | case1 => simp [translate]
  | case2 p rest ih1 ih2 =>
    by_cases allp : ∀ x ∈ rest, p.1 < x.1
    · -- the whole `rest` is below `p`: it is one block; the new pair extends
      -- it or starts a sibling
      have allp' : ∀ x ∈ rest, (fun q : ℕ × ℕ => decide (p.1 < q.1)) x = true := by
        intro x hx; simpa using allp x hx
      have tw : rest.takeWhile (fun q => p.1 < q.1) = rest :=
        List.takeWhile_eq_self_iff.2 allp'
      have dw : rest.dropWhile (fun q => p.1 < q.1) = [] :=
        List.dropWhile_eq_nil_iff.2 allp'
      by_cases hm : p.1 < m.1
      · have all' : ∀ x ∈ rest ++ [m], (fun q : ℕ × ℕ => decide (p.1 < q.1)) x = true := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact allp' x hx
          · simp at hx
            simpa [hx] using hm
        have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1) = rest ++ [m] :=
          List.takeWhile_eq_self_iff.2 all'
        have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1) = [] :=
          List.dropWhile_eq_nil_iff.2 all'
        have key : translate rest <o translate (rest ++ [m]) := by
          rw [tw] at ih1; exact ih1
        have eL : translate (p :: rest) = P p.2 (translate rest) Z :=
          translate_single_tree allp
        have eR : translate (p :: (rest ++ [m]))
            = P p.2 (translate (rest ++ [m])) Z :=
          translate_single_tree (by
            intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact allp x hx
            · simp at hx
              simpa [hx] using hm)
        rw [List.cons_append, eL, eR]
        exact olt_P_b _ _ _ key
      · have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1) = rest := by
          rw [takeWhile_append_all allp']
          simp [hm]
        have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1) = [m] := by
          rw [dropWhile_append_all allp']
          simp [hm]
        have eL : translate (p :: rest) = P p.2 (translate rest) Z :=
          translate_single_tree allp
        have eR : translate (p :: (rest ++ [m]))
            = P p.2 (translate rest) (translate [m]) := by
          rw [translate, tw', dw']
        rw [List.cons_append, eL, eR]
        exact olt_P_c _ _ (by simp [translate])
    · push Not at allp
      obtain ⟨x, hx, hnx⟩ := allp
      have hnx' : ¬ (fun q : ℕ × ℕ => decide (p.1 < q.1)) x = true := by simpa using hnx
      have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1)
          = rest.takeWhile (fun q => p.1 < q.1) := takeWhile_append_not hx hnx'
      have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1)
          = rest.dropWhile (fun q => p.1 < q.1) ++ [m] := dropWhile_append_not hx hnx'
      have eL : translate (p :: rest)
          = P p.2 (translate (rest.takeWhile fun q => p.1 < q.1))
              (translate (rest.dropWhile fun q => p.1 < q.1)) := by
        rw [translate]
      have eR : translate (p :: (rest ++ [m]))
          = P p.2 (translate (rest.takeWhile fun q => p.1 < q.1))
              (translate ((rest.dropWhile fun q => p.1 < q.1) ++ [m])) := by
        rw [translate, tw', dw']
      rw [List.cons_append, eL, eR]
      exact olt_P_c _ _ ih2

theorem translate_dropLast_decrease {C : PairSeq} (h : C ≠ []) :
    translate C.dropLast <o translate C := by
  conv_rhs => rw [← List.dropLast_append_getLast h]
  exact translate_snoc_increase _ _

/-- Appending a pair can only *increase* (weakly) the translation of a leading
same-level block `takeWhile (fun x => a < x.1)`: either the block is unchanged
(some earlier pair already stopped it) or it is extended by the new pair (then
`translate_snoc_increase` applies).  Used for the sibling-condition transfer
in `cnf_snoc`. -/
theorem translate_takeWhile_snoc_le (a : ℕ) (C : PairSeq) (m : ℕ × ℕ) :
    translate (C.takeWhile fun x => a < x.1)
      ≤o translate ((C ++ [m]).takeWhile fun x => a < x.1) := by
  by_cases hall : ∀ x ∈ C, a < x.1
  · have hall' : ∀ x ∈ C, (fun q : ℕ × ℕ => decide (a < q.1)) x = true := by
      intro x hx; simpa using hall x hx
    have twC : C.takeWhile (fun x => a < x.1) = C := List.takeWhile_eq_self_iff.2 hall'
    by_cases hm : a < m.1
    · have e : (C ++ [m]).takeWhile (fun x => a < x.1) = C ++ [m] := by
        apply List.takeWhile_eq_self_iff.2
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hall' x hx
        · simp at hx
          simpa [hx] using hm
      rw [twC, e]
      exact Or.inl (translate_snoc_increase _ _)
    · have e : (C ++ [m]).takeWhile (fun x => a < x.1) = C := by
        rw [takeWhile_append_all hall']
        simp [hm]
      rw [twC, e]
      exact Or.inr rfl
  · push Not at hall
    obtain ⟨x, hx, hnx⟩ := hall
    have hnx' : ¬ (fun q : ℕ × ℕ => decide (a < q.1)) x = true := by simpa using hnx
    rw [takeWhile_append_not hx hnx']
    exact Or.inr rfl

/-! ## Abstract bad-step cores -/

/-- Core for `i1 = 0` (exact copies).  A tree rooted at `(v0,w0)` with body
`R` (all above `v0`), followed by any block `T` that re-opens at or below `v0`
(the next exact copy's root), is strictly below the same tree with the body
extended by one more descendant `lp` (the dropped last pair).  The leading
argument is `R` on the left but grows to `R ++ [lp]` on the right; the number
of trailing copies (in `T`) is irrelevant. -/
theorem core_i0 {v0 w0 : ℕ} {R T : PairSeq} {lp : ℕ × ℕ}
    (hR : ∀ x ∈ R, v0 < x.1) (vl : v0 < lp.1)
    (hT : T = [] ∨ ¬ v0 < (T.headI).1) :
    translate (((v0, w0) :: R) ++ T) <o translate (((v0, w0) :: R) ++ [lp]) := by
  have lhs : translate (((v0, w0) :: R) ++ T) = P w0 (translate R) (translate T) :=
    translate_block_append hR hT
  have rhs : translate (((v0, w0) :: R) ++ [lp]) = P w0 (translate (R ++ [lp])) Z := by
    have all : ∀ x ∈ R ++ [lp], ((v0, w0) : ℕ × ℕ).1 < x.1 := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hR x hx
      · simp at hx
        simpa [hx] using vl
    calc translate (((v0, w0) :: R) ++ [lp]) = translate ((v0, w0) :: (R ++ [lp])) := by
          rw [List.cons_append]
      _ = P w0 (translate (R ++ [lp])) Z := translate_single_tree all
  rw [lhs, rhs]
  exact olt_P_b _ _ _ (translate_snoc_increase R lp)

/-- Core for `i1 = 1` (ascending copies).  The copy-rest `C` is itself a
single tree rooted at the same row-0 as the dropped last pair `lp` but with a
strictly smaller subscript; so `C ≺ [lp]` by subscript-first domination, and
the common bodies `(v0,w0) :: R` / `R` propagate it via BADCTX. -/
theorem core_i1 {v0 w0 : ℕ} {R : PairSeq} {c : ℕ × ℕ} {C' : PairSeq} {lp : ℕ × ℕ}
    (hR : ∀ x ∈ R, v0 < x.1)
    (Cge : ∀ x ∈ C', c.1 ≤ x.1)
    (Croot : c.1 = lp.1)
    (lpv : v0 < lp.1)
    (lead_lt : c.2 < lp.2) :
    translate (((v0, w0) :: R) ++ (c :: C')) <o translate (((v0, w0) :: R) ++ [lp]) := by
  -- subscript-first domination: `c :: C'` leads with subscript `c.2 < lp.2`
  have hCdom : translate (c :: C') <o translate [lp] := by
    have leadC : lead (translate (c :: C')) = c.2 := by
      rw [lead_translate]
    have : translate (c :: C') <o P lp.2 Z Z :=
      olt_P_of_lead_lt _ _ (Or.inr (by rw [leadC]; exact lead_lt))
    calc translate (c :: C') <o P lp.2 Z Z := this
      _ = translate [lp] := by
          rw [translate]
          simp [translate]
  -- propagate through the common body `R`, then through the root `(v0,w0)`
  have inner : translate (R ++ c :: C') <o translate (R ++ lp :: ([] : PairSeq)) :=
    translate_ctx_cong hCdom Croot Cge (by simp) R
  have allRC : ∀ x ∈ R ++ c :: C', ((v0, w0) : ℕ × ℕ).1 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hR x hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact lt_of_lt_of_eq lpv Croot.symm
      · exact lt_of_lt_of_le (lt_of_lt_of_eq lpv Croot.symm) (Cge x hx)
  have allRlp : ∀ x ∈ R ++ [lp], ((v0, w0) : ℕ × ℕ).1 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hR x hx
    · simp at hx
      simpa [hx] using lpv
  have lhs : translate (((v0, w0) :: R) ++ (c :: C'))
      = P w0 (translate (R ++ c :: C')) Z := by
    rw [List.cons_append]
    exact translate_single_tree allRC
  have rhs : translate (((v0, w0) :: R) ++ [lp])
      = P w0 (translate (R ++ [lp])) Z := by
    rw [List.cons_append]
    exact translate_single_tree allRlp
  rw [lhs, rhs]
  exact olt_P_b _ _ _ (by simpa using inner)

/-! ## The expansion step strictly decreases the measure: `Pred` branches

In the two degenerate branches of `M⟦n⟧` (last pair `(0,0)`, or no unique
parent in row `i1`) the step drops the last pair, so the measure decreases by
`translate_dropLast_decrease`.  The remaining (bad) branch is the genuine
core, handled separately. -/

theorem translate_oper_pred {M : PairSeq} (n : ℕ) (L : 1 < M.length)
    (br : (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0)
        ∨ ¬ hasParent M (idx1 M (M.length - 1)) (M.length - 1)) :
    translate (M⟦n⟧) <o translate M := by
  have j1ne : M.length - 1 ≠ 0 := by omega
  have hMn : M⟦n⟧ = Pred M := by
    rcases br with hz | hp
    · exact oper_eq_pred_of_zero n j1ne hz
    · by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
      · exact oper_eq_pred_of_zero n j1ne hz
      · exact oper_eq_pred_of_noParent n j1ne hz hp
  have hPred : Pred M = M.dropLast := by
    unfold Pred
    rw [if_neg (by omega)]
  rw [hMn, hPred]
  exact translate_dropLast_decrease (by
    intro h
    rw [h] at L
    simp at L)

/-! ## The bad-branch decomposition

In the genuine (bad) branch the step factors as `M = G ++ blk ++ [lp]` and
`M⟦n⟧ = G ++ (n shifted copies of blk)`, where `blk = (v0,w0) :: R` with body
`R` strictly above the root `v0`, the dropped descendant `lp` nests
(`v0 < lp.1`), and the per-copy row-0 shift `d0` either vanishes (`i1 = 0`,
exact copies) or is positive with `w0 < lp.2` and `lp.1 = v0 + d0` (`i1 = 1`,
ascending copies).  (This is the data the CNF-preservation proof needs; the
decrease lemma `translate_oper_bad` is derived from it below.) -/

theorem parent_nextR {M : PairSeq} {i j1 : ℕ} (hp : hasParent M i j1) :
    nextR M i (parent M i j1) j1 :=
  Classical.epsilon_spec hp.exists

theorem nextR_index_lt {M : PairSeq} {i j0 j1 : ℕ} (h : nextR M i j0 j1) :
    j0 < j1 := by
  unfold nextR at h
  split at h
  · exact h.2.2.1
  · exact h.2.2.1

theorem nextR_chain0 {M : PairSeq} {i j0 j1 : ℕ} (h : nextR M i j0 j1) :
    Relation.ReflTransGen (nextrel0 M) j0 j1 := by
  unfold nextR at h
  split at h
  · exact Relation.ReflTransGen.single h
  · exact h.2.2.2.2.1.2.2

theorem oper_bad_blocks {M : PairSeq} {n : ℕ} (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1))
    (_hn : 1 ≤ n) :
    ∃ (G : PairSeq) (v0 w0 : ℕ) (R : PairSeq) (d0 : ℕ) (lp : ℕ × ℕ),
      M = G ++ ((v0, w0) :: R) ++ [lp] ∧
      M⟦n⟧ = G ++ (List.range n).flatMap
        (fun k => ((v0, w0) :: R).map fun p => (p.1 + k * d0, p.2)) ∧
      (∀ x ∈ R, v0 < x.1) ∧
      v0 < lp.1 ∧
      ((d0 = 0 ∧ idx1 M (M.length - 1) = 0)
        ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0 ∧
            nextrel1 M G.length (M.length - 1))) ∧
      nextR M (idx1 M (M.length - 1)) G.length (M.length - 1) := by
  have hLen : M.length = (M.length - 1) + 1 := by omega
  -- abbreviations (kept as plain `have`-style definitions to ease rewriting)
  have np : nextR M (idx1 M (M.length - 1)) (parent M (idx1 M (M.length - 1)) (M.length - 1))
      (M.length - 1) := parent_nextR hp
  have j0lt : parent M (idx1 M (M.length - 1)) (M.length - 1) < M.length - 1 :=
    nextR_index_lt np
  have chain := nextR_chain0 np
  have iv : ∀ k, parent M (idx1 M (M.length - 1)) (M.length - 1) < k → k ≤ M.length - 1 →
      entry M 0 (parent M (idx1 M (M.length - 1)) (M.length - 1)) < entry M 0 k :=
    fun k h1 h2 => le0_interval_gt chain k ⟨h1, h2⟩
  set j1 := M.length - 1 with hj1
  set i1 := idx1 M j1 with hi1
  set j0 := parent M i1 j1 with hj0
  set d0 := (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0) with hd0
  have hsplit : List.range' j0 (j1 - j0) = j0 :: List.range' (j0 + 1) (j1 - (j0 + 1)) := by
    have h : j1 - j0 = (j1 - (j0 + 1)) + 1 := by omega
    rw [h, List.range'_succ]
  -- the components
  refine ⟨M.take j0, entry M 0 j0, entry M 1 j0,
    (List.range' (j0 + 1) (j1 - (j0 + 1))).map (fun j => (entry M 0 j, entry M 1 j)),
    d0, M.getD j1 (0, 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `M = G ++ blk ++ [lp]`
    have dropM : M.drop j0 = ((entry M 0 j0, entry M 1 j0)
        :: (List.range' (j0 + 1) (j1 - (j0 + 1))).map (fun j => (entry M 0 j, entry M 1 j)))
        ++ [M.getD j1 (0, 0)] := by
      rw [drop_eq_map_getD M j0 (0, 0)]
      have hlen' : M.length - j0 = (j1 - j0) + 1 := by omega
      have hras : List.range' j0 ((j1 - j0) + 1)
          = List.range' j0 (j1 - j0) ++ [j1] := by
        have h := List.range'_append (s := j0) (m := j1 - j0) (n := 1) (step := 1)
        rw [List.range'_one] at h
        rw [show j0 + 1 * (j1 - j0) = j1 by omega] at h
        exact h.symm
      rw [hlen', hras, List.map_append, hsplit, List.map_cons]
      rfl
    conv_lhs => rw [← List.take_append_drop j0 M]
    rw [dropM, List.append_assoc]
  · -- `M⟦n⟧ = G ++ copies`
    have B_pair : ((entry M 0 j0, entry M 1 j0)
          :: (List.range' (j0 + 1) (j1 - (j0 + 1))).map (fun j => (entry M 0 j, entry M 1 j)))
        = (List.range' j0 (j1 - j0)).map (fun j => (entry M 0 j, entry M 1 j)) := by
      rw [hsplit, List.map_cons]
    have hfun : (fun k => (List.range' j0 (j1 - j0)).map
          (fun j => (entry M 0 j + k * d0, entry M 1 j)))
        = (fun k => (((entry M 0 j0, entry M 1 j0))
            :: (List.range' (j0 + 1) (j1 - (j0 + 1))).map
                (fun j => (entry M 0 j, entry M 1 j))).map
            (fun p => (p.1 + k * d0, p.2))) := by
      funext k
      rw [B_pair, List.map_map]
      rfl
    rw [oper_bad_unfold n (by omega) hz hp]
    show M.take j0 ++ (List.range n).flatMap
        (fun k => (List.range' j0 (j1 - j0)).map
          (fun j => (entry M 0 j + k * d0, entry M 1 j))) = _
    rw [hfun]
  · -- `∀ x ∈ R, v0 < x.1`
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hj
    exact iv _ (by omega) (by omega)
  · -- `v0 < lp.1`
    exact iv j1 j0lt le_rfl
  · -- the shift disjunction
    by_cases hi : 0 < i1
    · right
      have nl1 : nextrel1 M j0 j1 := by
        have np' := np
        unfold nextR at np'
        rw [if_neg (by omega : ¬ i1 = 0)] at np'
        exact np'
      have v0lt : entry M 0 j0 < entry M 0 j1 := iv j1 j0lt le_rfl
      have hd0eq : d0 = entry M 0 j1 - entry M 0 j0 := by
        rw [hd0, if_pos hi]
      refine ⟨by omega, nl1.2.2.2.1, ?_, ?_⟩
      · show entry M 0 j1 = entry M 0 j0 + d0
        omega
      · have hlen' : (M.take j0).length = j0 := by
          rw [List.length_take]
          omega
        rw [hlen']
        exact nl1
    · left
      constructor
      · rw [hd0, if_neg hi]
      · omega
  · -- the parenthood of the last column at the prefix boundary
    have hlen' : (M.take j0).length = j0 := by
      rw [List.length_take]
      omega
    rw [hlen']
    exact np

/-! ## The expansion step strictly decreases the measure: bad branch

The genuine case: the bad part `B` is copied (with row-0 ascension when
`i1 = 1`) and the last pair dropped.  Decompose `M = G ++ B ++ [lp]` and
`M⟦n⟧ = G ++ (B ++ C)`; the abstract cores give `B ++ C ≺ B ++ [lp]` and
BADCTX lifts it through `G`. -/

theorem translate_oper_bad {M : PairSeq} {n : ℕ} (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1))
    (hn : 1 ≤ n) :
    translate (M⟦n⟧) <o translate M := by
  obtain ⟨G, v0, w0, R, d0, lp, hM, hMn, R_gt, lp_gt, disj, -⟩ :=
    oper_bad_blocks L hz hp hn
  -- split the copies into the base block and the rest `C`
  have hrange : List.range n = 0 :: List.range' 1 (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [List.range_eq_range', List.range'_succ]
  have hk0 : ((v0, w0) :: R).map (fun p => (p.1 + 0 * d0, p.2)) = (v0, w0) :: R := by
    simp
  set C := (List.range' 1 (n - 1)).flatMap
      (fun k => ((v0, w0) :: R).map fun p => (p.1 + k * d0, p.2)) with hC
  have hMn' : M⟦n⟧ = G ++ ((v0, w0) :: (R ++ C)) := by
    rw [hMn, hrange, List.flatMap_cons, hk0, hC]
    simp
  have hM' : M = G ++ ((v0, w0) :: (R ++ [lp])) := by
    rw [hM]
    simp
  -- `v0` bounds everything in `C`
  have allC_v0 : ∀ x ∈ C, v0 ≤ x.1 := by
    intro x hx
    rw [hC] at hx
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hx
    obtain ⟨p, hpmem, rfl⟩ := List.mem_map.1 hk
    have hvp : v0 ≤ p.1 := by
      rcases List.mem_cons.1 hpmem with rfl | hpR
      · simp
      · exact (R_gt p hpR).le
    calc v0 ≤ p.1 := hvp
      _ ≤ p.1 + k * d0 := Nat.le_add_right _ _
  -- the core: `blk ++ C ≺ blk ++ [lp]`
  have core : translate (((v0, w0) :: R) ++ C) <o translate (((v0, w0) :: R) ++ [lp]) := by
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · -- `n = 1`: no copies, `C = []`
      have : n - 1 = 0 := by omega
      have hCnil : C = [] := by rw [hC, this]; rfl
      exact core_i0 R_gt lp_gt (Or.inl hCnil)
    · -- `n ≥ 2`: expose the head of `C`
      have hsplit : List.range' 1 (n - 1) = 1 :: List.range' 2 (n - 2) := by
        have : n - 1 = (n - 2) + 1 := by omega
        rw [this, List.range'_succ]
      have hCcons : C = (v0 + 1 * d0, w0)
          :: (R.map (fun p => (p.1 + 1 * d0, p.2))
              ++ (List.range' 2 (n - 2)).flatMap
                  (fun k => ((v0, w0) :: R).map fun p => (p.1 + k * d0, p.2))) := by
        rw [hC, hsplit, List.flatMap_cons, List.map_cons, List.cons_append]
      rcases disj with ⟨hd0, -⟩ | ⟨d0pos, w0lt, lpfst, -⟩
      · -- `d0 = 0`: exact copies, the next copy re-opens at `v0`
        apply core_i0 R_gt lp_gt
        right
        rw [hCcons]
        simp [hd0]
      · -- `d0 > 0`: ascending copies, single tree with smaller subscript
        have Cge : ∀ x ∈ R.map (fun p => (p.1 + 1 * d0, p.2))
              ++ (List.range' 2 (n - 2)).flatMap
                  (fun k => ((v0, w0) :: R).map fun p => (p.1 + k * d0, p.2)),
            ((v0 + 1 * d0, w0) : ℕ × ℕ).1 ≤ x.1 := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨p, hpR, rfl⟩ := List.mem_map.1 hx
            simp only [Nat.one_mul]
            exact Nat.add_le_add_right (R_gt p hpR).le d0
          · obtain ⟨k, hkmem, hk⟩ := List.mem_flatMap.1 hx
            obtain ⟨p, hpmem, rfl⟩ := List.mem_map.1 hk
            have hk2 : 2 ≤ k := by
              have := List.mem_range'.1 hkmem
              omega
            have hvp : v0 ≤ p.1 := by
              rcases List.mem_cons.1 hpmem with rfl | hpR
              · simp
              · exact (R_gt p hpR).le
            have hdk : 1 * d0 ≤ k * d0 := Nat.mul_le_mul_right d0 (by omega)
            simp only []
            calc v0 + 1 * d0 ≤ p.1 + k * d0 := by omega
              _ = ((fun p : ℕ × ℕ => (p.1 + k * d0, p.2)) p).1 := rfl
        have Croot : ((v0 + 1 * d0, w0) : ℕ × ℕ).1 = lp.1 := by
          simp only [Nat.one_mul]
          omega
        have lead_lt : ((v0 + 1 * d0, w0) : ℕ × ℕ).2 < lp.2 := w0lt
        rw [hCcons]
        exact core_i1 R_gt Cge Croot lp_gt lead_lt
  -- lift through the good part `G` by BADCTX
  have bc : translate (G ++ ((v0, w0) :: (R ++ C)))
      <o translate (G ++ ((v0, w0) :: (R ++ [lp]))) := by
    apply translate_ctx_cong
    · -- base: the core, reshaped
      have e1 : ((v0, w0) :: R) ++ C = (v0, w0) :: (R ++ C) := by simp
      have e2 : ((v0, w0) :: R) ++ [lp] = (v0, w0) :: (R ++ [lp]) := by simp
      rw [← e1, ← e2]
      exact core
    · rfl
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact (R_gt x hx).le
      · exact allC_v0 x hx
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact (R_gt x hx).le
      · simp at hx
        simp [hx, lp_gt.le]
  rw [hMn', hM']
  exact bc

/-! ## The decrease lemma -/

/-- Every expansion step on a sequence of length `> 1` strictly decreases the
measure, regardless of the copy count `n ≥ 1` (and regardless of
standardness). -/
theorem m_step_decreases {M : PairSeq} {n : ℕ} (L : 1 < M.length) (hn : 1 ≤ n) :
    translate (M⟦n⟧) <o translate M := by
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · exact translate_oper_pred n L (Or.inl hz)
  · by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
    · exact translate_oper_bad L hz hp hn
    · exact translate_oper_pred n L (Or.inr hp)

end YAPSS
