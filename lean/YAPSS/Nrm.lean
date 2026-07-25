/-
**Term normalization `nrm`** and the coefficient projection `proj`: purely
syntactic rewritings of `Three` terms.

At a principal `P a b c` whose argument `b` has a coefficient
`g ∈ Gterm a b` with `¬ g <o b`, `proj a` replaces `b` by the largest such `g`
and repeats; `ins` inserts a principal into a sum, dropping it when a later
principal already dominates it; `nrm` applies both recursively.

Only the *syntactic* content survives in the termination proof: the auxiliary
lemmas about `nextrel0` / `le0` / `nextR` on appended pair sequences, proved at
the end of this module, are what `Nrmstep.lean` and `Cofinality.lean` use.
-/
import YAPSS.Wf

namespace YAPSS

open Three

/-! ## Decidability of `olt` -/

/-! ## Executable critical-term collection -/

/-! ## Projection at a collapse point -/

/-! ## Sum insertion with absorption, and `nrm` -/

/-- Every `ST_PS` list is non-empty (the diagonals have length `v+1`; `oper`
preserves non-emptiness via `oper_eq_dropLast_append`). -/
theorem stps_len_pos {M : PairSeq} (hM : ST_PS M) : 0 < M.length := by
  induction hM with
  | diag v => rw [diagSeq_cons (Nat.zero_le v)]; simp
  | @oper N n hN hn ih =>
    by_cases L : 1 < N.length
    · obtain ⟨R, hR, -⟩ := oper_eq_dropLast_append L hn
      rw [hR, List.length_append, List.length_dropLast]; omega
    · rw [oper_eq_self_short n (by omega)]; exact ih

/-- Every `ST_PS` list begins with `(0,0)`: the diagonals start at `(0,0)`, and
`oper` preserves the head (`N⟦n⟧ = N.dropLast ++ R` keeps `N`'s first column when
`1 < |N|`).  So for `ST_PS (p :: rest)` the `dropWhile`-threshold is `p.1 = 0`. -/
theorem stps_head {M : PairSeq} (hM : ST_PS M) : M.headD (0,0) = (0,0) := by
  induction hM with
  | diag v => rw [diagSeq_cons (Nat.zero_le v)]; rfl
  | @oper N n hN hn ih =>
    by_cases L : 1 < N.length
    · obtain ⟨R, hR, -⟩ := oper_eq_dropLast_append L hn
      rw [hR]
      match N, L with
      | a :: b :: u, _ =>
        simp only [List.dropLast_cons_cons, List.cons_append, List.headD_cons]
        simpa using ih
    · rw [oper_eq_self_short n (by omega)]; exact ih

/-! ### `oper`-prefix-commute: suffix-invariance of the parent relations

To prove `oper (A ++ T) n = A ++ oper T n` (when the operative last block lies in
`T` and `T` is root-anchored) we need the parent-relation machinery
(`entry`/`nextrel0`/`nextrel1`/`le0`/`idx1`/`hasParent`/`parent`) evaluated at
indices `≥ |A|` to be unaffected by the prefix `A`.  These are concrete unfolding
lemmas on the relation defs. -/

/-- `getD` reads the right summand on out-of-`A` indices. -/
theorem getD_app_right (A T : PairSeq) {i : ℕ} (h : A.length ≤ i) :
    (A ++ T).getD i (0,0) = T.getD (i - A.length) (0,0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- `entry` is suffix-invariant: `entry (A ++ T) i (|A| + j) = entry T i j`. -/
theorem entry_append_right (A T : PairSeq) (i j : ℕ) :
    entry (A ++ T) i (A.length + j) = entry T i j := by
  unfold entry; rw [getD_app_right A T (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- `nextrel0` is suffix-invariant on shifted indices (the valley between
`|A|+j0` and `|A|+j1` only sees `T`-indices). -/
theorem nextrel0_append_right (A T : PairSeq) (j0 j1 : ℕ) :
    nextrel0 (A ++ T) (A.length + j0) (A.length + j1) ↔ nextrel0 T j0 j1 := by
  unfold nextrel0; rw [List.length_append]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    rw [entry_append_right, entry_append_right] at h4
    refine ⟨by omega, by omega, by omega, h4, ?_⟩
    intro j hj
    have := h5 (A.length + j) (by omega); rwa [entry_append_right, entry_append_right] at this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, by omega,
      by rw [entry_append_right, entry_append_right]; exact h4, ?_⟩
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = A.length + j' := ⟨j - A.length, by omega⟩
    rw [entry_append_right, entry_append_right]; exact h5 j' (by omega)

/-- `nextrel0`-reachability lifts from `T` to `A ++ T` on shifted indices. -/
theorem rtg_nextrel0_lift (A T : PairSeq) {j0 c : ℕ}
    (h : Relation.ReflTransGen (nextrel0 T) j0 c) :
    Relation.ReflTransGen (nextrel0 (A ++ T)) (A.length + j0) (A.length + c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hbc hcd ih =>
    exact Relation.ReflTransGen.tail ih ((nextrel0_append_right A T b c).2 hcd)

/-- `le0` lifts from `T` to `A ++ T` on shifted indices (forward direction). -/
theorem le0_append_right_of (A T : PairSeq) {j0 j1 : ℕ} (h : le0 T j0 j1) :
    le0 (A ++ T) (A.length + j0) (A.length + j1) := by
  obtain ⟨hb0, hb1, hrt⟩ := h
  exact ⟨by rw [List.length_append]; omega, by rw [List.length_append]; omega,
    rtg_nextrel0_lift A T hrt⟩

/-- `nextrel0` strictly increases the index. -/
theorem nextrel0_lt {M : PairSeq} {a b : ℕ} (h : nextrel0 M a b) : a < b := h.2.2.1

/-- A `nextrel0`-reachability chain in `A ++ T` starting at a shifted index
`|A| + a` stays within `T` (each step increases the index from `≥ |A|`), so it
mirrors a chain in `T`. -/
theorem rtg_nextrel0_unlift (A T : PairSeq) {a c : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (A ++ T)) (A.length + a) c) :
    ∃ c', c = A.length + c' ∧ Relation.ReflTransGen (nextrel0 T) a c' := by
  induction h with
  | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | @tail d e hde hef ih =>
    obtain ⟨d', rfl, ihd⟩ := ih
    have hge : A.length ≤ e :=
      le_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) (nextrel0_lt hef))
    obtain ⟨e', rfl⟩ : ∃ e', e = A.length + e' := ⟨e - A.length, by omega⟩
    exact ⟨e', rfl, Relation.ReflTransGen.tail ihd ((nextrel0_append_right A T d' e').1 hef)⟩

/-- `le0` is suffix-invariant on shifted indices: forward by `le0_append_right_of`,
backward because the chain stays in `T` (`rtg_nextrel0_unlift`). -/
theorem le0_append_right (A T : PairSeq) (j0 j1 : ℕ) :
    le0 (A ++ T) (A.length + j0) (A.length + j1) ↔ le0 T j0 j1 := by
  constructor
  · rintro ⟨hb0, hb1, hrt⟩
    rw [List.length_append] at hb0 hb1
    obtain ⟨c', hc', hrtT⟩ := rtg_nextrel0_unlift A T hrt
    have hjc : j1 = c' := by omega
    subst hjc
    exact ⟨by omega, by omega, hrtT⟩
  · exact le0_append_right_of A T

/-- `nextrel0` blocking: with `T` root-anchored (`entry T 0 0 = 0`) no `nextrel0`
edge crosses from a prefix index `k < |A|` into a positive-row-0 column at index
`j ≥ |A|` (the root at `|A|` violates the valley). -/
theorem nextrel0_no_cross (A T : PairSeq) (hroot : entry T 0 0 = 0)
    {k j : ℕ} (hk : k < A.length) (hj : A.length ≤ j)
    (hpos : 0 < entry (A ++ T) 0 j) (hne : nextrel0 (A ++ T) k j) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hne
  have hjne : A.length < j := by
    rcases Nat.lt_or_ge A.length j with h | h
    · exact h
    · -- A.length = j, but entry j > 0 and entry (A.length) = root = 0
      have : j = A.length := by omega
      subst this
      have hz : entry (A ++ T) 0 A.length = 0 := by
        have := entry_append_right A T 0 0; rw [Nat.add_zero] at this; rw [this, hroot]
      omega
  have hval := h5 A.length ⟨by omega, hjne⟩
  have hz : entry (A ++ T) 0 A.length = 0 := by
    have := entry_append_right A T 0 0; rw [Nat.add_zero] at this; rw [this, hroot]
  rw [hz] at hval; omega

/-- A row-0-`0` column has no `nextrel0`-predecessor (`nextrel0` needs a strict
row-0 increase into it). -/
theorem nextrel0_no_pred_zero {M : PairSeq} {a b : ℕ} (hz : entry M 0 b = 0)
    (h : nextrel0 M a b) : False := by
  obtain ⟨_, _, _, h4, _⟩ := h; rw [hz] at h4; omega

/-- A `nextrel0`-reachability chain ending at a row-0-`0` column is trivial
(`refl`): the root has no predecessor. -/
theorem rtg_to_root {M : PairSeq} {k b : ℕ} (hz : entry M 0 b = 0)
    (h : Relation.ReflTransGen (nextrel0 M) k b) : k = b := by
  cases h with
  | refl => rfl
  | tail _ hlast => exact absurd hlast (fun hh => nextrel0_no_pred_zero hz hh)

/-- **`le0` blocking** (the key cross-boundary fact): with `T` root-anchored, no
`le0`-chain crosses from a prefix index `k < |A|` into a positive-row-0 column at
index `|A| + j1`.  Induction on the chain: each step into a positive column has
its source `≥ |A|` (`nextrel0_no_cross`); a root source would have no predecessor
(`rtg_to_root`), forcing `k` itself `≥ |A|`. -/
theorem le0_no_cross (A T : PairSeq) (hroot : entry T 0 0 = 0)
    {k j1 : ℕ} (hk : k < A.length) (hpos : 0 < entry (A ++ T) 0 (A.length + j1))
    (h : le0 (A ++ T) k (A.length + j1)) : False := by
  obtain ⟨-, -, hrt⟩ := h
  suffices H : ∀ e, Relation.ReflTransGen (nextrel0 (A ++ T)) k e →
      A.length ≤ e → 0 < entry (A ++ T) 0 e → A.length ≤ k by
    exact absurd (H _ hrt (by omega) hpos) (by omega)
  intro e hrt'
  induction hrt' with
  | refl => intro he _; exact he
  | @tail c d hcd hde ih =>
    intro hd hpd
    have hcA : A.length ≤ c := by
      by_contra hlt; push_neg at hlt
      exact nextrel0_no_cross A T hroot hlt hd hpd hde
    by_cases hcpos : 0 < entry (A ++ T) 0 c
    · exact ih hcA hcpos
    · have hcz : entry (A ++ T) 0 c = 0 := by omega
      have hkc : k = c := rtg_to_root hcz hcd
      omega

/-- `nextrel1` is suffix-invariant on shifted indices.  The row-1 valley universal
ranges only over `j > |A| + j0 ≥ |A|` (all in `T`); `le0` is suffix-invariant
(`le0_append_right`). -/
theorem nextrel1_append_right (A T : PairSeq) (j0 j1 : ℕ) :
    nextrel1 (A ++ T) (A.length + j0) (A.length + j1) ↔ nextrel1 T j0 j1 := by
  unfold nextrel1
  rw [List.length_append]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    rw [entry_append_right, entry_append_right] at h4
    rw [le0_append_right] at h5
    refine ⟨by omega, by omega, by omega, h4, h5, ?_⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := hj
    -- forward: T-valley.  apply M-valley h6 at shifted index |A|+j
    have := h6 (A.length + j) ⟨by omega, (le0_append_right A T j j1).2 hj2⟩
    rwa [entry_append_right, entry_append_right] at this
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, by omega, by omega,
      by rw [entry_append_right, entry_append_right]; exact h4,
      (le0_append_right A T j0 j1).2 h5, ?_⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := hj
    -- backward: M-valley.  j > |A|+j0 ≥ |A|, so j = |A|+j' in T
    obtain ⟨j', rfl⟩ : ∃ j', j = A.length + j' := ⟨j - A.length, by omega⟩
    rw [le0_append_right] at hj2
    have := h6 j' ⟨by omega, hj2⟩
    rwa [entry_append_right, entry_append_right]

/-- `nextR` (row-indexed) is suffix-invariant on shifted indices. -/
theorem nextR_append_right (A T : PairSeq) (i j0 j1 : ℕ) :
    nextR (A ++ T) i (A.length + j0) (A.length + j1) ↔ nextR T i j0 j1 := by
  unfold nextR
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos hi]; exact nextrel0_append_right A T j0 j1
  · rw [if_neg hi, if_neg hi]; exact nextrel1_append_right A T j0 j1

/-- `idx1` is suffix-invariant on shifted indices (it only reads the column). -/
theorem idx1_append_right (A T : PairSeq) (j : ℕ) :
    idx1 (A ++ T) (A.length + j) = idx1 T j := by
  unfold idx1; rw [entry_append_right]

/-- A `nextR` edge gives `le0` to its target. -/
theorem nextR_le0 {M : PairSeq} {i k b : ℕ} (h : nextR M i k b) : le0 M k b := by
  unfold nextR at h
  by_cases hi : i = 0
  · rw [if_pos hi] at h; exact ⟨h.1, h.2.1, Relation.ReflTransGen.single h⟩
  · rw [if_neg hi] at h; exact h.2.2.2.2.1

/-- A `nextR`-source of a positive-row-0 column at index `|A| + j1` is in `T`
(via `le0_no_cross`). -/
theorem nextR_src_in_T (A T : PairSeq) (hroot : entry T 0 0 = 0)
    {i k j1 : ℕ} (hpos : 0 < entry (A ++ T) 0 (A.length + j1))
    (h : nextR (A ++ T) i k (A.length + j1)) : A.length ≤ k := by
  by_contra hlt; push_neg at hlt
  exact le0_no_cross A T hroot hlt hpos (nextR_le0 h)

/-- `hasParent` is suffix-invariant at a positive-row-0 column `|A| + j1` (the
parent lies in `T` by `nextR_src_in_T`; uniqueness transfers via
`nextR_append_right`). -/
theorem hasParent_append_right (A T : PairSeq) (hroot : entry T 0 0 = 0)
    {i j1 : ℕ} (hpos : 0 < entry (A ++ T) 0 (A.length + j1)) :
    hasParent (A ++ T) i (A.length + j1) ↔ hasParent T i j1 := by
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, huniq⟩
    have hge := nextR_src_in_T A T hroot hpos hj0
    obtain ⟨j0', rfl⟩ : ∃ j0', j0 = A.length + j0' := ⟨j0 - A.length, by omega⟩
    refine ⟨j0', (nextR_append_right A T i j0' j1).1 hj0, ?_⟩
    intro y hy
    have : A.length + y = A.length + j0' :=
      huniq (A.length + y) ((nextR_append_right A T i y j1).2 hy)
    omega
  · rintro ⟨j0', hj0', huniq⟩
    refine ⟨A.length + j0', (nextR_append_right A T i j0' j1).2 hj0', ?_⟩
    intro y hy
    have hge := nextR_src_in_T A T hroot hpos hy
    obtain ⟨y', rfl⟩ : ∃ y', y = A.length + y' := ⟨y - A.length, by omega⟩
    have := huniq y' ((nextR_append_right A T i y' j1).1 hy)
    omega

/-- `parent` shifts by `|A|` at a positive-row-0 column (both `parent (A++T)` and
`|A| + parent T` satisfy the unique `nextR`). -/
theorem parent_append_right (A T : PairSeq) (hroot : entry T 0 0 = 0)
    {i j1 : ℕ} (hpos : 0 < entry (A ++ T) 0 (A.length + j1))
    (hpT : hasParent T i j1) :
    parent (A ++ T) i (A.length + j1) = A.length + parent T i j1 := by
  have hpM : hasParent (A ++ T) i (A.length + j1) :=
    (hasParent_append_right A T hroot hpos).2 hpT
  -- both `parent (A++T)` and `|A| + parent T` satisfy nextR; conclude equal by uniqueness
  exact hpM.unique (parent_nextR hpM)
    ((nextR_append_right A T i (parent T i j1) j1).2 (parent_nextR hpT))

/-- `take` at a shifted index splits across the append. -/
theorem take_append_right (A T : PairSeq) (j : ℕ) :
    (A ++ T).take (A.length + j) = A ++ T.take j := by
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- A single shifted copy-block reading `entry (A ++ T)` equals the copy-block
reading `entry T` (all indices land in `T`). -/
theorem copyblock_append (A T : PairSeq) (a m k d0 d1 : ℕ) :
    (List.range' (A.length + a) m).map
      (fun j => (entry (A ++ T) 0 j + k * d0, entry (A ++ T) 1 j + k * d1))
    = (List.range' a m).map
      (fun j => (entry T 0 j + k * d0, entry T 1 j + k * d1)) := by
  have hshift : List.range' (A.length + a) m = (List.range' a m).map (A.length + ·) := by
    rw [List.range'_eq_map_range, List.range'_eq_map_range, List.map_map]
    congr 1; funext x; simp; omega
  rw [hshift, List.map_map]
  congr 1; funext j
  simp only [Function.comp_apply]
  rw [entry_append_right, entry_append_right]

/-- `Pred` splits across the append when `2 ≤ |T|` (both stay in the `dropLast`
of `T`). -/
theorem Pred_append_right (A T : PairSeq) (hT : 2 ≤ T.length) :
    Pred (A ++ T) = A ++ Pred T := by
  unfold Pred
  rw [List.length_append, if_neg (by omega), if_neg (by omega),
      List.dropLast_append_of_ne_nil]
  intro h; rw [h] at hT; simp at hT

/-- A row-0-`0` column has no parent (its only `le0`-predecessor would be itself,
but `nextR` is strict).  So in the `oper` tiling branch the last column has
positive row-0. -/
theorem no_hasParent_of_row0_zero {M : PairSeq} {i j1 : ℕ}
    (hz : entry M 0 j1 = 0) (hp : hasParent M i j1) : False := by
  obtain ⟨j0, hj0, -⟩ := hp
  obtain ⟨-, -, hrt⟩ := nextR_le0 hj0
  exact absurd (rtg_to_root hz hrt) (Nat.ne_of_lt (nextR_index_lt hj0))

/-- **`oper`-prefix-commute** — the central kernel.  When `2 ≤ |T|` and `T` is
root-anchored (`entry T 0 0 = 0`), `oper` operates only on the last top-level
block (inside `T`), so it commutes with the prefix `A`:
`oper (A ++ T) n = A ++ oper T n`.  Proof: unfold `oper` on both; the last index
is `|A| + (|T|-1)`; every `entry`/`idx1`/`hasParent`/`parent` reads is
suffix-invariant; the `take` and copy-blocks split across `A`. -/
theorem oper_append_right (A T : PairSeq) (n : ℕ) (hT : 2 ≤ T.length)
    (hroot : entry T 0 0 = 0) :
    oper (A ++ T) n = A ++ oper T n := by
  have hlenAT : (A ++ T).length - 1 = A.length + (T.length - 1) := by
    rw [List.length_append]; omega
  unfold oper
  -- abbreviate j1 for T
  set j1 := T.length - 1 with hj1
  -- the last index of A++T is A.length + j1
  rw [hlenAT]
  -- (A++T).length-1 = A.length + j1 ; rewrite the j1 of the AT side
  have hne_AT : ¬ (A.length + j1 = 0) := by omega
  have hne_T : ¬ (j1 = 0) := by omega
  rw [if_neg hne_AT, if_neg hne_T]
  -- entries at last index suffix-invariant
  have he0 : entry (A ++ T) 0 (A.length + j1) = entry T 0 j1 := entry_append_right A T 0 j1
  have he1 : entry (A ++ T) 1 (A.length + j1) = entry T 1 j1 := entry_append_right A T 1 j1
  rw [he0, he1]
  by_cases hz : entry T 0 j1 = 0 ∧ entry T 1 j1 = 0
  · rw [if_pos hz, if_pos hz]; exact Pred_append_right A T hT
  · rw [if_neg hz, if_neg hz]
    -- idx1 suffix-invariant
    have hidx : idx1 (A ++ T) (A.length + j1) = idx1 T j1 := idx1_append_right A T j1
    rw [hidx]
    by_cases hp : hasParent T (idx1 T j1) j1
    · -- tiling: entry 0 last > 0 (no_hasParent_of_row0_zero)
      have hpos : 0 < entry (A ++ T) 0 (A.length + j1) := by
        rw [he0]
        by_contra hzero; push_neg at hzero
        exact no_hasParent_of_row0_zero (by omega) hp
      have hpAT : hasParent (A ++ T) (idx1 T j1) (A.length + j1) :=
        (hasParent_append_right A T hroot hpos).2 hp
      rw [if_neg (not_not.2 hpAT), if_neg (not_not.2 hp)]
      -- parent shifts
      have hpar : parent (A ++ T) (idx1 T j1) (A.length + j1)
          = A.length + parent T (idx1 T j1) j1 := parent_append_right A T hroot hpos hp
      set j0 := parent T (idx1 T j1) j1 with hj0
      -- unfold the `let`-bindings on both sides
      simp only [hpar]
      -- d0, d1 (using the shifted parent) are suffix-invariant: rewrite them to T-form
      have hd0 : entry T 0 j1 - entry (A ++ T) 0 (A.length + j0) = entry T 0 j1 - entry T 0 j0 := by
        rw [entry_append_right]
      have hd1 : entry T 1 j1 - entry (A ++ T) 1 (A.length + j0) = entry T 1 j1 - entry T 1 j0 := by
        rw [entry_append_right]
      rw [hd0, hd1]
      have hrange : (A.length + j1) - (A.length + j0) = j1 - j0 := by omega
      rw [hrange, take_append_right, List.append_assoc]
      congr 1
      congr 1
      apply List.flatMap_congr
      intro k _
      exact copyblock_append A T j0 (j1 - j0) k _ _
    · -- no parent in T ⟹ no parent in A++T ⟹ both Pred
      have hpAT : ¬ hasParent (A ++ T) (idx1 T j1) (A.length + j1) := by
        intro hh
        by_cases hpos : 0 < entry (A ++ T) 0 (A.length + j1)
        · exact hp ((hasParent_append_right A T hroot hpos).1 hh)
        · exact no_hasParent_of_row0_zero (by omega) hh
      rw [if_pos hp, if_pos hpAT]
      exact Pred_append_right A T hT

/-! ### Helpers for `oper_tail_cases` -/

/-- `(range j1).map (entry-pair)` is the prefix `N.take j1` (for `j1 ≤ |N|`). -/
theorem map_range_entry_eq_take (N : PairSeq) {j1 : ℕ} (h : j1 ≤ N.length) :
    (List.range j1).map (fun j => (entry N 0 j, entry N 1 j)) = N.take j1 := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intro i h1 h2
    have hi : i < N.length := by
      rw [List.length_take, Nat.min_eq_left h] at h2; omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, entry,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp

/-- The head of `N⟦n⟧` is `N`'s head, for a long list (`1 < |N|`, `1 ≤ n`):
`N⟦n⟧ = N.dropLast ++ R` and `N.dropLast` is nonempty starting at `N`'s head. -/
theorem oper_headD (N : PairSeq) {n : ℕ} (L : 1 < N.length) (hn : 1 ≤ n) :
    (N⟦n⟧).headD (0,0) = N.headD (0,0) := by
  obtain ⟨R, hR, -⟩ := oper_eq_dropLast_append L hn
  rw [hR]
  match N, L with
  | a :: b :: u, _ =>
    simp only [List.dropLast_cons_cons, List.cons_append, List.headD_cons]

end YAPSS
