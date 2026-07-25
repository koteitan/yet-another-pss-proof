/-
**The three-branch notation `p_a(b)+c` and the translation `translate`.**

The notation `Three`, the subscript-first order `<o` / `≤o` on it, the leading
subscript `lead`, the translation of a pair sequence into a term, and the
list and parent-relation bookkeeping the translation needs.
-/
import Pss
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

namespace YAPSS

inductive Three : Type where
  | Z : Three
  | P : ℕ → Three → Three → Three
  deriving DecidableEq, Repr, Inhabited

namespace Three

/-! ## The subscript-first lexicographic order -/

/-- The subscript-first lexicographic order on `Three`. -/
def olt : Three → Three → Prop
  | Z, Z => False
  | Z, P _ _ _ => True
  | P _ _ _, Z => False
  | P a b c, P e f g => a < e ∨ (a = e ∧ olt b f) ∨ (a = e ∧ b = f ∧ olt c g)

@[inherit_doc] infix:50 " <o " => olt

/-- `x ≤o y` iff `x <o y ∨ x = y`. -/
def ole (x y : Three) : Prop := x <o y ∨ x = y

@[inherit_doc] infix:50 " ≤o " => ole

@[simp] theorem olt_Z_Z : ¬ (Z <o Z) := fun h => h

@[simp] theorem olt_Z_P (a : ℕ) (b c : Three) : Z <o P a b c := trivial

@[simp] theorem olt_P_Z (a : ℕ) (b c : Three) : ¬ (P a b c <o Z) := fun h => h

@[simp] theorem olt_P_P {a e : ℕ} {b c f g : Three} :
    P a b c <o P e f g ↔
      a < e ∨ (a = e ∧ b <o f) ∨ (a = e ∧ b = f ∧ c <o g) := Iff.rfl

/-- Leading subscript of a term (the subscript of its first principal term). -/
def lead : Three → ℕ
  | Z => 0
  | P a _ _ => a

@[simp] theorem lead_Z : lead Z = 0 := rfl
@[simp] theorem lead_P (a : ℕ) (b c : Three) : lead (P a b c) = a := rfl

/-- Subscript-first domination: a term whose leading subscript is below `w`
(or which is `Z`) is strictly below *any* principal term `p_w(b)+c`.  This is
the mechanism behind the bad-step decrease: the ascending copies all have
leading subscript `= row-1 of the bad root`, which is strictly below the
row-1 of the dropped last pair. -/
theorem olt_P_of_lead_lt {t : Three} {w : ℕ} (b c : Three)
    (h : t = Z ∨ lead t < w) : t <o P w b c := by
  cases t with
  | Z => simp
  | P a b' c' =>
    simp only [lead_P] at h
    simp [h.resolve_left (by simp)]

theorem olt_irrefl (x : Three) : ¬ x <o x := by
  induction x with
  | Z => simp
  | P a b c ihb ihc => simp [ihb, ihc]

@[simp] theorem not_olt_Z (x : Three) : ¬ x <o Z := by
  cases x <;> simp

theorem olt_trans {x y z : Three} (hxy : x <o y) (hyz : y <o z) : x <o z := by
  induction z generalizing x y with
  | Z => exact absurd hyz (not_olt_Z y)
  | P c1 c2 c3 ih2 ih3 =>
    cases x with
    | Z => simp
    | P a1 a2 a3 =>
      obtain ⟨e1, e2, e3, rfl⟩ : ∃ e1 e2 e3, y = P e1 e2 e3 := by
        cases y with
        | Z => exact absurd hxy (not_olt_Z _)
        | P e1 e2 e3 => exact ⟨e1, e2, e3, rfl⟩
      rw [olt_P_P] at hxy hyz ⊢
      rcases hxy with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, h1⟩ <;>
        rcases hyz with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩
      · exact Or.inl (Nat.lt_trans h1 h2)
      · exact Or.inl h1
      · exact Or.inl h1
      · exact Or.inl h2
      · exact Or.inr (Or.inl ⟨rfl, ih2 h1 h2⟩)
      · exact Or.inr (Or.inl ⟨rfl, h1⟩)
      · exact Or.inl h2
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl, ih3 h1 h2⟩)

theorem olt_ole_trans {x y z : Three} (hxy : x <o y) (hyz : y ≤o z) : x <o z := by
  rcases hyz with h | rfl
  · exact olt_trans hxy h
  · exact hxy

/-- Strict monotonicity of a principal term in its argument. -/
theorem olt_P_b {b1 b2 : Three} (a : ℕ) (c1 c2 : Three) (h : b1 <o b2) :
    P a b1 c1 <o P a b2 c2 := by simp [h]

/-- Strict monotonicity of a principal term in its tail. -/
theorem olt_P_c {c1 c2 : Three} (a : ℕ) (b : Three) (h : c1 <o c2) :
    P a b c1 <o P a b c2 := by simp [h]

end Three

/-! ## The translation `translate : PairSeq → Three`

Read the pair sequence left to right as a forest by row 0 (the first
component): the head pair `(x,y)` becomes a principal term `p_y(…)` whose
argument is the translation of the maximal following block of pairs with
row-0 value `> x` (its descendants), and whose tail is the translation of the
remaining suffix (its siblings).  The subscript is the row-1 value `y`.
This is the PrSS forest map `omap` with `ω^•` replaced by `p_y(•)`. -/

open Three in
def translate : PairSeq → Three
  | [] => Z
  | p :: rest =>
    P p.2 (translate (rest.takeWhile fun q => p.1 < q.1))
          (translate (rest.dropWhile fun q => p.1 < q.1))
  termination_by M => M.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

open Three

theorem lead_translate (M : PairSeq) :
    lead (translate M) = match M with | [] => 0 | p :: _ => p.2 := by
  cases M <;> simp [translate]

/-! ### List bookkeeping helpers -/

section ListHelpers

variable {α : Type*} {p : α → Bool} {xs ys : List α}

theorem takeWhile_append_all (h : ∀ x ∈ xs, p x) :
    (xs ++ ys).takeWhile p = xs ++ ys.takeWhile p := by
  rw [List.takeWhile_append, if_pos (by rw [List.takeWhile_eq_self_iff.2 h])]

theorem dropWhile_append_all (h : ∀ x ∈ xs, p x) :
    (xs ++ ys).dropWhile p = ys.dropWhile p := by
  rw [List.dropWhile_append, if_pos (by simp [List.dropWhile_eq_nil_iff.2 h])]

theorem takeWhile_append_not {x : α} (hx : x ∈ xs) (hnx : ¬ p x) :
    (xs ++ ys).takeWhile p = xs.takeWhile p := by
  rw [List.takeWhile_append, if_neg]
  intro hlen
  exact hnx (List.takeWhile_eq_self_iff.1
    ((List.takeWhile_sublist p).eq_of_length hlen) x hx)

theorem dropWhile_append_not {x : α} (hx : x ∈ xs) (hnx : ¬ p x) :
    (xs ++ ys).dropWhile p = xs.dropWhile p ++ ys := by
  rw [List.dropWhile_append, if_neg]
  intro hempty
  exact hnx (List.dropWhile_eq_nil_iff.1 (List.isEmpty_iff.1 hempty) x hx)

/-- A suffix as an index map (helper for the bad-step list bookkeeping;
indexing via the total `getD`). -/
theorem drop_eq_map_getD (xs : List α) (a : ℕ) (d : α) :
    xs.drop a = (List.range' a (xs.length - a)).map fun i => xs.getD i d := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_drop, List.getElem_map, List.getElem_range']
    have hi : a + 1 * i < xs.length := by simp at h2 ⊢; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp [Nat.one_mul]

end ListHelpers

/-! ## Row-0 monotonicity of the parent relation

Along a row-0 ancestry the row-0 value strictly / weakly increases.  This
underlies the single-tree shape of the bad part (its root has the least
row-0). -/

theorem nextrel0_entry0_less {M : PairSeq} {j0 j1 : ℕ} (h : nextrel0 M j0 j1) :
    entry M 0 j0 < entry M 0 j1 := h.2.2.2.1

theorem le0_entry0_mono {M : PairSeq} {j0 j1 : ℕ} (h : le0 M j0 j1) :
    entry M 0 j0 ≤ entry M 0 j1 := by
  obtain ⟨-, -, hchain⟩ := h
  induction hchain with
  | refl => exact le_rfl
  | tail _ hyz ih => exact ih.trans (nextrel0_entry0_less hyz).le

/-- Indices increase along the row-0 Next relation. -/
theorem nextrel0_index_less {M : PairSeq} {a b : ℕ} (h : nextrel0 M a b) : a < b :=
  h.2.2.1

theorem nextrel0_rtrancl_index_le {M : PairSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hyz ih => exact ih.trans (nextrel0_index_less hyz).le

/-- Key interval lemma: along a row-0 ancestry `j0 ≤_M j1`, *every* index in
`(j0, j1]` (not only the chain points) has row-0 strictly above `j0`: the
valleys between chain points are `≥` the next chain point by `nextrel0`.  This
makes the bad part a single tree rooted at `j0` (its least row-0). -/
theorem le0_interval_gt {M : PairSeq} {j0 j1 : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) j0 j1) :
    ∀ k, j0 < k ∧ k ≤ j1 → entry M 0 j0 < entry M 0 k := by
  induction h with
  | refl => intro k hk; omega
  | @tail y z hj0y hyz ih =>
    have yz : entry M 0 y < entry M 0 z := nextrel0_entry0_less hyz
    have j0y : j0 ≤ y := nextrel0_rtrancl_index_le hj0y
    have j0le : entry M 0 j0 ≤ entry M 0 y := by
      rcases Nat.lt_or_ge j0 y with hlt | hge
      · exact (ih y ⟨hlt, le_rfl⟩).le
      · have : j0 = y := le_antisymm j0y hge
        exact this ▸ le_rfl
    intro k ⟨hk1, hk2⟩
    rcases Nat.lt_or_ge y k with hyk | hky
    case inr =>
      exact ih k ⟨hk1, hky⟩
    rcases eq_or_lt_of_le hk2 with rfl | hkz
    · exact lt_of_le_of_lt j0le yz
    · have hmid : entry M 0 z ≤ entry M 0 k := hyz.2.2.2.2 k ⟨hyk, hkz⟩
      exact lt_of_le_of_lt j0le (lt_of_lt_of_le yz hmid)

/-! ## Shape lemmas for `translate` -/

/-- If every pair after the head lies strictly above it in row 0, the whole
list reads as one tree: a single principal term with empty tail. -/
theorem translate_single_tree {p : ℕ × ℕ} {R : PairSeq}
    (h : ∀ x ∈ R, p.1 < x.1) :
    translate (p :: R) = P p.2 (translate R) Z := by
  have tw : R.takeWhile (fun q => p.1 < q.1) = R :=
    List.takeWhile_eq_self_iff.2 (by simpa using h)
  have dw : R.dropWhile (fun q => p.1 < q.1) = [] :=
    List.dropWhile_eq_nil_iff.2 (by simpa using h)
  rw [translate, tw, dw, translate]

/-- A block `(v0,w0) :: R` (root `v0`, body `R` all above `v0`) followed by a
tail `T` that re-opens at or below `v0` translates to a single principal whose
argument is `R` and whose siblings are `T`.  (This is the block shape used by
the bad-step cores; exposed here for the CNF preservation proof.) -/
theorem translate_block_append {v0 w0 : ℕ} {R T : PairSeq}
    (hR : ∀ x ∈ R, v0 < x.1) (hT : T = [] ∨ ¬ v0 < (T.headI).1) :
    translate (((v0, w0) :: R) ++ T) = P w0 (translate R) (translate T) := by
  have hR' : ∀ x ∈ R, (fun q : ℕ × ℕ => decide (v0 < q.1)) x = true := by
    intro x hx; simpa using hR x hx
  have twT : (R ++ T).takeWhile (fun q => v0 < q.1) = R := by
    rcases hT with rfl | hT
    · simpa using List.takeWhile_eq_self_iff.2 hR'
    · rcases T with - | ⟨t, ts⟩
      · simpa using List.takeWhile_eq_self_iff.2 hR'
      · rw [takeWhile_append_all hR']
        simp only [List.headI] at hT
        simp [hT]
  have dwT : (R ++ T).dropWhile (fun q => v0 < q.1) = T := by
    rcases hT with rfl | hT
    · simpa using List.dropWhile_eq_nil_iff.2 hR'
    · rcases T with - | ⟨t, ts⟩
      · simpa using List.dropWhile_eq_nil_iff.2 hR'
      · rw [dropWhile_append_all hR']
        simp only [List.headI] at hT
        simp [hT]
  rw [List.cons_append, translate]
  show P w0 (translate ((R ++ T).takeWhile fun q => v0 < q.1))
      (translate ((R ++ T).dropWhile fun q => v0 < q.1)) = _
  rw [twT, dwT]

/-- Shifting every row-0 value by a constant preserves the translation:
`translate` only reads row-0 through the strict comparisons `p.1 < q.1`
(shift-invariant) and reads row-1 (`.2`) unchanged.  This is why the ascending
copies of the bad-step tiling (which differ from the base block only by a
uniform row-0 shift) all translate to the same tree. -/
theorem translate_shift (d : ℕ) (M : PairSeq) :
    translate (M.map fun p => (p.1 + d, p.2)) = translate M := by
  induction M using translate.induct with
  | case1 => simp [translate]
  | case2 p rest ih1 ih2 =>
    have hpred : ((fun q : ℕ × ℕ => decide (p.1 + d < q.1))
          ∘ fun r : ℕ × ℕ => (r.1 + d, r.2))
        = fun r : ℕ × ℕ => decide (p.1 < r.1) := by
      funext r
      simp only [Function.comp_apply]
      rw [decide_eq_decide]
      omega
    rw [List.map_cons, translate]
    show P p.2 (translate ((rest.map fun r => (r.1 + d, r.2)).takeWhile
          fun q => p.1 + d < q.1))
        (translate ((rest.map fun r => (r.1 + d, r.2)).dropWhile
          fun q => p.1 + d < q.1)) = _
    rw [List.takeWhile_map, List.dropWhile_map, hpred, ih1, ih2, translate]

/-! ## Context congruence (BADCTX)

If two tails `Z1, Z2` share the same first pair's row-0 value and all their
other pairs lie strictly above it (so each is a single tree once read), then a
common good part `G` preserves a strict decrease between them.  This is the
context-peeling step of the bad-branch decrease: by induction on `G`, each
good pair either closes the comparison inside its own subtree or passes it on
one level deeper, until `G` is consumed and the comparison is exactly the one
on `Z1, Z2`. -/

theorem translate_ctx_cong {z1 z2 : ℕ × ℕ} {T1 T2 : PairSeq}
    (base : translate (z1 :: T1) <o translate (z2 :: T2))
    (root : z1.1 = z2.1)
    (r1 : ∀ x ∈ T1, z1.1 ≤ x.1)
    (r2 : ∀ x ∈ T2, z2.1 ≤ x.1)
    (G : PairSeq) :
    translate (G ++ z1 :: T1) <o translate (G ++ z2 :: T2) := by
  match G with
  | [] => simpa using base
  | g :: G' =>
    by_cases allG : ∀ x ∈ G', g.1 < x.1
    · by_cases hPg : g.1 < z1.1
      · -- case (b): the whole tail nests under `g`; pass to `G'`
        have aZ1 : ∀ x ∈ z1 :: T1, g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hPg
          · exact lt_of_lt_of_le hPg (r1 _ hx)
        have aZ2 : ∀ x ∈ z2 :: T2, g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact root ▸ hPg
          · exact lt_of_lt_of_le (root ▸ hPg) (r2 _ hx)
        have all1 : ∀ x ∈ G' ++ z1 :: T1, g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aZ1 x h]
        have all2 : ∀ x ∈ G' ++ z2 :: T2, g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aZ2 x h]
        have e1 : translate (g :: (G' ++ z1 :: T1))
            = P g.2 (translate (G' ++ z1 :: T1)) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all1),
            List.dropWhile_eq_nil_iff.2 (by simpa using all1), translate]
        have e2 : translate (g :: (G' ++ z2 :: T2))
            = P g.2 (translate (G' ++ z2 :: T2)) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all2),
            List.dropWhile_eq_nil_iff.2 (by simpa using all2), translate]
        simp only [List.cons_append]
        rw [e1, e2]
        exact olt_P_b _ _ _ (translate_ctx_cong base root r1 r2 G')
      · -- case (c): the tail is a sibling after `g`'s subtree; use the base case
        have hPg2 : ¬ g.1 < z2.1 := root ▸ hPg
        have allG' : ∀ x ∈ G', (fun q : ℕ × ℕ => decide (g.1 < q.1)) x = true := by
          intro x hx; simpa using allG x hx
        have tw1 : (G' ++ z1 :: T1).takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg]
        have dw1 : (G' ++ z1 :: T1).dropWhile (fun q => g.1 < q.1) = z1 :: T1 := by
          rw [dropWhile_append_all allG']
          simp [hPg]
        have tw2 : (G' ++ z2 :: T2).takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg2]
        have dw2 : (G' ++ z2 :: T2).dropWhile (fun q => g.1 < q.1) = z2 :: T2 := by
          rw [dropWhile_append_all allG']
          simp [hPg2]
        have e1 : translate (g :: (G' ++ z1 :: T1))
            = P g.2 (translate G') (translate (z1 :: T1)) := by
          rw [translate, tw1, dw1]
        have e2 : translate (g :: (G' ++ z2 :: T2))
            = P g.2 (translate G') (translate (z2 :: T2)) := by
          rw [translate, tw2, dw2]
        simp only [List.cons_append]
        rw [e1, e2]
        exact olt_P_c _ _ base
    · -- case (a): `G'` already drops to/below `g`; recurse on the shorter tail of `G'`
      push Not at allG
      obtain ⟨x, hx, hnx⟩ := allG
      have hnx' : ¬ (fun q => decide (g.1 < q.1)) x = true := by simpa using hnx
      have tw1 : (G' ++ z1 :: T1).takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw1 : (G' ++ z1 :: T1).dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ z1 :: T1 := dropWhile_append_not hx hnx'
      have tw2 : (G' ++ z2 :: T2).takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw2 : (G' ++ z2 :: T2).dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ z2 :: T2 := dropWhile_append_not hx hnx'
      have e1 : translate (g :: (G' ++ z1 :: T1))
          = P g.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((G'.dropWhile fun q => g.1 < q.1) ++ z1 :: T1)) := by
        rw [translate, tw1, dw1]
      have e2 : translate (g :: (G' ++ z2 :: T2))
          = P g.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((G'.dropWhile fun q => g.1 < q.1) ++ z2 :: T2)) := by
        rw [translate, tw2, dw2]
      simp only [List.cons_append]
      rw [e1, e2]
      exact olt_P_c _ _
        (translate_ctx_cong base root r1 r2 (G'.dropWhile fun q => g.1 < q.1))
  termination_by G.length
  decreasing_by
  · simp
  · simp [Nat.lt_succ_of_le (List.length_dropWhile_le _ G')]

/-! ## Subscripts and their monotonicity under expansion -/

/-- The set of row-1 values of a pair sequence. -/
def sndSet (M : PairSeq) : Set ℕ := Prod.snd '' {x | x ∈ M}

@[simp] theorem mem_sndSet {y : ℕ} {M : PairSeq} :
    y ∈ sndSet M ↔ ∃ p ∈ M, p.2 = y := by
  simp [sndSet]

@[simp] theorem sndSet_nil : sndSet ([] : PairSeq) = ∅ := by
  ext y
  simp

/-- The row index `i1` is at most 1, so the row-1 increment `δ1` is always 0. -/
theorem idx1_le1 (M : PairSeq) (j : ℕ) : idx1 M j ≤ 1 := by
  unfold idx1; split <;> simp

end YAPSS
