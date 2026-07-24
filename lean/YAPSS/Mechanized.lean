/-
The ternary-tree notation `p_a(b)+c`.  Lean port of `mechanized.thy`.

The type `Three` is a tree whose nodes carry one natural number and two
subtrees; it is named after that structure, not after any order (linearity of
`<o` is proved below, not presupposed).  `P a b c` denotes `p_a(b) + c`: a
principal term `p_a(b)` with natural-number subscript `a` (the row-1 value of
a pair) and argument `b` (the sub-forest), followed by the rest of the sum
`c`.  `Z` denotes `0`.  This generalises the PrSS notation `E a b = ω^a + b`:
the single exponent `ω^a` is replaced by the subscripted `p_a(b)`.

The order `<o` is the lexicographic order on principal terms with the
subscript taken first (subscript-first).  Under this direction the expansion
step strictly decreases the translate (see `m_step_decreases` below).
-/
import YAPSS.Def
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

theorem olt_Z_iff {x y : Three} (h : x <o y) : y ≠ Z := by
  rintro rfl; exact not_olt_Z x h

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

theorem olt_total (x y : Three) : x <o y ∨ x = y ∨ y <o x := by
  induction x generalizing y with
  | Z => cases y <;> simp
  | P a1 a2 a3 ih2 ih3 =>
    cases y with
    | Z => simp
    | P e1 e2 e3 =>
      rcases Nat.lt_trichotomy a1 e1 with h1 | rfl | h1
      · exact Or.inl (by simp [h1])
      · rcases ih2 e2 with h2 | rfl | h2
        · exact Or.inl (by simp [h2])
        · rcases ih3 e3 with h3 | rfl | h3
          · exact Or.inl (by simp [h3])
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (by simp [h3]))
        · exact Or.inr (Or.inr (by simp [h2]))
      · exact Or.inr (Or.inr (by simp [h1]))

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

/-! ### Sanity checks (the examples of the task description) -/

example : translate [(0,0)] = P 0 Z Z := by simp [translate]

/-- `(0,0)(1,0) = p₀(p₀(0))` -/
example : translate [(0,0),(1,0)] = P 0 (P 0 Z Z) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-- `(0,0)(1,1) = p₀(p₁(0))` -/
example : translate [(0,0),(1,1)] = P 0 (P 1 Z Z) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-- `(0,0)(1,0)(1,0) = p₀(p₀(0)+p₀(0))` -/
example : translate [(0,0),(1,0),(1,0)] = P 0 (P 0 Z (P 0 Z Z)) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-- `(0,0)(1,1)(2,2)(3,3) = p₀(p₁(p₂(p₃(0))))` -/
example : translate [(0,0),(1,1),(2,2),(3,3)] = P 0 (P 1 (P 2 (P 3 Z Z) Z) Z) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-! ### List bookkeeping helpers (Isabelle's `takeWhile_append1/2` etc.) -/

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
Isabelle's `drop_eq_map_nth`, with the partial `!` replaced by `getD`). -/
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

/-- The set of row-1 values of a pair sequence (Isabelle's `snd ` set M`). -/
def sndSet (M : PairSeq) : Set ℕ := Prod.snd '' {x | x ∈ M}

@[simp] theorem mem_sndSet {y : ℕ} {M : PairSeq} :
    y ∈ sndSet M ↔ ∃ p ∈ M, p.2 = y := by
  simp [sndSet]

@[simp] theorem sndSet_nil : sndSet ([] : PairSeq) = ∅ := by
  ext y
  simp

theorem sndSet_mono {M N : PairSeq} (h : ∀ x ∈ M, x ∈ N) : sndSet M ⊆ sndSet N := by
  intro y hy
  rw [mem_sndSet] at hy ⊢
  obtain ⟨p, hp, rfl⟩ := hy
  exact ⟨p, h p hp, rfl⟩

/-- The row index `i1` is at most 1, so the row-1 increment `δ1` is always 0. -/
theorem idx1_le1 (M : PairSeq) (j : ℕ) : idx1 M j ≤ 1 := by
  unfold idx1; split <;> simp

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
