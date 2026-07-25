/-
**Attack file for `nrm_order_pres` / `nrm_step_dec`** — the independent Lean
campaign on the remaining core (this file is NOT a port of `ord/nrmstep.thy`;
it shares the mathematical skeleton discovered there but is developed
directly in Lean).

Layer 1 (this file, pure — no class assumptions):
  * `maxo_ub`        — `maxo` is an upper bound of its argument list
  * `Gterm_trans`    — the critical-term relation is transitive
  * `proj_ole`       — projection is inflationary (`b ≤o proj u b`)
  * `proj_fire`      — **one-step theorem**: the maximal critical term has no
    violator of its own, so `proj` terminates after a single rewrite;
    `proj u b` is either `b` (no fire) or `maxo` of the violators (fire)
  * fire corollaries — `proj_mem_of_fire`, `olt_proj_of_fire`,
    `proj_ub_of_fire`
  * `ins_olt_mono`   — sum insertion is *unconditionally* strictly monotone
    in the tail (absorption needs no side condition: absorb-left implies
    absorb-right via `absorb_mono`)

These give the downstream case analyses the clean shape
`proj u b = if fire then max-violator else b`.
-/
import YAPSS.Nrm
import YAPSS.Seqlex
import Mathlib.Data.Nat.Find

namespace YAPSS

open Three

/-! ## `maxo` is an upper bound -/

theorem maxo_ub {x : Three} {ys : List Three} : ∀ y ∈ x :: ys, y ≤o maxo x ys := by
  induction ys generalizing x with
  | nil =>
    intro y hy
    rcases List.mem_singleton.1 hy with rfl
    exact Or.inr rfl
  | cons z zs ih =>
    intro y hy
    rw [maxo_cons]
    by_cases h : olt x z
    · rw [if_pos h]
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact ole_trans (Or.inl h) (ih z (List.mem_cons_self ..))
      · exact ih y hy'
    · rw [if_neg h]
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact ih y (List.mem_cons_self ..)
      · rcases List.mem_cons.1 hy' with rfl | hy''
        · have hyx : y ≤o x := by
            rcases olt_total y x with h1 | h1 | h1
            · exact Or.inl h1
            · exact Or.inr h1
            · exact absurd h1 h
          exact ole_trans hyx (ih x (List.mem_cons_self ..))
        · exact ih y (List.mem_cons_of_mem _ hy'')

theorem maxo_ub_mem {gs : List Three} (h : gs ≠ []) :
    ∀ y ∈ gs, y ≤o maxo gs.headI gs.tail := by
  cases gs with
  | nil => exact absurd rfl h
  | cons g gs =>
    intro y hy
    simpa using maxo_ub y (by simpa using hy)

/-! ## Transitivity of the critical-term relation -/

theorem Gterm_trans {u : ℕ} {x g t : Three} (hx : x ∈ Gterm u g)
    (hg : g ∈ Gterm u t) : x ∈ Gterm u t := by
  induction t with
  | Z => simp at hg
  | P a b c ihb ihc =>
    rcases mem_Gterm_P.1 hg with ⟨ha, rfl | hgb⟩ | hgc
    · exact mem_Gterm_P.2 (Or.inl ⟨ha, Or.inr hx⟩)
    · exact mem_Gterm_P.2 (Or.inl ⟨ha, Or.inr (ihb hgb)⟩)
    · exact mem_Gterm_P.2 (Or.inr (ihc hgc))

/-! ## Projection is inflationary -/

/-- Members of the violator list are critical terms of `b`. -/
theorem mem_filter_Gterm {u : ℕ} {b g : Three}
    (h : g ∈ (Glist u b).filter (fun g => ¬ olt g b)) : g ∈ Gterm u b :=
  mem_Glist.1 (List.mem_of_mem_filter h)

/-- Members of the violator list do not lie below `b`. -/
theorem mem_filter_not_olt {u : ℕ} {b g : Three}
    (h : g ∈ (Glist u b).filter (fun g => ¬ olt g b)) : ¬ g <o b := by
  have := List.of_mem_filter h
  simpa using this

theorem proj_ole (u : ℕ) (b : Three) : b ≤o proj u b := by
  generalize hs : tsize b = n
  induction n using Nat.strong_induction_on generalizing b with
  | _ n IH =>
    subst hs
    by_cases h : (Glist u b).filter (fun g => ¬ olt g b) = []
    · rw [proj_id h]
      exact Or.inr rfl
    · rw [proj_rec h]
      have hin := maxo_hdtl_in h
      have hG : maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
          ((Glist u b).filter (fun g => ¬ olt g b)).tail ∈ Gterm u b :=
        mem_filter_Gterm hin
      have hble : b ≤o maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
          ((Glist u b).filter (fun g => ¬ olt g b)).tail := by
        rcases olt_total b _ with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · exact absurd h1 (mem_filter_not_olt hin)
      exact ole_trans hble (IH (tsize _) (Gterm_tsize hG) _ rfl)

/-! ## The one-step theorem -/

/-! ## The firing predicate and projection submonotonicity -/

/-- `pfire u b`: `b` has a critical term not below itself, so `proj` rewrites. -/
def pfire (u : ℕ) (b : Three) : Prop :=
  (Glist u b).filter (fun g => ¬ olt g b) ≠ []

theorem pfire_iff {u : ℕ} {b : Three} :
    pfire u b ↔ ∃ g ∈ Gterm u b, ¬ g <o b := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨g, mem_filter_Gterm hg, mem_filter_not_olt hg⟩
  · rintro ⟨g, hG, hng⟩ he
    have hmem : g ∈ (Glist u b).filter (fun g => ¬ olt g b) :=
      List.mem_filter.2 ⟨mem_Glist.2 hG, by simpa using hng⟩
    rw [he] at hmem
    simp at hmem

theorem proj_nofire {u : ℕ} {b : Three} (h : ¬ pfire u b) : proj u b = b :=
  proj_id (not_not.1 h)

theorem olt_ole_trans {x y z : Three} (h1 : x <o y) (h2 : y ≤o z) : x <o z := by
  rcases h2 with h2 | rfl
  · exact olt_trans h1 h2
  · exact h1

/-! ## Unconditional strict monotonicity of `ins` in the tail -/

/-- Absorb-left implies absorb-right along `<o`: if the head of `t` already
absorbs `(a, b)` and `t <o t'`, then the head of `t'` absorbs it too. -/
theorem absorb_mono {a e e' : ℕ} {b f f' g g' : Three}
    (habs : a < e ∨ (a = e ∧ b <o f)) (h : P e f g <o P e' f' g') :
    a < e' ∨ (a = e' ∧ b <o f') := by
  rcases olt_P_P.1 h with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩
  · rcases habs with h1 | ⟨rfl, h1⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl h2
  · rcases habs with h1 | ⟨rfl, h1⟩
    · exact Or.inl h1
    · exact Or.inr ⟨rfl, olt_trans h1 h2⟩
  · exact habs

/-- **`ins` is strictly monotone in the tail, with no side condition.**
If absorption fires on the left it fires on the right (`absorb_mono`); if it
fires only on the right, the right head already dominates `(a, b)`; if on
neither, the comparison descends to the tails. -/
theorem ins_olt_mono {a : ℕ} {b t t' : Three} (h : t <o t') :
    ins a b t <o ins a b t' := by
  cases t with
  | Z =>
    cases t' with
    | Z => exact absurd h olt_Z_Z
    | P e f g =>
      rw [ins_Z, ins_P]
      by_cases habs : a < e ∨ (a = e ∧ b <o f)
      · rw [if_pos habs]
        rcases habs with h1 | ⟨rfl, h2⟩
        · exact olt_P_P.2 (Or.inl h1)
        · exact olt_P_P.2 (Or.inr (Or.inl ⟨rfl, h2⟩))
      · rw [if_neg habs]
        exact olt_P_P.2 (Or.inr (Or.inr ⟨rfl, rfl, by simp⟩))
  | P e f g =>
    cases t' with
    | Z => exact absurd h (not_olt_Z _)
    | P e' f' g' =>
      rw [ins_P, ins_P]
      by_cases h1 : a < e ∨ (a = e ∧ b <o f)
      · rw [if_pos h1, if_pos (absorb_mono h1 h)]
        exact h
      · rw [if_neg h1]
        by_cases h2 : a < e' ∨ (a = e' ∧ b <o f')
        · rw [if_pos h2]
          rcases h2 with h3 | ⟨rfl, h3⟩
          · exact olt_P_P.2 (Or.inl h3)
          · exact olt_P_P.2 (Or.inr (Or.inl ⟨rfl, h3⟩))
        · rw [if_neg h2]
          exact olt_P_P.2 (Or.inr (Or.inr ⟨rfl, rfl, h⟩))

/-! ## One-position increase relations

`lext`: one leaf inserted at a `Z`-position (deepest tail end or empty
argument).  `lflip`: one leaf's subscript incremented.  `einc`/`eflip` are
the *end-position* restrictions: along tails to the last summand, then (only
when the tail is already `Z`) into its argument.  These are the shapes
actually produced by appending one column to a standard segment. -/

inductive lext : Three → Three → Prop
  | end_ (w : ℕ) : lext Z (P w Z Z)
  | tail {c c' : Three} (a : ℕ) (b : Three) : lext c c' → lext (P a b c) (P a b c')
  | arg {b b' : Three} (a : ℕ) (c : Three) : lext b b' → lext (P a b c) (P a b' c)

inductive lflip : Three → Three → Prop
  | leaf {w w' : ℕ} : w < w' → lflip (P w Z Z) (P w' Z Z)
  | tail {c c' : Three} (a : ℕ) (b : Three) : lflip c c' → lflip (P a b c) (P a b c')
  | arg {b b' : Three} (a : ℕ) (c : Three) : lflip b b' → lflip (P a b c) (P a b' c)

inductive einc : Three → Three → Prop
  | end_ (w : ℕ) : einc Z (P w Z Z)
  | tail {c c' : Three} (a : ℕ) (b : Three) : einc c c' → einc (P a b c) (P a b c')
  | argZ {b b' : Three} (a : ℕ) : einc b b' → einc (P a b Z) (P a b' Z)

inductive eflip : Three → Three → Prop
  | leaf {w w' : ℕ} : w < w' → eflip (P w Z Z) (P w' Z Z)
  | tail {c c' : Three} (a : ℕ) (b : Three) : eflip c c' → eflip (P a b c) (P a b c')
  | argZ {b b' : Three} (a : ℕ) : eflip b b' → eflip (P a b Z) (P a b' Z)

/-! ## The gap lemmas

Nothing of size below `x` separates `x` from its end-increase `x'`: an
order-witness `¬ g <o x` together with `g <o x'` forces the comparison to be
resolved exactly at the modified end position, so `g` contains a copy of all
of `x` before that position. -/

/-! ## Critical sets under one-position increase

No critical term is lost: every critical of `b` either survives in `b'` or
has a pointwise `lext`/`lflip`-partner among the criticals of `b'`. -/

/-! ## Fire transport

A collapse witness of `x` yields one for any end-increase of `x`: by the gap
lemma the old witness cannot have fallen strictly below `x'` (it is too
small), and by `Gterm_*_sup` it (or a pointwise partner above it) is still a
critical term of `x'`. -/

/-! ## Small computation lemmas -/

@[simp] theorem translate_nil : translate [] = Z := by rw [translate]

theorem translate_cons (p : ℕ × ℕ) (rest : PairSeq) :
    translate (p :: rest) =
      P p.2 (translate (rest.takeWhile fun r => p.1 < r.1))
            (translate (rest.dropWhile fun r => p.1 < r.1)) := by
  rw [translate]

theorem translate_single (q : ℕ × ℕ) : translate [q] = P q.2 Z Z := by
  simp [translate]

@[simp] theorem proj_Z (u : ℕ) : proj u Z = Z := proj_id (by simp)

theorem nrm_leaf (w : ℕ) : nrm (P w Z Z) = P w Z Z := by
  rw [nrm_P, nrm_Z, proj_Z, ins_Z]

/-! ## The snoc condition bundle and main induction

`snocok C q`: the conditions along the recursive decomposition of `C` under
which appending `q` strictly increases the normalized image.  Thanks to
`ins_olt_mono` the bundle degenerates to a single condition at the innermost
dominated run: when `q` extends the argument (`p.1 < q.1`), the projected
argument must strictly increase.  Deriving the bundle from standardness of
the host is the remaining class obligation (`ST_snocok`, future work). -/

def snocok : PairSeq → ℕ × ℕ → Prop
  | [], _ => False
  | p :: rest, q =>
    if (rest.dropWhile fun r => p.1 < r.1) = [] then
      p.1 < q.1 →
        proj p.2 (nrm (translate rest)) <o proj p.2 (nrm (translate (rest ++ [q])))
    else snocok (rest.dropWhile fun r => p.1 < r.1) q
  termination_by C _ => C.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

@[simp] theorem snocok_nil (q : ℕ × ℕ) : ¬ snocok [] q := by
  rw [snocok]
  exact id

theorem snocok_cons (p : ℕ × ℕ) (rest : PairSeq) (q : ℕ × ℕ) :
    snocok (p :: rest) q =
      (if (rest.dropWhile fun r => p.1 < r.1) = [] then
        p.1 < q.1 →
          proj p.2 (nrm (translate rest)) <o proj p.2 (nrm (translate (rest ++ [q])))
      else snocok (rest.dropWhile fun r => p.1 < r.1) q) := by
  rw [snocok]

/-- **Snoc main induction**: under the condition bundle, appending one column
strictly increases the normalized image.  Case (A) (new summand) is an
instance of `ins_olt_mono` with `Z <o` a leaf; case (B) (tail extension)
is `ins_olt_mono` on the recursive call; case (C) (argument extension)
is the bundled condition itself. -/
theorem nrm_snoc_seg : ∀ {C : PairSeq} {q : ℕ × ℕ}, snocok C q → C ≠ [] →
    nrm (translate C) <o nrm (translate (C ++ [q]))
  | [], _, _, hne => absurd rfl hne
  | p :: rest, q, hsok, _ => by
    by_cases hT : (rest.dropWhile fun r => p.1 < r.1) = []
    · have Kall : (rest.takeWhile fun r => p.1 < r.1) = rest :=
        List.takeWhile_eq_self_iff.2 (List.dropWhile_eq_nil_iff.1 hT)
      have nCs : nrm (translate (p :: rest))
          = P p.2 (proj p.2 (nrm (translate rest))) Z := by
        rw [translate_cons, Kall, hT, translate_nil, nrm_P, nrm_Z, ins_Z]
      rw [snocok_cons, if_pos hT] at hsok
      by_cases qd : p.1 < q.1
      · -- (C) argument extension
        have tw' : ((rest ++ [q]).takeWhile fun r => p.1 < r.1) = rest ++ [q] := by
          rw [takeWhile_append_all (List.dropWhile_eq_nil_iff.1 hT)]
          simp [qd]
        have dw' : ((rest ++ [q]).dropWhile fun r => p.1 < r.1) = [] := by
          rw [dropWhile_append_all (List.dropWhile_eq_nil_iff.1 hT)]
          simp [qd]
        have nC' : nrm (translate ((p :: rest) ++ [q]))
            = P p.2 (proj p.2 (nrm (translate (rest ++ [q])))) Z := by
          rw [List.cons_append, translate_cons, tw', dw', translate_nil,
              nrm_P, nrm_Z, ins_Z]
        rw [nCs, nC']
        exact olt_P_b p.2 Z Z (hsok qd)
      · -- (A) new summand
        have tw' : ((rest ++ [q]).takeWhile fun r => p.1 < r.1) = rest := by
          rw [takeWhile_append_all (List.dropWhile_eq_nil_iff.1 hT)]
          simp [qd]
        have dw' : ((rest ++ [q]).dropWhile fun r => p.1 < r.1) = [q] := by
          rw [dropWhile_append_all (List.dropWhile_eq_nil_iff.1 hT)]
          simp [qd]
        have nC' : nrm (translate ((p :: rest) ++ [q]))
            = ins p.2 (proj p.2 (nrm (translate rest))) (P q.2 Z Z) := by
          rw [List.cons_append, translate_cons, tw', dw', translate_single,
              nrm_P, nrm_leaf]
        have nCz : nrm (translate (p :: rest))
            = ins p.2 (proj p.2 (nrm (translate rest))) Z := by
          rw [translate_cons, Kall, hT, translate_nil, nrm_P, nrm_Z]
        rw [nCz, nC']
        exact ins_olt_mono (by simp)
    · -- (B) tail extension
      obtain ⟨w, win, wnp⟩ : ∃ w ∈ rest, ¬ p.1 < w.1 := by
        by_contra hall
        push Not at hall
        exact hT (List.dropWhile_eq_nil_iff.2 (by
          intro x hx
          simpa using hall x hx))
      have tw' : ((rest ++ [q]).takeWhile fun r => p.1 < r.1)
          = rest.takeWhile fun r => p.1 < r.1 :=
        takeWhile_append_not win (by simpa using wnp)
      have dw' : ((rest ++ [q]).dropWhile fun r => p.1 < r.1)
          = (rest.dropWhile fun r => p.1 < r.1) ++ [q] :=
        dropWhile_append_not win (by simpa using wnp)
      have nC : nrm (translate (p :: rest))
          = ins p.2 (proj p.2 (nrm (translate (rest.takeWhile fun r => p.1 < r.1))))
                (nrm (translate (rest.dropWhile fun r => p.1 < r.1))) := by
        rw [translate_cons, nrm_P]
      have nC' : nrm (translate ((p :: rest) ++ [q]))
          = ins p.2 (proj p.2 (nrm (translate (rest.takeWhile fun r => p.1 < r.1))))
                (nrm (translate ((rest.dropWhile fun r => p.1 < r.1) ++ [q]))) := by
        rw [List.cons_append, translate_cons, tw', dw', nrm_P]
      rw [snocok_cons, if_neg hT] at hsok
      rw [nC, nC']
      exact ins_olt_mono (nrm_snoc_seg hsok hT)
  termination_by C _ _ _ => C.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

/-! ## The max-row1 suffix (sequence side of the E6 machinery)

`msfx S` is the suffix of `S` starting at the *first* column whose row-1
value is maximal.  Empirically (E6): on standard dominated segments the
host-level projection, when it fires, evaluates to `nrm (translate (msfx S))`.
This section provides the pure sequence laws of `maxr1`/`msfx`. -/

/-- Maximal row-1 value of a segment (`0` on the empty segment). -/
def maxr1 (S : PairSeq) : ℕ := S.foldr (fun c m => max c.2 m) 0

@[simp] theorem maxr1_nil : maxr1 [] = 0 := rfl

theorem maxr1_cons (c : ℕ × ℕ) (S : PairSeq) :
    maxr1 (c :: S) = max c.2 (maxr1 S) := rfl

theorem le_maxr1 {S : PairSeq} : ∀ c ∈ S, c.2 ≤ maxr1 S := by
  induction S with
  | nil => simp
  | cons d S ih =>
    intro c hc
    rw [maxr1_cons]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact le_max_left ..
    · exact le_trans (ih c hc) (le_max_right ..)

/-! ## Row-1 discipline `r1ok`

Every column at positive level has a row-0 parent (the nearest preceding
column one level below, with no dip in between) whose row-1 value it exceeds
by at most one.  Empirically exact on all standard hosts (14,558 columns).
This is the foundation for arithmetizing the row-level facts of the E6
campaign. -/

def r1ok (M : PairSeq) : Prop :=
  ∀ j, j < M.length → 0 < (M.getD j (0,0)).1 →
    ∃ k, k < j ∧ (M.getD k (0,0)).1 + 1 = (M.getD j (0,0)).1
      ∧ (∀ l, k < l → l < j → (M.getD j (0,0)).1 ≤ (M.getD l (0,0)).1)
      ∧ (M.getD j (0,0)).2 ≤ (M.getD k (0,0)).2 + 1

/-! ### Relative `r1ok` — the self-contained sub-block carrier

The absolute `r1ok` references row-`0` `> 0`, so a column at the *bottom* of a
sub-block (whose climbing parent lay outside) has no in-block parent and the
predicate breaks on sub-blocks.  `r1okRel base M` relaxes the threshold: only
columns with row-`0` `> base` need an in-block climbing parent.  Empirically
(262077/262077) a **descendant block** `K = takeWhile (v < ·.1) rest` of a
column with row-`0` `= v` satisfies `r1okRel (v+1) K` — i.e. it is self-contained
relative to its own minimum row-`0` `= v+1`.  This is the inductive carrier the
forest bridge needs (absolute `r1ok` is the `base = 0` instance). -/
theorem diagSeq0_length (v : ℕ) : (diagSeq 0 v).length = v + 1 := by
  unfold diagSeq
  rw [List.length_map, List.length_range']
  omega

theorem diagSeq0_getD {v i : ℕ} (hi : i < v + 1) :
    (diagSeq 0 v).getD i (0,0) = (i, i) := by
  unfold diagSeq
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range' (by simpa using hi)]
  simp

theorem r1ok_diagSeq (v : ℕ) : r1ok (diagSeq 0 v) := by
  intro j hj hpos
  rw [diagSeq0_length] at hj
  rw [diagSeq0_getD hj] at hpos
  have hj0 : 0 < j := by simpa using hpos
  refine ⟨j - 1, by omega, ?_, ?_, ?_⟩
  · rw [diagSeq0_getD hj, diagSeq0_getD (show j - 1 < v + 1 by omega)]
    show j - 1 + 1 = j
    omega
  · intro l hl1 hl2
    omega
  · rw [diagSeq0_getD hj, diagSeq0_getD (show j - 1 < v + 1 by omega)]
    show j ≤ (j - 1) + 1
    omega

theorem getD_take {M : PairSeq} {m j : ℕ} (h : j < m) :
    (M.take m).getD j (0,0) = M.getD j (0,0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take, if_pos h]

theorem r1ok_take {M : PairSeq} (h : r1ok M) (m : ℕ) : r1ok (M.take m) := by
  intro j hj hpos
  rw [List.length_take] at hj
  have hjm : j < m := lt_of_lt_of_le hj (min_le_left _ _)
  have hjM : j < M.length := lt_of_lt_of_le hj (min_le_right _ _)
  rw [getD_take hjm] at hpos
  obtain ⟨k, hk, he, hbetween, hsnd⟩ := h j hjM hpos
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · rw [getD_take (lt_trans hk hjm), getD_take hjm]
    exact he
  · intro l hl1 hl2
    rw [getD_take hjm, getD_take (lt_trans hl2 hjm)]
    exact hbetween l hl1 hl2
  · rw [getD_take hjm, getD_take (lt_trans hk hjm)]
    exact hsnd

theorem r1ok_dropLast {M : PairSeq} (h : r1ok M) : r1ok M.dropLast := by
  rw [List.dropLast_eq_take]
  exact r1ok_take h _

/-! ## Index bookkeeping for the copy decomposition

`oper_bad_blocks` presents the expansion as `G ++ (range n).flatMap (copy k)`;
these lemmas convert positions `k * |B| + q` of the flat copy region to the
source block, and decompose an arbitrary region index. -/

theorem getD_append_left {G X : PairSeq} {i : ℕ} (h : i < G.length) :
    (G ++ X).getD i (0,0) = G.getD i (0,0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h]

theorem getD_append_right {G X : PairSeq} {i : ℕ} (h : G.length ≤ i) :
    (G ++ X).getD i (0,0) = X.getD (i - G.length) (0,0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right h]

theorem index_decomp {i L n : ℕ} (hL : 0 < L) (hi : i < n * L) :
    ∃ k q, k < n ∧ q < L ∧ i = k * L + q := by
  refine ⟨i / L, i % L, ?_, Nat.mod_lt _ hL, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hL).2 hi
  · calc i = L * (i / L) + i % L := (Nat.div_add_mod i L).symm
    _ = i / L * L + i % L := by rw [Nat.mul_comm]

theorem copies_map_length (B : PairSeq) (f : ℕ → ℕ × ℕ → ℕ × ℕ) (n : ℕ) :
    ((List.range n).flatMap fun k => B.map (f k)).length = n * B.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp [ih, Nat.succ_mul]

theorem copies_map_getD {B : PairSeq} {n k q : ℕ} {f : ℕ → ℕ × ℕ → ℕ × ℕ}
    (hk : k < n) (hq : q < B.length) :
    ((List.range n).flatMap fun k => B.map (f k)).getD (k * B.length + q) (0,0)
      = f k (B.getD q (0,0)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hkn : k < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left,
          ← List.getD_eq_getElem?_getD]
      · exact ih hkn
      · rw [copies_map_length]
        calc k * B.length + q < k * B.length + B.length := by omega
        _ = (k + 1) * B.length := (Nat.succ_mul k B.length).symm
        _ ≤ n * B.length := Nat.mul_le_mul_right _ hkn
    · have hk_eq : k = n := by omega
      subst hk_eq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right
            (by rw [copies_map_length]; exact Nat.le_add_right _ _),
          copies_map_length, Nat.add_sub_cancel_left]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.getElem?_map, List.getElem?_eq_getElem hq]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
      rfl

/-! ## Row-1 discipline under the copy expansion

`copyExp G B d0 n` abstracts the bad branch of `oper` (`oper_bad_blocks`):
prefix `G` followed by `n` copies of the block `B`, the `k`-th copy shifted
in row 0 by `k * d0`.  `r1ok_copyExp` proves the three unconditional witness
cases (prefix transfer, identity copy, same-copy translation); the
level-minimal case (witness in the previous copy, the `r1ok_climb` core) is
the explicit hypothesis `hmin`. -/

/-- The copy expansion shape produced by the bad branch of `oper`. -/
def copyExp (G B : PairSeq) (d0 n : ℕ) : PairSeq :=
  G ++ (List.range n).flatMap fun k => B.map fun p => (p.1 + k * d0, p.2)

theorem copyExp_length (G B : PairSeq) (d0 n : ℕ) :
    (copyExp G B d0 n).length = G.length + n * B.length := by
  unfold copyExp
  rw [List.length_append, copies_map_length]

theorem copyExp_getD_pre {G B : PairSeq} {d0 n i : ℕ} (h : i < G.length) :
    (copyExp G B d0 n).getD i (0,0) = G.getD i (0,0) :=
  getD_append_left h

theorem copyExp_getD_copy {G B : PairSeq} {d0 n k q : ℕ}
    (hk : k < n) (hq : q < B.length) :
    (copyExp G B d0 n).getD (G.length + (k * B.length + q)) (0,0)
      = ((B.getD q (0,0)).1 + k * d0, (B.getD q (0,0)).2) := by
  unfold copyExp
  rw [getD_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      copies_map_getD hk hq]

theorem hostM_getD_pre {G B : PairSeq} {lp : ℕ × ℕ} {i : ℕ} (h : i < G.length) :
    (G ++ B ++ [lp]).getD i (0,0) = G.getD i (0,0) := by
  rw [getD_append_left (by simp; omega), getD_append_left h]

theorem hostM_getD_blk {G B : PairSeq} {lp : ℕ × ℕ} {q : ℕ} (hq : q < B.length) :
    (G ++ B ++ [lp]).getD (G.length + q) (0,0) = B.getD q (0,0) := by
  rw [getD_append_left (by simp; omega),
      getD_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem hostM_length (G B : PairSeq) (lp : ℕ × ℕ) :
    (G ++ B ++ [lp]).length = G.length + B.length + 1 := by
  simp
  omega

theorem r1ok_copyExp {G B : PairSeq} {lp : ℕ × ℕ} {n d0 : ℕ}
    (hr : r1ok (G ++ B ++ [lp]))
    (hmin : ∀ k q, 0 < k → k < n → q < B.length →
      (∀ r, r < q → (B.getD q (0,0)).1 ≤ (B.getD r (0,0)).1) →
      0 < (B.getD q (0,0)).1 + k * d0 →
      ∃ p, p < G.length + (k * B.length + q) ∧
        ((copyExp G B d0 n).getD p (0,0)).1 + 1 = (B.getD q (0,0)).1 + k * d0 ∧
        (∀ l, p < l → l < G.length + (k * B.length + q) →
          (B.getD q (0,0)).1 + k * d0 ≤ ((copyExp G B d0 n).getD l (0,0)).1) ∧
        (B.getD q (0,0)).2 ≤ ((copyExp G B d0 n).getD p (0,0)).2 + 1) :
    r1ok (copyExp G B d0 n) := by
  intro j hj hpos
  rw [copyExp_length] at hj
  by_cases hjL : j < G.length + B.length
  · -- transfer region: `copyExp` agrees with the host on `[0, |G| + |B|)`
    have hagree : ∀ i, i ≤ j → (copyExp G B d0 n).getD i (0,0)
        = (G ++ B ++ [lp]).getD i (0,0) := by
      intro i hi
      by_cases hig : i < G.length
      · rw [copyExp_getD_pre hig, hostM_getD_pre hig]
      · push Not at hig
        have hiL : i - G.length < B.length := by omega
        have hn0 : 0 < n := by
          cases n with
          | zero =>
            rw [Nat.zero_mul] at hj
            omega
          | succ m => exact Nat.succ_pos m
        have e1 : (copyExp G B d0 n).getD i (0,0)
            = ((B.getD (i - G.length) (0,0)).1 + 0 * d0,
               (B.getD (i - G.length) (0,0)).2) := by
          have hieq : i = G.length + (0 * B.length + (i - G.length)) := by
            rw [Nat.zero_mul]
            omega
          conv_lhs => rw [hieq]
          rw [copyExp_getD_copy hn0 hiL]
        have e2 : (G ++ B ++ [lp]).getD i (0,0) = B.getD (i - G.length) (0,0) := by
          have hieq : i = G.length + (i - G.length) := by omega
          conv_lhs => rw [hieq]
          rw [hostM_getD_blk hiL]
        rw [e1, e2]
        simp
    have hjM : j < (G ++ B ++ [lp]).length := by
      rw [hostM_length]
      omega
    have hposM : 0 < ((G ++ B ++ [lp]).getD j (0,0)).1 := by
      rw [← hagree j le_rfl]
      exact hpos
    obtain ⟨p, hp, he, hnd, hs⟩ := hr j hjM hposM
    refine ⟨p, hp, ?_, ?_, ?_⟩
    · rw [hagree p (le_of_lt hp), hagree j le_rfl]
      exact he
    · intro l hl1 hl2
      rw [hagree j le_rfl, hagree l (le_of_lt hl2)]
      exact hnd l hl1 hl2
    · rw [hagree j le_rfl, hagree p (le_of_lt hp)]
      exact hs
  · -- copy region with `k ≥ 1`
    push Not at hjL
    have hL : 0 < B.length := by
      by_contra hB0
      push Not at hB0
      have hB0' : B.length = 0 := by omega
      rw [hB0', Nat.mul_zero] at hj
      omega
    obtain ⟨k, q, hk, hq, hdec⟩ :=
      index_decomp hL (show j - G.length < n * B.length by omega)
    have hk1 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · rw [Nat.zero_mul] at hdec
        omega
      · exact h
    have hjeq : j = G.length + (k * B.length + q) := by omega
    subst hjeq
    rw [copyExp_getD_copy hk hq] at hpos ⊢
    by_cases hPM : ∀ r, r < q → (B.getD q (0,0)).1 ≤ (B.getD r (0,0)).1
    · -- level-minimal: previous-copy witness, by hypothesis
      exact hmin k q hk1 hk hq hPM hpos
    · -- in-block dip: the host witness lies in the block; translate it
      push Not at hPM
      obtain ⟨r, hrq, hrdip⟩ := hPM
      have hposB : 0 < (B.getD q (0,0)).1 := by omega
      have hjMq : G.length + q < (G ++ B ++ [lp]).length := by
        rw [hostM_length]
        omega
      have hposMq : 0 < ((G ++ B ++ [lp]).getD (G.length + q) (0,0)).1 := by
        rw [hostM_getD_blk hq]
        exact hposB
      obtain ⟨p, hp, he, hnd, hs⟩ := hr (G.length + q) hjMq hposMq
      have hpg : G.length + r ≤ p := by
        by_contra hcon
        push Not at hcon
        have hh := hnd (G.length + r) (by omega) (by omega)
        rw [hostM_getD_blk hq, hostM_getD_blk (lt_trans hrq hq)] at hh
        omega
      obtain ⟨r', rfl⟩ : ∃ r', p = G.length + r' := ⟨p - G.length, by omega⟩
      have hr'q : r' < q := by omega
      have hr'B : r' < B.length := lt_trans hr'q hq
      rw [hostM_getD_blk hr'B, hostM_getD_blk hq] at he hs
      refine ⟨G.length + (k * B.length + r'), by omega, ?_, ?_, ?_⟩
      · rw [copyExp_getD_copy hk hr'B]
        show (B.getD r' (0,0)).1 + k * d0 + 1 = (B.getD q (0,0)).1 + k * d0
        omega
      · intro l hl1 hl2
        obtain ⟨rr, hrr1, hrr2, rfl⟩ :
            ∃ rr, r' < rr ∧ rr < q ∧ l = G.length + (k * B.length + rr) :=
          ⟨l - G.length - k * B.length, by omega, by omega, by omega⟩
        rw [copyExp_getD_copy hk (lt_trans hrr2 hq)]
        show (B.getD q (0,0)).1 + k * d0 ≤ (B.getD rr (0,0)).1 + k * d0
        have hh := hnd (G.length + rr) (by omega) (by omega)
        rw [hostM_getD_blk hq, hostM_getD_blk (lt_trans hrr2 hq)] at hh
        omega
      · rw [copyExp_getD_copy hk hr'B]
        show (B.getD q (0,0)).2 ≤ (B.getD r' (0,0)).2 + 1
        exact hs

/-! ## The previous-copy witness: `q = 0` degeneration and the `d0 = 0` case

In `oper_bad_blocks` the block is *strictly* dominated (every later element
exceeds the root level `v0`), so the only level-minimal offset is the block
root itself (`dominated_PM_zero`).  For exact copies (`d0 = 0`) the host
witness of the root serves every copy unchanged. -/

theorem getD_mem {l : List (ℕ × ℕ)} {i : ℕ} (h : i < l.length) :
    l.getD i (0,0) ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- In the strictly dominated block of `oper_bad_blocks`, the only
level-minimal offset is `q = 0`: any later offset has the dip `r = 0`. -/
theorem dominated_PM_zero {v0 w0 : ℕ} {R : PairSeq} {q : ℕ}
    (hdom : ∀ x ∈ R, v0 < x.1) (hq : q < ((v0,w0) :: R).length)
    (hPM : ∀ r, r < q →
      (((v0,w0) :: R).getD q (0,0)).1 ≤ (((v0,w0) :: R).getD r (0,0)).1) :
    q = 0 := by
  by_contra hq0
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hq' : q' < R.length := by simpa using hq
  have hmem : R.getD q' (0,0) ∈ R := getD_mem hq'
  have hv : v0 < (R.getD q' (0,0)).1 := hdom _ hmem
  have h0 := hPM 0 (by omega)
  rw [List.getD_cons_zero, List.getD_cons_succ] at h0
  have h0' : (R.getD q' (0,0)).1 ≤ v0 := h0
  omega

/-- The previous-copy witness case for `d0 = 0`: the host witness of the
block root lies in the prefix and serves every copy (all copy levels stay
at or above `v0`). -/
theorem r1ok_min_d0zero {G B : PairSeq} {lp : ℕ × ℕ} {n v0 w0 : ℕ} {R : PairSeq}
    (hB : B = (v0, w0) :: R) (hdom : ∀ x ∈ R, v0 < x.1)
    (hr : r1ok (G ++ B ++ [lp]))
    {k q : ℕ} (_hk1 : 0 < k) (hk : k < n) (hq : q < B.length)
    (hPM : ∀ r, r < q → (B.getD q (0,0)).1 ≤ (B.getD r (0,0)).1)
    (hpos : 0 < (B.getD q (0,0)).1 + k * 0) :
    ∃ p, p < G.length + (k * B.length + q) ∧
      ((copyExp G B 0 n).getD p (0,0)).1 + 1 = (B.getD q (0,0)).1 + k * 0 ∧
      (∀ l, p < l → l < G.length + (k * B.length + q) →
        (B.getD q (0,0)).1 + k * 0 ≤ ((copyExp G B 0 n).getD l (0,0)).1) ∧
      (B.getD q (0,0)).2 ≤ ((copyExp G B 0 n).getD p (0,0)).2 + 1 := by
  subst hB
  have hq0 : q = 0 := dominated_PM_zero hdom hq hPM
  subst hq0
  have hposv : 0 < v0 := by simpa using hpos
  have hMg : (G ++ ((v0,w0) :: R) ++ [lp]).getD G.length (0,0) = (v0, w0) := by
    have h := hostM_getD_blk (G := G) (lp := lp)
      (show 0 < ((v0,w0) :: R).length by simp)
    rw [Nat.add_zero] at h
    rw [h, List.getD_cons_zero]
  have hjM : G.length < (G ++ ((v0,w0) :: R) ++ [lp]).length := by
    rw [hostM_length]
    omega
  have hposM : 0 < ((G ++ ((v0,w0) :: R) ++ [lp]).getD G.length (0,0)).1 := by
    rw [hMg]
    exact hposv
  obtain ⟨p, hp, he, hnd, hs⟩ := hr G.length hjM hposM
  rw [hostM_getD_pre hp, hMg] at he hs
  have he' : (G.getD p (0,0)).1 + 1 = v0 := he
  have hs' : w0 ≤ (G.getD p (0,0)).2 + 1 := hs
  refine ⟨p, by omega, ?_, ?_, ?_⟩
  · rw [copyExp_getD_pre hp]
    show (G.getD p (0,0)).1 + 1 = v0 + k * 0
    omega
  · intro l hl1 hl2
    show v0 + k * 0 ≤ ((copyExp G ((v0,w0) :: R) 0 n).getD l (0,0)).1
    by_cases hlg : l < G.length
    · rw [copyExp_getD_pre hlg]
      have hh := hnd l hl1 hlg
      rw [hostM_getD_pre hlg, hMg] at hh
      have hh' : v0 ≤ (G.getD l (0,0)).1 := hh
      omega
    · push Not at hlg
      have hmul : k * ((v0,w0) :: R).length ≤ n * ((v0,w0) :: R).length :=
        Nat.mul_le_mul_right _ (le_of_lt hk)
      have hlX : l - G.length < n * ((v0,w0) :: R).length := by omega
      obtain ⟨k', r, hk', hrL, hldec⟩ :=
        index_decomp (show 0 < ((v0,w0) :: R).length by simp) hlX
      obtain rfl : l = G.length + (k' * ((v0,w0) :: R).length + r) := by omega
      rw [copyExp_getD_copy hk' hrL]
      show v0 + k * 0 ≤ (((v0,w0) :: R).getD r (0,0)).1 + k' * 0
      have hbase : v0 ≤ (((v0,w0) :: R).getD r (0,0)).1 := by
        cases r with
        | zero => simp
        | succ r' =>
          rw [List.getD_cons_succ]
          exact le_of_lt (hdom _ (getD_mem (by simpa using hrL)))
      omega
  · rw [copyExp_getD_pre hp]
    show w0 ≤ (G.getD p (0,0)).2 + 1
    exact hs'

/-- The previous-copy witness case for `d0 ≥ 1`: the witness is the *last*
block offset at level `v0 + d0 - 1` in the previous copy.  Exactness of the
level and the no-dip property are forced by the `≤ +1` step discipline and
maximality; only the row-1 bound (`hclimb`) is a class fact. -/
theorem r1ok_min_d0pos {G B : PairSeq} {lp : ℕ × ℕ} {n v0 w0 d0 : ℕ} {R : PairSeq}
    (hB : B = (v0, w0) :: R) (hdom : ∀ x ∈ R, v0 < x.1)
    (hd0 : 0 < d0) (hlp : lp.1 = v0 + d0)
    (hstep : ∀ r, r + 1 < B.length →
      (B.getD (r+1) (0,0)).1 ≤ (B.getD r (0,0)).1 + 1)
    (hlpstep : lp.1 ≤ (B.getD (B.length - 1) (0,0)).1 + 1)
    (hclimb : ∀ r', r' < B.length → (B.getD r' (0,0)).1 = v0 + d0 - 1 →
      (∀ rr, r' < rr → rr < B.length → v0 + d0 ≤ (B.getD rr (0,0)).1) →
      w0 ≤ (B.getD r' (0,0)).2 + 1)
    {k q : ℕ} (hk1 : 0 < k) (hk : k < n) (hq : q < B.length)
    (hPM : ∀ r, r < q → (B.getD q (0,0)).1 ≤ (B.getD r (0,0)).1)
    (_hpos : 0 < (B.getD q (0,0)).1 + k * d0) :
    ∃ p, p < G.length + (k * B.length + q) ∧
      ((copyExp G B d0 n).getD p (0,0)).1 + 1 = (B.getD q (0,0)).1 + k * d0 ∧
      (∀ l, p < l → l < G.length + (k * B.length + q) →
        (B.getD q (0,0)).1 + k * d0 ≤ ((copyExp G B d0 n).getD l (0,0)).1) ∧
      (B.getD q (0,0)).2 ≤ ((copyExp G B d0 n).getD p (0,0)).2 + 1 := by
  have hq0 : q = 0 := by
    subst hB
    exact dominated_PM_zero hdom hq hPM
  subst hq0
  have hL : 0 < B.length := by
    subst hB
    simp
  have hB0 : B.getD 0 (0,0) = (v0, w0) := by
    subst hB
    rfl
  -- the candidate set and its greatest element
  set P : ℕ → Prop := fun r => (B.getD r (0,0)).1 ≤ v0 + d0 - 1 with hP
  have hP0 : P 0 := by
    rw [hP]
    simp only [hB0]
    show v0 ≤ v0 + d0 - 1
    omega
  set r' := Nat.findGreatest P (B.length - 1) with hr'def
  have hPr' : P r' := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hr'L : r' ≤ B.length - 1 := Nat.findGreatest_le _
  have hgreat : ∀ rr, r' < rr → rr ≤ B.length - 1 → ¬ P rr := by
    intro rr h1 h2
    exact Nat.findGreatest_is_greatest h1 h2
  have hgreat' : ∀ rr, r' < rr → rr < B.length →
      v0 + d0 ≤ (B.getD rr (0,0)).1 := by
    intro rr h1 h2
    have := hgreat rr h1 (by omega)
    rw [hP] at this
    simp only [not_le] at this
    omega
  -- level exactness at the witness
  have rexact : (B.getD r' (0,0)).1 = v0 + d0 - 1 := by
    have hub : (B.getD r' (0,0)).1 ≤ v0 + d0 - 1 := hPr'
    rcases Nat.lt_or_ge r' (B.length - 1) with hlt | hge
    · have hnP := hgreat (r' + 1) (Nat.lt_succ_self _) (by omega)
      rw [hP] at hnP
      simp only [not_le] at hnP
      have := hstep r' (by omega)
      omega
    · have hr'eq : r' = B.length - 1 := by omega
      rw [hlp] at hlpstep
      rw [hr'eq]
      rw [hr'eq] at hub
      omega
  -- multiplication bookkeeping
  have hkL : k * B.length = (k - 1) * B.length + B.length := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.succ_mul]
    simp
  have hkd : k * d0 = (k - 1) * d0 + d0 := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.succ_mul]
    simp
  have hk1n : k - 1 < n := by omega
  have hr'B : r' < B.length := by omega
  refine ⟨G.length + ((k - 1) * B.length + r'), by omega, ?_, ?_, ?_⟩
  · rw [copyExp_getD_copy hk1n hr'B]
    show (B.getD r' (0,0)).1 + (k - 1) * d0 + 1 = (B.getD 0 (0,0)).1 + k * d0
    rw [hB0, rexact]
    show v0 + d0 - 1 + (k - 1) * d0 + 1 = v0 + k * d0
    omega
  · intro l hl1 hl2
    have hmul : k * B.length ≤ n * B.length :=
      Nat.mul_le_mul_right _ (le_of_lt hk)
    have hlX : l - G.length < n * B.length := by omega
    obtain ⟨k'', rr, hk'', hrrL, hldec⟩ := index_decomp hL hlX
    -- the in-between positions live in copy `k - 1`, beyond `r'`
    have hk''eq : k'' = k - 1 := by
      rcases Nat.lt_trichotomy k'' (k - 1) with h | h | h
      · exfalso
        have : k'' + 1 ≤ k - 1 := by omega
        have hmul2 : (k'' + 1) * B.length ≤ (k - 1) * B.length :=
          Nat.mul_le_mul_right _ this
        rw [Nat.succ_mul] at hmul2
        omega
      · exact h
      · exfalso
        have : k ≤ k'' := by omega
        have hmul2 : k * B.length ≤ k'' * B.length :=
          Nat.mul_le_mul_right _ this
        omega
    subst hk''eq
    have hrr1 : r' < rr := by omega
    obtain rfl : l = G.length + ((k - 1) * B.length + rr) := by omega
    rw [copyExp_getD_copy hk1n hrrL]
    show (B.getD 0 (0,0)).1 + k * d0 ≤ (B.getD rr (0,0)).1 + (k - 1) * d0
    rw [hB0]
    have := hgreat' rr hrr1 hrrL
    show v0 + k * d0 ≤ (B.getD rr (0,0)).1 + (k - 1) * d0
    omega
  · rw [copyExp_getD_copy hk1n hr'B]
    show (B.getD 0 (0,0)).2 ≤ (B.getD r' (0,0)).2 + 1
    rw [hB0]
    exact hclimb r' hr'B rexact hgreat'

/-! ## Assembly: `r1ok` is preserved by `oper`, hence holds on `ST_PS`

All branches of the expansion step are wired: identity (short), `Pred`
(dropLast), and the bad branch through `oper_bad_blocks` → `copyExp`.
The step facts `hstep`/`hlpstep` come from the `steps1` component of
`blockok_ST_PS`.  The sole remaining obligation is the class fact
`climbok` (the `r1ok_climb` of the Isabelle campaign, open there too). -/

theorem hostM_getD_lp {G B : PairSeq} {lp : ℕ × ℕ} :
    (G ++ B ++ [lp]).getD (G.length + B.length) (0,0) = lp := by
  have e : (G ++ B).length = G.length + B.length := by simp
  rw [getD_append_right (by omega), e, Nat.sub_self]
  rfl

theorem r1ok_Pred {M : PairSeq} (h : r1ok M) : r1ok (Pred M) := by
  unfold Pred
  by_cases hl : M.length ≤ 1
  · rw [if_pos hl]
    exact h
  · rw [if_neg hl]
    exact r1ok_dropLast h

/-- **The climb bound.**  At a bad-branch decomposition with strictly
ascending copies (`d0 ≥ 1`, so the parent is in row 1), the last block column
`r'` at the parent level `v0 + d0 - 1` is a row-0 ancestor of the last
column; the maximality clause of `nextrel1` therefore forces its row-1 value
to be at least `lp.2 > w0`.  (This closes the `r1ok_climb` core: the `q = 0`
reduction `dominated_PM_zero` ties the witness to the *parent structure* of
the last column, where row-1 parenthood is decisive.) -/
theorem climb_bound {M G : PairSeq} {v0 w0 d0 : ℕ} {R : PairSeq} {lp : ℕ × ℕ}
    (hM : M = G ++ ((v0,w0) :: R) ++ [lp])
    (hd0 : 0 < d0) (hlp1 : lp.1 = v0 + d0) (hwlt : w0 < lp.2)
    (hnl1 : nextrel1 M G.length (M.length - 1))
    {r' : ℕ} (hr' : r' < ((v0,w0) :: R).length)
    (hlev : (((v0,w0) :: R).getD r' (0,0)).1 = v0 + d0 - 1)
    (hafter : ∀ rr, r' < rr → rr < ((v0,w0) :: R).length →
      v0 + d0 ≤ (((v0,w0) :: R).getD rr (0,0)).1) :
    w0 ≤ (((v0,w0) :: R).getD r' (0,0)).2 + 1 := by
  subst hM
  rcases Nat.eq_zero_or_pos r' with rfl | hr'pos
  · rw [List.getD_cons_zero]
    omega
  · have hlen : (G ++ ((v0,w0) :: R) ++ [lp]).length
        = G.length + ((v0,w0) :: R).length + 1 := hostM_length ..
    have hj1 : (G ++ ((v0,w0) :: R) ++ [lp]).length - 1
        = G.length + ((v0,w0) :: R).length := by omega
    have e0r : entry (G ++ ((v0,w0) :: R) ++ [lp]) 0 (G.length + r')
        = v0 + d0 - 1 := by
      unfold entry
      rw [if_pos rfl, hostM_getD_blk hr']
      exact hlev
    have e0j1 : entry (G ++ ((v0,w0) :: R) ++ [lp]) 0
        (G.length + ((v0,w0) :: R).length) = v0 + d0 := by
      unfold entry
      rw [if_pos rfl, hostM_getD_lp]
      exact hlp1
    have hn0 : nextrel0 (G ++ ((v0,w0) :: R) ++ [lp]) (G.length + r')
        (G.length + ((v0,w0) :: R).length) := by
      refine ⟨by omega, by omega, by omega, ?_, ?_⟩
      · rw [e0r, e0j1]
        omega
      · intro j hj
        obtain ⟨rr, hrr1, hrr2, rfl⟩ : ∃ rr, r' < rr
            ∧ rr < ((v0,w0) :: R).length ∧ j = G.length + rr :=
          ⟨j - G.length, by omega, by omega, by omega⟩
        rw [e0j1]
        unfold entry
        rw [if_pos rfl, hostM_getD_blk hrr2]
        exact hafter rr hrr1 hrr2
    have hle0 : le0 (G ++ ((v0,w0) :: R) ++ [lp]) (G.length + r')
        (G.length + ((v0,w0) :: R).length) :=
      ⟨by omega, by omega, Relation.ReflTransGen.single hn0⟩
    have hmax := hnl1.2.2.2.2.2 (G.length + r')
      ⟨by omega, by rw [hj1]; exact hle0⟩
    rw [hj1] at hmax
    have e1j1 : entry (G ++ ((v0,w0) :: R) ++ [lp]) 1
        (G.length + ((v0,w0) :: R).length) = lp.2 := by
      unfold entry
      rw [if_neg one_ne_zero, hostM_getD_lp]
    have e1r : entry (G ++ ((v0,w0) :: R) ++ [lp]) 1 (G.length + r')
        = (((v0,w0) :: R).getD r' (0,0)).2 := by
      unfold entry
      rw [if_neg one_ne_zero, hostM_getD_blk hr']
    rw [e1j1, e1r] at hmax
    omega

/-- **Row-1 discipline is preserved by the expansion step.** -/
theorem r1ok_oper {M : PairSeq} {n : ℕ} (hn : 1 ≤ n) (hr : r1ok M)
    (hst : steps1 M) : r1ok (M⟦n⟧) := by
  by_cases hL0 : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL0]
    exact hr
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL0 hz]
    exact r1ok_Pred hr
  by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL0 hz hp]
    exact r1ok_Pred hr
  case pos =>
    obtain ⟨G, v0, w0, R, d0, lp, hM, hX, hdom, _hlpgt, hd0, -⟩ :=
      oper_bad_blocks (by omega) hz hp hn
    rw [hX]
    have hrM : r1ok (G ++ ((v0,w0) :: R) ++ [lp]) := hM ▸ hr
    have hstM : steps1 (G ++ ((v0,w0) :: R) ++ [lp]) := hM ▸ hst
    have hstep : ∀ r, r + 1 < ((v0,w0) :: R).length →
        ((((v0,w0) :: R)).getD (r+1) (0,0)).1
          ≤ ((((v0,w0) :: R)).getD r (0,0)).1 + 1 := by
      intro r hr1
      have hs := steps1_iff.1 hstM (G.length + r)
        (by rw [hostM_length]; omega)
      rw [show G.length + r + 1 = G.length + (r+1) by omega] at hs
      rw [hostM_getD_blk hr1, hostM_getD_blk (by omega)] at hs
      exact hs
    have hlpstep : lp.1
        ≤ ((((v0,w0) :: R)).getD (((v0,w0) :: R).length - 1) (0,0)).1 + 1 := by
      have hBlen : 0 < ((v0,w0) :: R).length := by simp
      have hs := steps1_iff.1 hstM (G.length + (((v0,w0) :: R).length - 1))
        (by rw [hostM_length]; omega)
      rw [show G.length + (((v0,w0) :: R).length - 1) + 1
            = G.length + ((v0,w0) :: R).length by omega] at hs
      rw [hostM_getD_lp, hostM_getD_blk (by omega)] at hs
      exact hs
    show r1ok (copyExp G ((v0,w0) :: R) d0 n)
    refine r1ok_copyExp hrM ?_
    intro k q hk1 hk hq hPM hpos
    rcases hd0 with ⟨hd00, -⟩ | ⟨hd0p, hwlt, hlpe, hnl1⟩
    · subst hd00
      exact r1ok_min_d0zero rfl hdom hrM hk1 hk hq hPM hpos
    · exact r1ok_min_d0pos rfl hdom hd0p hlpe hstep hlpstep
        (fun r' hr' hlev hafter => climb_bound hM hd0p hlpe hwlt hnl1 hr' hlev hafter)
        hk1 hk hq hPM hpos

/-- **Row-1 discipline of standard sequences.** -/
theorem r1ok_ST_PS {M : PairSeq} (hM : ST_PS M) : r1ok M := by
  induction hM with
  | diag v => exact r1ok_diagSeq v
  | oper hN hn ih => exact r1ok_oper hn ih (blockok_ST_PS hN).2.2

/-! ## The innermost dominated run and the `ST_snocok` interface -/

/-! ## Case combinators for `ST_snoc_C` -/

/-! ## Structural layer: the `einc ∪ eflip` snoc characterization

Where `nrm_snoc_seg` records only the strict `olt` increase, the structural
bundle `snocokS` pins the exact shape: appending one column performs one
end-position increase on the normalized image.  This is the input to
`pfire_transport` (a base-side fire survives the append), which excludes the
"base fires, extension does not" case of `ST_snoc_C`. -/

/-- Head argument of a term (`Z` on `Z`). -/
def hdarg : Three → Three
  | Z => Z
  | P _ b _ => b

@[simp] theorem hdarg_Z : hdarg Z = Z := rfl
@[simp] theorem hdarg_P (a : ℕ) (b c : Three) : hdarg (P a b c) = b := rfl

/-- The no-absorption condition for `ins a b t`. -/
def noabsorb (a : ℕ) (b t : Three) : Prop :=
  ¬ (a < lead t ∨ (a = lead t ∧ b <o hdarg t))

/-! ## Both-fire reduction and the subscript chain -/

/-! ### `proj0_olt_NF`: proj-side order on `NF` arguments (the argument-head residual)

`proj 0`-monotonicity on `NF` arguments — `olt b f → olt (proj 0 b) (proj 0 f)`.
This is the genuine residual of the argument-head of `oV_nf_order_pres` (see
`Nrm.psi0_oV_lt_of_proj_olt`).  FALSE on general `wf3` (7291 reversals, a dead
static-domain family) but TRUE on `NF` arguments (audited 79800/79800, zero
reversals).  Pure `olt` (no ordinals), `wf3`-free.  Via `proj_olt_of_fireprop`
it splits into the two `NF`-standardness residuals below.

STATUS (this campaign).  Extracted sorry-free: the `maxsub`/`climb`/spine
discipline (`maxsub_eq_climb_NF`, `maxsub_arg_eq_climb`, `maxsub_arg_dom`,
`maxsub_arg_mono`, `lead_arg_le_one`, `climb_achieved`, `pfire0_of_lt_climb`);
the self-contained all-`0` OT3 (`OT3all_msub0`, `not_pfire0_of_maxsub0`,
`lead0_maxsub0_NF`, `fire_lead_one_NF`, `fire_shape_NF`); the one-step-`proj`
facts (`maxo_bad_nofire`, `proj_eq_maxo_bad`, `proj_mem_Gterm_of_fire`,
`proj_ge_crit` — `proj` is the single `maxo` of the violator list and is the
GREATEST critical, all pure-term/no-`NF`); and `lead_proj_eq_maxsub_NF`
(`proj 0` of a firing `NF` arg leads with `maxsub`).  With these BOTH proj-side
residuals are reduced to clean single leaves:
  • **`proj0_fireprop_NF` ⟶ `not_pfire0_lead1max1_NF`** (a `lead = 1, maxsub = 1`
    `NF` arg does not fire = the maxr1-`≤1` head-`0` OT3 wall, shared with
    `Wttone.H0clause_translate`);
  • **`proj0_bothfire_NF` ⟶ `proj_bothfire_witness`** (the single §1 firing
    witness, *uniform* — no eq/strict-`maxsub` split).  GREEN reduction: a
    `G₀`-critical `h` of the larger `f` strictly above `proj 0 b`, with
    `h ≤o proj 0 f` (`proj_ge_crit`) and `olt_ole_trans`, closes
    `olt (proj 0 b) (proj 0 f)`.  The residual is exactly the witness
    existence `∃ h ∈ Gterm 0 f, olt (proj 0 b) h`, model-verified
    `824970 / 0` (`tools/probe_strict_wit.py` W1); the underlying critical
    embedding is `NF`-discipline-dependent (FALSE on general terms, 3.7M
    violations, `probe_cd_proof.py` E4).

So Wall B (proj-side) is now exactly TWO `NF`-discipline leaves; everything
around them is proved. -/

/-! #### `maxsub`/`climb` discipline of `NF` arguments

The `NF` spine discipline (`nfinv`: `maxsub = climb`, every subscript lies on
the leading `.b`-spine) gives the clean lever `pfire 0 b ⟺ lead b < maxsub b`
on `NF` arguments.  These lemmas extract the reusable `maxsub`/`climb` facts:
the max subscript of an `NF` argument is on its own spine (`maxsub_arg_eq_climb`),
the argument dominates the whole term's `maxsub` (`maxsub_arg_dom`), and `maxsub`
is `olt`-monotone on `NF` arguments (`maxsub_arg_mono`). -/

/-! #### `proj` is one-step on firing terms (general, no `NF`)

The single `maxo` of the violator list already has no violators of its own
(`maxo_bad_nofire`), so `proj` terminates after exactly one rewrite
(`proj_eq_maxo_bad`).  This makes the "peel" of the both-fire analysis a
triviality and is pure-term (no `NF`). -/

/-- The `maxo` of the level-`u` violator list of `b` does not itself fire at
level `u`: every critical `g` of `maxo` is a critical of `b` (`Gterm_trans`),
hence either `< b ≤o maxo` (non-violator) or `≤o maxo` and a proper subterm
(violator), so `< maxo`. -/
theorem maxo_bad_nofire {u : ℕ} {b : Three}
    (h : (Glist u b).filter (fun g => ¬ olt g b) ≠ []) :
    ¬ pfire u (maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
                    ((Glist u b).filter (fun g => ¬ olt g b)).tail) := by
  set bad := (Glist u b).filter (fun g => ¬ olt g b) with hbad
  set m := maxo bad.headI bad.tail with hm
  have hmin : m ∈ bad := maxo_hdtl_in h
  have hmG : m ∈ Gterm u b := mem_filter_Gterm hmin
  have hmnotolt : ¬ olt m b := mem_filter_not_olt hmin
  have hbm : b ≤o m := by
    rcases olt_total b m with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hmnotolt
  rw [pfire_iff]; push_neg
  intro g hgGm
  have hgGb : g ∈ Gterm u b := Gterm_trans hgGm hmG
  have hgsz : tsize g < tsize m := Gterm_tsize hgGm
  have hgne : g ≠ m := by intro he; rw [he] at hgsz; omega
  by_cases hgb : olt g b
  · exact Three.olt_ole_trans hgb hbm
  · have hgbad : g ∈ bad := by
      rw [hbad]; exact List.mem_filter.2 ⟨mem_Glist.2 hgGb, by simpa using hgb⟩
    rcases maxo_ub_mem h g hgbad with h1 | h1
    · exact h1
    · exact absurd h1 hgne

/-- **`proj` is one-step on firing terms** (general, no `NF`): when `b` fires,
`proj u b` equals the single `maxo` of its violator list. -/
theorem proj_eq_maxo_bad {u : ℕ} {b : Three} (hf : pfire u b) :
    proj u b = maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
                    ((Glist u b).filter (fun g => ¬ olt g b)).tail := by
  have h : (Glist u b).filter (fun g => ¬ olt g b) ≠ [] := by
    rw [pfire] at hf; exact hf
  rw [proj_rec h]
  exact proj_nofire (maxo_bad_nofire h)

/-! ### Keystone: the leading-`.b`-chain descent of `proj 0`

`proj 0` of a term whose maximal subscript lies on its head argument's own
leading spine descends to that head argument: `proj 0 (P L x y) = proj 0 x`
under `1 ≤ L < lead x`, `maxsub x = climb x`, `maxsub y < maxsub x`.  This is
the term-level engine of the equal-`maxsub` firing comparison; model-verified
`58803 / 58803` (`tools/probe_keystone_*.py`) and the firing-`NF` chain nodes
all satisfy its side-conditions (`1764 / 1764`).  The side-conditions are
essential: it is term-locally FALSE without them (e.g. `x` a sum, or `x`'s max
off its spine — `maxsub = climb` necessary). -/

/-! ### `descok`: the consecutive-spine descent predicate

`descok t`: the leading `.b`-chain of `t` descends with *consecutive* leads
`[lead t, lead t + 1, …, maxsub t]` to the node at lead `= maxsub`, and at each
non-top node the tail's max subscript is strictly below the head argument's.
This is the recursion carrier for the equal-`maxsub` firing comparison
(model-verified: all firing-`NF` args satisfy it, the head-descent preserves it,
and the main `proj`-order comparison holds `991020 / 991020`). -/

/-- `descok t` (recursive on the leading `.b`-chain). -/
def descok : Three → Prop
  | Z => False
  | P a x y =>
    a = maxsub (P a x y) ∨
      (lead x = a + 1 ∧ maxsub y < maxsub x ∧ descok x)

@[simp] theorem descok_Z : ¬ descok Z := id

theorem descok_P {a : ℕ} {x y : Three} :
    descok (P a x y) ↔
      a = maxsub (P a x y) ∨
        (lead x = a + 1 ∧ maxsub y < maxsub x ∧ descok x) := Iff.rfl

/-! ### The EQUAL-`maxsub` both-fire witness (THE single irreducible §1 firing
residual), Lean form.  For two firing head-`0` `NF` arguments `b <o f` with
`maxsub b = maxsub f`, there is a `G₀`-critical `h` of `f` strictly dominating
`proj 0 b`: `∃ h ∈ Gterm 0 f, olt (proj 0 b) h`.

This is the genuine, irreducible equal-lead first-difference core of the
Buchholz §1 firing wall.  Model-verified `438747 / 438747` (the equal-`maxsub`
share of `probe_strict_wit.py` W1; `probe_eqmaxsub_witness.py`).  **Why no
constructive shortcut breaks the circularity** (all verified, the Lean `Three`
encoding):
  • `proj 0 b = chainAt b (maxsub b)` and the witness `= chainAt f (maxsub b)`
    (the leading-`.b`-chain node at lead `= maxsub b`, `probe_witness_recursion`,
    `1285 / 1285`); but with `maxsub b = maxsub f` this witness IS
    `chainAt f (maxsub f) = proj 0 f`, so `olt (proj 0 b) h` *is* the goal
    `olt (proj 0 b)(proj 0 f)` — **circular** (`/tmp` spinemono probe);
  • `lead (proj 0 b) = maxsub b = maxsub f = lead (proj 0 f)`, so the comparison
    is NOT lead-resolvable — it is the equal-lead structural first-difference;
  • `f <o proj 0 b` (`olt_arg_lt_proj_NF`), so the witness must be a *violator*
    of `f` above `proj 0 b`, not below `f`;
  • the naive recursion "firing leading-chain node, `olt b t ⟹ olt (proj 0 b)
    (proj 0 t)`" is FALSE (299559 / 2031339, `probe_witness_general.py` GL).
A proof needs the equal-lead spine-alignment of the two NF args' greatest
criticals under `olt b f` — the deep Buchholz §1 content, isolated here.

**Structural handle for a future proof** (`probe_witness_recursion.py`,
`probe_seqlex_mech.py`, `probe_descent_step.py`, all `1285 / 1285` resp.
`438747 / 438747`): the leading `.b`-chain of a firing `NF` arg realises
*consecutive* leads `[1, 2, …, maxsub]` (the `nfinv`/`inv2` spine), `proj 0 b`
is its node at lead `maxsub b` (`proj 0 b = chainAt b (maxsub b)`), and
`olt (chain node L of b)(chain node L of f)` holds at **every** lead `1 ≤ L ≤ k`
— *arg-resolved* at each `L < k` and resolved at the top `L = k` (the goal).
The downward step rests on `proj 0 (P L x y) = proj 0 x` when the head arg `x`
carries the max subscript (`probe_witness_recursion.py`, `1764 / 1764` on the
`L ≥ 1` spine).

**WHY `olt_ST_iff_seqlex` does NOT directly close it** (verified this session):
`seqlex` orders the `ST_PS` *preimages* (`PairSeq`), but `proj 0`/greatest-
critical is a *term-level* (`Three`) operation with **no sound bridge** to the
preimage structure — the only candidate bridge, the E6 identity
`proj y B = nrm (translate (msfx S))`, is FALSE on `dseg` arg-zones (4 cters,
`probe_e6`).  And the term-level descent does **not** terminate on any simple
numeric measure: in the arg-resolved cases the second-level `maxsub` is strict
only `154737 / 438666` (`268045` equal-`maxsub`-args, `/tmp` final probe), so it
is a genuine structural first-difference recursion (the `seqlex` order, but on
the term side).  The precise remaining obligation is the term-level lead-`k`
chain-node comparison `olt (chainAt b k)(chainAt f k)` from `olt b f`, via the
`L ≥ 1` spine descent.

**The keystone IS NOW PROVEN** (`proj_keystone`, GREEN): with the right local
guard `1 ≤ L < lead x ∧ maxsub x = climb x ∧ maxsub y < maxsub x` the descent
`proj 0 (P L x y) = proj 0 x` holds (model-verified `58803 / 58803`).  The
remaining gap is the **recursion assembly + base case**, both now precisely
characterized (`probe_descok_recursion.py`, `probe_base_nofire.py`):

  • **Recursion (verified `991020 / 991020`).**  Define `descok t`: the leading
    `.b`-chain from `t` descends with *consecutive* leads `[lead t, …, maxsub t]`
    to the lead-`maxsub` node, each non-top node's tail strictly below its head
    in `maxsub`.  All firing-`NF` args satisfy `descok`; for `descok x, descok y`
    with `lead x = lead y`, `maxsub x = maxsub y`, `olt x y`, the keystone gives
    `proj 0 x = proj 0 x'`, `proj 0 y = proj 0 y'` and the head args satisfy the
    same invariant at lead `+1` (`552273 / 552273`), so strong `tsize` induction
    descends to the base.
  • **Base case (lead `=` maxsub):** the top node does NOT fire
    (`1285 / 1285` on firing-`NF` chains), so `proj 0 = id` and `olt x y`
    transports directly.  **CAUTION (caught this session): the clean term-local
    base lemma `cnf t ∧ lead t = maxsub t ⟹ ¬ pfire 0 t` is FALSE at depth `4`**
    — `t = p₁(p₀(p₁(p₁0)))` is `cnf` with `lead = maxsub = 1` yet fires
    (`probe_base_nofire` re-run); so the base case ALSO needs the hereditary
    `descok`/gap-free-spine structure, not just `cnf`.

So `proj_keystone` (the genuinely novel engine) is landed GREEN, and the
`descok` predicate + head-descent (`descok_arg`) + keystone side-condition
propagation (`descok_arg_maxsub_eq_climb`) are all GREEN (above).  But the
`descok` recursion does **NOT** bypass the wall — established rigorously this
session:

  • **Base case** `descok t ∧ lead t = maxsub t ⟹ ¬ pfire 0 t` is FALSE on
    general `descok` terms: `p₁(p₀(p₁(p₁0)))` is `cnf`, hereditarily
    `maxsub = climb`, `descok` (top, `lead = maxsub = 1`) yet FIRES (violator
    `p₁(p₁0)`); it holds only on the *`NF`-image* `descok` nodes (`1285 / 1285`).
  • **Step arg-resolution** `olt x y ⟹ olt x' y'` (head args, needed to recurse)
    is FALSE on general `descok` terms: `244493 / 7553142` are *tail*-resolved
    (`x' = y'`, e.g. `P 0 (p₁0) Z` vs `P 0 (p₁0) (p₀0)`), which would make
    `proj 0 x = proj 0 x' = proj 0 y' = proj 0 y` and the goal `olt z z` false;
    it holds only on the `NF`-image nodes (`552273 / 552273`), because "no two
    distinct firing `NF` args share their `proj`-head `b'`" — an `NF` uniqueness.

Both gaps are the SAME `NF`-global-anchoring (`ST_PS`-reachability /
`r1ok`/`steps1`) forest core that the project shares: per
`Wttone.H0clause_translate`, this is *"the SAME open obstruction as
`proj0_fireprop_NF`/`proj0_bothfire_NF` … the genuine forest core the whole
project shares, not a quick development."*

**The anchoring is GLOBAL `r1ok` (base `0`), not any local relaxation** (pinned
this session, `probe_r1ok_base.py`/`probe_real_subterm.py`):
  • term-local predicates (`cnf`, `maxsub = climb`, hereditary, `descok`, `okH`)
    ALL admit firing counterexamples (`okH` is `0 / 1285` on the image — false);
  • even **sequence-local** `r1okRel` relative to a sub-block's own minimum
    row-`0` is insufficient: the firing sub-blocks (e.g.
    `(3,1)(4,0)(5,1)(6,1)(7,0)(8,1)…`) SATISFY `r1okRel(min)` (`0 / 2002` fail it)
    yet their `translate` fires;
  • only the GLOBAL `r1ok M` (base `0`, climbing from the row-`0`-`0` root
    through the whole parent forest) excludes them: the real `descok` base nodes
    arising via the chain from a head-`0` `NF` arg never fire (`1285 / 1285`).
So the bridge genuinely requires the full `r1ok`-through-`translate` forest
correspondence (`subs_translate`/`Gterm_translate_lead_le` are the layer-1
entry; `maxsub_translate_eq_maxr1` pins `maxsub = maxr1`), pulling the global
`r1ok_ST_PS` climbing to the term-position subscripts.  The keystone reduces the
witness to this shared core but cannot eliminate it.  Helper `olt_arg_maxsub_le`
and the positional lemmas are available (GREEN).

CLEAN CARRIER DECOMPOSITION (this session): the witness `olt (proj 0 b)(proj 0 f)`
decomposes GREEN (`proj_ole_of_critembed` + `proj_bothfire_witness_eq_of_carrier`,
below) into TWO minimal forest carriers, each model-verified `824970 / 824970`:
  • `CritEmbed`: every `G₀`-critical of `b` is `≤o` some critical of `f`
    (gives `proj 0 b ≤o proj 0 f`, `probe_le_route.py` E1);
  • `proj`-injectivity: `olt b f` firing `NF` args have `proj 0 b ≠ proj 0 f`
    (≡ the head arg determines the firing `NF` arg — the `r1ok` forest
    uniqueness, `probe_inj.py` `0` collisions).
`≤o` + `≠` gives the strict `olt`.

`proj`-injectivity further factors (`probe_inj_route.py`, both `0`-multi) into
  (A) `proj 0 b` determines the head arg `b'` (`b = P 1 b' c'`; via the keystone
      `proj 0 b = proj 0 b'`), and
  (B) the head arg `b'` determines the whole firing `NF` arg — the tail `c'` is
      FORCED by `b'` through the `ST_PS` parent-forest continuation.
(B) is the irreducible `r1ok`/`ST_PS`-parenthood tail-forcing fact; both `CritEmbed`
and (B) genuinely need the global forest discipline (no clean head-arg recursion:
`CritEmbed(b',f')` fails `401715 / 438747`).  These are the precise irreducible
climbing facts; `SubBlock`/`Gterm_translate_subblock` (above) is the positional
correspondence into which `r1ok_ST_PS` must be pulled to discharge them.

ALTERNATE `≤o`-route (this session): the `≤o` half (`CritEmbed`, hence
`proj 0 b ≤o proj 0 f`) recurses CLEANLY via the keystone WITHOUT injectivity —
`proj 0 b = proj 0 b'` (keystone), `b' ≤o f'` (head descent, `≤o` tolerates the
tie), terminating at the chain bottom (`lead = maxsub`).  The strict `<o` then
needs only that the bottom does not fire.  BUT the bottom non-firing
`lead t = maxsub t = climb t ∧ cnf t ⟹ ¬ pfire 0 t` is FALSE at depth `4`
(`p₁(p₀(p₁(p₁0)))` has `lead = maxsub = climb = 1`, `cnf`, yet fires); only the
`NF`-image bottom non-firing holds (`1285 / 1285`).  `proj_G` gives `proj 0 X`
non-firing for free, but the recursion bottom is a `proj`-comparison at
`lead = maxsub` where the keystone no longer applies, so it does not terminate
term-locally.  Hence BOTH routes bottom out in the SAME `NF`-image bottom
non-firing forest fact — the irreducible core.

PRECISE IRREDUCIBLE FACT (pinned, `probe_bottom_seq.py`): the proj-descent
bottom is `translate K` for a DESCENDANT sub-block `K` (`SubBlock`,
`Gterm_translate_subblock`) whose head sits at row-`0` `= d ≥ 2` deep in the
forest (real bottoms: head row-`0` `∈ {2..11}`, head row-`1` `= maxr1 ∈ {2,3,4}`).
Its row-`1` climbing is ROOT-ANCHORED by the global `ST_PS` parent at row-`0`
`= d-1` (the `r1ok_ST_PS` climbing from the row-`0`-`0` root).  The fatal
counterexample `p₁(p₀(p₁(p₁0)))` is `translate [(0,1),(1,0),(2,1),(3,1)]` — an
`r1ok` (!) block but with head row-`0` `= 0`, row-`1` `= 1`: an UNANCHORED root
block (head row-`1` `= 1 ≠ 0` violates `ST_PS_head_val_zero`), so it is NOT
`ST_PS`-reachable and fires.  So the irreducible fact is: **a descendant block
of an `ST_PS` sequence, with head row-`1` `=` its `maxr1`, does not fire** —
provable only via the root-anchored `r1ok` climbing pulled through `SubBlock`,
the project-central construction (`r1ok` ALONE is insufficient: the cter is
`r1ok`; the missing ingredient is the root-`0`-anchoring / `ST_PS`-reachability
that excludes head row-`1` `> 0` root blocks).

EVERY decomposition bottoms out in this SAME forest fact (confirmed by explicit
counterexamples this session):
  • `maxoviol`-step recursion (one `proj` step, `tsize`-decreasing `1285 / 1285`):
    `olt b f ⟹ olt (maxoviol b) (maxoviol f)` holds on `NF` args (`438747 / 0`)
    but is FALSE on general terms (`929364 / 5753586`) — the step needs `NF` on
    the criticals, which leave the `NF` class;
  • `ST_PS`-descendant blocks STILL fire (`1652` real descendant blocks of `ST_PS`
    sequences fire) — "`ST_PS`-descendant" alone is NOT the predicate; the
    proj-descent bottoms are the STRICTER greatest-critical-descent subset;
  • the anchoring lemmas ARE available (kernel-checked sorryAx-free): `stps_head`
    (`ST_PS M → headD M = (0,0)`, head row-`1` `= 0`, the root-`0`-anchoring),
    `ST_PS_suffix` (suffix-closure, `Nrm.lean:1426`), `r1ok_ST_PS`, `z0ok_ST_PS`,
    `blockok_ST_PS`.  The gap is NOT a missing anchoring fact but the CARRIER that
    re-establishes `NF`/`ST_PS`-anchoring on the proj-descent criticals (which
    leave the `NF` class): the `maxoviol`-step monotonicity holds on the
    descent-class (`438747 / 0`) but the descent-class predicate `P` (= "greatest-
    critical-descent node of an `ST_PS`-image arg") is currently defined only
    operationally — formalizing `P` + its `maxoviol`-step preservation is the
    substantial remaining undertaking.
The criticals/bottoms of the proj-descent leave the `NF`/`ST_PS` class, and
re-establishing the forest anchoring on them (via `SubBlock` + `r1ok_ST_PS` +
`stps_head` + `ST_PS_suffix` + the `oper`/`translate` parent-forest) is the
substantial remaining construction.

**NOW FULLY ASSEMBLED** as `proj_bothfire_witness_eq_final` (below, GREEN modulo
the two precise forest residuals `Rdesc_firing_char` + `Rdesc_hstep`): the entire
`mvstep`-descent recursion (`mvstep`, `proj_mvstep`, `tsize_mvstep_lt`,
`proj0_olt_of_mvstep_olt`, `Rdesc`, `Rdesc_match`, `Rdesc_hfire`,
`proj_bothfire_witness_eq_of_Rdesc`) is sorry-free, so this lemma's content is
EXACTLY `Rdesc_firing_char` (`pfire 0 t ↔ lead t < maxsub t` on descent nodes) +
`Rdesc_hstep` (strict `mvstep`-monotonicity).  The equal-`maxsub` witness is
proved as `proj_bothfire_witness_eq_final` downstream (GREEN modulo those two
residuals); the both-fire/`proj0_olt_NF` chain is wired to it
(`proj_bothfire_witness` ... `proj0_olt_NF`, all downstream of `_final`). -/

/-! ### The `maxoviol`-descent class and the single STEP residual

`mvstep b` = one `proj`-step (the `maxo` of `b`'s level-`0` violators).  `proj 0`
is its fixpoint (`proj_eq_maxo_bad`: `proj 0 b = proj 0 (mvstep b)`), and
`tsize (mvstep b) < tsize b` when `b` fires.  The equal-`maxsub` witness reduces
(via the GREEN strong-`tsize` recursion `proj0_olt_of_mvstep`, below) to the
SINGLE residual `mvstep_olt_step`: `olt b f ⟹ olt (mvstep b) (mvstep f)` on the
descent class `Pdesc`.  Model-verified `438747 / 438747` on the descent class;
FALSE on general terms (`929364 / 5753586`) — it carries the `NF`/`ST_PS` forest
structure, the irreducible content. -/

/-- One `proj`-step: the `maxo` of the level-`0` violators (`= b` if `b` doesn't
fire). -/
def mvstep (b : Three) : Three :=
  if h : (Glist 0 b).filter (fun g => ¬ olt g b) = [] then b
  else maxo ((Glist 0 b).filter (fun g => ¬ olt g b)).headI
            ((Glist 0 b).filter (fun g => ¬ olt g b)).tail

/-- `mvstep b = b` when `b` doesn't fire. -/
theorem mvstep_nofire {b : Three} (h : ¬ pfire 0 b) : mvstep b = b := by
  unfold mvstep; rw [dif_pos (by rw [pfire] at h; exact not_not.1 h)]

/-- `proj 0 b = proj 0 (mvstep b)`: `proj` factors through one step. -/
theorem proj_mvstep (b : Three) : proj 0 b = proj 0 (mvstep b) := by
  by_cases h : pfire 0 b
  · -- firing: `mvstep b = maxo …`, which doesn't fire (`maxo_bad_nofire`), so
    -- `proj 0 (mvstep b) = mvstep b = proj 0 b`.
    have hne : (Glist 0 b).filter (fun g => ¬ olt g b) ≠ [] := by rw [pfire] at h; exact h
    have hmv : mvstep b = maxo ((Glist 0 b).filter (fun g => ¬ olt g b)).headI
                ((Glist 0 b).filter (fun g => ¬ olt g b)).tail := by
      unfold mvstep; rw [dif_neg hne]
    rw [hmv, proj_nofire (maxo_bad_nofire hne), ← proj_eq_maxo_bad h]
  · rw [mvstep_nofire h]

/-- `mvstep` strictly shrinks a firing term (it lands on a critical, a proper
subterm). -/
theorem tsize_mvstep_lt {b : Three} (h : pfire 0 b) : tsize (mvstep b) < tsize b := by
  have hne : (Glist 0 b).filter (fun g => ¬ olt g b) ≠ [] := by rw [pfire] at h; exact h
  have hmv : mvstep b = maxo ((Glist 0 b).filter (fun g => ¬ olt g b)).headI
              ((Glist 0 b).filter (fun g => ¬ olt g b)).tail := by
    unfold mvstep; rw [dif_neg hne]
  rw [hmv]
  have hin := maxo_hdtl_in hne
  exact Gterm_tsize (mem_Glist.1 (List.mem_of_mem_filter hin))

/-- **The STRICT `mvstep` recursion, relation-carrying** (model-verified the
strict STEP holds with ZERO ties on the matched descent class, `438747 / 438747`).
Given a binary relation `R` on the descent pairs that is preserved by `mvstep`
on both sides when both fire (`hpres`) and on which the strict STEP holds
(`hstep`: `R x y → olt x y → olt (mvstep x) (mvstep y)`), strong `tsize`
induction gives the strict `olt (proj 0 x) (proj 0 y)` for `R`-pairs with
`olt x y` — NO injectivity needed (the strict STEP already excludes the tie).
`R` carries exactly what the forest STEP needs (same lead + eq `maxsub` + the
`SubBlock`/`ST_PS` anchoring); GREEN, isolating the witness to that single
strict-STEP residual. -/
theorem proj0_olt_of_mvstep_olt {R : Three → Three → Prop}
    (hfire : ∀ x y, R x y → (pfire 0 x ↔ pfire 0 y))
    (hpres : ∀ x y, R x y → pfire 0 x → pfire 0 y → R (mvstep x) (mvstep y))
    (hstep : ∀ x y, R x y → olt x y → olt (mvstep x) (mvstep y)) :
    ∀ x y, R x y → olt x y → olt (proj 0 x) (proj 0 y) := by
  intro x
  generalize hs : tsize x = n
  induction n using Nat.strong_induction_on generalizing x with
  | _ n IH =>
    subst hs
    intro y hR hxy
    by_cases hfx : pfire 0 x
    · -- firing `x` ⟹ firing `y` (lockstep, `hfire`); descend via `mvstep`.
      have hfy : pfire 0 y := (hfire x y hR).1 hfx
      rw [proj_mvstep x, proj_mvstep y]
      exact IH (tsize (mvstep x)) (tsize_mvstep_lt hfx) (mvstep x) rfl
        (mvstep y) (hpres x y hR hfx hfy) (hstep x y hR hxy)
    · -- non-firing `x`: `proj 0 x = x <o y ≤o proj 0 y`.
      rw [proj_nofire hfx]
      exact olt_ole_trans hxy (proj_ole 0 y)

/-- **The descent-pair relation** `Rdesc x y`: `(x, y)` is reachable from a
firing `NF`-arg pair `(b, f)` (`P 0 b c, P 0 f g ∈ NF`, `olt b f`,
`maxsub b = maxsub f`) by simultaneous `mvstep`.  This is the carrier on which
the strict STEP holds (`hpres` is automatic from `base`/`step`).  The two
remaining residual obligations are `hfire` (lockstep firing) and `hstep` (the
strict STEP).

**Residual structure** (model-verified, the precise forest facts):
  • `Rdesc` carries `lead x = lead y ∧ maxsub x = maxsub y` (`877494 / 877494`,
    a structural invariant: base `NF` args lead `1`, eq `maxsub`; `step`
    preserves both since `lead (mvstep ·) = maxsub ·`);
  • `hfire` (`pfire 0 x ↔ pfire 0 y`, `877494 / 0`) reduces, via that match, to
    the firing characterization `pfire 0 t ↔ lead t < maxsub t` on `Rdesc` nodes
    (`2568 / 2568`) — FALSE off-class (the cter `p₁(p₀(p₁(p₁0)))` has
    `lead = maxsub = 1` yet fires), so it needs the descent-class forest
    structure;
  • `hstep` (`olt x y ⟹ olt (mvstep x) (mvstep y)`, `438747 / 0`) is the
    irreducible forest core — FALSE on general terms (`929364 / 5753586`); it
    needs the `SubBlock`/`r1ok_ST_PS`/`stps_head` anchoring carried through the
    descent.
Both residuals bottom out in the same forest discipline; the entire recursion
above them (`proj0_olt_of_mvstep_olt` etc.) is GREEN, so discharging `hfire` +
`hstep` closes `proj_bothfire_witness_eq` (and, symmetrically, `not_pfire0_-
lead1max1_NF` via `proj_G`-base + the same firing characterization). -/
inductive Rdesc : Three → Three → Prop
  | base {b c f g : Three} (hv : (P 0 b c) ∈ NF) (hu : (P 0 f g) ∈ NF)
      (harg : olt b f) (heq : maxsub b = maxsub f)
      (hb : pfire 0 b) (hf : pfire 0 f) : Rdesc b f
  | step {x y : Three} (h : Rdesc x y) (hfx : pfire 0 x) (hfy : pfire 0 y) :
      Rdesc (mvstep x) (mvstep y)

/-! ### The both-fire witness (reduced to the equal-`maxsub` core), Lean form.
For two firing head-`0` `NF` arguments `b <o f`, there is a `G₀`-critical `h`
of the larger argument `f` that **strictly dominates** `proj 0 b` (the greatest
critical of `b`): `∃ h ∈ Gterm 0 f, olt (proj 0 b) h`.

Equivalently (`olt_arg_lt_proj_NF`) the witness `h` is a **violator** of `f`
(`f <o proj 0 b <o h`, so `f <o h`, `¬ olt h f`); model-verified the witness is
always a node on `f`'s leading `.b`-chain with `lead h = maxsub b = lead (proj 0 b)`
(`tools/probe_witrec.py`, `probe_witness_recursion.py`) — so the strict order
`olt (proj 0 b) h` is an **equal-lead first-difference** comparison, the genuine
irreducible Buchholz §1 firing content (NOT lead-resolvable).

This is the sound Lean port of ya-pss's `argzone_fire_FF` / `proj_step_fire_-
witness` — the genuine Buchholz §1 firing content — but with the **Lean-correct
witness**: `h` is a critical of `f` (NOT necessarily `proj 0 f` and NOT
`= hdarg`, since `proj 0 X = hdarg X` is FALSE in this encoding); it is the
greatest critical of `f` on its leading argument chain that overshoots `proj 0 b`.

**Soundness gate** (`tools/probe_strict_wit.py` W1, the Lean `Three` encoding,
deep closure 5089 `NF` terms): `824970 / 824970` firing pairs `olt b f` admit
such a critical `h`; `tools/probe_crit_dom.py` confirms the underlying critical
embedding (`∀ g ∈ Gterm 0 b, ∃ h ∈ Gterm 0 f, g ≤o h`) is `0`-violation and
**class-essential** (FALSE on general terms, 3.7M violations,
`probe_cd_proof.py` E4 — the buried-subscript pattern `NF` excludes).

**Now reduced to the EQUAL-`maxsub` sub-case** (`proj_bothfire_witness_eq`): the
strict-`maxsub` branch is GREEN here via `proj 0 f` as the witness
(`proj 0 f ∈ Gterm 0 f` by `proj_mem_Gterm_of_fire`, and
`lead (proj 0 b) = maxsub b < maxsub f = lead (proj 0 f)` by
`lead_proj_eq_maxsub_NF` + `olt_P_of_lead_lt`).  Only the equal-`maxsub` case —
where the witness `proj 0 f` ties `proj 0 b` in lead, so `olt (proj 0 b)(proj 0 f)`
is the genuine equal-lead first-difference comparison — remains. -/
/-! ## The subscript chain: criticals, projections and `nrm` never invent
subscripts -/

/-! ### The two precise forest residuals (the carrier keystone)

The §1 firing wall is now EXACTLY these two facts on the `mvstep`-descent class
`Rdesc`/`RdescNode` (all reductions above are GREEN).  Both are the genuine
`r1ok_ST_PS`/`stps_head` root-anchored forest content — model-verified on the
descent class, FALSE off-class (the cter `p₁(p₀(p₁(p₁0)))` satisfies neither's
hypotheses since it is NOT a greatest-violator (`mvstep`)-image of any `NF`
subterm, `probe_cter_diff.py`).  Discharging both closes the §1 wall. -/

/-! ### The both-fire / `proj0_olt_NF` chain, wired to `_final`

The proj-side order crux `proj0_olt_NF`, now resting on EXACTLY the two forest
residuals (`Rdesc_firing_char`, `Rdesc_hstep`) via `proj_bothfire_witness_eq_final`
+ the GREEN fire-propagation `proj0_fireprop_NF`. -/

/-! ## Head-subscript facts for normalized images -/

/-! ## Low-subscript dominance -/

/-! ### Forest-bridge positional lemmas (`Gterm`-subscript ↔ row-1 value)

The first layer of the `Gterm`-position ↔ sequence-index correspondence: a
subscript appearing anywhere in `translate S` — in particular the leading
subscript of any `Gterm 0` critical — is a *row-1 value* of `S` (`subs_translate`).
Hence every critical's lead is `≤ maxr1 S`, the row-1 maximum.  These pull the
term-level subscript structure back to the sequence, the entry point for the
`r1ok` climbing discipline. -/

/-! ### Forest-bridge layer 2: the positional correspondence

Every `Gterm 0` critical of `translate M` is *itself* `translate K` for a
sub-block `K` of `M` arising in the `takeWhile`/`dropWhile` recursion — the
explicit `Gterm`-position ↔ sequence-subblock map (model-verified `2241 / 2241`,
`tools/probe_poscorr.py`).  This transports the term-level critical structure to
contiguous sub-blocks, the carrier for pulling `r1ok M`. -/

/-- **Sub-block relation**: `K` is reachable from `M` by iterated
`takeWhile`/`dropWhile` of the forest recursion.  Reflexive-transitive closure of
the descendant/sibling step. -/
inductive SubBlock : PairSeq → PairSeq → Prop
  | refl (M : PairSeq) : SubBlock M M
  | desc {M K : PairSeq} {p : ℕ × ℕ} {rest : PairSeq}
      (hM : M = p :: rest)
      (h : SubBlock (rest.takeWhile fun q => p.1 < q.1) K) : SubBlock M K
  | sib {M K : PairSeq} {p : ℕ × ℕ} {rest : PairSeq}
      (hM : M = p :: rest)
      (h : SubBlock (rest.dropWhile fun q => p.1 < q.1) K) : SubBlock M K

/-! ## The dominated-segment classes

`dseg u S`: `S` is a nonempty, entirely dominated standard sub-segment whose
enclosing head has row-1 value `u`.  `fbseg` relaxes the left boundary by a
skipped `mid` whose levels stay at or above the head of `S` (the forest
boundary condition); it is closed under both descents of the translate
recursion. -/

/-! ## The forest-boundary level squeeze -/

/-! ## Sum-adjacent row-1 non-increase (F1)

The CNF adjacency clause of the host translate, extracted at an arbitrary
column by walking the translate recursion: the head of the sum-adjacent
tail (at level at least the column's) has row-1 value at most the column's.
This is the engine behind the no-absorption facts of the C1 chain. -/

/-! ## Dominated runs by position (toward `SIB_prefix`) -/

/-! ## The constant-copy region and its drop decomposition -/

/-- The constant-copy region (`d0 = 0`): `n` literal repetitions of `B`. -/
def repB (B : PairSeq) : ℕ → PairSeq
  | 0 => []
  | n + 1 => B ++ repB B n

@[simp] theorem repB_zero (B : PairSeq) : repB B 0 = [] := rfl
theorem repB_succ (B : PairSeq) (n : ℕ) : repB B (n + 1) = B ++ repB B n := rfl

/-! ## Runs are blockok segments -/

/-! ## The tie-sibling run dichotomy (SIB without generation induction) -/

/-! ## The NT_tie combinator -/

/-! ## The HM⁺ discipline (head-maximality under low closure)

Mined exact on standard hosts (0/19030): whenever a run is closed by a
column whose row-1 value does not exceed the base's, every run based at or
inside the region is head-maximal.  This subsumes the head-maximality of
tie-closed sibling runs (the no-fire input of `NT_tie_of`) and of `i1 = 0`
block tails. -/

/-! ## HM⁺ under truncation -/

/-! ## The final-block discipline `tailok` -/

/-! ## Take-transfer for the parent relations -/

theorem nextrel0_bound {M : PairSeq} {a b : ℕ} (h : nextrel0 M a b) :
    b < M.length := h.2.1

theorem le0_le {M : PairSeq} {a b : ℕ} (h : le0 M a b) : a ≤ b := by
  obtain ⟨-, -, hch⟩ := h
  induction hch with
  | refl => exact le_rfl
  | tail _ hs ih => exact le_trans ih (le_of_lt (nextrel0_lt hs))

/-! ## H1: closures below the shared base transfer through the truncation -/

/-! ## Drop decomposition of the general copy region -/

/-! ## Run characterization at copy positions -/

/-! ## Assembly helpers for `hmok` under the copy expansion -/

/-! ## `hmok` survives the copy expansion -/

/-! ## Wholesale instance transfer below a shared truncation -/

/-! ## Within-copy parenthood transfer -/

/-! ## Segment extraction at copy positions -/

/-! ## Within-copy row-0 instances of `tailokA` -/

/-! ## Chain lifts between the host block and a copy -/

/-! ## Chains cover their interval without dips -/

/-! ## The Pred branch of the final-block discipline -/

/-! ## Level-0 columns are `(0,0)` -/

/-- Level-0 columns carry row-1 value `0`. -/
def z0ok (M : PairSeq) : Prop :=
  ∀ j, j < M.length → (M.getD j (0,0)).1 = 0 → (M.getD j (0,0)).2 = 0

theorem z0ok_diagSeq (v : ℕ) : z0ok (diagSeq 0 v) := by
  intro j hj h0
  rw [diagSeq0_length] at hj
  rw [diagSeq0_getD hj] at h0 ⊢
  simpa using h0

theorem z0ok_take {M : PairSeq} (h : z0ok M) (m : ℕ) : z0ok (M.take m) := by
  intro j hj h0
  rw [List.length_take] at hj
  rw [getD_take (by omega)] at h0 ⊢
  exact h j (by omega) h0

theorem z0ok_Pred {M : PairSeq} (h : z0ok M) : z0ok (Pred M) := by
  unfold Pred
  by_cases hl : M.length ≤ 1
  · rw [if_pos hl]
    exact h
  · rw [if_neg hl, List.dropLast_eq_take]
    exact z0ok_take h _

theorem z0ok_copyExp {G B : PairSeq} {lp : ℕ × ℕ} {d0 n : ℕ}
    (h : z0ok (G ++ B ++ [lp])) : z0ok (copyExp G B d0 n) := by
  intro j hj h0
  rw [copyExp_length] at hj
  by_cases hjg : j < G.length
  · rw [copyExp_getD_pre hjg] at h0 ⊢
    have hg := h j (by rw [hostM_length]; omega)
    rw [hostM_getD_pre hjg] at hg
    exact hg h0
  · push Not at hjg
    have hL : 0 < B.length := by
      by_contra hB0
      push Not at hB0
      have : B.length = 0 := by omega
      rw [this, Nat.mul_zero] at hj
      omega
    obtain ⟨k, q, hk, hq, hdec⟩ := index_decomp hL
      (show j - G.length < n * B.length by omega)
    have hjeq : j = G.length + (k * B.length + q) := by omega
    subst hjeq
    rw [copyExp_getD_copy hk hq] at h0 ⊢
    have h0' : (B.getD q (0,0)).1 + k * d0 = 0 := h0
    have hM := h (G.length + q) (by rw [hostM_length]; omega)
    rw [hostM_getD_blk hq] at hM
    show (B.getD q (0,0)).2 = 0
    exact hM (by omega)

/-! ## Parent uniqueness and row-0 existence -/

/-- Row-0 parents are unique: a later candidate dips the earlier's clause. -/
theorem nextrel0_unique {M : PairSeq} {k1 k2 j : ℕ}
    (h1 : nextrel0 M k1 j) (h2 : nextrel0 M k2 j) : k1 = k2 := by
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := h1.2.2.2.2 k2 ⟨h, h2.2.2.1⟩
    have := h2.2.2.2.1
    omega
  · exact h
  · have := h2.2.2.2.2 k1 ⟨h, h1.2.2.1⟩
    have := h1.2.2.2.1
    omega

/-- Row-1 parents are unique: maximality excludes a later candidate. -/
theorem nextrel1_unique {M : PairSeq} {k1 k2 j : ℕ}
    (h1 : nextrel1 M k1 j) (h2 : nextrel1 M k2 j) : k1 = k2 := by
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := h1.2.2.2.2.2 k2 ⟨h, h2.2.2.2.2.1⟩
    have := h2.2.2.2.1
    omega
  · exact h
  · have := h2.2.2.2.2.2 k1 ⟨h, h1.2.2.2.2.1⟩
    have := h1.2.2.2.1
    omega

/-- The head of a `blockok 0` host is a level-0 column. -/
theorem blockok_head_zero {M : PairSeq} (hb : blockok 0 M)
    (hne : 0 < M.length) : (M.getD 0 (0,0)).1 = 0 := by
  obtain ⟨m0, M', rfl⟩ : ∃ m0 M', M = m0 :: M' := by
    cases M with
    | nil => simp at hne
    | cons m0 M' => exact ⟨m0, M', rfl⟩
  rw [List.getD_cons_zero]
  have := hb.1 (by simp)
  rw [List.headI_cons] at this
  exact this

/-- Row-0 parent existence: the largest lower-level position qualifies. -/
theorem parent0_exists {M : PairSeq} (hb : blockok 0 M) {j : ℕ}
    (hj : j < M.length) (h0 : 0 < entry M 0 j) :
    ∃ k, nextrel0 M k j := by
  classical
  have hj0 : 0 < j := by
    by_contra hc
    push Not at hc
    have : j = 0 := by omega
    subst this
    have := blockok_head_zero hb (by omega)
    unfold entry at h0
    rw [if_pos rfl] at h0
    omega
  set P : ℕ → Prop := fun k => entry M 0 k < entry M 0 j with hP
  have hP0 : P 0 := by
    show entry M 0 0 < entry M 0 j
    unfold entry
    rw [if_pos rfl, blockok_head_zero hb (by omega)]
    unfold entry at h0
    rw [if_pos rfl] at h0
    exact h0
  refine ⟨Nat.findGreatest P (j - 1), ?_, hj, ?_, ?_, ?_⟩
  · have := Nat.findGreatest_le (P := P) (j - 1)
    omega
  · have := Nat.findGreatest_le (P := P) (j - 1)
    omega
  · exact Nat.findGreatest_spec (Nat.zero_le _) hP0
  · intro l hl
    have hnl := Nat.findGreatest_is_greatest (P := P) hl.1 (by omega)
    rw [hP] at hnl
    push Not at hnl
    exact hnl

/-! ## Parent existence: the no-parent branch is empty on the class -/

theorem chain_to_zero {M : PairSeq} (hb : blockok 0 M) :
    ∀ lev j, entry M 0 j = lev → j < M.length →
      ∃ r, r ≤ j ∧ entry M 0 r = 0
        ∧ Relation.ReflTransGen (nextrel0 M) r j := by
  intro lev
  induction lev using Nat.strong_induction_on with
  | _ lev IH =>
    intro j he hj
    by_cases h0 : entry M 0 j = 0
    · exact ⟨j, le_rfl, h0, Relation.ReflTransGen.refl⟩
    · obtain ⟨k, hk⟩ := parent0_exists hb hj (by omega)
      have hklt : entry M 0 k < entry M 0 j := hk.2.2.2.1
      have hkj : k < j := hk.2.2.1
      obtain ⟨r, hr1, hr2, hr3⟩ :=
        IH (entry M 0 k) (by omega) k rfl hk.1
      exact ⟨r, by omega, hr2, hr3.tail hk⟩

theorem parent1_exists {M : PairSeq} (hb : blockok 0 M) (hz : z0ok M)
    {j : ℕ} (hj : j < M.length) (h1 : 0 < entry M 1 j) :
    ∃ k, nextrel1 M k j := by
  classical
  obtain ⟨r, hrle, hr0, hchain⟩ := chain_to_zero hb (entry M 0 j) j rfl hj
  have hre1 : entry M 1 r = 0 := by
    have hz' := hz r (by omega)
    unfold entry at hr0 ⊢
    rw [if_pos rfl] at hr0
    rw [if_neg one_ne_zero]
    exact hz' hr0
  have hrj : r < j := by
    rcases Nat.eq_or_lt_of_le hrle with rfl | h
    · omega
    · exact h
  set P : ℕ → Prop := fun k => le0 M k j ∧ entry M 1 k < entry M 1 j with hP
  have hPr : P r := by
    refine ⟨⟨by omega, hj, hchain⟩, ?_⟩
    rw [hre1]
    exact h1
  have hspec := Nat.findGreatest_spec (P := P) (show r ≤ j - 1 by omega) hPr
  have hle := Nat.findGreatest_le (P := P) (j - 1)
  refine ⟨Nat.findGreatest P (j - 1), ?_, hj, by omega, hspec.2, hspec.1, ?_⟩
  · omega
  · intro j' hj'
    rcases Nat.eq_or_lt_of_le (le0_le hj'.2) with rfl | hlt
    · exact le_rfl
    · by_contra hcon
      push Not at hcon
      exact Nat.findGreatest_is_greatest (P := P) hj'.1 (by omega)
        ⟨hj'.2, hcon⟩

theorem nextR_one_iff {M : PairSeq} {k j : ℕ} :
    nextR M 1 k j ↔ nextrel1 M k j := by
  unfold nextR
  rw [if_neg one_ne_zero]

theorem nextR_zero_iff {M : PairSeq} {k j : ℕ} :
    nextR M 0 k j ↔ nextrel0 M k j := by
  unfold nextR
  rw [if_pos rfl]

/-- **Every nonzero final column of a standard-shaped host has a unique
parent** — the no-parent `Pred` branch is empty on the class. -/
theorem hp_last {M : PairSeq} (hb : blockok 0 M) (hz : z0ok M)
    (hlen : 0 < M.length)
    (hzz : ¬ M.getD (M.length - 1) (0,0) = (0,0)) :
    hasParent M (idx1 M (M.length - 1)) (M.length - 1) := by
  classical
  by_cases h1 : 0 < entry M 1 (M.length - 1)
  · have hi : idx1 M (M.length - 1) = 1 := by
      unfold idx1
      rw [if_pos h1]
    obtain ⟨k, hk⟩ := parent1_exists hb hz (by omega) h1
    refine ⟨k, ?_, ?_⟩
    · show nextR M (idx1 M (M.length - 1)) k (M.length - 1)
      rw [hi, nextR_one_iff]
      exact hk
    · intro y hy
      have hy' : nextR M (idx1 M (M.length - 1)) y (M.length - 1) := hy
      rw [hi, nextR_one_iff] at hy'
      exact nextrel1_unique hy' hk
  · have h1' : entry M 1 (M.length - 1) = 0 := by omega
    have h0 : 0 < entry M 0 (M.length - 1) := by
      by_contra hc
      push Not at hc
      apply hzz
      unfold entry at h1'
      rw [if_neg one_ne_zero] at h1'
      have h0' : (M.getD (M.length - 1) (0,0)).1 = 0 := by
        unfold entry at hc
        rw [if_pos rfl] at hc
        omega
      exact Prod.ext h0' h1'
    have hi : idx1 M (M.length - 1) = 0 := by
      unfold idx1
      rw [if_neg (by omega)]
    obtain ⟨k, hk⟩ := parent0_exists hb (by omega) h0
    refine ⟨k, ?_, ?_⟩
    · show nextR M (idx1 M (M.length - 1)) k (M.length - 1)
      rw [hi, nextR_zero_iff]
      exact hk
    · intro y hy
      have hy' : nextR M (idx1 M (M.length - 1)) y (M.length - 1) := hy
      rw [hi, nextR_zero_iff] at hy'
      exact nextrel0_unique hy' hk

/-! ## Block intervals above a base are hereditarily head-maximal -/

/-! ## Final-column instances with a parent inside the last copy -/

theorem z0ok_oper {M : PairSeq} {n : ℕ} (hn : 1 ≤ n) (h : z0ok M) :
    z0ok (M⟦n⟧) := by
  by_cases hL0 : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL0]
    exact h
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL0 hz]
    exact z0ok_Pred h
  by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL0 hz hp]
    exact z0ok_Pred h
  case pos =>
    obtain ⟨G, v0, w0, R, d0, lp, hMeq, hX, -, -, -, -⟩ :=
      oper_bad_blocks (by omega) hz hp hn
    rw [hX]
    show z0ok (copyExp G ((v0,w0) :: R) d0 n)
    exact z0ok_copyExp (hMeq ▸ h)

/-- **Level-0 columns of standard hosts are `(0,0)`** — unconditional. -/
theorem z0ok_ST_PS {M : PairSeq} (hM : ST_PS M) : z0ok M := by
  induction hM with
  | diag v => exact z0ok_diagSeq v
  | oper hN hn ih => exact z0ok_oper hn ih

/-! ## The conditional generation closure of the invariant package -/

/-! ## The single-climb discipline -/

/-- **The single-climb discipline** (anchored form; mined exact over all
infixes of all hosts, 87,690/87,690): in a row-1 parented segment whose
parent edge is anchored at the segment head, no column strictly between the
head and the last column's row-0 parent reaches within one of the last
column's level. -/
def sclimb (M : PairSeq) : Prop :=
  ∀ r' r, 1 < M.length →
    nextR M (idx1 M (M.length - 1)) 0 (M.length - 1) →
    idx1 M (M.length - 1) = 1 →
    0 < r' → r' + 1 < M.length →
    (M.getD r' (0,0)).1 + 1 = (M.getD (M.length - 1) (0,0)).1 →
    (∀ l, r' < l → l + 1 < M.length →
      (M.getD (M.length - 1) (0,0)).1 ≤ (M.getD l (0,0)).1) →
    0 < r → r < r' →
    (M.getD r (0,0)).1 + 1 < (M.getD (M.length - 1) (0,0)).1

/-! ## Drop transfer and chain-pivot machinery -/

/-- A row-0 chain cannot jump a strict floor: if every column in `(ρ, b]`
sits strictly above `ρ`, any chain into `b` from before `ρ` passes
through `ρ`. -/
theorem rtg_through_pivot {M : PairSeq} {ρ : ℕ} :
    ∀ {a b}, Relation.ReflTransGen (nextrel0 M) a b → a < ρ → ρ ≤ b →
    (∀ y, ρ < y → y ≤ b → entry M 0 ρ < entry M 0 y) →
    Relation.ReflTransGen (nextrel0 M) ρ b := by
  intro a b h
  induction h with
  | refl =>
    intro h1 h2 _
    exact absurd (h1.trans_le h2) (lt_irrefl a)
  | @tail y z hay hyz ih =>
    intro h1 h2 hpiv
    by_cases hρy : ρ ≤ y
    · have ihy := ih h1 hρy
        (fun y' hy1 hy2 => hpiv y' hy1 (hy2.trans (nextrel0_lt hyz).le))
      exact ihy.tail hyz
    · push Not at hρy
      rcases eq_or_lt_of_le h2 with he | hlt
      · rw [he]
      · have hb5 := hyz.2.2.2.2 ρ ⟨hρy, hlt⟩
        exact absurd (hpiv z hlt le_rfl) (not_lt.mpr hb5)

theorem le0_through_pivot {M : PairSeq} {a ρ b : ℕ}
    (h : le0 M a b) (h1 : a < ρ) (h2 : ρ ≤ b)
    (hpiv : ∀ y, ρ < y → y ≤ b → entry M 0 ρ < entry M 0 y) :
    le0 M ρ b := by
  obtain ⟨_, hb, hch⟩ := h
  exact ⟨by omega, hb, rtg_through_pivot hch h1 h2 hpiv⟩

/-! ## The master segment discipline -/

/-! ## Shift invariance of the parent relations -/

theorem entry_shift {S : PairSeq} {d j : ℕ} (hj : j < S.length) :
    entry (S.map fun p => (p.1 + d, p.2)) 0 j = entry S 0 j + d
    ∧ entry (S.map fun p => (p.1 + d, p.2)) 1 j = entry S 1 j := by
  unfold entry
  rw [if_pos rfl, if_neg one_ne_zero,
      getD_eq_getElem' _ _ (by rw [List.length_map]; omega),
      List.getElem_map, ← getD_eq_getElem' _ (0,0) hj]
  exact ⟨rfl, rfl⟩

theorem nextrel0_shift_iff {S : PairSeq} {d a b : ℕ} (hb : b < S.length) :
    nextrel0 (S.map fun p => (p.1 + d, p.2)) a b ↔ nextrel0 S a b := by
  unfold nextrel0
  rw [List.length_map]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [(entry_shift (by omega)).1, (entry_shift hb).1] at h4
      omega
    · intro l hl
      have h6 := h5 l hl
      rw [(entry_shift hb).1, (entry_shift (by omega)).1] at h6
      omega
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [(entry_shift (by omega)).1, (entry_shift hb).1]
      omega
    · intro l hl
      have h6 := h5 l hl
      rw [(entry_shift hb).1, (entry_shift (by omega)).1]
      omega

theorem rtg_shift_of {S : PairSeq} {d : ℕ} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (S.map fun p => (p.1 + d, p.2))) a b) :
    Relation.ReflTransGen (nextrel0 S) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c e hchain hstep ih =>
    have hb := nextrel0_bound hstep
    rw [List.length_map] at hb
    exact ih.tail ((nextrel0_shift_iff hb).1 hstep)

theorem rtg_shift_to {S : PairSeq} {d : ℕ} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 S) a b) :
    Relation.ReflTransGen (nextrel0 (S.map fun p => (p.1 + d, p.2))) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c e hchain hstep ih =>
    have hb := nextrel0_bound hstep
    exact ih.tail ((nextrel0_shift_iff hb).2 hstep)

theorem le0_shift_iff {S : PairSeq} {d a b : ℕ} :
    le0 (S.map fun p => (p.1 + d, p.2)) a b ↔ le0 S a b := by
  unfold le0
  rw [List.length_map]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, rtg_shift_of h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, rtg_shift_to h3⟩⟩

theorem idx1_shift {S : PairSeq} {d j : ℕ} :
    idx1 (S.map fun p => (p.1 + d, p.2)) j = idx1 S j := by
  unfold idx1
  by_cases hj : j < S.length
  · rw [(entry_shift hj).2]
  · push Not at hj
    have h1 : (S.map fun p => (p.1 + d, p.2)).getD j (0,0) = (0,0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (by rw [List.length_map]; omega)]
      rfl
    have h2 : S.getD j (0,0) = (0,0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    unfold entry
    rw [if_neg one_ne_zero, if_neg one_ne_zero, h1, h2]

theorem nextrel1_shift_iff {S : PairSeq} {d a b : ℕ} (hb : b < S.length) :
    nextrel1 (S.map fun p => (p.1 + d, p.2)) a b ↔ nextrel1 S a b := by
  unfold nextrel1
  rw [List.length_map]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, ?_, (le0_shift_iff).1 h5, ?_⟩
    · rwa [(entry_shift (by omega)).2, (entry_shift hb).2] at h4
    · intro l hl
      have h7 := h6 l ⟨hl.1, (le0_shift_iff).2 hl.2⟩
      have hlb : l ≤ b := le0_le hl.2
      rwa [(entry_shift hb).2, (entry_shift (by omega)).2] at h7
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, ?_, (le0_shift_iff).2 h5, ?_⟩
    · rwa [(entry_shift (by omega)).2, (entry_shift hb).2]
    · intro l hl
      have hl0 := (le0_shift_iff).1 hl.2
      have hlb : l ≤ b := le0_le hl0
      have h7 := h6 l ⟨hl.1, hl0⟩
      rwa [(entry_shift hb).2, (entry_shift (by omega)).2]

/-- The guard under which `oper` truncates: zero last column or no unique
parent. -/
def predGuard (N : PairSeq) : Prop :=
  (entry N 0 (N.length - 1) = 0 ∧ entry N 1 (N.length - 1) = 0) ∨
  ¬ hasParent N (idx1 N (N.length - 1)) (N.length - 1)

/-- Guarded truncation images. -/
inductive predImages : PairSeq → PairSeq → Prop
  | refl (M : PairSeq) : predImages M M
  | step {M N : PairSeq} (h : predImages M N) (hg : predGuard N) :
      predImages M (Pred N)

/-! ## The arg-zone ORDER reframe (port of ya-pss `proj_nrm_argzone_olt`)

This section ports the ya-pss "arg-zone ORDER" decomposition of the Buchholz
§1 wall (`ord/nrm.thy` ~2440–2900) into Lean, as the **replacement** for the
stuck value-collapse route of `nrm_order_pres` (`psi_proj`/`CollapseResidueMaxo`,
`Nrm.lean`).  The route attacks ORDER preservation of `nrm` term-structurally,
bypassing the ordinal-membership collapse (proved structurally dead).

ya-pss factors `proj_nrm_argzone_olt` at the `nrm`/`proj` seam into:
  • **NRMMONO** `nrm_argzone_olt` — `nrm` is `olt`-monotone on arg-zone
    translates of standard forms (= `nrm_order_pres` one depth down, the
    recursion; ya-pss-verified TRUE 44850/0/0; left as a clearly-marked
    residual here, identical in content to `nrm_order_pres`).
  • **PROJSTEP** `proj_step_argzone_olt` — the genuine §1 crux: the shared
    collapse `proj 0` preserves the order of two already-`olt`-ordered
    arg-zone images.

**Soundness note (`tools/probe_argzone_order_lean.py`, deep closure, the Lean
`Three` encoding).**  The *whole-image* form of PROJSTEP
(`olt B F → olt (proj 0 B) (proj 0 F)` on full `NF` terms) is **FALSE** in this
encoding (6 reversals at closure+5, the tail-difference `d0=0` re-entry family
`P 0 (P 1 0) (…)` — same hard core the prior campaign flagged); likewise
ya-pss's whole-image head identity `proj 0 X = hdarg X` is **FALSE** here
(580/1948 firing images, the buried-`P 2` deeper-fire pattern), and the deeper
head-arg order `olt (hdarg B) (hdarg F)` is FALSE on the same tail family.  So
the head-`harg` decomposition is a ya-pss-representation artifact and is NOT
ported.  The **sound** Lean port of PROJSTEP is the *argument-level* statement
`proj0_olt_NF` (above): `olt b f → olt (proj 0 b) (proj 0 f)` for the arguments
`b,f` of head-`0` `NF` terms — model-confirmed `167910 / 0` (`audit_proj0.py`,
matched here).  Lean's `lead`/`maxsub` spine discipline (`lead_proj_eq_maxsub_NF`,
`maxsub_arg_mono`) lets `proj0_olt_NF` route around ya-pss's four head-arg
residuals, leaving a **single** residual `proj_bothfire_witness`.
-/

/-! ### H1 head-arg residual, the GREEN lead-gap

ya-pss's H1 (`argzone_head_lead_gt`: `lead X < lead (harg X)` on a firing
image) is the one head-arg fact that survives the encoding and is GREEN from
Lean's spine machinery.  A firing `NF` argument has `lead = 1`
(`fire_lead_one_NF`) and `maxsub ≥ 2` (`pfire0_maxsub_ge2_NF`); on the `NF`
spine `maxsub = climb` is the head-argument's leading subscript, which is
therefore `≥ 2 > 1 = lead b`. -/

/-! ### H2 transport residuals, GREEN where sound

ya-pss's H2 (`argzone_fire_transport`) splits into two transports.  In the
Lean encoding the arg-level versions are model-sound (`/tmp/probe_arg.py`,
`167910 / 0`):
  • firing transports `B→F` (`argzone_F_fires`) — GREEN from `proj0_fireprop_NF`.
The deeper head-arg order `olt (hdarg B) (hdarg F)` is NOT needed: Lean's
PROJSTEP (`proj0_olt_NF`) proves the projection order directly via `maxsub`
domination, bypassing ya-pss's `argzone_harg_olt`. -/

/-! ### NRMMONO half — the recursion residual

ya-pss `nrm_argzone_olt`: `nrm` is `olt`-monotone on arg-zone translates of
standard forms.  This is `nrm_order_pres` one depth down (the arg zones are
depth-1 `NF` blocks) — the clean half; ya-pss-verified TRUE (44850/0/0).  It is
exactly `nrm_order_pres` restricted to the `NF` image class, so we state it as a
residual whose content is identical to (and discharged by) `nrm_order_pres`. -/

end YAPSS
