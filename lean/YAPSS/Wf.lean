/-
Towards `diagacc` (well-foundedness of `<o` on `NF`).  Lean port of `wf.thy`.

This file develops the *syntactic* core of the subscript-monotonicity of
descent: along the leftmost argument spine of a term, the subscript-first
order `<o` refines the lexicographic order on the spine; together with the
normal-form invariants of `NF` (the spine begins `0,1,…,maxsub`; every
subscript is ≤ the spine maximum) this yields `w <o x → maxsub w ≤ maxsub x`.

Port conventions: Isabelle's partial `s ! i` is rendered `s.getD i 0` (each
use is guarded by `i < length s`).
-/
import YAPSS.Proofs
import Mathlib.Order.WellFounded
import Mathlib.Data.Prod.Lex

namespace YAPSS

open Three

/-! ## The spine as the strictly-increasing-row-0 prefix

The leftmost argument spine of `translate M` reads off the row-1 values of
the maximal prefix of `M` along which row 0 (`.1`) strictly increases. -/

/-- A `getD`/`getElem` bridge used throughout this file. -/
theorem getD_eq_getElem' {α : Type*} (l : List α) (d : α) {i : ℕ}
    (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-! ## The bad-case expansion as `dropLast M` followed by ascending copies

In the bad case the `k = 0` copy reproduces the dropped suffix, so the
expansion is `dropLast M` followed by the (`k ≥ 1`) ascending copies; the
copies only repeat row-1 values already present in `dropLast M`.  (Isabelle's
`take_split_map_nth` bookkeeping is subsumed here by reusing
`oper_bad_blocks`.) -/

/-- Unifying the three `oper` branches (for `1 < Lng M`): the expansion is
always `dropLast M` followed by a block whose row-1 values already occur in
`dropLast M`. -/
theorem oper_eq_dropLast_append {M : PairSeq} {n : ℕ} (L : 1 < M.length)
    (n1 : 1 ≤ n) :
    ∃ R, M⟦n⟧ = M.dropLast ++ R ∧ sndSet R ⊆ sndSet M.dropLast := by
  have hPred : Pred M = M.dropLast := by
    unfold Pred
    rw [if_neg (by omega)]
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · refine ⟨[], ?_, by simp⟩
    rw [oper_eq_pred_of_zero n (by omega) hz, hPred, List.append_nil]
  · by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
    · -- bad case, via the block decomposition
      obtain ⟨G, v0, w0, R0, d0, lp, hM, hMn, -, -, -, -⟩ :=
        oper_bad_blocks L hz hp n1
      have hdrop : M.dropLast = G ++ (v0, w0) :: R0 := by
        rw [hM, List.dropLast_concat]
      have hrange : List.range n = 0 :: List.range' 1 (n - 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp [List.range_eq_range', List.range'_succ]
      have hk0 : ((v0, w0) :: R0).map (fun p => (p.1 + 0 * d0, p.2))
          = (v0, w0) :: R0 := by simp
      refine ⟨(List.range' 1 (n - 1)).flatMap
        (fun k => ((v0, w0) :: R0).map fun p => (p.1 + k * d0, p.2)), ?_, ?_⟩
      · rw [hMn, hrange, List.flatMap_cons, hk0, hdrop, List.append_assoc]
      · intro y hy
        obtain ⟨p, hp', rfl⟩ := mem_sndSet.1 hy
        obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hp'
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hk
        refine mem_sndSet.2 ⟨q, ?_, rfl⟩
        rw [hdrop]
        exact List.mem_append_right G hq
    · refine ⟨[], ?_, by simp⟩
      rw [oper_eq_pred_of_noParent n (by omega) hz hp, hPred, List.append_nil]

/-! ## The NF invariants for the diagonal towers (base case) -/

theorem diagSeq_cons {u v : ℕ} (h : u ≤ v) :
    diagSeq u v = (u, u) :: diagSeq (u + 1) v := by
  unfold diagSeq
  rw [show v + 1 - u = (v + 1 - (u + 1)) + 1 by omega, List.range'_succ, List.map_cons]

theorem fst_in_diagSeq {q : ℕ × ℕ} {a b : ℕ} (h : q ∈ diagSeq a b) : a ≤ q.1 := by
  unfold diagSeq at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  obtain ⟨i, _, rfl⟩ := List.mem_range'.1 hj
  simp

theorem translate_diagSeq {u v : ℕ} (h : u ≤ v) :
    translate (diagSeq u v) = P u (translate (diagSeq (u + 1) v)) Z := by
  rw [diagSeq_cons h]
  exact translate_single_tree fun q hq => by
    have := fst_in_diagSeq hq
    simp only []
    omega

/-! ## Cantor normal form: siblings are non-increasing

The within-level order is not well-founded on `nfinv` terms alone (e.g.
`p₀(0) + p₀(p₀(0))` has increasing siblings yet satisfies `nfinv`); the
genuine standard forms additionally have *non-increasing* sibling sums
(CNF). -/

def cnf : Three → Prop
  | Z => True
  | P _ b Z => cnf b
  | P a b (P e f g) => cnf b ∧ ¬ (P a b Z <o P e f Z) ∧ cnf (P e f g)

@[simp] theorem cnf_Z : cnf Z := trivial

@[simp] theorem cnf_P_Z {a : ℕ} {b : Three} : cnf (P a b Z) ↔ cnf b := Iff.rfl

@[simp] theorem cnf_P_P {a e : ℕ} {b f g : Three} :
    cnf (P a b (P e f g)) ↔
      cnf b ∧ ¬ (P a b Z <o P e f Z) ∧ cnf (P e f g) := Iff.rfl

theorem cnf_translate_diagSeq_aux (n u : ℕ) :
    cnf (translate (diagSeq u (u + n))) := by
  induction n generalizing u with
  | zero =>
    have e : diagSeq (u + 1) u = [] := by
      unfold diagSeq
      rw [show u + 1 - (u + 1) = 0 by omega]
      rfl
    rw [show u + 0 = u from rfl, translate_diagSeq le_rfl, e]
    simp [translate]
  | succ n ih =>
    rw [translate_diagSeq (by omega : u ≤ u + (n + 1))]
    rw [show diagSeq (u + 1) (u + (n + 1)) = diagSeq (u + 1) ((u + 1) + n) by
      congr 1; omega]
    exact (cnf_P_Z).2 (ih (u + 1))

theorem cnf_diag (v : ℕ) : cnf (translate (diagSeq 0 v)) := by
  have := cnf_translate_diagSeq_aux v 0
  rwa [Nat.zero_add] at this

/-- `cnf` is preserved by dropping the last pair: if `translate (D ++ [m])`
is in CNF then so is `translate D`.  The interesting case appends `m` deep
inside the last sibling block; the leading two-principal comparison is
preserved because the earlier sibling's argument only grows
(`translate_takeWhile_snoc_le`) and `olt_ole_trans`.  This discharges the
`Pred` case of `cnf` preservation under `oper`. -/
theorem cnf_snoc {D : PairSeq} {m : ℕ × ℕ}
    (h : cnf (translate (D ++ [m]))) : cnf (translate D) := by
  induction D using translate.induct with
  | case1 => simp [translate]
  | case2 p rest ih1 ih2 =>
    by_cases allp : ∀ x ∈ rest, p.1 < x.1
    · have allp' : ∀ x ∈ rest, (fun q : ℕ × ℕ => decide (p.1 < q.1)) x = true := by
        intro x hx; simpa using allp x hx
      have tw : rest.takeWhile (fun q => p.1 < q.1) = rest :=
        List.takeWhile_eq_self_iff.2 allp'
      have dw : rest.dropWhile (fun q => p.1 < q.1) = [] :=
        List.dropWhile_eq_nil_iff.2 allp'
      have eq0 : translate (p :: rest) = P p.2 (translate rest) Z := by
        rw [translate, tw, dw, translate]
      by_cases hm : p.1 < m.1
      · have all' : ∀ x ∈ rest ++ [m],
            (fun q : ℕ × ℕ => decide (p.1 < q.1)) x = true := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact allp' x hx
          · simp at hx
            simpa [hx] using hm
        have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1) = rest ++ [m] :=
          List.takeWhile_eq_self_iff.2 all'
        have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1) = [] :=
          List.dropWhile_eq_nil_iff.2 all'
        have hsnoc : cnf (translate (rest ++ [m])) := by
          have e : translate ((p :: rest) ++ [m])
              = P p.2 (translate (rest ++ [m])) Z := by
            rw [List.cons_append, translate, tw', dw', translate]
          rw [e] at h
          exact (cnf_P_Z).1 h
        have : cnf (translate rest) := by
          have := ih1 (by rw [tw]; exact hsnoc)
          rwa [tw] at this
        rw [eq0]
        exact (cnf_P_Z).2 this
      · have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1) = rest := by
          rw [takeWhile_append_all allp']
          simp [hm]
        have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1) = [m] := by
          rw [dropWhile_append_all allp']
          simp [hm]
        have e : translate ((p :: rest) ++ [m])
            = P p.2 (translate rest) (translate [m]) := by
          rw [List.cons_append, translate, tw', dw']
        have e2 : translate ([m] : PairSeq) = P m.2 Z Z := by
          rw [translate]
          simp [translate]
        rw [e, e2] at h
        rw [eq0]
        exact (cnf_P_Z).2 h.1
    · push Not at allp
      obtain ⟨x, hx, hnx⟩ := allp
      have hnx' : ¬ (fun q : ℕ × ℕ => decide (p.1 < q.1)) x = true := by simpa using hnx
      have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1)
          = rest.takeWhile (fun q => p.1 < q.1) := takeWhile_append_not hx hnx'
      have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1)
          = rest.dropWhile (fun q => p.1 < q.1) ++ [m] := dropWhile_append_not hx hnx'
      have dwne : rest.dropWhile (fun q => p.1 < q.1) ≠ [] := by
        intro he
        exact hnx' (List.dropWhile_eq_nil_iff.1 he x hx)
      obtain ⟨q, rest2, dwq⟩ : ∃ q rest2,
          rest.dropWhile (fun q => p.1 < q.1) = q :: rest2 := by
        rcases hdw : rest.dropWhile (fun q => p.1 < q.1) with - | ⟨q, rest2⟩
        · exact absurd hdw dwne
        · exact ⟨q, rest2, hdw⟩
      have td : translate (rest.dropWhile fun q => p.1 < q.1)
          = P q.2 (translate (rest2.takeWhile fun y => q.1 < y.1))
              (translate (rest2.dropWhile fun y => q.1 < y.1)) := by
        rw [dwq, translate]
      have td' : translate ((rest.dropWhile fun q => p.1 < q.1) ++ [m])
          = P q.2 (translate ((rest2 ++ [m]).takeWhile fun y => q.1 < y.1))
              (translate ((rest2 ++ [m]).dropWhile fun y => q.1 < y.1)) := by
        rw [dwq, List.cons_append, translate]
      have fle : translate (rest2.takeWhile fun y => q.1 < y.1)
          ≤o translate ((rest2 ++ [m]).takeWhile fun y => q.1 < y.1) :=
        translate_takeWhile_snoc_le q.1 rest2 m
      -- unfold the CNF of the snoc'd term
      have e : translate ((p :: rest) ++ [m])
          = P p.2 (translate (rest.takeWhile fun q => p.1 < q.1))
              (translate ((rest.dropWhile fun q => p.1 < q.1) ++ [m])) := by
        rw [List.cons_append, translate, tw', dw']
      rw [e, td'] at h
      obtain ⟨cb, sib', cnf'⟩ := cnf_P_P.1 h
      have cdw : cnf (translate (rest.dropWhile fun q => p.1 < q.1)) := by
        apply ih2
        rw [td']
        exact cnf'
      -- transfer the sibling non-increase from `f'` back to `f`
      have leP : P q.2 (translate (rest2.takeWhile fun y => q.1 < y.1)) Z
          ≤o P q.2 (translate ((rest2 ++ [m]).takeWhile fun y => q.1 < y.1)) Z := by
        rcases fle with hlt | heq
        · exact Or.inl (olt_P_b _ _ _ hlt)
        · rw [heq]
          exact Or.inr rfl
      have sib : ¬ (P p.2 (translate (rest.takeWhile fun q => p.1 < q.1)) Z
          <o P q.2 (translate (rest2.takeWhile fun y => q.1 < y.1)) Z) := by
        intro hlt
        exact sib' (olt_ole_trans hlt leP)
      rw [translate, td]
      exact cnf_P_P.2 ⟨cb, sib, td ▸ cdw⟩

theorem cnf_dropLast {C : PairSeq} (ne : C ≠ []) (h : cnf (translate C)) :
    cnf (translate C.dropLast) := by
  apply cnf_snoc (m := C.getLast ne)
  rwa [List.dropLast_append_getLast ne]

/-- `cnf` is preserved by any prefix `take k` (iterated `cnf_dropLast`). -/
theorem cnf_take {M : PairSeq} (h : cnf (translate M)) (k : ℕ) :
    cnf (translate (M.take k)) := by
  suffices H : ∀ d k, M.length - k = d → cnf (translate (M.take k)) from H _ k rfl
  intro d
  induction d with
  | zero =>
    intro k hk
    rw [List.take_of_length_le (by omega)]
    exact h
  | succ d ih =>
    intro k hk
    have klt : k < M.length := by omega
    have ihk : cnf (translate (M.take (k + 1))) := ih (k + 1) (by omega)
    have ne : M.take (k + 1) ≠ [] := by
      have hlen : (M.take (k + 1)).length = k + 1 := by
        rw [List.length_take]
        omega
      intro he
      rw [he] at hlen
      simp at hlen
    have e : (M.take (k + 1)).dropLast = M.take k := by
      rw [List.dropLast_eq_take, List.take_take]
      congr 1
      simp
      omega
    rw [← e]
    exact cnf_dropLast ne ihk

/-- CNF core, the exact-copy (`i1 = 0`) case: `n` identical copies of a block
`(v0,w0) :: R` translate to a CNF term — the equal sibling blocks are
non-increasing by irreflexivity of `<o`. -/
theorem cnf_replicate_block {v0 w0 : ℕ} {R : PairSeq}
    (hR : ∀ x ∈ R, v0 < x.1) (cR : cnf (translate R)) (n : ℕ) :
    cnf (translate (List.replicate n ((v0, w0) :: R)).flatten) := by
  induction n with
  | zero => simp [translate]
  | succ m ih =>
    have hd : (List.replicate (m + 1) ((v0, w0) :: R)).flatten
        = ((v0, w0) :: R) ++ (List.replicate m ((v0, w0) :: R)).flatten := by
      rw [List.replicate_succ, List.flatten_cons]
    have Tcond : (List.replicate m ((v0, w0) :: R)).flatten = []
        ∨ ¬ v0 < (((List.replicate m ((v0, w0) :: R)).flatten).headI).1 := by
      cases m with
      | zero => left; rfl
      | succ m' =>
        right
        rw [List.replicate_succ, List.flatten_cons]
        simp
    have tb : translate (((v0, w0) :: R) ++ (List.replicate m ((v0, w0) :: R)).flatten)
        = P w0 (translate R)
            (translate (List.replicate m ((v0, w0) :: R)).flatten) :=
      translate_block_append hR Tcond
    cases m with
    | zero =>
      rw [hd, tb,
        show translate (List.replicate 0 ((v0, w0) :: R)).flatten = Z from by
          simp [translate]]
      exact cnf_P_Z.2 cR
    | succ m' =>
      have e : (List.replicate (m' + 1) ((v0, w0) :: R)).flatten
          = ((v0, w0) :: R) ++ (List.replicate m' ((v0, w0) :: R)).flatten := by
        rw [List.replicate_succ, List.flatten_cons]
      have c : (List.replicate m' ((v0, w0) :: R)).flatten = []
          ∨ ¬ v0 < (((List.replicate m' ((v0, w0) :: R)).flatten).headI).1 := by
        cases m' with
        | zero => left; rfl
        | succ m'' =>
          right
          rw [List.replicate_succ, List.flatten_cons]
          simp
      have tT : translate (List.replicate (m' + 1) ((v0, w0) :: R)).flatten
          = P w0 (translate R)
              (translate (List.replicate m' ((v0, w0) :: R)).flatten) := by
        rw [e]
        exact translate_block_append hR c
      rw [hd, tb, tT]
      refine cnf_P_P.2 ⟨cR, fun hlt => olt_irrefl _ hlt, ?_⟩
      rw [← tT]
      exact ih

/-- **CNF context congruence.**  If `Z1 = z1 :: T1`, `Z2 = z2 :: T2` share
their leading row-0 (`z1.1 = z2.1`), `translate Z1 <o translate Z2`, and
`translate Z1` is CNF, then a common good part `G` preserves CNF:
`cnf (translate (G ++ Z2))` implies `cnf (translate (G ++ Z1))`.  The
sibling-boundary that `G` creates is preserved because the leading argument
only shrinks (`P a1 b1 Z ≤o P a2 b2 Z`) and `<o` is transitive. -/
theorem cnf_ctx_cong {z1 z2 : ℕ × ℕ} {T1 T2 : PairSeq}
    (cZ1 : cnf (translate (z1 :: T1)))
    (decr : translate (z1 :: T1) <o translate (z2 :: T2))
    (root : z1.1 = z2.1)
    (leadle : ∃ a1 b1 c1 a2 b2 c2, translate (z1 :: T1) = P a1 b1 c1
        ∧ translate (z2 :: T2) = P a2 b2 c2 ∧ P a1 b1 Z ≤o P a2 b2 Z)
    (r1 : ∀ x ∈ T1, z1.1 ≤ x.1) (r2 : ∀ x ∈ T2, z2.1 ≤ x.1)
    (G : PairSeq) (hG2 : cnf (translate (G ++ z2 :: T2))) :
    cnf (translate (G ++ z1 :: T1)) := by
  obtain ⟨a1, b1, c1, a2, b2, c2, lZ1, lZ2, lle⟩ := leadle
  match G with
  | [] => simpa using cZ1
  | g :: G' =>
    by_cases allG : ∀ x ∈ G', g.1 < x.1
    · have allG' : ∀ x ∈ G', (fun q : ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        intro x hx; simpa using allG x hx
      by_cases hPg : g.1 < z1.1
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
        rw [List.cons_append] at hG2 ⊢
        rw [e2] at hG2
        rw [e1]
        exact cnf_P_Z.2 (cnf_ctx_cong cZ1 decr root
          ⟨a1, b1, c1, a2, b2, c2, lZ1, lZ2, lle⟩ r1 r2 G' (cnf_P_Z.1 hG2))
      · -- case (c): the tail is a sibling after `g`'s subtree
        have hPg2 : ¬ g.1 < z2.1 := root ▸ hPg
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
            = P g.2 (translate G') (P a1 b1 c1) := by
          rw [translate, tw1, dw1, lZ1]
        have e2 : translate (g :: (G' ++ z2 :: T2))
            = P g.2 (translate G') (P a2 b2 c2) := by
          rw [translate, tw2, dw2, lZ2]
        rw [List.cons_append] at hG2 ⊢
        rw [e2] at hG2
        obtain ⟨ctg, bnd2, -⟩ := cnf_P_P.1 hG2
        have bnd1 : ¬ (P g.2 (translate G') Z <o P a1 b1 Z) := by
          intro hlt
          exact bnd2 (olt_ole_trans hlt lle)
        rw [e1]
        exact cnf_P_P.2 ⟨ctg, bnd1, lZ1 ▸ cZ1⟩
    · -- case (a): `G'` already drops to/below `g`; recurse on the shorter tail
      push Not at allG
      obtain ⟨x, hx, hnx⟩ := allG
      have hnx' : ¬ (fun q : ℕ × ℕ => decide (g.1 < q.1)) x = true := by simpa using hnx
      have tw1 : (G' ++ z1 :: T1).takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw1 : (G' ++ z1 :: T1).dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ z1 :: T1 := dropWhile_append_not hx hnx'
      have tw2 : (G' ++ z2 :: T2).takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw2 : (G' ++ z2 :: T2).dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ z2 :: T2 := dropWhile_append_not hx hnx'
      have Dne : G'.dropWhile (fun q => g.1 < q.1) ≠ [] := by
        intro he
        exact hnx' (List.dropWhile_eq_nil_iff.1 he x hx)
      obtain ⟨d, D', hD⟩ : ∃ d D', G'.dropWhile (fun q => g.1 < q.1) = d :: D' := by
        rcases hD : G'.dropWhile (fun q => g.1 < q.1) with - | ⟨d, D'⟩
        · exact absurd hD Dne
        · exact ⟨d, D', hD⟩
      have e1 : translate (g :: (G' ++ z1 :: T1))
          = P g.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((d :: D') ++ z1 :: T1)) := by
        rw [translate, tw1, dw1, hD]
      have e2 : translate (g :: (G' ++ z2 :: T2))
          = P g.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((d :: D') ++ z2 :: T2)) := by
        rw [translate, tw2, dw2, hD]
      have p1 : translate ((d :: D') ++ z1 :: T1)
          = P d.2 (translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1))
              (translate ((D' ++ z1 :: T1).dropWhile fun y => d.1 < y.1)) := by
        rw [List.cons_append, translate]
      have p2 : translate ((d :: D') ++ z2 :: T2)
          = P d.2 (translate ((D' ++ z2 :: T2).takeWhile fun y => d.1 < y.1))
              (translate ((D' ++ z2 :: T2).dropWhile fun y => d.1 < y.1)) := by
        rw [List.cons_append, translate]
      have decrD : translate ((d :: D') ++ z1 :: T1)
          <o translate ((d :: D') ++ z2 :: T2) :=
        translate_ctx_cong decr root r1 r2 (d :: D')
      have argle : translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1)
            <o translate ((D' ++ z2 :: T2).takeWhile fun y => d.1 < y.1)
          ∨ translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1)
            = translate ((D' ++ z2 :: T2).takeWhile fun y => d.1 < y.1) := by
        rw [p1, p2, olt_P_P] at decrD
        rcases decrD with h | ⟨-, h⟩ | ⟨-, h, -⟩
        · omega
        · exact Or.inl h
        · exact Or.inr h
      rw [List.cons_append] at hG2 ⊢
      rw [e2, p2] at hG2
      obtain ⟨ctw, bnd2, cD2⟩ := cnf_P_P.1 hG2
      have cD2' : cnf (translate ((d :: D') ++ z2 :: T2)) := by
        rw [p2]
        exact cD2
      have cD1 : cnf (translate ((d :: D') ++ z1 :: T1)) :=
        cnf_ctx_cong cZ1 decr root
          ⟨a1, b1, c1, a2, b2, c2, lZ1, lZ2, lle⟩ r1 r2 (d :: D') cD2'
      -- the boundary `¬ (... <o P e arg1 Z)` transfers from `arg2`
      have bnd1 : ¬ (P g.2 (translate (G'.takeWhile fun q => g.1 < q.1)) Z
          <o P d.2 (translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1)) Z) := by
        intro hlt
        rw [olt_P_P] at hlt
        rcases hlt with h | ⟨heq, h⟩ | ⟨-, -, h⟩
        · exact bnd2 (olt_P_P.2 (Or.inl h))
        · rcases argle with ha | ha
          · exact bnd2 (olt_P_P.2 (Or.inr (Or.inl ⟨heq, olt_trans h ha⟩)))
          · exact bnd2 (olt_P_P.2 (Or.inr (Or.inl ⟨heq, ha ▸ h⟩)))
        · exact not_olt_Z Z h
      rw [e1, p1]
      refine cnf_P_P.2 ⟨ctw, bnd1, ?_⟩
      rw [← p1]
      exact cD1
  termination_by G.length
  decreasing_by
  · simp only [List.length_cons]
    omega
  · -- |d :: D'| = |dropWhile … G'| ≤ |G'| < |g :: G'|
    have hle : (d :: D').length ≤ G'.length := by
      rw [← hD]
      exact List.length_dropWhile_le _ G'
    simp only [List.length_cons] at hle ⊢
    omega

/-- CNF is inherited by a re-opening tail: if `translate (G ++ T)` is CNF and
`T = t :: T'` is a single well-formed block (its non-leading pairs all lie at
or above its root), then `translate T` is CNF. -/
theorem cnf_tail {t : ℕ × ℕ} {T' : PairSeq}
    (rT : ∀ x ∈ T', t.1 ≤ x.1)
    (G : PairSeq) (hGT : cnf (translate (G ++ t :: T'))) :
    cnf (translate (t :: T')) := by
  match G with
  | [] => simpa using hGT
  | g :: G' =>
    by_cases allG : ∀ x ∈ G', g.1 < x.1
    · have allG' : ∀ x ∈ G', (fun q : ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        intro x hx; simpa using allG x hx
      by_cases hPg : g.1 < t.1
      · have aT : ∀ x ∈ t :: T', g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hPg
          · exact lt_of_lt_of_le hPg (rT _ hx)
        have all : ∀ x ∈ G' ++ t :: T', g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aT x h]
        have e : translate (g :: (G' ++ t :: T'))
            = P g.2 (translate (G' ++ t :: T')) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all),
            List.dropWhile_eq_nil_iff.2 (by simpa using all), translate]
        rw [List.cons_append] at hGT
        rw [e] at hGT
        exact cnf_tail rT G' (cnf_P_Z.1 hGT)
      · have tw : (G' ++ t :: T').takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg]
        have dw : (G' ++ t :: T').dropWhile (fun q => g.1 < q.1) = t :: T' := by
          rw [dropWhile_append_all allG']
          simp [hPg]
        have e : translate (g :: (G' ++ t :: T'))
            = P g.2 (translate G') (translate (t :: T')) := by
          rw [translate, tw, dw]
        rw [List.cons_append] at hGT
        rw [e, translate] at hGT
        rw [translate]
        exact (cnf_P_P.1 hGT).2.2
    · push Not at allG
      obtain ⟨x, hx, hnx⟩ := allG
      have hnx' : ¬ (fun q : ℕ × ℕ => decide (g.1 < q.1)) x = true := by simpa using hnx
      have tw : (G' ++ t :: T').takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw : (G' ++ t :: T').dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ t :: T' := dropWhile_append_not hx hnx'
      have Dne : G'.dropWhile (fun q => g.1 < q.1) ≠ [] := by
        intro he
        exact hnx' (List.dropWhile_eq_nil_iff.1 he x hx)
      obtain ⟨d, D', hD⟩ : ∃ d D', G'.dropWhile (fun q => g.1 < q.1) = d :: D' := by
        rcases hD : G'.dropWhile (fun q => g.1 < q.1) with - | ⟨d, D'⟩
        · exact absurd hD Dne
        · exact ⟨d, D', hD⟩
      have e : translate (g :: (G' ++ t :: T'))
          = P g.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((d :: D') ++ t :: T')) := by
        rw [translate, tw, dw, hD]
      have p : translate ((d :: D') ++ t :: T')
          = P d.2 (translate ((D' ++ t :: T').takeWhile fun y => d.1 < y.1))
              (translate ((D' ++ t :: T').dropWhile fun y => d.1 < y.1)) := by
        rw [List.cons_append, translate]
      rw [List.cons_append] at hGT
      rw [e, p] at hGT
      have hD1 : cnf (translate ((d :: D') ++ t :: T')) := by
        rw [p]
        exact (cnf_P_P.1 hGT).2.2
      exact cnf_tail rT (d :: D') hD1
  termination_by G.length
  decreasing_by
  · simp only [List.length_cons]
    omega
  · have hle : (d :: D').length ≤ G'.length := by
      rw [← hD]
      exact List.length_dropWhile_le _ G'
    simp only [List.length_cons] at hle ⊢
    omega

/-- **CNF preservation, the exact-copy (`i1 = 0`) oper case (abstract).**
Replacing a block `(v0,w0) :: R` followed by the dropped descendant `lp`
(which nests, `v0 < lp.1`) by `n` exact copies of the block preserves CNF. -/
theorem cnf_oper_i1eq0 {v0 w0 : ℕ} {R : PairSeq} {lp : ℕ × ℕ} {G : PairSeq} {n : ℕ}
    (hR : ∀ x ∈ R, v0 < x.1) (lpv : v0 < lp.1) (n1 : 1 ≤ n)
    (cM : cnf (translate (G ++ ((v0, w0) :: R) ++ [lp]))) :
    cnf (translate (G ++ (List.replicate n ((v0, w0) :: R)).flatten)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- structures of the two tails
  have RlpV : ∀ x ∈ R ++ [lp], v0 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hR x hx
    · simp at hx
      simpa [hx] using lpv
  have tZ2 : translate ((v0, w0) :: (R ++ [lp]))
      = P w0 (translate (R ++ [lp])) Z := translate_single_tree RlpV
  have Tcond : (List.replicate m ((v0, w0) :: R)).flatten = []
      ∨ ¬ v0 < (((List.replicate m ((v0, w0) :: R)).flatten).headI).1 := by
    cases m with
    | zero => left; rfl
    | succ m' =>
      right
      rw [List.replicate_succ, List.flatten_cons]
      simp
  have e1n : (List.replicate (m + 1) ((v0, w0) :: R)).flatten
      = (v0, w0) :: (R ++ (List.replicate m ((v0, w0) :: R)).flatten) := by
    rw [List.replicate_succ, List.flatten_cons, List.cons_append]
  have tZ1 : translate ((v0, w0) :: (R ++ (List.replicate m ((v0, w0) :: R)).flatten))
      = P w0 (translate R)
          (translate (List.replicate m ((v0, w0) :: R)).flatten) := by
    rw [← List.cons_append]
    exact translate_block_append hR Tcond
  -- extract CNF of the block body from CNF of `M`
  have rT : ∀ x ∈ R ++ [lp], ((v0, w0) : ℕ × ℕ).1 ≤ x.1 :=
    fun x hx => (RlpV x hx).le
  have cM' : cnf (translate (G ++ (v0, w0) :: (R ++ [lp]))) := by
    have h : G ++ ((v0, w0) :: R) ++ [lp] = G ++ (v0, w0) :: (R ++ [lp]) := by
      simp
    rwa [h] at cM
  have cblk : cnf (translate ((v0, w0) :: (R ++ [lp]))) := cnf_tail rT G cM'
  have cRlp : cnf (translate (R ++ [lp])) := by
    rw [tZ2] at cblk
    exact cnf_P_Z.1 cblk
  have cR : cnf (translate R) := cnf_snoc cRlp
  have cZ1 : cnf (translate (List.replicate (m + 1) ((v0, w0) :: R)).flatten) :=
    cnf_replicate_block hR cR (m + 1)
  -- lead (`b1 ≤o b2`) and the strict decrease
  have RltRlp : translate R <o translate (R ++ [lp]) := translate_snoc_increase R lp
  have decr : translate ((v0, w0) :: (R ++ (List.replicate m ((v0, w0) :: R)).flatten))
      <o translate ((v0, w0) :: (R ++ [lp])) := by
    rw [tZ1, tZ2]
    exact olt_P_b _ _ _ RltRlp
  -- side conditions for the context congruence
  have sub : ∀ x ∈ (List.replicate m ((v0, w0) :: R)).flatten, x ∈ (v0, w0) :: R := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    rwa [List.eq_of_mem_replicate hl] at hxl
  have r1 : ∀ x ∈ R ++ (List.replicate m ((v0, w0) :: R)).flatten,
      ((v0, w0) : ℕ × ℕ).1 ≤ x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact (hR x hx).le
    · rcases List.mem_cons.1 (sub x hx) with rfl | hx'
      · exact le_rfl
      · exact (hR x hx').le
  have key : cnf (translate (G ++ (v0, w0)
      :: (R ++ (List.replicate m ((v0, w0) :: R)).flatten))) := by
    refine cnf_ctx_cong ?_ decr rfl ?_ r1 rT G cM'
    · rw [← e1n]
      exact cZ1
    · exact ⟨w0, translate R,
        translate (List.replicate m ((v0, w0) :: R)).flatten,
        w0, translate (R ++ [lp]), Z, tZ1, tZ2,
        Or.inl (olt_P_b _ _ _ RltRlp)⟩
  rw [e1n]
  exact key

/-! ## CNF preservation, the ascending-copies (`i1 = 1`) oper case

The `i1 = 1` bad step replaces the block `blk = (v0,w0) :: R` followed by the
dropped descendant `lp` by `n` *ascending* copies of `blk`: the `k`-th copy is
`blk` with every row-0 entry shifted up by `k * d0` (`d0 > 0`).  We package
the copy list as `copies d0 blk n`. -/

def shiftr0 (d : ℕ) : PairSeq → PairSeq := List.map fun p => (p.1 + d, p.2)

def copies (d : ℕ) (blk : PairSeq) (n : ℕ) : PairSeq :=
  (List.range n).flatMap fun k => shiftr0 (k * d) blk

@[simp] theorem shiftr0_zero (M : PairSeq) : shiftr0 0 M = M := by
  unfold shiftr0
  simp

@[simp] theorem shiftr0_nil (d : ℕ) : shiftr0 d [] = [] := rfl

@[simp] theorem shiftr0_eq_nil {d : ℕ} {M : PairSeq} : shiftr0 d M = [] ↔ M = [] := by
  unfold shiftr0
  simp

@[simp] theorem translate_shiftr0 (d : ℕ) (M : PairSeq) :
    translate (shiftr0 d M) = translate M :=
  translate_shift d M

theorem shiftr0_cons (d : ℕ) (p : ℕ × ℕ) (M : PairSeq) :
    shiftr0 d (p :: M) = (p.1 + d, p.2) :: shiftr0 d M := rfl

theorem mem_shiftr0 {d : ℕ} {M : PairSeq} {x : ℕ × ℕ} :
    x ∈ shiftr0 d M ↔ ∃ p ∈ M, (p.1 + d, p.2) = x := by
  unfold shiftr0
  simp

@[simp] theorem copies_zero (d : ℕ) (blk : PairSeq) : copies d blk 0 = [] := rfl

theorem copies_succ_front (d : ℕ) (blk : PairSeq) (n : ℕ) :
    copies d blk (n + 1) = blk ++ shiftr0 d (copies d blk n) := by
  unfold copies
  rw [List.range_succ_eq_map, List.flatMap_cons, Nat.zero_mul, shiftr0_zero]
  congr 1
  rw [List.flatMap_map]
  unfold shiftr0
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_map]
  congr 1
  funext p
  simp only [Function.comp_apply, Nat.succ_mul, Prod.mk.injEq, and_true]
  omega

@[simp] theorem copies_one (d : ℕ) (blk : PairSeq) : copies d blk 1 = blk := by
  rw [copies_succ_front]
  simp

/-- `copies` of a cons block, exposed in cons form. -/
theorem copies_succ_cons (d v0 w0 : ℕ) (R : PairSeq) (n : ℕ) :
    copies d ((v0, w0) :: R) (n + 1)
      = (v0, w0) :: (R ++ shiftr0 d (copies d ((v0, w0) :: R) n)) := by
  rw [copies_succ_front, List.cons_append]

theorem copies_v0_le {v0 w0 : ℕ} {R : PairSeq}
    (Rle : ∀ x ∈ R, v0 ≤ x.1) (d n : ℕ) :
    ∀ x ∈ copies d ((v0, w0) :: R) n, v0 ≤ x.1 := by
  intro x hx
  unfold copies at hx
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hx
  obtain ⟨p, hp, rfl⟩ := mem_shiftr0.1 hk
  have hvp : v0 ≤ p.1 := by
    rcases List.mem_cons.1 hp with rfl | hp'
    · simp
    · exact Rle p hp'
  simp only []
  omega

theorem copies_tl_gt {v0 w0 : ℕ} {R : PairSeq}
    (hR : ∀ x ∈ R, v0 < x.1) {d : ℕ} (dpos : 0 < d) {n : ℕ} (_n1 : 1 ≤ n) :
    ∀ x ∈ R ++ shiftr0 d (copies d ((v0, w0) :: R) (n - 1)), v0 < x.1 := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hR x hx
  · obtain ⟨p, hp, rfl⟩ := mem_shiftr0.1 hx
    have hvp : v0 ≤ p.1 :=
      copies_v0_le (fun x hx => (hR x hx).le) d (n - 1) p hp
    simp only []
    omega

/-- The core induction: `n` ascending copies of a CNF block translate to a
CNF term.  Each new copy is grafted by `cnf_ctx_cong` against the dropped
tail `[lp]`; its leading subscript `w0` is strictly below `lp.2` (the row-1
increase of the `i1 = 1` parent), so the leading principal does not increase
and the boundary is preserved. -/
theorem cnf_copies {v0 w0 d0 : ℕ} {R : PairSeq} {lp : ℕ × ℕ}
    (hR : ∀ x ∈ R, v0 < x.1)
    (d0pos : 0 < d0)
    (w0lt : w0 < lp.2)
    (lphd : lp.1 = v0 + d0)
    (cBlp : cnf (translate (((v0, w0) :: R) ++ [lp])))
    (n : ℕ) :
    cnf (translate (copies d0 ((v0, w0) :: R) n)) := by
  induction n with
  | zero => simp [translate]
  | succ n ih =>
    cases n with
    | zero =>
      rw [copies_one]
      have h0 : translate ((v0, w0) :: R)
          = translate ((((v0, w0) :: R) ++ [lp]).dropLast) := by
        rw [List.dropLast_concat]
      rw [h0]
      exact cnf_dropLast (by simp) cBlp
    | succ m =>
      have n1 : 1 ≤ m + 1 := by omega
      -- cons form of `copies (m+1)`
      have cpcons := copies_succ_cons d0 v0 w0 R m
      -- `Z1 = shiftr0 d0 (copies d0 blk (m+1))`, in cons form
      have z1cons : shiftr0 d0 (copies d0 ((v0, w0) :: R) (m + 1))
          = (v0 + d0, w0)
            :: shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)) := by
        rw [copies_succ_cons, shiftr0_cons]
      -- tail bound for the shifted copies
      have tlgt : ∀ x ∈ R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m), v0 < x.1 := by
        have h := copies_tl_gt (w0 := w0) hR d0pos (n := m + 1) (by omega)
        simpa using h
      -- single-tree shape of `copies (m+1)`
      have st1 : translate (copies d0 ((v0, w0) :: R) (m + 1))
          = P w0 (translate (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m))) Z := by
        rw [cpcons]
        exact translate_single_tree tlgt
      have tZ1 : translate ((v0 + d0, w0)
            :: shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)))
          = P w0 (translate (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m))) Z := by
        rw [← z1cons, translate_shiftr0, st1]
      have tlp : translate ([lp] : PairSeq) = P lp.2 Z Z := by
        rw [translate]
        simp [translate]
      -- the decrease and the lead
      have decr : translate ((v0 + d0, w0)
            :: shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)))
          <o translate ([lp] : PairSeq) := by
        rw [tZ1, tlp, olt_P_P]
        exact Or.inl w0lt
      -- cnf of Z1
      have cZ1 : cnf (translate ((v0 + d0, w0)
          :: shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)))) := by
        rw [← z1cons, translate_shiftr0]
        exact ih
      -- r1: tail of Z1 lies above its head
      have r1 : ∀ x ∈ shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)),
          ((v0 + d0, w0) : ℕ × ℕ).1 ≤ x.1 := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := mem_shiftr0.1 hx
        have : v0 ≤ p.1 := (tlgt p hp).le
        simp only []
        omega
      have root : ((v0 + d0, w0) : ℕ × ℕ).1 = lp.1 := lphd.symm
      have leadle : ∃ a1 b1 c1 a2 b2 c2,
          translate ((v0 + d0, w0)
            :: shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)))
            = P a1 b1 c1
          ∧ translate ([lp] : PairSeq) = P a2 b2 c2 ∧ P a1 b1 Z ≤o P a2 b2 Z :=
        ⟨w0, translate (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)), Z,
          lp.2, Z, Z, tZ1, tlp, Or.inl (olt_P_P.2 (Or.inl w0lt))⟩
      have key := cnf_ctx_cong cZ1 decr root leadle r1 (by simp)
        ((v0, w0) :: R) (by simpa using cBlp)
      rw [copies_succ_front, z1cons]
      exact key

/-- **CNF preservation, the ascending-copies (`i1 = 1`) oper case.**  Like
`cnf_oper_i1eq0` but for the genuinely ascending copies; the strict decrease
`translate (copies d0 blk n) <o translate (blk ++ [lp])` (the bad-step core,
derived internally from `core_i1`) lifts the block's CNF through the good
part `G` via `cnf_ctx_cong`, while `cnf_copies` furnishes CNF of the copies
themselves. -/
theorem cnf_oper_i1eq1 {v0 w0 d0 : ℕ} {R : PairSeq} {lp : ℕ × ℕ} {G : PairSeq} {n : ℕ}
    (hR : ∀ x ∈ R, v0 < x.1)
    (d0pos : 0 < d0)
    (w0lt : w0 < lp.2)
    (lphd : lp.1 = v0 + d0)
    (n1 : 1 ≤ n)
    (cM : cnf (translate (G ++ ((v0, w0) :: R) ++ [lp]))) :
    cnf (translate (G ++ copies d0 ((v0, w0) :: R) n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have lpv : v0 < lp.1 := by omega
  have Rlp_gt : ∀ x ∈ R ++ [lp], v0 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hR x hx
    · simp at hx
      simp [hx]
      omega
  -- the bad-step core decrease
  have decr : translate (copies d0 ((v0, w0) :: R) (m + 1))
      <o translate (((v0, w0) :: R) ++ [lp]) := by
    cases m with
    | zero =>
      rw [copies_one]
      exact translate_snoc_increase _ _
    | succ m' =>
      have cpcons' := copies_succ_cons d0 v0 w0 R m'
      have z1cons : shiftr0 d0 (copies d0 ((v0, w0) :: R) (m' + 1))
          = (v0 + d0, w0)
            :: shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m')) := by
        rw [copies_succ_cons, shiftr0_cons]
      have tlgt' : ∀ x ∈ R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m'), v0 < x.1 := by
        have h := copies_tl_gt (w0 := w0) hR d0pos (n := m' + 1) (by omega)
        simpa using h
      have Cge : ∀ x ∈ shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m')),
          ((v0 + d0, w0) : ℕ × ℕ).1 ≤ x.1 := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := mem_shiftr0.1 hx
        have : v0 ≤ p.1 := (tlgt' p hp).le
        simp only []
        omega
      have Croot : ((v0 + d0, w0) : ℕ × ℕ).1 = lp.1 := lphd.symm
      have lead_lt : ((v0 + d0, w0) : ℕ × ℕ).2 < lp.2 := w0lt
      have core := core_i1 (w0 := w0) hR Cge Croot lpv lead_lt
      have e : copies d0 ((v0, w0) :: R) (m' + 1 + 1)
          = ((v0, w0) :: R) ++ ((v0 + d0, w0)
              :: shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m'))) := by
        rw [copies_succ_front, z1cons]
      rw [e]
      exact core
  -- cons form and single-tree shapes
  have cpcons := copies_succ_cons d0 v0 w0 R m
  have tlgt : ∀ x ∈ R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m), v0 < x.1 := by
    have h := copies_tl_gt (w0 := w0) hR d0pos (n := m + 1) (by omega)
    simpa using h
  have st1 : translate (copies d0 ((v0, w0) :: R) (m + 1))
      = P w0 (translate (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m))) Z := by
    rw [cpcons]
    exact translate_single_tree tlgt
  have st2 : translate (((v0, w0) :: R) ++ [lp])
      = P w0 (translate (R ++ [lp])) Z := by
    rw [List.cons_append]
    exact translate_single_tree Rlp_gt
  -- side conditions for the outer context congruence
  have rT : ∀ x ∈ R ++ [lp], ((v0, w0) : ℕ × ℕ).1 ≤ x.1 :=
    fun x hx => (Rlp_gt x hx).le
  have cM' : cnf (translate (G ++ (v0, w0) :: (R ++ [lp]))) := by
    have h : G ++ ((v0, w0) :: R) ++ [lp] = G ++ (v0, w0) :: (R ++ [lp]) := by
      simp
    rwa [h] at cM
  have cBlp : cnf (translate (((v0, w0) :: R) ++ [lp])) := by
    rw [List.cons_append]
    exact cnf_tail rT G cM'
  have cCopies : cnf (translate (copies d0 ((v0, w0) :: R) (m + 1))) :=
    cnf_copies hR d0pos w0lt lphd cBlp (m + 1)
  -- the lead
  have argA : translate (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m))
      <o translate (R ++ [lp]) := by
    have d := decr
    rw [st1, st2, olt_P_P] at d
    rcases d with h | ⟨-, h⟩ | ⟨-, -, h⟩
    · omega
    · exact h
    · exact absurd h (not_olt_Z Z)
  have leadle : ∃ a1 b1 c1 a2 b2 c2,
      translate ((v0, w0) :: (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)))
        = P a1 b1 c1
      ∧ translate ((v0, w0) :: (R ++ [lp])) = P a2 b2 c2
      ∧ P a1 b1 Z ≤o P a2 b2 Z := by
    refine ⟨w0, translate (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)), Z,
      w0, translate (R ++ [lp]), Z, ?_, ?_, Or.inl (olt_P_b _ _ _ argA)⟩
    · rw [← cpcons]
      exact st1
    · rw [← List.cons_append]
      exact st2
  have decr' : translate ((v0, w0) :: (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)))
      <o translate ((v0, w0) :: (R ++ [lp])) := by
    rw [← cpcons, ← List.cons_append]
    exact decr
  have cCopies' : cnf (translate ((v0, w0)
      :: (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)))) := by
    rw [← cpcons]
    exact cCopies
  have r1 : ∀ x ∈ R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m),
      ((v0, w0) : ℕ × ℕ).1 ≤ x.1 := fun x hx => (tlgt x hx).le
  have key := cnf_ctx_cong cCopies' decr' rfl leadle r1 rT G cM'
  rw [cpcons]
  exact key

theorem copies_replicate (blk : PairSeq) (n : ℕ) :
    copies 0 blk n = (List.replicate n blk).flatten := by
  unfold copies
  have h : (fun k : ℕ => shiftr0 (k * 0) blk) = fun _ : ℕ => blk := by
    funext k
    rw [Nat.mul_zero, shiftr0_zero]
  rw [h, List.flatMap_def, List.map_const', List.length_range]

/-- **CNF is preserved by one expansion step.**  The degenerate (`Pred`)
branches drop the last pair (`cnf_dropLast`) or leave `M` unchanged; the
genuine (bad) branch is discharged by `cnf_oper_i1eq0` (exact copies,
`d0 = 0`) or `cnf_oper_i1eq1` (ascending copies, `d0 > 0`), fed by the
decomposition `oper_bad_blocks`. -/
theorem cnf_oper {M : PairSeq} {n : ℕ} (hn : 1 ≤ n) (cM : cnf (translate M)) :
    cnf (translate (M⟦n⟧)) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact cM
  · have L1 : 1 < M.length := by omega
    have Mne : M ≠ [] := by
      intro he
      rw [he] at L1
      simp at L1
    have hPred : Pred M = M.dropLast := by
      unfold Pred
      rw [if_neg (by omega)]
    by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
    · rw [oper_eq_pred_of_zero n hL hz, hPred]
      exact cnf_dropLast Mne cM
    · by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
      · obtain ⟨G, v0, w0, R, d0, lp, Meq, Mneq, hR, lpv, disj, -⟩ :=
          oper_bad_blocks L1 hz hp hn
        have raweq : (List.range n).flatMap
              (fun k => ((v0, w0) :: R).map fun p => (p.1 + k * d0, p.2))
            = copies d0 ((v0, w0) :: R) n := rfl
        have cM' : cnf (translate (G ++ ((v0, w0) :: R) ++ [lp])) := Meq ▸ cM
        rw [Mneq, raweq]
        rcases disj with ⟨d0z, -⟩ | ⟨d0pos, w0lt, lphd, -⟩
        · subst d0z
          rw [copies_replicate]
          exact cnf_oper_i1eq0 hR lpv hn cM'
        · exact cnf_oper_i1eq1 hR d0pos w0lt lphd hn cM'
      · rw [oper_eq_pred_of_noParent n hL hz hp, hPred]
        exact cnf_dropLast Mne cM

/-- **Every standard-form sequence translates to a CNF term.**  Induction
over the generation of `ST_PS`: the diagonal seeds are CNF (`cnf_diag`) and
each expansion step preserves CNF (`cnf_oper`). -/
theorem cnf_ST_PS {M : PairSeq} (hM : ST_PS M) : cnf (translate M) := by
  induction hM with
  | diag v => exact cnf_diag v
  | oper hM hn ih => exact cnf_oper hn ih

end YAPSS
