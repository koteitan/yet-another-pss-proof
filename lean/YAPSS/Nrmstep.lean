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
import Mathlib.Algebra.NeZero

namespace YAPSS

open Three

/-! ## Small computation lemmas -/

@[simp] theorem translate_nil : translate [] = Z := by rw [translate]

/-! ## The max-row1 suffix (sequence side of the E6 machinery)

`msfx S` is the suffix of `S` starting at the *first* column whose row-1
value is maximal.  Empirically (E6): on standard dominated segments the
host-level projection, when it fires, evaluates to `nrm (translate (msfx S))`.
This section provides the pure sequence laws of `maxr1`/`msfx`. -/

/-- Maximal row-1 value of a segment (`0` on the empty segment). -/
def maxr1 (S : PairSeq) : ℕ := S.foldr (fun c m => max c.2 m) 0

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

/-! ## Take-transfer for the parent relations -/

theorem nextrel0_bound {M : PairSeq} {a b : ℕ} (h : nextrel0 M a b) :
    b < M.length := h.2.1

theorem le0_le {M : PairSeq} {a b : ℕ} (h : le0 M a b) : a ≤ b := by
  obtain ⟨-, -, hch⟩ := h
  induction hch with
  | refl => exact le_rfl
  | tail _ hs ih => exact le_trans ih (le_of_lt (nextrel0_lt hs))

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

end YAPSS
