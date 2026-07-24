/-
# `AscArgDom` reduced to a single HOST-FREE core (`ArgDomCore`)

`YAPSS/Cofinality.lean` reduces PSS Bachmann cofinality to the ascending
residual `AscArgDom`: with `blk = (v0,w0) :: R`, `q = (v0+d0,w0)` and
`S_hi = S.takeWhile (v0+d0 < ·.1)`,

    ST_PS (G ++ blk ++ [(v0+d0, w0+1)]) → ST_PS (G ++ blk ++ q :: S) → …
      → ∃ m, sle S_hi (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 blk) m)).

That statement mentions **two** standard forms (the host `M` and the small side
`N`).  This file removes the host: everything reduces to one statement about a
**single** standard form,

    `ArgDomCore` : inside `N`, the argument of a column `(u+e, w)` that sits
    inside the argument `A` of an earlier column `(u, w)` is `sle`-dominated by
    the `e`-shift of `A`, provided every *right-visible* column of the material
    between them that lies below level `u+e` carries row-1 `≥ w`.

The host `M` is used only to supply that side condition (`SpineOK`): by
`le0_through_pivot`, a right-visible column of `R` below level `v0+d0` is a
**row-0 ancestor of the dropped column** `lp`, and the `nextrel1` minimality
clause — the very clause whose absence made the old statement false — then gives
its row-1 value `≥ w0 + 1`.

The passage from the single `ArgDomCore` instance to the full copy tower is pure
list algebra (`peel_aux`): the conclusion of `ArgDomCore` is *self-referential*
(`A` contains `B`), so one application unfolds into the whole tower, one copy per
recursion step.  This is also why the explicit witness `m = |S_hi|` of
`AscArgDomExplicit` works: each unfolding step consumes at least one column of
`S_hi`.

## Model evidence

* `ArgDomCore` itself (as stated here, with the right-visible side condition):
  **0 violations** over 965 / 18358 / 190729 instances at closures
  `(v ≤ 4, n ≤ 3, len ≤ 10, depth 5)`, `(v ≤ 5, n ≤ 5, len ≤ 11, depth 7)`,
  `(v ≤ 3, n ≤ 5, len ≤ 14, depth 9)` (`tools/probe_k1c4.py`).
* The side condition is **load-bearing**: dropping it gives 50 violations / 1460
  already at the smallest closure — the minimal witness is
  `N = (0,0)(1,1)(2,1)(3,0)(4,1)(5,1)` at the pair `(2,1) … (4,1)`, which is
  exactly the counterexample recorded in `AscArgDomProof.lean`.
* The right-visible condition and the `le0`-ancestor condition
  ("every row-0 ancestor of `j` strictly between carries row-1 `≥ w`") select
  **exactly** the same instances (0 mismatches over all three closures).

## What remains, and what is ruled out

`ArgDomCore` is the whole residual.  Part E below proves — as a real theorem,
`argDomCore_needs_reachability` — that it does **not** follow from
`blockok / z0ok / r1ok / cnf`: the sequence `(0,0)(1,1)(2,1)(3,2)(2,1)(3,2)`
satisfies all four and refutes the conclusion.  So any proof must descend the
`ST_PS` derivation itself (the non-structural axis), i.e. induct on
`ST_PS.diag / ST_PS.oper`:

* `diag`: vacuous — in `diagSeq 0 v` a column is `(t,t)`, so `row1 i = row1 j`
  forces `i = j`.
* `oper`, `|N₁| ≤ 1`: `N = N₁` has `≤ 1` column, no instance.
* `oper`, last column `(0,0)`: `N = N₁.dropLast`, and both arguments and `le0`
  are unchanged (the `(0,0)` never enters a `takeWhile` at level `> 0`) — direct
  IH.
* `oper`, `noparent`: empty on `ST_PS` (`hasParent_last_ST_PS`).
* `oper`, `bad`: `N = G₁ ++ copies d₁ blk₁ k` — the real case, needing positional
  bookkeeping between the instance `(i,j)` and the copy decomposition.

Measured shape of the residual comparison (`tools/probe_argcore_stats.py`, 96884
non-degenerate instances): the *head* columns of `B` and `shiftr0 e A` always sit
at the same level, and

    S1 :  B.headI.2 ≤ (shiftr0 e A).headI.2   —   0 violations,

so the comparison is decided at the head in 44% of instances, `B` is a prefix in
20%, and the rest recurse (max observed depth 5).  `S1` is exactly what the
local-invariant counterexample above violates, so `S1` also needs the derivation.

## State of this file

Green and `sorryAx`-free except for **one** named residual, `argDomCoreOn_bad`
(Part F): the `bad` branch of the `ST_PS` derivation induction for `ArgDomCore`.
Everything else — the reduction `ArgDomCore → AscArgDom → pss_cofinality`, the
`diag`, `|M| ≤ 1`, `(0,0)`-last and `noparent` branches of that induction, and
the negative result of Part E — is complete.  `argDomCoreOn_bad`'s docstring
carries the three-case plan (`j < p`, `p ≤ i`, `i < p ≤ j`) and the tools built
for it (`sle_of_short`, `sle_shiftr0`, `peel_aux`, `seqlex_of_sle_not_prefix`).
-/
import YAPSS.Cofinality

namespace YAPSS

open Three

/-! ## Part A — list algebra

Two facts about `sle` / `seqlex` that drive the unfolding of one `ArgDomCore`
instance into the whole copy tower. -/

/-- If `X` is `sle`-below `W ++ Y` but `W` is **not** a prefix of `X`, then the
comparison is already decided inside `W`: `X` is strictly below `W ++ Y'` for
*every* continuation `Y'`. -/
theorem seqlex_of_sle_not_prefix : ∀ {W X Y : PairSeq}, sle X (W ++ Y) →
    (∀ X', X ≠ W ++ X') → ∀ (Y' : PairSeq), seqlex X (W ++ Y') := by
  intro W
  induction W with
  | nil =>
    intro X Y _ hnp _
    exact absurd (by simp : X = [] ++ X) (hnp X)
  | cons w W' ih =>
    intro X Y h hnp Y'
    rcases X with _ | ⟨x, X''⟩
    · simp
    · rw [List.cons_append] at h ⊢
      rcases h with he | hs
      · exact absurd he (by
          have := hnp Y
          rw [List.cons_append] at this
          exact this)
      · rw [seqlex_cons_cons] at hs
        rcases hs with hp | ⟨rfl, hs'⟩
        · exact Or.inl hp
        · refine Or.inr ⟨rfl, ih (Y := Y) (Or.inr hs') ?_ Y'⟩
          intro Z hZ
          exact hnp Z (by rw [hZ, List.cons_append])

/-- **The peel.**  `ArgDomCore`'s conclusion is self-referential: the bound
`Q ++ (a,w) :: shiftr0 d (X ++ A2)` mentions `X` itself.  Unfolding it one step
at a time either decides the comparison inside `Q ++ [(a,w)]` (done, one copy
suffices) or strips `Q ++ [(a,w)]` off `X` and repeats one level up — which is
exactly the next copy of the tower.  The recursion terminates because each step
consumes at least the column `(a,w)`. -/
theorem peel_aux (d w : ℕ) : ∀ (n : ℕ) (X Q A2 : PairSeq) (a : ℕ), X.length ≤ n →
    sle X (Q ++ (a, w) :: shiftr0 d (X ++ A2)) →
    ∃ m, sle X (Q ++ copies d ((a, w) :: shiftr0 d Q) m) := by
  intro n
  induction n with
  | zero =>
    intro X Q A2 a hlen _
    have hX : X = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hX
    refine ⟨0, ?_⟩
    rw [copies_zero, List.append_nil]
    rcases Q with _ | ⟨q, Q'⟩
    · exact Or.inl rfl
    · exact Or.inr (by simp)
  | succ n ih =>
    intro X Q A2 a hlen h
    classical
    by_cases hpre : ∃ X', X = Q ++ (a, w) :: X'
    · obtain ⟨X', rfl⟩ := hpre
      -- strip the common prefix `Q ++ [(a,w)]`
      have hstep : sle X' (shiftr0 d Q ++ (a + d, w) :: shiftr0 d (X' ++ A2)) := by
        have h' : sle (Q ++ (a, w) :: X')
            (Q ++ (a, w) :: shiftr0 d ((Q ++ (a, w) :: X') ++ A2)) := h
        have hc : sle ((a, w) :: X') ((a, w) :: shiftr0 d ((Q ++ (a, w) :: X') ++ A2)) :=
          (sle_append_cancel Q).1 h'
        have hc2 : sle X' (shiftr0 d ((Q ++ (a, w) :: X') ++ A2)) :=
          (sle_append_cancel [(a, w)]).1 (by simpa using hc)
        have hrw : shiftr0 d ((Q ++ (a, w) :: X') ++ A2)
            = shiftr0 d Q ++ (a + d, w) :: shiftr0 d (X' ++ A2) := by
          rw [List.append_assoc, List.cons_append, shiftr0_append, shiftr0_cons]
        rwa [hrw] at hc2
      have hlen' : X'.length ≤ n := by
        simp only [List.length_append, List.length_cons] at hlen
        omega
      obtain ⟨m, hm⟩ := ih X' (shiftr0 d Q) A2 (a + d) hlen' hstep
      refine ⟨m + 1, ?_⟩
      have hrw : Q ++ copies d ((a, w) :: shiftr0 d Q) (m + 1)
          = (Q ++ [(a, w)]) ++
              (shiftr0 d Q ++ copies d ((a + d, w) :: shiftr0 d (shiftr0 d Q)) m) := by
        rw [copies_succ_front, shiftr0_copies, shiftr0_cons]
        simp
      rw [hrw]
      have : Q ++ (a, w) :: X' = (Q ++ [(a, w)]) ++ X' := by simp
      rw [this]
      exact (sle_append_cancel _).2 hm
    · -- the comparison is decided inside `Q ++ [(a,w)]`
      refine ⟨1, Or.inr ?_⟩
      rw [copies_one]
      have hW : sle X ((Q ++ [(a, w)]) ++ shiftr0 d (X ++ A2)) := by
        simpa using h
      have hnp : ∀ X', X ≠ (Q ++ [(a, w)]) ++ X' := by
        intro X' hX'
        exact hpre ⟨X', by rw [hX']; simp⟩
      have := seqlex_of_sle_not_prefix hW hnp (shiftr0 d Q)
      simpa using this


/-- A comparison that is already over by the end of `P` does not see `Y` at all. -/
theorem sle_take_of_short : ∀ {P X Y : PairSeq}, sle X (P ++ Y) →
    X.length ≤ P.length → sle X P := by
  intro P
  induction P with
  | nil =>
    intro X Y _ hlen
    have : X = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    exact Or.inl this
  | cons p P' ih =>
    intro X Y h hlen
    rcases X with _ | ⟨x, X''⟩
    · exact Or.inr (by simp)
    · simp only [List.length_cons] at hlen
      rw [List.cons_append] at h
      rcases h with he | hs
      · -- `X` reproduces `P ++ Y` verbatim, so `Y` must be empty
        have hx : x = p := by simpa using congrArg List.headI he
        have hX'' : X'' = P' ++ Y := by simpa using congrArg List.tail he
        have hY : Y = [] := by
          have : X''.length = P'.length + Y.length := by rw [hX'']; simp
          exact List.eq_nil_of_length_eq_zero (by omega)
        rw [hY, List.append_nil] at hX''
        exact Or.inl (by rw [hx, hX''])
      · rw [seqlex_cons_cons] at hs
        rcases hs with hp | ⟨rfl, hs'⟩
        · exact Or.inr (Or.inl hp)
        · rcases ih (Or.inr hs') (by omega) with he' | hs''
          · exact Or.inl (by rw [he'])
          · exact Or.inr (Or.inr ⟨rfl, hs''⟩)

/-- Corollary: the verdict transfers to any other continuation. -/
theorem sle_of_short {P X Y Y' : PairSeq} (h : sle X (P ++ Y))
    (hlen : X.length ≤ P.length) : sle X (P ++ Y') :=
  sle_append_mono (sle_take_of_short h hlen) Y'

/-- `shiftr0 d` is injective. -/
theorem shiftr0_injective (d : ℕ) {X Y : PairSeq} (h : shiftr0 d X = shiftr0 d Y) : X = Y := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1 + d, p.2)) := by
    intro a b hab
    rw [Prod.mk.injEq] at hab
    exact Prod.ext (by omega) hab.2
  exact List.map_injective_iff.2 hinj h

/-- `shiftr0` is an order isomorphism for `seqlex` (it shifts every row-0 value
by the same amount, so all column comparisons are unchanged). -/
theorem seqlex_shiftr0 (d : ℕ) : ∀ {X Y : PairSeq},
    seqlex (shiftr0 d X) (shiftr0 d Y) ↔ seqlex X Y := by
  intro X
  induction X with
  | nil =>
    intro Y
    rcases Y with _ | ⟨y, Y'⟩ <;> simp [shiftr0]
  | cons x X' ih =>
    intro Y
    rcases Y with _ | ⟨y, Y'⟩
    · simp [shiftr0]
    · rw [shiftr0_cons, shiftr0_cons, seqlex_cons_cons, seqlex_cons_cons, ih]
      constructor
      · rintro (hp | ⟨he, hs⟩)
        · exact Or.inl (by simp only [pairlt] at hp ⊢; omega)
        · rw [Prod.mk.injEq] at he
          exact Or.inr ⟨Prod.ext (by omega) he.2, hs⟩
      · rintro (hp | ⟨rfl, hs⟩)
        · exact Or.inl (by simp only [pairlt] at hp ⊢; omega)
        · exact Or.inr ⟨rfl, hs⟩

theorem sle_shiftr0 (d : ℕ) {X Y : PairSeq} : sle (shiftr0 d X) (shiftr0 d Y) ↔ sle X Y := by
  unfold sle
  rw [seqlex_shiftr0 d]
  constructor
  · rintro (he | hs)
    · exact Or.inl (shiftr0_injective d he)
    · exact Or.inr hs
  · rintro (rfl | hs)
    · exact Or.inl rfl
    · exact Or.inr hs

/-! ## Part B — the side condition, and the host-free core -/

/-- `SpineOK A L w`: every **right-visible** column of `A` below level `L`
carries row-1 at least `w`.  "Right-visible" = no later column of `A` sits at or
below its level; these are exactly the row-0 ancestors that a column at level
`≥ L` placed after `A` would climb through. -/
def SpineOK (A : PairSeq) (L w : ℕ) : Prop :=
  ∀ (U V : PairSeq) (x : ℕ × ℕ), A = U ++ x :: V → x.1 < L →
    (∀ y ∈ V, x.1 < y.1) → w ≤ x.2

/-- **The host-free core of PSS Bachmann cofinality.**

Inside a *single* standard form, `(u, w)` is a column with argument (descendant
block) `A = A1 ++ (u+e, w) :: (B ++ A2)`, so that `(u+e, w)` is a strictly deeper
column carrying the *same* row-1 value `w`, with argument `B`.  Then `B` is
column-lex dominated by the `e`-shift of `A`.

The side condition `SpineOK A1 (u+e) w` says the row-0 ancestors of `(u+e,w)`
strictly between the two columns all carry row-1 `≥ w` — equivalently, the two
columns are **row-1 siblings**.  Without it the statement is false
(`AscArgDomProof.lean`'s counterexample is the minimal instance). -/
def ArgDomCore : Prop :=
  ∀ {X A1 B A2 Z : PairSeq} {u w e : ℕ},
    ST_PS ((X ++ (u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z) →
    0 < e →
    (∀ x ∈ A1, u < x.1) →
    (∀ x ∈ B, u + e < x.1) →
    (∀ x ∈ A2, u < x.1) →
    (A2 = [] ∨ (A2.headI).1 ≤ u + e) →
    (Z = [] ∨ (Z.headI).1 ≤ u) →
    SpineOK A1 (u + e) w →
    sle B (shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2)))

/-! ## Part C — the host supplies the side condition

This is the *only* place the host `M` is used, and it is exactly where the
`nextrel1` clause (whose absence made the older statement false, see
`AscArgDomProof.lean`) pays for itself. -/

/-- **`SpineOK` from the `nextrel1` clause.**  A right-visible column `x` of `R`
below level `v0+d0` has *every* later column of `M` strictly above it, so
`le0_through_pivot` promotes the row-0 ancestry `le0 M G.length (M.length-1)`
supplied by `nextrel1` to `le0 M x (M.length-1)`: `x` is a row-0 ancestor of the
dropped column.  The `nextrel1` minimality clause then forces
`x.2 ≥ lp.2 = w0 + 1`. -/
theorem spineOK_of_nextrel1 {G R : PairSeq} {v0 w0 d0 : ℕ}
    (hnr : nextrel1 ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) G.length
      (G ++ ((v0, w0) :: R)).length) :
    SpineOK R (v0 + d0) w0 := by
  intro U V x hR hxlt hV
  obtain ⟨-, -, -, -, hle0, hmin⟩ := hnr
  set lp : ℕ × ℕ := (v0 + d0, w0 + 1) with hlp
  set M := (G ++ ((v0, w0) :: R)) ++ [lp] with hMdef
  set A := G ++ ((v0, w0) :: U) with hAdef
  have hMeq : M = A ++ (x :: (V ++ [lp])) := by
    rw [hMdef, hAdef, hR]; simp
  have hAlen : A.length = G.length + 1 + U.length := by
    rw [hAdef]; simp; omega
  have hj1 : (G ++ ((v0, w0) :: R)).length = A.length + 1 + V.length := by
    rw [hR, hAlen]; simp; omega
  -- the column at `A.length` is `x`
  have hgx : M.getD A.length (0, 0) = x := by
    have h := getD_append_right' A (x :: (V ++ [lp])) 0
    rw [Nat.add_zero] at h
    rw [hMeq]; exact h
  -- every later column of `M`, up to and including `lp`, is strictly above `x`
  have hpiv : ∀ y, A.length < y → y ≤ (G ++ ((v0, w0) :: R)).length →
      entry M 0 A.length < entry M 0 y := by
    intro y hy1 hy2
    obtain ⟨t, rfl⟩ : ∃ t, y = A.length + (t + 1) := ⟨y - A.length - 1, by omega⟩
    have hgy : M.getD (A.length + (t + 1)) (0, 0) = (V ++ [lp]).getD t (0, 0) := by
      have h := getD_append_right' A (x :: (V ++ [lp])) (t + 1)
      rw [hMeq, h, List.getD_cons_succ]
    rw [entry_zero, entry_zero, hgx, hgy]
    rcases Nat.lt_or_ge t V.length with ht | ht
    · have hmem : V.getD t (0, 0) ∈ V := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
        exact List.getElem_mem _
      have : (V ++ [lp]).getD t (0, 0) = V.getD t (0, 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left ht]
      rw [this]
      exact hV _ hmem
    · have htv : t = V.length := by omega
      subst htv
      have : (V ++ [lp]).getD V.length (0, 0) = lp := by
        have h := getD_append_right' V [lp] 0
        rw [Nat.add_zero] at h
        exact h
      rw [this, hlp]
      exact hxlt
  -- so `x` is a row-0 ancestor of the dropped column
  have hxle0 : le0 M A.length (G ++ ((v0, w0) :: R)).length :=
    le0_through_pivot hle0 (by omega) (by omega) hpiv
  -- and the `nextrel1` minimality clause bounds its row-1 value
  have hlast : entry M 1 (G ++ ((v0, w0) :: R)).length = w0 + 1 := by
    have h := getD_append_right' (G ++ ((v0, w0) :: R)) [lp] 0
    rw [Nat.add_zero] at h
    rw [entry_one, hMdef, h, List.getD_cons_zero, hlp]
  have := hmin A.length ⟨by omega, hxle0⟩
  rw [hlast, entry_one, hgx] at this
  omega

/-! ## Part D — the reduction -/

/-- **`AscArgDom` follows from the host-free core.**

`ArgDomCore` is applied exactly once, at the block root `(v0,w0)` of `N` against
the ascending copy root `q = (v0+d0,w0)`; the host `M` enters only through
`spineOK_of_nextrel1`.  `peel_aux` then unfolds the self-referential bound into
the copy tower. -/
theorem ascArgDom_of_core (H : ArgDomCore) : AscArgDom := by
  intro G R S v0 w0 d0 _ hN hRgt hd hnr
  classical
  set Shi := S.takeWhile (fun p => v0 + d0 < p.1) with hShidef
  set D := S.dropWhile (fun p => v0 + d0 < p.1) with hDdef
  set A2 := D.takeWhile (fun p => v0 < p.1) with hA2def
  set Z := D.dropWhile (fun p => v0 < p.1) with hZdef
  have hSsplit : Shi ++ D = S := List.takeWhile_append_dropWhile
  have hDsplit : A2 ++ Z = D := List.takeWhile_append_dropWhile
  have hShigt : ∀ x ∈ Shi, v0 + d0 < x.1 := by
    intro x hx; simpa using List.mem_takeWhile_imp hx
  have hA2gt : ∀ x ∈ A2, v0 < x.1 := by
    intro x hx; simpa using List.mem_takeWhile_imp hx
  have hDhd : D = [] ∨ (D.headI).1 ≤ v0 + d0 := by
    rcases hdd : D with _ | ⟨z, Z'⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h := List.head?_dropWhile_not (fun p : ℕ × ℕ => decide (v0 + d0 < p.1)) S
      rw [← hDdef, hdd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 + d0 < z.1) := by simpa using h
      simp only [List.headI]; omega
  have hA2hd : A2 = [] ∨ (A2.headI).1 ≤ v0 + d0 := by
    rcases hdd : A2 with _ | ⟨z, Z'⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have hDne : D ≠ [] := by
        intro he; rw [hA2def, he] at hdd; simp at hdd
      have hhd : A2.headI = D.headI := by
        rcases hd2 : D with _ | ⟨y, Y⟩
        · exact absurd hd2 hDne
        · rw [hA2def, hd2]
          by_cases hy : v0 < y.1
          · rw [List.takeWhile_cons_of_pos (by simpa using hy)]; rfl
          · rw [List.takeWhile_cons_of_neg (by simpa using hy)]
            rw [hA2def, hd2, List.takeWhile_cons_of_neg (by simpa using hy)] at hdd
            simp at hdd
      rw [← hdd, hhd]
      rcases hDhd with h | h
      · exact absurd h hDne
      · exact h
  have hZhd : Z = [] ∨ (Z.headI).1 ≤ v0 := by
    rcases hdd : Z with _ | ⟨z, Z'⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h := List.head?_dropWhile_not (fun p : ℕ × ℕ => decide (v0 < p.1)) D
      rw [← hZdef, hdd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 < z.1) := by simpa using h
      simp only [List.headI]; omega
  -- re-bracket `N` in the shape `ArgDomCore` wants
  have hNeq : (G ++ ((v0, w0) :: R)) ++ (v0 + d0, w0) :: S
      = (G ++ (v0, w0) :: (R ++ (v0 + d0, w0) :: (Shi ++ A2))) ++ Z := by
    rw [← hSsplit, ← hDsplit]; simp
  have hcore := H (X := G) (A1 := R) (B := Shi) (A2 := A2) (Z := Z)
    (u := v0) (w := w0) (e := d0) (hNeq ▸ hN) hd hRgt hShigt hA2gt hA2hd hZhd
    (spineOK_of_nextrel1 hnr)
  -- the bound is self-referential; unfold it into the copy tower
  have hbnd : shiftr0 d0 (R ++ (v0 + d0, w0) :: (Shi ++ A2))
      = shiftr0 d0 R ++ (v0 + d0 + d0, w0) :: shiftr0 d0 (Shi ++ A2) := by
    rw [shiftr0_append, shiftr0_cons]
  rw [hbnd] at hcore
  obtain ⟨m, hm⟩ := peel_aux d0 w0 Shi.length Shi (shiftr0 d0 R) A2 (v0 + d0 + d0)
    le_rfl hcore
  refine ⟨m, ?_⟩
  have hgoal : shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R)) m)
      = shiftr0 d0 R ++ copies d0 ((v0 + d0 + d0, w0) :: shiftr0 d0 (shiftr0 d0 R)) m := by
    rw [shiftr0_append, shiftr0_copies, shiftr0_cons, shiftr0_cons]
  rw [hgoal]
  exact hm

/-- **PSS Bachmann cofinality from the single host-free core.** -/
theorem pss_cofinality_of_core (H : ArgDomCore) {M N : PairSeq}
    (hM : ST_PS M) (hN : ST_PS N) (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  pss_cofinality_of_argdom (ascArgDom_of_core H) hM hN h


/-! ## Part E — the core genuinely needs reachability

`ArgDomCore` is **not** a consequence of the local standard-form invariants.
The sequence

    L = (0,0)(1,1)(2,1)(3,2)(2,1)(3,2)

satisfies `blockok 0`, `z0ok`, `r1ok` **and** `cnf (translate ·)` — every local
invariant the file's machinery supplies — yet violates the conclusion of
`ArgDomCore` at `(u,w) = (1,1)`, `e = 1` (where `SpineOK` is vacuous):

    A = (2,1)(3,2)(2,1)(3,2),   B = (3,2),   shiftr0 1 A = (3,1)(4,2)(3,1)(4,2)

and `(3,2) > (3,1)`.  `L ∉ ST_PS` (model-checked over three closures), so the
proof of `ArgDomCore` **must** descend the `ST_PS` derivation; no argument from
`blockok / z0ok / r1ok / cnf` alone can work. -/

/-- The local-invariant witness `L = (0,0)(1,1)(2,1)(3,2)(2,1)(3,2)`. -/
def locL : PairSeq := [(0, 0), (1, 1), (2, 1), (3, 2), (2, 1), (3, 2)]

theorem locL_eq :
    locL = (([((0:ℕ), (0:ℕ))] ++ (1, 1) :: ([(2, 1), (3, 2)] ++ (1 + 1, 1) ::
      ([((3:ℕ), (2:ℕ))] ++ []))) ++ []) := by decide

theorem locL_blockok : blockok 0 locL := by
  refine ⟨fun _ => rfl, by decide, ?_⟩
  show steps1 locL
  unfold locL
  exact ⟨by decide, by decide, by decide, by decide, by decide, trivial⟩

theorem locL_z0ok : z0ok locL := by
  intro j hj h0
  have hj6 : j < 6 := by simpa [locL] using hj
  rcases j with _ | _ | _ | _ | _ | _ | j
  · revert h0; decide
  · revert h0; decide
  · revert h0; decide
  · revert h0; decide
  · revert h0; decide
  · revert h0; decide
  · omega

theorem locL_r1ok : r1ok locL := by
  intro j hj hpos
  have hj6 : j < 6 := by simpa [locL] using hj
  rcases j with _ | _ | _ | _ | _ | _ | j
  · exact absurd hpos (by decide)
  · exact ⟨0, by decide, by decide, by intro l h1 h2; omega, by decide⟩
  · exact ⟨1, by decide, by decide, by intro l h1 h2; omega, by decide⟩
  · exact ⟨2, by decide, by decide, by intro l h1 h2; omega, by decide⟩
  · refine ⟨1, by decide, by decide, ?_, by decide⟩
    intro l h1 h2
    rcases l with _ | _ | _ | l
    · omega
    · omega
    · decide
    · rcases l with _ | l
      · decide
      · omega
  · exact ⟨4, by decide, by decide, by intro l h1 h2; omega, by decide⟩
  · omega

theorem locL_translate :
    translate locL = P 0 (P 1 (P 1 (P 2 Z Z) (P 1 (P 2 Z Z) Z)) Z) Z := by
  unfold locL
  simp [translate, List.takeWhile, List.dropWhile]

theorem locL_cnf : cnf (translate locL) := by
  rw [locL_translate]
  refine cnf_P_Z.2 (cnf_P_Z.2 (cnf_P_P.2 ⟨cnf_P_Z.2 cnf_Z, ?_, cnf_P_Z.2 (cnf_P_Z.2 cnf_Z)⟩))
  exact olt_irrefl _

/-- `SpineOK` is vacuous here: no column of `A1` sits below level `u + e = 2`. -/
theorem locL_spineOK : SpineOK [((2:ℕ), (1:ℕ)), (3, 2)] (1 + 1) 1 := by
  intro U V x hUV hxlt _
  have hx : x ∈ [((2:ℕ), (1:ℕ)), (3, 2)] := by
    rw [hUV]; exact List.mem_append_right _ (List.mem_cons_self ..)
  rcases List.mem_cons.1 hx with rfl | hx
  · exact absurd hxlt (by decide)
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact absurd hxlt (by decide)
    · simp at hx

/-- 🚨 **The conclusion fails on `locL`**: `(3,2)` exceeds `(3,1)` at the very
first column. -/
theorem locL_not_sle :
    ¬ sle [((3:ℕ), (2:ℕ))]
        (shiftr0 1 ([((2:ℕ), (1:ℕ)), (3, 2)] ++ (1 + 1, 1) :: ([((3:ℕ), (2:ℕ))] ++ []))) := by
  have hs : shiftr0 1 ([((2:ℕ), (1:ℕ)), (3, 2)] ++ (1 + 1, 1) :: ([((3:ℕ), (2:ℕ))] ++ []))
      = ((3 : ℕ), (1 : ℕ)) :: [(4, 2), (3, 1), (4, 2)] := by decide
  rw [hs]
  rintro (h | h)
  · exact absurd h (by decide)
  · rw [seqlex_cons_cons] at h
    rcases h with h | ⟨h, -⟩
    · exact absurd h (by unfold pairlt; simp)
    · exact absurd h (by decide)

/-- 🚨 **`ArgDomCore` is not implied by `blockok / z0ok / r1ok / cnf`.**  Any
proof must use the `ST_PS` derivation itself. -/
theorem argDomCore_needs_reachability :
    ∃ (N X A1 B A2 Z : PairSeq) (u w e : ℕ),
      N = (X ++ (u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z ∧
      blockok 0 N ∧ z0ok N ∧ r1ok N ∧ cnf (translate N) ∧
      0 < e ∧ (∀ x ∈ A1, u < x.1) ∧ (∀ x ∈ B, u + e < x.1) ∧ (∀ x ∈ A2, u < x.1) ∧
      (A2 = [] ∨ (A2.headI).1 ≤ u + e) ∧ (Z = [] ∨ (Z.headI).1 ≤ u) ∧
      SpineOK A1 (u + e) w ∧
      ¬ sle B (shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2))) :=
  ⟨locL, [(0, 0)], [(2, 1), (3, 2)], [(3, 2)], [], [], 1, 1, 1,
    locL_eq, locL_blockok, locL_z0ok, locL_r1ok, locL_cnf, one_pos,
    by decide, by decide, by decide, Or.inl rfl, Or.inl rfl,
    locL_spineOK, locL_not_sle⟩


/-! ## Part F — the `ST_PS` derivation induction for `ArgDomCore`

Part E rules out every argument from the local invariants, so the proof has to
descend the derivation.  This section sets up that induction and discharges all
branches except `bad`, which is isolated as `argDomCoreOn_bad`. -/

/-- Per-sequence form of `ArgDomCore` (the induction carrier). -/
def ArgDomCoreOn (N : PairSeq) : Prop :=
  ∀ ⦃X A1 B A2 Z : PairSeq⦄ ⦃u w e : ℕ⦄,
    N = (X ++ (u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z →
    0 < e →
    (∀ x ∈ A1, u < x.1) →
    (∀ x ∈ B, u + e < x.1) →
    (∀ x ∈ A2, u < x.1) →
    (A2 = [] ∨ (A2.headI).1 ≤ u + e) →
    (Z = [] ∨ (Z.headI).1 ≤ u) →
    SpineOK A1 (u + e) w →
    sle B (shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2)))

theorem argDomCore_of_on (H : ∀ N, ST_PS N → ArgDomCoreOn N) : ArgDomCore := by
  intro X A1 B A2 Z u w e hST hd h1 h2 h3 h4 h5 h6
  exact H _ hST rfl hd h1 h2 h3 h4 h5 h6

/-- The two marked columns of an `ArgDomCoreOn` instance, by position. -/
theorem argdom_pos {N X A1 B A2 Z : PairSeq} {u w e : ℕ}
    (heq : N = (X ++ (u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z) :
    N.getD X.length (0, 0) = (u, w) ∧
    N.getD (X.length + (A1.length + 1)) (0, 0) = (u + e, w) ∧
    X.length + (A1.length + 1) < N.length := by
  have hN : N = X ++ ((u, w) :: ((A1 ++ (u + e, w) :: ((B ++ A2) ++ Z)))) := by
    rw [heq]; simp [List.append_assoc]
  refine ⟨?_, ?_, ?_⟩
  · have h := getD_append_right' X ((u, w) :: (A1 ++ (u + e, w) :: ((B ++ A2) ++ Z))) 0
    rw [Nat.add_zero] at h
    rw [hN, h, List.getD_cons_zero]
  · have h := getD_append_right' X ((u, w) :: (A1 ++ (u + e, w) :: ((B ++ A2) ++ Z)))
      (A1.length + 1)
    have h2 := getD_append_right' A1 ((u + e, w) :: ((B ++ A2) ++ Z)) 0
    rw [Nat.add_zero] at h2
    rw [hN, h, List.getD_cons_succ, h2, List.getD_cons_zero]
  · rw [hN]; simp

/-- **Base case**: in a diagonal every column is `(t,t)`, so two columns with the
same row-1 value are equal — no instance has `0 < e`. -/
theorem argDomCoreOn_diag (v : ℕ) : ArgDomCoreOn (diagSeq 0 v) := by
  intro X A1 B A2 Z u w e heq he _ _ _ _ _ _
  exfalso
  obtain ⟨hp, hq, hlt⟩ := argdom_pos heq
  rw [diagSeq0_length] at hlt
  rw [diagSeq0_getD (by omega)] at hp
  rw [diagSeq0_getD (by omega)] at hq
  have h1 : X.length = u := congrArg Prod.fst hp
  have h2 : X.length = w := congrArg Prod.snd hp
  have h3 : X.length + (A1.length + 1) = u + e := congrArg Prod.fst hq
  have h4 : X.length + (A1.length + 1) = w := congrArg Prod.snd hq
  omega

/-- **`(0,0)`-last branch**: dropping a level-`0` last column changes nothing —
the extra column can only join the trailing context `Z`, whose only requirement
is that it re-open at or below `u`. -/
theorem argDomCoreOn_snoc_zero {N : PairSeq} {p : ℕ × ℕ} (hp : p.1 = 0)
    (H : ArgDomCoreOn (N ++ [p])) : ArgDomCoreOn N := by
  intro X A1 B A2 Z u w e heq he h1 h2 h3 h4 h5 h6
  refine H (X := X) (A1 := A1) (B := B) (A2 := A2) (Z := Z ++ [p]) ?_ he h1 h2 h3 h4 ?_ h6
  · rw [heq]; simp [List.append_assoc]
  · rcases Z with _ | ⟨z, Z'⟩
    · exact Or.inr (by simp [hp])
    · refine Or.inr ?_
      rcases h5 with hc | hc
      · exact absurd hc (by simp)
      · exact hc


/-! ### Transfer lemmas for the induction step

`ArgDomCoreOn` never mentions the prefix `X` except through the defining
equation, so instances are insensitive to what sits to their left, and they
commute with a uniform row-0 shift.  Together these reduce an instance living
beyond the first copy of `M⟦n⟧` to one in `M⟦n-1⟧`. -/

/-- Instances do not see the material to their left. -/
theorem argDomCoreOn_drop_left {P S : PairSeq} (H : ArgDomCoreOn (P ++ S)) :
    ArgDomCoreOn S := by
  intro X A1 B A2 Z u w e heq he h1 h2 h3 h4 h5 h6
  refine H (X := P ++ X) (A1 := A1) (B := B) (A2 := A2) (Z := Z) ?_ he h1 h2 h3 h4 h5 h6
  rw [heq]; simp [List.append_assoc]

/-- Conversely, an instance of `S` is an instance of `P ++ S` (the prefix is
absorbed into `X`).  This is the form used to *apply* an inherited instance. -/
theorem argDomCoreOn_extend_left {S : PairSeq} (H : ArgDomCoreOn S) (P : PairSeq)
    ⦃X A1 B A2 Z : PairSeq⦄ ⦃u w e : ℕ⦄
    (heq : P ++ S = ((P ++ X) ++ (u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z)
    (he : 0 < e) (h1 : ∀ x ∈ A1, u < x.1) (h2 : ∀ x ∈ B, u + e < x.1)
    (h3 : ∀ x ∈ A2, u < x.1) (h4 : A2 = [] ∨ (A2.headI).1 ≤ u + e)
    (h5 : Z = [] ∨ (Z.headI).1 ≤ u) (h6 : SpineOK A1 (u + e) w) :
    sle B (shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2))) := by
  refine H (X := X) (A1 := A1) (B := B) (A2 := A2) (Z := Z) ?_ he h1 h2 h3 h4 h5 h6
  have : P ++ S = P ++ ((X ++ (u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z) := by
    rw [heq]; simp [List.append_assoc]
  exact List.append_cancel_left this

/-- The left inverse of `shiftr0`. -/
def shiftl0 (d : ℕ) : PairSeq → PairSeq := List.map fun p => (p.1 - d, p.2)

theorem shiftl0_cons (d : ℕ) (p : ℕ × ℕ) (A : PairSeq) :
    shiftl0 d (p :: A) = (p.1 - d, p.2) :: shiftl0 d A := rfl

theorem shiftl0_append (d : ℕ) (A B : PairSeq) :
    shiftl0 d (A ++ B) = shiftl0 d A ++ shiftl0 d B := List.map_append

theorem mem_shiftl0 {d : ℕ} {M : PairSeq} {x : ℕ × ℕ} :
    x ∈ shiftl0 d M ↔ ∃ p ∈ M, ((p.1 - d, p.2) : ℕ × ℕ) = x := by
  unfold shiftl0; simp

@[simp] theorem shiftl0_shiftr0 (d : ℕ) (X : PairSeq) : shiftl0 d (shiftr0 d X) = X := by
  induction X with
  | nil => rfl
  | cons p X' ih => rw [shiftr0_cons, shiftl0_cons, ih]; simp

theorem shiftr0_shiftl0 {d : ℕ} {L : PairSeq} (h : ∀ x ∈ L, d ≤ x.1) :
    shiftr0 d (shiftl0 d L) = L := by
  induction L with
  | nil => rfl
  | cons p L' ih =>
    have hp : d ≤ p.1 := h p (List.mem_cons_self ..)
    rw [shiftl0_cons, shiftr0_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    congr 1
    exact Prod.ext (by simp only []; omega) rfl

theorem shiftr0_comm (d e : ℕ) (L : PairSeq) :
    shiftr0 e (shiftr0 d L) = shiftr0 d (shiftr0 e L) := by
  unfold shiftr0
  rw [List.map_map, List.map_map]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.mk.injEq, and_true]
  omega

/-- Instances commute with a uniform row-0 shift. -/
theorem argDomCoreOn_shiftr0 {W : PairSeq} (d : ℕ) (H : ArgDomCoreOn W) :
    ArgDomCoreOn (shiftr0 d W) := by
  intro X A1 B A2 Z u w e heq he h1 h2 h3 h4 h5 h6
  -- every column of the decomposition sits at row-0 `≥ d`
  have hall : ∀ x ∈ (X ++ (u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z, d ≤ x.1 := by
    rw [← heq]
    intro x hx
    obtain ⟨q, -, rfl⟩ := mem_shiftr0.1 hx
    simp
  have hmid : ∀ {L : PairSeq}, (∀ x ∈ L, x ∈ A1 ++ (u + e, w) :: (B ++ A2)) →
      ∀ x ∈ L, d ≤ x.1 := by
    intro L hL x hx
    exact hall x (List.mem_append_left Z (List.mem_append_right X
      (List.mem_cons_of_mem _ (hL x hx))))
  have hX : ∀ x ∈ X, d ≤ x.1 := fun x hx =>
    hall x (List.mem_append_left Z (List.mem_append_left _ hx))
  have hZ : ∀ x ∈ Z, d ≤ x.1 := fun x hx => hall x (List.mem_append_right _ hx)
  have hA1 : ∀ x ∈ A1, d ≤ x.1 := hmid (fun x hx => List.mem_append_left _ hx)
  have hB : ∀ x ∈ B, d ≤ x.1 := hmid (fun x hx =>
    List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
  have hA2 : ∀ x ∈ A2, d ≤ x.1 := hmid (fun x hx =>
    List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hx)))
  have hu : d ≤ u := hall (u, w) (List.mem_append_left Z (List.mem_append_right X
    (List.mem_cons_self ..)))
  -- pull the decomposition back through the shift
  set X' := shiftl0 d X with hX'
  set A1' := shiftl0 d A1 with hA1'
  set B' := shiftl0 d B with hB'
  set A2' := shiftl0 d A2 with hA2'
  set Z' := shiftl0 d Z with hZ'
  have eX : shiftr0 d X' = X := shiftr0_shiftl0 hX
  have eA1 : shiftr0 d A1' = A1 := shiftr0_shiftl0 hA1
  have eB : shiftr0 d B' = B := shiftr0_shiftl0 hB
  have eA2 : shiftr0 d A2' = A2 := shiftr0_shiftl0 hA2
  have eZ : shiftr0 d Z' = Z := shiftr0_shiftl0 hZ
  have hWeq : W = (X' ++ (u - d, w) :: (A1' ++ ((u - d) + e, w) :: (B' ++ A2'))) ++ Z' := by
    have := congrArg (shiftl0 d) heq
    rw [shiftl0_shiftr0] at this
    have harith : u + e - d = u - d + e := by omega
    rw [this, shiftl0_append, shiftl0_append, shiftl0_cons, shiftl0_append,
      shiftl0_cons, shiftl0_append]
    simp only [hX', hA1', hB', hA2', hZ', harith]
  -- transport the side conditions
  have g1 : ∀ x ∈ A1', u - d < x.1 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_shiftl0.1 hx
    have := h1 q hq; have := hA1 q hq
    simp only []; omega
  have g2 : ∀ x ∈ B', (u - d) + e < x.1 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_shiftl0.1 hx
    have := h2 q hq; have := hB q hq
    simp only []; omega
  have g3 : ∀ x ∈ A2', u - d < x.1 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_shiftl0.1 hx
    have := h3 q hq; have := hA2 q hq
    simp only []; omega
  have g4 : A2' = [] ∨ (A2'.headI).1 ≤ (u - d) + e := by
    rcases hA2e : A2 with _ | ⟨a, A2''⟩
    · exact Or.inl (by rw [hA2', hA2e]; rfl)
    · refine Or.inr ?_
      have hah : (A2.headI).1 ≤ u + e := by
        rcases h4 with hc | hc
        · exact absurd hc (by rw [hA2e]; simp)
        · exact hc
      have hage : d ≤ (A2.headI).1 := hA2 A2.headI (by rw [hA2e]; simp)
      rw [hA2', hA2e, shiftl0_cons]
      simp only [List.headI]
      rw [hA2e] at hah hage
      simp only [List.headI] at hah hage
      omega
  have g5 : Z' = [] ∨ (Z'.headI).1 ≤ u - d := by
    rcases hZe : Z with _ | ⟨z, Z''⟩
    · exact Or.inl (by rw [hZ', hZe]; rfl)
    · refine Or.inr ?_
      have hzh : (Z.headI).1 ≤ u := by
        rcases h5 with hc | hc
        · exact absurd hc (by rw [hZe]; simp)
        · exact hc
      rw [hZ', hZe, shiftl0_cons]
      simp only [List.headI]
      rw [hZe] at hzh
      simp only [List.headI] at hzh
      omega
  have g6 : SpineOK A1' ((u - d) + e) w := by
    intro U' V' x' hdec hxlt hV'
    have hdec2 : A1 = shiftr0 d U' ++ (x'.1 + d, x'.2) :: shiftr0 d V' := by
      rw [← eA1, hdec, shiftr0_append, shiftr0_cons]
    refine h6 (shiftr0 d U') (shiftr0 d V') (x'.1 + d, x'.2) hdec2 ?_ ?_
    · simp only []; omega
    · intro y hy
      obtain ⟨q, hq, rfl⟩ := mem_shiftr0.1 hy
      have := hV' q hq
      simp only []; omega
  -- apply the inherited instance and un-shift the conclusion
  have hcore := H (X := X') (A1 := A1') (B := B') (A2 := A2') (Z := Z') hWeq he g1 g2 g3 g4 g5 g6
  have hgoal : shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2))
      = shiftr0 d (shiftr0 e (A1' ++ ((u - d) + e, w) :: (B' ++ A2'))) := by
    rw [← shiftr0_comm, ← eA1, ← eB, ← eA2]
    congr 1
    rw [shiftr0_append, shiftr0_cons, shiftr0_append]
    congr 2
    exact Prod.ext (by simp only []; omega) rfl
  rw [hgoal, ← eB]
  exact (sle_shiftr0 d).2 hcore

/-- 🚨 **THE RESIDUAL** — the `bad` branch of the derivation induction.

`M = G ++ blk ++ [lp]`, `blk = (v0,w0) :: R`, `M⟦n⟧ = G ++ copies d0 blk n`.
Given `ArgDomCoreOn M`, show `ArgDomCoreOn (M⟦n⟧)`.

The right boundary is `p := G.length + blk.length` (**not** `G.length`): copy `0`
*is* `blk`, so `M⟦n⟧` and `M` agree on the whole of `M.take (M.length - 1)`.
With `i`/`j` the positions of the shallower / deeper marked column, the split is

| case | census (`tools/probe_badbranch_cases2.py`) |
|---|---|
| **B**  `j < p`  — both marked columns inside `G ++ blk` | 50237 |
| **A1** `p ≤ i`  — both beyond copy 0                    | 9369  |
| **A2** `i < p ≤ j` — the cross case                     | 26290 |

Three traps, all model-confirmed, that a coarser split walks into:

* Marked columns inside `G` (or inside one copy) do **not** give an instance of
  `M` (resp. a shift of one) for free: the *arguments* `A`, `B` are cut by the
  material to the right, which differs.  In case B alone, 29069 of 50237
  instances have `arg i` running past `p` into the copy tower (only 21168 stay).
* The cross case A2 exists and is large (26290) — an instance whose shallower
  column is in `G ++ blk` and whose deeper column is in a later copy.
* In A1 the two marked columns need **not** be the same column of `blk` repeated:
  `blk` may carry two different columns with the same row-1 value.  Witness:
  `M = (0,0)(1,1)(2,0)(1,1)`, `blk = (0,0)(1,1)(2,0)`, `d0 = 1`, `n = 2`, so
  `M⟦2⟧ = (0,0)(1,1)(2,0)(1,0)(2,1)(3,0)` and the instance `i = 0`, `j = 5`
  pairs `blk`'s offset-0 column with `blk`'s offset-2 column (502 such instances
  in the census).

Status of each case:

* **A1** — tooled and routine: `argDomCoreOn_drop_left`, `argDomCoreOn_shiftr0`
  and `argDomCoreOn_extend_left` (above) turn an instance beyond copy 0 into an
  instance of `copies d0 blk (n-1)`, hence of `M⟦n-1⟧`, via
  `copies_succ_front`.  Needs an inner induction on `n` inside the `oper` case
  (legitimate: prove `∀ n ≥ 1, ArgDomCoreOn (M⟦n⟧)` from `ArgDomCoreOn M`).
* **B** — worked out on paper: split on whether the common part is a prefix; one
  branch closes by `sle_of_short`, the other by `pairlt (tower.headI) lp`, which
  holds in *both* `oper` sub-branches (`(v1+d₁,w1) < (v1+d₁,w1+1)` ascending,
  `(v1,w1) < (v1+1,0)` exact) and is handed over by the IH.
* **A2** — the genuinely open piece.  `SpineOK` forces `w ≤ w0` here (the copy
  roots strictly between the two marked columns are right-visible and sit below
  level `u+e`), which is the handle to exploit. -/
theorem argDomCoreOn_bad {M G R : PairSeq} {v0 w0 d0 n : ℕ} {lp : ℕ × ℕ}
    (hM : ST_PS M) (hMon : ArgDomCoreOn M)
    (hMeq : M = G ++ ((v0, w0) :: R) ++ [lp])
    (hRgt : ∀ x ∈ R, v0 < x.1) (hlp : v0 < lp.1)
    (hdisj : (d0 = 0 ∧ lp.2 = 0 ∧ lp.1 = v0 + 1)
      ∨ (0 < d0 ∧ lp.2 = w0 + 1 ∧ lp.1 = v0 + d0
          ∧ nextrel1 M G.length (M.length - 1)))
    (hn : 1 ≤ n) :
    ArgDomCoreOn (G ++ copies d0 ((v0, w0) :: R) n) := by
  sorry

/-- The induction step: `ArgDomCoreOn` is preserved by `oper`. -/
theorem argDomCoreOn_oper {M : PairSeq} (hM : ST_PS M) (hMon : ArgDomCoreOn M)
    {n : ℕ} (hn : 1 ≤ n) : ArgDomCoreOn (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]; exact hMon
  · by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
    · rw [oper_eq_pred_of_zero n (by omega) hz]
      unfold Pred; rw [if_neg (by omega)]
      have hne : M ≠ [] := by intro he; rw [he] at hL; simp at hL
      have hlast : M.getD (M.length - 1) (0, 0) = (0, 0) := by
        rw [entry_zero] at hz; rw [entry_one] at hz
        exact Prod.ext hz.1 hz.2
      refine argDomCoreOn_snoc_zero (p := ((0 : ℕ), (0 : ℕ))) rfl ?_
      have hsp : M.dropLast ++ [((0 : ℕ), (0 : ℕ))] = M := by
        rw [← hlast]; exact dropLast_snoc_getD hne
      rw [hsp]; exact hMon
    · have hpar := hasParent_last_ST_PS hM (by omega) hz
      obtain ⟨G, v0, w0, R, d0, lp, hMeq, hMn, R_gt, lp_gt, disj⟩ :=
        oper_bad_blocks_all (by omega) (blockok_ST_PS hM).2.2 (r1ok_ST_PS hM) hz hpar
      rw [hMn n hn]
      exact argDomCoreOn_bad hM hMon hMeq R_gt lp_gt disj hn

/-- The derivation induction, modulo the `bad` branch. -/
theorem argDomCoreOn_ST_PS {N : PairSeq} (hN : ST_PS N) : ArgDomCoreOn N := by
  induction hN with
  | diag v => exact argDomCoreOn_diag v
  | @oper M n hM hn ih => exact argDomCoreOn_oper hM ih hn

/-- `ArgDomCore`, modulo `argDomCoreOn_bad`. -/
theorem argDomCore_holds : ArgDomCore :=
  argDomCore_of_on (fun _ h => argDomCoreOn_ST_PS h)

#print axioms peel_aux
#print axioms sle_of_short
#print axioms argDomCoreOn_drop_left
#print axioms argDomCoreOn_extend_left
#print axioms argDomCoreOn_shiftr0
#print axioms sle_shiftr0
#print axioms spineOK_of_nextrel1
#print axioms ascArgDom_of_core
#print axioms pss_cofinality_of_core
#print axioms argDomCore_needs_reachability
#print axioms argDomCoreOn_diag
#print axioms argDomCoreOn_snoc_zero
#print axioms argDomCoreOn_oper

end YAPSS

