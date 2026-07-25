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

## 証明の構造

`ArgDomCore` は `blockok` / `z0ok` / `r1ok` / `cnf` からは従わない
（`argDomCore_needs_reachability`）。したがって証明は `ST_PS` の導出そのものに沿った
帰納法になる。その分岐は次の通りである。

* `diag`：`diagSeq 0 v` の列は `(t,t)` なので `row1 i = row1 j` から `i = j` となり、
  インスタンスが存在しない。
* `oper`, `|N₁| ≤ 1`：`N = N₁` は列が 1 本以下でインスタンスが無い。
* `oper`, 末尾が `(0,0)`：`N = N₁.dropLast` で引数も `le0` も変わらない。
* `oper`, 親なし：`hasParent_last_ST_PS` により `ST_PS` 上では空。
* `oper`, コピー分岐：インスタンスの 2 本の印付き列とコピー分解との位置関係で
  3 つに分かれる（`argDomCoreOn_bad_A1` / `_B` / `_A2`）。

-/
import Cofinality

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

theorem sle_trans {A B C : PairSeq} (h1 : sle A B) (h2 : sle B C) : sle A C := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (seqlex_sle_trans h1 h2)

/-- Truncating the *smaller* side on the right keeps it below. -/
theorem sle_of_append_left {X Y W : PairSeq} (h : sle (X ++ Y) W) : sle X W := by
  refine sle_trans ?_ h
  rcases Y with _ | ⟨y, Y'⟩
  · exact Or.inl (by simp)
  · exact Or.inr (seqlex_prefix (by simp) X)

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
(the counterexample above is the minimal instance). -/
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
the counterexample above) pays for itself. -/

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

/-! ### Positional bookkeeping for the copy tower -/

/-- Split a concatenation against a shorter left factor. -/
theorem split_prefix_left {C D E F : PairSeq} (h : C ++ D = E ++ F)
    (hle : E.length ≤ C.length) :
    C = E ++ C.drop E.length ∧ F = C.drop E.length ++ D := by
  have hC : C = C.take E.length ++ C.drop E.length := (List.take_append_drop _ _).symm
  have h' : (C.take E.length) ++ (C.drop E.length ++ D) = E ++ F := by
    rw [← List.append_assoc, ← hC]; exact h
  have hlen : (C.take E.length).length = E.length := by
    rw [List.length_take]; omega
  obtain ⟨h1, h2⟩ := List.append_inj h' hlen
  refine ⟨?_, h2.symm⟩
  calc C = C.take E.length ++ C.drop E.length := hC
    _ = E ++ C.drop E.length := by rw [h1]

/-- Split a concatenation against a longer left factor. -/
theorem split_prefix_right {C D E F : PairSeq} (h : C ++ D = E ++ F)
    (hle : C.length ≤ E.length) :
    E = C ++ E.drop C.length ∧ D = E.drop C.length ++ F :=
  split_prefix_left h.symm hle

/-- The head of a nonempty copy tower is the block root. -/
theorem copies_headI {d : ℕ} {blk : PairSeq} (hne : blk ≠ []) {n : ℕ} (hn : 1 ≤ n) :
    (copies d blk n).headI = blk.headI := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [copies_succ_front]
  rcases blk with _ | ⟨b, blk'⟩
  · exact absurd rfl hne
  · simp

/-- The `ArgDomCore` bound, split at the end of the deeper argument.  Everything
to the right of `P` is invisible to the comparison because `B` is strictly
shorter than `P`. -/
theorem argbound_split (e u w : ℕ) (A1 B A2 : PairSeq) :
    shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2))
      = (shiftr0 e A1 ++ (u + e + e, w) :: shiftr0 e B) ++ shiftr0 e A2 := by
  rw [shiftr0_append, shiftr0_cons, shiftr0_append]
  simp

theorem argbound_len (e u w : ℕ) (A1 B : PairSeq) :
    B.length < (shiftr0 e A1 ++ (u + e + e, w) :: shiftr0 e B).length := by
  simp [shiftr0_length]
  omega

/-! ### The `bad` branch, split into its three cases

Fix the `oper_bad_blocks` data: `M = G ++ blk ++ [lp]` with `blk = (v0,w0) :: R`,
so the expanded sequence is

    N := G ++ copies d0 blk n        (`= M⟦n⟧` for `n ≥ 1`).

Copy `0` of the tower **is** `blk` (`copies d blk n = concat_{k<n} shiftr0 (k*d) blk`),
so `N` and `M` agree on the whole of `M.take (M.length - 1)` and the right
boundary of the shared part is

    p := G.length + blk.length = G.length + (R.length + 1)

— **not** `G.length`.

An `ArgDomCoreOn N` instance is a decomposition
`N = (X ++ (u,w) :: (A1 ++ (u+e,w) :: (B ++ A2))) ++ Z`.  By `argdom_pos` its two
marked columns sit at the positions

    i := X.length                     -- the shallower column `(u,w)`
    j := X.length + (A1.length + 1)   -- the deeper column `(u+e,w)`

and `i < j` holds by construction.  The case split is on where `i`, `j` fall
relative to `p`, phrased purely in the decomposition data:

| name | discriminator | position reading |
|---|---|---|
| **B**  | `X.length + (A1.length + 1) < G.length + (R.length + 1)` | `j < p` |
| **A2** | `X.length < G.length + (R.length + 1)` and `G.length + (R.length + 1) ≤ X.length + (A1.length + 1)` | `i < p ≤ j` |
| **A1** | `G.length + (R.length + 1) ≤ X.length` | `p ≤ i` |


**Coverage** (the point of this split): the three are pairwise exclusive and
exhaust every instance, by two applications of `Nat.lt_or_ge` and nothing else —
if `¬ (j < p)` then `p ≤ j`, and then either `i < p` (case A2) or `p ≤ i`
(case A1).  In particular the argument needs no relation between `i` and `j`, so
it cannot silently drop an instance.  `argDomCoreOn_bad` below performs exactly
this dispatch.

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
  ).

**Shared context.**  Each of the three case lemmas repeats the *entire* context,
so that it is self-contained and provable in isolation:

* `hM`, `hMon` — the host's derivation and its inherited `ArgDomCoreOn`;
* `hMeq`, `hRgt`, `hlp`, `hdisj` — the full `oper_bad_blocks_all` package
  (`hdisj` carries the `nextrel1` clause, which is load-bearing: without it the
  statement is false);
* `hSTn : ∀ m, 1 ≤ m → ST_PS (G ++ copies d0 blk m)` — the expanded sequences are
  themselves standard forms, so `blockok_ST_PS / z0ok_ST_PS / r1ok_ST_PS / cnf`
  are available *on the tower*, not just on `M`;
* `hIH : ∀ m, 1 ≤ m → m < n → ArgDomCoreOn (G ++ copies d0 blk m)` — the strong
  induction hypothesis over **smaller copy counts**.  `argDomCoreOn_bad` runs the
  inner strong induction on `n` and hands this to all three cases.  Case A1 is
  the intended consumer: `copies_succ_front` peels copy `0`, leaving the instance
  inside `shiftr0 d0 (copies d0 blk (n-1))`, which `argDomCoreOn_drop_left`,
  `argDomCoreOn_shiftr0` and `argDomCoreOn_extend_left` reduce to `hIH (n-1)`.
  Cases B and A2 receive it too, for free;
* `hn : 1 ≤ n` and the eight side conditions `heq, he, h1 … h6` of the instance;
* the case's own discriminator, last.
 -/

/-- **Case A1** — both marked columns lie beyond copy `0`: `p ≤ i` (hence
`p ≤ j` as well, since `i < j`).

Proof.  Write `n = m + 1`.  `copies_succ_front` peels copy `0`,

    G ++ copies d0 blk (m+1) = (G ++ blk) ++ shiftr0 d0 (copies d0 blk m),

and the discriminator `p ≤ i` says the prefix `G ++ blk` — whose length is
exactly `p` — is consumed by `X`.  So `split_prefix_right` splits the instance
across that boundary and re-exhibits it *verbatim* inside the tail
`shiftr0 d0 (copies d0 blk m)`, with `X` replaced by `X.drop p` and **all eight
side conditions unchanged** (they never mention the prefix).

* `m = 0` (i.e. `n = 1`): the tail is `[]`, but the re-exhibited decomposition
  contains the column `(u,w)` — contradiction on lengths.  This is the "vacuous"
  reading: the tower has length exactly `p` while `p ≤ i < j < N.length = p`.
* `m ≥ 1`: `hIH m` gives `ArgDomCoreOn (G ++ copies d0 blk m)`;
  `argDomCoreOn_drop_left` discards `G` and `argDomCoreOn_shiftr0` puts the
  `d0`-shift back on, yielding `ArgDomCoreOn (shiftr0 d0 (copies d0 blk m))`,
  which the re-exhibited instance closes directly.

Only `hIH` is used: `hM`, `hMon`, `hMeq`, `hRgt`, `hlp`, `hdisj` and `hSTn` are
not needed in this case.

⚠ Trap 3 is handled automatically: the argument never identifies the two marked
columns with columns of `blk`, so it does not care that they may be *different*
columns of `blk` carrying the same row-1 value (see the section docstring for the
witness). -/
theorem argDomCoreOn_bad_A1 {M G R : PairSeq} {v0 w0 d0 n : ℕ} {lp : ℕ × ℕ}
    (hM : ST_PS M) (hMon : ArgDomCoreOn M)
    (hMeq : M = G ++ ((v0, w0) :: R) ++ [lp])
    (hRgt : ∀ x ∈ R, v0 < x.1) (hlp : v0 < lp.1)
    (hdisj : (d0 = 0 ∧ lp.2 = 0 ∧ lp.1 = v0 + 1)
      ∨ (0 < d0 ∧ lp.2 = w0 + 1 ∧ lp.1 = v0 + d0
          ∧ nextrel1 M G.length (M.length - 1)))
    (hSTn : ∀ m, 1 ≤ m → ST_PS (G ++ copies d0 ((v0, w0) :: R) m))
    (hIH : ∀ m, 1 ≤ m → m < n → ArgDomCoreOn (G ++ copies d0 ((v0, w0) :: R) m))
    (hn : 1 ≤ n)
    {X A1 B A2 Z : PairSeq} {u w e : ℕ}
    (heq : G ++ copies d0 ((v0, w0) :: R) n
      = (X ++ (u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z)
    (he : 0 < e) (h1 : ∀ x ∈ A1, u < x.1) (h2 : ∀ x ∈ B, u + e < x.1)
    (h3 : ∀ x ∈ A2, u < x.1) (h4 : A2 = [] ∨ (A2.headI).1 ≤ u + e)
    (h5 : Z = [] ∨ (Z.headI).1 ≤ u) (h6 : SpineOK A1 (u + e) w)
    (hcase : G.length + (R.length + 1) ≤ X.length) :
    sle B (shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- peel copy `0`: `G ++ copies d0 blk (m+1) = (G ++ blk) ++ shiftr0 d0 (copies d0 blk m)`
  have hplen : (G ++ ((v0, w0) :: R)).length = G.length + (R.length + 1) := by simp
  have heq' : (G ++ ((v0, w0) :: R)) ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)
      = X ++ (((u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z) := by
    rw [List.append_assoc, ← copies_succ_front, heq]
    simp [List.append_assoc]
  -- `p ≤ i` puts the whole instance strictly to the right of copy `0`
  obtain ⟨hX, hW⟩ := split_prefix_right heq' (by omega)
  have hWeq : shiftr0 d0 (copies d0 ((v0, w0) :: R) m)
      = (X.drop (G ++ ((v0, w0) :: R)).length ++ (u, w) ::
          (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z := by
    rw [hW]; simp [List.append_assoc]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `n = 1`: the tower is exactly `G ++ blk`, so there is no room — vacuous
    exfalso
    rw [copies_zero, shiftr0_nil] at hWeq
    have hlen := congrArg List.length hWeq
    simp at hlen
  · -- `n ≥ 2`: drop `G`, strip the shift, and close with the copy-count IH
    exact argDomCoreOn_shiftr0 d0 (argDomCoreOn_drop_left (hIH m hm (by omega)))
      hWeq he h1 h2 h3 h4 h5 h6

/-- Split a column list at the first column at or below level `L`: the prefix is
the argument (everything strictly above `L`), the suffix re-opens at or below
`L`. -/
theorem arg_split (L : ℕ) : ∀ (E : PairSeq),
    ∃ Bp Rp : PairSeq, E = Bp ++ Rp ∧ (∀ x ∈ Bp, L < x.1) ∧ (Rp = [] ∨ (Rp.headI).1 ≤ L) := by
  intro E
  induction E with
  | nil => exact ⟨[], [], rfl, by simp, Or.inl rfl⟩
  | cons a E' ih =>
    by_cases ha : L < a.1
    · obtain ⟨Bp, Rp, hE, hBp, hRp⟩ := ih
      refine ⟨a :: Bp, Rp, by rw [List.cons_append, ← hE], ?_, hRp⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact hBp x hx
    · exact ⟨[], a :: E', rfl, by simp, Or.inr (by simp; omega)⟩

/-- **The splice at the dropped column, bound-relative form.**  Strengthening of
`seqlex_of_sle_snoc`: the hypothesis only has to bound `X ++ [lp]` by *some*
continuation of `V`, and the conclusion is then valid for *every* continuation of
`V`.  (`seqlex_of_sle_snoc` is the special case `E = []`.)  This is what
transfers a bound proved in the host `M` — whose material after `X` is the
dropped column `lp` — to the copy tower, whose material after `X` starts with a
copy root `< lp` and then continues completely differently. -/
theorem seqlex_of_sle_snoc' : ∀ {X V E : PairSeq} {lp q : ℕ × ℕ}, sle (X ++ [lp]) (V ++ E) →
    pairlt q lp → X.length < V.length → ∀ (S' E' : PairSeq), seqlex (X ++ q :: S') (V ++ E') := by
  intro X
  induction X with
  | nil =>
    intro V E lp q h hq hlen S' E'
    rcases V with _ | ⟨v, V'⟩
    · simp at hlen
    · rw [List.nil_append, List.cons_append]
      refine Or.inl ?_
      rw [List.nil_append, List.cons_append] at h
      rcases h with he | hs
      · have : lp = v := by simpa using congrArg List.headI he
        rw [← this]; exact hq
      · rw [seqlex_cons_cons] at hs
        rcases hs with hp | ⟨he, -⟩
        · exact pairlt_trans hq hp
        · rw [← he]; exact hq
  | cons x X' ih =>
    intro V E lp q h hq hlen S' E'
    rcases V with _ | ⟨v, V'⟩
    · simp at hlen
    · simp only [List.length_cons] at hlen
      rw [List.cons_append, List.cons_append] at h
      rw [List.cons_append, List.cons_append, seqlex_cons_cons]
      rcases h with he | hs
      · have hxy : x = v := by simpa using congrArg List.headI he
        have hrest : X' ++ [lp] = V' ++ E := by simpa using congrArg List.tail he
        exact Or.inr ⟨hxy, ih (Or.inl hrest) hq (by omega) S' E'⟩
      · rw [seqlex_cons_cons] at hs
        rcases hs with hp | ⟨rfl, hs'⟩
        · exact Or.inl hp
        · exact Or.inr ⟨rfl, ih (Or.inr hs') hq (by omega) S' E'⟩

/-- **Case B** — both marked columns lie inside `G ++ blk`, i.e. `j < p`.

`G ++ blk = M.take (M.length - 1)` is a common prefix of the host `M` (which
continues with the dropped column `lp`) and of the tower `N = G ++ copies d0 blk n`
(which continues with copy `1`), so the two marked columns and the whole of `A1`
occur *identically* in `M`, whose instance `hMon` is available.  Since `j < p`,
the prefix `Cp := X ++ (u,w) :: A1 ++ [(u+e,w)]` up to and including the deeper
marked column is a prefix of `G ++ blk`; write `G ++ blk = Cp ++ D`, so that
`M = Cp ++ (D ++ [lp])` while `B ++ A2 ++ Z = D ++ T` with `T` the rest of the
tower.  The local `key` then supplies the host's verdict for *any* admissible
splitting of the host's remainder `D ++ [lp]`, in the truncated form
`sle B' (shiftr0 e A1 ++ (u+e+e,w) :: shiftr0 e B')` — the comparison is settled
inside that prefix, `argbound_split` / `argbound_len` — and `goal_of` puts the
goal in the same form.  Three leaves:

* `|B| < |D|`: the tower's argument stops strictly inside the shared part, so it
  *is* the host's argument — the next column `Dr.headI = (A2 ++ Z).headI`
  re-opens at or below `u + e` by `h4` / `h5`.  `arg_split` supplies `A2'`, `Z'`
  and `key B` closes it.
* `|D| ≤ |B|` and `u + e < lp.1`: the host's argument is `D ++ [lp]` — this is
  ⚠ Trap 1 (29069 of the 50237 instances have `B` running past `p`, so `B` is
  *not* a sub-list of `M`).  If `B = D` the extra column is dropped by
  `sle_of_append_left` + `sle_take_of_short`; otherwise `B = D ++ q :: B2'` with
  `q = (v0+d0, w0)` the root of copy `1`, and `seqlex_of_sle_snoc'` replaces
  `lp` by `q` — legitimate because `pairlt q lp` holds in *both* `oper`
  sub-branches of `hdisj` (`(v0+d0,w0) < (v0+d0,w0+1)` ascending,
  `(v0,w0) < (v0+1,0)` exact).
* `|D| ≤ |B|` and `lp.1 ≤ u + e`: then `B` cannot reach copy `1` at all (its
  root would satisfy `u + e < q.1 ≤ lp.1`), so `B = D` and `key B` closes it
  with `lp` pushed into `A2'` or `Z'`.

Only `hMon` and `hdisj` are used; `hM`, `hRgt`, `hlp`, `hSTn`, `hIH` are not
needed in this case. -/
theorem argDomCoreOn_bad_B {M G R : PairSeq} {v0 w0 d0 n : ℕ} {lp : ℕ × ℕ}
    (hM : ST_PS M) (hMon : ArgDomCoreOn M)
    (hMeq : M = G ++ ((v0, w0) :: R) ++ [lp])
    (hRgt : ∀ x ∈ R, v0 < x.1) (hlp : v0 < lp.1)
    (hdisj : (d0 = 0 ∧ lp.2 = 0 ∧ lp.1 = v0 + 1)
      ∨ (0 < d0 ∧ lp.2 = w0 + 1 ∧ lp.1 = v0 + d0
          ∧ nextrel1 M G.length (M.length - 1)))
    (hSTn : ∀ m, 1 ≤ m → ST_PS (G ++ copies d0 ((v0, w0) :: R) m))
    (hIH : ∀ m, 1 ≤ m → m < n → ArgDomCoreOn (G ++ copies d0 ((v0, w0) :: R) m))
    (hn : 1 ≤ n)
    {X A1 B A2 Z : PairSeq} {u w e : ℕ}
    (heq : G ++ copies d0 ((v0, w0) :: R) n
      = (X ++ (u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z)
    (he : 0 < e) (h1 : ∀ x ∈ A1, u < x.1) (h2 : ∀ x ∈ B, u + e < x.1)
    (h3 : ∀ x ∈ A2, u < x.1) (h4 : A2 = [] ∨ (A2.headI).1 ≤ u + e)
    (h5 : Z = [] ∨ (Z.headI).1 ≤ u) (h6 : SpineOK A1 (u + e) w)
    (hcase : X.length + (A1.length + 1) < G.length + (R.length + 1)) :
    sle B (shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2))) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- copy `0` of the tower is `blk`, so the shared part is `P = G ++ blk`
  have hcopy : G ++ copies d0 ((v0, w0) :: R) (m + 1)
      = (G ++ ((v0, w0) :: R)) ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m) := by
    rw [copies_succ_front, List.append_assoc]
  have hNsplit : (G ++ ((v0, w0) :: R)) ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)
      = (X ++ (u, w) :: (A1 ++ [(u + e, w)])) ++ (B ++ (A2 ++ Z)) := by
    rw [← hcopy, heq]; simp [List.append_assoc]
  have hClen : (X ++ (u, w) :: (A1 ++ [(u + e, w)])).length
      ≤ (G ++ ((v0, w0) :: R)).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨D, hPD, hBAZ⟩ : ∃ D : PairSeq,
      G ++ ((v0, w0) :: R) = (X ++ (u, w) :: (A1 ++ [(u + e, w)])) ++ D
      ∧ B ++ (A2 ++ Z) = D ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m) :=
    ⟨_, split_prefix_left hNsplit hClen⟩
  -- the host in the same coordinates: it continues with the dropped column
  have hMsplit : M = (X ++ (u, w) :: (A1 ++ [(u + e, w)])) ++ (D ++ [lp]) := by
    rw [hMeq, ← List.append_assoc, hPD, List.append_assoc]
  -- ### the host's verdict, for any admissible split of `D ++ [lp]`
  have key : ∀ (B' A2' Z' : PairSeq), D ++ [lp] = B' ++ (A2' ++ Z') →
      (∀ x ∈ B', u + e < x.1) → (∀ x ∈ A2', u < x.1) →
      (A2' = [] ∨ (A2'.headI).1 ≤ u + e) → (Z' = [] ∨ (Z'.headI).1 ≤ u) →
      sle B' (shiftr0 e A1 ++ (u + e + e, w) :: shiftr0 e B') := by
    intro B' A2' Z' hsplit hB'gt hA2'gt hA2'hd hZ'hd
    have hMeq' : M = (X ++ (u, w) :: (A1 ++ (u + e, w) :: (B' ++ A2'))) ++ Z' := by
      rw [hMsplit, hsplit]; simp [List.append_assoc]
    have hcore := hMon hMeq' he h1 hB'gt hA2'gt hA2'hd hZ'hd h6
    rw [argbound_split] at hcore
    exact sle_take_of_short hcore (le_of_lt (argbound_len e u w A1 B'))
  -- ### the goal, in the same `W`-form
  have goal_of : sle B (shiftr0 e A1 ++ (u + e + e, w) :: shiftr0 e B) →
      sle B (shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2))) := by
    intro h
    rw [argbound_split]
    exact sle_append_mono h _
  rcases Nat.lt_or_ge B.length D.length with hBD | hBD
  · -- #### `B` stops strictly inside the shared part: the host's argument *is* `B`
    obtain ⟨Dr, hDr, hArest⟩ : ∃ Dr : PairSeq, D = B ++ Dr
        ∧ A2 ++ Z = Dr ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m) :=
      ⟨_, split_prefix_right hBAZ (le_of_lt hBD)⟩
    have hDrne : Dr ≠ [] := by
      intro hnil
      rw [hnil, List.append_nil] at hDr
      rw [hDr] at hBD
      omega
    have hne : A2 ++ Z ≠ [] := by
      rw [hArest]
      rcases Dr with _ | ⟨dr, Dr'⟩
      · exact absurd rfl hDrne
      · simp
    have hDrhd : (Dr.headI).1 ≤ u + e := by
      have hhd : (A2 ++ Z).headI = Dr.headI := by
        rw [hArest, headI_append_left hDrne]
      rw [← hhd]
      by_cases hA2 : A2 = []
      · subst hA2
        have hZne : Z ≠ [] := by simpa using hne
        rw [List.nil_append]
        rcases h5 with hc | hc
        · exact absurd hc hZne
        · omega
      · rw [headI_append_left hA2]
        rcases h4 with hc | hc
        · exact absurd hc hA2
        · exact hc
    obtain ⟨A2', Z', hsp, hA2'gt, hZ'hd⟩ := arg_split u (Dr ++ [lp])
    have hA2'hd : A2' = [] ∨ (A2'.headI).1 ≤ u + e := by
      by_cases hA2' : A2' = []
      · exact Or.inl hA2'
      · refine Or.inr ?_
        have hh1 : (Dr ++ [lp]).headI = A2'.headI := by
          rw [hsp, headI_append_left hA2']
        rw [← hh1, headI_append_left hDrne]
        exact hDrhd
    refine goal_of (key B A2' Z' ?_ h2 hA2'gt hA2'hd hZ'hd)
    rw [hDr, List.append_assoc, ← hsp]
  · -- #### `B` reaches the end of the shared part
    obtain ⟨B2, hB2, hT⟩ : ∃ B2 : PairSeq, B = D ++ B2
        ∧ shiftr0 d0 (copies d0 ((v0, w0) :: R) m) = B2 ++ (A2 ++ Z) :=
      ⟨_, split_prefix_left hBAZ hBD⟩
    have hDgt : ∀ x ∈ D, u + e < x.1 := fun x hx =>
      h2 x (by rw [hB2]; exact List.mem_append_left _ hx)
    -- the head of the next copy is the shifted block root
    have hhead : ∀ (q : ℕ × ℕ) (B2' : PairSeq), B2 = q :: B2' → q = (v0 + d0, w0) := by
      intro q B2' hB2'
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
        rcases m with _ | m'
        · exfalso
          rw [copies_zero, shiftr0_nil, hB2'] at hT
          simp at hT
        · exact ⟨m', rfl⟩
      rw [copies_succ_front, List.cons_append, shiftr0_cons, hB2', List.cons_append] at hT
      exact ((List.cons_eq_cons.1 hT).1).symm
    have hqle : ∀ (q : ℕ × ℕ) (B2' : PairSeq), B2 = q :: B2' → q.1 ≤ lp.1 := by
      intro q B2' hB2'
      have hq := hhead q B2' hB2'
      rcases hdisj with ⟨hd0, -, hlp1⟩ | ⟨hd0, -, hlp1, -⟩
      · rw [hq, hlp1, hd0]; simp
      · rw [hq, hlp1]
    have hqlt : ∀ (q : ℕ × ℕ) (B2' : PairSeq), B2 = q :: B2' → pairlt q lp := by
      intro q B2' hB2'
      have hq := hhead q B2' hB2'
      rcases hdisj with ⟨hd0, hlp2, hlp1⟩ | ⟨hd0, hlp2, hlp1, -⟩
      · refine Or.inl ?_
        rw [hq, hlp1, hd0]; simp
      · refine Or.inr ⟨?_, ?_⟩
        · rw [hq, hlp1]
        · rw [hq, hlp2]; simp
    by_cases hlpg : u + e < lp.1
    · -- the host's argument is `D ++ [lp]`
      have hB'gt : ∀ x ∈ D ++ [lp], u + e < x.1 := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hDgt x hx
        · rw [List.mem_singleton.1 hx]; exact hlpg
      have hkey := key (D ++ [lp]) [] [] (by simp) hB'gt (by simp) (Or.inl rfl) (Or.inl rfl)
      rw [shiftr0_append] at hkey
      have hrw : shiftr0 e A1 ++ (u + e + e, w) :: (shiftr0 e D ++ shiftr0 e [lp])
          = (shiftr0 e A1 ++ (u + e + e, w) :: shiftr0 e D) ++ shiftr0 e [lp] := by
        simp [List.append_assoc]
      rw [hrw] at hkey
      rcases hB2e : B2 with _ | ⟨q, B2'⟩
      · -- `B` is exactly the shared part
        rw [hB2e, List.append_nil] at hB2
        subst hB2
        refine goal_of ?_
        have hle : B.length ≤ (shiftr0 e A1 ++ (u + e + e, w) :: shiftr0 e B).length := by
          simp only [List.length_append, List.length_cons, shiftr0_length]
          omega
        exact sle_take_of_short (sle_of_append_left hkey) hle
      · -- `B` runs into the next copy: replace `lp` by the copy root
        refine goal_of (Or.inr ?_)
        have hlen : D.length < (shiftr0 e A1 ++ (u + e + e, w) :: shiftr0 e D).length := by
          simp only [List.length_append, List.length_cons, shiftr0_length]
          omega
        have hres := seqlex_of_sle_snoc' hkey (hqlt q B2' hB2e) hlen B2'
          ((q.1 + e, q.2) :: shiftr0 e B2')
        have hgB : B = D ++ q :: B2' := by rw [hB2, hB2e]
        have hgb : shiftr0 e A1 ++ (u + e + e, w) :: shiftr0 e (D ++ q :: B2')
            = (shiftr0 e A1 ++ (u + e + e, w) :: shiftr0 e D)
              ++ (q.1 + e, q.2) :: shiftr0 e B2' := by
          rw [shiftr0_append, shiftr0_cons]
          simp [List.append_assoc]
        rw [hgB, hgb]
        exact hres
    · -- the dropped column is at or below the deeper marked level: `B` cannot
      -- reach into the next copy, so `B` is exactly the shared part
      have hB2nil : B2 = [] := by
        rcases hB2e : B2 with _ | ⟨q, B2'⟩
        · rfl
        · exfalso
          have hqmem : q ∈ B := by rw [hB2, hB2e]; exact List.mem_append_right _ (by simp)
          have := h2 q hqmem
          have := hqle q B2' hB2e
          omega
      rw [hB2nil, List.append_nil] at hB2
      subst hB2
      by_cases hu : u < lp.1
      · refine goal_of (key B [lp] [] (by simp) h2 ?_ (Or.inr ?_) (Or.inl rfl))
        · intro x hx; rw [List.mem_singleton.1 hx]; exact hu
        · simp; omega
      · refine goal_of (key B [] [lp] (by simp) h2 (by simp) (Or.inl rfl) (Or.inr ?_))
        · simp; omega

/-! ### Tooling for case A2 (the cross case)

The cross case is closed by a *one-period descent*: an instance whose deeper
column sits at least one full block-length above the shallower one is the exact
`d0`-shift of an instance of the **smaller** tower `G ++ copies d0 blk (n-1)`,
which the strong induction hypothesis `hIH` settles.  The lemmas below supply
the list algebra for that descent. -/

/-- `shiftr0` composes. -/
theorem shiftr0_add (a b : ℕ) (X : PairSeq) :
    shiftr0 (a + b) X = shiftr0 a (shiftr0 b X) := by
  unfold shiftr0
  rw [List.map_map]
  refine congrArg (fun f => List.map f X) ?_
  funext p
  simp only [Function.comp_apply, Prod.mk.injEq, and_true]
  omega

/-- A prefix is `sle`-below. -/
theorem sle_of_prefix {X Y : PairSeq} (h : X <+: Y) : sle X Y := by
  obtain ⟨t, rfl⟩ := h
  rcases t with _ | ⟨a, t'⟩
  · exact Or.inl (by simp)
  · exact Or.inr (seqlex_prefix (by simp) X)

/-- A uniform row-0 shift preserves the prefix relation. -/
theorem shiftr0_prefix (d : ℕ) {X Y : PairSeq} (h : X <+: Y) :
    shiftr0 d X <+: shiftr0 d Y := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨shiftr0 d t, (shiftr0_append d X t).symm⟩

/-- Prefixes are stable under a common left factor. -/
theorem prefix_append_left {X Y : PairSeq} (P : PairSeq) (h : X <+: Y) :
    P ++ X <+: P ++ Y := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t, by simp [List.append_assoc]⟩

/-- Length of a copy tower. -/
theorem copies_length (d : ℕ) (blk : PairSeq) (n : ℕ) :
    (copies d blk n).length = n * blk.length := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [copies_succ_back, List.length_append, ih, shiftr0_length, Nat.succ_mul]

/-- Existential form of `split_prefix_left`. -/
theorem split_append_left {C D E F : PairSeq} (h : C ++ D = E ++ F)
    (hle : E.length ≤ C.length) : ∃ K, C = E ++ K ∧ F = K ++ D :=
  ⟨C.drop E.length, split_prefix_left h hle⟩

/-- Prefixes are stable under a common left factor followed by a common column. -/
theorem prefix_cons_append {P Q : PairSeq} (A : PairSeq) (c : ℕ × ℕ) (h : P <+: Q) :
    A ++ c :: P <+: A ++ c :: Q := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t, by simp [List.append_assoc]⟩

/-- **Sharp form of `spineOK_of_nextrel1`.**  The `nextrel1` minimality clause
actually forces the *strict* bound `w0 < x.2` on every right-visible column `x`
of `R` below level `v0+d0` — the dropped column carries row-1 `w0 + 1`, and a
row-0 ancestor of it cannot carry less.  Case A2 needs this sharpened form to
refute the configuration where the shallower marked column sits strictly inside
the block. -/
theorem spineOK_of_nextrel1_strict {G R : PairSeq} {v0 w0 d0 : ℕ}
    (hnr : nextrel1 ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) G.length
      (G ++ ((v0, w0) :: R)).length) :
    SpineOK R (v0 + d0) (w0 + 1) := by
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
  have hgx : M.getD A.length (0, 0) = x := by
    have h := getD_append_right' A (x :: (V ++ [lp])) 0
    rw [Nat.add_zero] at h
    rw [hMeq]; exact h
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
  have hxle0 : le0 M A.length (G ++ ((v0, w0) :: R)).length :=
    le0_through_pivot hle0 (by omega) (by omega) hpiv
  have hlast : entry M 1 (G ++ ((v0, w0) :: R)).length = w0 + 1 := by
    have h := getD_append_right' (G ++ ((v0, w0) :: R)) [lp] 0
    rw [Nat.add_zero] at h
    rw [entry_one, hMdef, h, List.getD_cons_zero, hlp]
  have := hmin A.length ⟨by omega, hxle0⟩
  rw [hlast, entry_one, hgx] at this
  omega

/-- **Case A2** — the cross case: the shallower marked column is inside
`G ++ blk` and the deeper one is in a later copy, `i < p ≤ j`.  This case is
not vacuous.

**The one-period descent.**  Write `L = |blk| = R.length + 1`.  For `n = 1` the
case is empty (the tower stops at `p`, but `j ≥ p`), so `n ≥ 2` and the smaller
tower `N' = G ++ copies d0 blk (n-1)` is available through `hIH`.  Cutting the
instance at `p` gives `G ++ blk = X ++ (u,w) :: C`, `A1 = C ++ D` and
`shiftr0 d0 (copies d0 blk (n-1)) = D ++ (u+e,w) :: (B ++ A2 ++ Z)`; un-shifting
the latter exhibits `N'` cut at the column `j - L`, whose row-1 value is again
`w`.  Three cases, comparing `i` with `j - L = G.length + |D|`:

* `i < j - L` — the instance **descends**: `X`, `(u,w)`, `A1'`, `(u+e-d0,w)`,
  `shiftl0 d0 B` is an instance of `N'` (its trailing `A2`/`Z` produced by
  `takeWhile`/`dropWhile` at level `u`), `hIH` settles it, and the conclusion is
  transported back up by `shiftr0 d0`: `B = shiftr0 d0 (shiftl0 d0 B)` because
  every column of `B` sits at row-0 `> u+e ≥ d0`, and the smaller bound is a
  *prefix* of the bigger one.  The one real point is `SpineOK` for the descended
  gap: a right-visible column `x` of `A1'` either sits in `G` — where the head
  of the tower forces `x.1 < v0`, so every column of `blk ++ D` is above `x` and
  `x` is right-visible in `A1` too — or sits in the un-shifted window, where its
  `d0`-shifted twin one period up is right-visible in `A1` and carries the same
  row-1 value.  Either way `h6` applies.
* `i = j - L` — then `e = d0` and `shiftl0 d0 B` is a prefix of
  `A1 ++ (u+e,w) :: (B ++ A2)`, so the goal is a pure prefix comparison; `hIH`
  is not needed.
* `i > j - L` — **impossible**.  The shallower column then lies strictly inside
  the block, hence is a right-visible column of `R` below level `v0+d0`, and the
  sharpened minimality clause `spineOK_of_nextrel1_strict` (from the `nextrel1`
  clause of `hdisj` — load-bearing) gives `w0 < w`; while the copy root sitting
  inside `A1` (or being the deeper column itself) gives `w ≤ w0` by `h6`.

Neither `hMon` nor `hSTn` is needed: the cross case is settled by the copy
tower's own periodicity plus the induction hypothesis on the copy count.

Model check (`tools/probe_badbranch_cases2.py` closures `(4,(1,2,3),10,6)` and
`(5,(1,2,3,4,5),11,7)`): of the 26290 cross instances, 24308 descend and 1982
are the base case; **no** instance falls in the refuted third case, and the
descended `SpineOK` holds in all 24308. -/
theorem argDomCoreOn_bad_A2 {M G R : PairSeq} {v0 w0 d0 n : ℕ} {lp : ℕ × ℕ}
    (hM : ST_PS M) (hMon : ArgDomCoreOn M)
    (hMeq : M = G ++ ((v0, w0) :: R) ++ [lp])
    (hRgt : ∀ x ∈ R, v0 < x.1) (hlp : v0 < lp.1)
    (hdisj : (d0 = 0 ∧ lp.2 = 0 ∧ lp.1 = v0 + 1)
      ∨ (0 < d0 ∧ lp.2 = w0 + 1 ∧ lp.1 = v0 + d0
          ∧ nextrel1 M G.length (M.length - 1)))
    (hSTn : ∀ m, 1 ≤ m → ST_PS (G ++ copies d0 ((v0, w0) :: R) m))
    (hIH : ∀ m, 1 ≤ m → m < n → ArgDomCoreOn (G ++ copies d0 ((v0, w0) :: R) m))
    (hn : 1 ≤ n)
    {X A1 B A2 Z : PairSeq} {u w e : ℕ}
    (heq : G ++ copies d0 ((v0, w0) :: R) n
      = (X ++ (u, w) :: (A1 ++ (u + e, w) :: (B ++ A2))) ++ Z)
    (he : 0 < e) (h1 : ∀ x ∈ A1, u < x.1) (h2 : ∀ x ∈ B, u + e < x.1)
    (h3 : ∀ x ∈ A2, u < x.1) (h4 : A2 = [] ∨ (A2.headI).1 ≤ u + e)
    (h5 : Z = [] ∨ (Z.headI).1 ≤ u) (h6 : SpineOK A1 (u + e) w)
    (hcaseL : X.length < G.length + (R.length + 1))
    (hcaseR : G.length + (R.length + 1) ≤ X.length + (A1.length + 1)) :
    sle B (shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2))) := by
  classical
  -- ## Step 0 — the copy count is at least `2`
  -- with `n = 1` the tower stops exactly at `p`, while the case puts `j ≥ p`.
  have hpos := argdom_pos heq
  have hlenN : (G ++ copies d0 ((v0, w0) :: R) n).length
      = G.length + n * (R.length + 1) := by
    rw [List.length_append, copies_length]
    simp
  have hn2 : 2 ≤ n := by
    by_contra hc
    have hn1 : n = 1 := by omega
    have h := hpos.2.2
    rw [hlenN, hn1] at h
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  -- ## Step 1 — peel copy `0`, and cut the instance at the boundary `p`
  have hexp : G ++ copies d0 ((v0, w0) :: R) (m + 1)
      = (G ++ ((v0, w0) :: R)) ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m) := by
    rw [copies_succ_front, ← List.append_assoc]
  have heq2 : (G ++ ((v0, w0) :: R)) ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m)
      = (X ++ [(u, w)]) ++ (A1 ++ (u + e, w) :: (B ++ (A2 ++ Z))) := by
    rw [← hexp, heq]; simp [List.append_assoc]
  obtain ⟨C, hC1, hC2⟩ := split_append_left heq2
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hClen : C.length = G.length + (R.length + 1) - (X.length + 1) := by
    have h := congrArg List.length hC1
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  obtain ⟨D, hD1, hD2⟩ := split_append_left hC2 (by omega)
  have hA1len : A1.length = C.length + D.length := by
    have h := congrArg List.length hD1
    simpa using h
  have hDlen : D.length = A1.length - C.length := by omega
  -- every column of the shifted tail sits at row-0 `≥ d0`
  have hmem_ge : ∀ x ∈ shiftr0 d0 (copies d0 ((v0, w0) :: R) m), d0 ≤ x.1 := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := mem_shiftr0.1 hx
    simp
  have hd0le : d0 ≤ u + e := by
    refine hmem_ge (u + e, w) ?_
    rw [hD2]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  -- ## Step 2 — un-shift: the smaller tower, cut at the same column
  have hSeq : copies d0 ((v0, w0) :: R) m
      = shiftl0 d0 D ++ (u + e - d0, w) ::
          (shiftl0 d0 B ++ (shiftl0 d0 A2 ++ shiftl0 d0 Z)) := by
    have h := congrArg (shiftl0 d0) hD2
    rw [shiftl0_shiftr0] at h
    rw [h, shiftl0_append, shiftl0_cons, shiftl0_append, shiftl0_append]
  -- ## Step 3 — where does the shallower column sit relative to `j - L`?
  rcases Nat.lt_trichotomy X.length (G.length + D.length) with hcase | hcase | hcase
  · -- (a) `i < j - L`: one-period descent onto the smaller tower
    obtain ⟨m'', hm''⟩ : ∃ m'', m = m'' + 1 := ⟨m - 1, by omega⟩
    -- the shallower column is still inside the *smaller* tower
    have hpre_blk : ((v0, w0) :: R) <+: copies d0 ((v0, w0) :: R) m := by
      rw [hm'', copies_succ_front]
      exact List.prefix_append _ _
    have hpre_SD : shiftl0 d0 D <+: copies d0 ((v0, w0) :: R) m := ⟨_, hSeq.symm⟩
    have hSDlen : (shiftl0 d0 D).length = D.length := by simp [shiftl0]
    have hp1 : X ++ [(u, w)] <+: G ++ shiftl0 d0 D := by
      refine List.prefix_of_prefix_length_le
        (List.IsPrefix.trans ⟨C, hC1.symm⟩ (prefix_append_left G hpre_blk))
        (prefix_append_left G hpre_SD) ?_
      simp only [List.length_append, List.length_cons, List.length_nil, hSDlen]
      omega
    obtain ⟨A1', hA1'⟩ := hp1
    have hA1'len : A1'.length = G.length + D.length - (X.length + 1) := by
      have h := congrArg List.length hA1'
      simp only [List.length_append, List.length_cons, List.length_nil, hSDlen] at h
      omega
    -- the smaller tower, in instance shape
    have hNm : G ++ copies d0 ((v0, w0) :: R) m
        = ((X ++ [(u, w)]) ++ A1') ++ (u + e - d0, w) ::
            (shiftl0 d0 B ++ (shiftl0 d0 A2 ++ shiftl0 d0 Z)) := by
      rw [hSeq, ← List.append_assoc, ← hA1']
    have hback : G ++ copies d0 ((v0, w0) :: R) (m + 1)
        = (G ++ copies d0 ((v0, w0) :: R) m) ++ shiftr0 (m * d0) ((v0, w0) :: R) := by
      rw [copies_succ_back, ← List.append_assoc]
    have hbig : (X ++ [(u, w)]) ++ (A1 ++ (u + e, w) :: (B ++ (A2 ++ Z)))
        = (X ++ [(u, w)]) ++ (A1' ++ (u + e - d0, w) ::
            ((shiftl0 d0 B ++ (shiftl0 d0 A2 ++ shiftl0 d0 Z))
              ++ shiftr0 (m * d0) ((v0, w0) :: R))) := by
      rw [← heq2, ← hexp, hback, hNm]
      simp [List.append_assoc]
    have hcancel := List.append_cancel_left hbig
    obtain ⟨Wnd, hW1, hW2⟩ := split_append_left hcancel (by omega)
    rcases Wnd with _ | ⟨wnd0, Wtl⟩
    · -- the window has length `R.length + 1 ≥ 1`
      have h := congrArg List.length hW1
      simp only [List.length_append, List.length_nil] at h
      omega
    · have hwnd0 : wnd0 = (u + e - d0, w) := by
        have h := hW2
        rw [List.cons_append] at h
        exact ((List.cons.injEq _ _ _ _ ▸ h).1).symm
      have hWtl : (shiftl0 d0 B ++ (shiftl0 d0 A2 ++ shiftl0 d0 Z))
            ++ shiftr0 (m * d0) ((v0, w0) :: R)
          = Wtl ++ (u + e, w) :: (B ++ (A2 ++ Z)) := by
        have h := hW2
        rw [List.cons_append] at h
        exact (List.cons.injEq _ _ _ _ ▸ h).2
      have hA1dec : A1 = A1' ++ (u + e - d0, w) :: Wtl := by rw [hW1, hwnd0]
      -- the descended column is still above `u`, so the shift `e - d0` is positive
      have hde : d0 < e := by
        have hm : (u + e - d0, w) ∈ A1 := by
          rw [hA1dec]
          exact List.mem_append_right _ (List.mem_cons_self ..)
        have := h1 _ hm
        simp only [] at this
        omega
      have hued : u + e - d0 = u + (e - d0) := by omega
      -- the trailing material of the smaller instance, packaged abstractly
      obtain ⟨A2', Z2, hA2Z, hA2'pre, hA2'gt, hA2'hd, hZ2hd⟩ :
          ∃ A2' Z2, A2' ++ Z2 = shiftl0 d0 A2 ++ shiftl0 d0 Z ∧
            A2' <+: shiftl0 d0 A2 ∧ (∀ x ∈ A2', u < x.1) ∧
            (A2' = [] ∨ (A2'.headI).1 ≤ u + (e - d0)) ∧ (Z2 = [] ∨ (Z2.headI).1 ≤ u) := by
        refine ⟨(shiftl0 d0 A2).takeWhile (fun p => u < p.1),
          (shiftl0 d0 A2).dropWhile (fun p => u < p.1) ++ shiftl0 d0 Z, ?_,
          List.takeWhile_prefix _, ?_, ?_, ?_⟩
        · rw [← List.append_assoc, List.takeWhile_append_dropWhile]
        · intro x hx
          have := List.mem_takeWhile_imp hx
          simpa using this
        · rcases hA2e : A2 with _ | ⟨a2, A2r⟩
          · exact Or.inl (by simp [shiftl0])
          · have hh4 : (A2.headI).1 ≤ u + e := by
              rcases h4 with hc | hc
              · exact absurd hc (by rw [hA2e]; simp)
              · exact hc
            rw [hA2e] at hh4
            simp only [List.headI] at hh4
            rw [shiftl0_cons]
            by_cases hp : u < a2.1 - d0
            · refine Or.inr ?_
              rw [List.takeWhile_cons_of_pos (by simpa using hp)]
              simp only [List.headI]
              omega
            · exact Or.inl (by rw [List.takeWhile_cons_of_neg (by simpa using hp)])
        · rcases hDW : (shiftl0 d0 A2).dropWhile (fun p => u < p.1) with _ | ⟨z, DW'⟩
          · rw [hDW, List.nil_append]
            rcases hZe : Z with _ | ⟨z0, Z'⟩
            · exact Or.inl (by simp [shiftl0])
            · refine Or.inr ?_
              have hz : (Z.headI).1 ≤ u := by
                rcases h5 with hc | hc
                · exact absurd hc (by rw [hZe]; simp)
                · exact hc
              rw [hZe] at hz
              simp only [List.headI] at hz
              rw [shiftl0_cons]
              simp only [List.headI]
              omega
          · refine Or.inr ?_
            have hh := List.head?_dropWhile_not (fun p : ℕ × ℕ => decide (u < p.1)) (shiftl0 d0 A2)
            rw [hDW] at hh
            simp only [List.head?_cons] at hh
            have hnz : ¬ (u < z.1) := by simpa using hh
            rw [hDW, List.cons_append]
            simp only [List.headI]
            omega
      -- the instance of the smaller tower
      have heq' : G ++ copies d0 ((v0, w0) :: R) m
          = (X ++ (u, w) :: (A1' ++ (u + (e - d0), w) :: (shiftl0 d0 B ++ A2'))) ++ Z2 := by
        rw [hNm, ← hA2Z, hued]
        simp [List.append_assoc]
      have hcore := hIH m hm1 (by omega) heq' (by omega)
        (fun x hx => h1 x (by rw [hA1dec]; exact List.mem_append_left _ hx))
        (by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := mem_shiftl0.1 hx
          have := h2 y hy
          simp only []
          omega)
        hA2'gt hA2'hd hZ2hd
        (by
          -- `SpineOK` for the descended gap: a right-visible column of `A1'`
          -- either is right-visible in `A1` as well (when it sits in `G`, where
          -- it must be below `v0`, hence below the whole tower), or its
          -- `d0`-shifted twin one period up is — and the twin carries the same
          -- row-1 value.
          intro U V x hdec hxlt hV
          have hGSD : ((X ++ [(u, w)]) ++ U) ++ x :: V = G ++ shiftl0 d0 D := by
            rw [← hA1', hdec]; simp [List.append_assoc]
          have hDge : ∀ y ∈ D, d0 ≤ y.1 := by
            intro y hy
            refine hmem_ge y ?_
            rw [hD2]
            exact List.mem_append_left _ hy
          have hDshift : shiftr0 d0 (shiftl0 d0 D) = D := shiftr0_shiftl0 hDge
          rcases Nat.lt_or_ge ((X ++ [(u, w)]) ++ U).length G.length with hlt | hge
          · -- `x` sits inside `G`, hence strictly below the block base `v0`
            have hle2 : (((X ++ [(u, w)]) ++ U) ++ [x]).length ≤ G.length := by
              simp only [List.length_append, List.length_cons, List.length_nil]
              simp only [List.length_append, List.length_cons, List.length_nil] at hlt
              omega
            have hGSD' : G ++ shiftl0 d0 D = (((X ++ [(u, w)]) ++ U) ++ [x]) ++ V := by
              rw [← hGSD]; simp [List.append_assoc]
            obtain ⟨V3, hV31, hV32⟩ := split_append_left hGSD' hle2
            have hCdec : C = (U ++ [x]) ++ (V3 ++ ((v0, w0) :: R)) := by
              have hh : (X ++ [(u, w)]) ++ ((U ++ [x]) ++ (V3 ++ ((v0, w0) :: R)))
                  = (X ++ [(u, w)]) ++ C := by
                rw [← hC1, hV31]; simp [List.append_assoc]
              exact (List.append_cancel_left hh).symm
            have hhead : (copies d0 ((v0, w0) :: R) m).headI = ((v0, w0) :: R).headI :=
              copies_headI (by simp) hm1
            simp only [List.headI] at hhead
            have hxv0 : x.1 < v0 := by
              rcases hSD : shiftl0 d0 D with _ | ⟨sd0, SD'⟩
              · rw [hSeq, hSD, List.nil_append] at hhead
                simp only [List.headI] at hhead
                have hfst := congrArg Prod.fst hhead
                simp only [] at hfst
                omega
              · have hmemV : sd0 ∈ V := by
                  rw [hV32, hSD]
                  exact List.mem_append_right _ (List.mem_cons_self ..)
                have hsd0 : sd0 = (v0, w0) := by
                  rw [hSeq, hSD] at hhead
                  simpa using hhead
                have hlt2 := hV sd0 hmemV
                rw [hsd0] at hlt2
                simpa using hlt2
            refine h6 U ((V3 ++ ((v0, w0) :: R)) ++ D) x ?_ (by omega) ?_
            · rw [hD1, hCdec]; simp [List.append_assoc]
            · intro y hy
              rcases List.mem_append.1 hy with hy | hy
              · rcases List.mem_append.1 hy with hy | hy
                · exact hV y (by rw [hV32]; exact List.mem_append_left _ hy)
                · rcases List.mem_cons.1 hy with rfl | hy
                  · exact hxv0
                  · have := hRgt y hy; omega
              · have hyD : y ∈ shiftr0 d0 (copies d0 ((v0, w0) :: R) m) := by
                  rw [hD2]; exact List.mem_append_left _ hy
                obtain ⟨z, hz, rfl⟩ := mem_shiftr0.1 hyD
                have hzv : v0 ≤ z.1 := copies_v0_le (fun q hq => (hRgt q hq).le) d0 m z hz
                simp only []
                omega
          · -- `x` sits inside the un-shifted window: use its twin one period up
            obtain ⟨U2, hU21, hU22⟩ := split_append_left hGSD hge
            have hDdec : D = shiftr0 d0 U2 ++ (x.1 + d0, x.2) :: shiftr0 d0 V := by
              rw [← hDshift, hU22, shiftr0_append, shiftr0_cons]
            refine h6 (C ++ shiftr0 d0 U2) (shiftr0 d0 V) (x.1 + d0, x.2) ?_ ?_ ?_
            · rw [hD1, hDdec]; simp [List.append_assoc]
            · simp only []
              omega
            · intro y hy
              obtain ⟨z, hz, rfl⟩ := mem_shiftr0.1 hy
              have := hV z hz
              simp only []
              omega)
      -- transport the conclusion back up
      have hpreB : shiftl0 d0 B ++ A2' <+: Wtl ++ (u + e, w) :: (B ++ A2) := by
        refine List.prefix_of_prefix_length_le
          (l₃ := Wtl ++ (u + e, w) :: (B ++ (A2 ++ Z))) ?_ ?_ ?_
        · rw [← hWtl]
          exact ⟨Z2 ++ shiftr0 (m * d0) ((v0, w0) :: R), by
            rw [← hA2Z]; simp [List.append_assoc]⟩
        · exact ⟨Z, by simp [List.append_assoc]⟩
        · have hlen := hA2'pre.length_le
          simp only [shiftl0, List.length_map] at hlen
          simp only [List.length_append, List.length_cons, shiftl0, List.length_map]
          omega
      have hpre_final : A1' ++ (u + (e - d0), w) :: (shiftl0 d0 B ++ A2')
          <+: A1 ++ (u + e, w) :: (B ++ A2) := by
        rw [hA1dec, hued]
        simp only [List.append_assoc, List.cons_append]
        exact prefix_cons_append _ _ hpreB
      obtain ⟨TT, hTT⟩ := shiftr0_prefix (e - d0) hpre_final
      have hstep : sle (shiftl0 d0 B) (shiftr0 (e - d0) (A1 ++ (u + e, w) :: (B ++ A2))) := by
        rw [← hTT]
        exact sle_append_mono hcore TT
      have hBmem : ∀ x ∈ B, d0 ≤ x.1 := by
        intro x hx
        have := h2 x hx
        omega
      have hfin := (sle_shiftr0 d0).2 hstep
      rw [shiftr0_shiftl0 hBmem, ← shiftr0_add, show d0 + (e - d0) = e by omega] at hfin
      exact hfin
  · -- (b) `i = j - L`: the deeper column is the exact `d0`-shift of the shallower
    -- the smaller tower, cut at the shallower column
    have hNm : G ++ copies d0 ((v0, w0) :: R) m
        = (G ++ shiftl0 d0 D) ++ (u + e - d0, w) ::
            (shiftl0 d0 B ++ (shiftl0 d0 A2 ++ shiftl0 d0 Z)) := by
      rw [hSeq, ← List.append_assoc]
    have hback : G ++ copies d0 ((v0, w0) :: R) (m + 1)
        = (G ++ copies d0 ((v0, w0) :: R) m) ++ shiftr0 (m * d0) ((v0, w0) :: R) := by
      rw [copies_succ_back, ← List.append_assoc]
    have hkey : (X ++ [(u, w)]) ++ (A1 ++ (u + e, w) :: (B ++ (A2 ++ Z)))
        = (G ++ shiftl0 d0 D) ++ ((u + e - d0, w) ::
            ((shiftl0 d0 B ++ (shiftl0 d0 A2 ++ shiftl0 d0 Z))
              ++ shiftr0 (m * d0) ((v0, w0) :: R))) := by
      rw [← heq2, ← hexp, hback, hNm]
      simp [List.append_assoc]
    obtain ⟨K, hK1, hK2⟩ := split_append_left hkey (by
      simp only [List.length_append, List.length_cons, List.length_nil, shiftl0,
        List.length_map]
      omega)
    have hKlen : K.length = 1 := by
      have h := congrArg List.length hK1
      simp only [List.length_append, List.length_cons, List.length_nil, shiftl0,
        List.length_map] at h
      omega
    rcases K with _ | ⟨k, K'⟩
    · simp at hKlen
    · have hK'nil : K' = [] := by
        have : K'.length = 0 := by simpa using hKlen
        exact List.eq_nil_of_length_eq_zero this
      subst hK'nil
      -- the two readings of the column at position `i`
      have hXeq : X = G ++ shiftl0 d0 D ∧ [(u, w)] = [k] := by
        refine List.append_inj hK1 ?_
        simp only [shiftl0, List.length_append, List.length_map]
        omega
      have hk1 : k = (u, w) := by
        have := hXeq.2
        simp at this
        exact this.symm
      have hk2 : k = (u + e - d0, w) := by
        have h := hK2
        simp only [List.singleton_append] at h
        exact (List.cons.injEq _ _ _ _ ▸ h).1.symm
      have hed : e = d0 := by
        rw [hk1] at hk2
        have := congrArg Prod.fst hk2
        simp only [] at this
        omega
      -- what follows the shallower column in the smaller tower
      have hRW : (shiftl0 d0 B ++ (shiftl0 d0 A2 ++ shiftl0 d0 Z))
            ++ shiftr0 (m * d0) ((v0, w0) :: R)
          = A1 ++ (u + e, w) :: (B ++ (A2 ++ Z)) := by
        have h := hK2
        simp only [List.singleton_append] at h
        exact (List.cons.injEq _ _ _ _ ▸ h).2
      have hpre1 : shiftl0 d0 B <+: A1 ++ (u + e, w) :: (B ++ (A2 ++ Z)) := by
        refine ⟨(shiftl0 d0 A2 ++ shiftl0 d0 Z) ++ shiftr0 (m * d0) ((v0, w0) :: R), ?_⟩
        rw [← hRW]
        simp [List.append_assoc]
      have hpre2 : A1 ++ (u + e, w) :: (B ++ A2) <+: A1 ++ (u + e, w) :: (B ++ (A2 ++ Z)) :=
        ⟨Z, by simp [List.append_assoc]⟩
      have hpre3 : shiftl0 d0 B <+: A1 ++ (u + e, w) :: (B ++ A2) := by
        refine List.prefix_of_prefix_length_le hpre1 hpre2 ?_
        simp only [shiftl0, List.length_map, List.length_append, List.length_cons]
        omega
      have hBmem : ∀ x ∈ B, d0 ≤ x.1 := by
        intro x hx
        have := h2 x hx
        omega
      have hBshift : shiftr0 e (shiftl0 d0 B) = B := by
        rw [hed]; exact shiftr0_shiftl0 hBmem
      have hfin : B <+: shiftr0 e (A1 ++ (u + e, w) :: (B ++ A2)) := by
        have h := shiftr0_prefix e hpre3
        rwa [hBshift] at h
      exact sle_of_prefix hfin
  · -- (c) `i > j - L`: refuted by the `nextrel1` minimality clause
    -- Here the shallower column lies strictly inside the block, so it is a
    -- right-visible column of `R` below level `v0+d0`; the sharpened minimality
    -- clause forces `w0 < w`, while the copy root inside `A1` forces `w ≤ w0`.
    exfalso
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    -- (1) `(u,w)` sits strictly inside `R`
    obtain ⟨K, hK1, hK2⟩ := split_append_left hC1.symm (by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    rcases K with _ | ⟨k0, K1⟩
    · have h := congrArg List.length hK1
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      omega
    · have hRK1 : R = K1 ++ C := by
        have h := hK2
        rw [List.cons_append] at h
        exact (List.cons.injEq _ _ _ _ ▸ h).2
      have hK1' : X ++ [(u, w)] = (G ++ [k0]) ++ K1 := by rw [hK1]; simp
      obtain ⟨T, hT1, hT2⟩ := split_append_left hK1' (by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      have hRdec : R = T ++ (u, w) :: C := by rw [hRK1, hT2]; simp
      have huv0 : v0 < u := by
        refine hRgt (u, w) ?_
        rw [hRdec]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      -- (2) the copy-1 root: it pins `u < v0 + d0` and `w ≤ w0`
      have hSC : shiftr0 d0 (copies d0 ((v0, w0) :: R) (m' + 1))
          = (v0 + d0, w0) :: shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m')) := by
        rw [copies_succ_cons, shiftr0_cons]
      have hDcase : u < v0 + d0 ∧ w ≤ w0 := by
        rcases hD : D with _ | ⟨d1, D'⟩
        · have h := hD2
          rw [hD, List.nil_append, hSC] at h
          have hh : ((v0 + d0, w0) : ℕ × ℕ) = (u + e, w) := (List.cons.injEq _ _ _ _ ▸ h).1
          have h1' := congrArg Prod.fst hh
          have h2' := congrArg Prod.snd hh
          simp only [] at h1' h2'
          omega
        · have h := hD2
          rw [hD, hSC, List.cons_append] at h
          have hd1 : d1 = (v0 + d0, w0) := ((List.cons.injEq _ _ _ _ ▸ h).1).symm
          have hrest : shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m'))
              = D' ++ (u + e, w) :: (B ++ (A2 ++ Z)) := (List.cons.injEq _ _ _ _ ▸ h).2
          have hA1dec : A1 = C ++ (v0 + d0, w0) :: D' := by rw [hD1, hD, hd1]
          have huv : u < v0 + d0 := by
            refine h1 (v0 + d0, w0) ?_
            rw [hA1dec]
            exact List.mem_append_right _ (List.mem_cons_self ..)
          have hd0pos : 0 < d0 := by omega
          have htl := copies_tl_gt (w0 := w0) hRgt hd0pos (n := m' + 1) (by omega)
          have htl' : ∀ x ∈ shiftr0 d0 (R ++ shiftr0 d0 (copies d0 ((v0, w0) :: R) m')),
              v0 + d0 < x.1 := by
            intro x hx
            obtain ⟨z, hz, rfl⟩ := mem_shiftr0.1 hx
            have := htl z (by simpa using hz)
            simp only []
            omega
          refine ⟨huv, h6 C D' (v0 + d0, w0) hA1dec ?_ ?_⟩
          · refine htl' (u + e, w) ?_
            rw [hrest]
            exact List.mem_append_right _ (List.mem_cons_self ..)
          · intro y hy
            refine htl' y ?_
            rw [hrest]
            exact List.mem_append_left _ hy
      obtain ⟨huv, hww0⟩ := hDcase
      have hd0pos : 0 < d0 := by omega
      -- (3) the sharpened `nextrel1` minimality clause
      rcases hdisj with ⟨hd0z, -, -⟩ | ⟨-, hlp2, hlp1, hnr⟩
      · omega
      · have hlpeq : lp = (v0 + d0, w0 + 1) := Prod.ext hlp1 hlp2
        have hnr' : nextrel1 ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) G.length
            (G ++ ((v0, w0) :: R)).length := by
          have h := hnr
          rw [hMeq, hlpeq] at h
          have hlen2 : ((G ++ ((v0, w0) :: R)) ++ [((v0 + d0, w0 + 1) : ℕ × ℕ)]).length - 1
              = (G ++ ((v0, w0) :: R)).length := by simp
          rw [hlen2] at h
          exact h
        have hstrict : w0 + 1 ≤ w :=
          spineOK_of_nextrel1_strict hnr' T C (u, w) hRdec huv
            (fun y hy => h1 y (by rw [hD1]; exact List.mem_append_left _ hy))
        omega

/-- **The `bad` branch of the derivation induction**, assembled from the three
cases above.

`M = G ++ blk ++ [lp]`, `blk = (v0,w0) :: R`, `M⟦n⟧ = G ++ copies d0 blk n`.
Given `ArgDomCoreOn M`, show `ArgDomCoreOn (M⟦n⟧)`.

The proof is the inner strong induction on the copy count `n` (legitimate: we
prove `∀ n ≥ 1, ArgDomCoreOn (M⟦n⟧)` from `ArgDomCoreOn M`, and case A1 consumes
the induction hypothesis) followed by the exhaustive three-way dispatch on the
position of the two marked columns relative to `p = G.length + blk.length`.  See
the section docstring above for the coverage argument. -/
theorem argDomCoreOn_bad {M G R : PairSeq} {v0 w0 d0 n : ℕ} {lp : ℕ × ℕ}
    (hM : ST_PS M) (hMon : ArgDomCoreOn M)
    (hMeq : M = G ++ ((v0, w0) :: R) ++ [lp])
    (hRgt : ∀ x ∈ R, v0 < x.1) (hlp : v0 < lp.1)
    (hdisj : (d0 = 0 ∧ lp.2 = 0 ∧ lp.1 = v0 + 1)
      ∨ (0 < d0 ∧ lp.2 = w0 + 1 ∧ lp.1 = v0 + d0
          ∧ nextrel1 M G.length (M.length - 1)))
    (hSTn : ∀ m, 1 ≤ m → ST_PS (G ++ copies d0 ((v0, w0) :: R) m))
    (hn : 1 ≤ n) :
    ArgDomCoreOn (G ++ copies d0 ((v0, w0) :: R) n) := by
  revert hn
  induction n using Nat.strong_induction_on with
  | _ n hstrong =>
    intro hn X A1 B A2 Z u w e heq he h1 h2 h3 h4 h5 h6
    have hIH : ∀ m, 1 ≤ m → m < n → ArgDomCoreOn (G ++ copies d0 ((v0, w0) :: R) m) :=
      fun m hm1 hm2 => hstrong m hm2 hm1
    -- the exhaustive three-way split: `j < p`, then `i < p ≤ j`, then `p ≤ i`
    rcases Nat.lt_or_ge (X.length + (A1.length + 1)) (G.length + (R.length + 1)) with hc | hc
    · exact argDomCoreOn_bad_B hM hMon hMeq hRgt hlp hdisj hSTn hIH hn
        heq he h1 h2 h3 h4 h5 h6 hc
    · rcases Nat.lt_or_ge X.length (G.length + (R.length + 1)) with hc2 | hc2
      · exact argDomCoreOn_bad_A2 hM hMon hMeq hRgt hlp hdisj hSTn hIH hn
          heq he h1 h2 h3 h4 h5 h6 hc2 (by omega)
      · exact argDomCoreOn_bad_A1 hM hMon hMeq hRgt hlp hdisj hSTn hIH hn
          heq he h1 h2 h3 h4 h5 h6 (by omega)

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
      -- every expanded sequence is itself a standard form
      have hSTn : ∀ m, 1 ≤ m → ST_PS (G ++ copies d0 ((v0, w0) :: R) m) := by
        intro m hm
        rw [← hMn m hm]
        exact ST_PS.oper hM hm
      rw [hMn n hn]
      exact argDomCoreOn_bad hM hMon hMeq R_gt lp_gt disj hSTn hn

/-- The derivation induction, modulo the `bad` branch. -/
theorem argDomCoreOn_ST_PS {N : PairSeq} (hN : ST_PS N) : ArgDomCoreOn N := by
  induction hN with
  | diag v => exact argDomCoreOn_diag v
  | @oper M n hM hn ih => exact argDomCoreOn_oper hM ih hn

/-- `ArgDomCore`, modulo `argDomCoreOn_bad`. -/
theorem argDomCore_holds : ArgDomCore :=
  argDomCore_of_on (fun _ h => argDomCoreOn_ST_PS h)

#print axioms peel_aux
#print axioms argDomCoreOn_drop_left
#print axioms argDomCoreOn_shiftr0
#print axioms sle_shiftr0
#print axioms spineOK_of_nextrel1
#print axioms ascArgDom_of_core
#print axioms pss_cofinality_of_core
#print axioms argDomCoreOn_diag
#print axioms argDomCoreOn_snoc_zero
#print axioms argDomCoreOn_bad_A1
#print axioms argDomCoreOn_oper

#print axioms argDomCoreOn_bad_A1
#print axioms argDomCoreOn_bad_B
#print axioms argDomCoreOn_bad_A2
#print axioms argDomCoreOn_bad
#print axioms argDomCoreOn_ST_PS
#print axioms argDomCore_holds
#print axioms ascArgDom_of_core
#print axioms pss_cofinality_of_core

end YAPSS
