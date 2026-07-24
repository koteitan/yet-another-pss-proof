/-
# `W_u` — the PSS iterated inductive set (pillar 2 of the ordinal-free route)

Companion of `YAPSS/Cofinality.lean` (pillar 1, `pss_cofinality`).  This file
transplants Buchholz (1987) §2 — the iterated inductive set `W_v = lfp(A_v)`
and its induction principle (A2) — to PSS pair sequences, and proves the
**bridge**

    (A/W least-fixpoint induction)  +  Bachmann cofinality  ⟹  `Acc` for `olt`
                                                                on `ST_PS` images.

Cofinality is taken as an explicit hypothesis (`hcof`); this file deliberately
does **not** import `YAPSS/Cofinality.lean`.

--------------------------------------------------------------------------------
## THE DESIGN PROBLEM AND ITS ANSWER

Buchholz's operator has three branches

    c ∈ A_v(X) ⟺ c = 0
               ∨ (dom c ∈ {{0}, ℕ_B} ∧ ∀ n, c[n̄] ∈ X)
               ∨ (∃ m < v, dom c = T_m ∧ ∀ z ∈ W_m, c[z] ∈ X)

and the **third branch is the entire engine**.  Without it `W = lfp(A)` is
literally the accessible part of the fundamental-sequence relation, so
"`M ∈ W`" *is* "the expansion tree below `M` is well-founded" — i.e. PSS
termination itself.  Any design that keeps only the ℕ-branch is therefore
CIRCULAR, and this is a real danger in PSS because **every** PSS expansion
`M⟦n⟧` is ℕ-indexed (`oper`, `YAPSS/Def.lean:100`; `ST_PS.oper` needs `1 ≤ n`).

### (a) What indexes `W_u`: the **row-1 (ψ-subscript) level**

`translate`'s principal subscript is the pair's row-1 value
(`lead_translate`, `Mechanized.lean:160`): `translate (p :: rest) = P p.2 _ _`,
i.e. `p_{p.2}(…)`.  So row-1 plays the role of Buchholz's `ψ`-subscript `v`,
a pair `(x, w)` with `w > 0` and no descendants plays the role of `Ω_w = D_w 0`,
and `T_m` = "all top-level principal subscripts `≤ m`" becomes "all top-level
forest roots carry row-1 `≤ m`".  `W_u` is indexed by that row-1 level `u`,
exactly as in the source, and the family is built by **iterated** induction on
`u : ℕ` (`Wset.Wf` below), because the `T_m`-branch mentions `W_m` in a
non-monotone parameter position.

### (b) What the `T_m` branch becomes: the **row-1-orphan / graft** branch

Read `dom` off the *rightmost spine* of the term, exactly as Buchholz does:

    dom(a + b) = dom(b),   dom(D_v b) = T_u  iff  dom(b) = T_u with u < v,
    dom(D_{m+1} 0) = T_m.

Under `translate`, the rightmost spine of `translate M` is the **row-0 ancestor
chain of the LAST pair of `M`** (the last summand is the last top-level tree,
its argument is that tree's descendant block, and so on; the bottom of the
spine is the last list entry).  Therefore, writing `j1 = |M| - 1`:

    dom(M) = T_m   ⟺   `entry M 1 j1 = m + 1`   (the spine bottoms out at `Ω_{m+1}`)
                   ∧   every strict row-0 ancestor of `j1` carries row-1 `> m`
                       (each `D_v` step on the way up must satisfy `u < v`).

and the second clause is **literally PSS's own `¬ hasParent M 1 j1`**: `nextrel1`
picks the *largest* row-0 ancestor with row-1 strictly below `entry M 1 j1`, so
such a parent exists iff *some* strict row-0 ancestor has a strictly smaller
row-1 value.  Hence

    `domT M m  :=  entry M 1 (|M|-1) = m + 1  ∧  ¬ hasParent M 1 (|M|-1)`

("the last pair is a **row-1 orphan** of level `m+1`") is the PSS `dom = T_m`.
The corresponding `T_m`-indexed fundamental sequence substitutes a level-`≤ m`
forest for that `Ω_{m+1}` leaf, i.e. it is the **graft**

    `graft M z  :=  M.dropLast ++ z.map (fun p => (p.1 + entry M 0 (|M|-1), p.2))`

(re-base the block `z` at the depth the dropped `Ω_{m+1}` occupied).  It is the
faithful reading of `(a' + D_v(… D_{m+1} 0 …))[z] = a' + D_v(… z …)`.

**Side condition (`based`).**  For `graft M z` to *be* that substitution the
block `z` must be given in normalised (depth-`0`-anchored) form, i.e.
`entry z 0 0 = 0`: only then does `z`'s first root land at exactly the row-0
depth the `Ω_{m+1}` leaf occupied, so that (i) the block attaches to the same
parent, (ii) `z`'s own roots stay roots, and (iii) the uniform shift — which
`translate` cannot see, since it compares row-0 values only pairwise — carries
`translate z` unchanged.  Without it, e.g. `M = (0,3)(1,2)(1,1)` (`domT M 0`)
and `z = (2,0)` would give `M.dropLast ++ [(3,0)]`, in which the grafted node
becomes a *child* of `(1,2)` instead of its sibling — a structurally wrong
graft.  The `T_m` branch therefore quantifies over `z ∈ W_m` with
`entry z 0 0 = 0`; `z = 0` (`[]`) satisfies it, which is all the bridge needs.

Note `graft M [] = M.dropLast`, and PSS's own `oper` in exactly this branch
returns `Pred M = M.dropLast` (`oper_eq_pred_of_noParent`): **PSS truncates the
`T_m`-indexed fundamental sequence to its bottom element `z = 0`.**  That is the
precise sense in which the level hierarchy is invisible to `oper` and has to be
re-introduced by hand.

### (c) Why this is not circular

Three independent reasons, all inherited from the source:

1. The `T_m`-branch quantifies over `W_m` for `m < u`, a set built at an
   **earlier stage** of the `ℕ`-recursion `Wf`.  So `W_u` is a genuine iterated
   inductive definition, not a self-reference.
2. The intended membership proof (the 2.6–2.8 analogue, `W_membership` below)
   runs by induction on the **length of the pair sequence** — a syntactic
   measure — and never descends the expansion tree.  It is the `T_m` branch
   that makes that possible: it lets `A` see the *argument* structure of a term
   rather than only its ℕ-indexed expansion.
3. `domT` is **never satisfied by an `ST_PS` standard form** of length `> 1` in
   a load-bearing way: for those, `graft M [] = M.dropLast = M⟦n⟧`, so the
   `T_m` branch *implies* the ℕ branch and the bridge closes with `hcof` alone
   (see `acc_of_W`).  The `T_m` branch does its real work on the *sub-blocks*
   (`Ω_{m+1}`-cofinal, hence non-`ST_PS`) that the membership induction
   traverses.  This is why the bridge below needs **no** extra cofinality
   hypothesis beyond the ℕ-indexed `hcof` the companion file proves.

### (d) Branch 1

Buchholz's first branch is `c = 0`.  In PSS `oper` is the identity on sequences
of length `≤ 1` (`oper_eq_self_of_short`), so those are *terminal* states of the
system and must be handled as atoms; the honest atom set is

    `|M| ≤ 1  ∧  entry M 1 0 = 0`,

i.e. `translate M ∈ {0, p_0(0)} = {0, 1}`, both of which are in every `W_v`
(`0` by (W1) and `1 = D_0 0` by `dom = {0}`, `1[0] = 0`).  A single pair
`(x, w)` with `w > 0` is *not* an atom: it is `Ω_w`, and it enters `W_u`
(`u ≥ w`) through the `T_{w-1}` branch — `domT [(x,w)] (w-1)` holds, and
`graft [(x,w)] z = z` re-based, which is exactly `Ω_w[z] = z`.

--------------------------------------------------------------------------------
## STATUS

* GREEN (`sorry`-free): `Wf`/`W`, (A1), (A2), (A2'), level monotonicity,
  `domT`/`graft` basics, the design-validation theorem `hasParent_one_iff`, and
  the **bridge** `acc_of_W` (modulo the explicit `hcof` parameter only — no
  second, `T_m`-indexed cofinality hypothesis is needed).
* `sorry` (exactly one, clearly labelled, believed TRUE, the remaining
  mathematical work): `W_membership` — the PSS analogue of Buchholz 2.8.
* Derived from the two: `wf_of_cofinality_and_membership`.

No `native_decide`, no `admit`.  **§6 at the bottom of the file is the report**,
including the flag that an `H0clause`-shaped coefficient-domination condition is
likely to reappear in the additive-closure step (2.4(b)) of the membership
route — the bridge itself is free of it.
-/
import YAPSS.Nrm

namespace YAPSS
open Three

namespace Wset

/-! ## 0. Small facts about `translate`, `ST_PS` and `oper` -/

/-- `translate` is `Z` only on the empty sequence. -/
theorem translate_eq_Z_iff {M : PairSeq} : translate M = Z ↔ M = [] := by
  cases M with
  | nil => simp [translate]
  | cons p rest => simp [translate]

/-- Nothing but `0` is `<o` the term `p₀(0) = 1`. -/
theorem eq_Z_of_olt_one {t : Three} (h : t <o P 0 Z Z) : t = Z := by
  cases t with
  | Z => rfl
  | P a b c =>
      rcases olt_P_P.mp h with h1 | ⟨-, h1⟩ | ⟨-, -, h1⟩
      · exact absurd h1 (Nat.not_lt_zero a)
      · exact absurd h1 (not_olt_Z b)
      · exact absurd h1 (not_olt_Z c)

/-- A standard form is nonempty. -/
theorem stps_ne_nil {M : PairSeq} (hM : ST_PS M) : M ≠ [] := by
  intro h
  have := stps_len_pos hM
  rw [h] at this
  simp at this

/-- A standard form of length `1` is `[(0,0)]`. -/
theorem stps_len_one {M : PairSeq} (hM : ST_PS M) (h : M.length = 1) : M = [(0, 0)] := by
  have hh := stps_head hM
  match M, h with
  | [p], _ => simpa [List.headD_cons] using congrArg (fun q => [q]) hh

/-! ## 1. `dom = T_m` and the `T_m`-indexed fundamental sequence (the graft)

See the design discussion (b) in the file header. -/

/-- **PSS `dom(M) = T_m`**: the last pair of `M` is a *row-1 orphan* of level
`m+1` — its row-1 value is `m+1 > 0` and it has no row-1 parent, i.e. every
strict row-0 ancestor carries a row-1 value `> m`.  This is exactly Buchholz's
`dom(a) = T_m` read off the rightmost spine of `translate M`. -/
def domT (M : PairSeq) (m : ℕ) : Prop :=
  entry M 1 (M.length - 1) = m + 1 ∧ ¬ hasParent M 1 (M.length - 1)

/-- **The `T_m`-indexed fundamental sequence `M[z]`**: replace the trailing
`Ω_{m+1}` leaf by the forest `z`, re-based at the depth (row-0 value) that leaf
occupied.  Only meaningful for `based z` (see `based`). -/
def graft (M z : PairSeq) : PairSeq :=
  M.dropLast ++ z.map (fun p => (p.1 + entry M 0 (M.length - 1), p.2))

/-- A block is in normalised (depth-`0`-anchored) form: its first entry sits at
row-0 depth `0`.  Since row-0 values are naturals, this makes index `0` a
minimum, hence a top-level root, hence `graft M z` really is the substitution
of `translate z` for the `Ω_{m+1}` leaf of `translate M`.  See the header. -/
def based (z : PairSeq) : Prop := entry z 0 0 = 0

@[simp] theorem based_nil : based ([] : PairSeq) := by simp [based, entry]

@[simp] theorem graft_nil (M : PairSeq) : graft M [] = M.dropLast := by
  simp [graft]

/-- `domT` is never satisfied by the empty sequence. -/
theorem not_domT_nil (m : ℕ) : ¬ domT ([] : PairSeq) m := by
  rintro ⟨h, -⟩
  simp [entry] at h

/-- In the `domT` branch PSS's own expansion degenerates to the bottom
(`z = 0`) element of the `T_m`-indexed family: `M⟦n⟧ = M.dropLast = graft M []`. -/
theorem oper_eq_graft_nil_of_domT {M : PairSeq} {m n : ℕ}
    (hL : 1 < M.length) (hd : domT M m) : M⟦n⟧ = graft M [] := by
  obtain ⟨hw, hp⟩ := hd
  have hj1 : M.length - 1 ≠ 0 := by omega
  have hpos : 0 < entry M 1 (M.length - 1) := by rw [hw]; omega
  have hi1 : idx1 M (M.length - 1) = 1 := by unfold idx1; rw [if_pos hpos]
  have hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0) := by
    rintro ⟨-, h2⟩; omega
  have := oper_eq_pred_of_noParent (M := M) n hj1 hz (by rw [hi1]; exact hp)
  rw [this, graft_nil]
  unfold Pred
  rw [if_neg (by omega)]

/-! ### 1a. Validation of the design answer

The header claims that PSS's own `hasParent … 1 …` predicate *is* the Buchholz
spine condition.  That is not a definition, it is a theorem about `nextrel1`, and
it is proved here so the design answer is checked rather than asserted. -/

/-- A strict row-0 ancestor of `j1` carrying a strictly smaller row-1 value —
i.e. a `D_v` step on the rightmost spine with `v ≤ m`, which is exactly what
breaks Buchholz's `T_m` propagation `dom(D_v b) = T_u  ⟸  u < v`. -/
def r1cand (M : PairSeq) (j1 j0 : ℕ) : Prop :=
  j0 < j1 ∧ le0 M j0 j1 ∧ entry M 1 j0 < entry M 1 j1

/-- **Design validation.**  `hasParent M 1 j1` holds iff *some* strict row-0
ancestor of `j1` carries a smaller row-1 value: `nextrel1` selects the
**largest** such ancestor, and that choice is automatically the unique one. -/
theorem hasParent_one_iff {M : PairSeq} {j1 : ℕ} (hj1 : j1 < M.length) :
    hasParent M 1 j1 ↔ ∃ j0, r1cand M j1 j0 := by
  classical
  have nR : ∀ j0 : ℕ, nextR M 1 j0 j1 ↔ nextrel1 M j0 j1 := by
    intro j0; unfold nextR; rw [if_neg (by omega)]
  constructor
  · rintro ⟨j0, hj0, -⟩
    have h : nextrel1 M j0 j1 := (nR j0).mp hj0
    exact ⟨j0, h.2.2.1, h.2.2.2.2.1, h.2.2.2.1⟩
  · rintro ⟨j0, hc⟩
    set P : ℕ → Prop := fun k => r1cand M j1 k with hP
    have hPg : P (Nat.findGreatest P j1) :=
      Nat.findGreatest_spec (m := j0) (le_of_lt hc.1) hc
    have hmax : ∀ k, P k → k ≤ Nat.findGreatest P j1 :=
      fun k hk => Nat.le_findGreatest (le_of_lt hk.1) hk
    refine ⟨Nat.findGreatest P j1, (nR _).mpr ?_, ?_⟩
    · refine ⟨lt_trans hPg.1 hj1, hj1, hPg.1, hPg.2.2, hPg.2.1, ?_⟩
      rintro j ⟨hgj, hlej⟩
      by_contra hcon
      have hlt : entry M 1 j < entry M 1 j1 := by omega
      have hjle : j ≤ j1 := nextrel0_rtrancl_index_le hlej.2.2
      rcases eq_or_lt_of_le hjle with rfl | hjlt
      · omega
      · exact absurd (hmax j ⟨hjlt, hlej, hlt⟩) (by omega)
    · intro y hy
      have hy' : nextrel1 M y j1 := (nR y).mp hy
      have hyP : P y := ⟨hy'.2.2.1, hy'.2.2.2.2.1, hy'.2.2.2.1⟩
      rcases eq_or_lt_of_le (hmax y hyP) with h | h
      · exact h
      · have := hy'.2.2.2.2.2 (Nat.findGreatest P j1) ⟨h, hPg.2.1⟩
        have := hPg.2.2
        omega

/-- `domT` spelled out as Buchholz's spine condition: the rightmost spine of
`translate M` bottoms out at `Ω_{m+1}` and every `D_v` on the way up has
`v > m`. -/
theorem domT_iff {M : PairSeq} {m : ℕ} (hne : M ≠ []) :
    domT M m ↔ (entry M 1 (M.length - 1) = m + 1 ∧
      ∀ j0, j0 < M.length - 1 → le0 M j0 (M.length - 1) → m + 1 ≤ entry M 1 j0) := by
  have hj1 : M.length - 1 < M.length := by
    have : 0 < M.length := List.length_pos_iff.mpr hne
    omega
  unfold domT
  rw [hasParent_one_iff hj1]
  constructor
  · rintro ⟨hw, hp⟩
    refine ⟨hw, fun j0 h1 h2 => ?_⟩
    by_contra hcon
    exact hp ⟨j0, h1, h2, by omega⟩
  · rintro ⟨hw, hall⟩
    refine ⟨hw, ?_⟩
    rintro ⟨j0, h1, h2, h3⟩
    have := hall j0 h1 h2
    omega

/-! ### 1b. Sanity checks: the `Ω_{m+1}` atom

A lone pair `(x, m+1)` is `Ω_{m+1}`: it satisfies `domT … m`, and its
`T_m`-indexed fundamental sequence is the identity `Ω_{m+1}[z] = z` (re-based),
exactly as in Buchholz. -/

example (x m : ℕ) : domT [(x, m + 1)] m := by
  refine ⟨by simp [entry], ?_⟩
  rintro ⟨j0, hj0, -⟩
  unfold nextR at hj0
  rw [if_neg (by omega)] at hj0
  have := hj0.2.2.1
  simp at this

example (x m : ℕ) (z : PairSeq) :
    graft [(x, m + 1)] z = z.map (fun p => (p.1 + x, p.2)) := by
  simp [graft, entry]

example (m : ℕ) : ¬ domT [((0 : ℕ), (0 : ℕ))] m := by
  rintro ⟨h, -⟩
  simp [entry] at h

/-! ### 1c. Sanity checks: why the `based` side condition is not cosmetic

`M = (0,3)(1,2)(1,1)` is `Ω_1`-cofinal (`domT M 0`): the trailing `(1,1)` is a
row-1 orphan (its only strict row-0 ancestor `(0,3)` carries row-1 `3 > 0`).  So
`translate M = p₃(p₂(0) + p₁(0))` and `M[z]` must be `p₃(p₂(0) + z)`.

The two blocks `[(0,0)]` and `[(2,0)]` have the *same* translate `p₀(0)`, but
only the `based` one grafts correctly: the other turns the grafted node into a
*child* of `(1,2)` instead of its sibling. -/

example : domT [(0, 3), (1, 2), (1, 1)] 0 := by
  rw [domT_iff (by simp)]
  refine ⟨by simp [entry], ?_⟩
  intro j0 h1 _
  have h2 : j0 = 0 ∨ j0 = 1 := by simp at h1; omega
  rcases h2 with rfl | rfl <;> simp [entry]

/-- The two candidate blocks are order-theoretically indistinguishable. -/
example : translate [((0 : ℕ), (0 : ℕ))] = translate [((2 : ℕ), (0 : ℕ))] := by
  simp [translate]

/-- `based` block: grafts to `p₃(p₂(0) + p₀(0))` — the honest substitution. -/
example : graft [(0, 3), (1, 2), (1, 1)] [(0, 0)] = [(0, 3), (1, 2), (1, 0)] := by
  decide

example : translate [((0 : ℕ), (3 : ℕ)), (1, 2), (1, 0)] = P 3 (P 2 Z (P 0 Z Z)) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-- Not `based`: the same `z` grafts to the WRONG term `p₃(p₂(p₀(0)))` — the
node became a *child* of `(1,2)` instead of its sibling. -/
example : graft [(0, 3), (1, 2), (1, 1)] [(2, 0)] = [(0, 3), (1, 2), (3, 0)] := by
  decide

example : translate [((0 : ℕ), (3 : ℕ)), (1, 2), (3, 0)] = P 3 (P 2 (P 0 Z Z) Z) Z := by
  simp [translate, List.takeWhile, List.dropWhile]

/-! ## 2. The operator `A_u` and the iterated inductive set `W_u`

Faithful transplant of Buchholz (1987) p.138 (1)(2), with the design answer of
the header substituted for the two PSS-specific branches. -/

/-- Least fixpoint on `Set PairSeq` (only the two Knaster–Tarski faces we use). -/
def lfpS (f : Set PairSeq → Set PairSeq) : Set PairSeq := ⋂₀ {Y | f Y ⊆ Y}

theorem lfpS_lowerbound {f : Set PairSeq → Set PairSeq} {Y : Set PairSeq}
    (h : f Y ⊆ Y) : lfpS f ⊆ Y := fun _ hx => hx Y h

theorem lfpS_unfold_le {f : Set PairSeq → Set PairSeq} (hm : Monotone f) :
    f (lfpS f) ⊆ lfpS f := by
  intro x hx Y hY
  exact hY (hm (lfpS_lowerbound hY) hx)

theorem lfpS_unfold_ge {f : Set PairSeq → Set PairSeq} (hm : Monotone f) :
    lfpS f ⊆ f (lfpS f) :=
  lfpS_lowerbound (hm (lfpS_unfold_le hm))

theorem lfpS_unfold {f : Set PairSeq → Set PairSeq} (hm : Monotone f) :
    f (lfpS f) = lfpS f :=
  Set.Subset.antisymm (lfpS_unfold_le hm) (lfpS_unfold_ge hm)

/-- **The PSS operator `A_u`.**  Branch 1 = the atoms `{0, 1}` (PSS's terminal
states, on which `oper` is the identity); branch 2 = the ℕ-indexed PSS
fundamental sequence `M⟦n⟧`; branch 3 = the `T_m`-graft branch of the header,
quantifying over the already-built stage `Wf m` for `m < u`. -/
def Aop (Wfam : ℕ → Set PairSeq) (u : ℕ) (X : Set PairSeq) (M : PairSeq) : Prop :=
  (M.length ≤ 1 ∧ entry M 1 0 = 0) ∨
  (∀ n : ℕ, 1 ≤ n → M⟦n⟧ ∈ X) ∨
  (∃ m : ℕ, m < u ∧ domT M m ∧ ∀ z ∈ Wfam m, based z → graft M z ∈ X)

def Aset (Wfam : ℕ → Set PairSeq) (u : ℕ) (X : Set PairSeq) : Set PairSeq :=
  {M | Aop Wfam u X M}

theorem Aop_mono_X {Wfam : ℕ → Set PairSeq} {u : ℕ} {X Y : Set PairSeq} {M : PairSeq}
    (h : Aop Wfam u X M) (hXY : X ⊆ Y) : Aop Wfam u Y M := by
  rcases h with h | h | ⟨m, hm, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl fun n hn => hXY (h n hn))
  · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz hb => hXY (hop z hz hb)⟩)

theorem Aset_mono (Wfam : ℕ → Set PairSeq) (u : ℕ) : Monotone (Aset Wfam u) := by
  intro X Y hXY M hM
  exact Aop_mono_X (Wfam := Wfam) (u := u) hM hXY

/-- `A_u(X) ⊆ A_v(X)` for `u ≤ v` (only the third branch sees `u`). -/
theorem Aop_mono_level {Wfam : ℕ → Set PairSeq} {u v : ℕ} {X : Set PairSeq} {M : PairSeq}
    (le : u ≤ v) (h : Aop Wfam u X M) : Aop Wfam v X M := by
  rcases h with h | h | ⟨m, hm, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨m, lt_of_lt_of_le hm le, hd, hop⟩)

/-- `A_u` reads only the stages `< u` of the family parameter. -/
theorem Aop_cong {Wfam Wgam : ℕ → Set PairSeq} {u : ℕ} {X : Set PairSeq} {M : PairSeq}
    (e : ∀ m : ℕ, m < u → Wfam m = Wgam m) :
    Aop Wfam u X M ↔ Aop Wgam u X M := by
  constructor
  · rintro (h | h | ⟨m, hm, hd, hop⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz => hop z ((e m hm) ▸ hz)⟩)
  · rintro (h | h | ⟨m, hm, hd, hop⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz => hop z ((e m hm).symm ▸ hz)⟩)

/-- Stage family: `Wf n m` is the honest `W_m` for `m < n` (and `∅` above). -/
def Wf : ℕ → ℕ → Set PairSeq
  | 0 => fun _ => ∅
  | v + 1 => fun m => if m = v then lfpS (Aset (Wf v) v) else Wf v m

/-- **The PSS iterated inductive set `W_u`.** -/
def W (u : ℕ) : Set PairSeq := Wf (u + 1) u

theorem Wf_coh {m n : ℕ} (h : m < n) : Wf n m = Wf (m + 1) m := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ v ih =>
      by_cases hmv : m = v
      · subst hmv; rfl
      · have mlv : m < v := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp h) hmv
        show (if m = v then _ else Wf v m) = _
        rw [if_neg hmv]
        exact ih mlv

theorem Wf_eq_W {m n : ℕ} (h : m < n) : Wf n m = W m := Wf_coh h

/-- Defining equation: `W_u = lfp (A_u)` with the *full* family `W` as parameter. -/
theorem W_unfold (u : ℕ) : W u = lfpS (Aset W u) := by
  have stage : W u = lfpS (Aset (Wf u) u) := by
    show Wf (u + 1) u = _
    show (if u = u then _ else Wf u u) = _
    rw [if_pos rfl]
  have cong : ∀ m : ℕ, m < u → Wf u m = W m := fun m hm => Wf_eq_W hm
  have ptw : ∀ X : Set PairSeq, Aset (Wf u) u X = Aset W u X := by
    intro X; ext M
    exact Aop_cong (Wfam := Wf u) (Wgam := W) (u := u) (X := X) cong
  rw [stage, funext ptw]

/-- **(A1)** the fixpoint equation `A_u(W_u) = W_u`. -/
theorem A1 (u : ℕ) : Aset W u (W u) = W u := by
  rw [W_unfold u]
  exact lfpS_unfold (Aset_mono W u)

/-- **(A2)** the induction principle `A_u(Y) ⊆ Y ⟹ W_u ⊆ Y`. -/
theorem A2 {u : ℕ} {Y : Set PairSeq} (h : Aset W u Y ⊆ Y) : W u ⊆ Y := by
  rw [W_unfold u]
  exact lfpS_lowerbound h

/-- **(A2′)** the pointwise form of the induction principle. -/
theorem A2' {u : ℕ} {Y : Set PairSeq}
    (hY : ∀ M : PairSeq, Aop W u Y M → M ∈ Y) : W u ⊆ Y :=
  A2 (fun M hM => hY M hM)

theorem A1_intro {u : ℕ} {M : PairSeq} (h : Aop W u (W u) M) : M ∈ W u := by
  have : M ∈ Aset W u (W u) := h
  rwa [A1 u] at this

theorem A1_dest {u : ℕ} {M : PairSeq} (h : M ∈ W u) : Aop W u (W u) M := by
  have : M ∈ Aset W u (W u) := by rw [A1 u]; exact h
  exact this

/-- (W1) `0 ∈ W_u`. -/
theorem W_nil (u : ℕ) : ([] : PairSeq) ∈ W u :=
  A1_intro (Or.inl ⟨by simp, by simp [entry]⟩)

/-- (W1′) the second atom `1 = p₀(0) ∈ W_u`. -/
theorem W_atom (u : ℕ) {M : PairSeq} (hl : M.length ≤ 1) (hw : entry M 1 0 = 0) :
    M ∈ W u :=
  A1_intro (Or.inl ⟨hl, hw⟩)

/-- Level monotonicity `u ≤ v ⟹ W_u ⊆ W_v` (Buchholz (1987) p.137). -/
theorem W_mono {u v : ℕ} (h : u ≤ v) : W u ⊆ W v :=
  A2' (fun _ A => A1_intro (Aop_mono_level h A))

/-! ## 3. The bridge: `W_u ⊆ Acc` under Bachmann cofinality

Mirror of `acc_of_W_wfe` in the source
(`pss-proof/git/lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-main.lean:151`).
Cofinality enters only through the explicit hypothesis `hcof`. -/

/-- The target relation: strict `olt` on `translate`-images of standard forms. -/
def Rst : PairSeq → PairSeq → Prop :=
  fun a b => ST_PS a ∧ ST_PS b ∧ translate a <o translate b

/-- `Acc` only depends on the `translate`-image (for standard forms). -/
theorem acc_of_translate_eq {a b : PairSeq} (ha : ST_PS a)
    (e : translate b = translate a) (h : Acc Rst a) : Acc Rst b :=
  Acc.intro b fun y hy => h.inv ⟨hy.1, ha, by rw [← e]; exact hy.2.2⟩

/-- The ℕ-branch step of the bridge: if all PSS expansions of a standard form
are accessible, so is the form itself.  This is where cofinality is used. -/
theorem acc_of_nat_branch
    (hcof : ∀ {M N : PairSeq}, ST_PS M → ST_PS N → translate N <o translate M →
      ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧))
    {c : PairSeq} (hc : ST_PS c) (h : ∀ n : ℕ, 1 ≤ n → Acc Rst (c⟦n⟧)) :
    Acc Rst c := by
  refine Acc.intro c ?_
  intro b hb
  obtain ⟨hbst, -, hlt⟩ := hb
  obtain ⟨n, hn, hle⟩ := hcof hc hbst hlt
  have hacc : Acc Rst (c⟦n⟧) := h n hn
  have hst : ST_PS (c⟦n⟧) := ST_PS.oper hc hn
  rcases hle with hlt' | heq
  · exact hacc.inv ⟨hbst, hst, hlt'⟩
  · exact acc_of_translate_eq hst heq hacc

/-- **The bridge.**  Under Bachmann cofinality every member of `W_u` is
accessible for the `ST_PS`-restricted `olt` order.

Mirrors `acc_of_W_wfe`; the three `A_u` branches are handled as follows.

* branch 1 (atoms): `translate M ∈ {0, 1}`, and nothing `ST_PS` is `<o 1`;
* branch 2 (ℕ): `hcof` (`acc_of_nat_branch`);
* branch 3 (`T_m`-graft): for `|M| > 1` this *implies* branch 2, because PSS's
  own `oper` degenerates to `graft M [] = M.dropLast` there
  (`oper_eq_graft_nil_of_domT`) and `[] ∈ W m`; for `|M| ≤ 1` a standard form is
  `[(0,0)]`, whose last pair has row-1 `= 0 ≠ m+1`, contradicting `domT`. -/
theorem acc_of_W
    (hcof : ∀ {M N : PairSeq}, ST_PS M → ST_PS N → translate N <o translate M →
      ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧))
    (u : ℕ) : ∀ M : PairSeq, M ∈ W u → Acc Rst M := by
  show W u ⊆ {M | Acc Rst M}
  refine A2' ?_
  intro c A
  by_cases hc : ST_PS c
  · -- `c` is a standard form: examine the three generating branches.
    have hne : c ≠ [] := stps_ne_nil hc
    rcases A with ⟨hlen, hw⟩ | hnat | ⟨m, -, hd, hgr⟩
    · -- branch 1: `translate c = p₀(0) = 1`; only `0` is below, and `0 ∉ ST_PS`.
      have hlen1 : c.length = 1 := by
        have := stps_len_pos hc; omega
      obtain ⟨p, rfl⟩ : ∃ p, c = [p] := by
        match c, hlen1 with
        | [p], _ => exact ⟨p, rfl⟩
      have hp2 : p.2 = 0 := by simpa [entry] using hw
      have ht : translate [p] = P 0 Z Z := by
        rw [translate]; simp [translate, hp2]
      refine Acc.intro _ ?_
      intro y hy
      obtain ⟨hyst, -, hlt⟩ := hy
      rw [ht] at hlt
      exact absurd (translate_eq_Z_iff.mp (eq_Z_of_olt_one hlt)) (stps_ne_nil hyst)
    · -- branch 2: the ℕ-indexed fundamental sequence.
      exact acc_of_nat_branch hcof hc hnat
    · -- branch 3: the `T_m`-graft branch.
      by_cases hlen : 1 < c.length
      · -- PSS's `oper` degenerates to `graft c [] = c.dropLast` here.
        refine acc_of_nat_branch hcof hc ?_
        intro n hn
        have := hgr [] (W_nil m) based_nil
        rw [← oper_eq_graft_nil_of_domT (n := n) hlen hd] at this
        exact this
      · -- a standard form of length `≤ 1` is `[(0,0)]`: `domT` fails.
        have hlen1 : c.length = 1 := by
          have := stps_len_pos hc; omega
        have hc0 : c = [(0, 0)] := stps_len_one hc hlen1
        exfalso
        obtain ⟨hw, -⟩ := hd
        rw [hc0] at hw
        simp [entry] at hw
  · -- `c` is not a standard form: it has no `Rst`-predecessor.
    exact Acc.intro c fun y hy => absurd hy.2.1 hc

/-! ## 4. Membership — the PSS analogue of Buchholz (1987) 2.8

**OPEN OBLIGATION (believed TRUE; the remaining mathematical work).**

The source route is 2.4(b) (additive closure) → 2.5 → 2.6 (`A_ω(W*) ⊆ W*` with
`W* = {x | ∀ u, D_u x ∈ W_u}`, core case `dom b = T_u`, `v ≤ u`, via the tower
`x_0 = D_v 0`, `x_{i+1} = D_v(b[x_i])` and `(D_v b)[n] = D_v(b[x_n])`) → 2.7
(induction on **term length**) → 2.8.

Its PSS reading, with the dictionary of the header:

* `D_u x` = "prepend the pair `(0,u)` to the block `x` pushed one row-0 level
  down"; `W* = {x | ∀ u, that sequence ∈ W_u}`;
* the tower `x_0, x_1, …` is the **BMS ascending copy/tiling**:
  `oper_bad_blocks` (`Mechanized.lean:836`) gives
  `M⟦n⟧ = G ++ (List.range n).flatMap (fun k => body.map (p ↦ (p.1 + k*d0, p.2)))`,
  i.e. the `n`-fold nesting of the block — literally `(D_v b)[n] = D_v(b[x_n])`,
  with `w0 < lp.2` (the `i1 = 1` clause of `oper_bad_blocks`) supplying the
  strict subscript drop that makes the tower land in `W_{u}` for the *lower*
  level `u`;
* 2.7's induction on term length becomes induction on `M.length`, the additive
  closure 2.4(b) becomes closure of `W_u` under list concatenation of blocks,
  and `T_m ⊆ W_m` (the source's `y3_TBv_dfree_W`) becomes "every pair sequence
  all of whose top-level roots carry row-1 `≤ m` is in `W_m`".

Every standard form has finitely many row-1 values (`oper_snd_subset`,
`Mechanized.lean:552`, shows they never increase), so the level `u` exists. -/
theorem W_membership : ∀ M : PairSeq, ST_PS M → ∃ u : ℕ, M ∈ W u := by
  sorry

/-! ## 5. Assembly -/

/-- **From the two pillars to well-foundedness.**  Cofinality (pillar 1,
`YAPSS/Cofinality.lean`) plus `W`-membership (pillar 2, `W_membership`) give
well-foundedness of `olt` restricted to `ST_PS` images — the statement the whole
ordinal-free route is aiming at. -/
theorem wf_of_cofinality_and_membership
    (hcof : ∀ {M N : PairSeq}, ST_PS M → ST_PS N → translate N <o translate M →
      ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧))
    (hmem : ∀ M : PairSeq, ST_PS M → ∃ u : ℕ, M ∈ W u) :
    WellFounded Rst := by
  refine WellFounded.intro (fun M => ?_)
  by_cases hM : ST_PS M
  · obtain ⟨u, hu⟩ := hmem M hM
    exact acc_of_W hcof u M hu
  · exact Acc.intro M fun y hy => absurd hy.2.1 hM

/-- The same statement with both pillars in their intended final form: the goal
relation written out. -/
theorem wf_olt_ST_PS_of_cofinality
    (hcof : ∀ {M N : PairSeq}, ST_PS M → ST_PS N → translate N <o translate M →
      ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧)) :
    WellFounded (fun a b : PairSeq => ST_PS a ∧ ST_PS b ∧ translate a <o translate b) :=
  wf_of_cofinality_and_membership hcof W_membership

/-! ## 6. REPORT — what is GREEN, what is open, and where the danger is

### GREEN (`sorryAx`-free, checked by the `#print axioms` below)

* the whole `A_u` / `W_u` apparatus: `Wf` (iterated stages), `W`, `W_unfold`,
  (A1) `A1`, (A2) `A2` / `A2'`, `A1_intro`, `A1_dest`, level monotonicity
  `W_mono`, the atoms `W_nil` / `W_atom`;
* the **design validation** `hasParent_one_iff` — PSS's own `hasParent … 1 …`
  really is Buchholz's spine condition — and its packaging `domT_iff`;
* `oper_eq_graft_nil_of_domT`: in the `T_m` branch PSS's `oper` degenerates to
  the bottom element `graft M [] = M.dropLast` of the `T_m`-indexed family;
* the **bridge** `acc_of_W` (deliverable 3) and the assembly
  `wf_of_cofinality_and_membership` (deliverable 5), modulo their explicit
  hypotheses.  The bridge needs `hcof` and **nothing else** — in particular no
  second, `T_m`-indexed cofinality statement.

### OPEN (the single `sorry`)

`W_membership` (deliverable 4).  Believed TRUE: it is the transplant of
Buchholz (1987) 2.8, which is a theorem, and the dictionary above is validated
piecewise here.  It is *not* circular (header §(c)).

### DANGER FLAGS — read before attempting `W_membership`

1. **`H0clause`-shaped coefficient domination may reappear in 2.4(b).**  The
   source's additive closure `a, b ∈ W_v ⟹ a + b ∈ W_v` is cheap there because
   `+` is only ever formed inside `OT_B`, whose *definition* already carries the
   CNF/coefficient-domination condition (`isOT_BT`).  Natively in PSS the
   analogue is "`A, B ∈ W_u ⟹ A ++ (B re-based) ∈ W_u`", and the re-basing has
   a genuine side condition — the appended block's roots must not be swallowed
   by `A`'s trailing subtree.  That side condition is exactly the shape of the
   project's open `Wttone.H0clause_oper_step` / `Gterm` domination facts.  **If
   a `W_u`-additivity lemma is attempted, check first whether its hypothesis is
   `H0clause` in disguise; if so the route has not gained anything and the
   membership proof must be re-planned around it.**  (The *bridge* is free of
   this — flagged so nobody assumes the whole route is.)
2. **The `based` side condition is load-bearing, not cosmetic.**  §1c above
   machine-checks a concrete failure: `[(0,0)]` and `[(2,0)]` have the same
   `translate`, but grafting the second into `M = (0,3)(1,2)(1,1)` produces
   `p₃(p₂(p₀(0)))` instead of `p₃(p₂(0) + p₀(0))`.  Any strengthening of the
   `T_m` branch must keep the `based z` guard, or `W_u` collapses to something
   for which `W_membership` is FALSE.
3. **`translate (graft M z)` is not yet related to term substitution.**  The
   membership route needs a lemma of the form "for `domT M m` and `based z`,
   `translate (graft M z)` is `translate M` with its trailing `Ω_{m+1}` replaced
   by `translate z`".  It is stated nowhere in this file and is a prerequisite
   for 2.6.  It should be provable from the `translate_block_append` /
   `translate_ctx_cong` family in `Mechanized.lean`, but it is real work.
4. **`ST_PS` forms are never `domT`.**  The bridge only uses the weak
   consequence "length-1 standard forms are `[(0,0)]`" (`stps_head`).  The
   stronger invariant — every top-level root of a standard form carries row-1
   `= 0`, hence `dom(translate M) ∈ {∅, {0}, ℕ}` for every standard form — is
   true and provable by `ST_PS` induction, and would be worth having if the
   `T_m` branch ever needs to be used on standard forms.
-/

#print axioms hasParent_one_iff
#print axioms domT_iff
#print axioms A1
#print axioms A2'
#print axioms W_mono
#print axioms W_nil
#print axioms oper_eq_graft_nil_of_domT
#print axioms acc_of_W
#print axioms wf_of_cofinality_and_membership

end Wset

end YAPSS
