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

**`sorry`-free.  Zero named assumptions beyond the single explicit `hcof`.**

```
#print axioms YAPSS.Wset.wf_olt_ST_PS_of_cofinality
  -- [propext, Classical.choice, Quot.sound]
```

i.e. pillar 2 is complete:

    PSS Bachmann cofinality  (hcof, = YAPSS/Cofinality.lean, pillar 1)
      ⟹  WellFounded (fun a b => ST_PS a ∧ ST_PS b ∧ translate a <o translate b)

The route is the full Buchholz (1987) §2 transplant:

* `Wf` / `W` (iterated stages), (A1), (A2), (A2'), `W_mono`, `W_nil`, `W_atom`;
* the design-validation theorems `hasParent_one_iff` / `hasParent_zero_iff` /
  `domT_iff` — PSS's own `hasParent` predicates **are** Buchholz's spine
  conditions;
* block algebra: `oper_shift` (row-0-shift equivariance of `oper`), `W_shift`,
  `split_lastMin`, `oper_append_gen`, `graft_append`, `domT_append`,
  `hasParent_append_gen`, `le0_cons_zero`;
* the four-case classification of `oper` on a principal block `(0,v) :: R`:
  `oper_cons_succ` (A′), `oper_cons_nat` (B′C′), `oper_cons_tower` (D′, the
  tower `(D_v b)[n] = D_v(b[x_n])`), `domT_cons_of_lt` (E′);
* **2.4(a)/(b)** `XA_closed` / `W_add`, **2.5** `Om_mem_W`, **2.6**
  `Wstar_closed`, **2.7** `mem_of_Aclosed`, **2.8** `mem_Wstar`, the level bound
  `mem_W_of_bound` / `mem_W_maxr1`, and **`W_membership`**;
* the **bridge** `acc_of_W` and the assembly `wf_of_cofinality_and_membership` /
  `wf_olt_ST_PS_of_cofinality`.

No `native_decide`, no `admit`.  **§9 at the bottom of the file is the report.**
Notably the feared `H0clause`-shaped coefficient domination never appeared: PSS
`Three`-addition is unconditional (`translate` has no CNF side condition built
in), so the additive closure 2.4(b) needs only the *positional* guard `rsum`.
-/
import Column
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Induction

namespace YAPSS
open Three

namespace Wset

/-! ## 0. Small facts about `translate`, `ST_PS` and `oper` -/

/-- `translate` is `Z` only on the empty sequence. -/
theorem translate_eq_Z_iff {M : PairSeq} : translate M = Z ↔ M = [] := by
  cases M with
  | nil => simp
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

/-- **`dom(M) ∈ {∅, {0}, ℕ}`** — the negation of `Ω`-cofinality.  This is the
guard on the ℕ-branch of `A_u`, mirroring Buchholz's `dom c ∈ {{0}, ℕ_B}`.  It is
load-bearing: without it the `T_m` branch and the ℕ branch could both fire on an
`Ω_{m+1}`-cofinal block, and the ℕ branch (which PSS truncates to `graft M []`)
carries far too little information to run the 2.6 tower. -/
def natDom (M : PairSeq) : Prop := ∀ m : ℕ, ¬ domT M m

theorem natDom_iff {M : PairSeq} :
    natDom M ↔ (entry M 1 (M.length - 1) = 0 ∨ hasParent M 1 (M.length - 1)) := by
  constructor
  · intro h
    by_cases hz : entry M 1 (M.length - 1) = 0
    · exact Or.inl hz
    · refine Or.inr ?_
      by_contra hp
      obtain ⟨m, hm⟩ : ∃ m, entry M 1 (M.length - 1) = m + 1 :=
        ⟨entry M 1 (M.length - 1) - 1, by omega⟩
      exact h m ⟨hm, hp⟩
  · rintro (hz | hp) m ⟨hw, hnp⟩
    · omega
    · exact hnp hp

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
  (natDom M ∧ ∀ n : ℕ, 1 ≤ n → M⟦n⟧ ∈ X) ∨
  (∃ m : ℕ, m < u ∧ domT M m ∧ ∀ z ∈ Wfam m, based z → graft M z ∈ X)

def Aset (Wfam : ℕ → Set PairSeq) (u : ℕ) (X : Set PairSeq) : Set PairSeq :=
  {M | Aop Wfam u X M}

theorem Aop_mono_X {Wfam : ℕ → Set PairSeq} {u : ℕ} {X Y : Set PairSeq} {M : PairSeq}
    (h : Aop Wfam u X M) (hXY : X ⊆ Y) : Aop Wfam u Y M := by
  rcases h with h | h | ⟨m, hm, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h.1, fun n hn => hXY (h.2 n hn)⟩)
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

/-- (W1) `0 ∈ W_u`. -/
theorem W_nil (u : ℕ) : ([] : PairSeq) ∈ W u :=
  A1_intro (Or.inl ⟨by simp, by simp [entry]⟩)

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
    rcases A with ⟨hlen, hw⟩ | ⟨-, hnat⟩ | ⟨m, -, hd, hgr⟩
    · -- branch 1: `translate c = p₀(0) = 1`; only `0` is below, and `0 ∉ ST_PS`.
      have hlen1 : c.length = 1 := by
        have := stps_len_pos hc; omega
      obtain ⟨p, rfl⟩ : ∃ p, c = [p] := by
        match c, hlen1 with
        | [p], _ => exact ⟨p, rfl⟩
      have hp2 : p.2 = 0 := by simpa [entry] using hw
      have ht : translate [p] = P 0 Z Z := by
        rw [translate]; simp [hp2]
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

/-! ## 4. Block algebra for the membership route (Buchholz 2.4–2.8)

The membership proof needs the PSS analogue of Buchholz's *term algebra*: sums
(list concatenation of top-level trees) and principal terms (`(c,v) :: R`).  This
section builds the three tools the source gets for free from `BT`:

* **shift-equivariance** of `oper` / `graft` / `domT` (`translate` never sees a
  uniform row-0 shift, and neither does `W`);
* the **last-minimum split** `M = A ++ P` into "everything but the last top-level
  tree" and "the last top-level tree";
* the **prefix-commutation** `(A ++ P)⟦n⟧ = A ++ P⟦n⟧` for such a split, which is
  `Nrm.oper_append_right` transported by the shift. -/

/-- `R` is an *argument block*: every entry sits strictly below depth `0`, i.e.
`R` is the descendant block of a root at depth `0`. -/
def argOK (R : PairSeq) : Prop := ∀ p ∈ R, 0 < p.1

/-- `P` is a genuine **top-level suffix** of `A ++ P`: `P`'s first entry sits at
the minimum row-0 depth of the whole sequence.  This is exactly the hypothesis
under which `oper`, `graft` and `domT` commute with the prefix `A`. -/
def rsum (A P : PairSeq) : Prop := ∀ p ∈ A ++ P, entry P 0 0 ≤ p.1

/-! ### 4a. Shift-equivariance -/

/-- `nextR` is row-0-shift invariant. -/
theorem nextR_shift_iff {S : PairSeq} {d i a b : ℕ} (hb : b < S.length) :
    nextR (S.map fun p => (p.1 + d, p.2)) i a b ↔ nextR S i a b := by
  unfold nextR
  split
  · exact nextrel0_shift_iff hb
  · exact nextrel1_shift_iff hb

theorem hasParent_shift {S : PairSeq} {d i b : ℕ} (hb : b < S.length) :
    hasParent (S.map fun p => (p.1 + d, p.2)) i b ↔ hasParent S i b := by
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, (nextR_shift_iff hb).mp hj0,
      fun y hy => hu y ((nextR_shift_iff hb).mpr hy)⟩
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, (nextR_shift_iff hb).mpr hj0,
      fun y hy => hu y ((nextR_shift_iff hb).mp hy)⟩

theorem parent_shift {S : PairSeq} {d i b : ℕ} (hb : b < S.length) :
    parent (S.map fun p => (p.1 + d, p.2)) i b = parent S i b := by
  unfold parent
  congr 1
  funext j0
  exact propext (nextR_shift_iff hb)

/-- **`oper` is row-0-shift equivariant.**  Every test `oper` performs is either
shift-invariant (row-1 values, `idx1`, `hasParent`, index arithmetic) or a
difference of row-0 values (`d0`); the one non-invariant test — "is the last pair
`(0,0)`?" — is redundant, because a row-0-`0` column has no parent at all
(`no_hasParent_of_row0_zero`), so both readings land in the same `Pred` branch. -/
theorem oper_shift (M : PairSeq) (d n : ℕ) :
    (M.map fun p => (p.1 + d, p.2))⟦n⟧ = (M⟦n⟧).map (fun p => (p.1 + d, p.2)) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n (by simpa using hL), oper_eq_self_of_short n hL]
  · have hlt : M.length - 1 < M.length := by omega
    have hlenmap : (M.map fun p => (p.1 + d, p.2)).length - 1 = M.length - 1 := by simp
    have hLm : (M.map fun p => (p.1 + d, p.2)).length - 1 ≠ 0 := by simpa using hL
    have hidx : idx1 (M.map fun p => (p.1 + d, p.2)) (M.length - 1)
        = idx1 M (M.length - 1) := idx1_shift
    by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
    · -- bad branch on both sides
      have hpos : 0 < entry M 0 (M.length - 1) := by
        by_contra h
        exact no_hasParent_of_row0_zero (by omega) hp
      have hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0) := by
        rintro ⟨h1, -⟩; omega
      have hpM : hasParent (M.map fun p => (p.1 + d, p.2))
          (idx1 (M.map fun p => (p.1 + d, p.2))
            ((M.map fun p => (p.1 + d, p.2)).length - 1))
          ((M.map fun p => (p.1 + d, p.2)).length - 1) := by
        rw [hlenmap, hidx]; exact (hasParent_shift hlt).mpr hp
      have hzM : ¬ (entry (M.map fun p => (p.1 + d, p.2)) 0
            ((M.map fun p => (p.1 + d, p.2)).length - 1) = 0 ∧
          entry (M.map fun p => (p.1 + d, p.2)) 1
            ((M.map fun p => (p.1 + d, p.2)).length - 1) = 0) := by
        rw [hlenmap]
        rintro ⟨h1, -⟩
        rw [(entry_shift (d := d) hlt).1] at h1
        omega
      rw [oper_bad_unfold n hLm hzM hpM, oper_bad_unfold n hL hz hp,
        hlenmap, hidx, parent_shift hlt]
      set j0 := parent M (idx1 M (M.length - 1)) (M.length - 1) with hj0
      have hj0lt : j0 < M.length - 1 := nextR_index_lt (parent_nextR hp)
      have hd0 : entry (M.map fun p => (p.1 + d, p.2)) 0 (M.length - 1) -
            entry (M.map fun p => (p.1 + d, p.2)) 0 j0
          = entry M 0 (M.length - 1) - entry M 0 j0 := by
        rw [(entry_shift (d := d) hlt).1, (entry_shift (d := d) (j := j0) (by omega)).1,
          Nat.add_sub_add_right]
      rw [hd0, List.map_append, List.map_take, List.map_flatMap]
      refine congrArg _ (List.flatMap_congr ?_)
      intro k _
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro j hj
      have hjlt : j < M.length := by
        rw [List.mem_range'] at hj
        omega
      simp only [Function.comp_apply, (entry_shift (d := d) hjlt).1,
        (entry_shift (d := d) hjlt).2, Prod.mk.injEq]
      exact ⟨Nat.add_right_comm _ _ _, trivial⟩
    · -- `Pred` on both sides
      have hpM : ¬ hasParent (M.map fun p => (p.1 + d, p.2))
          (idx1 (M.map fun p => (p.1 + d, p.2))
            ((M.map fun p => (p.1 + d, p.2)).length - 1))
          ((M.map fun p => (p.1 + d, p.2)).length - 1) := by
        rw [hlenmap, hidx]
        intro hh
        exact hp ((hasParent_shift hlt).mp hh)
      have hM : M⟦n⟧ = Pred M := by
        by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
        · exact oper_eq_pred_of_zero n hL hz
        · exact oper_eq_pred_of_noParent n hL hz hp
      have hMm : (M.map fun p => (p.1 + d, p.2))⟦n⟧
          = Pred (M.map fun p => (p.1 + d, p.2)) := by
        by_cases hz : entry (M.map fun p => (p.1 + d, p.2)) 0
              ((M.map fun p => (p.1 + d, p.2)).length - 1) = 0 ∧
            entry (M.map fun p => (p.1 + d, p.2)) 1
              ((M.map fun p => (p.1 + d, p.2)).length - 1) = 0
        · exact oper_eq_pred_of_zero n hLm hz
        · exact oper_eq_pred_of_noParent n hLm hz hpM
      rw [hM, hMm]
      unfold Pred
      rw [List.length_map, if_neg (by omega), if_neg (by omega), List.map_dropLast]

theorem domT_shift {M : PairSeq} {d m : ℕ} :
    domT (M.map fun p => (p.1 + d, p.2)) m ↔ domT M m := by
  rcases M with _ | ⟨p, rest⟩
  · simp [domT, entry]
  · have hlt : (p :: rest).length - 1 < (p :: rest).length := by simp
    unfold domT
    rw [List.length_map, (entry_shift (d := d) hlt).2, hasParent_shift hlt]

theorem natDom_shift {M : PairSeq} {d : ℕ} :
    natDom (M.map fun p => (p.1 + d, p.2)) ↔ natDom M :=
  ⟨fun h m hm => h m (domT_shift.mpr hm), fun h m hm => h m (domT_shift.mp hm)⟩

theorem graft_shift {M : PairSeq} (hM : M ≠ []) (z : PairSeq) (d : ℕ) :
    graft (M.map fun p => (p.1 + d, p.2)) z
      = (graft M z).map (fun p => (p.1 + d, p.2)) := by
  have hlt : M.length - 1 < M.length := by
    have : 0 < M.length := List.length_pos_iff.mpr hM
    omega
  unfold graft
  rw [List.length_map, (entry_shift (d := d) hlt).1, List.map_append,
    ← List.map_dropLast, List.map_map]
  refine congrArg _ (List.map_congr_left ?_)
  intro q _
  simp only [Function.comp_apply, Nat.add_assoc]

/-- **`W_u` is row-0-shift closed.**  `A_u` is shift-equivariant branch by
branch, so this is a one-line `A2'`. -/
theorem W_shift {u : ℕ} {M : PairSeq} (h : M ∈ W u) (d : ℕ) :
    (M.map fun p => (p.1 + d, p.2)) ∈ W u := by
  revert h
  show M ∈ W u → _
  have : W u ⊆ {N : PairSeq | (N.map fun p => (p.1 + d, p.2)) ∈ W u} := by
    refine A2' ?_
    intro N A
    refine A1_intro ?_
    rcases A with ⟨hl, hw⟩ | ⟨hnat, hop⟩ | ⟨m, hm, hd, hgr⟩
    · refine Or.inl ⟨by simpa using hl, ?_⟩
      rcases N with _ | ⟨p, rest⟩
      · simp [entry]
      · simpa [entry] using hw
    · exact Or.inr (Or.inl ⟨natDom_shift.mpr hnat, fun n hn => by
        rw [oper_shift]; exact hop n hn⟩)
    · refine Or.inr (Or.inr ⟨m, hm, domT_shift.mpr hd, fun z hz hb => ?_⟩)
      have hne : N ≠ [] := by rintro rfl; exact not_domT_nil m hd
      rw [graft_shift hne]; exact hgr z hz hb
  exact fun h => this h

/-! ### 4b. The last-minimum split -/

/-- Every nonempty block splits as `A ++ P` where `P` is its **last top-level
tree**: `P`'s head sits at the minimum depth of the whole block and everything
after that head is strictly deeper. -/
theorem split_lastMin : ∀ {M : PairSeq}, M ≠ [] →
    ∃ A P, M = A ++ P ∧ P ≠ [] ∧ rsum A P ∧ (∀ p ∈ P.tail, entry P 0 0 < p.1) := by
  intro M
  induction M using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton M' q ih =>
      intro _
      by_cases hM' : M' = []
      · subst hM'
        refine ⟨[], [q], by simp, by simp, ?_, by simp⟩
        intro p hp
        simp only [List.nil_append, List.mem_singleton] at hp
        subst hp
        simp [entry]
      · obtain ⟨A', P', hEq, hPne, hrs, htail⟩ := ih hM'
        by_cases hq : q.1 ≤ entry P' 0 0
        · refine ⟨M', [q], by simp, by simp, ?_, by simp⟩
          intro p hp
          have hq0 : entry ([q] : PairSeq) 0 0 = q.1 := by simp [entry]
          rw [hq0]
          rcases List.mem_append.mp hp with hp | hp
          · exact le_trans hq (hrs p (by rw [hEq] at hp; exact hp))
          · simp only [List.mem_singleton] at hp; subst hp; exact le_rfl
        · push Not at hq
          refine ⟨A', P' ++ [q], by rw [hEq, List.append_assoc], by simp, ?_, ?_⟩
          · have hhd : entry (P' ++ [q]) 0 0 = entry P' 0 0 := by
              rcases P' with _ | ⟨p0, P''⟩
              · exact absurd rfl hPne
              · simp [entry]
            intro p hp
            rw [hhd]
            rcases List.mem_append.mp hp with hp | hp
            · exact hrs p (List.mem_append_left _ hp)
            · rcases List.mem_append.mp hp with hp | hp
              · exact hrs p (List.mem_append_right _ hp)
              · simp only [List.mem_singleton] at hp; subst hp; omega
          · have hhd : entry (P' ++ [q]) 0 0 = entry P' 0 0 := by
              rcases P' with _ | ⟨p0, P''⟩
              · exact absurd rfl hPne
              · simp [entry]
            intro p hp
            rw [hhd]
            rcases P' with _ | ⟨p0, P''⟩
            · exact absurd rfl hPne
            · simp only [List.cons_append, List.tail_cons] at hp
              rcases List.mem_append.mp hp with hp | hp
              · exact htail p (by simpa using hp)
              · simp only [List.mem_singleton] at hp; subst hp; exact hq

/-! ### 4c. Prefix commutation -/

/-- `X.map (· - c) |>.map (· + c) = X` when every depth of `X` is `≥ c`. -/
theorem map_sub_add {c : ℕ} {X : PairSeq} (h : ∀ p ∈ X, c ≤ p.1) :
    (X.map fun p => (p.1 - c, p.2)).map (fun p => (p.1 + c, p.2)) = X := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id X]
  refine List.map_congr_left ?_
  intro q hq
  have hc := h q hq
  have h1 : q.1 - c + c = q.1 := by omega
  simp only [Function.comp_apply, id_eq, h1]

/-- The shift decomposition of a top-level split: `A ++ P` is the `c`-shift of a
root-anchored append, where `c = entry P 0 0` is the minimal depth. -/
theorem rsum_decomp {A P : PairSeq} (h : rsum A P) :
    ((A.map fun p => (p.1 - entry P 0 0, p.2)) ++
      (P.map fun p => (p.1 - entry P 0 0, p.2))).map (fun p => (p.1 + entry P 0 0, p.2))
      = A ++ P := by
  rw [List.map_append, map_sub_add (fun p hp => h p (List.mem_append_left _ hp)),
    map_sub_add (fun p hp => h p (List.mem_append_right _ hp))]

theorem entry_sub_zero {P : PairSeq} (hP : P ≠ []) :
    entry (P.map fun p => (p.1 - entry P 0 0, p.2)) 0 0 = 0 := by
  rcases P with _ | ⟨p0, P'⟩
  · exact absurd rfl hP
  · simp [entry]

/-- **Prefix commutation for a top-level split** (the shift-general form of
`Nrm.oper_append_right`). -/
theorem oper_append_gen {A P : PairSeq} (n : ℕ) (hP : 2 ≤ P.length) (h : rsum A P) :
    (A ++ P)⟦n⟧ = A ++ P⟦n⟧ := by
  set c := entry P 0 0 with hc
  set A₀ := A.map (fun p => (p.1 - c, p.2)) with hA0
  set P₀ := P.map (fun p => (p.1 - c, p.2)) with hP0
  have hPne : P ≠ [] := by rintro rfl; simp at hP
  have hroot : entry P₀ 0 0 = 0 := entry_sub_zero hPne
  have hlen0 : 2 ≤ P₀.length := by rw [hP0, List.length_map]; exact hP
  have hAP : (A₀ ++ P₀).map (fun p => (p.1 + c, p.2)) = A ++ P := rsum_decomp h
  have hPP : P₀.map (fun p => (p.1 + c, p.2)) = P :=
    map_sub_add (fun p hp => h p (List.mem_append_right _ hp))
  have hAA : A₀.map (fun p => (p.1 + c, p.2)) = A :=
    map_sub_add (fun p hp => h p (List.mem_append_left _ hp))
  calc (A ++ P)⟦n⟧ = ((A₀ ++ P₀).map (fun p => (p.1 + c, p.2)))⟦n⟧ := by rw [hAP]
    _ = ((A₀ ++ P₀)⟦n⟧).map (fun p => (p.1 + c, p.2)) := oper_shift _ _ _
    _ = (A₀ ++ P₀⟦n⟧).map (fun p => (p.1 + c, p.2)) := by
          rw [oper_append_right A₀ P₀ n hlen0 hroot]
    _ = A ++ (P₀⟦n⟧).map (fun p => (p.1 + c, p.2)) := by rw [List.map_append, hAA]
    _ = A ++ P⟦n⟧ := by rw [← oper_shift, hPP]

theorem graft_append {A P z : PairSeq} (hP : P ≠ []) :
    graft (A ++ P) z = A ++ graft P z := by
  have hlen : (A ++ P).length - 1 = A.length + (P.length - 1) := by
    have : 0 < P.length := List.length_pos_iff.mpr hP
    rw [List.length_append]; omega
  unfold graft
  rw [hlen, entry_append_right, List.dropLast_append_of_ne_nil hP, List.append_assoc]

/-- `hasParent` is invariant under a prefix, for a genuine top-level split. -/
theorem hasParent_append_gen {A P : PairSeq} {i j : ℕ} (hj : j < P.length)
    (h : rsum A P) : hasParent (A ++ P) i (A.length + j) ↔ hasParent P i j := by
  have hPne : P ≠ [] := by rintro rfl; simp at hj
  set c := entry P 0 0 with hc
  set A₀ := A.map (fun p => (p.1 - c, p.2)) with hA0
  set P₀ := P.map (fun p => (p.1 - c, p.2)) with hP0
  have hroot : entry P₀ 0 0 = 0 := entry_sub_zero hPne
  have hAP : (A₀ ++ P₀).map (fun p => (p.1 + c, p.2)) = A ++ P := rsum_decomp h
  have hPP : P₀.map (fun p => (p.1 + c, p.2)) = P :=
    map_sub_add (fun p hp => h p (List.mem_append_right _ hp))
  have hlenA : A₀.length = A.length := by rw [hA0, List.length_map]
  have hlenP : P₀.length = P.length := by rw [hP0, List.length_map]
  have hbound : A.length + j < (A₀ ++ P₀).length := by
    rw [List.length_append, hlenA, hlenP]; omega
  have step1 : hasParent (A ++ P) i (A.length + j) ↔ hasParent (A₀ ++ P₀) i (A₀.length + j) := by
    rw [hlenA, ← hAP]
    exact hasParent_shift hbound
  have step3 : hasParent P₀ i j ↔ hasParent P i j := by
    rw [← hPP]
    exact (hasParent_shift (S := P₀) (d := c) (i := i) (b := j)
      (by rw [hlenP]; exact hj)).symm
  have step2 : hasParent (A₀ ++ P₀) i (A₀.length + j) ↔ hasParent P₀ i j := by
    by_cases hz : entry P₀ 0 j = 0
    · constructor
      · intro hh
        exact absurd hh (fun hh' => no_hasParent_of_row0_zero
          (by rw [entry_append_right]; exact hz) hh')
      · intro hh
        exact absurd hh (fun hh' => no_hasParent_of_row0_zero hz hh')
    · exact hasParent_append_right A₀ P₀ hroot
        (by rw [entry_append_right]; omega)
  rw [step1, step2, step3]

theorem domT_append {A P : PairSeq} {m : ℕ} (hP : P ≠ []) (h : rsum A P) :
    domT (A ++ P) m ↔ domT P m := by
  have hPlen : 0 < P.length := List.length_pos_iff.mpr hP
  have hlen : (A ++ P).length - 1 = A.length + (P.length - 1) := by
    rw [List.length_append]; omega
  unfold domT
  rw [hlen, entry_append_right, hasParent_append_gen (by omega) h]

theorem natDom_append {A P : PairSeq} (hP : P ≠ []) (h : rsum A P) :
    natDom (A ++ P) ↔ natDom P :=
  ⟨fun hn m hm => hn m ((domT_append hP h).mpr hm),
   fun hn m hm => hn m ((domT_append hP h).mp hm)⟩

/-! ## 5. Buchholz 2.4 — additive closure

`X⁽ᴬ⁾ = {B | A ++ B ∈ X}`, guarded by `rsum A B` (the PSS side condition that
`B` really is a top-level suffix; in the source this is free because `+` is only
formed inside `OT_B`, whose definition already carries it). -/

/-- Buchholz's `X^{(a)}`, with the PSS top-level-suffix guard. -/
def XA (A : PairSeq) (X : Set PairSeq) : Set PairSeq := {B | rsum A B → A ++ B ∈ X}

/-! ### Depth bookkeeping: `oper` and `graft` never go shallower -/

theorem entry_zero_headD (X : PairSeq) : entry X 0 0 = (X.headD (0, 0)).1 := by
  cases X <;> simp [entry]

/-- `oper` keeps the head (hence the anchoring depth) for `n ≥ 1`. -/
theorem oper_head_eq {B : PairSeq} {n : ℕ} (hn : 1 ≤ n) :
    entry (B⟦n⟧) 0 0 = entry B 0 0 := by
  by_cases hL : 1 < B.length
  · rw [entry_zero_headD, entry_zero_headD, oper_headD B hL hn]
  · rw [oper_eq_self_of_short n (by omega)]

/-- The `j`-th column of `B` really is a member of `B`. -/
theorem entry_pair_mem {B : PairSeq} {j : ℕ} (hj : j < B.length) :
    ((entry B 0 j, entry B 1 j) : ℕ × ℕ) ∈ B := by
  have h : ((entry B 0 j, entry B 1 j) : ℕ × ℕ) = B.getD j (0, 0) := by
    unfold entry; rw [if_pos rfl, if_neg one_ne_zero]
  have h2 : B.getD j (0, 0) = B[j]'hj := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  rw [h, h2]
  exact List.getElem_mem hj

/-- `oper` never produces a column shallower than the shallowest column of `B`. -/
theorem oper_mem_ge {B : PairSeq} {c n : ℕ} (h : ∀ p ∈ B, c ≤ p.1) :
    ∀ p ∈ B⟦n⟧, c ≤ p.1 := by
  by_cases hL : B.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]; exact h
  · by_cases hp : hasParent B (idx1 B (B.length - 1)) (B.length - 1)
    · have hpos : 0 < entry B 0 (B.length - 1) := by
        by_contra hh
        exact no_hasParent_of_row0_zero (by omega) hp
      have hz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0) := by
        rintro ⟨h1, -⟩; omega
      rw [oper_bad_unfold n hL hz hp]
      intro p hp'
      rcases List.mem_append.mp hp' with hmem | hmem
      · exact h p (List.mem_of_mem_take hmem)
      · rw [List.mem_flatMap] at hmem
        obtain ⟨k, -, hmem2⟩ := hmem
        rw [List.mem_map] at hmem2
        obtain ⟨j, hj, rfl⟩ := hmem2
        rw [List.mem_range'] at hj
        have hjlt : j < B.length := by omega
        have := h _ (entry_pair_mem hjlt)
        simp only []
        omega
    · have hB : B⟦n⟧ = Pred B := by
        by_cases hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0
        · exact oper_eq_pred_of_zero n hL hz
        · exact oper_eq_pred_of_noParent n hL hz hp
      rw [hB]
      unfold Pred
      split
      · exact h
      · exact fun p hp' => h p (List.dropLast_subset _ hp')

/-- `graft` never produces a column shallower than the shallowest column of `B`
(the grafted block is re-based at `B`'s deepest column). -/
theorem graft_mem_ge {B z : PairSeq} {c : ℕ} (hB : B ≠ []) (h : ∀ p ∈ B, c ≤ p.1) :
    ∀ p ∈ graft B z, c ≤ p.1 := by
  have hlt : B.length - 1 < B.length := by
    have : 0 < B.length := List.length_pos_iff.mpr hB
    omega
  have hx : c ≤ entry B 0 (B.length - 1) := h _ (entry_pair_mem hlt)
  intro p hp
  rcases List.mem_append.mp hp with hmem | hmem
  · exact h p (List.dropLast_subset _ hmem)
  · rw [List.mem_map] at hmem
    obtain ⟨q, -, rfl⟩ := hmem
    simp only []
    omega

/-- `graft` keeps the anchoring depth (whenever the result is nonempty). -/
theorem graft_head_eq {B z : PairSeq} (hB : B ≠ []) (hz : based z)
    (hne : graft B z ≠ []) : entry (graft B z) 0 0 = entry B 0 0 := by
  rcases hB2 : B with _ | ⟨b0, B'⟩
  · exact absurd hB2 hB
  · rcases B' with _ | ⟨b1, B''⟩
    · have hgr : graft [b0] z = z.map (fun p => (p.1 + b0.1, p.2)) := by simp [graft, entry]
      rw [hB2] at hne
      rw [hgr] at hne ⊢
      rcases z with _ | ⟨z0, z'⟩
      · simp at hne
      · have h0 : entry (z0 :: z') 0 0 = 0 := hz
        simp [entry] at h0 ⊢
        omega
    · simp [graft, entry]

/-- **2.4(a)**: `A_u(X) ⊆ X` and `A ∈ X` imply `A_u(X⁽ᴬ⁾) ⊆ X⁽ᴬ⁾`. -/
theorem XA_closed {u : ℕ} {X : Set PairSeq}
    (hX : ∀ M : PairSeq, Aop W u X M → M ∈ X) {A : PairSeq} (hA : A ∈ X) :
    ∀ M : PairSeq, Aop W u (XA A X) M → M ∈ XA A X := by
  intro B AB hrs
  by_cases hBnil : B = []
  · subst hBnil; simpa using hA
  · have hBlen : 0 < B.length := List.length_pos_iff.mpr hBnil
    have hBge : ∀ p ∈ B, entry B 0 0 ≤ p.1 := fun p hp => hrs p (List.mem_append_right _ hp)
    have hAge : ∀ p ∈ A, entry B 0 0 ≤ p.1 := fun p hp => hrs p (List.mem_append_left _ hp)
    rcases AB with ⟨hl, hw⟩ | ⟨hnat, hop⟩ | ⟨m, hm, hd, hgr⟩
    · -- branch 1: `B = [q]` with row-1 `0`; `A ++ [q]` drops back to `A`
      have hB1 : B.length = 1 := by omega
      by_cases hAnil : A = []
      · subst hAnil; simpa using hX B (Or.inl ⟨hl, hw⟩)
      · have hAlen : 0 < A.length := List.length_pos_iff.mpr hAnil
        have hlast : (A ++ B).length - 1 = A.length + 0 := by
          rw [List.length_append]; omega
        have hnp : ∀ i, ¬ hasParent (A ++ B) i ((A ++ B).length - 1) := by
          intro i hh
          rw [hlast] at hh
          have := (hasParent_append_gen (i := i) (j := 0) (by omega) hrs).mp hh
          obtain ⟨j0, hj0, -⟩ := this
          exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
        have hw0 : entry (A ++ B) 1 ((A ++ B).length - 1) = 0 := by
          rw [hlast, entry_append_right]
          simpa using hw
        refine hX _ (Or.inr (Or.inl ⟨(natDom_append hBnil hrs).mpr
          (natDom_iff.mpr (Or.inl (by rw [show B.length - 1 = 0 by omega]; simpa using hw))),
          fun n hn => ?_⟩))
        have hpred : (A ++ B)⟦n⟧ = Pred (A ++ B) := by
          by_cases hzz : entry (A ++ B) 0 ((A ++ B).length - 1) = 0 ∧
              entry (A ++ B) 1 ((A ++ B).length - 1) = 0
          · exact oper_eq_pred_of_zero n (by rw [List.length_append]; omega) hzz
          · exact oper_eq_pred_of_noParent n (by rw [List.length_append]; omega) hzz (hnp _)
        rw [hpred]
        unfold Pred
        rw [if_neg (by rw [List.length_append]; omega),
          List.dropLast_append_of_ne_nil hBnil]
        have : B.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
        rw [this]
        simpa using hA
    · -- branch 2: the ℕ-branch commutes with the prefix
      by_cases hB2 : 2 ≤ B.length
      · refine hX _ (Or.inr (Or.inl ⟨(natDom_append hBnil hrs).mpr hnat, fun n hn => ?_⟩))
        rw [oper_append_gen n hB2 hrs]
        refine hop n hn (fun p hp => ?_)
        rw [oper_head_eq hn]
        rcases List.mem_append.mp hp with hp | hp
        · exact hAge p hp
        · exact oper_mem_ge hBge p hp
      · -- `|B| = 1`: `B⟦1⟧ = B`, so the branch already gives the goal
        have hB1 : B⟦1⟧ = B := oper_eq_self_of_short 1 (by omega)
        have h1 := hop 1 le_rfl
        rw [hB1] at h1
        exact h1 hrs
    · -- branch 3: the `T_m`-graft commutes with the prefix
      refine hX _ (Or.inr (Or.inr ⟨m, hm, (domT_append hBnil hrs).mpr hd, fun z hz hbz => ?_⟩))
      rw [graft_append hBnil]
      refine hgr z hz hbz ?_
      by_cases hgz : graft B z = []
      · rw [hgz]; intro p hp; simp [entry]
      · intro p hp
        rw [graft_head_eq hBnil hbz hgz]
        rcases List.mem_append.mp hp with hp | hp
        · exact hAge p hp
        · exact graft_mem_ge hBnil hBge p hp

/-- **2.4(b)**: `W_u` is closed under top-level concatenation. -/
theorem W_add {u : ℕ} {A B : PairSeq} (hA : A ∈ W u) (hB : B ∈ W u)
    (h : rsum A B) : A ++ B ∈ W u :=
  A2' (XA_closed (u := u) (X := W u) (fun _ hM => A1_intro hM) hA) hB h

/-! ## 6. Buchholz 2.5/2.6 — the principal step and the tower -/

/-- **2.5**: `Ω_v = p_v(0) = [(0,v)] ∈ W_v`.  For `v = 0` this is the atom `1`;
for `v > 0` it is the `T_{v-1}` branch with `graft [(0,v)] z = z`. -/
theorem graft_Om (v : ℕ) (z : PairSeq) : graft [((0 : ℕ), v)] z = z := by
  simp [graft, entry]

theorem domT_Om (m : ℕ) : domT [((0 : ℕ), m + 1)] m := by
  refine ⟨by simp [entry], ?_⟩
  rintro ⟨j0, hj0, -⟩
  unfold nextR at hj0
  rw [if_neg (by omega)] at hj0
  have := hj0.2.2.1
  simp at this

theorem Om_mem_W (v : ℕ) : [((0 : ℕ), v)] ∈ W v := by
  rcases v with _ | w
  · exact A1_intro (Or.inl ⟨by simp, by simp [entry]⟩)
  · refine A1_intro (Or.inr (Or.inr ⟨w, by omega, domT_Om w, ?_⟩))
    intro z hz _
    rw [graft_Om]
    exact W_mono (Nat.le_succ w) hz

/-- Buchholz's `W* = {x | ∀ u, D_u x ∈ W_u}`, PSS reading: an argument block `R`
is in `W*` when every principal `p_v(R)` lands in `W_v`. -/
def Wstar : Set PairSeq := {R | argOK R → ∀ v : ℕ, ((0, v) :: R) ∈ W v}

/-- The **tower**: `t_0 = 0`, `t_{k+1} = p_v(R[t_k])`.  This is Buchholz's
`x_0 = D_v 0`, `x_{i+1} = D_v(b[x_i])`; on the PSS side it is literally the
`n`-fold ascending copy/tiling of `oper_bad_blocks`. -/
def tow (v : ℕ) (R : PairSeq) : ℕ → PairSeq
  | 0 => []
  | k + 1 => (0, v) :: graft R (tow v R k)

theorem graft_cons {v : ℕ} {R z : PairSeq} (hRne : R ≠ []) :
    graft ((0, v) :: R) z = (0, v) :: graft R z := by
  have h := graft_append (A := [((0 : ℕ), v)]) (P := R) (z := z) hRne
  simp [List.cons_append] at h
  exact h

/-- Index shift across a `cons`. -/
theorem entry_cons (p : ℕ × ℕ) (R : PairSeq) (i j : ℕ) :
    entry (p :: R) i (j + 1) = entry R i j := by
  have h := entry_append_right [p] R i j
  simp only [List.length_singleton] at h
  rw [Nat.add_comm 1 j] at h
  exact h

/-! ### The four `oper`-on-a-principal-block cases

`M = (0,v) :: R` with `argOK R`.  Writing `x = entry R 0 (|R|-1) ≥ 1` and
`w = entry R 1 (|R|-1)`, the row-0 ancestor chain of `M`'s last column is `R`'s
own chain **extended by the root** `(0,v)` (which is below everything, by
`argOK`).  Hence exactly four cases, matching Buchholz's case split in 2.6:

| case | condition | `dom` | `oper`|
|---|---|---|---|
| (A′) | `w = 0`, no row-0 parent in `R` | successor | `n` exact copies of `p_v(R[0])` |
| (B′)(C′) | `R`'s last column has a parent in `R` | `ℕ` | `p_v(R⟦n⟧)` |
| (D′) | `domT R m`, `v ≤ m` | `ℕ` (collapsing) | the **tower** |
| (E′) | `domT R m`, `m < v` | `T_m` (continuous) | graft through the root |

All five are pure facts about PSS `oper`/`hasParent`; none of them mentions
`W`, `olt`, `translate` or any coefficient-domination condition. -/

/-! #### `cons`-transfer of the parent machinery

`Nrm`'s `*_append_right` family is *unconditional* on shifted indices, so with
the prefix `[p]` it gives every "column `j` of `R` becomes column `j+1` of
`p :: R`" transfer for free.  Only the **index-`0`** case (the root) needs new
work, and that is where `argOK` enters. -/

theorem nextR_cons (p : ℕ × ℕ) (R : PairSeq) (i j0 j1 : ℕ) :
    nextR (p :: R) i (j0 + 1) (j1 + 1) ↔ nextR R i j0 j1 := by
  have h := nextR_append_right [p] R i j0 j1
  simp only [List.length_singleton, List.singleton_append] at h
  rw [Nat.add_comm 1 j0, Nat.add_comm 1 j1] at h
  exact h

theorem le0_cons (p : ℕ × ℕ) (R : PairSeq) (j0 j1 : ℕ) :
    le0 (p :: R) (j0 + 1) (j1 + 1) ↔ le0 R j0 j1 := by
  have h := le0_append_right [p] R j0 j1
  simp only [List.length_singleton, List.singleton_append] at h
  rw [Nat.add_comm 1 j0, Nat.add_comm 1 j1] at h
  exact h

theorem idx1_cons (p : ℕ × ℕ) (R : PairSeq) (j : ℕ) :
    idx1 (p :: R) (j + 1) = idx1 R j := by
  have h := idx1_append_right [p] R j
  simp only [List.length_singleton, List.singleton_append] at h
  rw [Nat.add_comm 1 j] at h
  exact h

/-- Row-0 companion of `hasParent_one_iff`: a column has a row-0 parent iff some
earlier column is strictly shallower. -/
theorem hasParent_zero_iff {M : PairSeq} {b : ℕ} (hb : b < M.length) :
    hasParent M 0 b ↔ ∃ k, k < b ∧ entry M 0 k < entry M 0 b := by
  classical
  have nR : ∀ k : ℕ, nextR M 0 k b ↔ nextrel0 M k b := by
    intro k; unfold nextR; rw [if_pos rfl]
  constructor
  · rintro ⟨k, hk, -⟩
    have h := (nR k).mp hk
    exact ⟨k, h.2.2.1, h.2.2.2.1⟩
  · rintro ⟨k, hk1, hk2⟩
    set P : ℕ → Prop := fun t => t < b ∧ entry M 0 t < entry M 0 b with hP
    have hPg : P (Nat.findGreatest P b) := Nat.findGreatest_spec (m := k) (le_of_lt hk1) ⟨hk1, hk2⟩
    have hmax : ∀ t, P t → t ≤ Nat.findGreatest P b :=
      fun t ht => Nat.le_findGreatest (le_of_lt ht.1) ht
    refine ⟨Nat.findGreatest P b, (nR _).mpr ?_, ?_⟩
    · refine ⟨by omega, hb, hPg.1, hPg.2, ?_⟩
      intro l hl
      by_contra hcon
      exact absurd (hmax l ⟨hl.2, by omega⟩) (by omega)
    · intro y hy
      have hy' : nextrel0 M y b := (nR y).mp hy
      have hyP : P y := ⟨hy'.2.2.1, hy'.2.2.2.1⟩
      rcases eq_or_lt_of_le (hmax y hyP) with h | h
      · exact h
      · have := hy'.2.2.2.2 (Nat.findGreatest P b) ⟨h, hPg.1⟩
        have := hPg.2
        omega

/-- The root of a principal block is a row-0 ancestor of **every** column: by
`argOK` it is strictly shallower than all of them, so the ancestor chain from any
column descends all the way to index `0`. -/
theorem le0_cons_zero {v : ℕ} {R : PairSeq} (hR : argOK R) :
    ∀ j, j < R.length → le0 ((0, v) :: R) 0 (j + 1) := by
  have key : ∀ N j, j ≤ N → j < R.length → le0 ((0, v) :: R) 0 (j + 1) := by
    intro N
    induction N with
    | zero =>
        intro j hj hjR
        have hj0 : j = 0 := by omega
        subst hj0
        refine ⟨by simp, by simp; omega, ?_⟩
        refine Relation.ReflTransGen.single ?_
        refine ⟨by simp, by simp; omega, by omega, ?_, ?_⟩
        · rw [entry_cons]
          have := hR _ (entry_pair_mem (B := R) (j := 0) (by omega))
          simpa [entry] using this
        · intro l hl; omega
    | succ N ih =>
        intro j hj hjR
        have hbnd : j + 1 < ((0, v) :: R).length := by simp; omega
        have hpos : 0 < entry ((0, v) :: R) 0 (j + 1) := by
          rw [entry_cons]
          exact hR _ (entry_pair_mem (B := R) hjR)
        have hex : ∃ k, k < j + 1 ∧
            entry ((0, v) :: R) 0 k < entry ((0, v) :: R) 0 (j + 1) := by
          refine ⟨0, by omega, ?_⟩
          simpa [entry] using hpos
        obtain ⟨k, hk, -⟩ := (hasParent_zero_iff hbnd).mpr hex
        have hnk : nextrel0 ((0, v) :: R) k (j + 1) := by
          unfold nextR at hk; rwa [if_pos rfl] at hk
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          exact ⟨by simp, hbnd, Relation.ReflTransGen.single hnk⟩
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hklt : k' + 1 < j + 1 := hnk.2.2.1
          have hk'lt : k' < j := by omega
          have hk'R : k' < R.length := by omega
          obtain ⟨-, -, hchain⟩ := ih k' (by omega) hk'R
          exact ⟨by simp, hbnd, hchain.tail hnk⟩
  intro j hj
  exact key j j le_rfl hj

theorem len_succ {R : PairSeq} (hRne : R ≠ []) : R.length = (R.length - 1) + 1 := by
  have : 0 < R.length := List.length_pos_iff.mpr hRne
  omega

theorem entry_cons_last {p : ℕ × ℕ} {R : PairSeq} (hRne : R ≠ []) (i : ℕ) :
    entry (p :: R) i R.length = entry R i (R.length - 1) := by
  conv_lhs => rw [len_succ hRne]
  rw [entry_cons]

theorem le0_cons_last {p : ℕ × ℕ} {R : PairSeq} (hRne : R ≠ []) (j : ℕ) :
    le0 (p :: R) (j + 1) R.length ↔ le0 R j (R.length - 1) := by
  conv_lhs => rw [len_succ hRne]
  rw [le0_cons]

theorem nextR_cons_last {p : ℕ × ℕ} {R : PairSeq} (hRne : R ≠ []) (i j : ℕ) :
    nextR (p :: R) i (j + 1) R.length ↔ nextR R i j (R.length - 1) := by
  conv_lhs => rw [len_succ hRne]
  rw [nextR_cons]

theorem idx1_cons_last {p : ℕ × ℕ} {R : PairSeq} (hRne : R ≠ []) :
    idx1 (p :: R) R.length = idx1 R (R.length - 1) := by
  conv_lhs => rw [len_succ hRne]
  rw [idx1_cons]

theorem cons_len_lt {p : ℕ × ℕ} (R : PairSeq) : R.length < (p :: R).length := by simp

/-- (C′)/(D′) The root `(0,v)` becomes the row-1 parent of `M`'s last column
whenever `R` has no row-1 parent of its own but `v` is below `R`'s trailing
subscript — and `R`'s own parent survives the `cons` otherwise. -/
theorem hasParent_cons_one {v : ℕ} {R : PairSeq} (hR : argOK R) (hRne : R ≠ [])
    (h : hasParent R 1 (R.length - 1) ∨ v < entry R 1 (R.length - 1)) :
    hasParent ((0, v) :: R) 1 R.length := by
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  rw [hasParent_one_iff (cons_len_lt R)]
  have hE : entry ((0, v) :: R) 1 R.length = entry R 1 (R.length - 1) :=
    entry_cons_last hRne 1
  rcases h with h | h
  · rw [hasParent_one_iff (by omega)] at h
    obtain ⟨j', hj1, hj2, hj3⟩ := h
    refine ⟨j' + 1, by omega, (le0_cons_last hRne j').mpr hj2, ?_⟩
    rw [hE, entry_cons]
    exact hj3
  · exact ⟨0, hRlen, by
      have := le0_cons_zero (v := v) hR (R.length - 1) (by omega)
      rwa [← len_succ hRne] at this, by rw [hE]; simpa [entry] using h⟩

/-- When the parent of the last column is the root (index `0`), `oper` tiles the
whole of `M.dropLast`. -/
theorem oper_root_tiling {M : PairSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1))
    (hpar : parent M (idx1 M (M.length - 1)) (M.length - 1) = 0) :
    M⟦n⟧ = (List.range n).flatMap (fun k =>
      M.dropLast.map (fun p =>
        (p.1 + k * (if 0 < idx1 M (M.length - 1)
          then entry M 0 (M.length - 1) - entry M 0 0 else 0), p.2))) := by
  rw [oper_bad_unfold n hL hz hp, hpar]
  simp only [List.take_zero, List.nil_append, Nat.sub_zero]
  refine List.flatMap_congr ?_
  intro k _
  rw [List.dropLast_eq_take, ← map_range_entry_eq_take M (by omega), List.map_map,
    ← List.range_eq_range']
  rfl

/-- (B′)(C′) Non-collapsing principal step: `p_v(R)[n] = p_v(R[n])`. -/
theorem oper_cons_nat {v n : ℕ} {R : PairSeq} (hR : argOK R) (hRne : R ≠ [])
    (hp : hasParent R (idx1 R (R.length - 1)) (R.length - 1)) :
    ((0, v) :: R)⟦n⟧ = (0, v) :: R⟦n⟧ := by
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hnrR := parent_nextR hp
  have hj0lt : parent R (idx1 R (R.length - 1)) (R.length - 1) < R.length - 1 :=
    nextR_index_lt hnrR
  have hLR : R.length - 1 ≠ 0 := by omega
  have hxpos : 0 < entry R 0 (R.length - 1) := hR _ (entry_pair_mem (B := R) (by omega))
  have hzR : ¬ (entry R 0 (R.length - 1) = 0 ∧ entry R 1 (R.length - 1) = 0) := by
    rintro ⟨h1, -⟩; omega
  have hMlen : ((0, v) :: R).length - 1 = R.length := by simp
  have hEx : entry ((0, v) :: R) 0 R.length = entry R 0 (R.length - 1) :=
    entry_cons_last hRne 0
  have hE1 : entry ((0, v) :: R) 1 R.length = entry R 1 (R.length - 1) :=
    entry_cons_last hRne 1
  have hLM : ((0, v) :: R).length - 1 ≠ 0 := by rw [hMlen]; omega
  have hzM : ¬ (entry ((0, v) :: R) 0 (((0, v) :: R).length - 1) = 0 ∧
      entry ((0, v) :: R) 1 (((0, v) :: R).length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -⟩; rw [hEx] at h1; omega
  have hi1M : idx1 ((0, v) :: R) (((0, v) :: R).length - 1) = idx1 R (R.length - 1) := by
    rw [hMlen, idx1_cons_last hRne]
  -- the root is *not* a parent of the last column: `R`'s own parent blocks it
  have hnoroot : ¬ nextR ((0, v) :: R) (idx1 R (R.length - 1)) 0 R.length := by
    intro h0
    by_cases hi : idx1 R (R.length - 1) = 0
    · have h0' : nextrel0 ((0, v) :: R) 0 R.length := by
        unfold nextR at h0; rw [if_pos hi] at h0; exact h0
      have hnr0 : nextrel0 R (parent R (idx1 R (R.length - 1)) (R.length - 1))
          (R.length - 1) := by
        have h := hnrR; unfold nextR at h; rw [if_pos hi] at h; exact h
      have hval := h0'.2.2.2.2 (parent R (idx1 R (R.length - 1)) (R.length - 1) + 1)
        ⟨by omega, by omega⟩
      rw [hEx, entry_cons] at hval
      have := hnr0.2.2.2.1
      omega
    · have h0' : nextrel1 ((0, v) :: R) 0 R.length := by
        unfold nextR at h0; rw [if_neg hi] at h0; exact h0
      have hnr1 : nextrel1 R (parent R (idx1 R (R.length - 1)) (R.length - 1))
          (R.length - 1) := by
        have h := hnrR; unfold nextR at h; rw [if_neg hi] at h; exact h
      have hle : le0 ((0, v) :: R) (parent R (idx1 R (R.length - 1)) (R.length - 1) + 1)
          R.length := (le0_cons_last hRne _).mpr hnr1.2.2.2.2.1
      have hval := h0'.2.2.2.2.2 (parent R (idx1 R (R.length - 1)) (R.length - 1) + 1)
        ⟨by omega, hle⟩
      rw [hE1, entry_cons] at hval
      have := hnr1.2.2.2.1
      omega
  have huniq : ∀ y, nextR ((0, v) :: R) (idx1 R (R.length - 1)) y R.length →
      y = parent R (idx1 R (R.length - 1)) (R.length - 1) + 1 := by
    intro y hy
    rcases Nat.eq_zero_or_pos y with rfl | hy0
    · exact absurd hy hnoroot
    · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      have hyR := (nextR_cons_last hRne (idx1 R (R.length - 1)) y').mp hy
      rw [hp.unique hyR hnrR]
  have hpM : hasParent ((0, v) :: R) (idx1 ((0, v) :: R) (((0, v) :: R).length - 1))
      (((0, v) :: R).length - 1) := by
    rw [hi1M, hMlen]
    exact ⟨parent R (idx1 R (R.length - 1)) (R.length - 1) + 1,
      (nextR_cons_last hRne _ _).mpr hnrR, huniq⟩
  have hparM : parent ((0, v) :: R) (idx1 ((0, v) :: R) (((0, v) :: R).length - 1))
      (((0, v) :: R).length - 1)
      = parent R (idx1 R (R.length - 1)) (R.length - 1) + 1 := by
    have heq : parent ((0, v) :: R) (idx1 ((0, v) :: R) (((0, v) :: R).length - 1))
        (((0, v) :: R).length - 1)
        = parent ((0, v) :: R) (idx1 R (R.length - 1)) R.length := by rw [hi1M, hMlen]
    rw [heq]
    refine huniq _ (parent_nextR ?_)
    rw [hi1M, hMlen] at hpM; exact hpM
  have hrange : R.length - (parent R (idx1 R (R.length - 1)) (R.length - 1) + 1)
      = R.length - 1 - parent R (idx1 R (R.length - 1)) (R.length - 1) := by omega
  rw [oper_bad_unfold n hLM hzM hpM, oper_bad_unfold n hLR hzR hp,
    hparM, hi1M, hMlen, hEx, entry_cons, hrange, List.take_succ_cons,
    List.cons_append]
  congr 1
  congr 1
  refine List.flatMap_congr ?_
  intro k _
  have hshift : List.range' (parent R (idx1 R (R.length - 1)) (R.length - 1) + 1)
      (R.length - 1 - parent R (idx1 R (R.length - 1)) (R.length - 1))
      = (List.range' (parent R (idx1 R (R.length - 1)) (R.length - 1))
          (R.length - 1 - parent R (idx1 R (R.length - 1)) (R.length - 1))).map (fun j => j + 1) := by
    rw [List.range'_eq_map_range, List.range'_eq_map_range, List.map_map]
    refine List.map_congr_left ?_
    intro j _
    simp only [Function.comp_apply]
    omega
  rw [hshift, List.map_map]
  refine List.map_congr_left ?_
  intro j _
  simp only [Function.comp_apply, entry_cons]

/-- (A′) Successor case `dom R = {0}`: `p_v(β+1)[n] = p_v(β)·n`. -/
theorem oper_cons_succ {v n : ℕ} {R : PairSeq} (hR : argOK R) (hRne : R ≠ [])
    (hw : entry R 1 (R.length - 1) = 0)
    (hnp : ¬ hasParent R 0 (R.length - 1)) :
    ((0, v) :: R)⟦n⟧ =
      (List.range n).flatMap (fun _ => ((0, v) :: R.dropLast)) := by
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : ((0, v) :: R).length - 1 = R.length := by simp
  have hEx : entry ((0, v) :: R) 0 R.length = entry R 0 (R.length - 1) :=
    entry_cons_last hRne 0
  have hxpos : 0 < entry R 0 (R.length - 1) := hR _ (entry_pair_mem (B := R) (by omega))
  have hL : ((0, v) :: R).length - 1 ≠ 0 := by rw [hMlen]; omega
  have hz : ¬ (entry ((0, v) :: R) 0 (((0, v) :: R).length - 1) = 0 ∧
      entry ((0, v) :: R) 1 (((0, v) :: R).length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -⟩; rw [hEx] at h1; omega
  have hi1 : idx1 ((0, v) :: R) (((0, v) :: R).length - 1) = 0 := by
    rw [hMlen, idx1_cons_last hRne]
    unfold idx1; rw [if_neg (by omega)]
  have hallge : ∀ k, k < R.length - 1 → entry R 0 (R.length - 1) ≤ entry R 0 k := by
    intro k hk
    by_contra hcon
    exact hnp ((hasParent_zero_iff (by omega)).mpr ⟨k, hk, by omega⟩)
  -- the root is a `nextrel0`-parent of the last column …
  have hnr : nextrel0 ((0, v) :: R) 0 R.length := by
    refine ⟨by simp, by simp, hRlen, ?_, ?_⟩
    · rw [hEx]; simpa [entry] using hxpos
    · rintro l ⟨hl1, hl2⟩
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [hEx, entry_cons]
      exact hallge l' (by omega)
  -- … and the only one
  have huniq : ∀ y, nextR ((0, v) :: R) 0 y R.length → y = 0 := by
    intro y hy
    by_contra hy0
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have hyR : nextrel0 R y' (R.length - 1) := (nextR_cons_last hRne 0 y').mp hy
    have h1 := hallge y' hyR.2.2.1
    have h2 := hyR.2.2.2.1
    omega
  have hp : hasParent ((0, v) :: R) (idx1 ((0, v) :: R) (((0, v) :: R).length - 1))
      (((0, v) :: R).length - 1) := by
    rw [hi1, hMlen]
    exact ⟨0, hnr, huniq⟩
  have hpar : parent ((0, v) :: R) (idx1 ((0, v) :: R) (((0, v) :: R).length - 1))
      (((0, v) :: R).length - 1) = 0 := by
    have hp' : hasParent ((0, v) :: R) 0 R.length := by rw [hi1, hMlen] at hp; exact hp
    have := parent_nextR hp'
    have heq : parent ((0, v) :: R) (idx1 ((0, v) :: R) (((0, v) :: R).length - 1))
        (((0, v) :: R).length - 1) = parent ((0, v) :: R) 0 R.length := by
      rw [hi1, hMlen]
    rw [heq]
    exact huniq _ this
  rw [oper_root_tiling n hL hz hp hpar, hi1]
  have hdl : ((0, v) :: R).dropLast = (0, v) :: R.dropLast := by
    cases R with
    | nil => exact absurd rfl hRne
    | cons a b => simp
  rw [hdl]
  refine List.flatMap_congr ?_
  intro k _
  simp

/-- (D′) **The tower identity** — the PSS form of `(D_v b)[n] = D_v(b[x_n])`.
This is `oper_bad_blocks`' `n`-fold ascending tiling read through `graft`. -/
theorem oper_cons_tower {v m n : ℕ} {R : PairSeq}
    (hR : argOK R) (hd : domT R m) (hvm : v ≤ m) :
    ((0, v) :: R)⟦n⟧ = tow v R n := by
  have hRne : R ≠ [] := by rintro rfl; exact not_domT_nil m hd
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : ((0, v) :: R).length - 1 = R.length := by simp
  have hEx : entry ((0, v) :: R) 0 R.length = entry R 0 (R.length - 1) :=
    entry_cons_last hRne 0
  have hE1 : entry ((0, v) :: R) 1 R.length = entry R 1 (R.length - 1) :=
    entry_cons_last hRne 1
  have hxpos : 0 < entry R 0 (R.length - 1) := hR _ (entry_pair_mem (B := R) (by omega))
  have hw : entry R 1 (R.length - 1) = m + 1 := hd.1
  have hL : ((0, v) :: R).length - 1 ≠ 0 := by rw [hMlen]; omega
  have hz : ¬ (entry ((0, v) :: R) 0 (((0, v) :: R).length - 1) = 0 ∧
      entry ((0, v) :: R) 1 (((0, v) :: R).length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -⟩; rw [hEx] at h1; omega
  have hi1 : idx1 ((0, v) :: R) (((0, v) :: R).length - 1) = 1 := by
    rw [hMlen, idx1_cons_last hRne]
    unfold idx1; rw [if_pos (by omega)]
  have huniq : ∀ y, nextR ((0, v) :: R) 1 y R.length → y = 0 := by
    intro y hy
    by_contra hy0
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have hyR : nextrel1 R y' (R.length - 1) := (nextR_cons_last hRne 1 y').mp hy
    exact hd.2 ((hasParent_one_iff (by omega)).mpr
      ⟨y', hyR.2.2.1, hyR.2.2.2.2.1, hyR.2.2.2.1⟩)
  have hp1 : hasParent ((0, v) :: R) 1 R.length :=
    hasParent_cons_one hR hRne (Or.inr (by omega))
  have hp : hasParent ((0, v) :: R) (idx1 ((0, v) :: R) (((0, v) :: R).length - 1))
      (((0, v) :: R).length - 1) := by rw [hi1, hMlen]; exact hp1
  have hpar : parent ((0, v) :: R) (idx1 ((0, v) :: R) (((0, v) :: R).length - 1))
      (((0, v) :: R).length - 1) = 0 := by
    have heq : parent ((0, v) :: R) (idx1 ((0, v) :: R) (((0, v) :: R).length - 1))
        (((0, v) :: R).length - 1) = parent ((0, v) :: R) 1 R.length := by
      rw [hi1, hMlen]
    rw [heq]
    exact huniq _ (parent_nextR hp1)
  have hdl : ((0, v) :: R).dropLast = (0, v) :: R.dropLast := by
    cases R with
    | nil => exact absurd rfl hRne
    | cons a b => simp
  have hroot0 : entry ((0, v) :: R) 0 0 = 0 := by simp [entry]
  rw [oper_root_tiling n hL hz hp hpar, hi1, hMlen, hEx, hroot0, hdl,
    if_pos Nat.zero_lt_one, Nat.sub_zero]
  -- now: `(range n).flatMap (k ↦ D.map (· + k*x)) = tow v R n`
  clear hp hpar hz hL hi1 huniq hp1
  induction n with
  | zero => simp [tow]
  | succ n ih =>
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      have h0 : ((0, v) :: R.dropLast).map
          (fun p => (p.1 + 0 * entry R 0 (R.length - 1), p.2)) = (0, v) :: R.dropLast := by
        simp
      rw [h0]
      have hstep : (((List.range n).flatMap fun k =>
            ((0, v) :: R.dropLast).map fun p => (p.1 + k * entry R 0 (R.length - 1), p.2)).map
            (fun p => (p.1 + entry R 0 (R.length - 1), p.2)))
          = (List.range n).flatMap (fun k => ((0, v) :: R.dropLast).map
              fun p => (p.1 + (k + 1) * entry R 0 (R.length - 1), p.2)) := by
        rw [List.map_flatMap]
        refine List.flatMap_congr ?_
        intro k _
        rw [List.map_map]
        refine List.map_congr_left ?_
        intro q _
        simp only [Function.comp_apply, Nat.succ_mul, Nat.add_assoc]
      show ((0, v) :: R.dropLast) ++ (List.range n).flatMap
          (fun k => ((0, v) :: R.dropLast).map
            fun p => (p.1 + (k + 1) * entry R 0 (R.length - 1), p.2))
        = tow v R (n + 1)
      rw [← hstep, ih]
      show ((0, v) :: R.dropLast) ++ (tow v R n).map
          (fun p => (p.1 + entry R 0 (R.length - 1), p.2))
        = (0, v) :: graft R (tow v R n)
      rw [graft]
      simp

/-- (E′) Continuous case `dom R = T_m` with `m < v`: `dom (p_v R) = T_m`. -/
theorem domT_cons_of_lt {v m : ℕ} {R : PairSeq} (hR : argOK R) (hd : domT R m)
    (hmv : m < v) : domT ((0, v) :: R) m := by
  have hRne : R ≠ [] := by rintro rfl; exact not_domT_nil m hd
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hlast : ((0, v) :: R).length - 1 = R.length := by simp
  have hE : entry ((0, v) :: R) 1 R.length = entry R 1 (R.length - 1) :=
    entry_cons_last hRne 1
  refine ⟨by rw [hlast, hE]; exact hd.1, ?_⟩
  rw [hlast, hasParent_one_iff (cons_len_lt R)]
  rintro ⟨j0, hj1, hj2, hj3⟩
  rw [hE, hd.1] at hj3
  rcases Nat.eq_zero_or_pos j0 with rfl | hj0
  · simp [entry] at hj3; omega
  · obtain ⟨j', rfl⟩ : ∃ j', j0 = j' + 1 := ⟨j0 - 1, by omega⟩
    rw [entry_cons] at hj3
    have h1 : entry R 1 (R.length - 1) = m + 1 := hd.1
    refine hd.2 ((hasParent_one_iff (by omega)).mpr ⟨j', by omega,
      (le0_cons_last hRne j').mp hj2, by omega⟩)

/-! ### Assembling 2.6 -/

theorem argOK_oper {R : PairSeq} (hR : argOK R) (n : ℕ) : argOK (R⟦n⟧) :=
  fun p hp => oper_mem_ge (c := 1) (fun q hq => hR q hq) p hp

theorem argOK_graft {R : PairSeq} (hRne : R ≠ []) (hR : argOK R) (z' : PairSeq) :
    argOK (graft R z') :=
  fun p hp => graft_mem_ge (c := 1) hRne (fun q hq => hR q hq) p hp

theorem argOK_dropLast {R : PairSeq} (hR : argOK R) : argOK R.dropLast :=
  fun p hp => hR p (List.dropLast_subset _ hp)

theorem based_cons (v : ℕ) (R : PairSeq) : based ((0, v) :: R) := by
  simp [based, entry]

theorem rsum_self_cons (v : ℕ) (R : PairSeq) :
    ∀ p ∈ ((0, v) :: R), entry ((0, v) :: R) 0 0 ≤ p.1 := by
  intro p _
  simp [entry]

/-- `n` copies of a single tree stay in `W u`. -/
theorem W_flatMap_copies {u : ℕ} {Q : PairSeq} (hQ : Q ∈ W u)
    (hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1) :
    ∀ n : ℕ, ((List.range n).flatMap fun _ => Q) ∈ W u := by
  intro n
  induction n with
  | zero => simpa using W_nil u
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append]
      have hQ1 : ((List.flatMap fun _ => Q) [n]) = Q := by simp
      rw [hQ1]
      refine W_add ih hQ ?_
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rw [List.mem_flatMap] at hp
        obtain ⟨-, -, hp⟩ := hp
        exact hQr p hp
      · exact hQr p hp

/-- **2.6**: `A_ω(W*) ⊆ W*`. -/
theorem Wstar_closed : ∀ (u : ℕ) (M : PairSeq), Aop W u Wstar M → M ∈ Wstar := by
  intro u R AR hR v
  by_cases hRnil : R = []
  · subst hRnil; simpa using Om_mem_W v
  · have hRlen : 0 < R.length := List.length_pos_iff.mpr hRnil
    have hlast : ((0, v) :: R).length - 1 = R.length := by simp
    have hE1 : entry ((0, v) :: R) 1 (((0, v) :: R).length - 1)
        = entry R 1 (R.length - 1) := by
      rw [hlast]
      conv_lhs => rw [show R.length = (R.length - 1) + 1 by omega]
      rw [entry_cons]
    -- `natDom` of the principal block, given a parent for its last column
    have hnatOf : hasParent ((0, v) :: R) 1 R.length → natDom ((0, v) :: R) := by
      intro hh; exact natDom_iff.mpr (Or.inr (by rw [hlast]; exact hh))
    have hnatZero : entry R 1 (R.length - 1) = 0 → natDom ((0, v) :: R) := by
      intro hz; exact natDom_iff.mpr (Or.inl (by rw [hE1]; exact hz))
    rcases AR with ⟨hl, hw⟩ | ⟨hnat, hop⟩ | ⟨m, hm, hd, hgr⟩
    · -- branch 1: `R = [(x,0)]`, so `p_v(R) = p_v(1)`, expansion `p_v(0)·n`
      have hR1 : R.length = 1 := by omega
      have hw' : entry R 1 (R.length - 1) = 0 := by rw [hR1]; simpa using hw
      have hnp : ¬ hasParent R 0 (R.length - 1) := by
        rw [hR1]
        rintro ⟨j0, hj0, -⟩
        exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
      have hdl : R.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      refine A1_intro (Or.inr (Or.inl ⟨hnatZero hw', fun n hn => ?_⟩))
      rw [oper_cons_succ hR hRnil hw' hnp, hdl]
      exact W_flatMap_copies (Om_mem_W v) (rsum_self_cons v []) n
    · -- branch 2: `natDom R`
      by_cases hp : hasParent R (idx1 R (R.length - 1)) (R.length - 1)
      · -- (B′)(C′): `p_v(R)[n] = p_v(R[n])`
        have hnatM : natDom ((0, v) :: R) := by
          by_cases hz : entry R 1 (R.length - 1) = 0
          · exact hnatZero hz
          · refine hnatOf (hasParent_cons_one hR hRnil (Or.inl ?_))
            have : idx1 R (R.length - 1) = 1 := by
              unfold idx1; rw [if_pos (by omega)]
            rwa [this] at hp
        refine A1_intro (Or.inr (Or.inl ⟨hnatM, fun n hn => ?_⟩))
        rw [oper_cons_nat hR hRnil hp]
        exact hop n hn (argOK_oper hR n) v
      · -- no parent: `natDom R` forces the successor case `w = 0`
        have hw0 : entry R 1 (R.length - 1) = 0 := by
          by_contra hz
          obtain ⟨m, hm⟩ : ∃ m, entry R 1 (R.length - 1) = m + 1 :=
            ⟨entry R 1 (R.length - 1) - 1, by omega⟩
          refine hnat m ⟨hm, ?_⟩
          intro hh
          exact hp (by
            have : idx1 R (R.length - 1) = 1 := by unfold idx1; rw [if_pos (by omega)]
            rw [this]; exact hh)
        have hnp : ¬ hasParent R 0 (R.length - 1) := by
          intro hh
          exact hp (by
            have : idx1 R (R.length - 1) = 0 := by unfold idx1; rw [if_neg (by omega)]
            rw [this]; exact hh)
        refine A1_intro (Or.inr (Or.inl ⟨hnatZero hw0, fun n hn => ?_⟩))
        rw [oper_cons_succ hR hRnil hw0 hnp]
        refine W_flatMap_copies ?_ (rsum_self_cons v _) n
        -- `p_v(R[1]) ∈ W v`, and `R[1] = R.dropLast` unless `|R| = 1`
        by_cases hR2 : 2 ≤ R.length
        · have hop1 := hop 1 le_rfl
          have hpred : R⟦1⟧ = R.dropLast := by
            have hL : R.length - 1 ≠ 0 := by omega
            have : R⟦1⟧ = Pred R := by
              by_cases hz : entry R 0 (R.length - 1) = 0 ∧ entry R 1 (R.length - 1) = 0
              · exact oper_eq_pred_of_zero 1 hL hz
              · exact oper_eq_pred_of_noParent 1 hL hz hp
            rw [this]
            unfold Pred
            rw [if_neg (by omega)]
          rw [hpred] at hop1
          exact hop1 (argOK_dropLast hR) v
        · have : R.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
          rw [this]
          simpa using Om_mem_W v
    · -- branch 3: `domT R m`
      by_cases hvm : v ≤ m
      · -- (D′) the tower
        have htow : ∀ k, tow v R k ∈ W v := by
          intro k
          induction k with
          | zero => simpa [tow] using W_nil v
          | succ k ihk =>
              have hbased : based (tow v R k) := by
                cases k with
                | zero => simp [tow]
                | succ k' => simpa [tow] using based_cons v _
              have hlift : tow v R k ∈ W m := W_mono hvm ihk
              have := hgr (tow v R k) hlift hbased
              exact this (argOK_graft hRnil hR _) v
        refine A1_intro (Or.inr (Or.inl ⟨?_, fun n hn => ?_⟩))
        · refine hnatOf (hasParent_cons_one hR hRnil (Or.inr ?_))
          rw [hd.1]; omega
        · rw [oper_cons_tower hR hd hvm]; exact htow n
      · -- (E′) continuous: `dom (p_v R) = T_m` with `m < v`
        push Not at hvm
        refine A1_intro (Or.inr (Or.inr ⟨m, hvm, domT_cons_of_lt hR hd hvm, ?_⟩))
        intro z hz hbz
        rw [graft_cons hRnil]
        exact hgr z hz hbz (argOK_graft hRnil hR z) v

/-! ## 7. Buchholz 2.7/2.8 — induction on block length -/

/-- The single-tree shift: a tree rooted at depth `c` is the `c`-shift of a tree
rooted at depth `0`. -/
theorem tree_shift {p0 : ℕ × ℕ} {R : PairSeq} (hR : ∀ q ∈ R, p0.1 ≤ q.1) :
    (((0, p0.2) :: R.map (fun q => (q.1 - p0.1, q.2))).map
      fun q => (q.1 + p0.1, q.2)) = p0 :: R := by
  rw [List.map_cons, map_sub_add hR]
  simp

theorem mem_of_Aclosed_aux : ∀ (N : ℕ) (M : PairSeq), M.length ≤ N →
    ∀ X : Set PairSeq, (∀ (u : ℕ) (M' : PairSeq), Aop W u X M' → M' ∈ X) → M ∈ X := by
  intro N
  induction N with
  | zero =>
      intro M hM X hX
      have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      exact hX 0 [] (Or.inl ⟨by simp, by simp [entry]⟩)
  | succ N ih =>
      intro M hM X hX
      by_cases hMnil : M = []
      · subst hMnil; exact hX 0 [] (Or.inl ⟨by simp, by simp [entry]⟩)
      · obtain ⟨A, P, hEq, hPne, hrs, htail⟩ := split_lastMin hMnil
        subst hEq
        have hPlen : 0 < P.length := List.length_pos_iff.mpr hPne
        have hMlen : A.length + P.length ≤ N + 1 := by
          rw [List.length_append] at hM; exact hM
        by_cases hAnil : A = []
        · subst hAnil
          obtain ⟨p0, R, rfl⟩ : ∃ p0 R, P = p0 :: R := by
            cases P with
            | nil => exact absurd rfl hPne
            | cons a b => exact ⟨a, b, rfl⟩
          have hRgt : ∀ q ∈ R, p0.1 < q.1 := by
            intro q hq
            have := htail q (by simpa using hq)
            simpa [entry] using this
          have hargOK : argOK (R.map fun q => (q.1 - p0.1, q.2)) := by
            intro q hq
            rw [List.mem_map] at hq
            obtain ⟨r, hr, rfl⟩ := hq
            have := hRgt r hr
            simp only []
            omega
          have hWs : (R.map fun q => (q.1 - p0.1, q.2)) ∈ Wstar := by
            refine ih _ ?_ Wstar Wstar_closed
            rw [List.length_map]
            simp only [List.length_cons] at hMlen
            omega
          have hmem : ((0, p0.2) :: R.map fun q => (q.1 - p0.1, q.2)) ∈ W p0.2 :=
            hWs hargOK p0.2
          have hP : (p0 :: R) ∈ W p0.2 := by
            rw [← tree_shift (fun q hq => le_of_lt (hRgt q hq))]
            exact W_shift hmem p0.1
          simp only [List.nil_append]
          exact A2' (fun M' h => hX p0.2 M' h) hP
        · have hAlen : 0 < A.length := List.length_pos_iff.mpr hAnil
          have hAX : A ∈ X := ih A (by omega) X hX
          have hPX : P ∈ XA A X := ih P (by omega) (XA A X)
            (fun u M' h => XA_closed (fun M'' h'' => hX u M'' h'') hAX M' h)
          exact hPX hrs

/-- **2.7**: every block belongs to every `A`-closed set.  Induction on
`M.length`: split off the last top-level tree (`split_lastMin`), recombine with
2.4(a), and handle the principal `(0,v) :: R` by 2.6 applied to `R` (shorter). -/
theorem mem_of_Aclosed {X : Set PairSeq}
    (hX : ∀ (u : ℕ) (M : PairSeq), Aop W u X M → M ∈ X) :
    ∀ M : PairSeq, M ∈ X :=
  fun M => mem_of_Aclosed_aux M.length M le_rfl X hX

/-- **2.8**: every argument block is in `W*`. -/
theorem mem_Wstar (R : PairSeq) : R ∈ Wstar :=
  mem_of_Aclosed Wstar_closed R

/-- **Every block lies in `W u` as soon as `u` bounds its row-1 values.**  The
top-level trees go into `W` at their own root subscript (2.8 via `Wstar`), are
lifted by level monotonicity, and are recombined by the additive closure. -/
theorem mem_W_of_bound_aux : ∀ (N : ℕ) (M : PairSeq), M.length ≤ N →
    ∀ u : ℕ, (∀ p ∈ M, p.2 ≤ u) → M ∈ W u := by
  intro N
  induction N with
  | zero =>
      intro M hM u _
      have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      exact W_nil u
  | succ N ih =>
      intro M hM u hbd
      by_cases hMnil : M = []
      · subst hMnil; exact W_nil u
      · obtain ⟨A, P, hEq, hPne, hrs, htail⟩ := split_lastMin hMnil
        subst hEq
        have hPlen : 0 < P.length := List.length_pos_iff.mpr hPne
        have hMlen : A.length + P.length ≤ N + 1 := by
          rw [List.length_append] at hM; exact hM
        obtain ⟨p0, R, hPeq⟩ : ∃ p0 R, P = p0 :: R := by
          cases P with
          | nil => exact absurd rfl hPne
          | cons a b => exact ⟨a, b, rfl⟩
        subst hPeq
        have hRgt : ∀ q ∈ R, p0.1 < q.1 := by
          intro q hq
          have := htail q (by simpa using hq)
          simpa [entry] using this
        have hargOK : argOK (R.map fun q => (q.1 - p0.1, q.2)) := by
          intro q hq
          rw [List.mem_map] at hq
          obtain ⟨r, hr, rfl⟩ := hq
          have := hRgt r hr
          simp only []
          omega
        have hmem : ((0, p0.2) :: R.map fun q => (q.1 - p0.1, q.2)) ∈ W p0.2 :=
          mem_Wstar _ hargOK p0.2
        have hP : (p0 :: R) ∈ W p0.2 := by
          rw [← tree_shift (fun q hq => le_of_lt (hRgt q hq))]
          exact W_shift hmem p0.1
        have hPu : (p0 :: R) ∈ W u :=
          W_mono (hbd p0 (List.mem_append_right _ List.mem_cons_self)) hP
        by_cases hAnil : A = []
        · subst hAnil; simpa using hPu
        · have hAlen : 0 < A.length := List.length_pos_iff.mpr hAnil
          have hAu : A ∈ W u :=
            ih A (by omega) u (fun p hp => hbd p (List.mem_append_left _ hp))
          exact W_add hAu hPu hrs

theorem mem_W_of_bound (M : PairSeq) (u : ℕ) (h : ∀ p ∈ M, p.2 ≤ u) : M ∈ W u :=
  mem_W_of_bound_aux M.length M le_rfl u h

theorem le_maxr1 : ∀ {S : PairSeq}, ∀ p ∈ S, p.2 ≤ maxr1 S := by
  intro S
  induction S with
  | nil => intro p hp; simp at hp
  | cons q S ih =>
      intro p hp
      rw [maxr1_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact le_max_left _ _
      · exact le_trans (ih p hp) (le_max_right _ _)

/-- Every block lies in `W u` for `u` its maximal row-1 value. -/
theorem mem_W_maxr1 (M : PairSeq) : M ∈ W (maxr1 M) :=
  mem_W_of_bound M (maxr1 M) le_maxr1

/-! ## 8. Membership — the PSS analogue of Buchholz (1987) 2.8

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
theorem W_membership : ∀ M : PairSeq, ST_PS M → ∃ u : ℕ, M ∈ W u :=
  fun M _ => ⟨maxr1 M, mem_W_maxr1 M⟩

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

/-! ## 9. REPORT — what is GREEN, what is open, and where the danger is

Everything in this file is `sorryAx`-free; the `#print axioms` block below is
the machine check.  What follows records the shape of the completed argument and
the facts a reader should not have to rediscover.

### The two design decisions that made it work

1. **`dom = T_m` is PSS's own `¬ hasParent M 1 (|M|-1)`** (`domT`), and the
   `T_m`-indexed fundamental sequence is the `graft`.  Validated, not asserted:
   `hasParent_one_iff` proves that `nextrel1` picks the *largest* row-0 ancestor
   with a smaller row-1 value, so a row-1 parent exists iff *some* strict row-0
   ancestor breaks Buchholz's `u < v` spine condition.
2. **The ℕ-branch of `A_u` carries the guard `natDom`** (Buchholz's
   `dom c ∈ {{0}, ℕ_B}`).  This is load-bearing: without it branch 2 could fire
   on an `Ω_{m+1}`-cofinal block, where PSS's `oper` degenerates to
   `graft M []` and carries far too little information to run the 2.6 tower.

### The engine: `oper_shift`

`Nrm.oper_append_right` needs the right summand anchored at depth `0`; PSS
blocks are not.  `oper_shift` (`oper` is row-0-shift equivariant) converts it
into the shift-general `oper_append_gen`, which is what `split_lastMin` feeds.
The one non-shift-invariant test inside `oper` — "is the last pair `(0,0)`?" —
turns out to be **redundant**: a row-0-`0` column has no parent at all, so both
readings land in the same `Pred` branch.

### The tower

`oper_cons_tower` is the PSS form of `(D_v b)[n] = D_v(b[x_n])`.  The proof is
the recursion `M⟦n+1⟧ = M.dropLast ++ (M⟦n⟧).map (· + d0)` with
`d0 = entry R 0 (|R|-1)`, matched against
`tow v R (k+1) = (0,v) :: graft R (tow v R k)`.  The root `(0,v)` is the row-1
parent of the last column precisely because `v ≤ m` (`hasParent_cons_one`), and
`argOK R` makes it a row-0 ancestor of everything (`le0_cons_zero`).

### The `H0clause` question — answered NO, and structurally

The worry was Buchholz's additive closure 2.4(b), free in the source only
because `+` is formed inside `OT_B`, whose *definition* carries the CNF
condition.  On the PSS side `translate`'s `+` is the third component of
`P a b c` and carries **no** normal-form condition, so `A ++ B` is
unconditional at the term level; 2.4(b) needs only the *positional* guard
`rsum A B` ("`B` is a genuine top-level suffix"), which `split_lastMin` supplies
for free.  The reason is the one the design answer predicted: the carrier of the
induction is **W-membership** (`A`-closed by construction), never an
order-domination clause, so no `olt` comparison — hence no `Gterm` domination —
is ever needed.  The five `oper_cons_*` lemmas confirm this: they are pure
statements about `oper`/`hasParent`, and their proofs never mention `translate`.

### Facts worth not rediscovering

* **`based` and `argOK` are different and both necessary.**  `based M` ("first
  column at depth `0`") is what `oper` preserves; `argOK R` ("every column
  strictly below depth `0`") is what makes the root of `(0,v) :: R` an ancestor
  of everything.  "Minimum depth `0`" is *not* `oper`-stable, which is why
  `split_lastMin` + `oper_shift` replace any naive normalisation.
* **The `based z` guard on the `T_m` branch is load-bearing** — §1c
  machine-checks a concrete failure (`[(0,0)]` and `[(2,0)]` have the same
  `translate` but graft differently).  It survived the whole chain because the
  tower's graft argument `tow v R k` is `[]` or a depth-`0` `cons`.
* **`ST_PS`-ness is barely used.**  `mem_W_of_bound` proves membership for
  *every* block, so `W_membership` never needs the invariant "no standard form
  is `Ω`-cofinal"; the bridge uses only `stps_head` (length-`1` standard forms
  are `[(0,0)]`).
-/

#print axioms hasParent_one_iff
#print axioms domT_iff
#print axioms oper_shift
#print axioms W_shift
#print axioms split_lastMin
#print axioms oper_append_gen
#print axioms domT_append
#print axioms XA_closed
#print axioms W_add
#print axioms Om_mem_W
#print axioms hasParent_zero_iff
#print axioms le0_cons_zero
#print axioms hasParent_cons_one
#print axioms domT_cons_of_lt
#print axioms oper_cons_succ
#print axioms oper_cons_nat
#print axioms oper_cons_tower
#print axioms Wstar_closed
#print axioms mem_of_Aclosed
#print axioms mem_Wstar
#print axioms mem_W_of_bound
#print axioms mem_W_maxr1
#print axioms W_membership
#print axioms wf_olt_ST_PS_of_cofinality
#print axioms A1
#print axioms A2'
#print axioms W_mono
#print axioms W_nil
#print axioms oper_eq_graft_nil_of_domT
#print axioms acc_of_W
#print axioms wf_of_cofinality_and_membership

end Wset

end YAPSS
