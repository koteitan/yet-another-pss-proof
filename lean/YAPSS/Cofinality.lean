/-
# PSS Bachmann cofinality — the load-bearing statement of the W_u transplant

## Why this file exists (2026-07-24 route change)

`pss-proof` produced an **ordinal-free SYNTACTIC** well-foundedness proof of
Buchholz `OT_B` (sorry-free, named-assumption-free) whose engine is

    Bachmann cofinality  +  the iterated inductive set `W_u` (least fixpoint of `A_u`)

instead of the ordinal evaluation map.  That **falsifies the premise** on which this
project's previous terminal rested — namely that `wf_olt_wf3` (via `oV`/`wf3`) is the
only WF certificate for `olt`, whence `wf3`-membership (= the open `H0clause`) was
"unavoidable".  It is not: there is a second, ordinal-free certificate.

Two further points make this genuinely new rather than a 14th bypass:

* every induction axis this project exhausted (term-local, column-local, forest-LEVEL,
  row-1, oper-derivation, per-level, forest-ancestor) is a **structural** induction, and
  each died the same way — the carrier breaks at an *intermediate node*.  The `W_u`
  least-fixpoint induction is **not structural**: it descends the **fundamental
  sequence** (`oper`, i.e. `M⟦n⟧`) and never visits those intermediate nodes.
* PSS standard forms are **not** Buchholz `OT` terms (bypass #7: `translate (diagSeq 0 2)`
  fails OT3), so the source proof cannot be imported — it must be redone natively.  In
  the source, the coefficient-domination (G) condition is *free* precisely because
  `isOT_BT` is **defined** by it; natively it is not free, which is why we route around
  it via cofinality instead.

## The statement (model-verified TRUE)

`tools/probe_pss_cofinality.py`: **0 violations** over 5778 / 19503 / 79003 pairs at
closure +5/+6/+7 on the `row1 ≤ 1` ST_PS fragment, and non-degenerate (every host has
genuine `M⟦n⟧ ≠ M` expansions; excluding the degenerate case still gives 0 violations).
Re-checked with `n ≥ 1` only (which `ST_PS.oper` requires): still 0 violations.

Crucially the statement **never mentions `Gterm` / coefficient domination**, so it is a
genuinely different obligation from `H0clause_oper_step`.

## Intended assembly

    pss_cofinality  +  (A/W least-fixpoint induction, mirroring the source)
        ⟹  WF (olt on ST_PS images)
        ⟹  PSS termination            (the decrease `m_step_decreases` is already GREEN)

## Where the proof should come from

The GREEN PSS-concrete assets are exactly the right shape here, because they relate an
**expansion to its original** (unlike the cross-level order-lift, where their domain was
empty):  `oper_bad_blocks` (Mechanized.lean:836, the oper copy/tile decomposition),
`core_i0` (:714) and `core_i1` (:737) (ascending-copy domination), together with
`translate_shift`, `translate_take_le`, `translate_append_ge` (Gterm0Olt.lean).

## STATE (2026-07-24, this file)

The proof is routed through **`olt_ST_iff_seqlex`** (Seqlex.lean:709): on `ST_PS`,
`translate` is an order isomorphism onto the column-lex order `seqlex`, so the whole
statement becomes combinatorics on pair sequences.  Everything below is GREEN except a
single residual `AscCrux1`:

| branch of `oper` on `ST_PS M`             | status                                  |
|-------------------------------------------|-----------------------------------------|
| `M.length ≤ 1` (`M⟦n⟧ = M`)               | GREEN `seqlex_cof_short`                |
| last column `(0,0)` (`M⟦n⟧ = M.dropLast`) | GREEN `seqlex_cof_zero`                 |
| no unique parent                          | GREEN — **branch is empty** on `ST_PS`  |
|                                           | (`hasParent_last_ST_PS`, via `hp_last`) |
| bad, `d0 = 0` (exact copies)              | GREEN `crux_zero` / `copy_dom_zero`     |
| bad, `d0 > 0` (ascending), head step      | GREEN `asc_head_step`                   |
| bad, `d0 > 0`, copy-count bookkeeping      | GREEN `asc_crux1_of_argdom`             |
| bad, `d0 > 0`, the collapse domination     | **OPEN** — `AscArgDom`                  |

`pss_cofinality_of_argdom : AscArgDom → pss_cofinality`, where the *entire*
residual is the single `≤lex` inequality (`blk = (v0,w0)::R`,
`blk' = shiftr0 d0 blk`, `S_hi = S.takeWhile (v0+d0 < ·.1)`):

    ∃ m,  S_hi  ≤lex  shiftr0 d0 (R ++ copies d0 blk' m)

under `ST_PS (G ++ blk ++ [(v0+d0, w0+1)])` and `ST_PS (G ++ blk ++ (v0+d0,w0) :: S)`.
In words: *the argument of the collapsed node `(v0+d0, w0)` in `N` is dominated
by the (shifted) argument of the block root in the host expansion `M⟦m+1⟧`* —
literally the `∃n, e ≤ c[x_n]` step `(*)` of the Buchholz source's collapse
branch, transposed to BMS copy structure.

Model-verified TRUE: **0 violations** over 6095 / 7969 / 15579 instances at
closures `(v≤4,d=5)`, `(v≤5,d=5)`, `(v≤4,d=6)` with `m ≤ 12/12/14`
(`tools/probe_cof_asc.py` + the inline check recorded in the session).

### Recommended next attack

Since no *local* invariant of `N` can supply `AscArgDom` (the host-free version
is refuted above), the next route is an induction along the **`ST_PS` derivation
of `N`** for the whole of `SeqlexCofinality`:

* `N` is never a base diagonal in the ascending configuration (a diagonal has
  row-0 `=` row-1 in every column, forcing `d0 = 0`), so `N = N'⟦k⟧`;
* if `seqlex N' M` the IH closes it; if `N' = M` take `m = k`;
* the only hard case is `seqlex M N'`, i.e. `N'⟦k⟧ <lex M <lex N'`.  There `M`
  cannot be a prefix of `N'` (that contradicts `N'⟦1⟧ ≤lex N'⟦k⟧`), so writing
  `N' = (G' ++ blk'') ++ [lp']` the snoc analysis (`seqlex_snoc_cases`) forces
  `M = (G' ++ blk'') ++ q' :: S'` with `pairlt q' lp'` — the *same* two-form
  configuration, with the roles of host and small side exchanged.  Also, `N'`
  is necessarily in the **bad** branch there (the `(0,0)`-last branch makes the
  case vacuous, and `noparent` is empty on `ST_PS`).

`Part 6b` below supplies the column discipline that this induction's base case
needs (`snd_le_fst_ST_PS`, `le_diag_ST_PS`).

Running the same derivation induction **directly on `AscArgDom`** (writing
`N = N₁⟦k⟧`, `p = |G| + |blk|` for the position of the copy root `q`) splits as:

* `N` a base diagonal — impossible (`row-0 = row-1` in a diagonal forces `d0 = 0`);
* `|N₁| ≤ 1` — impossible (`|N| ≥ p + 1 ≥ 2`);
* `N₁` in the `noparent` branch — impossible (`hasParent_last_ST_PS`);
* `N₁` in the `(0,0)`-last branch — `N = N₁.dropLast`, `N₁ = N ++ [(0,0)]`, and
  `S_hi` is *unchanged* (`(0,0).1 = 0 ≤ v0+d0` stops the `takeWhile` no later),
  so the IH at `N₁` transfers verbatim;
* `N₁` in the **bad** branch, `N = G₁ ++ copies d₁ blk₁ k` — the real case.  It
  subdivides on where `p` sits relative to `|G₁|`; when the `takeWhile` defining
  `S_hi` stops inside `G₁` the IH at `N₁` again transfers, and what is left is
  `S_hi` reaching into `N`'s own copy region.  Formalising that last piece is
  the open work; it needs positional bookkeeping between the two copy
  decompositions (`N`'s own, and the host's `copies d0 blk'`).

Polarity note: by `sle_iff_not_seqlex` the goal is equivalent to
`∃ m, ¬ seqlex (shiftr0 d0 (R ++ copies d0 blk' m)) S_hi`, i.e. a pure
*no-overshoot* statement — the continuation of `N` never strictly exceeds the
copy word.  That is the shape the positional argument wants.

### Why `d0 = 0` closes but `d0 > 0` does not

The exact-copy branch is driven by **CNF** (`cnf_ST_PS`): the level-`v0` siblings of a
standard form are `≤o`-non-increasing, so the continuation of `N` after the block either
drops strictly below it (done) or reproduces it verbatim (recurse; `copy_dom_zero`).

In the ascending branch the copy root `q = (v0+d0, w0)` is a *descendant* of the block
root, not a sibling of it.  Its preceding sibling `s` at level `v0+d0` (if any) lies
inside `R`, and CNF **of the host** `M` already forces `s.2 ≥ lp.2 = w0+1 > w0` (`lp` is a
sibling of `s` in `M`); if `R` has no column at level `v0+d0` then `q` has no preceding
sibling at all.  Either way the CNF clause at `q` is discharged by the *subscript* alone
and puts **no** constraint on `q`'s argument.  So a further fact bounding the *argument of
the collapsed node* is required — i.e. exactly a coefficient/`Gterm`-domination-shaped
statement (the `G_u(e) < c` hypothesis of the Buchholz source, which is free there only
because `isOT_BT` is defined by it).  `core_i0`/`core_i1` do not supply it: their `C` is
*literally the copy list produced by `oper`*, whereas here the continuation of `N` is an
unknown standard form.

Model-verification of the residual: `tools/probe_cof_asc.py` (fact A3, 6095 instances,
0 violations at closure `v ≤ 4`, depth 5, `n ≤ 4`) and `tools/probe_cof_seqlex.py`
(the `seqlex` reformulation itself, 106491 pairs, 0 violations).

**The residual is irreducibly a two-form statement.**  Dropping the host `M` from
`AscCrux1` — i.e. asking only that *inside one standard form* the continuation after an
ascending copy root be dominated by the shifted body — is **FALSE**: 15289 violations /
115859 instances on the same closure (smallest witness
`N = (0,0)(1,1)(2,1)(3,0)(4,1)(5,1)` at the copy pair `(2,1) … (4,1)`, where the
continuation `(5,1)` exceeds the shifted body `(5,0)`).  So the constraint really comes
from the *existence of the companion standard form* `M = G ++ blk ++ [(v0+d0, w0+1)]`,
which is precisely the shape of a Bachmann/coefficient-domination hypothesis, not of any
local invariant of `N` (`blockok`, `r1ok`, `z0ok`, `cnf` are all local and all hold in
that counterexample).
-/
import YAPSS.Mechanized
import YAPSS.Gterm0Olt
import YAPSS.Seqlex
import YAPSS.Nrmstep

namespace YAPSS
open Three

/-! ## Part 0 — `seqlex` plumbing

`olt_ST_iff_seqlex` (Seqlex.lean:709) turns the whole statement into a purely
combinatorial one about the *column-lexicographic* order on pair sequences.
This section collects the list-level facts about `seqlex` that the reduction
needs (they are absent from `Seqlex.lean`, which only needed the two
directions of the iso). -/

theorem pairlt_trans {p q r : ℕ × ℕ} (h1 : pairlt p q) (h2 : pairlt q r) :
    pairlt p r := by
  unfold pairlt at *; omega

theorem pairlt_irrefl (p : ℕ × ℕ) : ¬ pairlt p p := by
  unfold pairlt; omega

theorem pairlt_total (p q : ℕ × ℕ) : pairlt p q ∨ p = q ∨ pairlt q p := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  unfold pairlt
  simp only [Prod.mk.injEq]
  omega

/-- `seqlex` is transitive. -/
theorem seqlex_trans : ∀ {A B C : PairSeq}, seqlex A B → seqlex B C → seqlex A C := by
  intro A
  induction A with
  | nil =>
    intro B C _ h2
    rcases C with _ | ⟨c, C'⟩
    · rcases B with _ | ⟨b, B'⟩
      · exact absurd h2 (by simp)
      · exact absurd h2 (by simp)
    · simp
  | cons a A' ih =>
    intro B C h1 h2
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h1 (by simp)
    rcases C with _ | ⟨c, C'⟩
    · exact absurd h2 (by simp)
    rw [seqlex_cons_cons] at h1 h2 ⊢
    rcases h1 with p1 | ⟨rfl, s1⟩ <;> rcases h2 with p2 | ⟨rfl, s2⟩
    · exact Or.inl (pairlt_trans p1 p2)
    · exact Or.inl p1
    · exact Or.inl p2
    · exact Or.inr ⟨rfl, ih s1 s2⟩

theorem seqlex_irrefl : ∀ (A : PairSeq), ¬ seqlex A A := by
  intro A
  induction A with
  | nil => simp
  | cons a A' ih =>
    rw [seqlex_cons_cons]
    rintro (h | ⟨-, h⟩)
    · exact pairlt_irrefl a h
    · exact ih h

/-- `≤` version of `seqlex`. -/
def sle (M N : PairSeq) : Prop := M = N ∨ seqlex M N

theorem sle_refl (M : PairSeq) : sle M M := Or.inl rfl

/-- `seqlex` is a linear order, so `sle` is exactly the negation of the strict
order the other way.  (Turns every `sle` goal into a *no-overshoot* goal, which
is the useful polarity for the copy-tiling arguments: one only ever has to rule
out that the continuation strictly exceeds the copy word.) -/
theorem sle_iff_not_seqlex {A B : PairSeq} : sle A B ↔ ¬ seqlex B A := by
  constructor
  · rintro (rfl | h) hBA
    · exact seqlex_irrefl _ hBA
    · exact seqlex_irrefl _ (seqlex_trans h hBA)
  · intro h
    rcases seqlex_total A B with he | hs | hs
    · exact Or.inl he
    · exact Or.inr hs
    · exact absurd hs h

theorem sle_seqlex_trans {A B C : PairSeq} (h1 : sle A B) (h2 : seqlex B C) :
    seqlex A C := by
  rcases h1 with rfl | h1
  · exact h2
  · exact seqlex_trans h1 h2

theorem seqlex_sle_trans {A B C : PairSeq} (h1 : seqlex A B) (h2 : sle B C) :
    seqlex A C := by
  rcases h2 with rfl | h2
  · exact h1
  · exact seqlex_trans h1 h2

/-- `seqlex` is monotone under extending the *larger* side on the right. -/
theorem seqlex_append_mono : ∀ {A B : PairSeq}, seqlex A B → ∀ (C : PairSeq),
    seqlex A (B ++ C) := by
  intro A
  induction A with
  | nil =>
    intro B h C
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h (by simp)
    · simp
  | cons a A' ih =>
    intro B h C
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h (by simp)
    · rw [seqlex_cons_cons] at h
      rcases h with hp | ⟨rfl, hs⟩
      · exact Or.inl hp
      · exact Or.inr ⟨rfl, ih hs C⟩

/-- `sle` version of `seqlex_append_mono`. -/
theorem sle_append_mono {A B : PairSeq} (h : sle A B) (C : PairSeq) :
    sle A (B ++ C) := by
  rcases h with rfl | h
  · rcases C with _ | ⟨c, C'⟩
    · exact Or.inl (by simp)
    · exact Or.inr (seqlex_prefix (by simp) A)
  · exact Or.inr (seqlex_append_mono h C)

/-- Extending on the right strictly increases (`seqlex_prefix`, `≤` form). -/
theorem sle_append_right {A B : PairSeq} (h : sle A B) (C : PairSeq) (hC : C ≠ []) :
    seqlex A (B ++ C) :=
  sle_seqlex_trans h (seqlex_prefix hC B)

/-- **Snoc case analysis.**  A sequence below `D ++ [lp]` either stays `≤ D`,
or extends `D` by a first column strictly below `lp`.  This is the shape that
drives every branch of the cofinality proof. -/
theorem seqlex_snoc_cases : ∀ {D : PairSeq} {lp : ℕ × ℕ} {N : PairSeq},
    seqlex N (D ++ [lp]) →
    sle N D ∨ ∃ q S, N = D ++ q :: S ∧ pairlt q lp := by
  intro D
  induction D with
  | nil =>
    intro lp N h
    rcases N with _ | ⟨q, S⟩
    · exact Or.inl (sle_refl _)
    · rw [List.nil_append, seqlex_cons_cons] at h
      rcases h with h | ⟨rfl, h⟩
      · exact Or.inr ⟨q, S, rfl, h⟩
      · exact absurd h (by cases S <;> simp)
  | cons d D' ih =>
    intro lp N h
    rcases N with _ | ⟨q, S⟩
    · exact Or.inl (Or.inr (by simp))
    rw [List.cons_append, seqlex_cons_cons] at h
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl (Or.inr (Or.inl h))
    · rcases ih h with hle | ⟨q', S', rfl, hq'⟩
      · refine Or.inl ?_
        rcases hle with rfl | hle
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨rfl, hle⟩)
      · exact Or.inr ⟨q', S', by simp, hq'⟩

/-! ## Part 1 — the reduction to `seqlex`

`pss_cofinality` follows from its `seqlex` form, because `translate` is an
order isomorphism onto `<o` on standard forms (`olt_ST_iff_seqlex`). -/

/-- The `seqlex` form of PSS Bachmann cofinality. -/
def SeqlexCofinality : Prop :=
  ∀ {M N : PairSeq}, ST_PS M → ST_PS N → seqlex N M →
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧)

theorem pss_cofinality_of_seqlex (H : SeqlexCofinality)
    {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) := by
  have hne : N ≠ M := by
    rintro rfl; exact olt_irrefl _ h
  have hsl : seqlex N M := (olt_ST_iff_seqlex hN hM hne).1 h
  obtain ⟨n, hn, hres⟩ := H hM hN hsl
  refine ⟨n, hn, ?_⟩
  rcases hres with rfl | hlt
  · exact Or.inr rfl
  · by_cases he : N = M⟦n⟧
    · exact Or.inr (by rw [he])
    · exact Or.inl ((olt_ST_iff_seqlex hN (ST_PS.oper hM hn) he).2 hlt)

/-! ## Part 2 — the degenerate branches of `oper` -/

theorem entry_zero (M : PairSeq) (j : ℕ) : entry M 0 j = (M.getD j (0, 0)).1 := by
  unfold entry; rw [if_pos rfl]

theorem entry_one (M : PairSeq) (j : ℕ) : entry M 1 j = (M.getD j (0, 0)).2 := by
  unfold entry; rw [if_neg one_ne_zero]

theorem dropLast_snoc_getD {M : PairSeq} (hne : M ≠ []) :
    M.dropLast ++ [M.getD (M.length - 1) (0, 0)] = M := by
  have hlen : 0 < M.length := List.length_pos_of_ne_nil hne
  have h1 : M.getD (M.length - 1) (0, 0) = M.getLast hne := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      List.getLast_eq_getElem]
    rfl
  rw [h1, List.dropLast_append_getLast]

/-- **Branch `self`**: `M` has length `≤ 1`, so `M⟦n⟧ = M` and the hypothesis
is already the conclusion. -/
theorem seqlex_cof_short {M N : PairSeq} (hL : M.length - 1 = 0) (h : seqlex N M) :
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) :=
  ⟨1, le_rfl, Or.inr (by rw [oper_eq_self_of_short 1 hL]; exact h)⟩

/-- **Branch `zero`**: the last column is `(0,0)`, so `M⟦n⟧ = M.dropLast`.
Nothing can squeeze strictly between `M.dropLast` and `M.dropLast ++ [(0,0)]`
because `(0,0)` is the `pairlt`-minimum. -/
theorem seqlex_cof_zero {M N : PairSeq} (hL : 1 < M.length)
    (hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0)
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
  have hne : M ≠ [] := by intro he; rw [he] at hL; simp at hL
  have hlpz : M.getD (M.length - 1) (0, 0) = (0, 0) := by
    rw [entry_zero] at hz
    rw [entry_one] at hz
    exact Prod.ext hz.1 hz.2
  have hMsplit : M.dropLast ++ [M.getD (M.length - 1) (0, 0)] = M :=
    dropLast_snoc_getD hne
  have hop : M⟦1⟧ = M.dropLast := by
    rw [oper_eq_pred_of_zero 1 (by omega) hz]
    unfold Pred; rw [if_neg (by omega)]
  refine ⟨1, le_rfl, ?_⟩
  rw [hop]
  rcases seqlex_snoc_cases (D := M.dropLast) (lp := M.getD (M.length - 1) (0, 0))
      (N := N) (by rw [hMsplit]; exact h) with hle | ⟨q, S, -, hq⟩
  · exact hle
  · rw [hlpz] at hq
    exact absurd hq (by simp [pairlt])

/-- **The `noparent` branch is empty on `ST_PS`** (`hp_last`, Nrmstep.lean:5990):
every standard form whose last column is not `(0,0)` does have a unique parent. -/
theorem hasParent_last_ST_PS {M : PairSeq} (hM : ST_PS M) (hlen : 0 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0)) :
    hasParent M (idx1 M (M.length - 1)) (M.length - 1) := by
  refine hp_last (blockok_ST_PS hM) (z0ok_ST_PS hM) hlen ?_
  intro he
  exact hz ⟨by rw [entry_zero, he], by rw [entry_one, he]⟩

/-! ## Part 3 — the bad branch: reduction to the copy-tiling crux -/

/-- The `oper_bad_blocks` copy list *is* `Wf.copies` (the `shiftr0`-packaged
form used by the CNF proofs). -/
theorem flatMap_eq_copies (blk : PairSeq) (d0 n : ℕ) :
    (List.range n).flatMap (fun k => blk.map fun p => (p.1 + k * d0, p.2))
      = copies d0 blk n := rfl

theorem sle_append_cancel (A : PairSeq) {u v : PairSeq} :
    sle (A ++ u) (A ++ v) ↔ sle u v := by
  unfold sle
  rw [seqlex_append_cancel]
  constructor
  · rintro (h | h)
    · exact Or.inl (List.append_cancel_left h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem getD_append_right' (A B : PairSeq) (i : ℕ) :
    (A ++ B).getD (A.length + i) (0, 0) = B.getD i (0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

theorem getD_last_of_snoc (D : PairSeq) (lp : ℕ × ℕ) :
    (D ++ [lp]).getD ((D ++ [lp]).length - 1) (0, 0) = lp := by
  have hl : (D ++ [lp]).length - 1 = D.length := by simp
  rw [hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

/-- **The row-`1` `+1` discipline at the last column.**  If the last column of
a standard-shaped host has row-`1` parent `j0` (`nextrel1`), then its row-`1`
value is *exactly* one above the parent's.

Proof: take the first `nextrel0`-step `j0 → c` of the row-`0` ancestor chain
`le0 M j0 j1`.  `r1ok` at `c` gives `row1 c ≤ row1 (parent₀ c) + 1`, and the
`nextrel0`-parent is unique, so `parent₀ c = j0`; the `nextrel1` minimality
gives `row1 j1 ≤ row1 c`.  Together with `row1 j0 < row1 j1` this pins the
value.  (Model-verified: `tools/probe_cof_asc.py` fact A1, 0 violations.) -/
theorem nextrel1_snd_succ {M : PairSeq} (hr : r1ok M) {j0 j1 : ℕ}
    (h : nextrel1 M j0 j1) : entry M 1 j1 = entry M 1 j0 + 1 := by
  obtain ⟨hj0, hj1, hlt, hincr, hle0, hmin⟩ := h
  -- the first step of the row-`0` ancestor chain out of `j0`
  obtain ⟨c, hstep, hchain⟩ :
      ∃ c, nextrel0 M j0 c ∧ Relation.ReflTransGen (nextrel0 M) c j1 := by
    rcases Relation.ReflTransGen.cases_head hle0.2.2 with he | h
    · exact absurd he (by omega)
    · exact h
  have hcj0 : j0 < c := hstep.2.2.1
  have hclen : c < M.length := hstep.2.1
  have hcj1 : le0 M c j1 := ⟨hclen, hj1, hchain⟩
  have h1 : entry M 1 j1 ≤ entry M 1 c := hmin c ⟨hcj0, hcj1⟩
  -- `r1ok` at `c`: its row-`0` climbing parent is the (unique) `nextrel0` parent `j0`
  have hc0 : 0 < (M.getD c (0, 0)).1 := by
    have := hstep.2.2.2.1
    rw [entry_zero, entry_zero] at this
    omega
  obtain ⟨k, hkc, hk1, hkmin, hk2⟩ := hr c hclen hc0
  have hnk : nextrel0 M k c := by
    refine ⟨by omega, hclen, hkc, ?_, ?_⟩
    · rw [entry_zero, entry_zero]; omega
    · intro l hl
      rw [entry_zero, entry_zero]
      exact hkmin l hl.1 hl.2
  have hkj0 : k = j0 := nextrel0_unique hnk hstep
  have h2 : entry M 1 c ≤ entry M 1 j0 + 1 := by
    rw [entry_one, entry_one, ← hkj0]
    exact hk2
  omega

/-- **The bad-branch decomposition, uniformly in `n`.**  `oper_bad_blocks`
produces its block data per copy count; the parent is unique (`hasParent`), so
the data is in fact the same for every `n`.  This packages it once and for all,
in the `copies`/`shiftr0` form. -/
theorem oper_bad_blocks_all {M : PairSeq} (L : 1 < M.length) (hst : steps1 M)
    (hr : r1ok M)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)) :
    ∃ (G : PairSeq) (v0 w0 : ℕ) (R : PairSeq) (d0 : ℕ) (lp : ℕ × ℕ),
      M = G ++ ((v0, w0) :: R) ++ [lp] ∧
      (∀ n, 1 ≤ n → M⟦n⟧ = G ++ copies d0 ((v0, w0) :: R) n) ∧
      (∀ x ∈ R, v0 < x.1) ∧ v0 < lp.1 ∧
      ((d0 = 0 ∧ lp.2 = 0 ∧ lp.1 = v0 + 1)
        ∨ (0 < d0 ∧ lp.2 = w0 + 1 ∧ lp.1 = v0 + d0
            ∧ nextrel1 M G.length (M.length - 1))) := by
  obtain ⟨G, v0, w0, R, d0, lp, hM1, -, R_gt, lp_gt, disj, hnR⟩ :=
    oper_bad_blocks (n := 1) L hz hp le_rfl
  -- the dropped column is the last column of `M`
  have hlpM : lp = M.getD (M.length - 1) (0, 0) := by
    conv_rhs => rw [hM1]
    exact (getD_last_of_snoc _ _).symm
  -- positional data used by the `idx1 = 0` branch
  have hM1' : M = G ++ (((v0, w0) :: R) ++ [lp]) := by rw [hM1, List.append_assoc]
  have hlenM : M.length = G.length + (R.length + 2) := by
    rw [hM1']; simp
  have hGd : M.getD G.length (0, 0) = (v0, w0) := by
    have h := getD_append_right' G (((v0, w0) :: R) ++ [lp]) 0
    rw [← hM1'] at h
    simpa using h
  have hGd1 : M.getD (G.length + 1) (0, 0) = (R ++ [lp]).getD 0 (0, 0) := by
    have h := getD_append_right' G (((v0, w0) :: R) ++ [lp]) 1
    rw [← hM1'] at h
    simpa using h
  -- the `idx1 = 0` branch pins `lp.2 = 0` and `lp.1 = v0 + 1`
  have hdisj' : (d0 = 0 ∧ lp.2 = 0 ∧ lp.1 = v0 + 1)
      ∨ (0 < d0 ∧ lp.2 = w0 + 1 ∧ lp.1 = v0 + d0
          ∧ nextrel1 M G.length (M.length - 1)) := by
    rcases disj with ⟨h0, hi⟩ | ⟨h1, h2, h3, hn1⟩
    · have hlp2 : lp.2 = 0 := by
        unfold idx1 at hi
        split at hi
        · exact absurd hi one_ne_zero
        · rw [hlpM, ← entry_one]; omega
      refine Or.inl ⟨h0, hlp2, ?_⟩
      -- the row-`0` parent is at `G.length`, so no column in between dips below `lp.1`
      have hn0 : nextrel0 M G.length (M.length - 1) := by
        have := hnR
        rw [hi, nextR_zero_iff] at this
        exact this
      have hj1 : M.length - 1 = G.length + 1 + R.length := by omega
      have hstep : entry M 0 (G.length + 1) ≤ entry M 0 G.length + 1 := by
        have := steps1_iff.1 hst G.length (by omega)
        rw [entry_zero, entry_zero]
        exact this
      have hv0 : entry M 0 G.length = v0 := by rw [entry_zero, hGd]
      have hlp1 : lp.1 = entry M 0 (M.length - 1) := by rw [entry_zero, ← hlpM]
      have hmin : entry M 0 (M.length - 1) ≤ entry M 0 (G.length + 1) := by
        rcases Nat.eq_or_lt_of_le (show G.length + 1 ≤ M.length - 1 by omega) with he | hlt
        · rw [← he]
        · exact hn0.2.2.2.2 (G.length + 1) ⟨by omega, hlt⟩
      omega
    · refine Or.inr ⟨h1, ?_, h3, hn1⟩
      have hs := nextrel1_snd_succ hr hn1
      rw [entry_one, entry_one, ← hlpM, hGd] at hs
      exact hs
  refine ⟨G, v0, w0, R, d0, lp, hM1, ?_, R_gt, lp_gt, hdisj'⟩
  intro n hn
  obtain ⟨G', v0', w0', R', d0', lp', hM2, hMn2, -, -, disj', hnR'⟩ :=
    oper_bad_blocks (n := n) L hz hp hn
  -- the two decompositions agree: the parent index is unique
  have hlen : G'.length = G.length := hp.unique hnR' hnR
  have heq : (G' ++ ((v0', w0') :: R')) ++ [lp'] = (G ++ ((v0, w0) :: R)) ++ [lp] :=
    hM2.symm.trans hM1
  obtain ⟨hGb, hlpe⟩ := List.append_inj' heq rfl
  obtain ⟨rfl, hblk⟩ := List.append_inj hGb hlen
  have hlp' : lp' = lp := by simpa using hlpe
  obtain ⟨hv, hR'⟩ : (v0', w0') = (v0, w0) ∧ R' = R := by
    exact ⟨by simpa using congrArg (fun l => l.headI) hblk, by
      simpa using congrArg (fun l => l.tail) hblk⟩
  obtain ⟨rfl, rfl⟩ : v0' = v0 ∧ w0' = w0 := ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩
  subst hR'
  -- and so does the shift
  have hd : d0' = d0 := by
    have hi1 : ∀ {e : ℕ}, nextrel1 M e (M.length - 1) → idx1 M (M.length - 1) ≠ 0 := by
      intro e hne he
      have hlt : entry M 1 e < entry M 1 (M.length - 1) := hne.2.2.2.1
      unfold idx1 at he
      split at he
      · exact one_ne_zero he
      · omega
    rcases disj with ⟨h0, hi⟩ | ⟨-, -, h3, hn1⟩ <;>
      rcases disj' with ⟨h0', hi'⟩ | ⟨-, -, h3', hn1'⟩
    · rw [h0, h0']
    · exact absurd hi (hi1 hn1')
    · exact absurd hi' (hi1 hn1)
    · rw [hlp'] at h3'; omega
  rw [hMn2, hd]
  rfl

/-! ## Part 4 — the exact-copy (`d0 = 0`) half of the crux

Here the copies are *identical* (`shiftr0 0 = id`), so `M⟦n⟧` repeats the block
`blk = (v0,w0) :: R` verbatim.  The engine is **CNF**: inside a standard form
the level-`v0` siblings are `≤o`-non-increasing, so every further sibling of
the `blk` root either drops strictly below `blk` (done at once) or reproduces
it exactly (recurse on the strictly shorter remainder). -/

/-- **Splice.**  A strictly smaller argument block stays smaller once the
tails are attached, provided the left tail re-opens at or below the block base
while every column of the right block is strictly above it. -/
theorem seqlex_splice : ∀ {A B : PairSeq}, seqlex A B →
    ∀ {U : PairSeq}, (U = [] ∨ ∀ x ∈ B, pairlt (U.headI) x) →
    ∀ (C : PairSeq), seqlex (A ++ U) (B ++ C) := by
  intro A
  induction A with
  | nil =>
    intro B h U hU C
    rcases B with _ | ⟨b0, B'⟩
    · exact absurd h (by simp)
    · rcases U with _ | ⟨u, U'⟩
      · simp
      · refine Or.inl ?_
        rcases hU with h' | h'
        · exact absurd h' (by simp)
        · simpa using h' b0 (by simp)
  | cons a A' ihA =>
    intro B h U hU C
    rcases B with _ | ⟨b0, B'⟩
    · exact absurd h (by simp)
    · rw [seqlex_cons_cons] at h
      rcases h with hp | ⟨rfl, hs⟩
      · exact Or.inl hp
      · refine Or.inr ⟨rfl, ihA hs ?_ C⟩
        rcases hU with h' | h'
        · exact Or.inl h'
        · exact Or.inr (fun x hx => h' x (List.mem_cons_of_mem _ hx))

/-- The block split at the base level: `R` is exactly the leading run above
`v0` and `Y` exactly the rest. -/
theorem split_block {v0 : ℕ} {R Y : PairSeq} (hRgt : ∀ x ∈ R, v0 < x.1)
    (hYhd : Y = [] ∨ ¬ v0 < (Y.headI).1) :
    (R ++ Y).takeWhile (fun q => v0 < q.1) = R ∧
    (R ++ Y).dropWhile (fun q => v0 < q.1) = Y := by
  have hR' : ∀ x ∈ R, (fun q : ℕ × ℕ => decide (v0 < q.1)) x = true := by
    intro x hx; simpa using hRgt x hx
  rcases hYhd with rfl | hY
  · exact ⟨by simpa using List.takeWhile_eq_self_iff.2 hR',
      by simpa using List.dropWhile_eq_nil_iff.2 hR'⟩
  · rcases Y with _ | ⟨y, Y'⟩
    · exact ⟨by simpa using List.takeWhile_eq_self_iff.2 hR',
        by simpa using List.dropWhile_eq_nil_iff.2 hR'⟩
    · simp only [List.headI] at hY
      exact ⟨by rw [takeWhile_append_all hR']; simp [hY],
        by rw [dropWhile_append_all hR']; simp [hY]⟩

/-- **Exact-copy domination (`d0 = 0`).**  The level-`v0` remainder `Y` after a
block `blk = (v0,w0) :: R` of a CNF standard form is dominated by finitely many
verbatim copies of `blk`. -/
theorem copy_dom_zero : ∀ (d : ℕ) (Y : PairSeq) (v0 w0 : ℕ) (R : PairSeq),
    Y.length ≤ d →
    blockok v0 ((v0, w0) :: (R ++ Y)) →
    (∀ x ∈ R, v0 < x.1) →
    (Y = [] ∨ ¬ v0 < (Y.headI).1) →
    cnf (translate ((v0, w0) :: (R ++ Y))) →
    ∃ m, 1 ≤ m ∧ sle Y (copies 0 ((v0, w0) :: R) m) := by
  intro d
  induction d with
  | zero =>
    intro Y v0 w0 R hlen _ _ _ _
    have hY : Y = [] := by
      cases Y with
      | nil => rfl
      | cons y Y' => simp at hlen
    subst hY
    exact ⟨1, le_rfl, Or.inr (by rw [copies_one]; simp)⟩
  | succ d ih =>
    intro Y v0 w0 R hlen hbo hRgt hYhd hcnf
    rcases Y with _ | ⟨y, Y'⟩
    · exact ⟨1, le_rfl, Or.inr (by rw [copies_one]; simp)⟩
    -- the head of `Y` sits exactly at level `v0`
    have hyv : y.1 = v0 := by
      have h1 : v0 ≤ y.1 := hbo.2.1 y (by simp)
      have h2 : ¬ v0 < y.1 := by
        rcases hYhd with h' | h'
        · exact absurd h' (by simp)
        · simpa using h'
      omega
    have hy : y = (v0, y.2) := Prod.ext hyv rfl
    -- split `Y'` into the descendant block `R'` and the remainder `Y''`
    set R' := Y'.takeWhile (fun q => v0 < q.1) with hR'def
    set Y'' := Y'.dropWhile (fun q => v0 < q.1) with hY''def
    have hY'split : R' ++ Y'' = Y' := List.takeWhile_append_dropWhile
    have hR'gt : ∀ x ∈ R', v0 < x.1 := by
      intro x hx
      have := List.mem_takeWhile_imp hx
      simpa using this
    have hY''hd : Y'' = [] ∨ ¬ v0 < (Y''.headI).1 := by
      rcases hd : Y'' with _ | ⟨z, Z⟩
      · exact Or.inl rfl
      · refine Or.inr ?_
        have h := List.head?_dropWhile_not (fun q : ℕ × ℕ => decide (v0 < q.1)) Y'
        rw [← hY''def, hd] at h
        simpa using h
    -- the two `translate` shapes
    have hTy : translate (y :: Y') = P y.2 (translate R') (translate Y'') := by
      rw [hy]
      have : ((v0, y.2) :: R') ++ Y'' = (v0, y.2) :: Y' := by
        rw [List.cons_append, hY'split]
      rw [← this]
      exact translate_block_append hR'gt hY''hd
    have hTall : translate ((v0, w0) :: (R ++ (y :: Y')))
        = P w0 (translate R) (translate (y :: Y')) := by
      have : ((v0, w0) :: R) ++ (y :: Y') = (v0, w0) :: (R ++ (y :: Y')) := by
        rw [List.cons_append]
      rw [← this]
      exact translate_block_append hRgt hYhd
    rw [hTall, hTy] at hcnf
    obtain ⟨cR, hsib, ctail⟩ := cnf_P_P.1 hcnf
    -- CNF at the sibling boundary: `y.2 ≤ w0`
    have hy2 : y.2 ≤ w0 := by
      by_contra hcon
      exact hsib (olt_P_P.2 (Or.inl (by omega)))
    rcases Nat.lt_or_ge y.2 w0 with hlt | hge
    · -- strictly smaller sibling: one copy already dominates
      refine ⟨1, le_rfl, Or.inr ?_⟩
      rw [copies_one, hy]
      exact Or.inl (by unfold pairlt; omega)
    · -- equal subscripts: CNF compares the two bodies
      have hy2eq : y.2 = w0 := by omega
      have hyw : y = (v0, w0) := by rw [hy, hy2eq]
      have hnolt : ¬ (translate R <o translate R') := by
        intro hcon
        exact hsib (olt_P_P.2 (Or.inr (Or.inl ⟨hy2eq.symm, hcon⟩)))
      -- the two bodies are depth-`v0+1` blocks
      have hsp := split_block hRgt hYhd
      have hboY : blockok v0 (y :: Y') := by
        have := blockok_tail (d := v0) (y := w0) (r := R ++ (y :: Y')) hbo
        rwa [hsp.2] at this
      have hboR : blockok (v0 + 1) R := by
        have := blockok_arg (d := v0) (y := w0) (r := R ++ (y :: Y')) hbo
        rwa [hsp.1] at this
      have hboR' : blockok (v0 + 1) R' := by
        have hboY' : blockok v0 ((v0, y.2) :: Y') := by rw [← hy]; exact hboY
        exact blockok_arg hboY'
      by_cases hRR : R' = R
      · -- the sibling reproduces the block: recurse on the remainder
        have hYeq : y :: Y' = ((v0, w0) :: R) ++ Y'' := by
          rw [hyw, List.cons_append, ← hY'split, hRR]
        have hlen'' : Y''.length ≤ d := by
          have h1 : (R' ++ Y'').length = Y'.length := by rw [hY'split]
          simp only [List.length_append] at h1
          simp only [List.length_cons] at hlen
          omega
        have hbo'' : blockok v0 ((v0, w0) :: (R ++ Y'')) := by
          rw [← List.cons_append, ← hYeq]; exact hboY
        have hcnf'' : cnf (translate ((v0, w0) :: (R ++ Y''))) := by
          rw [← List.cons_append, ← hYeq, hTy]
          exact ctail
        obtain ⟨m, hm, hsle⟩ := ih Y'' v0 w0 R hlen'' hbo'' hRgt hY''hd hcnf''
        refine ⟨m + 1, by omega, ?_⟩
        rw [copies_succ_cons, shiftr0_zero, hYeq, ← List.cons_append]
        exact (sle_append_cancel _).2 hsle
      · -- the sibling body is strictly smaller: two copies suffice
        have hslR : seqlex R' R := by
          rcases seqlex_total R' R with he | h | h
          · exact absurd he hRR
          · exact h
          · exact absurd (seqlex_imp_olt (v0 + 1) R R' hboR hboR' h) hnolt
        refine ⟨2, by omega, Or.inr ?_⟩
        rw [show (2 : ℕ) = 1 + 1 from rfl, copies_succ_cons, shiftr0_zero, copies_one,
          hyw]
        refine Or.inr ⟨rfl, ?_⟩
        rw [← hY'split]
        refine seqlex_splice hslR ?_ _
        rcases hY''hd with h | h
        · exact Or.inl h
        · refine Or.inr (fun x hx => ?_)
          have h1 := hRgt x hx
          unfold pairlt; omega

/-! ## Part 5 — the `d0 = 0` half of the crux, discharged -/

theorem copies_zero_succ (blk : PairSeq) (m : ℕ) :
    copies 0 blk (m + 1) = copies 0 blk m ++ blk := by
  unfold copies
  rw [List.range_succ, List.flatMap_append]
  simp

/-- **The exact-copy branch of the crux is CLOSED.**  When `d0 = 0` the dropped
column is `lp = (v0+1, 0)`, so the continuation `q :: S` of `N` re-opens at or
below `v0`; `copy_dom_zero` then bounds its level-`v0` part by finitely many
copies of the block, and the part below `v0` is `pairlt`-smaller than every
column of the copies. -/
theorem crux_zero {G R S : PairSeq} {v0 w0 : ℕ} {lp q : ℕ × ℕ}
    (hN : ST_PS ((G ++ ((v0, w0) :: R)) ++ q :: S))
    (hRgt : ∀ x ∈ R, v0 < x.1)
    (hlp2 : lp.2 = 0) (hlp1 : lp.1 = v0 + 1)
    (hq : pairlt q lp) :
    ∃ m, 1 ≤ m ∧ sle (q :: S) (copies 0 ((v0, w0) :: R) m) := by
  classical
  -- the continuation re-opens at or below `v0`
  have hqv : q.1 ≤ v0 := by
    rcases hq with h | ⟨-, h⟩
    · omega
    · omega
  rcases Nat.lt_or_ge q.1 v0 with hlt | hge
  · exact ⟨1, le_rfl, Or.inr (by
      rw [copies_one]; exact Or.inl (by unfold pairlt; omega))⟩
  have hqv0 : q.1 = v0 := by omega
  -- split the continuation at the first column strictly below `v0`
  set Y := (q :: S).takeWhile (fun p => v0 ≤ p.1) with hYdef
  set V := (q :: S).dropWhile (fun p => v0 ≤ p.1) with hVdef
  have hYV : Y ++ V = q :: S := List.takeWhile_append_dropWhile
  have hYcons : Y = q :: S.takeWhile (fun p => v0 ≤ p.1) := by
    rw [hYdef, List.takeWhile_cons_of_pos (by simpa using hqv0.ge)]
  have hYhead : (Y.headI).1 = v0 := by rw [hYcons]; simpa using hqv0
  have hYge : ∀ x ∈ Y, v0 ≤ x.1 := by
    intro x hx
    have := List.mem_takeWhile_imp hx
    simpa using this
  have hVhd : V = [] ∨ ∃ z Z, V = z :: Z ∧ z.1 < v0 := by
    rcases hd : V with _ | ⟨z, Z⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨z, Z, rfl, ?_⟩
      have h := List.head?_dropWhile_not (fun p : ℕ × ℕ => decide (v0 ≤ p.1)) (q :: S)
      rw [← hVdef, hd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 ≤ z.1) := by simpa using h
      omega
  -- the level-`v0` window `blk ++ Y` is an infix block of `N`
  have hNsplit : (G ++ ((v0, w0) :: R)) ++ q :: S
      = (G ++ (((v0, w0) :: R) ++ Y)) ++ V := by
    rw [← hYV]; simp
  have hstN : steps1 ((G ++ ((v0, w0) :: R)) ++ q :: S) := (blockok_ST_PS hN).2.2
  have hstBY : steps1 (((v0, w0) :: R) ++ Y) := by
    rw [hNsplit] at hstN
    exact (steps1_append.1 (steps1_append.1 hstN).1).2.1
  have hallBY : ∀ x ∈ ((v0, w0) :: R) ++ Y, v0 ≤ x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact le_rfl
      · exact (hRgt x hx).le
    · exact hYge x hx
  have hbo : blockok v0 (((v0, w0) :: R) ++ Y) := ⟨by intro _; rfl, hallBY, hstBY⟩
  -- CNF of the window: prefix-closure plus `cnf_tail`
  have hcnfN : cnf (translate ((G ++ ((v0, w0) :: R)) ++ q :: S)) := cnf_ST_PS hN
  have hcnfW : cnf (translate ((v0, w0) :: (R ++ Y))) := by
    have h1 : cnf (translate ((G ++ (((v0, w0) :: R) ++ Y)) ++ V)) := by
      rw [← hNsplit]; exact hcnfN
    have h2 : cnf (translate (G ++ (((v0, w0) :: R) ++ Y))) := by
      have := cnf_take h1 (G ++ (((v0, w0) :: R) ++ Y)).length
      rwa [List.take_left] at this
    have h3 : cnf (translate (G ++ ((v0, w0) :: (R ++ Y)))) := by
      rwa [List.cons_append] at h2
    exact cnf_tail (t := (v0, w0)) (T' := R ++ Y)
      (fun x hx => hallBY x (by
        rcases List.mem_append.1 hx with h | h
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
        · exact List.mem_append_right _ h)) G h3
  -- the exact-copy domination
  obtain ⟨m, hm, hsle⟩ := copy_dom_zero Y.length Y v0 w0 R le_rfl
    (by rwa [List.cons_append] at hbo) hRgt (Or.inr (by rw [hYhead]; omega))
    hcnfW
  refine ⟨m + 1, by omega, Or.inr ?_⟩
  rw [← hYV, copies_zero_succ]
  rcases hsle with heq | hlt
  · rw [← heq, seqlex_append_cancel]
    rcases hVhd with hV | ⟨z, Z, hV, hz⟩
    · rw [hV]; simp
    · rw [hV]; exact Or.inl (by unfold pairlt; omega)
  · refine seqlex_splice hlt ?_ _
    rcases hVhd with hV | ⟨z, Z, hV, hz⟩
    · exact Or.inl hV
    · refine Or.inr (fun x hx => ?_)
      have := copies_v0_le (fun y hy => (hRgt y hy).le) 0 m x hx
      rw [hV]
      unfold pairlt
      simp only [List.headI]
      omega

/-- **The residual crux — ascending copies only.**  The `d0 = 0` (exact-copy)
half is discharged below by `crux_zero`; this is what is left: a standard form
`N` that agrees with the host `M` on the *whole* good prefix `G` and bad block
`blk = (v0,w0) :: R`, and then continues with a column strictly below the
dropped column `lp`, is dominated by finitely many **ascending** copies of
`blk`.

Model-verified (`tools/probe_cof_asc.py`, closure `v ≤ 4`, depth 5, `n ≤ 4`,
2041 hosts): the two head-level facts
`lp.2 = w0 + 1` (A1) and `q ≤ (v0+d0, w0)` (A2) hold with 0 violations, and so
does the recursion step
`Y' does not exceed shiftr0 d0 R at the first mismatch` (A3, 6095 instances,
0 violations). -/
def AscCrux : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ} {lp q : ℕ × ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [lp]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ q :: S) →
    (∀ x ∈ R, v0 < x.1) →
    0 < d0 → lp.2 = w0 + 1 → lp.1 = v0 + d0 →
    nextrel1 ((G ++ ((v0, w0) :: R)) ++ [lp]) G.length
      (G ++ ((v0, w0) :: R)).length →
    pairlt q lp →
    ∃ m, 1 ≤ m ∧ sle (q :: S) (shiftr0 d0 (copies d0 ((v0, w0) :: R) m))

/-- **The residual, with the head step taken.**  By `nextrel1_snd_succ` the
dropped column is `lp = (v0+d0, w0+1)`, so a continuation column `q` with
`pairlt q lp` satisfies `q ≤ (v0+d0, w0)` — the head of the first ascending
copy — and the only case that is not immediate is `q = (v0+d0, w0)`.  This is
what remains open. -/
def AscCrux1 : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ (v0 + d0, w0) :: S) →
    (∀ x ∈ R, v0 < x.1) → 0 < d0 →
    nextrel1 ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) G.length
      (G ++ ((v0, w0) :: R)).length →
    ∃ m, 1 ≤ m ∧ sle ((v0 + d0, w0) :: S) (shiftr0 d0 (copies d0 ((v0, w0) :: R) m))

/-! ## Part 6 — the ascending (`d0 > 0`) half: reduction to ONE `≤o`

Because the ascending copies are **nested** (`blk_{k+1}` sits strictly inside
`blk_k`), matching the first copy already exhausts everything the continuation
of `N` can reach: the next copy root is at level `v0 + 2*d0`, strictly deeper
than any column `S` still has after leaving `q`'s subtree.  So — unlike the
exact-copy branch — there is **no recursion** here: two copies always suffice,
and the entire branch collapses to the single inequality

    translate (q's descendant block in `N`)  ≤o  translate R

i.e. *the collapsed node's argument is dominated by the original block body*. -/

theorem shiftr0_length (d : ℕ) (X : PairSeq) : (shiftr0 d X).length = X.length := by
  unfold shiftr0; simp

theorem shiftr0_getD {d : ℕ} {X : PairSeq} {j : ℕ} (hj : j < X.length) :
    (shiftr0 d X).getD j (0, 0) = ((X.getD j (0, 0)).1 + d, (X.getD j (0, 0)).2) := by
  unfold shiftr0
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

theorem steps1_shiftr0 (d : ℕ) {X : PairSeq} (h : steps1 X) : steps1 (shiftr0 d X) := by
  rw [steps1_iff] at h ⊢
  intro j hj
  rw [shiftr0_length] at hj
  rw [shiftr0_getD (by omega), shiftr0_getD (by omega)]
  have := h j hj
  simp only []
  omega

theorem headI_shiftr0 {d : ℕ} {X : PairSeq} (hne : X ≠ []) :
    ((shiftr0 d X).headI).1 = (X.headI).1 + d := by
  rcases X with _ | ⟨x, X'⟩
  · exact absurd rfl hne
  · rfl

theorem mem_shiftr0_le {d : ℕ} (e : ℕ) {X : PairSeq} (h : ∀ x ∈ X, d ≤ x.1) :
    ∀ x ∈ shiftr0 e X, d + e ≤ x.1 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := mem_shiftr0.1 hx
  have := h p hp
  simp only []
  omega

theorem blockok_shiftr0 {d e : ℕ} {X : PairSeq} (h : blockok d X) :
    blockok (d + e) (shiftr0 e X) := by
  refine ⟨?_, mem_shiftr0_le e h.2.1, steps1_shiftr0 e h.2.2⟩
  intro hne
  have hXne : X ≠ [] := by
    intro he; rw [he] at hne; exact hne rfl
  rw [headI_shiftr0 hXne, h.1 hXne]

/-- `shiftr0` commutes with the copy tower (shifting all copies = shifting the
block). -/
theorem shiftr0_copies (d : ℕ) (blk : PairSeq) (n : ℕ) :
    shiftr0 d (copies d blk n) = copies d (shiftr0 d blk) n := by
  unfold copies shiftr0
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_map, List.map_map]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.mk.injEq, and_true]
  omega

/-- **The residual, in its sharpest form.**  `S_hi := S.takeWhile (v0+d0 < ·.1)`
is the descendant block of the ascending copy root `q = (v0+d0, w0)` inside `N`,
and `R ++ copies d0 blk' m` is the descendant block of the *original* block root
inside the host expansion `M⟦m+1⟧` (`blk' = shiftr0 d0 blk`).  All that is
missing for PSS Bachmann cofinality is that the *collapsed argument* is
dominated by the shifted host argument at some stage `m`:

    S_hi  ≤lex  shiftr0 d0 (R ++ copies d0 blk' m).

This is exactly the `∃n, e ≤ c[x_n]` step `(*)` of the Buchholz source's collapse
branch, transposed to BMS copy structure.

It is genuinely a **two-form** statement: dropping the host `M` makes the
corresponding fact FALSE (15289 / 115859 violations on the closure — see the
file header), so it cannot follow from any local invariant of `N` (`blockok`,
`steps1`, `r1ok`, `z0ok`, `cnf` all hold in the counterexample).

REFUTED variant (do **not** retry): the `m`-free form `S_hi ≤lex shiftr0 d0 R`
is FALSE — `M = (0,0)(1,1)`, `N = (0,0)(1,0)(2,0) = M⟦3⟧` gives
`S_hi = [(2,0)]` but `shiftr0 1 R = []` (4390 / 6095 violations).  The reason is
that `S_hi` is *everything* above level `v0+d0`, hence also covers the later
copies — the `m` in the statement above is what accounts for them. -/
def AscArgDom : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ (v0 + d0, w0) :: S) →
    (∀ x ∈ R, v0 < x.1) → 0 < d0 →
    nextrel1 ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) G.length
      (G ++ ((v0, w0) :: R)).length →
    ∃ m, sle (S.takeWhile fun p => v0 + d0 < p.1)
      (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R)) m))

/-- **`AscArgDom` with an explicit witness.**  The stage `m := |S_hi|` always
works (model-verified, 0 violations / 140, 294, 692 instances at closure
`+5/+6/+7`), so the existential can be eliminated.  Note this removes the
*search* for `m`, not the content: what remains is still the no-overshoot
comparison, which is decided by a **row-1** inequality in 4047 of 6095 measured
instances (only 297 by a row-0 drop), so it is not a pure length/prefix fact. -/
def AscArgDomExplicit : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ (v0 + d0, w0) :: S) →
    (∀ x ∈ R, v0 < x.1) → 0 < d0 →
    nextrel1 ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) G.length
      (G ++ ((v0, w0) :: R)).length →
    sle (S.takeWhile fun p => v0 + d0 < p.1)
      (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R))
        (S.takeWhile fun p => v0 + d0 < p.1).length))

theorem ascArgDom_of_explicit (H : AscArgDomExplicit) : AscArgDom := by
  intro G R S v0 w0 d0 hM hN hR hd hnr
  exact ⟨_, H hM hN hR hd hnr⟩

theorem shiftr0_append (d : ℕ) (A B : PairSeq) :
    shiftr0 d (A ++ B) = shiftr0 d A ++ shiftr0 d B := List.map_append

theorem copies_succ_back (d : ℕ) (blk : PairSeq) (n : ℕ) :
    copies d blk (n + 1) = copies d blk n ++ shiftr0 (n * d) blk := by
  unfold copies
  rw [List.range_succ, List.flatMap_append]
  simp

/-- **The ascending branch needs only ONE extra copy beyond the witness**:
`AscArgDom` at stage `m` closes it at `m + 2` copies. -/
theorem asc_crux1_of_argdom (H : AscArgDom) : AscCrux1 := by
  intro G R S v0 w0 d0 hM hN hRgt hd hnr
  classical
  obtain ⟨m, hdom⟩ := H hM hN hRgt hd hnr
  set Shi := S.takeWhile (fun p => v0 + d0 < p.1) with hShidef
  set Slo := S.dropWhile (fun p => v0 + d0 < p.1) with hSlodef
  have hSsplit : Shi ++ Slo = S := List.takeWhile_append_dropWhile
  set blk' := shiftr0 d0 ((v0, w0) :: R) with hblk'
  have hblk'cons : blk' = (v0 + d0, w0) :: shiftr0 d0 R := by
    rw [hblk', shiftr0_cons]
  -- every column of the host argument is strictly above `v0`
  have hDmGt : ∀ x ∈ R ++ copies d0 blk' m, v0 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hRgt x hx
    · rw [hblk'cons] at hx
      have := copies_v0_le (v0 := v0 + d0) (w0 := w0) (R := shiftr0 d0 R)
        (mem_shiftr0_le d0 (fun y hy => (hRgt y hy).le)) d0 m x hx
      omega
  -- the tail below the copy root
  have hSloHd : Slo = [] ∨ (Slo.headI).1 ≤ v0 + d0 := by
    rcases hdd : Slo with _ | ⟨z, Z⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h := List.head?_dropWhile_not (fun p : ℕ × ℕ => decide (v0 + d0 < p.1)) S
      rw [← hSlodef, hdd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 + d0 < z.1) := by simpa using h
      simp only [List.headI]
      omega
  refine ⟨m + 2, by omega, ?_⟩
  -- unfold the target into: copy root, host argument, one further copy
  have hinner : shiftr0 d0 (copies d0 blk' (m + 1))
      = shiftr0 d0 (copies d0 blk' m) ++ shiftr0 d0 (shiftr0 (m * d0) blk') := by
    rw [copies_succ_back, shiftr0_append]
  have htgt : shiftr0 d0 (copies d0 ((v0, w0) :: R) (m + 2))
      = (v0 + d0, w0) :: (shiftr0 d0 (R ++ copies d0 blk' m)
          ++ shiftr0 d0 (shiftr0 (m * d0) blk')) := by
    rw [shiftr0_copies, ← hblk', copies_succ_front, hinner, shiftr0_append,
      List.append_assoc]
    conv_lhs => rw [hblk'cons]
    rw [List.cons_append, ← hblk'cons]
  rw [htgt]
  have hEne : shiftr0 d0 (shiftr0 (m * d0) blk') ≠ [] := by
    rw [hblk'cons]; simp [shiftr0]
  have hEhd : ((shiftr0 d0 (shiftr0 (m * d0) blk')).headI).1 = v0 + d0 + m * d0 + d0 := by
    rw [hblk'cons, shiftr0_cons, shiftr0_cons]
    simp
  show sle ([((v0 + d0 : ℕ), (w0 : ℕ))] ++ S)
    ([((v0 + d0 : ℕ), (w0 : ℕ))] ++ _)
  rw [sle_append_cancel]
  rcases hdom with heq | hlt
  · -- the argument is reproduced verbatim: one further copy dominates the drop
    have hS : S = shiftr0 d0 (R ++ copies d0 blk' m) ++ Slo := by
      rw [← hSsplit, heq]
    rw [hS]
    refine (sle_append_cancel _).2 ?_
    rcases hSloHd with h | h
    · rw [h]; exact Or.inr (by simpa using hEne)
    · rcases hdd : Slo with _ | ⟨z, Z⟩
      · exact Or.inr (by simpa using hEne)
      · rcases hb : shiftr0 d0 (shiftr0 (m * d0) blk') with _ | ⟨b, B⟩
        · exact absurd hb hEne
        · refine Or.inr (Or.inl ?_)
          rw [hdd] at h
          rw [hb] at hEhd
          simp only [List.headI] at h hEhd
          unfold pairlt
          omega
  · -- strictly smaller argument: splice the sub-`v0+d0` tail past it
    refine Or.inr ?_
    rw [← hSsplit]
    refine seqlex_splice hlt ?_ _
    rcases hSloHd with h | h
    · exact Or.inl h
    · refine Or.inr (fun x hx => ?_)
      obtain ⟨y, hy, rfl⟩ := mem_shiftr0.1 hx
      have := hDmGt y hy
      unfold pairlt
      simp only []
      omega

/-- **Monotonicity of the copy-tower bound in the stage `m`.**  This is what
lets a "witness per constituent, then take the max" argument (the shape of the
source's `(*)` proof) go through: a bound at stage `m` survives at every later
stage. -/
theorem argdom_bound_mono {X R : PairSeq} {v0 w0 d0 m : ℕ}
    (h : sle X (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R)) m))) :
    sle X (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R)) (m + 1))) := by
  have he : shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R)) (m + 1))
      = shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R)) m)
        ++ shiftr0 d0 (shiftr0 (m * d0) (shiftr0 d0 ((v0, w0) :: R))) := by
    rw [copies_succ_back, ← List.append_assoc, shiftr0_append]
  rw [he]
  exact sle_append_mono h _

/-- Iterated form: the bound survives to every later stage. -/
theorem argdom_bound_mono_le {X R : PairSeq} {v0 w0 d0 m m' : ℕ} (hm : m ≤ m')
    (h : sle X (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R)) m))) :
    sle X (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R)) m')) := by
  obtain ⟨t, rfl⟩ : ∃ t, m' = m + t := ⟨m' - m, by omega⟩
  induction t with
  | zero => exact h
  | succ t ih => exact argdom_bound_mono (ih (by omega))

/-- **The first column of the collapsed argument is pinned.**  The column right
after the ascending copy root `q = (v0+d0, w0)` that still lies above `q` sits at
level exactly `v0+d0+1` and carries row-1 at most `w0 + 1`: its `r1ok` climbing
parent can only be `q` itself (anything earlier would have to pass through `q`,
whose row-0 is too small).

This is the `k = 0` half of `AscArgDom`: paired with `R.headI.2 ≥ w0 + 1` (CNF of
the host plus `nextrel1` minimality — NOT yet proved) it settles the first
column of the comparison. -/
theorem asc_first_column {G R S : PairSeq} {v0 w0 d0 : ℕ}
    (hN : ST_PS ((G ++ ((v0, w0) :: R)) ++ (v0 + d0, w0) :: S))
    {z : ℕ × ℕ} {Z : PairSeq} (hS : S = z :: Z) (hz : v0 + d0 < z.1) :
    z.1 = v0 + d0 + 1 ∧ z.2 ≤ w0 + 1 := by
  set A := G ++ ((v0, w0) :: R) with hA
  set L := A ++ (v0 + d0, w0) :: S with hL
  have hq : L.getD A.length (0, 0) = ((v0 + d0 : ℕ), (w0 : ℕ)) := by
    have h := getD_append_right' A ((v0 + d0, w0) :: S) 0
    rw [Nat.add_zero] at h
    rw [hL]
    exact h
  have hzg : L.getD (A.length + 1) (0, 0) = z := by
    have h := getD_append_right' A ((v0 + d0, w0) :: S) 1
    rw [hS] at h
    rw [hL, hS]
    exact h
  have hLlen : L.length = A.length + (S.length + 1) := by
    rw [hL, List.length_append]
    simp
  have hSlen : S.length = Z.length + 1 := by rw [hS]; simp
  have hlen : A.length + 1 < L.length := by omega
  obtain ⟨k, hkl, hk1, hkmin, hk2⟩ :=
    r1ok_ST_PS hN (A.length + 1) hlen (by rw [hzg]; omega)
  have hkp : k = A.length := by
    by_contra hne
    have hklt : k < A.length := by omega
    have := hkmin A.length hklt (by omega)
    rw [hq, hzg] at this
    simp only [] at this
    omega
  subst hkp
  rw [hq, hzg] at hk1 hk2
  exact ⟨by simpa using hk1.symm, by simpa using hk2⟩

/-! ## Part 6b — `ST_PS` column discipline (assets for the `N`-side induction)

The remaining residual `AscArgDom` cannot come from a local invariant of `N`
(see the header), so the next attack has to be an induction along the **`ST_PS`
derivation of `N`**.  Its base case is `N = diagSeq 0 v`, and the two lemmas
below are exactly what that base case needs. -/

/-- **Row 1 never exceeds row 0** on a standard form.  Climb the `r1ok` chain:
each step down lowers row 0 by exactly one and row 1 by at most one, and at
row 0 `= 0` the column is `(0,0)` (`z0ok`). -/
theorem snd_le_fst_ST_PS {M : PairSeq} (hM : ST_PS M) :
    ∀ j, j < M.length → (M.getD j (0, 0)).2 ≤ (M.getD j (0, 0)).1 := by
  have hr := r1ok_ST_PS hM
  have hz := z0ok_ST_PS hM
  suffices H : ∀ (d j : ℕ), j < M.length → (M.getD j (0, 0)).1 ≤ d →
      (M.getD j (0, 0)).2 ≤ (M.getD j (0, 0)).1 from
    fun j hj => H _ j hj le_rfl
  intro d
  induction d with
  | zero =>
    intro j hj h0
    have h1 : (M.getD j (0, 0)).1 = 0 := by omega
    have := hz j hj h1
    omega
  | succ d ih =>
    intro j hj hle
    by_cases h0 : (M.getD j (0, 0)).1 = 0
    · have := hz j hj h0; omega
    · obtain ⟨k, hkj, hk1, -, hk2⟩ := hr j hj (by omega)
      have hklen : k < M.length := by omega
      have := ih k hklen (by omega)
      omega

/-- **A standard form never rises above the diagonal.**  If `M` has matched the
base diagonal on `[0, i)`, then its `i`-th column is `pairlt`-below or equal to
`(i,i)`: `steps1` caps row 0 by `i`, and `snd_le_fst_ST_PS` caps row 1 by row 0.

Consequence (the base case of an induction along the `ST_PS` derivation of the
*small* side): `seqlex (diagSeq 0 v) M` forces `diagSeq 0 v` to be a **prefix**
of `M` — the comparison can never be decided by a strictly larger column. -/
theorem le_diag_ST_PS {M : PairSeq} (hM : ST_PS M) {i : ℕ} (hi : i < M.length)
    (hpre : ∀ j, j < i → M.getD j (0, 0) = (j, j)) :
    ¬ pairlt ((i, i) : ℕ × ℕ) (M.getD i (0, 0)) := by
  have h2 : (M.getD i (0, 0)).2 ≤ (M.getD i (0, 0)).1 := snd_le_fst_ST_PS hM i hi
  have h1 : (M.getD i (0, 0)).1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · have hhd : M.headD (0, 0) = (0, 0) := stps_head hM
      have h0 : M.getD 0 (0, 0) = M.headD (0, 0) := by
        rcases M with _ | ⟨x, xs⟩ <;> rfl
      rw [h0, hhd]
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hst : steps1 M := (blockok_ST_PS hM).2.2
      have hup := steps1_iff.1 hst i' hi
      rw [hpre i' (by omega)] at hup
      simpa using hup
  unfold pairlt
  omega


/-! ## Part 7 — assembly (modulo the ascending crux) -/

/-- **The head step of the ascending crux is CLOSED**: only the `q = (v0+d0,w0)`
case survives. -/
theorem asc_head_step (H : AscCrux1) : AscCrux := by
  intro G R S v0 w0 d0 lp q hM hN hRgt hd hlp2 hlp1 hnr hq
  have hlpe : lp = (v0 + d0, w0 + 1) := Prod.ext hlp1 hlp2
  by_cases hqe : q = (v0 + d0, w0)
  · subst hqe
    exact H (hlpe ▸ hM) hN hRgt hd (hlpe ▸ hnr)
  · refine ⟨1, le_rfl, Or.inr ?_⟩
    rw [copies_one, shiftr0_cons]
    refine Or.inl ?_
    rw [hlpe] at hq
    have : q.1 < v0 + d0 ∨ (q.1 = v0 + d0 ∧ q.2 < w0 + 1) := hq
    have hne : ¬ (q.1 = v0 + d0 ∧ q.2 = w0) := by
      intro ⟨h1, h2⟩; exact hqe (Prod.ext h1 h2)
    unfold pairlt
    simp only []
    omega

/-- **Branch `bad`**: modulo the *ascending* crux, the genuine branch. -/
theorem seqlex_cof_bad (H : AscCrux) {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0))
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
  have hp := hasParent_last_ST_PS hM (by omega) hz
  obtain ⟨G, v0, w0, R, d0, lp, hMeq, hMn, R_gt, lp_gt, disj⟩ :=
    oper_bad_blocks_all L (blockok_ST_PS hM).2.2 (r1ok_ST_PS hM) hz hp
  rcases seqlex_snoc_cases (D := G ++ ((v0, w0) :: R)) (lp := lp) (N := N)
      (by rw [← hMeq]; exact h) with hle | ⟨q, S, hNeq, hq⟩
  · exact ⟨1, le_rfl, by rw [hMn 1 le_rfl, copies_one]; exact hle⟩
  · obtain ⟨m, hm, hsle⟩ : ∃ m, 1 ≤ m ∧
        sle (q :: S) (shiftr0 d0 (copies d0 ((v0, w0) :: R) m)) := by
      rcases disj with ⟨rfl, hlp2, hlp1⟩ | ⟨hd, hw, hlpe, hn1⟩
      · simp only [shiftr0_zero]
        exact crux_zero (hNeq ▸ hN) R_gt hlp2 hlp1 hq
      · have hlen : M.length - 1 = (G ++ ((v0, w0) :: R)).length := by
          rw [hMeq]; simp
        have hnr : nextrel1 ((G ++ ((v0, w0) :: R)) ++ [lp]) G.length
            (G ++ ((v0, w0) :: R)).length := by
          rw [← hlen, ← hMeq]; exact hn1
        exact H (hMeq ▸ hM) (hNeq ▸ hN) R_gt hd hw hlpe hnr hq
    refine ⟨m + 1, by omega, ?_⟩
    rw [hMn (m + 1) (by omega), copies_succ_front, hNeq, List.append_assoc]
    exact (sle_append_cancel _).2 ((sle_append_cancel _).2 hsle)

/-- Modulo the crux, the `seqlex` form of cofinality holds. -/
theorem seqlex_cofinality_of_crux (H : AscCrux) : SeqlexCofinality := by
  intro M N hM hN h
  by_cases hL : M.length - 1 = 0
  · exact seqlex_cof_short hL h
  · by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
    · exact seqlex_cof_zero (by omega) hz h
    · exact seqlex_cof_bad H hM hN (by omega) hz h

/-- **PSS Bachmann cofinality** (the load-bearing statement of the ordinal-free route).

Every standard form strictly `olt`-below `M` is bounded by some expansion of `M`:
the fundamental sequence `M⟦·⟧` is cofinal below `M`.

Model-verified TRUE: 0 violations / 79003 pairs at closure `+5/+6/+7`, non-degenerate,
with `n ≥ 1`. -/
theorem pss_cofinality {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) := by
  sorry

/-- **PSS Bachmann cofinality, modulo the single residual `AscCrux1`.**
Everything else in the statement is GREEN:

* the reduction to the column-lex order (`pss_cofinality_of_seqlex`),
* the `self` and `(0,0)`-last branches (`seqlex_cof_short`, `seqlex_cof_zero`),
* the emptiness of the `noparent` branch on `ST_PS` (`hasParent_last_ST_PS`),
* the exact-copy (`d0 = 0`) half of the bad branch (`crux_zero`, via the CNF
  sibling recursion `copy_dom_zero`),
* the head step of the ascending half (`asc_head_step`, via the row-`1` `+1`
  discipline `nextrel1_snd_succ`). -/
theorem pss_cofinality_of_crux (H : AscCrux1) {M N : PairSeq}
    (hM : ST_PS M) (hN : ST_PS N) (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  pss_cofinality_of_seqlex (seqlex_cofinality_of_crux (asc_head_step H)) hM hN h

/-- **PSS Bachmann cofinality from the single `≤o` residual `AscArgDom`.**
This is the sharpest packaging: everything in `pss_cofinality` reduces to

    translate (S.takeWhile fun p => v0 + d0 < p.1)  ≤o  translate R

for the ascending bad branch.  Feed the result to `YAPSS/Wset.lean`'s `hcof`
parameter (`acc_of_nat_branch`, `wf_of_cofinality_and_membership`). -/
theorem pss_cofinality_of_argdom (H : AscArgDom) {M N : PairSeq}
    (hM : ST_PS M) (hN : ST_PS N) (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  pss_cofinality_of_crux (asc_crux1_of_argdom H) hM hN h

end YAPSS
