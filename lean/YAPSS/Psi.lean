/-
**Buchholz `ψ_v` collapsing functions on the Mathlib ordinals** (route A).
Lean port of `ord/psi.thy`.

Faithful transcription of Buchholz 1986 §1.  The PSS notation `Three` uses
only *finite* subscripts, so we index the collapsing functions by `ℕ`
(`v ∈ ℕ`); `ψ_ω` occurs only as the cofinal limit, never inside a term.
`Ω_v = ℵ_v` (`v > 0`), `Ω_0 = 1`.

Port conventions (Isabelle ZFC_in_HOL → Lean Mathlib):
  * the type `V` of sets, restricted to ordinals → `Ordinal.{0}`
  * `x ∈ elts α` (for ordinals)               → `x < α`
  * V-sets of ordinals                         → `Set Ordinal` + `Small.{u}`
  * `transrec`                                 → `WellFounded.fix lt_wf`
  * `LEAST`                                    → `sInf`
  * `vcard`/`gcard` arithmetic                 → `Cardinal.{1}` with `lift`
    (a `Set Ordinal.{0}` lives in `Type 1`)
-/
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Principal

namespace YAPSS

open Cardinal Ordinal Set

universe u

/-! ## The cardinals `Ω_v` -/

/-- `Ω_v`: `1` for `v = 0`, else `ℵ_v` (as an ordinal). -/
noncomputable def Om (v : ℕ) : Ordinal.{u} := if v = 0 then 1 else (ℵ_ v).ord

@[simp] theorem Om_zero : Om 0 = 1 := by simp [Om]

theorem Om_of_pos {v : ℕ} (hv : 0 < v) : Om v = (ℵ_ v).ord := by
  simp [Om, Nat.pos_iff_ne_zero.1 hv]

/-! ## The sets `C_v(α)` and the collapsing functions `ψ_v(α)` (Buchholz §1)

`C_v(α)` = least set `⊇ Ω_v` closed under `+` and under `ξ ↦ ψ_u ξ` for
`ξ < α`, `u ∈ ℕ` (Buchholz's condition `ξ ∈ C_u(ξ)` omitted per his Remark).
Built as the countable union of the finite closure iterates of `Cstep` from
`Iio (Om v)`. -/

def Cstep (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (X : Set Ordinal.{u}) : Set Ordinal.{u} :=
  X ∪ Set.image2 (· + ·) X X ∪ ⋃ u : ℕ, (fun ξ => p ξ u) '' (X ∩ Set.Iio α)

def Citer (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) (n : ℕ) : Set Ordinal.{u} :=
  (Cstep p α)^[n] (Set.Iio (Om v))

def Cset (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) : Set Ordinal.{u} :=
  ⋃ n : ℕ, Citer p α v n

/-! ### Smallness -/

/-! ### `ψ` is well defined -/

noncomputable def psi : Ordinal.{u} → ℕ → Ordinal.{u} :=
  Ordinal.lt_wf.fix (C := fun _ => ℕ → Ordinal.{u}) fun α IH v =>
    sInf {γ | γ ∉ Cset (fun ξ u => if h : ξ < α then IH ξ h u else 0) α v}

/-- `ψ_v(α)` with the conventional argument order. -/
noncomputable def Psi (v : ℕ) (α : Ordinal) : Ordinal := psi α v

/-! ## Closure properties of `C_v(α)` (Buchholz §1, conditions C1–C3) -/

/-! ## Basic properties of `ψ_v` (Buchholz Lemma 1.2) -/

/-! ## Monotonicity of `C_v(α)` and `ψ_v(α)` in `α` (Buchholz Lemma 1.2(d)) -/

/-! ## `ψ_v(α)` is additive principal (Buchholz Lemma 1.2(b)) -/

/-! ## The cardinality bound (Buchholz Lemma 1.2(c)): `ψ_v(α) < Ω_{v+1}`

`|C_v(α)| ≤ Ω_v ⊔ ω < Ω_{v+1}`, since `C_v(α)` is the closure of `Iio (Om v)`
under `+` and the countably many maps `ψ_u`.  All cardinality arithmetic is
done in `Cardinal.{1}` (a `Set Ordinal.{0}` lives in `Type 1`). -/

/-! ## Additive-principal abstraction -/

/-- An ordinal `δ` is additive principal when it is positive and a sum of two
ordinals below it stays below it. -/
def addprinc (δ : Ordinal) : Prop :=
  0 < δ ∧ ∀ β γ, β < δ → γ < δ → β + γ < δ

/-! ## With-condition collapsing functions `ψ^w_v` (Buchholz's *faithful* §1)

Buchholz 1986 defines `C_v(α)` with the generator side-condition `ξ ∈ C_u(ξ)`
(canonicity).  The omitted-condition port above drops it (his Remark p197).  The
with-condition version makes Buchholz 1.4(b) (the canonical-witness lemma, the
genuine core of the necessity direction) hold *by definition* — the generator
carries canonicity, so any extracted witness is canonical.

We add `ψ^w` (`psiW`) **additively**, in parallel with `psi`, so the existing
omitted development stays green.  `CstepW` = `Cstep` with the generator clause
intersected by the canonicity test `{ξ | ξ ∈ Cset p ξ u}`.  Since `ψ^w` fires a
*subset* of the omitted generators, `CsetW ⊆ Cset`, which gives smallness (hence
well-definedness) for free. -/

/-! ### §1 port for `ψ^w` (with-condition).  Buchholz 1.2–1.4(a). -/

/-! ### `ψ^w` additive-principality and arg-extraction (necessity payoff) -/

/-! ## Self-referential with-condition C-set `C^s_v(α)` (Buchholz's faithful form)

The `ψ^w`/`CsetW` above test canonicity with the *omitted* set (`ξ ∈ Cset p ξ u`),
which leaves an omitted=with residue surfacing in 1.3/1.4(a).  Buchholz's actual
condition is `ξ ∈ C_u(ξ)` referring to the SAME `C` under definition.  Modelled
here as `ξ ∈ CsetSelf p ξ u`: the canonicity test consults `CsetSelf` at the
strictly smaller bound `ξ < α`, so `CsetSelf` is definable by well-founded
recursion on the bound.  Crucially the test is **bound-independent**, which makes
the bound/parameter monotonicities (`CsetSelf_mono_bound`/`_param`/`CCSelf_mono`)
free — dissolving the residue (1.3/1.4(a) need no extra membership hypothesis). -/

/-! ### bound/parameter monotonicity (the residue-dissolving lemmas) -/

/-! ### well-definedness of `ψ^s` -/

/-! ### §1 port for `ψ^s` (Buchholz 1.2–1.4), residue-free -/

/-! ### `ψ^s` additive-principality + UNCONDITIONAL arg-extraction (necessity) -/

end YAPSS
