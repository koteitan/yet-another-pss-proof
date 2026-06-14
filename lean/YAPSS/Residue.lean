/-
**Buchholz §1 collapse reduction to a single residue.**

This file isolates the one remaining Buchholz §1 simultaneous-induction crux —
the Lean analogue of ya-pss's `alpha_step_residue` (necessity.thy:1139) — and
proves, GREEN modulo that single `sorry`, the whole reduction chain down to
`psi_proj_notmem` (the collapse obligation consumed by `Nrm.lean`).

**Route chosen: the `psiSelf`/`CsetSelf` self-referential route** (per the
project methodology constraint).  Lean's `CsetSelf` is the *canonical-only*
closure: its generator-closure lemma `CsetSelf_psi_closed` fires `p ξ u` only
under the self-canonicity test `ξ ∈ CsetSelf p ξ u`.  This is exactly ya-pss's
`Cset_c`/`acanon` discipline, but expressed Lean-natively and with the
omitted=with circle already eliminated *unconditionally at the ordinal level*
(no `acanon` predicate threaded by hand).  Thus the residue is phrased in the
`CsetSelf` world rather than by porting `Cset_c`+`acanon`.

The spine `Cset ⊆ CsetSelf` (Lean analogue of ya-pss's
`Citer_subset_Cset_c_alpha`) is a simultaneous transfinite induction:
* outer: strong induction on the bound `α` (Buchholz's α-induction), whose IH is
  the *full closure identity* `psi β = psiSelf β` for every `β < α`;
* inner: induction on the closure rank `n`.
The generator step splits exactly as ya-pss's `Cset_c_anygen_closed`:
  - `u < v`              → the value lands in `Ω_v` (free, `Iio_Om_subset_CsetSelf`);
  - canonical (`acanon`) → `CsetSelf_psi_closed` + the α-IH `psi ξ u = psiSelf ξ u`
                           (the param conversion mirrors necessity.thy:1360);
  - non-canonical, `v ≤ u` → **the single residue `alpha_step_residue`**.

From `Cset = CsetSelf` we get `psi = psiSelf` (sInf of equal complements), which
transports the proven self-collapse machinery to the omitted form.

**On `psi_proj_notmem`.**  ya-pss keeps the §1 core as *two* `sorry`s: the
necessity-side `alpha_step_residue` (necessity.thy:1139) and the collapse-side
`psi_proj_nonmem` (nrm.thy:186), explicitly the "same §1 core" but not reduced to
one another.  We mirror this: the single *new* `sorry` of this file is
`alpha_step_residue`; the collapse face is exposed as the named secondary
`CollapseResidue` (stated in the green self machinery, NOT the dead
interval-noncanonicity route), and `Nrm.psi_proj_notmem` is reduced to
`alpha_step_residue ∧ CollapseResidue`.
-/
import YAPSS.Buchholz17
import YAPSS.Nrm

set_option maxHeartbeats 1000000

namespace YAPSS

open Three

/-! ## The single residue (the shared Buchholz §1 simultaneous-induction crux) -/

/-- **`alpha_step_residue` (the SINGLE `sorry`).**  Lean analogue of ya-pss's
`alpha_step_residue` (necessity.thy:1139): the non-canonical-generator step of the
closure-rank induction, carrying the **α-induction hypothesis** `IHa` as an
explicit local assumption.

`IHa`: for every smaller bound `β < α`, the full omitted closure already equals
the canonical (self) closure (`psi β w = psiSelf β w`) — Buchholz's carried
invariant of the §1 simultaneous transfinite induction.

Given that IH and a generator `ψ_u ξ` whose argument `ξ ∈ CsetSelf_α` lies below
`α`, is **non-canonical** (`ξ ∉ CsetSelf (psiResSelf ξ) ξ u`) with `v ≤ u`, the
value `ψ_u ξ` is reproduced inside `CsetSelf_α`.  This is the genuine Buchholz §1
core (the cross-subscript canonical collapse of the non-canonical argument `ξ`
using the IH at `ξ < α`); it is attacked separately and is the only `sorry`. -/
theorem alpha_step_residue
    (α : Ordinal.{u}) (v : ℕ)
    (IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w)
    (ξ : Ordinal.{u}) (u : ℕ)
    (hξC : ξ ∈ CsetSelf (psiResSelf α) α v) (hξα : ξ < α)
    (hnc : ξ ∉ CsetSelf (psiResSelf ξ) ξ u) (hvu : v ≤ u) :
    psi.{u} ξ u ∈ CsetSelf (psiResSelf α) α v := by
  sorry

/-! ## The generator step (all three sub-cases), modulo the residue

Lean analogue of ya-pss's `Cset_c_anygen_closed`: every generator with argument
in `CsetSelf_α ∩ Iio α` is reproduced in `CsetSelf_α`.  Canonical and `u < v`
sub-cases are discharged here; the non-canonical `v ≤ u` sub-case is the residue. -/
theorem gen_step_CsetSelf
    (α : Ordinal.{u}) (v : ℕ)
    (IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w)
    (ξ : Ordinal.{u}) (u : ℕ)
    (hξC : ξ ∈ CsetSelf (psiResSelf α) α v) (hξα : ξ < α) :
    psi.{u} ξ u ∈ CsetSelf (psiResSelf α) α v := by
  by_cases hcanon : ξ ∈ CsetSelf (psiResSelf ξ) ξ u
  · -- canonical: CsetSelf_psi_closed + the α-IH (psi ξ u = psiSelf ξ u)
    have hconv : ξ ∈ CsetSelf (psiResSelf α) ξ u := by
      rwa [CsetSelf_param_eq (p := psiResSelf ξ) (q := psiResSelf α)
            (fun ζ uu hζ => by
              rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hξα)])] at hcanon
    have h := CsetSelf_psi_closed hξC hξα u hconv
    rw [psiResSelf, if_pos hξα] at h
    rwa [IHa ξ hξα u]
  · -- non-canonical: either u < v (value in Ω_v) or v ≤ u (the residue)
    rcases lt_or_ge u v with huv | hvu
    · apply Iio_Om_subset_CsetSelf
      exact lt_of_lt_of_le (psi_lt_Om_succ ξ u) (Om_mono huv)
    · exact alpha_step_residue α v IHa ξ u hξC hξα hcanon hvu

/-! ## The closure-rank spine, modulo the residue

Lean analogue of ya-pss's `Citer_subset_Cset_c_alpha`: every `Citer`-stage of the
omitted closure sits inside `CsetSelf_α`.  Inner induction on the rank `n`; the
`Om`/`+`/generator cases use `Iio_Om_subset_CsetSelf`, `CsetSelf_add_closed`,
`gen_step_CsetSelf`. -/
theorem Citer_subset_CsetSelf
    (α : Ordinal.{u}) (v : ℕ)
    (IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w) :
    ∀ n, Citer (psiRes α) α v n ⊆ CsetSelf (psiResSelf α) α v := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [Citer, Function.iterate_zero, id_eq] at hx
    exact Iio_Om_subset_CsetSelf hx
  | succ n IH =>
    intro x hx
    rw [Citer_succ, Cstep] at hx
    rcases hx with (h1 | h2) | h3
    · exact IH h1
    · obtain ⟨y, hy, z, hz, hyz⟩ := h2
      rw [← hyz]; exact CsetSelf_add_closed (IH hy) (IH hz)
    · obtain ⟨u, ⟨ξ, ⟨hξC, hξα⟩, hξx⟩⟩ := Set.mem_iUnion.1 h3
      have hξα : ξ < α := hξα
      simp only [psiRes, if_pos hξα] at hξx
      rw [← hξx]
      exact gen_step_CsetSelf α v IHa ξ u (IH hξC) hξα

/-- The spine at the `Cset` level: `Cset_α ⊆ CsetSelf_α`, modulo the residue. -/
theorem Cset_subset_CsetSelf
    (α : Ordinal.{u}) (v : ℕ)
    (IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w) :
    Cset (psiRes α) α v ⊆ CsetSelf (psiResSelf α) α v := by
  intro x hx
  obtain ⟨n, hn⟩ := Cset_mem_iff.1 hx
  exact Citer_subset_CsetSelf α v IHa n hn

/-! ## The full-closure identity `psi = psiSelf` (the simultaneous induction)

The outer α-induction: `Cset_α = CsetSelf_α` (antisymmetry with the proven
`CsetSelf_subset_Cset`), hence `psi α w = psiSelf α w` (`sInf` of equal
complements).  The strong-induction IH supplies the `IHa` hypothesis of the
spine for every `β < α`.  GREEN modulo `alpha_step_residue`. -/
/-- Below the bound, `psiResSelf α` and `psiRes α` agree as parameters *given the
α-IH* `psi β = psiSelf β` (β < α): `psiResSelf α ξ u = psiSelf ξ u = psi ξ u =
psiRes α ξ u` for `ξ < α`. -/
private theorem psiResSelf_eq_psiRes_below
    {α : Ordinal.{u}} (IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w)
    {ξ : Ordinal.{u}} {u : ℕ} (hξ : ξ < α) : psiResSelf α ξ u = psiRes α ξ u := by
  rw [psiResSelf, psiRes, if_pos hξ, if_pos hξ, IHa ξ hξ u]

theorem psi_eq_psiSelf (α : Ordinal.{u}) : ∀ w : ℕ, psi.{u} α w = psiSelf α w := by
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro w
    have IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w := fun β hβ w => IH β hβ w
    -- ⊆ : the spine (uses IHa via the canonical generator step)
    have hsub : Cset (psiRes α) α w ⊆ CsetSelf (psiResSelf α) α w :=
      Cset_subset_CsetSelf α w IHa
    -- ⊇ : CsetSelf ⊆ Cset (psiResSelf α), then param-swap to Cset (psiRes α)
    have hswap : Cset (psiResSelf α) α w ⊆ Cset (psiRes α) α w :=
      Cset_mono_param le_rfl (fun ξ u hξ => psiResSelf_eq_psiRes_below IHa hξ)
    have hsup : CsetSelf (psiResSelf α) α w ⊆ Cset (psiRes α) α w :=
      (CsetSelf_subset_Cset (psiResSelf α) α w).trans hswap
    have heq : Cset (psiRes α) α w = CsetSelf (psiResSelf α) α w :=
      Set.Subset.antisymm hsub hsup
    rw [psi_unfold, psiSelf_unfold, heq]

/-- The closure identity in set form: `Cset_α = CsetSelf_α`. -/
theorem Cset_eq_CsetSelf (α : Ordinal.{u}) (v : ℕ) :
    Cset (psiRes α) α v = CsetSelf (psiResSelf α) α v := by
  have IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w := fun β _ w => psi_eq_psiSelf β w
  have hswap : Cset (psiResSelf α) α v ⊆ Cset (psiRes α) α v :=
    Cset_mono_param le_rfl (fun ξ u hξ => psiResSelf_eq_psiRes_below IHa hξ)
  exact Set.Subset.antisymm
    (Cset_subset_CsetSelf α v IHa)
    ((CsetSelf_subset_Cset (psiResSelf α) α v).trans hswap)

/-! ## The omitted-form canonicity test equals the self test

A consequence of `Cset_eq_CsetSelf`: `δ ∈ Cset (psiRes δ) δ a ↔ δ ∈ CsetSelf
(psiResSelf δ) δ a`.  This identifies Lean's omitted-form "canonical" predicate
with ya-pss's `acanon` (self-form), making the self-collapse machinery directly
usable on the omitted form. -/
theorem canon_iff_self {δ : Ordinal.{u}} {a : ℕ} :
    δ ∈ Cset (psiRes δ) δ a ↔ δ ∈ CsetSelf (psiResSelf δ) δ a := by
  rw [Cset_eq_CsetSelf]

/-! ## Down to `psi_proj_notmem` (the `Nrm.lean` collapse obligation)

`psi_proj_notmem`: `ψ_a(oV b') ∉ C_a(oV g)` for an OT3-violator `g ∈ G_a(b')`
(`¬ olt g b'`, hence `oV b' ≤ oV g`).

**Scope of the reduction.**  The spine above reduces the **necessity / closure**
content (`Cset = CsetSelf`, the Lean analogue of ya-pss's
`Citer_subset_Cset_c_alpha`) to the single `alpha_step_residue`.  The
`psi_proj_notmem` obligation is the **collapse** content — its dual face.  ya-pss
keeps these as *two distinct* `sorry`s (`alpha_step_residue` in `necessity.thy`
vs. `psi_proj_nonmem` in `nrm.thy:186`), explicitly noting they are "the same §1
core" that only Buchholz's simultaneous transfinite induction breaks, but neither
is mechanically reduced to the other.  We mirror that faithfully: the genuine
single new `sorry` is `alpha_step_residue`; the collapse face is exposed below as
a clearly-named **secondary** statement, transported to the self form so it rests
on the *self-collapse* machinery (`collapseSelf_le`) that `Cset = CsetSelf` now
unlocks for the omitted form.

What the spine *does* buy here: by `psi_eq_psiSelf` / `Cset_eq_CsetSelf`, the
omitted-form collapse obligation is **equivalent** to its self-form version, and
self-non-canonicity is identified with omitted-form non-canonicity
(`canon_iff_self`).  So the remaining collapse residue can be stated and consumed
entirely in the green self machinery. -/

/-- The omitted-form `psi_proj_notmem` is **equivalent** to its self-form
counterpart, by the closure identity `psi_eq_psiSelf`.  GREEN modulo
`alpha_step_residue` (through `psi_eq_psiSelf`). -/
theorem psi_proj_notmem_iff_self {a : ℕ} {b' g : Three} (hle : oV.{u} b' ≤ oV g) :
    psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a ↔
      psiSelf.{u} (oV b') a ∉ CsetSelf (psiResSelf.{u} (oV g)) (oV g) a := by
  have h1 : psi.{u} (oV b') a = psiSelf (oV b') a := psi_eq_psiSelf _ _
  have h2 : Cset (psiRes (oV g)) (oV g) a = CsetSelf (psiResSelf (oV g)) (oV g) a :=
    Cset_eq_CsetSelf _ _
  have hmem : (psi.{u} (oV b') a ∈ Cset (psiRes (oV g)) (oV g) a)
            = (psiSelf (oV b') a ∈ CsetSelf (psiResSelf (oV g)) (oV g) a) := by
    rw [h1, h2]
  exact not_congr (iff_of_eq hmem)

/-- **The collapse-side residue (self form).**  Lean analogue of ya-pss's
`psi_proj_nonmem` (nrm.thy:186) — the *dual* face of `alpha_step_residue`, kept
(as in ya-pss) as a separate statement.  Stated in the green self machinery
(`psiSelf`/`CsetSelf`).  Note: this is **NOT** the dead interval-noncanonicity
`H` of `Nrm.psi_proj_notmem_of_intervalNoncanon` (which is false via Ω-crossing);
it is the bare per-step collapse non-membership, the genuine TRUE statement. -/
def CollapseResidue.{u} : Prop :=
  ∀ (a : ℕ) (b' g : Three), wf3 b' → g ∈ Gterm a b' → ¬ olt g b' →
    psiSelf.{u} (oV b') a ∉ CsetSelf (psiResSelf (oV g)) (oV g) a

/-- **`Nrm.lean`'s `psi_proj_notmem` from the collapse residue.**  Discharges the
omitted-form obligation by transporting it to the self form
(`psi_proj_notmem_iff_self`, green modulo `alpha_step_residue`) and applying the
collapse residue.  Thus `Nrm.psi_proj_notmem` reduces to
`alpha_step_residue ∧ CollapseResidue` — the two faces of the single Buchholz §1
core, exactly as in ya-pss. -/
theorem psi_proj_notmem_of_collapseResidue
    (CR : CollapseResidue.{u})
    (a : ℕ) (b' g : Three) (wb' : wf3 b')
    (hg : g ∈ Gterm a b') (hv : ¬ olt g b') :
    psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a := by
  have wg : wf3 g := wf3_Gterm wb' hg
  have hle : oV.{u} b' ≤ oV g := by
    rcases olt_total b' g with h | rfl | h
    · exact (oV_order_pres wb' wg h).le
    · exact le_rfl
    · exact absurd h hv
  exact (psi_proj_notmem_iff_self hle).2 (CR a b' g wb' hg hv)

end YAPSS
