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

**On the residue itself (NEW vacuity reduction, mirroring ya-pss).**
`alpha_step_residue` is reduced GREEN to the strictly sharper, **α-free** residual
`PsiValueAcanon`: *every ψ-value `psiSelf ζ w` is canonical at every subscript
`v ≤ w`*.  Given it, `alpha_step_residue` is **vacuous** — a member `ξ < α` of
`CsetSelf_α` is canonical at `v` (closure-rank induction `CsetSelf_mem_lt_acanon`)
hence at `u ≥ v` (`acanon_sub_mono`), contradicting the non-canonicity `hnc`.  This
**supersedes** the prior `CanonWitnessResidue` (canonical-witness existence): no
witness construction is needed, and the new residual is α-free and quantifier-
light.  The old wall (least-witness canonicity failing at ψ-fixpoints; `CsetSelf`
non-downward-closure) is bypassed.  Both routes (lean psiSelf, ya-pss Cset_c) now
bottom out at the **same** statement `psi_value_acanon` (necessity.thy).

**On `psi_proj_notmem`.**  ya-pss keeps the §1 core as *two* `sorry`s: the
necessity-side `alpha_step_residue` (necessity.thy:1139) and the collapse-side
`psi_proj_nonmem` (nrm.thy:186), explicitly the "same §1 core" but not reduced to
one another.  We mirror this with two residues: the closure face `PsiValueAcanon`
(⟶ `alpha_step_residue`, the only `sorry`) and the collapse face `CollapseResidue`.
They are genuinely independent in the formalization (see the independence note at
file end); we keep both.

**End-to-end payoff.**  `oV_nrm_eq_of_collapseResidue : CollapseResidue → ∀ t,
oV (nrm t) = oV t` — the termination-relevant §1 consequence — is proven GREEN
through `Nrm.lean`'s parametric chain, resting on the single `CollapseResidue`
hypothesis (no `Nrm.lean` edit, no extra `sorry`; axiom profile WITHOUT `sorryAx`).
`CollapseResidue` is stated in the omitted form `psi`/`Cset` (so the chain
consumes it directly); the self-form `CollapseResidueSelf` (for attack via
`collapseSelf_le`) is equivalent modulo `alpha_step_residue`.
-/
import YAPSS.Buchholz17
import YAPSS.Nrm

set_option maxHeartbeats 1000000

namespace YAPSS

open Three

/-! ## The single residue (the shared Buchholz §1 simultaneous-induction crux)

**Status of the attack (psiSelf route, NEW vacuity reduction).**  Following
ya-pss's breakthrough (necessity.thy `psi_value_acanon` + `Citer_c_mem_lt_acanon`),
`alpha_step_residue` is reduced GREEN to the strictly sharper, **α-free** residual
`PsiValueAcanon`: *every ψ-value `psiSelf ζ w` is canonical at every subscript
`v ≤ w`* (`psiSelf ζ w ∈ CsetSelf (psiResSelf (psiSelf ζ w)) (psiSelf ζ w) v`).

With that single fact, `alpha_step_residue` is **VACUOUS**: a member `ξ < α` of
`CsetSelf_α` is canonical at `v` (`CsetSelf_mem_lt_acanon`, by closure-rank
induction — base/sum/generator all discharged, the ψ-value generator case being
exactly `PsiValueAcanon`), hence canonical at `u ≥ v` (`acanon_sub_mono`),
contradicting the non-canonicity hypothesis `hnc`.  So the non-canonical generator
with argument inside the closure never arises — Buchholz's "can be shown".

This **replaces** the previous `CanonWitnessResidue` (canonical-witness existence)
with `PsiValueAcanon`, which is strictly sharper: α-free, quantifier-light, and
`alpha_step_residue` now needs *no* witness construction at all.  Empirically TRUE
(ya-pss `probe_valcanon_final.py`: 0 violations over all distinct (value, w) with
`v ≤ w`, incl. the Ω₃ model).  The two routes (lean psiSelf, ya-pss Cset_c) now
bottom out at the **same** statement `psi_value_acanon`. -/

/-- **Non-canonical argument collapses at-or-below itself.**  If `ξ` is
non-canonical at `u` (`ξ ∉ CsetSelf (psiResSelf ξ) ξ u`) then `psiSelf ξ u ≤ ξ`.
(Contrapositive of `below_psiSelf_mem_CsetSelf` at bound `ξ`.)  Proven, no IH. -/
theorem psiSelf_le_self_of_not_canon {ξ : Ordinal.{u}} {u : ℕ}
    (hnc : ξ ∉ CsetSelf (psiResSelf ξ) ξ u) : psiSelf ξ u ≤ ξ := by
  by_contra h; push Not at h; exact hnc (below_psiSelf_mem_CsetSelf h)

/-! ### Subscript monotonicity of `CsetSelf` (only the base `Ω_v` grows) -/

/-- `CstepSelf'`-iterate is monotone in the subscript `v` (base `Iio (Om v)` grows
via `Om_mono`; the `+`/generator steps are subscript-independent). -/
theorem CiterSelf_sub_mono {p : Ordinal.{u} → ℕ → Ordinal.{u}} {α : Ordinal.{u}}
    {v u : ℕ} (hvu : v ≤ u) (n : ℕ) :
    (CstepSelf' p α)^[n] (Set.Iio (Om v)) ⊆ (CstepSelf' p α)^[n] (Set.Iio (Om u)) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    intro x hx; exact lt_of_lt_of_le hx (Om_mono hvu)
  | succ n IH =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    intro x hx
    rw [CstepSelf', CstepSelf] at hx ⊢
    rcases hx with (h1 | h2) | h3
    · exact Set.mem_union_left _ (Set.mem_union_left _ (IH h1))
    · obtain ⟨a, ha, b, hb, hab⟩ := h2
      exact Set.mem_union_left _ (Set.mem_union_right _ ⟨a, IH ha, b, IH hb, hab⟩)
    · obtain ⟨w, hw⟩ := Set.mem_iUnion.1 h3
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq] at hw
      obtain ⟨ξ, ⟨hξX, hξc⟩, hξx⟩ := hw
      refine Set.mem_union_right _ (Set.mem_iUnion.2 ⟨w, ?_⟩)
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨ξ, ⟨IH hξX, hξc⟩, hξx⟩

/-- `CsetSelf` is monotone in the subscript `v`. -/
theorem CsetSelf_sub_mono {p : Ordinal.{u} → ℕ → Ordinal.{u}} {α : Ordinal.{u}}
    {v u : ℕ} (hvu : v ≤ u) : CsetSelf p α v ⊆ CsetSelf p α u := by
  rw [CsetSelf_eq, CsetSelf_eq]
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨n, CiterSelf_sub_mono hvu n hn⟩

/-- **Canonicity is monotone in the subscript** (`acanon v δ → v ≤ u → acanon u δ`).
The self-form analogue of ya-pss `acanon_sub_mono`. -/
theorem acanon_sub_mono {δ : Ordinal.{u}} {v u : ℕ}
    (hv : δ ∈ CsetSelf (psiResSelf δ) δ v) (hvu : v ≤ u) :
    δ ∈ CsetSelf (psiResSelf δ) δ u := CsetSelf_sub_mono hvu hv

/-- A ψ-value at a higher subscript sits inside `Ω_v` when `w < v`. -/
theorem psiSelf_low_sub_in_Om {ζ : Ordinal.{u}} {w v : ℕ} (hwv : w < v) :
    psiSelf ζ w < Om v :=
  lt_of_lt_of_le (psiSelf_lt_Om_succ ζ w) (Om_mono hwv)

/-- **The sharpened residual (the psiSelf-route Buchholz §1 core).**  *Every
ψ-value is canonical at every lower-or-equal subscript.*  Lean analogue of ya-pss's
`psi_value_acanon` (necessity.thy).  α-free; strictly sharper than the previous
`CanonWitnessResidue` (no witness construction; `alpha_step_residue` is now
vacuous given it).  Empirically TRUE (0 violations).  The earlier candidate
`acanon u δ → δ < psiSelf δ u` is FALSE (e.g. `δ = ω`, `u = 0`); `PsiValueAcanon`
is the true replacement. -/
def PsiValueAcanon.{u} : Prop :=
  ∀ (ζ : Ordinal.{u}) (w v : ℕ), v ≤ w →
    psiSelf ζ w ∈ CsetSelf (psiResSelf (psiSelf ζ w)) (psiSelf ζ w) v

/-- **Closure-rank induction: every member `ξ < α` of `CsetSelf_α` is canonical
at `v`**, modulo `PsiValueAcanon`.  Lean analogue of ya-pss `Citer_c_mem_lt_acanon`.
By induction on the `CstepSelf'`-rank `N`:
* base (`ξ ∈ Ω_v`): `Iio_Om_subset_CsetSelf`;
* sum `ξ = a + b`: `a, b ≤ ξ < α` so canonical by inner IH, lifted to bound `ξ`
  by `CCSelf_mono` and recombined by `CsetSelf_add_closed`;
* generator `ξ = psiSelf ζ w` (`ζ < α`): if `w < v` it lands in `Ω_v`, else
  `v ≤ w` and `PsiValueAcanon` applies.
The α-IH is not even needed in this vacuity form. -/
theorem CiterSelf_mem_lt_acanon (PVA : PsiValueAcanon.{u})
    (α : Ordinal.{u}) (v : ℕ) :
    ∀ (N : ℕ) (ξ : Ordinal.{u}),
      ξ ∈ (CstepSelf' (psiResSelf α) α)^[N] (Set.Iio (Om v)) →
      ξ < α → ξ ∈ CsetSelf (psiResSelf ξ) ξ v := by
  intro N
  induction N with
  | zero =>
    intro ξ hξ hξα
    simp only [Function.iterate_zero, id_eq] at hξ
    exact Iio_Om_subset_CsetSelf hξ
  | succ N IH =>
    intro ξ hξ hξα
    rw [Function.iterate_succ_apply'] at hξ
    rw [CstepSelf', CstepSelf] at hξ
    rcases hξ with (h1 | h2) | h3
    · exact IH ξ h1 hξα
    · obtain ⟨a, ha, b, hb, hab⟩ := h2
      have hab' : a + b = ξ := hab
      subst hab'
      have haα : a < α := lt_of_le_of_lt le_self_add hξα
      have hbα : b < α := lt_of_le_of_lt le_add_self hξα
      have aC : a ∈ CsetSelf (psiResSelf (a + b)) (a + b) v :=
        CCSelf_mono le_self_add v (IH a ha haα)
      have bC : b ∈ CsetSelf (psiResSelf (a + b)) (a + b) v :=
        CCSelf_mono le_add_self v (IH b hb hbα)
      exact CsetSelf_add_closed aC bC
    · obtain ⟨w, hw⟩ := Set.mem_iUnion.1 h3
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq] at hw
      obtain ⟨ζ, ⟨hζX, ⟨hζα, hζc⟩⟩, hζx⟩ := hw
      rw [psiResSelf, if_pos hζα] at hζx
      subst hζx
      rcases lt_or_ge w v with hwv | hvw
      · exact Iio_Om_subset_CsetSelf (psiSelf_low_sub_in_Om hwv)
      · exact PVA ζ w v hvw

/-- **Every member `ξ < α` of the full closure `CsetSelf_α` is canonical at `v`**
(lift of `CiterSelf_mem_lt_acanon` to the full union).  Modulo `PsiValueAcanon`. -/
theorem CsetSelf_mem_lt_acanon (PVA : PsiValueAcanon.{u})
    {α : Ordinal.{u}} {v : ℕ} {ξ : Ordinal.{u}}
    (hξC : ξ ∈ CsetSelf (psiResSelf α) α v) (hξα : ξ < α) :
    ξ ∈ CsetSelf (psiResSelf ξ) ξ v := by
  obtain ⟨N, hN⟩ := CsetSelf_mem_iff.1 hξC
  exact CiterSelf_mem_lt_acanon PVA α v N ξ hN hξα

/-- **`alpha_step_residue` (the residue; now reduced to `PsiValueAcanon` via
vacuity).**  Lean analogue of ya-pss's `alpha_step_residue` (necessity.thy:1139),
the non-canonical-generator step of the closure-rank induction carrying the α-IH.
The hypotheses are **contradictory** modulo `PsiValueAcanon`: `ξ < α` in
`CsetSelf_α` is canonical at `v` (`CsetSelf_mem_lt_acanon`), hence at `u ≥ v`
(`acanon_sub_mono`), contradicting `hnc : ¬ acanon u ξ`.  So the conclusion holds
vacuously.  The single remaining `sorry` is `PsiValueAcanon`. -/
theorem alpha_step_residue
    (α : Ordinal.{u}) (v : ℕ)
    (IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w)
    (ξ : Ordinal.{u}) (u : ℕ)
    (hξC : ξ ∈ CsetSelf (psiResSelf α) α v) (hξα : ξ < α)
    (hnc : ξ ∉ CsetSelf (psiResSelf ξ) ξ u) (hvu : v ≤ u) :
    psi.{u} ξ u ∈ CsetSelf (psiResSelf α) α v := by
  exact absurd
    (acanon_sub_mono
      (CsetSelf_mem_lt_acanon
        (show PsiValueAcanon.{u} from
          -- The sharpened Buchholz §1 core: every ψ-value is canonical at every
          -- lower-or-equal subscript (ya-pss `psi_value_acanon`).  α-free; still
          -- open on BOTH the psiSelf route (here) and the Cset_c route (ya-pss).
          -- Empirically TRUE (0 violations).  See `PsiValueAcanon` docstring.
          sorry)
        hξC hξα)
      hvu)
    hnc

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
is mechanically reduced to the other (see the independence note at the end of this
file).  We mirror that faithfully: the genuine single new `sorry` is
`alpha_step_residue`; the collapse face is exposed as the clearly-named
**secondary** residue `CollapseResidue`.

**Design choice (this cleanup).**  `CollapseResidue` is stated in the *omitted*
form `psi`/`Cset` — exactly the shape `Nrm.psi_proj_notmem` has and the
`Nrm.lean` chain directly consumes.  This keeps the end-to-end payoff resting on
**exactly one** residue hypothesis with **no** transport drag (the end-to-end
theorem has axiom profile WITHOUT `sorryAx`; `sorryAx` only appears once you also
plug in `alpha_step_residue` via the spine).  The self-form phrasing — useful for
attacking the residue with the green `collapseSelf_le` machinery — is provided as
the equivalent `CollapseResidueSelf` (the equivalence holds modulo
`alpha_step_residue`, via `psi_eq_psiSelf`). -/

/-- **The collapse-side residue (omitted form).**  Lean analogue of ya-pss's
`psi_proj_nonmem` (nrm.thy:186) — the *dual* face of `alpha_step_residue`, kept
(as in ya-pss) as a separate statement.  Stated in the omitted machinery
`psi`/`Cset`, i.e. *literally* `Nrm.psi_proj_notmem`'s statement, so the
`Nrm.lean` chain consumes it with no transport.  Note: this is **NOT** the dead
interval-noncanonicity `H` of `Nrm.psi_proj_notmem_of_intervalNoncanon` (false via
Ω-crossing); it is the bare per-step collapse non-membership, the genuine TRUE
statement. -/
def CollapseResidue.{u} : Prop :=
  ∀ (a : ℕ) (b' g : Three), wf3 b' → g ∈ Gterm a b' → ¬ olt g b' →
    psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a

/-- **The collapse-side residue (self form).**  The `CollapseResidue` content
phrased in the green self machinery (`psiSelf`/`CsetSelf`), which is where the
self-collapse tool `collapseSelf_le` lives.  Provided so the residue can be
attacked self-side; equivalent to `CollapseResidue` modulo `alpha_step_residue`
(`collapseResidue_iff_self`). -/
def CollapseResidueSelf.{u} : Prop :=
  ∀ (a : ℕ) (b' g : Three), wf3 b' → g ∈ Gterm a b' → ¬ olt g b' →
    psiSelf.{u} (oV b') a ∉ CsetSelf (psiResSelf (oV g)) (oV g) a

/-- The omitted/self collapse non-membership are **equivalent** pointwise, by the
closure identity `psi_eq_psiSelf` / `Cset_eq_CsetSelf` (GREEN modulo
`alpha_step_residue`).  The `≤` is not needed — it is a pure rewrite. -/
theorem psi_proj_notmem_iff_self {a : ℕ} {b' g : Three} :
    psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a ↔
      psiSelf.{u} (oV b') a ∉ CsetSelf (psiResSelf.{u} (oV g)) (oV g) a := by
  have h1 : psi.{u} (oV b') a = psiSelf (oV b') a := psi_eq_psiSelf _ _
  have h2 : Cset (psiRes (oV g)) (oV g) a = CsetSelf (psiResSelf (oV g)) (oV g) a :=
    Cset_eq_CsetSelf _ _
  have hmem : (psi.{u} (oV b') a ∈ Cset (psiRes (oV g)) (oV g) a)
            = (psiSelf (oV b') a ∈ CsetSelf (psiResSelf (oV g)) (oV g) a) := by
    rw [h1, h2]
  exact not_congr (iff_of_eq hmem)

/-- `CollapseResidue ↔ CollapseResidueSelf` (GREEN modulo `alpha_step_residue`).
Lets the residue be attacked in the self machinery and consumed in the omitted
one interchangeably. -/
theorem collapseResidue_iff_self : CollapseResidue.{u} ↔ CollapseResidueSelf.{u} := by
  constructor
  · exact fun CR a b' g wb' hg hv => psi_proj_notmem_iff_self.1 (CR a b' g wb' hg hv)
  · exact fun CR a b' g wb' hg hv => psi_proj_notmem_iff_self.2 (CR a b' g wb' hg hv)

/-- **`Nrm.lean`'s `psi_proj_notmem` from the collapse residue.**  Since
`CollapseResidue` is the omitted form, this is *definitionally* the residue
applied — no transport, no `alpha_step_residue`.  (The self-form variant
`CollapseResidueSelf` is consumed via `collapseResidue_iff_self`, which does drag
in `alpha_step_residue`.) -/
theorem psi_proj_notmem_of_collapseResidue
    (CR : CollapseResidue.{u})
    (a : ℕ) (b' g : Three) (wb' : wf3 b')
    (hg : g ∈ Gterm a b') (hv : ¬ olt g b') :
    psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a :=
  CR a b' g wb' hg hv

/-! ## END-TO-END: the `nrm` value-preservation payoff, modulo `CollapseResidue`

The termination-relevant consequence that `Nrm.lean` ultimately wants from the §1
collapse core is **`oV (nrm t) = oV t`** (`nrm` preserves the ordinal value), which
is what makes the `Rnf`/`wf` argument go through.  `Nrm.lean` already exposes this
as a *parameterized* chain:

* `psi_proj_of_notmem`  : the per-step collapse `psi_proj_notmem` ⟹ `psi_proj`
  (`proj` preserves `ψ_a`);
* `oV_nrm_of_psi_proj`  : `psi_proj` ⟹ `oV (nrm t) = oV t`.

Composing the §1-route reduction `psi_proj_notmem_of_collapseResidue` through both
gives the single green end-to-end statement below.  No `Nrm.lean` edit is needed
(the chain is parametric), and no dangling extra `sorry` is introduced: the whole
chain rests on the **single** hypothesis `CollapseResidue` and nothing else.
Because `CollapseResidue` is the omitted form, this end-to-end theorem's axiom
profile is `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`** (it would
appear only after one *also* plugs in `alpha_step_residue` via the spine to
discharge `CollapseResidue`). -/

/-- **`proj` preserves `ψ_a`, modulo `CollapseResidue`.**  The §1-route discharge
of `Nrm.psi_proj` (which in `Nrm.lean` rests on the open `psi_proj_notmem`). -/
theorem psi_proj_of_collapseResidue (CR : CollapseResidue.{u})
    (a : ℕ) (b : Three) (wb : wf3 b) :
    psi.{u} (oV (proj a b)) a = psi (oV b) a :=
  psi_proj_of_notmem a (fun b' g => psi_proj_notmem_of_collapseResidue CR a b' g) b wb

/-- **END-TO-END: `nrm` preserves the ordinal value, modulo `CollapseResidue`.**
`oV (nrm t) = oV t` for every term `t`, the termination-relevant §1 payoff, proven
through the parametric `Nrm.lean` chain:
`CollapseResidue` ⟹ `psi_proj_notmem` ⟹ `psi_proj` ⟹ `oV ∘ nrm = oV`.
This is the clean single theorem a reader inspects to see "the §1 termination
consequence holds modulo exactly the collapse residue".  Axiom profile:
`[propext, Classical.choice, Quot.sound]` — NO `sorryAx`; the proof depends on
nothing open beyond the explicit `CollapseResidue` hypothesis. -/
theorem oV_nrm_eq_of_collapseResidue (CR : CollapseResidue.{u}) :
    ∀ t : Three, oV.{u} (nrm t) = oV t :=
  oV_nrm_of_psi_proj (fun a b wb => psi_proj_of_collapseResidue CR a b wb)

/-! ## Are `CollapseResidue` and `PsiValueAcanon` independent? — they are.

**Finding: the two residues are genuinely independent in the formalization; we
keep both (matching ya-pss), with a precise reason.**

`PsiValueAcanon` is a *canonicity* statement: every ψ-value `psiSelf ζ w` is
canonical at every `v ≤ w`.  Via the closure-rank induction (`CsetSelf_mem_lt_acanon`)
it makes `alpha_step_residue` vacuous and yields `Cset = CsetSelf`, hence
`psi = psiSelf` (`psi_eq_psiSelf`) — the **necessity / closure** content.

`CollapseResidue` is a *value-equality (collapse)* statement: by
`psi_notMem_iff_eq` (with `oV b' ≤ oV g`) it is exactly
`psi (oV b') a = psi (oV g) a` for the OT3-violator pair — the **collapse**
content (the gap `[oV b', oV g)` carries no new ψ-value).  (Equivalently in self
form `CollapseResidueSelf`, `collapseResidue_iff_self`.)

These do not reduce to one another:

* `CollapseResidue ⇏` from the closure structure.  Even granting `Cset = CsetSelf`
  (i.e. `PsiValueAcanon`), the membership
  `psi (oV b') a ∈ Cset (psiRes (oV g)) (oV g) a` only yields `oV b' < oV g` via
  `psi_arg_lt_of_mem` — which is *consistent* with `oV b' ≤ oV g`, NOT a
  contradiction.  So the closure/canonicity content cannot force the collapse
  equality; that equality is an extra fact about the specific gap.
* This mirrors ya-pss exactly: its `psi_proj_nonmem` (nrm.thy:186, the collapse
  face) "needs `ξ = oV(proj a b) ≥ oV m`, whose value-identity is `psi_proj`
  itself — the irreducible circularity"; ya-pss keeps it as a *separate* `sorry`
  from `alpha_step_residue` (necessity.thy:1139, the closure face), explicitly the
  "same §1 core" but not mechanically inter-reducible.

So Lean reproduces the ya-pss two-residue picture independently:
  - closure face: `PsiValueAcanon` (⟶ `alpha_step_residue`, the psiSelf spine);
  - collapse face: `CollapseResidue`.
Both bottom out at Buchholz's single simultaneous transfinite induction (which
proves closure + collapse *together*), but no sound first-order reduction collapses
one to the other without re-running that induction.  Hence we keep both, and the
end-to-end payoff `oV_nrm_eq_of_collapseResidue` rests on `CollapseResidue` (the
collapse face is the one `Nrm.lean`'s chain actually consumes). -/

end YAPSS
