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

**⚠⚠⚠ On the residue (CORRECTED — the vacuity route was UNSOUND).**
A prior session reduced `alpha_step_residue` to `PsiValueAcanon` ("every ψ-value
with a canonical argument is canonical at `v ≤ w`") via a **vacuity** argument
(`CsetSelf_mem_lt_acanon`: every member `ξ < α` is `v`-canonical, contradicting the
non-canonicity `hnc`).  **That residual `PsiValueAcanon` is FALSE**
(`PsiValueAcanon_is_false`): `ζ = Ω_1` is `0`-canonical, but its value
`c = psiSelf Ω_1 0` is NOT `0`-canonical (`C_0(c) ⊆ C_0(Ω_1)` and `c ∉ C_0(Ω_1)`).
So `CsetSelf_mem_lt_acanon` is false (`ξ = psiSelf Ω_1 0` is a non-canonical
member) and the non-canonical generator step is **NOT vacuous**.

`alpha_step_residue` is **re-sounded** to rest on the GENUINE residual
`AlphaStepResidue`: the non-canonical generator value `psiSelf ξ u` has a
**canonical representative** `δ < α` in `C_v(α)` (`δ` `u`-canonical,
`psiSelf δ u = psiSelf ξ u`); fire it via `CsetSelf_psi_closed`.  This is the real
Buchholz §1 content (necessity.thy:1139), TRUE (canonical-rep existence).

**Dead ends found and recorded** (all sorryAx-free disproofs):
* `AcanonLtValue` (canonical `δ ⟹ δ < psiSelf δ w`) — FALSE (`Ω_{w+1}`);
* `PsiValueAcanon` (value canonical) — FALSE (`psiSelf Ω_1 0`);
* `CanonRep` (witness `δ < c`) — FALSE when `psiSelf ζ w ≤ ζ` (no witness `< c`).
The GENUINE residual `AlphaStepResidue` puts the witness `δ < α` (NOT `δ < c`):
`δ` can be `≥ c` (the canonical rep of the value, sitting below the spine bound α).

PROVEN around the residual:
* the explicit value formula `psiSelf δ w = ω^(Ω_w+δ)` for `δ < ε(w)`
  (`psiSelf_eq_opow_add` / `psiSelf_zero_eq_opow`);
* `AcanonLtValue` below `ε(w)` (`AcanonLtValue_lt_epsLvl`) and the sub-`ε` diagonal
  (`psiValueAcanon_diag_lt_epsLvl`) — these remain TRUE on the sub-`ε` range;
* the non-collapse lever `psi_strict_mono_lt_epsLvl` (sub-`ε` injectivity).

The explicit formula also gives the **non-collapse lever** `psi_strict_mono_lt_
epsLvl` (sub-`ε` `ψ_a` injective), which discharges the §1 head of `oV_nf_arg_lt`
(`oV_nf_arg_lt_of_lever`) — the DUAL termination leaf.

**On `psi_proj_notmem`.**  ya-pss keeps the §1 core as *two* `sorry`s: the
necessity-side `alpha_step_residue` (necessity.thy:1139) and the collapse-side
`psi_proj_nonmem` (nrm.thy:186), explicitly the "same §1 core" but not reduced to
one another.  We mirror this with two residues: the closure face `AlphaStepResidue`
(⟶ `alpha_step_residue`, the only closure-side `sorry`) and the collapse face
`CollapseResidue`.  They are genuinely independent in the formalization (see the
independence note at file end); we keep both.

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

/-- **`PsiValueAcanon` — ⚠⚠ FALSE (`PsiValueAcanon_is_false`).**  "Every ψ-value
with a `w`-canonical argument is canonical at every `v ≤ w`."  A prior session used
this as the `alpha_step_residue` vacuity residual; it is **DISPROVEN**: `ζ = Ω_1`
is `0`-canonical but `c = psiSelf Ω_1 0` is NOT `0`-canonical (`C_0(c) ⊆ C_0(Ω_1)`,
`c ∉ C_0(Ω_1)`).  Kept ONLY so its disproof and the dead vacuity machinery
(`CiterSelf_mem_lt_acanon`, `CsetSelf_mem_lt_acanon`) are on record.  The genuine
residual is `AlphaStepResidue` (canonical-representative existence, witness `δ < α`
NOT `δ < c`).  Do NOT use `PsiValueAcanon`. -/
def PsiValueAcanon.{u} : Prop :=
  ∀ (ζ : Ordinal.{u}) (w v : ℕ), v ≤ w → ζ ∈ CsetSelf (psiResSelf ζ) ζ w →
    psiSelf ζ w ∈ CsetSelf (psiResSelf (psiSelf ζ w)) (psiSelf ζ w) v

/-- **Closure-rank induction: every member `ξ < α` of `CsetSelf_α` is canonical
at `v`**, modulo `PsiValueAcanon`.  Lean analogue of ya-pss `Citer_c_mem_lt_acanon`.
By induction on the `CstepSelf'`-rank `N`:
* base (`ξ ∈ Ω_v`): `Iio_Om_subset_CsetSelf`;
* sum `ξ = a + b`: `a, b ≤ ξ < α` so canonical by inner IH, lifted to bound `ξ`
  by `CCSelf_mono` and recombined by `CsetSelf_add_closed`;
* generator `ξ = psiSelf ζ w` (`ζ < α`, `ζ` `w`-canonical): if `w < v` it lands in
  `Ω_v`, else `v ≤ w` and `PsiValueAcanon` applies (the generator's built-in
  canonicity supplies `hζc`).
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
      · -- the generator's built-in canonicity `hζc` gives `ζ` `w`-canonical
        have hζcanon : ζ ∈ CsetSelf (psiResSelf ζ) ζ w := by
          rwa [CsetSelf_param_eq (p := psiResSelf α) (q := psiResSelf ζ)
                (fun η uu hη => by
                  rw [psiResSelf, psiResSelf, if_pos hη, if_pos (lt_trans hη hζα)])] at hζc
        exact PVA ζ w v hvw hζcanon

/-- **Every member `ξ < α` of the full closure `CsetSelf_α` is canonical at `v`**
(lift of `CiterSelf_mem_lt_acanon` to the full union).  Modulo `PsiValueAcanon`. -/
theorem CsetSelf_mem_lt_acanon (PVA : PsiValueAcanon.{u})
    {α : Ordinal.{u}} {v : ℕ} {ξ : Ordinal.{u}}
    (hξC : ξ ∈ CsetSelf (psiResSelf α) α v) (hξα : ξ < α) :
    ξ ∈ CsetSelf (psiResSelf ξ) ξ v := by
  obtain ⟨N, hN⟩ := CsetSelf_mem_iff.1 hξC
  exact CiterSelf_mem_lt_acanon PVA α v N ξ hN hξα

/-! ### Sharper sub-reduction of `PsiValueAcanon` to `(a) ∧ (c)`

`PsiValueAcanon` (`psiSelf ζ w ∈ CsetSelf (psiResSelf (psiSelf ζ w)) (psiSelf ζ w) v`)
is reduced here to TWO sub-residuals on the **least-argument witness**
`lwit c w := sInf {d | psiSelf d w = c}` of the value `c = psiSelf ζ w`:

* **(a)** `lwit c w < c` — the least witness is strictly below the value;
* **(c)** `lwit c w ∈ CsetSelf (psiResSelf c) c v` — it lies in `c`'s `v`-closure.

The third obligation **(b)** *the least witness is canonical at `w`* is **DERIVED
from (a)** (`psiSelf_le_self_of_not_canon`: a non-canonical witness would have
`psiSelf (lwit) w ≤ lwit`, i.e. `c ≤ lwit`, contradicting (a)).  Then the
generator step `CsetSelf_psi_closed` fires `psiSelf (lwit) w = c` into `C_v(c)`.

**Why these are the genuine residual** (empirically verified, 0 violations on the
ya-pss model — `/tmp/probe_lw.py`, `/tmp/probe_c.py`):

* **(a)** "the least witness is below its value".  Now CLEANLY reduced (see the
  next section) to two TRUE canonical-rep facts `AcanonLtValue` + `CanonWitness`
  via `a_of_AcanonLtValue`.  (`lwit` is the plateau bottom — `lwit_least_lt`.)
* **(c)** is a `C_v`-membership of the *simpler* ordinal `lwit < c` — recursive,
  the same induction.  The `below_psiSelf` shortcut does NOT prove (c): for
  `v < w`, `psiSelf c v < c`, so `lwit < c` does not give `lwit < psiSelf c v`. -/

/-- The least argument realizing the value `c` at subscript `w`. -/
noncomputable def lwit (c : Ordinal.{u}) (w : ℕ) : Ordinal.{u} :=
  sInf {d : Ordinal | psiSelf d w = c}

/-- For a ψ-value `c = psiSelf ζ w`, the least witness realizes it. -/
theorem lwit_val (ζ : Ordinal.{u}) (w : ℕ) :
    psiSelf (lwit (psiSelf ζ w) w) w = psiSelf ζ w :=
  csInf_mem (s := {d : Ordinal | psiSelf d w = psiSelf ζ w}) ⟨ζ, rfl⟩

/-- **Below the least witness the value is strictly smaller.**  For any
`d < lwit c w` (with `c = psiSelf ζ w`), `psiSelf d w < c`.  (By minimality of
`lwit` the value can't equal `c`, and by monotonicity it can't exceed it.)  Proven,
no residual — confirms `lwit` is the plateau BOTTOM. -/
theorem lwit_least_lt (ζ : Ordinal.{u}) (w : ℕ) {d : Ordinal.{u}}
    (hd : d < lwit (psiSelf ζ w) w) : psiSelf d w < psiSelf ζ w := by
  set c := psiSelf ζ w with hc
  have hne : psiSelf d w ≠ c := fun he =>
    absurd hd (not_lt.2 (csInf_le' (s := {x : Ordinal | psiSelf x w = c}) he))
  have hmono : psiSelf d w ≤ psiSelf (lwit c w) w := psiSelf_mono_arg hd.le w
  rw [lwit_val ζ w] at hmono
  exact lt_of_le_of_ne hmono hne

/-! ### Sub-residual (a) cleanly reduced to two TRUE canonical-rep facts

**Correction (this session).**  A prior note claimed `acanon δ w ⟹ δ < psiSelf δ w`
is FALSE (alleged ε-number counterexample `δ = ω`, `w = 0`).  That is **WRONG**: in
the ya-pss ordinal model `psi(ω,0)` is simply outside the finite value table
(`None`), so the "counterexample" was never realized.  Empirically (0 violations
over all canonical `δ` with `psi` defined, all `w`) the statement is **TRUE**.  It
is the natural converse of `below_psiSelf_mem_CsetSelf`, and the right canonical-rep
lemma.  We name it `AcanonLtValue`.

Sub-residual **(a)** `lwit c w < c` then reduces (GREEN, `a_of_AcanonLtValue`) to
the conjunction of two clean canonical-rep facts:
* `AcanonLtValue` — every `w`-canonical `δ` is strictly below its own value
  `psiSelf δ w`;
* `CanonWitness` — every ψ-value `psiSelf ζ w` has a `w`-canonical witness.
Both are α-free, TRUE empirically (0 violations *where the finite model's value
table is defined* — see WARNING), and are the genuine residual:  each, by rank
induction, hits the *bound-tied* generator step where the element is itself a
ψ-value — Buchholz's simultaneous transfinite induction.  (Investigated: the rank
induction on `AcanonLtValue` stalls at the sum/generator sub-case because the inner
IH would need the summand/arg in its OWN closure, not the ambient one.)

**`AcanonLtValue` has a deeper root: the explicit-value formula** (see
`PsiSelfOpowForm` / `AcanonLtValue_of_form` below).  `psiSelf δ w = ω^(Ω_w + δ)`
for `w`-canonical `δ` reduces it to the arithmetic `δ < ω^(Ω_w+δ)`; the ε-number
"fixpoint" obstruction (`Ω_w+δ = δ`) is exactly the NON-canonical case, hence
vacuous.  The omitted-form formula `Buchholz17.psi_eq_opow_add` is already proven;
porting it to `psiSelf` (CsetSelf-only, no `psi_eq_psiSelf` bridge) is the deepest
clean sub-residual.

**WARNING (finite-model caveat).**  The ya-pss finite model returns `None` for
`psi(δ,w)` outside its value table (e.g. `psi(ω^(ω·2),0)`), making the *model's*
closure spuriously non-downward-closed there; so "0 violations" only covers δ with
the model value defined.  In the genuine ordinals `AcanonLtValue` holds (the
fixpoint exclusion above), but do NOT read the model as a proof for large δ. -/

/-- **`AcanonLtValue`.**  Every `w`-canonical ordinal is strictly below its own
value: `δ ∈ CsetSelf (psiResSelf δ) δ w → δ < psiSelf δ w`.

**⚠⚠ FALSE — DISPROVEN (`AcanonLtValue_is_false`).**  Counterexample
`δ = Ω_{w+1} = psiSelf 0 (w+1)`: it is `w`-canonical (it fires in `C_w(Ω_{w+1})`
as the generator `psiSelf 0 (w+1)`, since `0 < Ω_{w+1}` is canonical), yet
`psiSelf δ w < Ω_{w+1} = δ` (`psiSelf · w < Ω_{w+1}` always).  Root cause: EVERY
`δ < Ω_w` is `w`-canonical (it sits in the base `Iio(Ω_w)` of `C_w(δ)`) — and more
generally generators `psiSelf η u'` with `u' > w` produce `w`-canonical values
`≥ Ω_{w+1} > psiSelf δ w`.  So the "canonical ⟹ below own value" intuition fails
for `δ ≥ ε(w)` (it is TRUE only for `δ < ε(w)`, `AcanonLtValue_lt_epsLvl`).

CONSEQUENCE: the `AcanonLtValue`-based reductions below (`psiValueAcanon_of_
AcanonLtValue`, `psiValueAcanon_diag_of_AcanonLtValue`, `a_of_AcanonLtValue`,
`alpha_step_residue_of_AcanonLtValue`) are valid *implications* but rest on a FALSE
hypothesis, so they CANNOT discharge `PsiValueAcanon`.  The genuine residual is the
canonical-WITNESS existence (`δ < c` canonical with `psiSelf δ w = c`), NOT `ζ`
itself.  Kept only as documented dead-ends. -/
def AcanonLtValue.{u} : Prop :=
  ∀ {δ : Ordinal.{u}} {w : ℕ}, δ ∈ CsetSelf (psiResSelf δ) δ w → δ < psiSelf δ w

/-- **Canonical-rep fact 2 (`CanonWitness`).**  Every ψ-value has a canonical
witness: `∀ ζ w, ∃ δ, psiSelf δ w = psiSelf ζ w ∧ δ ∈ CsetSelf (psiResSelf δ) δ w`.
(`lwit` is the natural candidate, but its canonicity is itself this residual.) -/
def CanonWitness.{u} : Prop :=
  ∀ (ζ : Ordinal.{u}) (w : ℕ), ∃ δ,
    psiSelf δ w = psiSelf ζ w ∧ δ ∈ CsetSelf (psiResSelf δ) δ w

/-- **The deeper root of `AcanonLtValue`: the psiSelf explicit-value formula.**
`PsiSelfOpowForm` is the *parametric* form; the formula itself is now **PROVEN**
in-range as `psiSelf_eq_opow_add` (`psiSelf α v = ω^(Ω_v+α)` for `v ≥ 1`,
`α < ε_{Ω_v+1}`), a full port of `Buchholz17.psi_eq_opow_add` using only `CsetSelf`
closure lemmas (no `psi_eq_psiSelf` bridge).  It DISCHARGES `AcanonLtValue` on that
range — see `AcanonLtValue_lt_eps` (PROVEN, sorryAx-free).

**Why `AcanonLtValue` is TRUE (and the ε-fixpoint is consistent).**  With the
formula, `δ < psiSelf δ w = ω^(Ω_w+δ)` whenever `δ < Ω_w + δ` (no left-absorption)
— which holds exactly in the range `δ < ε_{Ω_w+1}` where the formula is valid.  An
ε-number `δ = ω^δ ≥ Ω_w` with `Ω_w + δ = δ` would give `psiSelf δ w = δ` (a
ψ-FIXPOINT) — but then `δ = psiSelf δ w ∉ CsetSelf (psiResSelf δ) δ w`, i.e. `δ` is
NON-canonical, so it is excluded from `AcanonLtValue`'s hypothesis.  Thus the
fixpoint case is vacuous, and `AcanonLtValue` is the genuine canonical-rep theorem,
rooted in the explicit-value formula. -/
def PsiSelfOpowForm.{u} : Prop :=
  ∀ (δ : Ordinal.{u}) (w : ℕ),
    δ ∈ CsetSelf (psiResSelf δ) δ w →
      psiSelf δ w = (Ordinal.omega0) ^ (Om w + δ) ∧ δ < Om w + δ

/-- `AcanonLtValue` from the explicit-value formula `PsiSelfOpowForm` (GREEN). -/
theorem AcanonLtValue_of_form (hF : PsiSelfOpowForm.{u}) : AcanonLtValue.{u} := by
  intro δ w hc
  obtain ⟨hform, hlt⟩ := hF δ w hc
  rw [hform]
  exact lt_of_lt_of_le hlt (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)

/-! ### PROVEN: the psiSelf explicit-value formula `psiSelf δ w = ω^(Ω_w + δ)`

The omitted-form `Buchholz17.psi_eq_opow_add` is here ported to `psiSelf`,
**fully GREEN** (no `sorry`, no `psi_eq_psiSelf` bridge — pure `CsetSelf` closure
lemmas), for the range `δ < ε_{Ω_w+1}` and subscript `w ≥ 1`.  This DISCHARGES
`AcanonLtValue` on that range (`AcanonLtValue_lt_eps`).  The full `AcanonLtValue`
remains open only at: (i) subscript `w = 0`, and (ii) arguments `δ ≥ ε_{Ω_w+1}`
(which, by the formula's range, are exactly the ε-number region — but there the
canonical ones still satisfy the inequality; closing them needs the `w=0` companion
`psi_zero_eq_opow` ported, and an ε-region argument).  This is concrete, committed
progress past the previous flat conjecture. -/

open Ordinal in
/-- `x * n` stays in the self-closure (nat-multiple closure). -/
theorem CsetSelf_mul_nat {α : Ordinal.{u}} {v : ℕ} {x : Ordinal.{u}}
    (hx : x ∈ CsetSelf (psiResSelf α) α v) (n : ℕ) :
    x * (n : Ordinal) ∈ CsetSelf (psiResSelf α) α v := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, mul_zero]
    exact Iio_Om_subset_CsetSelf (lt_of_lt_of_le zero_lt_one (one_le_Om v))
  | succ n IH => rw [Nat.cast_succ, mul_add, mul_one]; exact CsetSelf_add_closed IH hx

open Ordinal in
/-- `Iio (ω^{β+1}) ⊆ C^s_v(δ)` from `ω^β ∈ C^s` and `Iio(ω^β) ⊆ C^s`
(self-form port of `Iio_opow_succ_subset`). -/
theorem Iio_opow_succ_subset_Self {v : ℕ} {δ : Ordinal.{u}} (β : Ordinal.{u})
    (hω : omega0 ^ β ∈ CsetSelf (psiResSelf δ) δ v)
    (hbelow : ∀ s, s < omega0 ^ β → s ∈ CsetSelf (psiResSelf δ) δ v) :
    ∀ γ, γ < omega0 ^ (β + 1) → γ ∈ CsetSelf (psiResSelf δ) δ v := by
  intro γ hγ
  rw [show (β + 1) = Order.succ β from (Order.succ_eq_add_one β).symm] at hγ
  obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 hγ
  clear hγ
  induction n generalizing γ with
  | zero => simp at hn
  | succ n IH =>
    rw [Nat.cast_succ, mul_add, mul_one] at hn
    rcases lt_or_ge γ (omega0 ^ β * (n : Ordinal)) with hlt | hge
    · exact IH γ hlt
    · obtain ⟨s, rfl⟩ := exists_add_of_le hge
      exact CsetSelf_add_closed (CsetSelf_mul_nat hω n) (hbelow s ((add_lt_add_iff_left _).1 hn))

/-- **M1 for `psiSelf`** (self-form port of `psi_form_of_mem`): a principal
band-element of `C^s_v(α)` is a generator `psiSelf ξ v` with `ξ < α` in the
closure.  Uses `CsetSelf_witness_canonical` + the band-forces-subscript argument. -/
theorem psiSelf_form_of_mem {α δ : Ordinal.{u}} {v : ℕ}
    (hap : Ordinal.IsPrincipal (· + ·) δ) (hlo : Om v ≤ δ) (hhi : δ < Om (v + 1))
    (hmem : δ ∈ CsetSelf (psiResSelf α) α v) :
    ∃ ξ, ξ ∈ CsetSelf (psiResSelf α) α v ∧ ξ < α ∧ psiSelf ξ v = δ := by
  obtain ⟨u', ξ, heq, hξα, hξmem, hξc⟩ := CsetSelf_witness_canonical hap hlo hmem
  rw [psiResSelf, if_pos hξα] at heq
  have hu : u' = v := by
    have h1 : Om u' ≤ δ := heq ▸ Om_le_psiSelf ξ u'
    have h2 : δ < Om (u' + 1) := heq ▸ psiSelf_lt_Om_succ ξ u'
    have hle1 : u' ≤ v := by
      by_contra hcc; exact absurd (lt_of_le_of_lt h1 hhi) (not_lt.2 (Om_mono (by omega)))
    have hle2 : v ≤ u' := by
      by_contra hcc; exact absurd (lt_of_le_of_lt hlo h2) (not_lt.2 (Om_mono (by omega)))
    omega
  subst hu; exact ⟨ξ, hξmem, hξα, heq.symm⟩

open Ordinal in
/-- **PROVEN: the psiSelf explicit-value formula** (Buchholz 1.7, self-form).  For
`v ≥ 1` and `α < ε_{Ω_v+1}`: `α` is `v`-canonical and `psiSelf α v = ω^(Ω_v + α)`.
Full port of `Buchholz17.psi_eq_opow_add`; no `sorry`, no circular bridge. -/
theorem psiSelf_eq_opow_add (v : ℕ) (hv : 0 < v) :
    ∀ α : Ordinal.{u}, α < ε_ (Om v + 1) →
      α ∈ CsetSelf (psiResSelf α) α v ∧ psiSelf α v = omega0 ^ (Om v + α) := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro hα
    have hαΩ : α < Om (v + 1) := hα.trans epsilon_Om_succ_lt_Om
    have hΩα : Om v + α < Om (v + 1) := (Om_isPrincipal (v + 1)) (Om_lt_succ v) hαΩ
    have hbandhi : omega0 ^ (Om v + α) < Om (v + 1) := opow_lt_Om_succ hΩα
    have hbandlo : Om v ≤ omega0 ^ (Om v + α) := by
      calc Om v = omega0 ^ Om v := (omega_opow_Om hv).symm
        _ ≤ omega0 ^ (Om v + α) := opow_le_opow_right omega0_pos le_self_add
    have hsub : ∀ γ, γ < omega0 ^ (Om v + α) → γ ∈ CsetSelf (psiResSelf α) α v := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨δ, hδ⟩ | hlim
      · intro γ hγ
        rw [add_zero, omega_opow_Om hv] at hγ
        exact Iio_Om_subset_CsetSelf hγ
      · obtain ⟨δ, rfl⟩ : ∃ δ', α = δ' + 1 := ⟨δ, by rw [← hδ, Order.succ_eq_add_one]⟩
        have hδe : δ < ε_ (Om v + 1) := (lt_add_one δ).trans hα
        obtain ⟨hδc, hδf⟩ := IH δ (lt_add_one δ) hδe
        have hδc1 : δ ∈ CsetSelf (psiResSelf (δ+1)) (δ+1) v := CCSelf_mono (lt_add_one δ).le v hδc
        have hδcanon : δ ∈ CsetSelf (psiResSelf (δ+1)) δ v := by
          rwa [CsetSelf_param_eq (p := psiResSelf δ) (q := psiResSelf (δ+1))
                (fun ζ uu hζ => by
                  rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ (lt_add_one δ))])] at hδc
        have hω : omega0 ^ (Om v + δ) ∈ CsetSelf (psiResSelf (δ + 1)) (δ + 1) v := by
          have := CsetSelf_psi_closed hδc1 (lt_add_one δ) v hδcanon
          rwa [psiResSelf, if_pos (lt_add_one δ), hδf] at this
        have hbelow : ∀ s, s < omega0 ^ (Om v + δ) → s ∈ CsetSelf (psiResSelf (δ + 1)) (δ + 1) v := by
          intro s hs; rw [← hδf] at hs; exact CCSelf_mono (lt_add_one δ).le v (below_psiSelf_mem_CsetSelf hs)
        have heq : Om v + (δ + 1) = (Om v + δ) + 1 := by rw [add_assoc]
        rw [heq]; exact Iio_opow_succ_subset_Self (Om v + δ) hω hbelow
      · intro γ hγ
        have hlimΩ : Order.IsSuccLimit (Om v + α) := Ordinal.isSuccLimit_add _ hlim
        rw [lt_opow_of_isSuccLimit (by simp) hlimΩ] at hγ
        obtain ⟨β, hβ, hγβ⟩ := hγ
        rcases lt_or_ge β (Om v) with hβlo | hβhi
        · have : γ < Om v := by
            calc γ < omega0 ^ β := hγβ
              _ < omega0 ^ Om v := (opow_lt_opow_iff_right one_lt_omega0).2 hβlo
              _ = Om v := omega_opow_Om hv
          exact Iio_Om_subset_CsetSelf this
        · obtain ⟨α', rfl⟩ := exists_add_of_le hβhi
          have hα'α : α' < α := (add_lt_add_iff_left (Om v)).1 hβ
          obtain ⟨hα'c, hα'f⟩ := IH α' hα'α (hα'α.trans hα)
          rw [← hα'f] at hγβ
          exact CCSelf_mono hα'α.le v (below_psiSelf_mem_CsetSelf hγβ)
    have hle : psiSelf α v ≤ omega0 ^ (Om v + α) := by
      rw [psiSelf_unfold]; apply csInf_le'; intro hmem
      obtain ⟨ξ, hξC, hξα, hξeq⟩ := psiSelf_form_of_mem (isPrincipal_add_omega0_opow _) hbandlo hbandhi hmem
      rw [(IH ξ hξα (hξα.trans hα)).2] at hξeq
      exact absurd hξeq (ne_of_lt ((opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left (Om v)).2 hξα)))
    have hge : omega0 ^ (Om v + α) ≤ psiSelf α v := by
      by_contra hlt; push Not at hlt; exact psiSelf_notMem α v (hsub _ hlt)
    have hform : psiSelf α v = omega0 ^ (Om v + α) := le_antisymm hle hge
    exact ⟨below_psiSelf_mem_CsetSelf (by rw [hform]; exact lt_opow_Om_add hv hα), hform⟩

open Ordinal in
/-- **`AcanonLtValue` discharged on the range `v ≥ 1`, `δ < ε_{Ω_v+1}`** (PROVEN
via the formula): there `δ < Ω_v + δ ≤ ω^(Ω_v+δ) = psiSelf δ v`.  The `Ω_v + δ`
strict bound holds because `Ω_v + δ < ε_{Ω_v+1}` is not an ε-fixpoint of `δ ↦ ω^δ`
beneath `δ` — concretely `δ < Ω_v + δ` since `δ < ε_{Ω_v+1}` and `Ω_v ≥ 1` give no
left-absorption below the first ε-number. -/
theorem AcanonLtValue_lt_eps {δ : Ordinal.{u}} {v : ℕ} (hv : 0 < v)
    (hδe : δ < ε_ (Om v + 1)) :
    δ < psiSelf δ v := by
  obtain ⟨_, hform⟩ := psiSelf_eq_opow_add v hv δ hδe
  rw [hform]
  exact lt_opow_Om_add hv hδe

open Ordinal in
/-- **PROVEN: psiSelf explicit value at subscript 0** (`psi_zero_eq_opow` port).
For `α < ε₀`: `α` is `0`-canonical and `psiSelf α 0 = ω^α`. -/
theorem psiSelf_zero_eq_opow : ∀ α : Ordinal.{u}, α < ε_ 0 →
    α ∈ CsetSelf (psiResSelf α) α 0 ∧ psiSelf α 0 = omega0 ^ α := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro hα
    have hsub : ∀ γ, γ < omega0 ^ α → γ ∈ CsetSelf (psiResSelf α) α 0 := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨δ, hδ⟩ | hlim
      · intro γ hγ
        rw [opow_zero] at hγ
        exact Iio_Om_subset_CsetSelf (lt_of_lt_of_le hγ (one_le_Om 0))
      · obtain ⟨δ, rfl⟩ : ∃ δ', α = δ' + 1 := ⟨δ, by rw [← hδ, Order.succ_eq_add_one]⟩
        obtain ⟨hδc, hδf⟩ := IH δ (lt_add_one δ) ((lt_add_one δ).trans hα)
        have hδc1 : δ ∈ CsetSelf (psiResSelf (δ+1)) (δ+1) 0 := CCSelf_mono (lt_add_one δ).le 0 hδc
        have hδcanon : δ ∈ CsetSelf (psiResSelf (δ+1)) δ 0 := by
          rwa [CsetSelf_param_eq (p := psiResSelf δ) (q := psiResSelf (δ+1))
                (fun ζ uu hζ => by rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ (lt_add_one δ))])] at hδc
        have hω : omega0 ^ δ ∈ CsetSelf (psiResSelf (δ + 1)) (δ + 1) 0 := by
          have := CsetSelf_psi_closed hδc1 (lt_add_one δ) 0 hδcanon
          rwa [psiResSelf, if_pos (lt_add_one δ), hδf] at this
        have hbelow : ∀ s, s < omega0 ^ δ → s ∈ CsetSelf (psiResSelf (δ + 1)) (δ + 1) 0 := by
          intro s hs; rw [← hδf] at hs; exact CCSelf_mono (lt_add_one δ).le 0 (below_psiSelf_mem_CsetSelf hs)
        exact Iio_opow_succ_subset_Self δ hω hbelow
      · intro γ hγ
        rw [lt_opow_of_isSuccLimit (by simp) hlim] at hγ
        obtain ⟨β, hβα, hγβ⟩ := hγ
        obtain ⟨hβc, hβf⟩ := IH β hβα (hβα.trans hα)
        rw [← hβf] at hγβ
        exact CCSelf_mono hβα.le 0 (below_psiSelf_mem_CsetSelf hγβ)
    have hle : psiSelf α 0 ≤ omega0 ^ α := by
      rw [psiSelf_unfold]; apply csInf_le'; intro hmem
      obtain ⟨ξ, hξC, hξα, hξeq⟩ := psiSelf_form_of_mem (isPrincipal_add_omega0_opow α)
        (by rw [Om_zero, ← opow_zero omega0]; exact opow_le_opow_right omega0_pos bot_le)
        (opow_lt_Om_one_of_lt_epsilon0 hα) hmem
      rw [(IH ξ hξα (hξα.trans hα)).2] at hξeq
      exact absurd hξeq (ne_of_lt ((opow_lt_opow_iff_right one_lt_omega0).2 hξα))
    have hge : omega0 ^ α ≤ psiSelf α 0 := by
      by_contra hlt; push Not at hlt; exact psiSelf_notMem α 0 (hsub _ hlt)
    have hform : psiSelf α 0 = omega0 ^ α := le_antisymm hle hge
    exact ⟨below_psiSelf_mem_CsetSelf (hform ▸ lt_opow_self_of_lt_epsilon0 hα), hform⟩

open Ordinal in
/-- **PROVEN: `AcanonLtValue` on the unified below-`ε(w)` range, ALL `w`**
(`δ < epsLvl w → δ < psiSelf δ w`).  `w = 0` via `psiSelf_zero_eq_opow` +
`lt_opow_self_of_lt_epsilon0`; `w ≥ 1` via `AcanonLtValue_lt_eps`.  This is the
genuine §1.7 content (below `ε(w)` everything is canonical AND below its value),
now PROVEN for `psiSelf` with NO residual on this range. -/
theorem AcanonLtValue_lt_epsLvl {δ : Ordinal.{u}} {w : ℕ}
    (hδ : δ < epsLvl w) : δ < psiSelf δ w := by
  cases w with
  | zero =>
    have hδ0 : δ < ε_ 0 := by simpa [epsLvl] using hδ
    rw [(psiSelf_zero_eq_opow δ hδ0).2]
    exact lt_opow_self_of_lt_epsilon0 hδ0
  | succ k =>
    have hδe : δ < ε_ (Om (k+1) + 1) := by
      have : epsLvl (k+1) = ε_ (Om (k+1) + 1) := by simp [epsLvl]
      rwa [this] at hδ
    exact AcanonLtValue_lt_eps (Nat.succ_pos k) hδe

/-! ### `AcanonLtValue` is FALSE (the ε-boundary counterexample)

`Ω_{w+1} = psiSelf 0 (w+1)` is `w`-canonical but its value `psiSelf Ω_{w+1} w` is
`< Ω_{w+1}`.  This disproves `AcanonLtValue` and rules out the "witness = ζ itself"
route at and above `ε(w)`. -/

/-- `psiSelf 0 (w+1) = Ω_{w+1}` (the explicit formula at argument 0). -/
theorem psiSelf_zero_eq_Om (w : ℕ) : psiSelf 0 (w+1) = Om (w+1) := by
  have h := (psiSelf_eq_opow_add (w+1) (Nat.succ_pos w) 0
    (Ordinal.epsilon_pos (Om (w+1) + 1))).2
  rw [add_zero, omega_opow_Om (Nat.succ_pos w)] at h
  exact h

/-- `Ω_{w+1}` is `w`-canonical (it fires as the generator `psiSelf 0 (w+1)`). -/
theorem Omsucc_canon_at_w (w : ℕ) :
    Om (w+1) ∈ CsetSelf (psiResSelf (Om (w+1))) (Om (w+1)) w := by
  have hpos : (0:Ordinal) < Om (w+1) := lt_of_lt_of_le one_pos (one_le_Om _)
  have h0w : (0:Ordinal) < Om w := lt_of_lt_of_le one_pos (one_le_Om _)
  have h0canon : (0:Ordinal) ∈ CsetSelf (psiResSelf (Om (w+1))) 0 (w+1) :=
    Iio_Om_subset_CsetSelf (lt_of_lt_of_le one_pos (one_le_Om _))
  have h0mem : (0:Ordinal) ∈ CsetSelf (psiResSelf (Om (w+1))) (Om (w+1)) w :=
    Iio_Om_subset_CsetSelf h0w
  have hfire := CsetSelf_psi_closed h0mem hpos (w+1) h0canon
  rw [psiResSelf, if_pos hpos, psiSelf_zero_eq_Om] at hfire
  exact hfire

/-- **`AcanonLtValue` is FALSE** (Lean-proven).  Witness `δ = Ω_1`, `w = 0`: it is
`0`-canonical (`Omsucc_canon_at_w`) but `psiSelf Ω_1 0 < Ω_1`.  Rules out the
entire "witness = ζ itself / canonical ⟹ below value" route for `PsiValueAcanon`. -/
theorem AcanonLtValue_is_false : ¬ AcanonLtValue.{u} := by
  intro hALV
  have hlt : Om (0+1) < psiSelf (Om (0+1)) 0 := hALV (Omsucc_canon_at_w 0)
  exact absurd (lt_trans hlt (psiSelf_lt_Om_succ (Om (0+1)) 0)) (lt_irrefl _)

/-! ### ⚠⚠⚠ `PsiValueAcanon` ITSELF IS FALSE — the vacuity reduction is UNSOUND

The value `c = psiSelf Ω_1 0` is a `0`-canonical-argument ψ-value (`ζ = Ω_1` is
`0`-canonical, `Omsucc_canon_at_w`) yet `c` is **NOT** `0`-canonical:
`C_0(c) ⊆ C_0(Ω_1)` (`CCSelf_mono`, `c ≤ Ω_1`) and `c = psiSelf Ω_1 0 ∉ C_0(Ω_1)`
(`psiSelf_notMem`).  So `PsiValueAcanon` (even the canonical-`ζ` form) is FALSE.

CONSEQUENCE: the `alpha_step_residue` **vacuity** reduction (`CsetSelf_mem_lt_acanon`
— "every member `ξ < α` of `C_v(α)` is `v`-canonical") is **FALSE** (counterexample
`ξ = psiSelf Ω_1 0`, a non-canonical member), and `alpha_step_residue`'s `sorry`
asserts a FALSE statement.  The non-canonical generator step is NOT vacuous; it
genuinely must reproduce `psi ξ u`.  This invalidates the vacuity route (mine and
ya-pss's `Citer_c_mem_lt_acanon`/`psi_value_acanon` neighbourhood).  See the
re-sound `alpha_step_residue` below, which rests on the genuine canonical-WITNESS
residual instead. -/

/-- The ψ-value `psiSelf Ω_1 0` is NOT `0`-canonical (`C_0(c) ⊆ C_0(Ω_1)` and
`c ∉ C_0(Ω_1)`). -/
theorem psiSelf_Om1_not_canon :
    psiSelf (Om 1) 0 ∉ CsetSelf (psiResSelf (psiSelf (Om 1) 0)) (psiSelf (Om 1) 0) 0 := by
  intro hc
  exact psiSelf_notMem (Om 1) 0
    (CCSelf_mono (le_of_lt (psiSelf_lt_Om_succ (Om 1) 0)) 0 hc)

/-- **`PsiValueAcanon` is FALSE** (Lean-proven).  `ζ = Ω_1` is `0`-canonical
(`Omsucc_canon_at_w`) but its value `psiSelf Ω_1 0` is NOT `0`-canonical
(`psiSelf_Om1_not_canon`).  The vacuity reduction of `alpha_step_residue` is
therefore UNSOUND on this residual. -/
theorem PsiValueAcanon_is_false : ¬ PsiValueAcanon.{u} := fun hPVA =>
  psiSelf_Om1_not_canon (hPVA (Om 1) 0 0 (le_refl 0) (Omsucc_canon_at_w 0))

/-! ### `PsiValueAcanon` via the canonical argument ITSELF (the clean route)

**⚠⚠ DEAD ROUTE (this session's finding).**  This route takes the witness for
`c = psiSelf ζ w` to be **`ζ` itself**, needing `ζ < c` via `AcanonLtValue` — but
`AcanonLtValue` is **FALSE** (`AcanonLtValue_is_false`: `ζ = Ω_1` is `0`-canonical
yet `psiSelf Ω_1 0 < Ω_1`).  So `ζ` is NOT always `< c`, and these reductions
(valid implications) rest on a false hypothesis; they CANNOT discharge
`PsiValueAcanon`.  They are PROVEN only for `ζ < ε(w)` (where
`AcanonLtValue_lt_epsLvl` supplies `ζ < c`) — see `psiValueAcanon_diag_lt_epsLvl`
below for the salvaged sub-`ε` diagonal.  The genuine residual is the
canonical-WITNESS existence: a `δ < c` (NOT `ζ`) that is `w`-canonical with
`psiSelf δ w = c`.  Kept as documented dead-ends. -/

/-- **Diagonal `v = w` of `PsiValueAcanon` from `AcanonLtValue`** (GREEN).  For
`w`-canonical `ζ`, `psiSelf ζ w ∈ C_w(psiSelf ζ w)`: the witness is `ζ` (canonical,
`< c` by `AcanonLtValue`, and `< psiSelf c w` since `c ≤ psiSelf c w` by mono);
`CsetSelf_psi_closed` fires it. -/
theorem psiValueAcanon_diag_of_AcanonLtValue (hALV : AcanonLtValue.{u})
    {ζ : Ordinal.{u}} {w : ℕ} (hζc : ζ ∈ CsetSelf (psiResSelf ζ) ζ w) :
    psiSelf ζ w ∈ CsetSelf (psiResSelf (psiSelf ζ w)) (psiSelf ζ w) w := by
  set c := psiSelf ζ w with hcdef
  have hζlt : ζ < c := hALV hζc
  have hcc : c ≤ psiSelf c w := by
    have := psiSelf_mono_arg hζlt.le w; rwa [hcdef] at this
  have hζmem : ζ ∈ CsetSelf (psiResSelf c) c w :=
    below_psiSelf_mem_CsetSelf (lt_of_lt_of_le hζlt hcc)
  have hζcanon : ζ ∈ CsetSelf (psiResSelf c) ζ w := by
    rwa [CsetSelf_param_eq (p := psiResSelf ζ) (q := psiResSelf c)
          (fun η uu hη => by rw [psiResSelf, psiResSelf, if_pos hη, if_pos (lt_trans hη hζlt)])] at hζc
  have hfire := CsetSelf_psi_closed hζmem hζlt w hζcanon
  rwa [psiResSelf, if_pos hζlt, ← hcdef] at hfire

/-- **PROVEN (sub-`ε`): diagonal `v = w` of `PsiValueAcanon` for `ζ < ε(w)`.**  No
false hypothesis: `ζ < ε(w)` gives `ζ < psiSelf ζ w` outright via the explicit
formula (`AcanonLtValue_lt_epsLvl`), and `ζ` (canonical, `< c`) fires
`psiSelf ζ w = c` into `C_w(c)`.  This is the genuine sub-`ε` part of the §1 core,
fully closed.  (The `ζ ≥ ε(w)` diagonal needs a `δ < c` witness — open.) -/
theorem psiValueAcanon_diag_lt_epsLvl
    {ζ : Ordinal.{u}} {w : ℕ} (hζe : ζ < epsLvl w)
    (hζc : ζ ∈ CsetSelf (psiResSelf ζ) ζ w) :
    psiSelf ζ w ∈ CsetSelf (psiResSelf (psiSelf ζ w)) (psiSelf ζ w) w := by
  set c := psiSelf ζ w with hcdef
  have hζlt : ζ < c := AcanonLtValue_lt_epsLvl hζe
  have hcc : c ≤ psiSelf c w := by
    have := psiSelf_mono_arg hζlt.le w; rwa [hcdef] at this
  have hζmem : ζ ∈ CsetSelf (psiResSelf c) c w :=
    below_psiSelf_mem_CsetSelf (lt_of_lt_of_le hζlt hcc)
  have hζcanon : ζ ∈ CsetSelf (psiResSelf c) ζ w := by
    rwa [CsetSelf_param_eq (p := psiResSelf ζ) (q := psiResSelf c)
          (fun η uu hη => by rw [psiResSelf, psiResSelf, if_pos hη, if_pos (lt_trans hη hζlt)])] at hζc
  have hfire := CsetSelf_psi_closed hζmem hζlt w hζcanon
  rwa [psiResSelf, if_pos hζlt, ← hcdef] at hfire

/-! ### The GENUINE residual: canonical-representation existence `CanonRep`

The correct witness for `c = psiSelf ζ w` is a `δ < c` (NOT `ζ`, which can exceed
`c`) that is `w`-canonical with `psiSelf δ w = c` — Buchholz's canonical
representation.  `CanonRep` states exactly this; it cleanly gives the diagonal
`v = w` of `PsiValueAcanon` (`diag_of_CanonRep`).  For `ζ < ε(w)` the witness is
`ζ` itself (`psiValueAcanon_diag_lt_epsLvl`); for `ζ ≥ ε(w)` (the genuine §1 core)
the existence of `δ < c` is open. -/

/-- **Canonical-representation existence** (`CanonRep`): every value `c = psiSelf ζ w`
(`ζ` `w`-canonical) has a `w`-canonical witness `δ < c` with `psiSelf δ w = c`.
The genuine §1 residual (replaces the FALSE `AcanonLtValue` route). -/
def CanonRep.{u} : Prop :=
  ∀ (ζ : Ordinal.{u}) (w : ℕ), ζ ∈ CsetSelf (psiResSelf ζ) ζ w →
    ∃ δ, δ < psiSelf ζ w ∧ δ ∈ CsetSelf (psiResSelf δ) δ w ∧ psiSelf δ w = psiSelf ζ w

/-- **Diagonal `v = w` of `PsiValueAcanon` from `CanonRep`** (GREEN, sorryAx-free).
The witness `δ < c` (canonical) fires `psiSelf δ w = c` into `C_w(c)`. -/
theorem diag_of_CanonRep (hCR : CanonRep.{u})
    {ζ : Ordinal.{u}} {w : ℕ} (hζc : ζ ∈ CsetSelf (psiResSelf ζ) ζ w) :
    psiSelf ζ w ∈ CsetSelf (psiResSelf (psiSelf ζ w)) (psiSelf ζ w) w := by
  obtain ⟨δ, hδlt, hδc, hδv⟩ := hCR ζ w hζc
  set c := psiSelf ζ w with hcdef
  have hcc : c ≤ psiSelf c w := by
    have : psiSelf δ w ≤ psiSelf c w := psiSelf_mono_arg hδlt.le w
    rwa [hδv] at this
  have hδmem : δ ∈ CsetSelf (psiResSelf c) c w :=
    below_psiSelf_mem_CsetSelf (lt_of_lt_of_le hδlt hcc)
  have hδcanon : δ ∈ CsetSelf (psiResSelf c) δ w := by
    rwa [CsetSelf_param_eq (p := psiResSelf δ) (q := psiResSelf c)
          (fun η uu hη => by rw [psiResSelf, psiResSelf, if_pos hη, if_pos (lt_trans hη hδlt)])] at hδc
  have hfire := CsetSelf_psi_closed hδmem hδlt w hδcanon
  rw [psiResSelf, if_pos hδlt, hδv] at hfire
  exact hfire

/-- **`PsiValueAcanon` from `AcanonLtValue` + the `v < w` membership residual**
(GREEN).  The witness is the canonical `ζ` itself; `AcanonLtValue` gives `ζ < c`,
and the firing needs `ζ ∈ C_v(c)`.  For `v = w` this is free (`below_psiSelf`); the
hypothesis `hmem` supplies the residual `v < w` case. -/
theorem psiValueAcanon_of_AcanonLtValue (hALV : AcanonLtValue.{u})
    (hmem : ∀ (ζ : Ordinal.{u}) (w v : ℕ), v ≤ w → ζ ∈ CsetSelf (psiResSelf ζ) ζ w →
       ζ < psiSelf ζ w → ζ ∈ CsetSelf (psiResSelf (psiSelf ζ w)) (psiSelf ζ w) v) :
    PsiValueAcanon.{u} := by
  intro ζ w v hvw hζc
  set c := psiSelf ζ w with hcdef
  have hζlt : ζ < c := hALV hζc
  have hζmem : ζ ∈ CsetSelf (psiResSelf c) c v := hmem ζ w v hvw hζc hζlt
  have hζcanon : ζ ∈ CsetSelf (psiResSelf c) ζ w := by
    rwa [CsetSelf_param_eq (p := psiResSelf ζ) (q := psiResSelf c)
          (fun η uu hη => by rw [psiResSelf, psiResSelf, if_pos hη, if_pos (lt_trans hη hζlt)])] at hζc
  have hfire := CsetSelf_psi_closed hζmem hζlt w hζcanon
  rwa [psiResSelf, if_pos hζlt, ← hcdef] at hfire

/-! ### NON-COLLAPSE lever from the explicit formula (termination-critical)

The explicit value formula makes `ψ_a` **strictly monotone (injective) on the
sub-`ε(a)` range**, so there is NO `ψ_a`-plateau whose lower endpoint is below
`ε(a)`.  Concretely: a sub-`ε(a)` ordinal is `a`-canonical (`mem_Cself_lvl`), so
`psi_strict_mono_mem` fires with NO upper bound on the larger argument.  This is
the omitted-form lever that powers `oV_nf_arg_lt` (the non-collapse / argument
head), the DUAL of `CollapseResidue`.  These are PROVEN (sorryAx-free). -/

/-- **The non-collapse lever (omitted form).**  If `α < ε(a)` then `ψ_a` is
strictly increasing from `α` upward, with NO upper bound: `α < β → psi α a <
psi β a`.  (`α` is `a`-canonical by `mem_Cself_lvl`; `psi_strict_mono_mem`.) -/
theorem psi_strict_mono_lt_epsLvl {α β : Ordinal.{u}} {a : ℕ}
    (hαe : α < epsLvl a) (hαβ : α < β) : psi α a < psi β a :=
  psi_strict_mono_mem (CC_mono hαβ.le a (mem_Cself_lvl hαe)) hαβ

/-- **No `ψ_a`-collapse below `ε(a)`**: for `α < ε(a)` and `α ≤ β`,
`psi α a = psi β a ↔ α = β` is replaced by the usable form — distinctness of
arguments forces distinct values.  (Hence the plateau is confined to `≥ ε(a)`.) -/
theorem psi_noncollapse_lt_epsLvl {α β : Ordinal.{u}} {a : ℕ}
    (hαe : α < epsLvl a) (hαβ : α ≤ β) (hne : α ≠ β) : psi α a < psi β a :=
  psi_strict_mono_lt_epsLvl hαe (lt_of_le_of_ne hαβ hne)

/-- **`Nrm.oV_nf_arg_lt` discharged via the lever** (the §1 head content closed).
The argument-branch value strict-mono `oV (P 0 b c) < oV (P 0 f g)` follows from:
* `hbf` — the `<o`-to-`oV` order bridge `oV b < oV f` (NF-recursive order; the
  same recursion `oV_nf_order_pres` already runs);
* `hbe` — `oV b < ε(0)` (sub-`ε`: the head's genuine §1 hypothesis, now sufficient
  thanks to the lever — it REPLACES the false-on-`NF` `oV b ∈ C_0(oV b)`);
* `hspine` — tail domination `allprinc_lt (ψ_0(oV f)) c` (NF tail structure).

The §1 head `ψ_0(oV b) < ψ_0(oV f)` is PROVEN here by `psi_strict_mono_lt_epsLvl`
(no membership residual).  The remaining hypotheses are NF-structural (Wall B),
not §1.  This is the formula's payoff on the non-collapse leaf. -/
theorem oV_nf_arg_lt_of_lever {b c f g : Three}
    (hbf : oV.{u} b < oV f) (hbe : oV.{u} b < epsLvl 0)
    (hspine : allprinc_lt (psi.{u} (oV f) 0) c) :
    oV.{u} (P 0 b c) < oV (P 0 f g) := by
  have lead : psi.{u} (oV b) 0 < psi (oV f) 0 := psi_strict_mono_lt_epsLvl hbe hbf
  have hap : allprinc_lt (psi.{u} (oV f) 0) (P 0 b c) := ⟨lead, hspine⟩
  calc oV.{u} (P 0 b c) < psi (oV f) 0 := oV_lt_of_allprinc (psi_addprinc _ _) hap
    _ ≤ oV (P 0 f g) := psi_le_oV 0 f g

/-- **(a) `lwit c w < c` from `AcanonLtValue` + `CanonWitness`** (GREEN).  The
canonical witness `δ` is `< c` by `AcanonLtValue`, and `lwit ≤ δ` by minimality. -/
theorem a_of_AcanonLtValue (hALV : AcanonLtValue.{u}) (hCW : CanonWitness.{u})
    (ζ : Ordinal.{u}) (w : ℕ) : lwit (psiSelf ζ w) w < psiSelf ζ w := by
  obtain ⟨δ, hδv, hδc⟩ := hCW ζ w
  have hδlt : δ < psiSelf ζ w := hδv ▸ hALV hδc
  exact lt_of_le_of_lt
    (csInf_le' (s := {x : Ordinal | psiSelf x w = psiSelf ζ w}) hδv) hδlt

/-- **The residual for (a): `CanonWitnessLt`.**  Every ψ-value `psiSelf ζ w` has a
witness `δ < epsLvl w` (`psiSelf δ w = psiSelf ζ w`).  Because the "below value"
half is PROVEN (`AcanonLtValue_lt_epsLvl`), (a) follows from this existence
statement (`a_of_CanonWitnessLt`).

**⚠ CORRECTION / SOUNDNESS NOTE (this session).**  `CanonWitnessLt` is **FALSE at
ε-fixpoint values** and is therefore NOT a sound final residual for the *general*
(a).  Reason: by the explicit formula, witnesses `δ < ε(w)` give values
`psiSelf δ w = ω^(Ω_w+δ) < ε(w)`; so for `c = psiSelf ζ w` with `c ≥ ε(w)` (which
happens exactly when `ζ ≥ ε(w)`, e.g. the fixpoint `psiSelf ε(w) w = ε(w)`) there
is NO witness below `ε(w)`.  At such fixpoint values `lwit c w = c`, so even (a)
`lwit < c` itself FAILS.  Consequently the `lwit`-decomposition of `PsiValueAcanon`
is sound ONLY at non-fixpoint values; the ε-fixpoint values must be handled
directly (they are ε-numbers, additively principal limits, canonical via the limit
structure of `CsetSelf`).  This corrects the earlier "conjecturally TRUE" claim.
(NB: my indexing has `Ω_v = ω_v`, `Ω_0 = 1`, so the boundary is `ε(w)`, and
ya-pss's `Ω_1 = ω` counterexample to `acanon ⟹ δ<ψ` does NOT transfer — my
`AcanonLtValue_lt_epsLvl` is correct in this indexing.) -/
def CanonWitnessLt.{u} : Prop :=
  ∀ (ζ : Ordinal.{u}) (w : ℕ), ∃ δ, δ < epsLvl w ∧ psiSelf δ w = psiSelf ζ w

/-- **(a) `lwit c w < c` from `CanonWitnessLt` ALONE** (GREEN) — the "below value"
half is discharged by the PROVEN `AcanonLtValue_lt_epsLvl`. -/
theorem a_of_CanonWitnessLt (hCW : CanonWitnessLt.{u})
    (ζ : Ordinal.{u}) (w : ℕ) : lwit (psiSelf ζ w) w < psiSelf ζ w := by
  obtain ⟨δ, hδlt, hδv⟩ := hCW ζ w
  have hδc : δ < psiSelf ζ w := hδv ▸ AcanonLtValue_lt_epsLvl hδlt
  exact lt_of_le_of_lt
    (csInf_le' (s := {x : Ordinal | psiSelf x w = psiSelf ζ w}) hδv) hδc

/-- **The collapse-region residual `CanonWitnessLtBig`** — `ζ ≥ epsLvl w` ⟹ the
value `psiSelf ζ w` is attained by some `δ < epsLvl w`.

**⚠ FALSE (this session's finding).**  This is NOT true: for `ζ ≥ ε(w)`,
`psiSelf ζ w ≥ psiSelf ε(w) w = ε(w)` (the fixpoint), while every `δ < ε(w)` gives
`psiSelf δ w < ε(w)`.  So no sub-`ε(w)` witness exists for these values — the
"args beyond `ε(w)` add no new ψ-value" intuition is WRONG at the ε-boundary (they
add exactly the fixpoint and above).  Kept as a documented dead-end; the genuine
collapse-region content is that those values are themselves ε-numbers handled
directly, NOT re-attained below `ε(w)`. -/
def CanonWitnessLtBig.{u} : Prop :=
  ∀ (ζ : Ordinal.{u}) (w : ℕ), epsLvl w ≤ ζ →
    ∃ δ, δ < epsLvl w ∧ psiSelf δ w = psiSelf ζ w

/-- `CanonWitnessLt` from the collapse-region residual (the `ζ < ε(w)` case is the
trivial witness `δ = ζ`). -/
theorem CanonWitnessLt_of_big (hbig : CanonWitnessLtBig.{u}) : CanonWitnessLt.{u} := by
  intro ζ w
  rcases lt_or_ge ζ (epsLvl w) with h | h
  · exact ⟨ζ, h, rfl⟩
  · exact hbig ζ w h

/-- **`PsiValueAcanon` from the two sub-residuals (a) and (c)** (with (b) derived).
GREEN: given (a) `lwit c w < c` and (c) `lwit c w ∈ C_v(c)`, the least witness is
canonical at `w` (from (a)), and `CsetSelf_psi_closed` reproduces
`psiSelf (lwit) w = c` inside `C_v(c)`. -/
theorem psiValueAcanon_of_ac
    (ha : ∀ (ζ : Ordinal.{u}) (w : ℕ), lwit (psiSelf ζ w) w < psiSelf ζ w)
    (hc : ∀ (ζ : Ordinal.{u}) (w v : ℕ), v ≤ w →
       lwit (psiSelf ζ w) w ∈ CsetSelf (psiResSelf (psiSelf ζ w)) (psiSelf ζ w) v) :
    PsiValueAcanon.{u} := by
  intro ζ w v hvw _hζc
  set c := psiSelf ζ w with hcdef
  set ξ0 := lwit c w with hξ0
  have hval : psiSelf ξ0 w = c := lwit_val ζ w
  have haa : ξ0 < c := ha ζ w
  -- (b) derived from (a): canonical at w
  have hbb : ξ0 ∈ CsetSelf (psiResSelf ξ0) ξ0 w := by
    by_contra hnc
    have hle : psiSelf ξ0 w ≤ ξ0 := psiSelf_le_self_of_not_canon hnc
    rw [hval] at hle
    exact absurd hle (not_le.2 haa)
  have hcc : ξ0 ∈ CsetSelf (psiResSelf c) c v := hc ζ w v hvw
  have hconv : ξ0 ∈ CsetSelf (psiResSelf c) ξ0 w := by
    rwa [CsetSelf_param_eq (p := psiResSelf ξ0) (q := psiResSelf c)
          (fun ζ' uu hζ' => by
            rw [psiResSelf, psiResSelf, if_pos hζ', if_pos (lt_trans hζ' haa)])] at hbb
  have hfire := CsetSelf_psi_closed hcc haa w hconv
  rw [psiResSelf, if_pos haa, hval] at hfire
  exact hfire

/-- **The GENUINE `alpha_step_residue` residual (canonical-witness existence).**
Since the vacuity route is UNSOUND (`PsiValueAcanon_is_false`), `alpha_step_residue`
is NOT vacuous: the non-canonical generator value `psiSelf ξ u` must be genuinely
reproduced via its **canonical representative** `δ` — `δ ∈ C_v(α) ∩ Iio α`, `δ`
`u`-canonical, `psiSelf δ u = psiSelf ξ u`.  This is the real Buchholz §1 core
(necessity.thy:1139 content), not a contradiction. -/
def AlphaStepResidue.{u} : Prop :=
  ∀ (α : Ordinal.{u}) (v : ℕ) (ξ : Ordinal.{u}) (u : ℕ),
    ξ ∈ CsetSelf (psiResSelf α) α v → ξ < α →
    ξ ∉ CsetSelf (psiResSelf ξ) ξ u → v ≤ u →
    ∃ δ, δ < α ∧ δ ∈ CsetSelf (psiResSelf α) α v ∧
      δ ∈ CsetSelf (psiResSelf δ) δ u ∧ psiSelf δ u = psiSelf ξ u

/-! ### `AlphaStepResidue` SHARPENED to the bare value-membership

The whole `AlphaStepResidue` (canonical-representative existence) is **equivalent**
to the bare membership `psiSelf ξ u ∈ CsetSelf(psiResSelf α) α v` (= ya-pss's
`value_in_Cset_c_residue`, the most primitive form of the Buchholz Remark
`C_v(α) = C^c_v(α)`): given the membership, `CsetSelf_witness_canonical` (1.4b)
EXTRACTS the canonical generator `δ` (band forces the subscript `u`), so the
existential is recovered, NOT assumed.  This drops the witness construction. -/

/-- **The sharpest necessity-face residual: `NoncanonValueMem`.**  Every
non-canonical generator value lands in the closure:
`psiSelf ξ u ∈ CsetSelf(psiResSelf α) α v`.  Equivalent to `AlphaStepResidue`
(`canonRep_of_mem`); = ya-pss `value_in_Cset_c_residue` = the Buchholz Remark
content `C_v(α) = C^c_v(α)`, TRUE. -/
def NoncanonValueMem.{u} : Prop :=
  ∀ (α : Ordinal.{u}) (v : ℕ) (ξ : Ordinal.{u}) (u : ℕ),
    ξ ∈ CsetSelf (psiResSelf α) α v → ξ < α →
    ξ ∉ CsetSelf (psiResSelf ξ) ξ u → v ≤ u →
    psiSelf ξ u ∈ CsetSelf (psiResSelf α) α v

/-- **`AlphaStepResidue` from `NoncanonValueMem`** (GREEN): the canonical rep `δ` is
extracted from the membership by `CsetSelf_witness_canonical` (1.4b), with the band
forcing its subscript to `u`.  So the existential canonical-rep is recovered, not
assumed — the witness construction is dropped. -/
theorem alphaStepResidue_of_mem (H : NoncanonValueMem.{u}) : AlphaStepResidue.{u} := by
  intro α v ξ u hξC hξα hnc hvu
  have hmem : psiSelf ξ u ∈ CsetSelf (psiResSelf α) α v := H α v ξ u hξC hξα hnc hvu
  have hlo : Om v ≤ psiSelf ξ u := le_trans (Om_mono hvu) (Om_le_psiSelf ξ u)
  have hpr : Ordinal.IsPrincipal (· + ·) (psiSelf ξ u) :=
    fun {x y} hx hy => (psiSelf_addprinc ξ u).2 x y hx hy
  obtain ⟨u', δ, heq, hδα, hδv, hδc⟩ := CsetSelf_witness_canonical hpr hlo hmem
  rw [psiResSelf, if_pos hδα] at heq
  have hua : u' = u := by
    have h1 : Om u' ≤ psiSelf ξ u := heq ▸ Om_le_psiSelf δ u'
    have h2 : psiSelf ξ u < Om (u' + 1) := heq ▸ psiSelf_lt_Om_succ δ u'
    have hle1 : u' ≤ u := by
      by_contra hc; exact absurd (lt_of_le_of_lt h1 (psiSelf_lt_Om_succ ξ u)) (not_lt.2 (Om_mono (by omega)))
    have hle2 : u ≤ u' := by
      by_contra hc; exact absurd (lt_of_le_of_lt (Om_le_psiSelf ξ u) h2) (not_lt.2 (Om_mono (by omega)))
    omega
  rw [hua] at heq hδc
  have hδc_self : δ ∈ CsetSelf (psiResSelf δ) δ u :=
    CsetSelf_mono_param _ _ δ u
      (fun ζ uu hζ => by rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hδα)]) hδc
  exact ⟨δ, hδα, hδv, hδc_self, heq.symm⟩

/-- **Finishing step of the joint induction (GREEN, sorry-free): canonical rep ⟹
membership.**  If the value `psiSelf ξ u` has a `u`-canonical representative `δ < α`
inside `CsetSelf α v` (`psiSelf δ u = psiSelf ξ u`), then `psiSelf ξ u ∈ CsetSelf
α v` — by `CsetSelf_psi_closed` (δ canonical fires `psiSelf δ u` into the closure)
and the value rewrite.  This is the *converse* of `alphaStepResidue_of_mem`: together
they give `NoncanonValueMem ⟺ AlphaStepResidue` (canonical-rep existence).  So the
joint induction's whole burden is PRODUCING `δ` (= `proj u ξ`, the canonical rep;
model-verified `δ < α`, `δ ∈ CsetSelf α v`, `δ` canonical, value-equal at
closure+5/+6, 30001/30001). -/
theorem nvm_finish_of_rep {α : Ordinal.{u}} {v : ℕ} {ξ : Ordinal.{u}} {u : ℕ}
    (δ : Ordinal.{u})
    (hδα : δ < α) (hδC : δ ∈ CsetSelf (psiResSelf α) α v)
    (hδcanon : δ ∈ CsetSelf (psiResSelf δ) δ u)
    (hval : psiSelf δ u = psiSelf ξ u) :
    psiSelf ξ u ∈ CsetSelf (psiResSelf α) α v := by
  have hconv : δ ∈ CsetSelf (psiResSelf α) δ u :=
    CsetSelf_mono_param _ _ δ u
      (fun ζ uu hζ => by rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hδα)]) hδcanon
  have hfire := CsetSelf_psi_closed hδC hδα u hconv
  rw [psiResSelf, if_pos hδα, hval] at hfire
  exact hfire

/-- **`NoncanonValueMem ⟺ AlphaStepResidue`** (both directions GREEN).  Forward is
`alphaStepResidue_of_mem`; backward feeds the canonical rep through
`nvm_finish_of_rep`.  Confirms the two §1 faces are the SAME content; the joint
induction targets either. -/
theorem noncanonValueMem_iff_alphaStepResidue :
    NoncanonValueMem.{u} ↔ AlphaStepResidue.{u} := by
  refine ⟨alphaStepResidue_of_mem, fun H α v ξ u hξC hξα hnc hvu => ?_⟩
  obtain ⟨δ, hδα, hδC, hδcanon, hval⟩ := H α v ξ u hξC hξα hnc hvu
  exact nvm_finish_of_rep δ hδα hδC hδcanon hval

/-! ### THE GENUINE BUCHHOLZ §1 JOINT SIMULTANEOUS TRANSFINITE INDUCTION

`NoncanonValueMem` (= `AlphaStepResidue`, the §1 necessity/canonical-rep face) is
proven here by the genuine Buchholz joint induction: **outer strong induction on the
bound `α`, inner induction on the closure-rank `n`** of the generator `ξ` in
`CsetSelf α v`.  The induction is structured so that the canonical-rep identity
(`psi_proj`) needed at the non-canonical-generator step is supplied by the IH at
SMALLER data — breaking the circularity that blocks the monolithic residual.

The skeleton (`noncanonValueMem_joint`) is **fully proven** (sorry-free) modulo
EXACTLY FOUR precise sub-lemmas, each model-verified TRUE at closure+5/+6 with
explicit canonicity (so NONE is an Ω-crossing false proxy):

* `NVM_subA_le` — `ψ^s_w(η) ≤ η` when `η` is `u`-canonical (`u ≤ w`) and `ψ^s_w(η)`
  is `u`-non-canonical (the band fact `Ω_{w+1} ≤ η`; 343/343 at +6);
* `NVM_subA_nm` — `ψ^s_u(ψ^s_w(η)) ∉ C^s_u(η)` (the plateau-collapse non-membership;
  343/343);  [together (A) closes the generator step when `η` is `u`-canonical, via
  the plateau bridge `psiSelf_eq_of_notMem`: `δ = η`]
* `NVM_caseB` — the generator step when `η` is `u`-NON-canonical (`δ = proj_u η`,
  the rep of `η`; canon + value-collapse 151/151);
* `NVM_caseSum` — the sum step `ξ = x + y` (rare, 3/497).

What is ALREADY CLOSED in the skeleton (sorry-free): the base case `n = 0`
(`ξ < Ω_v` ⟹ canonical, vacuous); the rank-descent case; the generator step
sub-case (A) (`η` `u`-canonical) via the bridge; the `w < u` band case (vacuous:
`ψ^s_w(η) < Ω_{w+1} ≤ Ω_u`); and the finishing step (`nvm_finish_of_rep`).

This REPLACES the single monolithic `NoncanonValueMem` sorry with four strictly
smaller, model-verified residuals — the sharper joint-induction skeleton. -/

/-! ### The value-bounded gap collapse — the genuine §1 lever for the Ω-crossing region

`collapseSelf_le` (Buchholz17) requires *every* gap point `γ ∈ [α,β)` to be
`a`-NON-canonical, so its succ-step `collapseSelf_succ` fires.  In the deep
ε-collapse region the gap crosses `a`-CANONICAL `Ω_k` points (the Ω-crossing that
killed `IntervalNoncanon`), so `collapseSelf_le` is inapplicable there.

The genuine §1 generalization admits `a`-canonical gap points **provided their
value is bounded by the collapse target**: a canonical `γ ∈ [α,β)` contributes its
generator value `ψ^s_a(γ)` to `C^s_a(β)`, but if `ψ^s_a(γ) < ψ^s_a(α)` that value
is already below the target and harmless — `ψ^s_a(α)` stays the least non-member.

Proof (no succ-induction; direct via `psiSelf_eq_of_notMem`): suppose
`ψ^s_a(α) ∈ C^s_a(β)`.  `CsetSelf_witness_canonical` extracts a CANONICAL generator
`ξ` (band forces subscript `a`) with `ξ < β` and `ψ^s_a(ξ) = ψ^s_a(α)`.  Either
`ξ < α` (then `psiSelf_strict_mono_arg` gives `ψ^s_a(ξ) < ψ^s_a(α)`, contradiction)
or `α ≤ ξ < β` (then `ξ` is an `a`-canonical gap point, so the value-bound gives
`ψ^s_a(ξ) < ψ^s_a(α)`, contradiction).  Either way the membership is impossible.

Model-verified (`tools/probe_vb.py`, closure+5/+6/+7): the value-bound holds 623/623
in the sub-case-A crux instances (every `a`-canonical `γ ∈ [c,η)` has
`ψ^s_a(γ) < ψ^s_a(c)`), and the BAD `=` case is 0/623 (load-bearing). -/
theorem collapseSelf_le_valuebounded {a : ℕ} {α β : Ordinal.{u}} (hαβ : α ≤ β)
    (hgap : ∀ γ, α ≤ γ → γ < β →
      γ ∈ CsetSelf (psiResSelf γ) γ a → psiSelf γ a < psiSelf α a) :
    psiSelf α a = psiSelf β a := by
  apply psiSelf_eq_of_notMem hαβ
  intro hmem
  -- extract the canonical generator witness ξ of the value psiSelf α a
  have hap : Ordinal.IsPrincipal (· + ·) (psiSelf α a) :=
    fun {x y} hx hy => (psiSelf_addprinc α a).2 x y hx hy
  obtain ⟨u', ξ, heq, hξβ, _hξmem, hξc⟩ :=
    CsetSelf_witness_canonical hap (Om_le_psiSelf α a) hmem
  rw [psiResSelf, if_pos hξβ] at heq
  -- band forces the generator subscript u' = a
  have hu : u' = a := by
    have h1 : Om u' ≤ psiSelf α a := heq ▸ Om_le_psiSelf ξ u'
    have h2 : psiSelf α a < Om (u' + 1) := heq ▸ psiSelf_lt_Om_succ ξ u'
    have hle1 : u' ≤ a := by
      by_contra hcc
      exact absurd (lt_of_le_of_lt h1 (psiSelf_lt_Om_succ α a)) (not_lt.2 (Om_mono (by omega)))
    have hle2 : a ≤ u' := by
      by_contra hcc
      exact absurd (lt_of_le_of_lt (Om_le_psiSelf α a) h2) (not_lt.2 (Om_mono (by omega)))
    omega
  subst u'
  -- convert the witness canonicity from `psiResSelf β`-param to the self-param
  -- (`psiResSelf ξ`), valid since both agree strictly below the bound `ξ < β`
  have hξc_self : ξ ∈ CsetSelf (psiResSelf ξ) ξ a :=
    CsetSelf_mono_param _ _ ξ a
      (fun ζ uu hζ => by
        rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hξβ)]) hξc
  -- ξ is a-canonical with psiSelf ξ a = psiSelf α a; case on ξ < α vs α ≤ ξ
  rcases lt_or_ge ξ α with hξα | hαξ
  · -- ξ < α, ξ canonical ⟹ psiSelf ξ a < psiSelf α a, contradicting heq
    exact absurd heq.symm (ne_of_lt (psiSelf_strict_mono_arg hξα hξc_self))
  · -- α ≤ ξ < β, ξ a-canonical ⟹ value-bound psiSelf ξ a < psiSelf α a, contra heq
    exact absurd heq.symm (ne_of_lt (hgap ξ hαξ hξβ hξc_self))

/-! ### GREEN PIECE 1 (Gset construction, step 1): the self-form Buchholz 1.5

The whole §1 residue (all four leaves of `noncanonValueMem_joint`, the closure
face `AlphaStepResidue`/`alpha_step_residue` AND the collapse face
`CollapseResidueMaxo`) bottoms out — via `collapseSelf_le_valuebounded` — at the
**deep-region value-bound**: every `u`-canonical gap point `γ ∈ [α,β)` has
`ψ^s_u(γ) < ψ^s_u(α)`.  The minimal construction discharging it is Buchholz's
`G_uγ` device + Lemma 1.9 (`γ ∈ C_u(α) ⟺ G_uγ ⊆ α`), NOT the full normal-form
term system T.

This lemma is the FIRST bridge: by Buchholz Lemma 1.5 (self-form), the value-bound
`ψ^s_u(γ) < ψ^s_u(α)` is *equivalent* to the membership
`γ ∈ C^s_u(α)` for a `u`-canonical `γ` — because `ψ^s_u(γ) < Ω_{u+1}` always, and
1.5 says `C^s_u(α) ∩ Ω_{u+1} = ψ^s_u(α)`; so once `γ`'s canonical generators are
`< α` (the `G_u` content) `CsetSelf_psi_closed` fires `ψ^s_u(γ) ∈ C^s_u(α)` and 1.5
converts it to the strict bound.  See `psiSelf_lt_of_mem_canon` (the bound from
membership) immediately below. -/

open Ordinal in
/-- **Buchholz Lemma 1.5 (self-form, one direction), `C^s_a(α) ∩ Ω_{a+1} = ψ^s_a(α)`.**
Every member of `C^s_a(α)` that is `< Ω_{a+1}` is `< ψ^s_a(α)`.  Self-form port of
`Otembed.Cset_lt_psi_of_lt_Om` (clean `CstepSelf'`-stage induction; the
`ψ`-generator case at `u = a` uses `psiSelf_strict_mono_arg`, no circularity). -/
theorem CsetSelf_lt_psiSelf_of_lt_Om {α x : Ordinal.{u}} {a : ℕ}
    (hx : x ∈ CsetSelf (psiResSelf α) α a) (hlt : x < Om (a + 1)) :
    x < psiSelf α a := by
  obtain ⟨n, hn⟩ := CsetSelf_mem_iff.1 hx
  clear hx
  induction n generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hn
    exact lt_of_lt_of_le hn (Om_le_psiSelf α a)
  | succ n IH =>
    rw [Function.iterate_succ_apply'] at hn
    rcases hn with (h1 | h2) | h3
    · exact IH hlt h1
    · obtain ⟨y, hy, z, hz, hyz⟩ := h2
      have hyx : y ≤ x := hyz ▸ le_self_add
      have hzx : z ≤ x := hyz ▸ le_add_self
      have hy' : y < psiSelf α a := IH (lt_of_le_of_lt hyx hlt) hy
      have hz' : z < psiSelf α a := IH (lt_of_le_of_lt hzx hlt) hz
      rw [← hyz]
      exact (psiSelf_addprinc α a).2 y z hy' hz'
    · obtain ⟨u, ⟨ξ, ⟨hξC, hξα, hξcanon⟩, hξx⟩⟩ := Set.mem_iUnion.1 h3
      simp only [psiResSelf, if_pos hξα] at hξx
      subst hξx
      have hu_le : u ≤ a := by
        by_contra hc
        have hau : a + 1 ≤ u := by omega
        exact absurd (lt_of_lt_of_le hlt (Om_mono hau)) (not_lt.2 (Om_le_psiSelf ξ u))
      rcases lt_or_eq_of_le hu_le with hua | hua
      · calc psiSelf ξ u < Om (u + 1) := psiSelf_lt_Om_succ ξ u
          _ ≤ Om a := Om_mono (by omega)
          _ ≤ psiSelf α a := Om_le_psiSelf α a
      · subst hua
        have hξcanon' : ξ ∈ CsetSelf (psiResSelf ξ) ξ u :=
          CsetSelf_mono_param _ _ ξ u
            (fun ζ uu hζ => by
              rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hξα)]) hξcanon
        exact psiSelf_strict_mono_arg hξα hξcanon'

/-- **GREEN PIECE 2: the value-bound from canonical membership.**  If a
`u`-canonical `γ` lies in `C^s_u(α)` and `γ < α`, then `ψ^s_u(γ) < ψ^s_u(α)`.
This is the bridge consumed by `collapseSelf_le_valuebounded`'s `hgap`: it converts
the *membership* `γ ∈ C^s_u(α)` (the `G_u γ ⊆ α` content) into the value-bound.
Proof: `CsetSelf_psi_closed` fires `ψ^s_u(γ) ∈ C^s_u(α)`, then Lemma 1.5
(`CsetSelf_lt_psiSelf_of_lt_Om`, with `ψ^s_u(γ) < Ω_{u+1}`) gives the strict bound. -/
theorem psiSelf_lt_of_mem_canon {α γ : Ordinal.{u}} {u : ℕ}
    (hγα : γ < α) (hγC : γ ∈ CsetSelf (psiResSelf α) α u)
    (hγcanon : γ ∈ CsetSelf (psiResSelf γ) γ u) :
    psiSelf γ u < psiSelf α u := by
  have hconv : γ ∈ CsetSelf (psiResSelf α) γ u :=
    CsetSelf_mono_param _ _ γ u
      (fun ζ uu hζ => by rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hγα)]) hγcanon
  have hfire := CsetSelf_psi_closed hγC hγα u hconv
  rw [psiResSelf, if_pos hγα] at hfire
  exact CsetSelf_lt_psiSelf_of_lt_Om hfire (psiSelf_lt_Om_succ γ u)

/-- **GREEN PIECE 5: full self-form Buchholz 1.5 characterization** (both directions).
For `x < Ω_{a+1}`: `x ∈ C^s_a(α) ⟺ x < ψ^s_a(α)`.  Forward is
`CsetSelf_lt_psiSelf_of_lt_Om`; backward is `below_psiSelf_mem_CsetSelf`.  This is the
clean membership ↔ value-order bridge the `G_u`/Lemma-1.9 gap-cleanness work consumes
(`ψ^s`-values are `< Ω_{a+1}`, so membership of a value is the same as its value-order
position). -/
theorem mem_CsetSelf_iff_lt_psiSelf {α x : Ordinal.{u}} {a : ℕ} (hlt : x < Om (a + 1)) :
    x ∈ CsetSelf (psiResSelf α) α a ↔ x < psiSelf α a :=
  ⟨fun hx => CsetSelf_lt_psiSelf_of_lt_Om hx hlt, fun hx => below_psiSelf_mem_CsetSelf hx⟩

/-- **`subA_nm`'s conclusion from the value-bound** (GREEN, hypothesis-carrying).
The generator-step (A) plateau-collapse non-membership `ψ^s_u(ψ^s_w(η)) ∉ C^s_u(η)`
follows from `collapseSelf_le_valuebounded` applied to the gap `[ψ^s_w(η), η]`: the
collapse gives `ψ^s_u(ψ^s_w(η)) = ψ^s_u(η)`, and `ψ^s_u(η) ∉ C^s_u(η)` is
`psiSelf_notMem`.  The two carried hypotheses — `hle : ψ^s_w(η) ≤ η` (supplied by
`subA_le` in the skeleton) and the value-bound `hVB` (the genuine §1 content the
joint induction must output) — make this `sorry`-free.  This isolates the remaining
content of `subA_nm` to exactly the value-bound `hVB`. -/
theorem subA_nm_of_valuebound {η : Ordinal.{u}} {w u : ℕ}
    (hle : psiSelf η w ≤ η)
    (hVB : ∀ γ, psiSelf η w ≤ γ → γ < η →
      γ ∈ CsetSelf (psiResSelf γ) γ u → psiSelf γ u < psiSelf (psiSelf η w) u) :
    psiSelf (psiSelf η w) u ∉ CsetSelf (psiResSelf η) η u := by
  have hcollapse : psiSelf (psiSelf η w) u = psiSelf η u :=
    collapseSelf_le_valuebounded hle hVB
  rw [hcollapse]
  exact psiSelf_notMem η u

/-- **H1 (the caseB residue) from the two shared-rep value-bounds** (GREEN,
hypothesis-carrying).  The subscript-collapse `ψ^s_u(η) = ψ^s_u(ψ^s_w(η))` is
assembled from psi_proj at `η` and at `c = ψ^s_w(η)` through their COMMON `u`-rep
`δ` (model: `proj_u η = proj_u(ψ^s_w η)`, 884/884, and both `≤ δ`):

* `ψ^s_u(η) = ψ^s_u(δ)`  via `collapseSelf_le_valuebounded` (gap `[η,δ)`, bound `hVBη`);
* `ψ^s_u(c) = ψ^s_u(δ)`  via `collapseSelf_le_valuebounded` (gap `[c,δ)`, bound `hVBc`);
* compose: `ψ^s_u(η) = ψ^s_u(δ) = ψ^s_u(c)`.

The two value-bounds `hVBη`, `hVBc` (every `u`-canonical gap point has value
`< ψ^s_u(·)` of the lower endpoint; model 884/884 @+5/+6/+7) are the genuine §1
value-identity content the joint recursion must supply.  This reduces `NVM_caseB`
(H1) to exactly those two value-bounds at a shared canonical rep `δ`. -/
theorem caseB_H1_of_valuebounds {η : Ordinal.{u}} {w u : ℕ} (δ : Ordinal.{u})
    (hηδ : η ≤ δ) (hcδ : psiSelf η w ≤ δ)
    (hVBη : ∀ γ, η ≤ γ → γ < δ →
      γ ∈ CsetSelf (psiResSelf γ) γ u → psiSelf γ u < psiSelf η u)
    (hVBc : ∀ γ, psiSelf η w ≤ γ → γ < δ →
      γ ∈ CsetSelf (psiResSelf γ) γ u → psiSelf γ u < psiSelf (psiSelf η w) u) :
    psiSelf η u = psiSelf (psiSelf η w) u := by
  have h1 : psiSelf η u = psiSelf δ u := collapseSelf_le_valuebounded hηδ hVBη
  have h2 : psiSelf (psiSelf η w) u = psiSelf δ u := collapseSelf_le_valuebounded hcδ hVBc
  rw [h1, h2]

/-! ### ⚠⚠⚠ SOUNDNESS CORRECTION — the value-bound `hVB` is FALSE in true ordinals

**The value-bound `hVB`/`hVBη`/`hVBc` (consumed by `subA_nm_of_valuebound` and
`caseB_H1_of_valuebounds`) is FALSE in the genuine ordinals.**  Proven below
(`hVB_is_contradictory`, sorryAx-free): `hVB` asserts `psiSelf γ u < psiSelf α u`
for a gap point `α ≤ γ`, but `psiSelf_mono_arg` gives `psiSelf α u ≤ psiSelf γ u`
from `α ≤ γ` — a flat contradiction the instant ANY `u`-canonical `γ` exists in the
**ordinal** interval `[α, β)`.  So `hVB` is satisfiable ONLY when the gap is
canonical-free — i.e. it adds NOTHING over `collapseSelf_le`'s clean-gap condition.

The prior "`hVB` model-verified 623/623, 884/884 @+5/+6/+7" certifications were a
**term-model artifact**: they ordered the gap by `lt_term`, which is NOT faithful to
`psiSelf`'s ordinal order — the term model violates `psiSelf` monotonicity 85356×
(`tools/probe_mono_check.py`, rounds 7).  This is the recurrence, at the value-bound
layer, of the "`subA_nm`-was-silently-false" lesson.  `collapseSelf_le_valuebounded`
itself is SOUND (it just collapses to `collapseSelf_le` on canonical-free gaps), but
the leaves CANNOT supply `hVB`.

**The HONEST residue** (TRUE, Buchholz 1.6(b) plateau condition): the ordinal gap
`[ψ^s_w(η), η)` is entirely `u`-non-canonical (`subA_nm_of_cleangap`); the two caseB
gaps `[η,δ)`, `[c,δ)` likewise (`caseB_H1_of_cleangap`).  These discharge the leaves
via the GREEN clean `collapseSelf_le` with NO value-bound.  The genuine remaining §1
content is therefore **gap-cleanness**, established by the `G_u`/Lemma-1.9 device
(GREEN pieces 1-2 above are its first bridges). -/

/-- **`hVB` is contradictory at any ordinal-gap canonical point** (Lean-proven,
sorryAx-free).  Discharges the soundness correction: the value-bound form of the
generator-step residue is FALSE in true ordinals. -/
theorem hVB_is_contradictory {α β : Ordinal.{u}} {u : ℕ}
    (hVB : ∀ γ, α ≤ γ → γ < β →
      γ ∈ CsetSelf (psiResSelf γ) γ u → psiSelf γ u < psiSelf α u)
    {γ : Ordinal.{u}} (h1 : α ≤ γ) (h2 : γ < β)
    (hc : γ ∈ CsetSelf (psiResSelf γ) γ u) : False :=
  absurd (hVB γ h1 h2 hc) (not_lt.2 (psiSelf_mono_arg h1 u))

/-- **GREEN PIECE 3: `subA_nm` from the HONEST clean-gap residue** (sound replacement
for the FALSE `subA_nm_of_valuebound`).  If the ordinal gap `[ψ^s_w(η), η)` is
entirely `u`-non-canonical, the clean `collapseSelf_le` gives the plateau collapse
`ψ^s_u(ψ^s_w(η)) = ψ^s_u(η)`, and `psiSelf_notMem` finishes.  No value-bound. -/
theorem subA_nm_of_cleangap {η : Ordinal.{u}} {w u : ℕ}
    (hle : psiSelf η w ≤ η)
    (hclean : ∀ γ, psiSelf η w ≤ γ → γ < η → γ ∉ CsetSelf (psiResSelf γ) γ u) :
    psiSelf (psiSelf η w) u ∉ CsetSelf (psiResSelf η) η u := by
  have hcollapse : psiSelf (psiSelf η w) u = psiSelf η u :=
    collapseSelf_le η (psiSelf η w) hle hclean
  rw [hcollapse]; exact psiSelf_notMem η u

/-- **GREEN PIECE 4: caseB H1 from the HONEST clean-gap residue** (sound replacement
for the FALSE `caseB_H1_of_valuebounds`).  Both caseB gaps `[η,δ)`, `[ψ^s_w(η),δ)`
entirely `u`-non-canonical ⟹ the shared-rep collapse `ψ^s_u(η) = ψ^s_u(δ) =
ψ^s_u(ψ^s_w(η))` via clean `collapseSelf_le`.  No value-bound. -/
theorem caseB_H1_of_cleangap {η : Ordinal.{u}} {w u : ℕ} (δ : Ordinal.{u})
    (hηδ : η ≤ δ) (hcδ : psiSelf η w ≤ δ)
    (hcleanη : ∀ γ, η ≤ γ → γ < δ → γ ∉ CsetSelf (psiResSelf γ) γ u)
    (hcleanc : ∀ γ, psiSelf η w ≤ γ → γ < δ → γ ∉ CsetSelf (psiResSelf γ) γ u) :
    psiSelf η u = psiSelf (psiSelf η w) u := by
  have h1 : psiSelf η u = psiSelf δ u := collapseSelf_le δ η hηδ hcleanη
  have h2 : psiSelf (psiSelf η w) u = psiSelf δ u := collapseSelf_le δ (psiSelf η w) hcδ hcleanc
  rw [h1, h2]

/-- **GREEN PIECE 7: subA_nm collapse from the NO-REALIZER condition** (the sharpest
honest §1 residue).  If no `u`-canonical `ζ < η` realizes the value `ψ^s_u(ψ^s_w η)`, then
`ψ^s_u(ψ^s_w η) = ψ^s_u η` (the sub-case-A collapse).  Proof: membership of `ψ^s_u(ψ^s_w η)`
in `C^s_u(η)` would, by `CsetSelf_witness_canonical` (1.4b), produce exactly such a
realizer `ζ < η` (band forces subscript `u`); absent it, `psiSelf_eq_of_notMem` gives the
collapse.  This is the dual of canonical-rep existence (`CanonRep`) and the genuine
deep-region core — soundly characterized (the collapse is an EQUALITY, consistent; its
`≤` half is free `psiSelf_mono_arg`; NOT a false value-bound like the dead `hVB`).  The
`G_u`/Lemma-1.9 construction in `Crank.lean` localizes the whole §1 residue to exactly
this condition (deep region); it holds unconditionally sub-`ε` (`AcanonLtValue_lt_epsLvl`). -/
theorem subA_nm_collapse_of_noRealizer {η : Ordinal.{u}} {w u : ℕ}
    (hle : psiSelf η w ≤ η)
    (hno : ∀ ζ : Ordinal.{u}, ζ < η → ζ ∈ CsetSelf (psiResSelf ζ) ζ u →
       psiSelf ζ u ≠ psiSelf (psiSelf η w) u) :
    psiSelf (psiSelf η w) u = psiSelf η u := by
  apply psiSelf_eq_of_notMem hle
  intro hmem
  have hlo : Om u ≤ psiSelf (psiSelf η w) u := Om_le_psiSelf _ _
  have hap : Ordinal.IsPrincipal (· + ·) (psiSelf (psiSelf η w) u) :=
    fun {x y} hx hy => (psiSelf_addprinc _ _).2 x y hx hy
  obtain ⟨u', ζ, heq, hζη, hζmem, hζc⟩ := CsetSelf_witness_canonical hap hlo hmem
  rw [psiResSelf, if_pos hζη] at heq
  have hu' : u' = u := by
    have h1 : Om u' ≤ psiSelf (psiSelf η w) u := heq ▸ Om_le_psiSelf ζ u'
    have h2 : psiSelf (psiSelf η w) u < Om (u' + 1) := heq ▸ psiSelf_lt_Om_succ ζ u'
    have hle1 : u' ≤ u := by
      by_contra hc
      exact absurd (lt_of_le_of_lt h1 (psiSelf_lt_Om_succ (psiSelf η w) u)) (not_lt.2 (Om_mono (by omega)))
    have hle2 : u ≤ u' := by
      by_contra hc
      exact absurd (lt_of_le_of_lt (Om_le_psiSelf (psiSelf η w) u) h2) (not_lt.2 (Om_mono (by omega)))
    omega
  subst hu'
  have hζc_self : ζ ∈ CsetSelf (psiResSelf ζ) ζ u' :=
    CsetSelf_mono_param _ _ ζ u'
      (fun ρ uu hρ => by rw [psiResSelf, psiResSelf, if_pos hρ, if_pos (lt_trans hρ hζη)]) hζc
  exact hno ζ hζη hζc_self heq.symm

/-- Generator step (A) BAND fact: `Ω_{w+1} ≤ η` when `η` is `u`-canonical (`u ≤ w`)
and `ψ^s_w(η)` is `u`-non-canonical.  Sharper than the prior `ψ^s_w(η) ≤ η` (which
follows by `psiSelf_lt_Om_succ` + this).  Mechanism (model-verified 4892/4892): a
`u`-canonical `η < Ω_{w+1}` makes `ψ^s_w(η)` `u`-canonical, so non-canonicity forces
`Ω_{w+1} ≤ η`. -/
def NVM_subA_le.{u} : Prop :=
  ∀ (η : Ordinal.{u}) (w u : ℕ), u ≤ w →
    η ∈ CsetSelf (psiResSelf η) η u →
    psiSelf η w ∉ CsetSelf (psiResSelf (psiSelf η w)) (psiSelf η w) u →
    Om (w + 1) ≤ η

/-- Generator step (A) plateau-collapse, **no-realizer form** (the HONEST §1 residue,
re-sounded 2026-06-20c — sharpest yet).  History: the VALUE-BOUND form was FALSE in true
ordinals (`hVB_is_contradictory`); the clean-gap form (`subA_nm_of_cleangap`) is TRUE but
needs full gap-cleanness.  The `G_u`/Lemma-1.9 construction (`Crank.lean`) LOCALIZES the
residue precisely to the **no-realizer condition**: no `u`-canonical `ζ < η` realizes the
value `ψ^s_u(ψ^s_w η)` (`Crank.subA_nm_collapse_of_noRealizer` then gives the collapse via
`CsetSelf_witness_canonical` + `psiSelf_eq_of_notMem`).  This is the dual of canonical-rep
existence (`CanonRep`) — the genuine deep-region core, soundly characterized: the collapse
is an EQUALITY (consistent; its `≤` half is free `psiSelf_mono_arg`), NOT a false
value-bound.  In the sub-ε region it holds (`AcanonLtValue_lt_epsLvl`). -/
def NVM_subA_nm.{u} : Prop :=
  ∀ (η : Ordinal.{u}) (w u : ℕ), u ≤ w →
    η ∈ CsetSelf (psiResSelf η) η u →
    psiSelf η w ∉ CsetSelf (psiResSelf (psiSelf η w)) (psiSelf η w) u →
    psiSelf η w ≤ η →
    ∀ ζ : Ordinal.{u}, ζ < η → ζ ∈ CsetSelf (psiResSelf ζ) ζ u →
      psiSelf ζ u ≠ psiSelf (psiSelf η w) u

/-- Generator step (B), **reduced to the subscript-collapse H1** (the genuine residue).
The full caseB (produce a canonical rep `δ` with `δ < α`, `δ ∈ C^s_v(α)`, `δ`
`u`-canonical, `ψ^s_u(δ) = ψ^s_u(ψ^s_w(η))`) is **discharged inside the skeleton by
the rank-IH `IHn` applied to `η`** (η is at rank `n`, `u`-non-canonical, `η < α`,
`v ≤ u`): `IHn` produces exactly the rep `δ` of `η` with `ψ^s_u(δ) = ψ^s_u(η)`.
The ONLY genuinely-new residue is then the **subscript collapse H1**
`ψ^s_u(η) = ψ^s_u(ψ^s_w(η))` (model-verified 884/884 @+5/+6/+7 in the caseB context:
η `u`-non-canonical, `u ≤ w`, `ψ^s_w(η)` `u`-non-canonical), which converts the
rep's value-identity to caseB's target.  This is the value-identity the recursion
must supply (= psi_proj at the value `ψ^s_w(η)`, whose `u`-rep coincides with η's:
`proj_u(ψ^s_w η) = proj_u η`, 884/884). -/
def NVM_caseB.{u} : Prop :=
  ∀ (η : Ordinal.{u}) (w u : ℕ),
    u ≤ w → η ∉ CsetSelf (psiResSelf η) η u →
    psiSelf η w ∉ CsetSelf (psiResSelf (psiSelf η w)) (psiSelf η w) u →
    psiSelf η u = psiSelf (psiSelf η w) u

/-- Sum step: `ξ = x + y` non-canonical generator. -/
def NVM_caseSum.{u} : Prop :=
  ∀ (α : Ordinal.{u}) (v u : ℕ) (x y : Ordinal.{u}),
    (x + y) < α → x + y ∉ CsetSelf (psiResSelf (x+y)) (x+y) u → v ≤ u →
    ∃ δ, δ < α ∧ δ ∈ CsetSelf (psiResSelf α) α v ∧
      δ ∈ CsetSelf (psiResSelf δ) δ u ∧ psiSelf δ u = psiSelf (x+y) u

/-- **`NoncanonValueMem` by the genuine Buchholz §1 joint simultaneous induction**
(outer on `α`, inner on closure-rank `n`).  Fully proven modulo the four precise
sub-lemmas above (all model-verified at closure+5/+6).  See the section header. -/
theorem noncanonValueMem_joint
    (subA_le : NVM_subA_le.{u}) (subA_nm : NVM_subA_nm.{u})
    (caseB : NVM_caseB.{u}) (caseSum : NVM_caseSum.{u}) :
    NoncanonValueMem.{u} := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IHα =>
    have rnk : ∀ (n : ℕ) (v u : ℕ) (ξ : Ordinal.{u}),
        ξ ∈ (CstepSelf' (psiResSelf α) α)^[n] (Set.Iio (Om v)) → ξ < α →
        ξ ∉ CsetSelf (psiResSelf ξ) ξ u → v ≤ u →
        ∃ δ, δ < α ∧ δ ∈ CsetSelf (psiResSelf α) α v ∧
          δ ∈ CsetSelf (psiResSelf δ) δ u ∧ psiSelf δ u = psiSelf ξ u := by
      intro n
      induction n with
      | zero =>
        intro v u ξ hn hξα hnc hvu
        simp only [Function.iterate_zero, id_eq] at hn
        exact absurd (Iio_Om_subset_CsetSelf (lt_of_lt_of_le hn (Om_mono hvu))) hnc
      | succ n IHn =>
        intro v u ξ hn hξα hnc hvu
        rw [Function.iterate_succ_apply'] at hn
        rcases hn with (h1 | h2) | h3
        · exact IHn v u ξ h1 hξα hnc hvu
        · obtain ⟨x, hx, y, hy, hxy⟩ := h2
          subst hxy
          exact caseSum α v u x y hξα hnc hvu
        · obtain ⟨w, ⟨η, ⟨hηX, hηα, hηcanon⟩, hηξ⟩⟩ := Set.mem_iUnion.1 h3
          simp only [psiResSelf, if_pos hηα] at hηξ
          subst hηξ
          have hηC : η ∈ CsetSelf (psiResSelf α) α v := CiterSelf_subset_CsetSelf hηX
          have hηcw : η ∈ CsetSelf (psiResSelf η) η w := by
            have h0 : η ∈ CsetSelf (psiResSelf α) η w := hηcanon
            exact CsetSelf_mono_param _ _ η w
              (fun ζ uu hζ => by
                rw [psiResSelf, psiResSelf, if_pos (lt_trans hζ hηα), if_pos hζ]) h0
          by_cases hwu : u ≤ w
          · by_cases hηu : η ∈ CsetSelf (psiResSelf η) η u
            · refine ⟨η, hηα, hηC, hηu, ?_⟩
              have hle : psiSelf η w ≤ η :=
                le_trans (le_of_lt (psiSelf_lt_Om_succ η w)) (subA_le η w u hwu hηu hnc)
              -- the HONEST no-realizer residue → collapse → the value-identity
              exact (subA_nm_collapse_of_noRealizer hle (subA_nm η w u hwu hηu hnc hle)).symm
            · -- η `u`-non-canonical: the rank-IH `IHn` at η produces η's canonical rep δ
              -- (`psiSelf δ u = psiSelf η u`); H1 (`caseB`) converts to the caseB target.
              obtain ⟨δ, hδα, hδC, hδcanon, hval⟩ := IHn v u η hηX hηα hηu hvu
              exact ⟨δ, hδα, hδC, hδcanon, hval.trans (caseB η w u hwu hηu hnc)⟩
          · push Not at hwu
            exact absurd
              (Iio_Om_subset_CsetSelf
                (lt_of_lt_of_le (psiSelf_lt_Om_succ η w) (Om_mono (by omega)))) hnc
    intro v ξ u hξC hξα hnc hvu
    obtain ⟨n, hn⟩ := CsetSelf_mem_iff.1 hξC
    obtain ⟨δ, hδα, hδC, hδcanon, hval⟩ := rnk n v u ξ hn hξα hnc hvu
    exact nvm_finish_of_rep δ hδα hδC hδcanon hval

/-- **The non-canonical generator value is itself non-canonical and `≤ ξ`**
(ya-pss `noncanon_value_noncanon`).  If `ξ ∉ C_u(ξ)` then `psiSelf ξ u ≤ ξ`
(`psiSelf_le_self_of_not_canon`) and `psiSelf ξ u ∉ C_u(psiSelf ξ u)` (else it
would lie in its own band-closure `⊆` the `ξ`-closure that excludes it, since
`psiSelf ξ u ≤ ξ`).  This is why the MINIMAL witness is unusable (it can be the
non-canonical value itself / a ψ-fixpoint). -/
theorem noncanon_value_noncanon {ξ : Ordinal.{u}} {u : ℕ}
    (hnc : ξ ∉ CsetSelf (psiResSelf ξ) ξ u) :
    psiSelf ξ u ≤ ξ ∧ psiSelf ξ u ∉ CsetSelf (psiResSelf (psiSelf ξ u)) (psiSelf ξ u) u := by
  have hle : psiSelf ξ u ≤ ξ := psiSelf_le_self_of_not_canon hnc
  refine ⟨hle, ?_⟩
  intro hcc
  -- psiSelf ξ u ∈ C_u(psiSelf ξ u) ⊆ C_u(ξ) (CCSelf_mono, psiSelf ξ u ≤ ξ),
  -- contradicting psiSelf_notMem ξ u : psiSelf ξ u ∉ C_u(ξ).
  exact psiSelf_notMem ξ u (CCSelf_mono (α := psiSelf ξ u) (β := ξ) hle u hcc)


/-- **`NoncanonValueMem` reduces to the STRICT case `psiSelf ξ u < ξ`** (GREEN).
By `noncanon_value_noncanon` the value `c = psiSelf ξ u` satisfies `c ≤ ξ`.  The
fixpoint case `c = ξ` is FREE: then `psiSelf ξ u = ξ ∈ C_v(α)` is exactly the
generator hypothesis `hξC`.  So the genuine residual is only the strict subcase
`c < ξ`, where the value is a brand-new ordinal strictly below the (noncanonical)
generator — the irreducible Buchholz Remark content.  `NoncanonValueMemStrict`
assumes the strict band; `nvm_of_strict` lifts it to the full `NoncanonValueMem`. -/
def NoncanonValueMemStrict.{u} : Prop :=
  ∀ (α : Ordinal.{u}) (v : ℕ) (ξ : Ordinal.{u}) (u : ℕ),
    ξ ∈ CsetSelf (psiResSelf α) α v → ξ < α →
    ξ ∉ CsetSelf (psiResSelf ξ) ξ u → v ≤ u →
    psiSelf ξ u < ξ →
    psiSelf ξ u ∈ CsetSelf (psiResSelf α) α v

theorem nvm_of_strict (H : NoncanonValueMemStrict.{u}) : NoncanonValueMem.{u} := by
  intro α v ξ u hξC hξα hnc hvu
  have hle : psiSelf ξ u ≤ ξ := psiSelf_le_self_of_not_canon hnc
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact H α v ξ u hξC hξα hnc hvu hlt
  · -- fixpoint: psiSelf ξ u = ξ, so the value IS the generator, already in C_v(α)
    rw [heq]; exact hξC

/-- **`alpha_step_residue` (re-sound).**  Lean analogue of ya-pss's
`alpha_step_residue` (necessity.thy:1139), the non-canonical-generator step of the
closure-rank induction.  GREEN modulo the genuine `AlphaStepResidue` (canonical
representative existence): fire the canonical witness `δ` via `CsetSelf_psi_closed`,
then transport `psi ξ u = psiSelf ξ u` (`IHa` at `ξ < α`).

**This REPLACES the prior vacuity proof**, which was UNSOUND — it rested on
`PsiValueAcanon`, now DISPROVEN (`PsiValueAcanon_is_false`).  The non-canonical
generator with argument in the closure DOES arise (`ξ = psiSelf Ω_1 0`), so the
step is not vacuous; it genuinely reproduces the value via the canonical rep. -/
theorem alpha_step_residue
    (α : Ordinal.{u}) (v : ℕ)
    (IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w)
    (ξ : Ordinal.{u}) (u : ℕ)
    (hξC : ξ ∈ CsetSelf (psiResSelf α) α v) (hξα : ξ < α)
    (hnc : ξ ∉ CsetSelf (psiResSelf ξ) ξ u) (hvu : v ≤ u) :
    psi.{u} ξ u ∈ CsetSelf (psiResSelf α) α v := by
  -- transport psi → psiSelf at ξ < α
  rw [IHa ξ hξα u]
  -- the genuine residual supplies the canonical witness δ.  We rest on the
  -- SHARPEST form `NoncanonValueMem` (bare value-membership = ya-pss
  -- `value_in_Cset_c_residue`); `alphaStepResidue_of_mem` recovers the canonical
  -- representative `δ` from it via `CsetSelf_witness_canonical` (1.4b).
  obtain ⟨δ, hδα, hδC, hδcanon, hval⟩ :=
    alphaStepResidue_of_mem
      (-- GENUINE Buchholz §1 core via the JOINT SIMULTANEOUS INDUCTION
       -- (`noncanonValueMem_joint`): reduced to the FOUR precise, model-verified
       -- (closure+5/+6) sub-lemmas — NOT a monolithic residual.
       noncanonValueMem_joint
         (subA_le := sorry) (subA_nm := sorry)
         (caseB := sorry) (caseSum := sorry)) α v ξ u hξC hξα hnc hvu
  -- fire δ: psiResSelf α δ u = psiSelf δ u = psiSelf ξ u ∈ C_v(α)
  have hconv : δ ∈ CsetSelf (psiResSelf α) δ u := by
    rwa [CsetSelf_param_eq (p := psiResSelf δ) (q := psiResSelf α)
          (fun ζ' uu hζ' => by
            rw [psiResSelf, psiResSelf, if_pos hζ', if_pos (lt_trans hζ' hδα)])] at hδcanon
  have hfire := CsetSelf_psi_closed hδC hδα u hconv
  rw [psiResSelf, if_pos hδα, hval] at hfire
  exact hfire

/-- **`alpha_step_residue` reduced to `AcanonLtValue` + the `v < w` membership**
(GREEN, parametric).  Makes the residual structure legible: `PsiValueAcanon` (the
sound, canonical form) follows from the canonical-rep core `AcanonLtValue` (PROVEN
below `ε(w)`; open for canonical `δ ≥ ε(w)`) and the membership residual `hmem`
(only the `v < w` part is non-trivial — `v = w` is `below_psiSelf`).  So the WHOLE
necessity face rests on these two, and the diagonal `v = w` is already fully
reduced to `AcanonLtValue` alone. -/
theorem alpha_step_residue_of_AcanonLtValue
    (hALV : AcanonLtValue.{u})
    (hmem : ∀ (ζ : Ordinal.{u}) (w v : ℕ), v ≤ w → ζ ∈ CsetSelf (psiResSelf ζ) ζ w →
       ζ < psiSelf ζ w → ζ ∈ CsetSelf (psiResSelf (psiSelf ζ w)) (psiSelf ζ w) v)
    (α : Ordinal.{u}) (v : ℕ)
    (ξ : Ordinal.{u}) (u : ℕ)
    (hξC : ξ ∈ CsetSelf (psiResSelf α) α v) (hξα : ξ < α)
    (hnc : ξ ∉ CsetSelf (psiResSelf ξ) ξ u) (hvu : v ≤ u) :
    psiSelf.{u} ξ u ∈ CsetSelf (psiResSelf α) α v :=
  absurd
    (acanon_sub_mono
      (CsetSelf_mem_lt_acanon (psiValueAcanon_of_AcanonLtValue hALV hmem) hξC hξα) hvu)
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

/-! ### ⚠⚠⚠ `CollapseResidue` (arbitrary `g`) IS FALSE — must be MAXO-restricted

**Critical finding (this session).**  `CollapseResidue` / `Nrm.psi_proj_notmem` as
stated for an ARBITRARY OT3-violator `g` is **FALSE**.  Verified on the ya-pss
ordinal model (`/tmp/probe_maxo.py`): the collapse `ψ_a(oV b') = ψ_a(oV g)` holds
for the **maxo** (olt-greatest) violator `278/278`, but for NON-maxo violators only
`87/972` (~9%).  Concrete counterexample (`/tmp/probe_ce.py`): `a = 0`,
`b' = D₁(D₂(D₂ 0))`, non-maxo violator `g = D₂ 0` (maxo = `D₂(D₂ 0)`):
`ψ_0(oV b') ≠ ψ_0(oV g)`, so `ψ_0(oV b') ∈ C_0(oV g)` (membership) — the
non-membership `CollapseResidue` FAILS there.

Why: by `psi_proj_mem_imp_strict`, membership ⟺ `ψ_a(oV b') < ψ_a(oV g)` strict; a
non-maxo violator `oV g < oV maxo` leaves a larger violator above, so `ψ_a` has not
yet collapsed across the full plateau — `ψ_a(oV b') < ψ_a(oV g)` strict (membership).
Only the maxo violator sits at the plateau top where `ψ_a(oV b') = ψ_a(oV maxo)`.

**This does NOT break `Nrm.psi_proj`**: `psi_proj_of_notmem` only ever uses the
residual at `g = maxo (Glist a b).filter (¬ olt · b)` — see its proof.  So the
GENUINE residual is the MAXO-restricted `CollapseResidueMaxo` below, which is TRUE
(278/278).  `Reduction.lean`'s nrm route should consume `CollapseResidueMaxo`, not
the false general `CollapseResidue` (which is fed to the general
`psi_proj_of_notmem` whose premise is thereby unsatisfiable).  -/

/-- **The MAXO-restricted collapse residue (the TRUE one).**  Only the olt-greatest
OT3-violator `g` (`g ∈ Gterm a b'`, `¬ olt g b'`, and `g` is `ole`-above every
other violator) — exactly the `g = maxo …` that `proj` selects.  Empirically TRUE
(278/278); the general `CollapseResidue` is FALSE (non-maxo violators). -/
def CollapseResidueMaxo.{u} : Prop :=
  ∀ (a : ℕ) (b' g : Three), wf3 b' → g ∈ Gterm a b' → ¬ olt g b' →
    (∀ x ∈ Gterm a b', ¬ olt x b' → ole x g) →
    psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a

/-! ### COLLAPSE-face analysis (omitted form, no self-bridge) — the genuine reduction

`CollapseResidue` (= `Nrm.psi_proj_notmem`) is the COLLAPSE face.  Two clean facts
(both PROVEN here, sorryAx-free, omitted-form only):

* `oV_le_of_bad` — an OT3-violator `g` (`g ∈ Gterm a b'`, `¬ olt g b'`) has
  `oV b' ≤ oV g` (Buchholz B1, `bad_imp_oV_ge`);
* `collapse_iff_eq` — `CollapseResidue` (per step) ⟺ the **collapse equality**
  `psi (oV b') a = psi (oV g) a` (via `psi_notMem_iff_eq`, since `oV b' ≤ oV g`);
* `psi_proj_mem_imp_strict` — *membership* `psi (oV b') a ∈ C_a(oV g)` ⟹
  `psi (oV b') a < psi (oV g) a` STRICT (M1 `psi_form_of_mem` + `psi_strict_mono_mem`).

So `CollapseResidue` ⟺ `psi (oV b') a = psi (oV g) a`, and its DUAL (membership)
is the strict `<` — exactly the dual of the non-collapse lever `oV_nf_arg_lt`.

**FINDING (this session): the collapse face is ENTANGLED with necessity (B2).**
Per ya-pss `nrm.thy` (`psi_proj_nonmem`, `oV_noncanon_of_bad`), the membership
`psi (oV b') a ∈ C_a(oV g)` is, by M1, a generator `psi ξ a` with `ξ < oV g`; the
case `ξ = oV b'` forces `oV b'` CANONICAL, contradicting **B2** (`oV b'`
non-canonical — TRUE because an OT3-violator with `oV g ≥ oV b'` violates Buchholz
1.9 necessity at the bound `oV b'`).  B2 needs the **necessity residual**
(`NEC_of_argExtract`'s `argExt`/`SUFF`, parametric in `Otembed`/`Buchholz17`) — so
the collapse face does NOT bypass necessity; it consumes a necessity INSTANCE (B2)
plus the larger-witness collapse (`ξ = oV(proj a b') ≥ oV g`, circular with
`psi_proj`).  Sub-`ε` corroboration: if `oV b' < ε(a)` then `oV b'` is canonical
(`mem_Cself_lvl`), so by necessity it has NO violator with larger value; hence an
OT3-violator forces `oV b' ≥ ε(a)` (the collapse region) — the dual of the lever's
"sub-ε ⟹ strict" (which would make `CollapseResidue` FALSE if a sub-ε strict
violator existed). -/

/-- **B1 (`bad_imp_oV_ge`)**: an OT3-violator has value `≥ oV b'`. -/
theorem oV_le_of_bad {a : ℕ} {b' g : Three}
    (wb' : wf3 b') (hg : g ∈ Gterm a b') (hv : ¬ olt g b') : oV.{u} b' ≤ oV g := by
  have wg : wf3 g := wf3_Gterm wb' hg
  rcases olt_total b' g with h | rfl | h
  · exact (oV_order_pres wb' wg h).le
  · exact le_rfl
  · exact absurd h hv

/-- **`CollapseResidue` (per step) ⟺ the collapse equality** `ψ_a(oV b') = ψ_a(oV g)`. -/
theorem collapse_iff_eq {a : ℕ} {b' g : Three}
    (wb' : wf3 b') (hg : g ∈ Gterm a b') (hv : ¬ olt g b') :
    psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a ↔ psi.{u} (oV b') a = psi (oV g) a :=
  psi_notMem_iff_eq (oV_le_of_bad wb' hg hv)

/-- **Membership ⟹ strict** (the DUAL of collapse): if `ψ_a(oV b') ∈ C_a(oV g)`
then `ψ_a(oV b') < ψ_a(oV g)`.  M1 extracts a generator `ψ_a(ξ)`, `ξ < oV g` in
`C_a(oV g)`, with value `ψ_a(oV b')`; `psi_strict_mono_mem` gives the strict gap. -/
theorem psi_proj_mem_imp_strict {a : ℕ} {b' g : Three}
    (hmem : psi.{u} (oV b') a ∈ Cset (psiRes (oV g)) (oV g) a) :
    psi.{u} (oV b') a < psi (oV g) a := by
  have hap : Ordinal.IsPrincipal (· + ·) (psi.{u} (oV b') a) :=
    fun {x y} hx hy => (psi_addprinc (oV b') a).2 x y hx hy
  obtain ⟨ξ, hξC, hξlt, hξeq⟩ :=
    psi_form_of_mem hap (Om_le_psi (oV b') a) (psi_lt_Om_succ (oV b') a) hmem
  exact hξeq ▸ psi_strict_mono_mem hξC hξlt

/-! ### Why the JOINT necessity induction cannot carry the collapse face — the
    polarity obstruction (kernel-checked record of the joint-induction attempt).

The necessity face is proven (mod 4 sub-lemmas) by the joint simultaneous induction
`noncanonValueMem_joint : NoncanonValueMem`, whose conclusion is a **membership**
`psiSelf ξ u ∈ CsetSelf (psiResSelf α) α v` (a non-canonical generator value lands
in the closure).  The collapse face (`CollapseResidueMaxo`) needs the **opposite
polarity** — a *non-membership* `ψ_a(oV b') ∉ C_a(oV g)`.  A statement whose
conclusion is a membership cannot prove a non-membership goal (its contrapositive
only negates hypotheses), so `NoncanonValueMem` / the joint induction is
structurally unable to discharge the collapse face.  This is recorded once, in
checked code, so the joint-induction route is not re-attempted for the collapse.

`crm_via_witness_strict` below shows the second half of the obstruction: the M1
witness `ξ` of a hypothetical membership *already* certifies the strict gap
`ψ_a(oV b') < ψ_a(oV g)` (= the negation of collapse) **with no use of `ξ`'s
canonicity** — `psi_strict_mono_mem` needs only `ξ ∈ C_a(oV g)` and `ξ < oV g`,
both supplied by M1.  Hence the canonical/non-canonical split of `ξ` that powers
the necessity kernel `argExt_of_kernel` (Buchholz17.lean) gives NO leverage here:
there is no `ξ`-canonicity hypothesis left to consume.  The only remaining content
is the **minimality of `oV g`** as a value-realizer — i.e. `oV g ≤ ξ` is forced —
which is exactly `oV g = oV(proj a b')` = `psi_proj`, the irreducible circularity
(ya-pss `psi_proj_nonmem`, nrm.thy:351: the larger-witness `ξ = oV(proj a b) ≥ oV m`
whose value-identity is `psi_proj` itself). -/

/-- **The collapse face IS exactly the bare equality** — no witness structure
survives.  For the maxo data (`oV b' ≤ oV g` by B1), the non-membership
`ψ_a(oV b') ∉ C_a(oV g)` holds **iff** `¬ (ψ_a(oV b') < ψ_a(oV g))`, iff the
collapse equality.  This packages `psi_proj_mem_imp_strict` (the only direction
with content) with `psi_mono_arg`: every hypothetical M1 witness already gives the
strict gap unconditionally, so the joint-induction witness-canonicity split is
vacuous and the face reduces to the bare equality (= `psi_proj`).  Sorry-free. -/
theorem crm_via_witness_strict {a : ℕ} {b' g : Three}
    (hle : oV.{u} b' ≤ oV g) :
    (psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a) ↔
      psi.{u} (oV b') a = psi (oV g) a := by
  refine ⟨psi_eq_of_notMem hle, fun he hmem => ?_⟩
  exact absurd (psi_proj_mem_imp_strict hmem) (by rw [he]; exact lt_irrefl _)

/-! ### TERM-NEC collapse analysis (the SOUND route) — and the precise irreducible
    circularity (matching ya-pss `psi_proj_nonmem`).

`CollapseResidueMaxo` is TRUE (re-verified at closure+6 via the term value model
`nrm (P a b' Z) = nrm (P a g Z)`: 328/328 instances collapse, 0 failures).  The
GENUINE structure of the maxo OT3-violator `g` of a `wf3 b'` (audit
`audit_collapse_face.py`, closure+5/+6, all 328/328):

* **g is the CANONICAL representative**: `proj a g = g` (g is a-reduced), so
  `oV g ∈ C_a(oV g)` (g is `a`-canonical, by `Ccond_of_lt`).
* **g IS the proj-target of b'**: `proj a b' = g`, so `oV g = oV (proj a b')` and
  the collapse `ψ_a(oV b') = ψ_a(oV g)` is EXACTLY `psi_proj` at one step.
* **`oV b'` is NON-canonical** (B2, `noncanon_of_bad_of_SUFF` below) — it has the
  violator `g` with `oV g ≥ oV b'`, defeating `wf3`-necessity at bound `oV b'`.

**The irreducible circularity (PRECISELY, in code).**  The two faces are
`collapse_iff_eq`-equivalent (`ψ_a(oV b') ∉ C_a(oV g) ⟺ ψ_a(oV b') = ψ_a(oV g)`),
and the dual `psi_proj_mem_imp_strict` gives `membership ⟹ ψ_a(oV b') < ψ_a(oV g)`
STRICT.  So the membership-route disproof would need the equality it is proving.
The structural route fails too: `psi_form_of_mem` (M1) extracts a witness `ξ < oV g`
with `ψ_a(ξ) = ψ_a(oV b')`, and the only non-circular finish is `ξ = oV (proj a b')
= oV g` — but `ξ = oV (proj a b')` is `ψ_a(oV b') = ψ_a(oV (proj a b'))`, i.e.
`psi_proj` itself.  And `Otembed.collapse_le` (all-gap-points non-canonical) is the
WRONG tool: the gap `[oV b', oV g)` crosses canonical `Ω_k` (Ω-crossing,
271/271 in-gap instances at closure+6), so `IntervalNoncanon` is FALSE.  This is
EXACTLY ya-pss's open `psi_proj_nonmem` (the larger-witness `ξ = oV(proj a b') ≥
oV g` circularity), which stays a `sorry` there even with `term_nec` green.

So the collapse face genuinely rests on `SUFF` (Buchholz 1.9 sufficiency, the
necessity residual — open) PLUS the irreducible witness-identity (= `psi_proj`).
The SOUND pieces below are sorry-free; the irreducible step is honestly left. -/

/-- **B2 — `oV b'` is `a`-non-canonical**, from `wf3`-necessity (`NEC_of_suff`,
modulo `SUFF`).  If `oV b'` were `a`-canonical, necessity would force every
`x ∈ Gterm a b'` to have `oV x < oV b'`; but the violator `g` has
`oV b' ≤ oV g` (`oV_le_of_bad`) — contradiction.  (sorry-free given `SUFF`.) -/
theorem noncanon_of_bad_of_SUFF
    (SUFF : ∀ (v a : ℕ) (β α : Ordinal.{u}), v ≤ a →
      β ∈ Cset (psiRes β) β a → β < α → β ∈ Cset (psiRes α) α v)
    {a : ℕ} {b' g : Three} (wb' : wf3 b') (hg : g ∈ Gterm a b') (hv : ¬ olt g b') :
    oV.{u} b' ∉ Cset (psiRes (oV b')) (oV b') a := by
  intro hcanon
  have hgle : oV.{u} g < oV b' := NEC_of_suff SUFF wb' (v := a) (α := oV b') hcanon g hg
  exact absurd hgle (not_lt.2 (oV_le_of_bad wb' hg hv))

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
NB: `CollapseResidue` (arbitrary `g`) is FALSE (see the maxo correction above); this
theorem is a valid implication but its hypothesis is unsatisfiable.  Use
`oV_nrm_eq_of_collapseResidueMaxo` (on the TRUE `CollapseResidueMaxo`) instead. -/
theorem oV_nrm_eq_of_collapseResidue (CR : CollapseResidue.{u}) :
    ∀ t : Three, oV.{u} (nrm t) = oV t :=
  oV_nrm_of_psi_proj (fun a b wb => psi_proj_of_collapseResidue CR a b wb)

/-! ### CORRECTED chain on the TRUE residual `CollapseResidueMaxo` -/

/-- `ole` transitivity (local helper for `maxo_ge`). -/
theorem ole_trans' {x y z : Three} (hxy : ole x y) (hyz : ole y z) : ole x z := by
  rcases hxy with h | rfl
  · exact Or.inl (olt_ole_trans h hyz)
  · exact hyz

/-- **`maxo` is the `ole`-maximum**: every element of `x :: ys` is `ole (maxo x ys)`. -/
theorem maxo_ge : ∀ (ys : List Three) (x y : Three),
    y ∈ x :: ys → ole y (maxo x ys) := by
  intro ys
  induction ys with
  | nil =>
    intro x y hy; rw [maxo_nil]
    rcases List.mem_cons.1 hy with heq | hy2
    · exact Or.inr heq
    · simp at hy2
  | cons z zs ih =>
    intro x y hy; rw [maxo_cons]
    by_cases hxz : olt x z
    · rw [if_pos hxz]
      rcases List.mem_cons.1 hy with heq | hy2
      · have : ole y z := Or.inl (heq ▸ hxz)
        exact ole_trans' this (ih z z List.mem_cons_self)
      · exact ih z y hy2
    · rw [if_neg hxz]
      have hzx : ole z x := by
        rcases olt_total z x with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hxz
      rcases List.mem_cons.1 hy with heq | hy2
      · exact heq ▸ ih x x List.mem_cons_self
      · rcases List.mem_cons.1 hy2 with heq2 | hy3
        · have : ole y x := heq2 ▸ hzx
          exact ole_trans' this (ih x x List.mem_cons_self)
        · exact ih x y (List.mem_cons_of_mem _ hy3)

/-- **`proj` preserves `ψ_a`, from the TRUE maxo-restricted residual** (re-derived,
mirroring `Nrm.psi_proj_of_notmem` but feeding `CollapseResidueMaxo` only at the
`maxo` violator that `proj` selects — supplying its `ole`-maximality via `maxo_ge`).
This REPLACES the false-hypothesis `psi_proj_of_collapseResidue`. -/
theorem psi_proj_of_collapseResidueMaxo (CRM : CollapseResidueMaxo.{u})
    (a : ℕ) (b : Three) (wb : wf3 b) :
    psi.{u} (oV (proj a b)) a = psi (oV b) a := by
  generalize hs : tsize b = n
  induction n using Nat.strong_induction_on generalizing b with
  | _ n IH =>
    subst hs
    by_cases h : (Glist a b).filter (fun g => ¬ olt g b) = []
    · rw [proj_id h]
    · rw [proj_rec h]
      have hin := maxo_hdtl_in h
      set g := maxo ((Glist a b).filter (fun g => ¬ olt g b)).headI
                    ((Glist a b).filter (fun g => ¬ olt g b)).tail with hg
      have hgmem : g ∈ Gterm a b := mem_Glist.1 (List.mem_of_mem_filter hin)
      have hgviol : ¬ olt g b := by
        have := List.of_mem_filter hin; simpa using this
      have wg : wf3 g := wf3_Gterm wb hgmem
      have hsz : tsize g < tsize b := Gterm_tsize hgmem
      have ihg : psi.{u} (oV (proj a g)) a = psi (oV g) a := IH (tsize g) hsz g wg rfl
      have hle : oV.{u} b ≤ oV g := by
        rcases olt_total b g with hbg | hbe | hgb
        · exact le_of_lt (oV_order_pres wb wg hbg)
        · rw [hbe]
        · exact absurd hgb hgviol
      have hmax : ∀ x ∈ Gterm a b, ¬ olt x b → ole x g := by
        intro x hxG hxv
        have hxf : x ∈ (Glist a b).filter (fun g => ¬ olt g b) :=
          List.mem_filter.2 ⟨mem_Glist.2 hxG, by simpa using hxv⟩
        have hlist : (Glist a b).filter (fun g => ¬ olt g b)
                   = ((Glist a b).filter (fun g => ¬ olt g b)).headI
                     :: ((Glist a b).filter (fun g => ¬ olt g b)).tail := by
          cases hc : (Glist a b).filter (fun g => ¬ olt g b) with
          | nil => exact absurd hc h
          | cons hd tl => simp [List.headI, List.tail]
        rw [hlist] at hxf
        exact hg ▸ maxo_ge _ _ x hxf
      have hstep : psi.{u} (oV g) a = psi (oV b) a :=
        (psi_eq_of_notMem hle (CRM a b g wb hgmem hgviol hmax)).symm
      rw [ihg]; exact hstep

/-- **END-TO-END (CORRECTED): `nrm` preserves the ordinal value, modulo the TRUE
`CollapseResidueMaxo`.**  `oV (nrm t) = oV t`, via `psi_proj_of_collapseResidueMaxo`
+ `oV_nrm_of_psi_proj`.  Rests on the maxo-restricted residual (TRUE, 278/278),
NOT the false general `CollapseResidue`.  Axiom profile: `[propext,
Classical.choice, Quot.sound]` — NO `sorryAx`. -/
theorem oV_nrm_eq_of_collapseResidueMaxo (CRM : CollapseResidueMaxo.{u}) :
    ∀ t : Three, oV.{u} (nrm t) = oV t :=
  oV_nrm_of_psi_proj (fun a b wb => psi_proj_of_collapseResidueMaxo CRM a b wb)

/-! ## COLLAPSE-FACE RESOLUTION — `IntervalNoncanon` is DEAD (Ω-crossing); the
    TRUE route is `ProjFixesNrm` (proj is identity on `nrm`-images).

**`IntervalNoncanon` is FALSE — DEAD ROUTE (do not use).**  The closure-rank gate
(`collapse_le` needs *every* gap point non-canonical) was a false proxy: the maxo
violator `g` has lead level `> a` (e.g. `g = D_2(…)`), so `oV g ≥ Ω_2` while
`oV b' = ψ_a(…) < Ω_{a+1}`.  Hence the gap `[oV b', oV g)` CROSSES `Ω_k`
(`a < k ≤ lead g`), and `Ω_k = ψ_k(0) ∈ C_a(Ω_k)` is `a`-CANONICAL inside the gap
(confirmed at closure+5/+6: 163/208 wf3-instances have an in-gap `Ω_k`).  So
"every `γ ∈ [oV b', oV g)` is non-canonical" is FALSE.  `collapseResidueMaxo_of_-
intervalNoncanon` is a valid implication with an UNSATISFIABLE hypothesis — a dead
end, NOT progress.  Likewise `CollapseResidueMaxo` over **all** `wf3 b'` is itself
suspect: the firing instances (cross-level args) appear to break the collapse.

**THE TRUE FIX (proven below): `proj` never fires on `nrm`-images.**  The nrm
value-chain (`Nrm.oV_nrm_of_psi_proj`) only ever calls `psi_proj` at the argument
`nrm b` — an `nrm`-image.  Empirically (closure+6, `audit`): `proj a (nrm t) =
nrm t` for ALL 2165/2165 proj-arg positions; `nrm` is idempotent and lands in OT.
So on the domain that the route actually uses, `proj` is the IDENTITY and the
collapse step is never invoked.  The genuine residual is therefore the clean,
TRUE statement `ProjFixesNrm` (= "nrm fully normalizes / is proj-fixed"), which
makes `psi_proj` at `nrm`-images hold by `rfl` after rewriting `proj a (nrm b) =
nrm b` — NO collapse equality, NO interval, NO `CollapseResidueMaxo`. -/

/-- **`ProjFixesNrm` — the TRUE collapse-face residual.**  `proj` is the identity on
every `nrm`-image: `proj a (nrm t) = nrm t`.  Equivalently, `nrm` fully normalizes
(no level-`a` OT3-violator survives in a `nrm`-image's proj-arg positions).
Empirically TRUE at closure+6 (2165/2165 proj-arg positions fixed); replaces the
FALSE `IntervalNoncanon`/`CollapseResidueMaxo`-over-all-`wf3` route. -/
def ProjFixesNrm : Prop := ∀ (a : ℕ) (t : Three), proj a (nrm t) = nrm t

/-- **Sharper `oV_nrm_of_psi_proj`: needs `psi_proj` only at `nrm`-images.**  The
nrm value-chain calls `psi_proj` solely at the argument `nrm b`; this version
mirrors `Nrm.oV_nrm_of_psi_proj` but quantifies the hypothesis only over
`nrm`-images, which is the honest domain. -/
theorem oV_nrm_of_psi_proj_onNrm
    (psi_proj_nrm : ∀ (a : ℕ) (b : Three),
      psi.{0} (oV (proj a (nrm b))) a = psi (oV (nrm b)) a) :
    ∀ t : Three, oV.{0} (nrm t) = oV t := by
  intro t
  induction t with
  | Z => rfl
  | P a b c ihb ihc =>
    rw [nrm_P, oV_ins (proj_wf3 (wf3_nrm b)) (wf3_nrm c) (proj_G a (nrm b)),
        oV_P, oV_P, psi_proj_nrm a b, ihb, ihc]

/-- **`nrm` preserves the ordinal value, from `ProjFixesNrm`** (GREEN, sorry-free).
Since `proj a (nrm b) = nrm b`, both sides of the per-step `psi_proj` are equal by
`rfl` — the collapse is never invoked.  This REPLACES `oV_nrm_eq_of_collapse-
ResidueMaxo` (which rested on the suspect all-`wf3` collapse). -/
theorem oV_nrm_eq_of_projFixesNrm (PF : ProjFixesNrm) :
    ∀ t : Three, oV.{0} (nrm t) = oV t := by
  apply oV_nrm_of_psi_proj_onNrm
  intro a b
  rw [PF a b]

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
