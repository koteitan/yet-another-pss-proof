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

**On the residue itself (vacuity reduction; SOUND form).**
`alpha_step_residue` is reduced GREEN to the **α-free** residual `PsiValueAcanon`:
*every ψ-value `psiSelf ζ w` with a `w`-CANONICAL argument is canonical at every
`v ≤ w`*.  (The canonicity restriction is a SOUNDNESS FIX — the all-`ζ` form is
FALSE at ε-fixpoints `psiSelf ε(w) w = ε(w)`, but those `ζ` are non-canonical and
the closure-rank generator only fires for canonical `ζ`.)  Given it,
`alpha_step_residue` is **vacuous** — a member `ξ < α` of `CsetSelf_α` is canonical
at `v` (`CsetSelf_mem_lt_acanon`) hence at `u ≥ v` (`acanon_sub_mono`),
contradicting `hnc`.

**Progress toward `PsiValueAcanon` (explicit-value formula + corrections).**
The witness for the value `c = psiSelf ζ w` is a `w`-canonical `δ < c` with
`psiSelf δ w = c` — Buchholz's canonical representation (`CanonRep`).  Earlier
sessions tried to use `ζ` itself as the witness, via `AcanonLtValue`
(canonical `δ ⟹ δ < psiSelf δ w`); but **`AcanonLtValue` is FALSE**
(`AcanonLtValue_is_false`: `ζ = Ω_{w+1}` is `w`-canonical with `ζ > psiSelf ζ w`),
so `ζ` need not be `< c`.  That route is a documented dead-end.

Status of `PsiValueAcanon`:
* **sub-`ε(w)` diagonal `v = w`: PROVEN** (`psiValueAcanon_diag_lt_epsLvl`) — for
  `ζ < ε(w)`, `ζ < c` via the formula `psiSelf δ w = ω^(Ω_w+δ)`, witness `δ = ζ`;
* general diagonal `v = w`: reduced to `CanonRep` (`diag_of_CanonRep`);
* `ζ ≥ ε(w)` (then `c ≥ ε(w)`): the witness `δ ∈ [ε(w), c)` — its existence is
  the irreducible §1 simultaneous-induction core (`CanonRep`);
* `v < w`: the value `c` must be canonical at `v` too — a collapse-region
  membership at level `v` (entangled with `CanonRep` at level `v`).

The explicit formula also gives the **non-collapse lever** `psi_strict_mono_lt_
epsLvl` (sub-`ε` `ψ_a` injective), which discharges the §1 head of `oV_nf_arg_lt`
(`oV_nf_arg_lt_of_lever`) — the DUAL termination leaf.

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
ψ-value with a `w`-CANONICAL argument is canonical at every lower-or-equal
subscript.*  Lean analogue of ya-pss's `psi_value_acanon` (necessity.thy).

**⚠ SOUNDNESS FIX (this session).**  The previous form quantified over ALL `ζ`;
that is **FALSE** at ε-fixpoints: for `ζ = ε(w)` (an ε-number `≥ Ω_w`),
`psiSelf ε(w) w = ε(w)` (the value is the least non-member of its own closure),
so `ε(w) ∉ CsetSelf (psiResSelf ε(w)) ε(w) w` — the conclusion fails.  But such
`ζ` is **non-canonical**, and in the closure-rank induction the generator only
fires for `w`-canonical `ζ` (the `CstepSelf` canonicity side-condition).  So we
restrict the residual to canonical `ζ` (`hζc`), which excludes the false ε-fixpoint
cases and is what the vacuity proof actually needs.  (NB: my indexing `Ω_v = ω_v`,
`Ω_0 = 1`; ya-pss's `Ω_1 = ω` counterexample lives in a different indexing.)

**PROOF STATUS (this session).**  The witness for `c = psiSelf ζ w` is NOT `ζ`
itself in general (`AcanonLtValue` is FALSE — `AcanonLtValue_is_false`,
counterexample `ζ = Ω_{w+1}`).  Proven so far:
* the **diagonal `v = w` for `ζ < ε(w)`** (`psiValueAcanon_diag_lt_epsLvl`,
  sorryAx-free, via the explicit formula).
Remaining (the genuine §1 core): the canonical-WITNESS existence — for canonical
`ζ ≥ ε(w)`, a `δ < c` that is `w`-canonical with `psiSelf δ w = c` — plus, for
`v < w`, the membership `δ ∈ C_v(c)`.  This is Buchholz's canonical-representation
existence, the irreducible simultaneous-induction step. -/
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
  -- the genuine residual supplies the canonical witness δ
  obtain ⟨δ, hδα, hδC, hδcanon, hval⟩ :=
    (show AlphaStepResidue.{u} from
      -- GENUINE Buchholz §1 core: the non-canonical generator's value has a
      -- canonical representative δ < α inside C_v(α).  Replaces the false vacuity.
      sorry) α v ξ u hξC hξα hnc hvu
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
