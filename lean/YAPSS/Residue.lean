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

**On the residue itself (this session).**  `alpha_step_residue` is no longer a
bare `sorry`: it is reduced GREEN to a strictly sharper residual
`CanonWitnessResidue` (canonical-witness existence for `psiSelf ξ u` inside the
closure).  The value-identity, the `< α` bound, and the `CsetSelf_psi_closed`
reproduction step are all discharged; the irreducible remainder is *(witness
canonical) ∧ (witness ∈ CsetSelf_α)*.  See the `CanonWitnessResidue` docstring for
the precise wall (the least-argument witness fails canonicity exactly at
ψ-fixpoint values; `CsetSelf` non-downward-closure blocks the membership).  This
is the genuine multi-session §1 core, still open on both the psiSelf route (here)
and ya-pss's `Cset_c` route — now isolated to the *same* residual on both sides.

**On `psi_proj_notmem`.**  ya-pss keeps the §1 core as *two* `sorry`s: the
necessity-side `alpha_step_residue` (necessity.thy:1139) and the collapse-side
`psi_proj_nonmem` (nrm.thy:186), explicitly the "same §1 core" but not reduced to
one another.  We mirror this with two residues: the closure face
`CanonWitnessResidue` (⟶ `alpha_step_residue`, the only `sorry`) and the collapse
face `CollapseResidue`.  They are genuinely independent in the formalization (see
the independence note at file end); we keep both.

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

**Status of the attack (psiSelf route).**  `alpha_step_residue` is reduced here,
GREEN, to a strictly sharper residual `CanonWitnessResidue` — the **existence of a
canonical generator witness** for the value `psiSelf ξ u` inside the closure.
Three of the four witness obligations are discharged unconditionally:

* the value identity `psiSelf δ u = psiSelf ξ u` (the least-argument witness,
  `leastWitness_val`);
* `δ < α` (the least witness is `≤ ξ < α`, `leastWitness_lt`);
* the reproduction step `CsetSelf_psi_closed` once a canonical δ ∈ closure is in
  hand (`alpha_step_of_canonWitness`).

The IRREDUCIBLE residual is the conjunction *(δ is canonical) ∧ (δ ∈ CsetSelf_α)*
for the witness.  The precise wall (documented on `CanonWitnessResidue`): the
least-argument witness is **NOT** always canonical — it fails exactly when the
value `c = psiSelf ξ u` is a ψ-fixpoint (`psiSelf c u = c`), which can occur for a
non-canonical ξ in c's plateau; and even a canonical δ need not be downward-
reachable inside `CsetSelf_α`.  This matches ya-pss's report that
`alpha_step_residue` is the multi-session §1 core (necessity.thy:1139, still a
`sorry` on its `Cset_c` route).  The two routes now isolate the **same** residual
(canonical-witness existence in the closure), giving an independent cross-check. -/

/-- **Non-canonical argument collapses at-or-below itself.**  If `ξ` is
non-canonical at `u` (`ξ ∉ CsetSelf (psiResSelf ξ) ξ u`) then `psiSelf ξ u ≤ ξ`.
(Contrapositive of `below_psiSelf_mem_CsetSelf` at bound `ξ`.)  Proven, no IH. -/
theorem psiSelf_le_self_of_not_canon {ξ : Ordinal.{u}} {u : ℕ}
    (hnc : ξ ∉ CsetSelf (psiResSelf ξ) ξ u) : psiSelf ξ u ≤ ξ := by
  by_contra h; push Not at h; exact hnc (below_psiSelf_mem_CsetSelf h)

/-- The least argument realizing the value `psiSelf ξ u`.  (The plateau bottom;
its value is `psiSelf ξ u` and it is `≤ ξ`.) -/
noncomputable def leastWitness (ξ : Ordinal.{u}) (u : ℕ) : Ordinal.{u} :=
  sInf {d : Ordinal | psiSelf d u = psiSelf ξ u}

theorem leastWitness_val (ξ : Ordinal.{u}) (u : ℕ) :
    psiSelf (leastWitness ξ u) u = psiSelf ξ u :=
  csInf_mem (s := {d : Ordinal | psiSelf d u = psiSelf ξ u}) ⟨ξ, rfl⟩

theorem leastWitness_le (ξ : Ordinal.{u}) (u : ℕ) : leastWitness ξ u ≤ ξ :=
  csInf_le' (s := {d : Ordinal | psiSelf d u = psiSelf ξ u}) rfl

theorem leastWitness_lt {α ξ : Ordinal.{u}} (u : ℕ) (hξα : ξ < α) :
    leastWitness ξ u < α :=
  lt_of_le_of_lt (leastWitness_le ξ u) hξα

/-- **The sharpened residual (the psiSelf-route Buchholz §1 core).**  The
existence of a *canonical generator witness* `δ` for the value `psiSelf ξ u`,
inside the closure `CsetSelf_α` and below `α`.  This is strictly weaker than the
original `alpha_step_residue` (it discharges the reproduction step and the value /
`< α` obligations; see `alpha_step_of_canonWitness`).

**Where the IH must enter, and the wall.**  The natural witness is
`leastWitness ξ u` (value-correct and `< α` for free).  Its two open obligations:
1. *canonicity* `δ ∈ CsetSelf (psiResSelf δ) δ u` — FALSE for the least witness
   exactly when `c = psiSelf ξ u` is a ψ-fixpoint (`psiSelf c u = c`); then the
   least witness is `c` itself and is non-canonical;
2. *membership* `δ ∈ CsetSelf (psiResSelf α) α v` — not derivable from
   `δ ≤ ξ ∈ CsetSelf_α` since `CsetSelf` is not downward-closed.
The α-IH `IHa : ∀ β < α, ∀ w, psi β w = psiSelf β w` is the intended lever for (2)
(canonicity of the *full* closure below α), but a Lean-native proof that the
canonical witness lands in `CsetSelf_α` is the genuine irreducible content. -/
def CanonWitnessResidue.{u} (α : Ordinal.{u}) (v : ℕ) (ξ : Ordinal.{u}) (u' : ℕ) : Prop :=
  ∃ δ, δ < α ∧ δ ∈ CsetSelf (psiResSelf α) α v ∧
    δ ∈ CsetSelf (psiResSelf δ) δ u' ∧ psiSelf δ u' = psiSelf ξ u'

/-- **`alpha_step_residue` reduced to the canonical-witness residual.**  GREEN:
given a canonical witness `δ` in the closure with the right value, the generator
value `psi ξ u = psiSelf ξ u` (`IHa` at `ξ < α`) is reproduced by
`CsetSelf_psi_closed` at `δ`.  All of `hξC`, `hnc`, `hvu` are consumed only inside
the (open) construction of the witness — here the witness does all the work. -/
theorem alpha_step_of_canonWitness
    (α : Ordinal.{u}) (v : ℕ)
    (IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w)
    (ξ : Ordinal.{u}) (u : ℕ) (hξα : ξ < α)
    (CWR : CanonWitnessResidue α v ξ u) :
    psi.{u} ξ u ∈ CsetSelf (psiResSelf α) α v := by
  rw [IHa ξ hξα u]
  obtain ⟨δ, hδα, hδC, hδcanon, hval⟩ := CWR
  have hconv : δ ∈ CsetSelf (psiResSelf α) δ u := by
    rwa [CsetSelf_param_eq (p := psiResSelf δ) (q := psiResSelf α)
          (fun ζ uu hζ => by
            rw [psiResSelf, psiResSelf, if_pos hζ, if_pos (lt_trans hζ hδα)])] at hδcanon
  have hc := CsetSelf_psi_closed hδC hδα u hconv
  rw [psiResSelf, if_pos hδα] at hc
  rwa [hval] at hc

/-- **`alpha_step_residue` (the residue; now reduced to `CanonWitnessResidue`).**
Lean analogue of ya-pss's `alpha_step_residue` (necessity.thy:1139), the
non-canonical-generator step of the closure-rank induction carrying the α-IH.
The single remaining `sorry` is the canonical-witness existence
`CanonWitnessResidue` (strictly sharper than the original statement — see the
docstring there for the precise wall). -/
theorem alpha_step_residue
    (α : Ordinal.{u}) (v : ℕ)
    (IHa : ∀ β, β < α → ∀ w, psi.{u} β w = psiSelf β w)
    (ξ : Ordinal.{u}) (u : ℕ)
    (hξC : ξ ∈ CsetSelf (psiResSelf α) α v) (hξα : ξ < α)
    (hnc : ξ ∉ CsetSelf (psiResSelf ξ) ξ u) (hvu : v ≤ u) :
    psi.{u} ξ u ∈ CsetSelf (psiResSelf α) α v :=
  alpha_step_of_canonWitness α v IHa ξ u hξα
    (show CanonWitnessResidue α v ξ u from
      -- The sharpened Buchholz §1 core: canonical-witness existence.  See the
      -- `CanonWitnessResidue` docstring for the precise (fixpoint / non-downward-
      -- closure) wall.  Still open on BOTH the psiSelf (here) and Cset_c (ya-pss)
      -- routes — the genuine multi-session simultaneous-induction core.
      sorry)

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

/-! ## Are `CollapseResidue` and `CanonWitnessResidue` independent? — they are.

**Finding: the two residues are genuinely independent in the formalization; we
keep both (matching ya-pss), with a precise reason.**

`CanonWitnessResidue α v ξ u` is a *closure-reproduction / existence* statement:
the value `psiSelf ξ u` has a **canonical generator witness** `δ < α` inside
`CsetSelf_α`.  Via the spine it yields `Cset = CsetSelf` and hence `psi = psiSelf`
(`psi_eq_psiSelf`) — the **necessity / closure** content.

`CollapseResidue` is a *value-equality (collapse)* statement: by
`psi_notMem_iff_eq` (with `oV b' ≤ oV g`) it is exactly
`psi (oV b') a = psi (oV g) a` for the OT3-violator pair — the **collapse**
content (the gap `[oV b', oV g)` carries no new ψ-value).  (Equivalently in self
form `CollapseResidueSelf`, `collapseResidue_iff_self`.)

These do not reduce to one another:

* `CollapseResidue ⇏` from the closure structure.  Even granting `Cset = CsetSelf`
  (i.e. `CanonWitnessResidue` everywhere), the membership
  `psi (oV b') a ∈ Cset (psiRes (oV g)) (oV g) a` only yields `oV b' < oV g` via
  `psi_arg_lt_of_mem` — which is *consistent* with `oV b' ≤ oV g`, NOT a
  contradiction.  So the closure/witness content cannot force the collapse
  equality; that equality is an extra fact about the specific gap.
* This mirrors ya-pss exactly: its `psi_proj_nonmem` (nrm.thy:186, the collapse
  face) "needs `ξ = oV(proj a b) ≥ oV m`, whose value-identity is `psi_proj`
  itself — the irreducible circularity"; ya-pss keeps it as a *separate* `sorry`
  from `alpha_step_residue` (necessity.thy:1139, the closure face), explicitly the
  "same §1 core" but not mechanically inter-reducible.

So Lean reproduces the ya-pss two-residue picture independently:
  - closure face: `CanonWitnessResidue` (⟶ `alpha_step_residue`, the psiSelf spine);
  - collapse face: `CollapseResidue`.
Both bottom out at Buchholz's single simultaneous transfinite induction (which
proves closure + collapse *together*), but no sound first-order reduction collapses
one to the other without re-running that induction.  Hence we keep both, and the
end-to-end payoff `oV_nrm_eq_of_collapseResidue` rests on `CollapseResidue` (the
collapse face is the one `Nrm.lean`'s chain actually consumes). -/

end YAPSS
