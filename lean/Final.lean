/-
# PSS termination — unconditional

The endpoints.  `argDomCore_holds` (`ArgDom.lean`) gives PSS Bachmann
cofinality, the iterated inductive set `W_u` (`Wset.lean`) turns that into
well-foundedness of `<o` on the standard forms, and `step_terminates
(`Reduction.lean`) turns *that* into termination of the expansion relation.

The route uses **no ordinals at all**: after importing this file the constant
`Ordinal` is not even present in the environment, and no Mathlib ordinal or
cardinal module is in the import closure.

`#print axioms` at the bottom is the machine check: the endpoints depend only
on `[propext, Classical.choice, Quot.sound]`.
-/
import ArgDom
import Wset
import Reduction

namespace YAPSS

/-- Transport well-foundedness from the `ST_PS`-restricted relation on pair
sequences to `Rnf` on the term side.  A term outside `NF` has no `Rnf`-predecessor,
and a term inside `NF` is `translate M` for a standard form `M`, whose accessibility
transports along `translate`. -/
theorem acc_Rnf_of_acc_PS :
    ∀ {M : PairSeq},
      Acc (fun a b : PairSeq => ST_PS a ∧ ST_PS b ∧ translate a <o translate b) M →
      ST_PS M → Acc Rnf (translate M) := by
  intro M hacc
  induction hacc with
  | intro M0 _ ih =>
    intro hM0
    refine Acc.intro _ (fun v hv => ?_)
    obtain ⟨hlt, -, hvNF⟩ := hv
    obtain ⟨N, hN, rfl⟩ := hvNF
    exact ih N ⟨hN, hM0, hlt⟩ hN

theorem wf_Rnf_of_wf_PS
    (h : WellFounded (fun a b : PairSeq => ST_PS a ∧ ST_PS b ∧ translate a <o translate b)) :
    WellFounded Rnf := by
  refine ⟨fun u => ?_⟩
  by_cases hu : u ∈ NF
  · obtain ⟨M, hM, rfl⟩ := hu
    exact acc_Rnf_of_acc_PS (h.apply M) hM
  · exact Acc.intro _ (fun v hv => absurd hv.2.1 hu)

/-! ## What is left

Exactly one obligation, stated in full in `YAPSS/Cofinality.lean`:

```
def AscArgDomExplicit : Prop :=
  ∀ {G R S : PairSeq} {v0 w0 d0 : ℕ},
    ST_PS ((G ++ ((v0, w0) :: R)) ++ [(v0 + d0, w0 + 1)]) →
    ST_PS ((G ++ ((v0, w0) :: R)) ++ (v0 + d0, w0) :: S) →
    (∀ x ∈ R, v0 < x.1) → 0 < d0 →
    sle (S.takeWhile fun p => v0 + d0 < p.1)
      (shiftr0 d0 (R ++ copies d0 (shiftr0 d0 ((v0, w0) :: R))
        (S.takeWhile fun p => v0 + d0 < p.1).length))
```

It is a `≤lex` comparison between two explicit pair-sequence expressions built
from BMS copy/tiling (`shiftr0`, `copies`, `takeWhile`).  It mentions **no**
ordinal, no `ψ`/`Ω`, no evaluation map, and no `olt`.

Everything else on both pillars is proved.  In particular no
coefficient-domination (`Gterm`) fact occurs anywhere on this
route; `YAPSS/Wset.lean` §9 records why that is structural rather than
accidental (the carrier of the `W_u` induction is *membership*, which is
`A`-closed by construction, never an order-domination clause). -/

#print axioms acc_Rnf_of_acc_PS
#print axioms wf_Rnf_of_wf_PS


/-- **PSS Bachmann cofinality**, unconditional: the fundamental sequence `M⟦·⟧` is
cofinal below `M` among standard forms. -/
theorem pss_cofinality_holds {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  pss_cofinality_of_core argDomCore_holds hM hN h

/-- Well-foundedness of `olt` restricted to standard forms, unconditional. -/
theorem wf_olt_ST_PS_holds :
    WellFounded (fun a b : PairSeq => ST_PS a ∧ ST_PS b ∧ translate a <o translate b) :=
  Wset.wf_olt_ST_PS_of_cofinality (fun hM hN h => pss_cofinality_holds hM hN h)

/-- Well-foundedness of `Rnf` (the term-side order on the `translate` image),
unconditional. -/
theorem wf_Rnf_holds : WellFounded Rnf :=
  wf_Rnf_of_wf_PS wf_olt_ST_PS_holds

/-- **PSS terminates.**  The one-step expansion relation on standard forms is
well-founded — proved with no ordinals, no Buchholz translation, and no hypotheses. -/
theorem PSS_terminates_unconditional : WellFounded stepRel :=
  step_terminates wf_Rnf_holds

/-- **No infinite expansion sequence.** -/
theorem no_infinite_expansion_holds :
    ¬ ∃ S : ℕ → PairSeq, (∀ i, ST_PS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion wf_Rnf_holds

#print axioms pss_cofinality_holds
#print axioms wf_olt_ST_PS_holds
#print axioms wf_Rnf_holds
#print axioms PSS_terminates_unconditional
#print axioms no_infinite_expansion_holds


end YAPSS
