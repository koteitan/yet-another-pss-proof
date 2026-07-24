/-
# PSS termination — unconditional, ordinal-free

This file closes the ordinal-free route: it discharges the hypothesis that
`YAPSS/OrdinalFree.lean` carried, and states PSS termination **with no hypotheses at
all**.

    argDomCore_holds                (AscArg.lean)      ArgDomCore, proved
      ⟹ PSS Bachmann cofinality     `pss_cofinality_of_core`
      ⟹ WellFounded (ST_PS-restricted `olt` on `PairSeq`)
                                    `Wset.wf_olt_ST_PS_of_cofinality`   (Wset.lean)
      ⟹ WellFounded `Rnf`           `wf_Rnf_of_wf_PS`                  (OrdinalFree.lean)
      ⟹ WellFounded `stepRel`       `step_terminates`                  (Proofs.lean)

The route uses **no ordinal evaluation map `oV`, no Buchholz `OT`/`wf3` embedding, and
no coefficient-domination (`H0clause` / `Gterm`) fact anywhere**.  Well-foundedness is
certified instead by Bachmann cofinality (`Cofinality.lean`, `AscArg.lean`) together
with the iterated inductive set `W_u` (`Wset.lean`), transplanted natively to PSS pair
sequences from the syntactic proof of `OT_B`'s well-foundedness.

`#print axioms` at the bottom is the machine check: the endpoints depend only on
`[propext, Classical.choice, Quot.sound]`.
-/
import YAPSS.AscArg
import YAPSS.OrdinalFree

namespace YAPSS

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
