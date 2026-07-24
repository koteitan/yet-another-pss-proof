/-
# PSS termination, ordinal-free — the end-to-end wiring

This file composes the two pillars of the ordinal-free route into the repository's
official termination statements, so that PSS termination is reduced to a **single**
remaining obligation.

    AscArgDomExplicit                                   (Cofinality.lean, open)
      ⟹ AscArgDom                                      `ascArgDom_of_explicit`
      ⟹ PSS Bachmann cofinality                        `pss_cofinality_of_argdom`
      ⟹ WellFounded (ST_PS-restricted `olt` on PairSeq) `wf_olt_ST_PS_of_cofinality`
      ⟹ WellFounded `Rnf`                              `wf_Rnf_of_wf_PS` (below)
      ⟹ WellFounded `stepRel` / no infinite expansion   `step_terminates`

Nothing here uses the ordinal evaluation map `oV`, the Buchholz `OT`/`wf3`
embedding, or `H0clause`: the route replaces the coefficient-domination certificate
by Bachmann cofinality plus the iterated inductive set `W_u` (`Wset.lean`, which is
fully `sorryAx`-free).

`AscArgDomExplicit` is model-verified: `tools/probe_argdom.py` gives 0 violations over
140 / 294 / 692 instances at closure `+5/+6/+7`, and `tools/probe_argdom_witness.py`
confirms the explicit witness `m := |S_hi|` used in its statement (0 violations).
-/
import YAPSS.Cofinality
import YAPSS.Wset
import YAPSS.Proofs

namespace YAPSS
open Three

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

/-- **PSS Bachmann cofinality from the explicit form.** -/
theorem pss_cofinality_of_explicit (H : AscArgDomExplicit) {M N : PairSeq}
    (hM : ST_PS M) (hN : ST_PS N) (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  pss_cofinality_of_argdom (ascArgDom_of_explicit H) hM hN h

/-- **Well-foundedness of `Rnf`, ordinal-free**, from the single open obligation. -/
theorem wf_Rnf_ordinal_free (H : AscArgDomExplicit) : WellFounded Rnf :=
  wf_Rnf_of_wf_PS
    (Wset.wf_olt_ST_PS_of_cofinality (fun hM hN h => pss_cofinality_of_explicit H hM hN h))

/-- **PSS termination, ordinal-free.**  The one-step expansion relation on standard
forms is well-founded, with no appeal to ordinals or to the Buchholz `OT` embedding. -/
theorem PSS_terminates_ordinal_free (H : AscArgDomExplicit) : WellFounded stepRel :=
  step_terminates (wf_Rnf_ordinal_free H)

/-- **No infinite expansion sequence**, ordinal-free. -/
theorem no_infinite_expansion_ordinal_free (H : AscArgDomExplicit) :
    ¬ ∃ S : ℕ → PairSeq, (∀ i, ST_PS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion (wf_Rnf_ordinal_free H)

#print axioms PSS_terminates_ordinal_free
#print axioms no_infinite_expansion_ordinal_free

end YAPSS
