import ArgDom
import Wset
import Reduction

namespace YAPSS

/-- Transport well-foundedness from the `ST_PS`-restricted relation on pair
sequences to `Rnf` on the term side. -/
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

/-- **PSS Bachmann cofinality**: the fundamental sequence `M⟦·⟧` is
cofinal below `M` among standard forms. -/
theorem pss_cofinality_holds {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  pss_cofinality_of_core argDomCore_holds hM hN h

/-- Well-foundedness of `olt` restricted to standard forms. -/
theorem wf_olt_ST_PS_holds :
    WellFounded (fun a b : PairSeq => ST_PS a ∧ ST_PS b ∧ translate a <o translate b) :=
  Wset.wf_olt_ST_PS_of_cofinality (fun hM hN h => pss_cofinality_holds hM hN h)

/-- Well-foundedness of `Rnf` (the term-side order on the `translate` image). -/
theorem wf_Rnf_holds : WellFounded Rnf :=
  wf_Rnf_of_wf_PS wf_olt_ST_PS_holds

/-- **PSS terminates.**  The one-step expansion relation on standard forms is
well-founded. -/
theorem PSS_terminates_unconditional : WellFounded stepRel :=
  step_terminates wf_Rnf_holds

/-- **No infinite expansion sequence.** -/
theorem no_infinite_expansion_holds :
    ¬ ∃ S : ℕ → PairSeq, (∀ i, ST_PS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion wf_Rnf_holds

end YAPSS
