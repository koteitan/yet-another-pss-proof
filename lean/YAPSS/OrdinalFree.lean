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

Nothing here uses ordinals: the route replaces the coefficient-domination
certificate by Bachmann cofinality plus the iterated inductive set `W_u`
(`Wset.lean`, which is fully `sorryAx`-free).  The ordinal modules that the
abandoned route needed (`Psi.lean`, and the evaluation map `oV` together with the
Buchholz `OT` predicate `wf3` in `Otembed.lean`) have been deleted from the
repository; `Gterm.lean` keeps only the syntactic coefficient set `Gterm`.

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

end YAPSS
