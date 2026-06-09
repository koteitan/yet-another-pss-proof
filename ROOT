session YAPSS = HOL +
  description "
    Yet Another termination proof of the Pair Sequence System
    (ペア数列システムの停止性・別アプローチ).

    Original termination proof of the Pair Sequence System (PSS), via a
    translation of pair sequences into a fresh ordinal notation p_a(b)+c
    (NOT Buchholz's psi), solved by a 3-dimensional transfinite induction
    on (a,b,c).  Same approach as the Primitive Sequence System (PrSS)
    proof: map each sequence to a well-founded notation and show the
    expansion step strictly decreases the measure.

    def         formalized PSS definitions (faithful to pss-original-paper.html)
    mechanized  the p_a(b)+c notation, well-foundedness, translate, decrease
    proof       top-level termination theorem
  "
  options [document = false, quick_and_dirty]
  sessions
    "HOL-Library"
  theories
    def
    mechanized
    proofs
    wf
    wfsum
    seqlex

session PSI in ord = ZFC_in_HOL +
  description "Buchholz Lemma 2.2 proved semantically: psi_v on ZFC-in-HOL ordinals
    + the value map oV embeds (wf3, olt) = Buchholz (OT, <) into the ordinals,
    hence wf_olt_wf3.  (Bridge NF -> wf3 pending.)"
  options [document = false, quick_and_dirty]
  sessions
    YAPSS
  theories
    psi
    otembed
