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
    wo
    accinfra
    wflevel
    buchholz
    embed
