#!/usr/bin/env python3
"""probe_m3_nf_lemma.py -- find the EXACT NF lemma that excludes the same-cr
subscript-drop, for the Lean M3 singleton step.

The singleton step needs: for NF t = P a b Z and any NF predecessor v <o t,
Acc v follows from {lower-cr IH, arg-accessibility on b}.  The dangerous case is
a summand P a' b' Z of v with a' < a at the SAME cr (the off-NF cnf cex).

CANDIDATE LEMMAS (each: does it hold for NF, and does it exclude the bad case?):
 (L1) NF maxsub-mono: v<o t => maxsub v <= maxsub t.  [GREEN maxsub_mono_NF']
      Does NOT exclude same-maxsub subscript-drop (cex maxsub equal).
 (L2) THE LEAD LEMMA: for NF t=P a b Z, an NF predecessor v has lead v <= a?
      (lead = leading subscript).  If lead v < a, v is dominated trivially
      (olt_P_of_lead_lt).  If lead v == a, the head principal of v is P a b'' ...
      with SAME subscript a (NOT a'<a).  => the FIRST summand has a'=a.  But
      LATER summands (siblings) could have a' < a... but those are <= the head
      (cnf noninc) so also fine?  CHECK: for NF v <o NF t=P a b Z, is
      lead v <= a, AND are all summands of v with subscript < a 'dominated'
      (i.e. the singleton step never needs them as direct preds)?
 (L3) THE CLEAN ONE: for NF v <o NF t, the DM decomposition olt_summands_decomp
      gives v = pre ++ bad, t = pre ++ front, with bad.head <o front.head.  For
      t = P a b Z (single principal), front = [P a b Z], pre = [].  So bad =
      summands(v), and EVERY summand of v is <o P a b Z (already have
      summand_lt_of_pred).  The question is whether each such summand P a' b' Z
      is handled.  Per forest_split: a'=a always (argdrop) for NF.  L3 asks: is
      'a' = a for the HEAD summand' provable from lead v <= a + lead v computed?

We test L2/L3: for NF v <o NF t=P a b Z (single principal), tabulate lead v vs a,
and for each summand P a' b' Z of v with cr(summand)>=cr(t)... no wait, we want
the DIRECT singleton preds.  Reframe to the LEAN-PROVABLE claim:

 CLAIM-FOR-LEAN: for NF t = P a b Z and NF v with v <o t, EITHER lead v < a
   (=> v <o t by olt_P_of_lead_lt, trivially dominated, Acc by anything), OR
   lead v == a AND v's head summand is P a b'' Z with b'' <o b OR b''==b...
   i.e. the comparison reduces to the ARG b.  Tabulate the lead distribution and
   whether lead v == a => head-arg <o b.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, olt, maxsub
from probe_bmocf_ancestor import enum_depth

Z = ()
def lead(t): return t[0] if t != Z else 0
def cr_inv(t):
    if t == (): return 0
    a, b, c = t
    inv = 1 if (b != () and maxsub(b) > a) else 0
    return max(inv + cr_inv(b), cr_inv(c))
def summands(t):
    if t == (): return []
    a, b, c = t
    return [(a, b, ())] + summands(c)

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        NF = set(translate(M) for M in seen); NF.discard(Z)
        NFl = list(NF)
        md = max(seen.values())
        sing = [t for t in NF if t[2] == Z and t != Z]

        # CLAIM: for NF v <o NF t=P a b Z: lead v <= a.
        lead_le = lead_gt = 0
        # When lead v == a: head summand P a b'' Z, is b'' <o b or b''==b?
        eqlead = eqlead_arg_ok = 0
        eqlead_ex = []
        for t in sing:
            a, b, _ = t
            for v in NFl:
                if v == t or not olt(v, t):
                    continue
                lv = lead(v)
                if lv <= a: lead_le += 1
                else:
                    lead_gt += 1
                if lv == a:
                    eqlead += 1
                    # head summand of v
                    hs = summands(v)[0]   # P a'' b'' Z
                    haa, hbb, _ = hs
                    # head subscript should be a (=lv); check arg vs b
                    if haa == a and (olt(hbb, b) or hbb == b):
                        eqlead_arg_ok += 1
                    elif len(eqlead_ex) < 6:
                        eqlead_ex.append((t, v, hs))

        print(f'[closure+{rounds}] maxdepth={md} singles={len(sing)}')
        print(f'  NF v <o NF t=P a b Z: lead v <= a : {lead_le}   lead v > a : {lead_gt}')
        print(f'  lead v == a cases: {eqlead}  head-arg <o b or == b: {eqlead_arg_ok}')
        for t, v, hs in eqlead_ex[:6]:
            from wfe_explore import fmt as tf
            print(f'     EX t={tf(t)[:26]} v={tf(v)[:26]} head={tf(hs)[:26]}')

if __name__ == '__main__':
    main()
