#!/usr/bin/env python3
"""probe_m3_lead_provable.py -- is `lead v <= a` (for NF v <o NF P a b Z) the
bare forest fact, or derivable from GREEN NF invariants?

GREEN NF invariants available in Lean:
  - maxsub_mono_NF': v<o u (both NF) => maxsub v <= maxsub u.
  - nfinv: spine begins 0,1,...,maxsub (inv2); maxsub = climb (max on spine).
  - cnf: siblings non-increasing.
  - The spine of P a b Z = a :: spine b.

The singleton-step target P a b Z.  Two regimes:
  NONCOLLAPSE (maxsub b <= a): maxsub(P a b Z) = a.  Then maxsub_mono_NF' gives
     maxsub v <= a, and lead v <= maxsub v <= a.  *** lead v <= a is FREE from
     maxsub_mono_NF' here. ***  (Need lead v <= maxsub v: trivially true, lead is
     a subscript of v, maxsub is the max subscript.)
  COLLAPSE (maxsub b > a): maxsub(P a b Z) = maxsub b > a.  maxsub_mono_NF' only
     gives lead v <= maxsub v <= maxsub b, NOT <= a.  So lead v <= a is NOT free
     here -- it's the forest content IF needed.

KEY QUESTION: in the COLLAPSE case, do we even NEED lead v <= a?  The singleton
step P a b Z with b critical (cr b = n-1): b in AccBelow n (lower-stratum IH).
The predecessors v <o P a b Z in Mn n.  We want Acc v.  Per forest_split, the
DIRECT singleton preds are argdrops (a'=a).  But to PROVE that in Lean without
lead v <= a, can we use the DM decomposition: v's summands are each <o P a b Z,
and decompose against the single front [P a b Z]?

Reframe the LEAN-PROVABLE singleton step for COLLAPSE:
  Acc(P a b Z) <= b in Accn(n-1) [lower stratum].  A pred v in Mn n, v <o P a b Z.
  Decompose v into summands; each summand s = P a' b' Z <o P a b Z.
  For each s: by olt, a'<a OR (a'=a, b'<o b) OR (a'=a,b'=b,...).
  - a'=a, b'<o b: b' <o b, and b' is... we want Acc(P a b' Z).  If cr(P a b' Z)
    relates to b's stratum.  cr(P a b' Z) = (1 if a<maxsub b' else 0)+cr b'.
  - a'<a: THE SAME-CR SUBSCRIPT DROP.  If this occurs in Mn n it's the wall.
    Per Q1 it's off-NF.  So we'd need NF(s) to exclude it -- but s is a SUMMAND
    of an NF v, is s itself NF?  CHECK: are summands of NF terms NF?

CRUCIAL CHECK: is summands-of-NF in NF?  If yes, then each summand s in NF, and
Q1 (NF excludes same-cr a'<a) applies to s directly => SUBDROP excluded by NF(s).
Then we need: NF(s) provable for s a summand of NF v.  And the off-NF exclusion
becomes: for NF s = P a' b' Z and NF t = P a b Z with s <o t, NOT(a'<a same cr).
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
        md = max(seen.values())

        # CHECK A: are summands of NF terms themselves NF?
        a_tot = a_innf = 0
        a_ex = []
        for t in NF:
            for s in summands(t):
                a_tot += 1
                if s in NF: a_innf += 1
                elif len(a_ex) < 5:
                    from wfe_explore import fmt as tf
                    a_ex.append((tf(t)[:30], tf(s)[:30]))

        # CHECK B: for NF single principals s=P a' b' Z, t=P a b Z, s<o t,
        #   is the same-cr a'<a case absent?  (the NF off-stratum exclusion, on
        #   single principals -- the actual unit after summands-in-NF)
        sing = [x for x in NF if x[2] == Z and x != Z]
        b_subdrop_samecr = 0
        b_ex = []
        for t in sing:
            a, b, _ = t; n = cr_inv(t)
            for s in sing:
                if s == t or not olt(s, t): continue
                sa, sb, _ = s
                if sa < a and cr_inv(s) == n:
                    b_subdrop_samecr += 1
                    if len(b_ex) < 5:
                        from wfe_explore import fmt as tf
                        b_ex.append((tf(t)[:28], tf(s)[:28], n))

        print(f'[closure+{rounds}] maxdepth={md} NF={len(NF)} singles={len(sing)}')
        print(f'  (A) summands of NF in NF: {a_innf}/{a_tot}', '' if a_innf==a_tot else a_ex)
        print(f'  (B) NF single-principal same-cr a\'<a preds: {b_subdrop_samecr}', b_ex if b_ex else '')

if __name__ == '__main__':
    main()
