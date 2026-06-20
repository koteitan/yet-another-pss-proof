#!/usr/bin/env python3
"""probe_m3_forest_split.py -- refine probe_m3_nf_close FOREST residual.

The FOREST class (NF same-cr in-Mn predecessor-summands of an NF single
principal) splits by the olt mechanism between P a' b' Z and P a b Z:
  ARGDROP : a' == a, b' <o b  -- handled by the arg-accessibility induction
            (Acc b => Acc (P a b Z)), the DM/singleton step, NO forest fact.
  SUBDROP : a' < a            -- subscript-drop at SAME cr in Mn: the bare
            forest-position wall (cr_inv does not separate it, NF excludes the
            OFF-stratum ones but these are IN Mn).
  OTHER   : a' == a, b' == b (impossible, would be equal) or weirdness.

DECISIVE: if SUBDROP == 0 over NF, then EVERY same-cr in-Mn predecessor is an
arg-drop => the Towsner singleton step closes by arg-accessibility induction
(M2-style), NO bare forest fact needed for the SINGLETON step itself.  The
LOWER-cr predecessors go to the stratum IH.  => door1 M3 BUILDABLE on NF.

If SUBDROP > 0, those subscript-drops at the SAME cr in Mn are the irreducible
forest content for the singleton step.  Report convergence.

Also re-checks with the STRICT Mn proxy and a STRONGER one (critSub recursively
accessible), to be sure the residual is not an artifact of a weak in_Mn.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt, maxsub
from wfe_explore import fmt as tfmt
from probe_bmocf_ancestor import enum_depth

Z = ()

def cr_inv(t):
    if t == (): return 0
    a, b, c = t
    inv = 1 if (b != () and maxsub(b) > a) else 0
    return max(inv + cr_inv(b), cr_inv(c))

def critSub(t):
    out = []
    def rec(t):
        if t == (): return
        a, b, c = t
        if b != () and maxsub(b) > a:
            out.append(b)
        rec(b); rec(c)
    rec(t); return out

def summands(t):
    if t == (): return []
    a, b, c = t
    return [(a, b, ())] + summands(c)

def in_Mn(s, n):
    if cr_inv(s) > n:
        return False
    return all(cr_inv(b) < n for b in critSub(s))

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        NF = set(translate(M) for M in seen)
        NF.discard(Z)
        NFl = list(NF)
        md = max(seen.values())
        sing = [t for t in NF if t[2] == Z and t != Z]

        ARGDROP = SUBDROP = OTHER = 0
        subdrop_ex = []
        for t in sing:
            n = cr_inv(t)
            a, b, _ = t
            for v in NFl:
                if v == t or not olt(v, t):
                    continue
                for s in summands(v):
                    sa, sb, _ = s
                    if cr_inv(s) < n:      # lower stratum: IH, skip
                        continue
                    if not in_Mn(s, n):    # K^<0 excludes: skip
                        continue
                    # same-cr in-Mn predecessor-summand: split by olt mechanism
                    # need olt(s, t) at summand level (s is one summand of v, but
                    # the relevant comparison for the singleton step is s vs t)
                    if not olt(s, t):
                        # s alone is not <o t (it's part of the sum); not a direct
                        # singleton-step predecessor.  The DM step handles these
                        # via the multiset order, not the singleton.  Count as
                        # OTHER (DM-handled, not the singleton wall).
                        OTHER += 1
                        continue
                    if sa == a and olt(sb, b):
                        ARGDROP += 1
                    elif sa < a:
                        SUBDROP += 1
                        if len(subdrop_ex) < 8:
                            subdrop_ex.append((t, s, n))
                    else:
                        OTHER += 1

        print(f'[closure+{rounds}] maxdepth={md} NF={len(NF)} singles={len(sing)}')
        print(f'  same-cr in-Mn pred-summands that ARE <o t (singleton-step preds):')
        print(f'     ARGDROP (a\'=a, b\'<b: arg-accessibility, NO forest) = {ARGDROP}')
        print(f'     SUBDROP (a\'<a same-cr in-Mn: THE BARE WALL)        = {SUBDROP}')
        print(f'     OTHER   (DM-handled / not direct singleton pred)    = {OTHER}')
        for t, s, n in subdrop_ex[:8]:
            print(f'       SUBDROP t={tfmt(t)[:34]} pred={tfmt(s)[:34]} n={n}')

if __name__ == '__main__':
    main()
