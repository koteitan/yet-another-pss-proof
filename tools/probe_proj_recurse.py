#!/usr/bin/env python3
"""Can proj0 b1 / proj0 f1 recurse?  proj0 b = P k b1 c1.

The proj result P k b1 c1 is a CRITICAL of b, hence a subterm-ish object.
b1 is the .b of a critical.  Is b1 itself a 'firing-NF-arg-like' object?
Better idea: the whole proj0 b = P k b1 c1 is a CRITICAL; criticals of NF args
are themselves... let's check if (b1, viewing P (k') b1 c1) is in NF.

ALTERNATE CLEAN ROUTE (the real one):  define the relation directly on
proj-results.  proj0 b = greatest k-critical.  Claim: the GREATEST critical map
g*(b) = proj 0 b is olt-monotone on firing NF args because:
  g*(b) is itself an NF term (critical of NF is NF?), lead = maxsub, and
  comparing g*(b) vs g*(f) is olt b f 'lifted'.

Probe: is proj0 b (a critical of b) ITSELF an NF term (in our NF set or NF-arg)?
And does olt (proj0 b)(proj0 f) <-> olt b f hold, suggesting g* is an order embed?
Also: tsize(proj0 b) vs tsize(b): is proj0 b SMALLER (subterm)?  -> recursion.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()
def tsize(t):
    if t == Z: return 1
    return 1 + tsize(t[1]) + tsize(t[2])
def Gterm(u, t):
    if t == Z: return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def pfire(u, b): return any(not olt(g, b) for g in Gterm(u, b))
def proj(u, b):
    while True:
        bad = [g for g in Gterm(u, b) if not olt(g, b)]
        if not bad: return b
        m = bad[0]
        for h in bad[1:]:
            if olt(m, h): m = h
        b = m
def lead(t): return 0 if t == Z else t[0]

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(M) for M in ST}, key=str)
    NFset = set(NF)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]

    # is proj0 b in NF (as a full term) or is P 0 (proj0 b) Z in NF?
    pb_in_NF = 0; pb_tsize_lt = 0; tot = 0
    for b in fire:
        tot += 1
        pb = proj(0, b)
        if pb in NFset: pb_in_NF += 1
        if tsize(pb) < tsize(b): pb_tsize_lt += 1
    print(f"firing args {tot}: proj0 b in NFset {pb_in_NF}, tsize(proj0 b)<tsize(b) {pb_tsize_lt}")

    # CLEAN CANDIDATE: olt(proj0 b)(proj0 f) provable by strong induction if
    # the .b args (b1,f1) of proj results are again 'firing NF args, eq maxsub
    # OR strict maxsub' on a SMALLER tsize.  Check on the main(b1!=f1) eqmaxsub:
    # does (b1,f1) satisfy: olt b1 f1 already given by maxsub b1 < maxsub f1
    # (strict -> lead-domination of proj closes) ?  count split.
    split = {'msub_strict':0, 'msub_eq':0}
    for b in fire:
        pb = proj(0,b)
        if pb==Z: continue
        _,b1,c1 = pb
        for f in fire:
            if not olt(b,f) or maxsub(b)!=maxsub(f): continue
            pf = proj(0,f)
            if pf==Z: continue
            _,f1,d1 = pf
            if b1==f1: continue
            if maxsub(b1) < maxsub(f1): split['msub_strict'] += 1
            else: split['msub_eq'] += 1
    print(f"main eqmaxsub: second-level maxsub split {split}")

if __name__ == '__main__':
    main()
