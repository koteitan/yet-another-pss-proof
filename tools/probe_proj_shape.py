#!/usr/bin/env python3
"""What is the SHAPE of proj 0 b for a firing NF head-0 arg b?

Hypothesis: proj 0 b is a 'spine tower' P k (P (k-1) ... ) ... determined by
the NF spine [0,1,...,maxsub], so two such towers with the SAME k=maxsub and
under olt b f compare by a clean recursive descent that mirrors olt b f itself.

Concretely test:
  S1: is proj 0 b = P k X Y with lead X = ? (is X again a 'projection' shape?)
  S2: KEY -- is proj 0 b DETERMINED by (maxsub b) and the sub-structure, i.e.
      does olt b f (eq maxsub) imply the proj-towers descend in lockstep?
  S3: Most useful for Lean: is there a SIMPLER equivalent goal --
      olt (proj0 b)(proj0 f)  <->  olt b f  ?? (i.e. proj0 is olt-monotone on
      this exact class -- the eqmaxsub firing NF args).  If TRUE that's the
      statement but we need a proof handle.
  S4: relate proj0 b to b directly: is proj0 b <=o b or >=o b ?  proj inflates
      (proj_ole: b <=o proj0 b).  So b <=o proj0 b.  Then olt b f gives
      b <o f <=o proj0 f, i.e. b <o proj0 f.  And proj0 b >=o b.  Does
      proj0 b <o proj0 f follow from proj0 b being the LEAST upper... no.
  S5: Check transitivity chain: b <o f <=o proj0 f, so b <o proj0 f.
      Also proj0 b: is proj0 b <o f or >=o f?  (R2 said proj0 b <o f is 0!)
      So proj0 b >=o f always (since not below). i.e. f <=o proj0 b.
      Then we have f <=o proj0 b AND b <o f.  And want proj0 b <o proj0 f.
      Since f <=o proj0 b and f <=o proj0 f, both >= f.  Hmm.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()
def le(s, t): return s == t or olt(s, t)
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
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]

    # S5: f <=o proj0 b  (since proj0 b not <o f) -- check on ALL firing args (not just pairs)
    f_le_projb = 0; tot_self = 0
    for b in fire:
        tot_self += 1
        pb = proj(0, b)
        # is b <=o proj0 b ? (proj_ole)
        # is the firing arg itself <o proj0 b strictly?
    # S3: proj0 olt-monotone on eqmaxsub firing pairs <-> olt b f
    s3_tot = s3_iff = 0
    # general: proj0 monotone on ALL firing pairs (not nec eq maxsub)?
    allpair_tot = allpair_ok = 0
    for b in fire:
        pb = proj(0, b)
        for f in fire:
            if not olt(b, f): continue
            pf = proj(0, f)
            allpair_tot += 1
            if olt(pb, pf): allpair_ok += 1
            if maxsub(b) == maxsub(f):
                s3_tot += 1
                if olt(pb, pf): s3_iff += 1
    print(f"ALL firing pairs olt b f: {allpair_tot}, olt(proj0 b)(proj0 f): {allpair_ok}")
    print(f"  eqmaxsub subset: {s3_tot}, ok {s3_iff}")
    # S4/S5: relation of proj0 b to f on eqmaxsub pairs
    rel = {'f_lt_pb':0,'f_eq_pb':0,'f_gt_pb':0}
    relbf = {'b_lt_pf':0}
    for b in fire:
        pb = proj(0, b)
        for f in fire:
            if not olt(b, f) or maxsub(b)!=maxsub(f): continue
            pf = proj(0,f)
            if olt(f, pb): rel['f_lt_pb'] += 1
            elif f == pb: rel['f_eq_pb'] += 1
            else: rel['f_gt_pb'] += 1
            if olt(b, pf): relbf['b_lt_pf'] += 1
    print(f"eqmaxsub pairs: f vs proj0 b: {rel}")
    print(f"  b <o proj0 f: {relbf}")

if __name__ == '__main__':
    main()
