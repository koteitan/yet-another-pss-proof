#!/usr/bin/env python3
"""CLEAN candidate: olt b f (firing NF args) => every critical g in Gterm0 b
satisfies g <=o proj0 f (the greatest critical of f).  If so, proj0 b (a
critical of b) <=o proj0 f; strictness from proj0 b != proj0 f.

Also test the SUFFICIENT lemma usable in Lean:
  CD: olt b f  =>  forall g in Gterm0 b,  g <=o proj0 f
  CD': olt b f  =>  proj0 b <=o proj0 f   (weaker, the actual need + strict)
  STRICT: proj0 b != proj0 f  on the pairs (so <=o + != gives <o)
Test on ALL firing pairs (not just eqmaxsub) since proj0_bothfire_NF is whole.
Also test the GENERALIZED critical-domination that could be proven by induction:
  GCD: olt x y (any terms, both fire? both NF-related?) => proj0 x <=o proj0 y
       -- but this is FALSE in general; restrict to firing NF args.
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

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(M) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]

    CD_tot=CD_bad=0; CDp_bad=0; strict_bad=0
    cd_ex=[]
    for b in fire:
        pb = proj(0,b); Gb = Gterm(0,b)
        for f in fire:
            if not olt(b,f): continue
            pf = proj(0,f)
            CD_tot += 1
            # CD: all criticals of b are <=o proj0 f
            if not all(le(g, pf) for g in Gb):
                CD_bad += 1
                if len(cd_ex)<5:
                    bad_g=[g for g in Gb if not le(g,pf)][:2]
                    cd_ex.append((b,f,pf,bad_g))
            if not le(pb, pf): CDp_bad += 1
            if pb == pf: strict_bad += 1
    print(f"ALL firing pairs olt b f: {CD_tot}")
    print(f"CD  (all crit of b <=o proj0 f) violations: {CD_bad}")
    print(f"CD' (proj0 b <=o proj0 f)        violations: {CDp_bad}")
    print(f"strict (proj0 b == proj0 f)      count     : {strict_bad}")
    for e in cd_ex: print("  CD VIOL b,f,pf,bad_g=", e)

if __name__ == '__main__':
    main()
