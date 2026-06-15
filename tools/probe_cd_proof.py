#!/usr/bin/env python3
"""Find the induction-friendly form of CD: olt b f => all g in Gterm0 b, g <=o proj0 f.

Candidate lemmas (firing NF args b,f, olt b f):
  E1: forall g in Gterm0 b, EXISTS h in Gterm0 f with g <=o h   (critical embed)
  E2: forall g in Gterm0 b, g <=o f  OR g in Gterm0 f           (g dominated by f's level)
  E3: the GENERAL fact (no NF, no fire): olt b f => forall g in Gterm0 b,
      g <=o f  OR  EXISTS h in Gterm0 f, g <=o h.  (pure olt/Gterm structural!)
      -- if E3 holds generally it's a clean structural induction.
  E4: even simpler: olt x y => forall g in Gterm u x, g <o y OR g in Gterm u y
      OR EXISTS h in Gterm u y with g <=o h.
  Test E3/E4 on ARBITRARY pairs (not just firing NF) to see if it's a pure
  structural lemma (provable by induction on olt).
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
import itertools
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

def gen_terms(depth, maxsub_):
    # small enumeration of Three terms for the pure-structural test
    if depth == 0:
        yield Z; return
    yield Z
    for a in range(maxsub_+1):
        for b in gen_terms(depth-1, maxsub_):
            for c in gen_terms(depth-1, maxsub_):
                yield (a,b,c)

def main():
    # PART 1: E1/E2 on firing NF args
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(M) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]
    E1_bad=E2_bad=tot=0
    for b in fire:
        Gb=Gterm(0,b)
        for f in fire:
            if not olt(b,f): continue
            tot+=1
            Gf=Gterm(0,f)
            for g in Gb:
                if not any(le(g,h) for h in Gf): E1_bad+=1; break
            for g in Gb:
                if not (olt(g,f) or g in Gf or any(le(g,h) for h in Gf)): E2_bad+=1; break
    print(f"firing NF pairs {tot}: E1(embed) viol {E1_bad}, E2 viol {E2_bad}")

    # PART 2: E3/E4 PURE STRUCTURAL on arbitrary small terms
    terms=list(gen_terms(3,2))
    e3_bad=e4_bad=ptot=0; ex=[]
    for x in terms:
        for y in terms:
            if not olt(x,y): continue
            ptot+=1
            Gx=Gterm(0,x); Gy=Gterm(0,y)
            for g in Gx:
                # E4: g <o y OR g in Gy OR exists h in Gy, g <=o h
                if not (olt(g,y) or g in Gy or any(le(g,h) for h in Gy)):
                    e4_bad+=1
                    if len(ex)<5: ex.append((x,y,g))
                    break
    print(f"PURE structural pairs {ptot}: E4 viol {e4_bad}")
    for e in ex: print("  E4 VIOL x,y,g=", e)

if __name__ == '__main__':
    main()
