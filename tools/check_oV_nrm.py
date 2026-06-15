#!/usr/bin/env python3
"""Test oV(nrm t) = oV t  on NF (and all subterms), proxy = nrm-name value.
nrm here is the three-level normalizer:
  proj a b: collapse-projection loop (replace b by max bad Gterm elt until OT3 holds)
  ins a b t: absorb principal D_a(b) if dominated by head of t else prepend
  nrm Z=Z; nrm(P a b c)=ins a (proj a (nrm b)) (nrm c)
Compare oV via nrm-name proxy: nrmname(threeterm).
"""
import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, fmt, enum_ST, maxsub
from valnorm import conv, nrm as nrmname, lt_term, fmtb

Z=()
def Gterm(u,t):
    if t==Z: return []
    a,b,c=t; r=[]
    if u<=a: r.append(b); r+=Gterm(u,b)
    r+=Gterm(u,c); return r
def olt3(s,t): return olt(s,t)
def proj(u,b):
    # loop: while exists g in Gterm u b with not olt g b: b := max such g
    while True:
        bad=[g for g in Gterm(u,b) if not olt(g,b)]
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if olt(g,h): g=h
        b=g
    return b
def ins(a,b,t):
    if t==Z: return (a,b,Z)
    e,f,g=t
    if a<e or (a==e and olt(b,f)): return t
    return (a,b,t)
def nrm3(t):
    if t==Z: return Z
    a,b,c=t
    return ins(a, proj(a, nrm3(b)), nrm3(c))

def oVkey(t): return nrmname(conv(t))

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4,5),max_len=16,rounds=7)
    NF=set(translate(M) for M in ST)
    # gather all subterms too
    allt=set()
    def subs(t):
        allt.add(t)
        if t!=Z:
            a,b,c=t; subs(b); subs(c)
    for t in NF: subs(t)
    print(f"#NF={len(NF)}  #all subterms={len(allt)}")
    viol=0; ex=[]
    for t in allt:
        if oVkey(nrm3(t)) != oVkey(t):
            viol+=1
            if len(ex)<8: ex.append(t)
    print(f"oV(nrm t)=oV t  VIOLATIONS: {viol} / {len(allt)}")
    for t in ex:
        print("  VIOL t=",fmt(t)," oV t=",fmtb(oVkey(t))," oV nrm t=",fmtb(oVkey(nrm3(t))))
    # also: is nrm3 image wf3? and does olt v u => olt (nrm3 v)(nrm3 u) on NF?
    NFl=list(NF)
    import random; rng=random.Random(2)
    pool=NFl if len(NFl)<1500 else rng.sample(NFl,1500)
    bad_op=0; exo=[]
    import itertools
    for v,u in itertools.permutations(pool,2):
        if olt(v,u):
            if not olt(nrm3(v),nrm3(u)):
                bad_op+=1
                if len(exo)<5: exo.append((v,u))
    print(f"nrm_order_pres (olt v u => olt(nrm v)(nrm u)) VIOL: {bad_op}")
    for v,u in exo:
        print("  OPVIOL",fmt(v),"<o",fmt(u)," but nrm:",fmt(nrm3(v)),"vs",fmt(nrm3(u)))

if __name__=="__main__":
    main()
