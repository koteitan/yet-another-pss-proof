#!/usr/bin/env python3
"""Find a provable invariant for the FF residue: olt B F, both fire (y),
need olt (proj y B) (proj y F). Test candidate handles:
 H1: mB := proj y B in Gterm y F          (max crit of B is a crit of F)
 H2: olt mB F                              (proj-of-smaller below larger host)
 H3: not olt mF mB   directly             (the goal, sanity)
 H4: mB in {criticals g of F with not olt g F}  (mB is a *violating* crit of F)
 H5: olt mB (proj y F) given mB violates F (then maxo_ub gives it)
We want some Hk that (a) always holds and (b) combined with maxo_ub/proj_once
yields the goal. mB violates F (not olt mB F) + mB in Gterm y F => mB in the
filtered list of F => maxo_ub => not olt mF mB => ole mB mF; with mB != mF => olt.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G
from fast_pss import oper

def proj(a,x):
    bb=x
    while True:
        bad=[g for g in G(a,bb) if not lt_term(g,bb)]
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if lt_term(g,h): g=h
        bb=g
    return bb
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))

base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(5):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=22 and tt not in extra:
                extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print('deep ST closure =',len(extra),flush=True)

from collections import defaultdict
byY=defaultdict(list); seen=defaultdict(set)
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if not aM: continue
    B=NT(aM)
    if B in seen[y]: continue
    seen[y].add(B); byY[y].append(B)

def crits(u,x): return list(G(u,x))
cap=300
H1f=H2f=H4f=0; tot=0
exH1=[]; exH2=[]; exH4=[]
for y,L in byY.items():
    if len(L)>cap: L=random.sample(L,cap)
    PR={}
    for B in L:
        if B not in PR: PR[B]=proj(y,B)
    for B,F in itertools.combinations(L,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): B,F=F,B
        else: continue
        pB=PR[B]; pF=PR[F]
        if pB==B or pF==F: continue  # only FF
        tot+=1
        cF=crits(y,F)
        inGF = any(str(pB)==str(g) for g in cF)   # H1
        viol = not lt_term(pB,F)                   # H2: mB violates F (not olt mB F)
        if not inGF:
            H1f+=1
            if len(exH1)<4: exH1.append((y,B,F,pB))
        if not viol:
            H2f+=1
            if len(exH2)<4: exH2.append((y,B,F,pB))
        # H4: mB is a violating critical of F
        if not (inGF and viol):
            H4f+=1
            if len(exH4)<4: exH4.append((y,B,F,pB,inGF,viol))
print(f'FF pairs tested = {tot}')
print(f'H1 (proj y B in Gterm y F)         fail={H1f}')
print(f'H2 (not olt (proj y B) F, i.e. mB violates F) fail={H2f}')
print(f'H4 (mB is a violating critical of F) fail={H4f}')
for y,B,F,pB in exH1[:4]: print('  H1FAIL y=%d proj=%s  F=%s'%(y,fmtb(pB),fmtb(F)))
for y,B,F,pB in exH2[:4]: print('  H2FAIL y=%d proj=%s  F=%s'%(y,fmtb(pB),fmtb(F)))
for y,B,F,pB,a,b in exH4[:4]: print('  H4FAIL y=%d inGF=%s viol=%s proj=%s F=%s'%(y,a,b,fmtb(pB),fmtb(F)))
print('DONE')
