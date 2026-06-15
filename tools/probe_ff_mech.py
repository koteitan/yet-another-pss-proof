#!/usr/bin/env python3
"""Mechanism hunt for S2: exists viol crit g of F with olt (proj y B) g.
proj y B = maxo vB.  We want to UNDERSTAND why, not just confirm.

Tests:
 M1: olt mB mF  (goal, sanity) -> count 0 fail expected.
 M2: For the specific gB := mB (max viol crit chain endpoint of B), is there
     a viol crit g of F with olt gB g OR gB == g but then olt fails?
     We need STRICT olt mB g.  Count pairs where NO viol crit g of F has olt mB g
     (== S2 fail). expect 0.
 M3: Decompose by 'why mB < some vF': test whether mF (=max vF) itself has
     olt mB mF (trivially the maxo). Already know 0 fail. The structural q:
     is mF ALWAYS a 'fresh' crit of F not present as a crit of B?
 M4: olt B F => is vB 'dominated' by vF elementwise? i.e for every gb in vB
     exists gf in vF with le_term gb gf? count fail.
 M5: KEY: olt B F and both fire. Is it true that olt mB F? (mB < F itself)
     i.e. proj y B < F.  Then since mF >= F? NO mF is a crit < F. Hmm.
     Actually mF = proj y F is a viol crit so NOT mF<F i.e F<=mF. So if mB<F<=mF
     => mB<mF. TEST: olt mB F (proj y B strictly below F).  count fail.
 M6: ole F mF (F <= proj y F)? viol crit means not olt mF F i.e F<=mF. count fail (expect 0).
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G
from fast_pss import oper
def projlist(a,x): return [g for g in G(a,x) if not lt_term(g,x)]
def proj(a,x):
    bb=x
    while True:
        bad=projlist(a,bb)
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if lt_term(g,h): g=h
        bb=g
    return bb
def le_term(a,b): return a==b or lt_term(a,b)
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
            if len(tt)<=22 and tt not in extra: extra.add(tt); new.append(tt)
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
cap=300
tot=0
m1f=m5f=m6f=s2f=m4f=0
exM5=[]
for y,L in byY.items():
    if len(L)>cap: L=random.sample(L,cap)
    PR={}; VC={}
    for B in L:
        if B not in PR: PR[B]=proj(y,B); VC[B]=projlist(y,B)
    for B,F in itertools.combinations(L,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): B,F=F,B
        else: continue
        mB=PR[B]; mF=PR[F]
        if mB==B or mF==F: continue
        tot+=1
        vF=VC[F]; vB=VC[B]
        if not lt_term(mB,mF): m1f+=1
        # M5: olt mB F  (proj y B strictly below the larger image F)
        if not lt_term(mB,F):
            m5f+=1
            if len(exM5)<5: exM5.append((y,mB,F))
        # M6: F<=mF  (viol crit => not olt mF F)
        if lt_term(mF,F): m6f+=1
        # S2
        if not any(lt_term(mB,g) for g in vF): s2f+=1
        # M4: every gb in vB dominated by some gf in vF
        if not all(any(le_term(gb,gf) for gf in vF) for gb in vB): m4f+=1
print(f'FF pairs={tot}')
print(f'M1 olt mB mF FAIL          = {m1f}')
print(f'M5 olt mB F  FAIL (mB<F)   = {m5f}   <-- if 0: KEY decomposition')
print(f'M6 olt mF F (should never) = {m6f}')
print(f'S2 exists viol g of F: olt mB g FAIL = {s2f}')
print(f'M4 vB dominated by vF FAIL = {m4f}')
for y,mB,F in exM5[:4]:
    print('  M5FAIL y=%d mB=%s F=%s'%(y,fmtb(mB),fmtb(F)))
print('DONE')
