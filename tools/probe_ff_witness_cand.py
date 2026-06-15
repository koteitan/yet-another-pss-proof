#!/usr/bin/env python3
"""Search for a STRUCTURAL, provable witness g' of F (firing case).
Need: g' in G(y,F), not olt g' F, and olt (proj y B) g'.

Candidates tested:
 C1: g' = proj y F  (== maxo of vF). This makes witness == goal (circular) but
     test the count to confirm it always works (sanity).
 C2: g' = max over vF (violating crits of F) by lt_term  (same as C1 essentially).
 C3: among violating crits g of F, ANY with olt mB g  (= S2; the existence form).
 C4: g' = the FIRST violating crit of F in Glist order with olt mB g.
 C5: KEY structural idea: mB is itself a violating crit of B (b's own max viol).
     Is mB IN G(y,F)?  (transport of B's crit into F). count.
 C6: Is there a violating crit g of F with mB == g? (mB lands ON an F-crit)
 C7: olt mB (proj y F) directly (the parent goal) -- count vs pairs.
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
def maxo_of(lst):
    g=lst[0]
    for h in lst[1:]:
        if lt_term(g,h): g=h
    return g
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
c1f=c5_in=c5_viol=c6=c7f=0
exC7=[]
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
        vF=VC[F]
        # C1: proj y F == maxo vF and olt mB mF
        if not lt_term(mB,mF): c1f+=1
        # C7 same as C1 here
        if not lt_term(mB,mF):
            c7f+=1
            if len(exC7)<4: exC7.append((y,mB,mF))
        # C5: is mB in G(y,F)?  is mB a violating crit of F?
        GF=G(y,F)
        if mB in GF: c5_in+=1
        if mB in vF: c5_viol+=1
        # C6: does any viol crit of F equal mB
        if any(g==mB for g in vF): c6+=1
print(f'FF pairs={tot}')
print(f'C1/C7 olt mB mF FAIL = {c1f}  (proj y F as witness)')
print(f'C5 mB in G(y,F) count = {c5_in} / {tot}')
print(f'C5viol mB in vF count = {c5_viol} / {tot}')
print(f'C6 some vF==mB count  = {c6} / {tot}')
for y,mB,mF in exC7[:3]:
    print('  C7FAIL y=%d mB=%s mF=%s'%(y,fmtb(mB),fmtb(mF)))
print('DONE')
