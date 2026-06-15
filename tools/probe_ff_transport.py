#!/usr/bin/env python3
"""FF residue: find the transport handle. olt B F, both fire.
mB=proj y B = max over {g in G(y,B): not olt g B}; mF likewise for F.
Candidates:
 T1: for the chosen mB, exists g' in G(y,F) with ole mB g' AND not olt g' F
     (mB transports to a *violating* critical g' of F that dominates it).
     Then mF >= g' >= mB by maxo_ub, giving ole mB mF.
 T2: weaker: exists g' in {violating crits of F} with not olt g' mB (g' >= mB).
 T3: ole mB mF directly (goal modulo eq) -- sanity.
 T4: is mB itself ole mF? and is it strict?
Also measure: among violating criticals of F, is the MAX (=mF) always >= mB?
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G
from fast_pss import oper

def projlist(a,x):
    return [g for g in G(a,x) if not lt_term(g,x)]
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
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
def ole(a,b): return (str(a)==str(b)) or lt_term(a,b)

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

cap=300
tot=0; T1f=T2f=0; exT1=[]
for y,L in byY.items():
    if len(L)>cap: L=random.sample(L,cap)
    PR={}; VC={}
    for B in L:
        if B not in PR:
            PR[B]=proj(y,B); VC[B]=projlist(y,B)
    for B,F in itertools.combinations(L,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): B,F=F,B
        else: continue
        mB=PR[B];
        if mB==B or PR[F]==F: continue
        tot+=1
        vF=VC[F]   # violating criticals of F
        # T1: exists g' in vF with ole mB g'
        t1 = any(ole(mB,g) for g in vF)
        # T2: exists g' in vF with not olt g' mB (g' >= mB)
        t2 = any(not lt_term(g,mB) for g in vF)
        if not t1:
            T1f+=1
            if len(exT1)<5: exT1.append((y,B,F,mB,vF))
        if not t2: T2f+=1
print(f'FF pairs={tot}')
print(f'T1 (exists violating crit g of F with mB <=o g) fail={T1f}')
print(f'T2 (exists violating crit g of F with g >=o mB) fail={T2f}')
for y,B,F,mB,vF in exT1[:3]:
    print('  T1FAIL y=%d mB=%s'%(y,fmtb(mB)))
    print('         vF=',[fmtb(g) for g in vF][:6])
print('DONE')
