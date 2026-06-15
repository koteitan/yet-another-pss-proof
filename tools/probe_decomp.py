#!/usr/bin/env python3
"""Decompose proj y . nrm on arg zones. Test alternative orderings/factorings:
  D1: olt B F => olt (nrm B) (nrm F)        ? (nrm alone order-pres on arg trans)
  D2: olt (nrm B)(nrm F) => olt (proj y nB)(proj y nF) ? (proj on nrm-images)
  D3: proj y (nrm B) == nrm (proj y B) ?  (commute)
  D4: proj y (nrm B) == proj y B ?         (nrm redundant after proj y)
  D5: the head-stripping: is the first principal of B always D_v1 with v1>=1,
      and does proj 0 just strip it? characterize proj y action precisely.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST, fmt
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
byY=defaultdict(set)
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if aM: byY[y].add(aM)

# D3/D4: commute / redundancy (no ordering needed)
d3bad=0; d4bad=0; tot1=0
exD3=[]; exD4=[]
for y,S in byY.items():
    for aM in S:
        tot1+=1
        B=conv(translate(list(aM)))
        nB=nrm(B)
        pnB=proj(y,nB)           # proj y (nrm B)  -- the target map
        npB=nrm(proj(y,B))       # nrm (proj y B)
        pB=proj(y,B)             # proj y B
        if pnB!=npB:
            d3bad+=1
            if len(exD3)<4: exD3.append((y,aM,pnB,npB))
        if pnB!=pB:
            d4bad+=1
            if len(exD4)<4: exD4.append((y,aM,pnB,pB))
print(f'D3 proj.nrm == nrm.proj : violations={d3bad}/{tot1}')
for y,aM,a,b in exD3[:3]: print(f'   y={y} {fmtb(a)} != {fmtb(b)}')
print(f'D4 proj.nrm == proj     : violations={d4bad}/{tot1}')
for y,aM,a,b in exD4[:3]: print(f'   y={y} {fmtb(a)} != {fmtb(b)}')

# D1 / D2 on ordered pairs grouped by y
cap=300
d1bad=0; d1coll=0; d2bad=0; d2coll=0; totp=0
exD1=[]; exD2=[]
for y,S in byY.items():
    S=list(S)
    if len(S)>cap: S=random.sample(S,cap)
    Bs=[(a, conv(translate(list(a)))) for a in S]
    for (aM,B),(aN,F) in itertools.combinations(Bs,2):
        if lt_term(B,F): lo,hi=B,F
        elif lt_term(F,B): lo,hi=F,B
        else: continue
        totp+=1
        nl,nh=nrm(lo),nrm(hi)
        # D1: nrm order-pres
        if lt_term(nh,nl): d1bad+=1; exD1.append((y,lo,hi)) if len(exD1)<4 else None
        elif nl==nh: d1coll+=1
        # D2: proj on nrm-images (using nl,nh ordered? must reorder by nrm order)
        if nl==nh: continue
        if lt_term(nl,nh): plo,phi=proj(y,nl),proj(y,nh)
        else: plo,phi=proj(y,nh),proj(y,nl)
        if lt_term(phi,plo): d2bad+=1; exD2.append((y,nl,nh)) if len(exD2)<4 else None
        elif plo==phi: d2coll+=1
print(f'D1 nrm order-pres on arg trans: pairs={totp} reversals={d1bad} collapses={d1coll}')
for y,lo,hi in exD1[:3]: print(f'   REV y={y}: {fmtb(lo)} <o {fmtb(hi)}  nrm-> {fmtb(nrm(lo))} vs {fmtb(nrm(hi))}')
print(f'D2 proj y order-pres on nrm-images: pairs handled reversals={d2bad} collapses={d2coll}')
for y,nl,nh in exD2[:3]: print(f'   REV y={y}: {fmtb(nl)} <o {fmtb(nh)} proj-> {fmtb(proj(y,nl))} vs {fmtb(proj(y,nh))}')
print('DONE')
