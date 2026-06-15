#!/usr/bin/env python3
"""Soundness gate for the TERM-LEVEL core proj_nrm_argzone_olt:
   for ST forms (0,y)#r, (0,y)#r' with arg zones aM != aN and
   olt (translate aM) (translate aN):
       olt (proj y (nrm (translate aM))) (proj y (nrm (translate aN)))
Tests the EXACT pairs the proof faces: same head subscript y, both arg zones
of depth-0 ST forms, projected at that y.  Deep closure +5.
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

# collect arg zones grouped by head subscript y
from collections import defaultdict
byY=defaultdict(set)
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if aM: byY[y].add(aM)

tot=0; rev=0; coll=0; exR=[]; exC=[]
cap=300
for y,S in byY.items():
    S=list(S)
    if len(S)>cap: S=random.sample(S,cap)
    Bs=[(a, conv(translate(list(a)))) for a in S]
    for (aM,B),(aN,F) in itertools.combinations(Bs,2):
        if lt_term(B,F): lo,hi,alo,ahi=B,F,aM,aN
        elif lt_term(F,B): lo,hi,alo,ahi=F,B,aN,aM
        else: continue
        if alo==ahi: continue
        tot+=1
        pl=proj(y,nrm(lo)); ph=proj(y,nrm(hi))
        if lt_term(ph,pl):
            rev+=1
            if len(exR)<6: exR.append((y,lo,hi))
        elif pl==ph:
            coll+=1
            if len(exC)<6: exC.append((y,lo,hi))
print(f'CORE proj_nrm_argzone_olt: ordered pairs={tot} reversals={rev} collapses={coll}',flush=True)
for y,lo,hi in exR: print(f'  REV y={y}: {fmtb(lo)} <o {fmtb(hi)} -> {fmtb(proj(y,nrm(lo)))} vs {fmtb(proj(y,nrm(hi)))}')
for y,lo,hi in exC: print(f'  COLL y={y}: {fmtb(lo)} <o {fmtb(hi)}')
print('DONE',flush=True)
