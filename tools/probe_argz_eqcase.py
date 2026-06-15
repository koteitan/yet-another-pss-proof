#!/usr/bin/env python3
"""The residual EQUALITY-case for the backward direction of (PS).
Need to rule out  oV X = oV Y  while  oV(nrm BM) < oV(nrm BN)  (X=proj y nrm BM).
Probe two things over ALL distinct arg-zone pairs at same y (NOT just olt-pairs):
  (INJ) proj y(nrm BM) value-INJECTIVE in oV(nrm BM):
        oV(nrm BM) != oV(nrm BN)  =>  oV X != oV Y   (i.e. proj-collapse never merges)
  (EQ)  oV X = oV Y  =>  oV(nrm BM) = oV(nrm BN)
  (MONO-PROJ) oV(nrm BM) < oV(nrm BN)  =>  oV X < oV Y   (full backward dir, on all pairs)
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, olt, fmt, enum_ST
from valnorm import conv, nrm, lt_term, le_term, G, in_OT, fmtb
from fast_pss import oper
Z=()
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

nINJ=0; vINJ=0; exINJ=[]
nMP=0; vMP=0; exMP=[]
cap=400
for y,aset in byY.items():
    al=sorted(aset)
    if len(al)>cap: al=random.sample(al,cap)
    # precompute
    data=[]
    for aM in al:
        BM=translate(list(aM)); nB=nrm(conv(BM)); Xn=proj(y,nB)
        data.append((aM,nB,Xn))
    for (aM,nB,Xn),(aN,nN,Yn) in itertools.permutations(data,2):
        # (INJ): nB != nN => Xn != Yn
        if nB!=nN:
            nINJ+=1
            if Xn==Yn:
                vINJ+=1
                if len(exINJ)<6: exINJ.append((y,fmtb(nB),fmtb(nN),fmtb(Xn)))
        # (MONO-PROJ): nB<nN => Xn<Yn   (full backward direction)
        if lt_term(nB,nN):
            nMP+=1
            if not lt_term(Xn,Yn):
                vMP+=1
                if len(exMP)<6: exMP.append((y,fmtb(nB),fmtb(nN),fmtb(Xn),fmtb(Yn)))
print(f"(INJ) oV(nrm BM)!=oV(nrm BN) => oV X!=oV Y: tested={nINJ} VIOL(collapse)={vINJ}")
for e in exINJ: print("   INJVIOL",e)
print(f"(MONO-PROJ) oV(nrm BM)<oV(nrm BN) => oV X<oV Y: tested={nMP} VIOL={vMP}")
for e in exMP: print("   MPVIOL",e)
