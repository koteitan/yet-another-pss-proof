#!/usr/bin/env python3
"""Second-stage probe: the chain that AVOIDS (MO) on non-wf3 BM.
We want  olt X Y  <=>  oV X < oV Y  (X,Y wf3) and reduce to psi-values.
Test sub-claims:
  (NM)  oV(nrm BM) < oV(nrm BN)   under hyp olt BM BN   [nrm preserves value, so = oV BM<oV BN]
  (CAN) oV(nrm BM) is y-canonical  [acanon y (oV(nrm BM))]
  (PS)  oV X < oV Y  <=>  oV(nrm BM) < oV(nrm BN)   [via psi_proj + psi strict mono]
  (NMwf) is nrm BM wf3 (in OT)?
oV proxy = valnorm.nrm.  acanon y alpha proxy: alpha is canonical at y iff
  every g in G_y(alpha-name) has value < alpha  (Buchholz OT3 at subscript y).
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
def acanon(y, alpha):   # alpha is a value-normal name; canonical at subscript y
    return all(lt_term(g, alpha) for g in G(y, alpha))

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

nNM=0; vNM=0; exNM=[]
nCAN=0; vCAN=0; exCAN=[]
nPS=0; vPS=0; exPS=[]
nNMwf=0; vNMwf=0
seen_nrmB=set()
cap=400
for y,aset in byY.items():
    al=sorted(aset)
    if len(al)>cap: al=random.sample(al,cap)
    # canonicity of oV(nrm BM) [independent of pairs]
    for aM in al:
        BM=translate(list(aM)); nB=nrm(conv(BM))
        nNMwf+=1
        if not in_OT(nB): vNMwf+=1
        nCAN+=1
        if not acanon(y, nB):
            vCAN+=1
            if len(exCAN)<5: exCAN.append((y,aM,fmtb(nB)))
    for aM,aN in itertools.permutations(al,2):
        BM=translate(list(aM)); BN=translate(list(aN))
        if not olt(BM,BN): continue
        nB=nrm(conv(BM)); nN=nrm(conv(BN))
        # (NM)
        nNM+=1
        if not lt_term(nB,nN):
            vNM+=1
            if len(exNM)<5: exNM.append((y,aM,aN))
        # (PS): oV X < oV Y  vs  oV(nrm BM)<oV(nrm BN)
        Xn=proj(y,nB); Yn=proj(y,nN)
        nPS+=1
        if lt_term(Xn,Yn) != lt_term(nB,nN):
            vPS+=1
            if len(exPS)<5: exPS.append((y,fmtb(Xn),fmtb(Yn),fmtb(nB),fmtb(nN)))

print(f"(NMwf) nrm(BM) in OT(wf3): tested={nNMwf} NOT-wf3={vNMwf}")
print(f"(CAN) oV(nrm BM) y-canonical: tested={nCAN} VIOL={vCAN}")
for e in exCAN: print("   CANVIOL",e)
print(f"(NM) oV(nrm BM)<oV(nrm BN) under hyp olt BM BN: tested={nNM} VIOL={vNM}")
for e in exNM: print("   NMVIOL",e)
print(f"(PS) [oV X<oV Y] == [oV(nrm BM)<oV(nrm BN)]: tested={nPS} VIOL={vPS}")
for e in exPS: print("   PSVIOL",e)
