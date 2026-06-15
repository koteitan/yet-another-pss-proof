#!/usr/bin/env python3
"""Deep soundness gate for the NEW localized residue psi_oV_nrm_argzone_lt:
  for ST forms (0,y)#r,(0,y)#r' with arg zones aM!=aN and olt(translate aM)(translate aN):
      psi(oV(nrm(translate aM))) y  <  psi(oV(nrm(translate aN))) y
proxy: oV(.)=valnorm.nrm(conv(.));  psi alpha y = nrm(( ('D',y,alpha), )).
Also re-confirms the GREEN-derived target olt(proj y nrm aM)(proj y nrm aN).
"""
import sys, itertools, random
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000); random.seed(23)
from wfe_explore import translate, olt, enum_ST
from valnorm import conv, nrm, lt_term, G
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
def psi_y(a,y): return nrm( (('D',y,a),) )
def oVn(t): return nrm(conv(t))
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
nRES=0; vRES=0; exRES=[]
nTGT=0; vTGT=0
cap=400
for y,aset in byY.items():
    al=sorted(aset)
    if len(al)>cap: al=random.sample(al,cap)
    data=[(aM, oVn(translate(list(aM))), proj(y,nrm(conv(translate(list(aM)))))) for aM in al]
    for (aM,nB,Xn),(aN,nN,Yn) in itertools.permutations(data,2):
        BM=translate(list(aM)); BN=translate(list(aN))
        if aM==aN: continue
        if not olt(BM,BN): continue
        nRES+=1
        if not lt_term(psi_y(nB,y), psi_y(nN,y)):
            vRES+=1
            if len(exRES)<6: exRES.append((y,aM,aN))
        nTGT+=1
        if not lt_term(Xn,Yn): vTGT+=1
print(f"RES psi(oV(nrm aM))y < psi(oV(nrm aN))y : tested={nRES} VIOL={vRES}")
for e in exRES: print("   RESVIOL",e)
print(f"TGT olt(proj y nrm aM)(proj y nrm aN) [green-derived]: tested={nTGT} VIOL={vTGT}")
