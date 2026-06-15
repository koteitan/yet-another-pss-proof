#!/usr/bin/env python3
"""Probe the WRAPPING route to reduce proj_nrm_argzone_olt to oV_mono_NF.
Wrap aM as NM=translate((0,y)#aM) in NF.  oV NM = psi(oV BM) y where BM=translate aM.
Links to probe (oV proxy = valnorm.nrm; psi alpha y proxy = ('D',y,alpha-name)):
  (W1) olt NM NN  <=>  olt BM BN                         [structural, should be trivial]
  (W2) psi(oV BM) y == psi(oV(nrm BM)) y  (nrm preserves head psi-value)
       i.e. nrm(('D',y, conv(BM)-as-value)) == nrm(('D',y, nrm(conv(BM))))
  (W3) psi(oV BM) y == psi(oV(proj y(nrm BM))) y == psi(oV p) y   [via psi_proj + W2]
  (W4) the full bridge: oV NM < oV NN  <=>  oV p < oV p'
       where oV NM proxy = nrm(('D',y, conv(BM)))  and oV p = proj(y, nrm(conv(BM)))
"""
import sys, itertools, random
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000); random.seed(23)
from wfe_explore import translate, olt, enum_ST
from valnorm import conv, nrm, lt_term, G, in_OT, fmtb
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
for _ in range(4):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=20 and tt not in extra:
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

# oV proxy of three-term t = nrm(conv(t)); psi alpha y proxy = nrm(( ('D',y, alpha), ))
def oVc(t): return nrm(conv(t))            # value-name of three-term
def psi_y(alpha_name, y): return nrm( (('D', y, alpha_name),) )

nW2=0; vW2=0; exW2=[]
nW4=0; vW4=0; exW4=[]
cap=350
for y,aset in byY.items():
    al=sorted(aset)
    if len(al)>cap: al=random.sample(al,cap)
    data=[]
    for aM in al:
        BM=translate(list(aM))
        vBM=oVc(BM)               # oV(translate aM)  value-name
        nB=nrm(conv(BM))          # = oVc(BM) actually (nrm of name) ; oV(nrm BM) value
        Xn=proj(y,nB)             # proj y (nrm BM)
        # (W2): psi(oV BM) y == psi(oV(nrm BM)) y ?
        nW2+=1
        if psi_y(vBM,y) != psi_y(nB,y):
            vW2+=1
            if len(exW2)<5: exW2.append((y,fmtb(vBM),fmtb(nB)))
        data.append((aM,vBM,Xn))
    for (aM,vBM,Xn),(aN,vBN,Yn) in itertools.permutations(data,2):
        # oV NM proxy = psi(oV BM) y = psi_y(vBM,y); oV p = Xn (value-name of proj)
        oNM=psi_y(vBM,y); oNN=psi_y(vBN,y)
        nW4+=1
        # (W4): [oV NM < oV NN] == [oV p < oV p']
        if lt_term(oNM,oNN) != lt_term(Xn,Yn):
            vW4+=1
            if len(exW4)<6: exW4.append((y,fmtb(oNM),fmtb(oNN),fmtb(Xn),fmtb(Yn)))
print(f"(W2) psi(oV BM) y == psi(oV(nrm BM)) y : tested={nW2} VIOL={vW2}")
for e in exW2: print("   W2VIOL",e)
print(f"(W4) [oV NM<oV NN] == [oV p<oV p'] : tested={nW4} VIOL={vW4}")
for e in exW4: print("   W4VIOL",e)
