#!/usr/bin/env python3
"""Soundness gate for the REDUCTION CHAIN of proj_nrm_argzone_olt.

Target: olt(proj y (nrm BM)) (proj y (nrm BN))     [BM=translate aM, BN=translate aN]
Chain (each step probed):
  (R)  reflection on wf3 X,Y:  olt X Y  <=>  oV X < oV Y    [oV_order_pres + totality]
  (PC) X=proj y(nrm BM), Y=proj y(nrm BN) are wf3 and y-canonical [proj_canonical]
  (PP) psi_proj:  psi(oV(nrm BM)) y = psi(oV X) y           [green mod psi_proj_nonmem]
  (CN) oV(nrm B) value-equals oV B (nrm preserves value)    [check]
  (MO) olt BM BN  =>  oV BM < oV BN  on ARG-ZONE translates  [NOT wf3 in general!]
  (PSY) psi a y strictly monotone on canonical a (both dirs) [psi_strict_mono_arg]

oV proxy = valnorm.nrm (value-normal form); oV order = lt_term on nrm forms.
psi alpha y proxy = the principal ('D', y, nrm-form-of-alpha); since alpha here
is itself a nrm-form value, psi alpha y proxy = ('D', y, alpha).
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

# oV proxy: value of a three-term = its value-normal name; order via lt_term
def oVname(threeterm): return nrm(conv(threeterm))
def oVlt(s,t): return lt_term(oVname(s), oVname(t))     # oV s < oV t
def oVeq(s,t): return oVname(s)==oVname(t)

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

# counters
nMO=0; vMO=0; exMO=[]          # (MO) olt BM BN => oV BM < oV BN on argzone translates
nCN=0; vCN=0                   # (CN) oV(nrm B)=oV B  (nrm B = nrm-name; trivial-ish)
nTGT=0; vTGT=0; exTGT=[]       # final target vs hypothesis
nPP=0; vPP=0; exPP=[]         # (PP-proxy) psi(oV(nrm BM)) y == psi(oV(proj y(nrm BM))) y
cap=400
for y,aset in byY.items():
    al=sorted(aset)
    if len(al)>cap:
        al=random.sample(al,cap)
    for aM,aN in itertools.permutations(al,2):
        BM=translate(list(aM)); BN=translate(list(aN))
        # hypothesis of the lemma:
        if not olt(BM,BN): continue
        # (MO): does olt BM BN imply oV BM < oV BN ?
        nMO+=1
        if not oVlt(BM,BN):
            vMO+=1
            if len(exMO)<5: exMO.append((y,aM,aN))
        # X,Y
        nB = nrm(conv(BM)); nN = nrm(conv(BN))    # value-normal names (oV of nrm B = same)
        # (PP) proxy: psi(oV(nrm BM)) y where oV(nrm BM) value = nB ; vs psi(oV(proj y nrm BM)) y
        # proj y (nrm BM): in name-space
        Xn = proj(y, nB); Yn = proj(y, nN)
        # psi alpha y proxy = ('D', y, alpha-name) as a 1-principal term
        psiBM = nrm((('D', y, nB),)); psiX = nrm((('D', y, Xn),))
        nPP+=1
        if psiBM != psiX:
            vPP+=1
            if len(exPP)<5: exPP.append((y,aM,aN,fmtb(psiBM),fmtb(psiX)))
        # (TGT) target: olt(proj y(nrm BM)) (proj y(nrm BN)) in value order = lt_term(Xn,Yn)
        nTGT+=1
        tgt = lt_term(Xn, Yn)
        if not tgt:
            vTGT+=1
            if len(exTGT)<6: exTGT.append((y,fmtb(Xn),fmtb(Yn)))

print(f"(MO) olt BM BN => oV BM<oV BN [argzone translates, maybe NOT wf3]: tested={nMO} VIOL={vMO}")
for y,aM,aN in exMO: print("   MOVIOL y=",y,"aM=",aM,"aN=",aN)
print(f"(PP) psi(oV(nrm BM)) y == psi(oV(proj y(nrm BM))) y : tested={nPP} VIOL={vPP}")
for e in exPP: print("   PPVIOL",e)
print(f"(TGT) target lt_term(proj y nrm BM, proj y nrm BN) under hyp olt BM BN: tested={nTGT} VIOL={vTGT}")
for e in exTGT: print("   TGTVIOL",e)

# Are arg-zone translates wf3 (in_OT of their nrm)?  And is BM itself in_OT?
nWF=0; notwf=0; exwf=[]
seen=set()
for y,aset in byY.items():
    for aM in aset:
        BM=translate(list(aM))
        cb=conv(BM)
        nWF+=1
        if not in_OT(cb):
            notwf+=1
            if len(exwf)<5: exwf.append(aM)
print(f"(WF) translate(argzone) already in OT(wf3): tested={nWF} NOT-wf3={notwf}")
for e in exwf: print("   notwf aM=",e)
