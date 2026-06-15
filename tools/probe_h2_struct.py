#!/usr/bin/env python3
"""H2 transport structure. Pairs B=NT(aM), F=NT(aN), y=0, olt B F, B fires.
Conclusions wanted: (1) not olt (harg F) F ; (2) olt (harg B)(harg F).
Probe relations to find the minimal residual:
 Both B,F have lead==1 when firing? B fires => lead B==1 (S1). F lead?
 leadB=B[0][1], leadF=F[0][1].
 R-leadeq: when olt B F and B fires, is leadB==leadF==1?  count leadF!=1.
 Given X=P 1 hb hc, olt B F with leadB=leadF=1 reduces (olt def) to:
    olt B F  <=>  olt hb hf  OR (hb==hf and olt hcB hcF).
 So olt(hargB)(hargF)=olt hb hf.  Is it implied by olt B F + something?
 Check D1: olt B F & B fires => olt hb hf  (clause2 direct).  count fail.
 Check D2: olt B F & B fires => not olt hf F (clause1).  count fail.
 Check D3: does clause2 (olt hb hf) + F-fires => clause1? i.e is F firing
    equivalent to not olt hf F? (that's residual B for F).  So if F fires
    then clause1 holds by residual B.  Need: F fires.
    Check Dfire: olt B F & B fires => F fires.  count fail.
 Check D4: hb fires? no (S5).  hf fires?  For clause structure: is hf a
    'stable' violator of F?  i.e proj0 hf == hf?  count fail.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from fast_pss import oper
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def fires(a,x): return any(not lt_term(g,x) for g in Glist(a,x))
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
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
seen=set(); imgs=[]
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    aM=tuple(takeW(M[1:]))
    if not aM: continue
    B=NT(aM)
    if B in seen: continue
    seen.add(B); imgs.append(B)
FR={X:fires(0,X) for X in imgs}
cap=600
L=[X for X in imgs]
if len(L)>cap: L=random.sample(L,cap)
tot=0; leadF_ne1=0; d1=0; d2=0; dfire=0; clause2_implies1=0
for B,F in itertools.combinations(L,2):
    if lt_term(B,F): pass
    elif lt_term(F,B): B,F=F,B
    else: continue
    if not FR[B]: continue
    tot+=1
    hb=harg(B); hf=harg(F)
    if leadof(F)!=1: leadF_ne1+=1
    if not lt_term(hb,hf): d1+=1
    if lt_term(hf,F): d2+=1   # clause1: not olt hf F -> fail if olt hf F
    if not FR[F]: dfire+=1
    # D3 check: if clause2 (olt hb hf) holds and F fires then clause1 by residualB-on-F
    if lt_term(hb,hf) and FR[F] and lt_term(hf,F): clause2_implies1+=1
print(f'firing pairs (sampled) = {tot}')
print(f'leadF != 1               = {leadF_ne1}')
print(f'D1 NOT olt hb hf (cl2)   = {d1}  (want 0)')
print(f'D2 olt hf F (cl1 fail)   = {d2}  (want 0)')
print(f'Dfire F does NOT fire    = {dfire}  (want 0: F fires)')
print(f'cl2&Ffire&cl1fail        = {clause2_implies1}')
print('DONE')
