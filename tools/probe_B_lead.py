#!/usr/bin/env python3
"""For firing arg-zone image X = P a hb hc (a=lead X=1).  hb=harg X.
B says: not olt hb X.  Investigate WHY structurally.
 leadhb = lead hb.  cases:
  - leadhb > a  => olt hb X is False immediately (since olt needs leadhb<a or ...). GOOD.
  - leadhb == a => olt hb X could be True via olt (harg hb) hb.  Need to check this case.
 Count for firing X:  how many have leadhb>a (strict), leadhb==a, leadhb<a.
 For leadhb==a cases, check whether olt hb X actually holds (would break B) -> must be 0.
 Also: is wf3 X true? (should be, nrm image). Then wf3 gives forall g in Gterm a hb. olt g hb.
   Note Gterm a hb with a=1. harg hb in Gterm a hb if a<=leadhb. If leadhb==a then yes
   harg hb in Gterm a hb so olt (harg hb) hb by wf3 => that's exactly olt b' hb => olt hb X True!
   So leadhb==a MUST be impossible for firing (else B breaks). Verify cnt_eq among firing.
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
def leadof(x): return -1 if x==() else x[0][1]
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
nf=0; gt=0; eq=0; lt=0; eq_breakB=0
for X in imgs:
    if not fires(0,X): continue
    nf+=1
    a=leadof(X); hb=harg(X); lh=leadof(hb)
    if lh>a: gt+=1
    elif lh==a:
        eq+=1
        if lt_term(hb,X): eq_breakB+=1
    else: lt+=1
print(f'firing images={nf}')
print(f'lead hb >  a : {gt}')
print(f'lead hb == a : {eq}')
print(f'lead hb <  a : {lt}')
print(f'  (eq cases where olt hb X i.e. B breaks): {eq_breakB}')
print('DONE')
