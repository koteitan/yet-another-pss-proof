#!/usr/bin/env python3
"""Is firing(proj 0 X) related cleanly to a<lead NTK?
For arg-zone aM, X=NT(aM)=P a hb hc, NTK=NT(K).
Test equivalences over ALL distinct aM:
  E1: fires(0,X)  <=>  a < lead NTK
  E2: fires(0,X)  <=>  not olt hb X   (hb violator)
  E3: a<lead NTK  =>   fires(0,X)
  E4: fires(0,X)  =>   a<lead NTK
Also: when NOT firing, what is lead hb vs a? (should be <=a)
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term
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
def takeWc(c,r):
    out=[]
    for p in r:
        if p[0]>c[0]: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
def leadof(x): return 0 if x==() else x[0][1]
def harg(x): return () if x==() else x[0][2]
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
seen=set()
e1f=0; e3f=0; e4f=0; e2f=0
nofire_lead_hb_gt_a=0
n=0
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    aM=tuple(takeW(M[1:]))
    if not aM: continue
    if aM in seen: continue
    seen.add(aM)
    n+=1
    X=NT(aM)
    a=leadof(X); hb=harg(X)
    c=aM[0]; K=tuple(takeWc(c,aM[1:]))
    NTK=NT(K)
    f=fires(0,X)
    cond = (a < leadof(NTK))
    if f != cond: e1f+=1
    if cond and not f: e3f+=1
    if f and not cond: e4f+=1
    viol = not lt_term(hb,X)   # not olt hb X
    if f != viol: e2f+=1
    if (not f) and leadof(hb)>a: nofire_lead_hb_gt_a+=1
print(f'distinct aM = {n}')
print(f'E1 fires(0,X) <=> a<lead NTK : mismatches = {e1f}')
print(f'E3 a<lead NTK => fires        : fails = {e3f}')
print(f'E4 fires => a<lead NTK        : fails = {e4f}')
print(f'E2 fires(0,X) <=> not olt hb X: mismatches = {e2f}')
print(f'non-firing X with lead hb>a   = {nofire_lead_hb_gt_a}')
print('DONE')
