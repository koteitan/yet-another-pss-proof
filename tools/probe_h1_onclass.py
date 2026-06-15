#!/usr/bin/env python3
"""Does H1 (all subscripts >= 1) actually hold for the relevant source term on the class?
hb = proj y1 (nrm arg1) where translate aM = P y1 arg1 tail1, y1=lead X=1.
Candidate: arg1 (= nrm b inside) has all subscripts >= 1?  Probably NOT (snd can be 0).
So find the TRUE minimal condition that makes proj0(proj1 .)=. and holds on class.

Re-examine: we need proj0 hb = hb where hb=proj1(nrm arg1). Test directly on class:
 does (nrm arg1) satisfy 'all subscripts>=1'?  -> A_allge1
 does proj0(proj1 (nrm arg1)) == proj1(nrm arg1) hold? (=T_allGhb restated) -> T
And cross: among class images, is T always true (yes, 0 from before). Is A_allge1 always true?
If A_allge1 FALSE on class but T still true, H1 is NOT the lever for the class.

Also test refined H1': all subscripts of (proj 1 t) that are < 1... trivial.
Test H5: maxsub(t) == lead(proj 1 t) AND <stuff>.
Actually test the cleaner: H6: 'every subscript of t is >= 1 OR ...'.
Just measure A_allge1 on class.
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
def harg(x): return () if x==() else x[0][2]
def all_subs_ge1(t):
    if t==(): return True
    a=t[0][1]; b=t[0][2]; c=tuple(t[1:])
    if a<1: return False
    return all_subs_ge1(b) and all_subs_ge1(c)
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(4):
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
    X=NT(aM)
    if X in seen: continue
    seen.add(X); imgs.append(X)
nfire=0; A_hb_ge1=0; A_X_ge1=0; hb0princ=0
for X in imgs:
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X)
    if all_subs_ge1(hb): A_hb_ge1+=1
    if all_subs_ge1(X): A_X_ge1+=1
print(f'firing images = {nfire}')
print(f'hb has all subscripts >= 1 = {A_hb_ge1} / {nfire}')
print(f'X  has all subscripts >= 1 = {A_X_ge1} / {nfire}')
print('=> if hb all>=1 always, H1 cannot apply to hb (hb has 0-subs). Check.')
print('DONE')
