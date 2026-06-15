#!/usr/bin/env python3
"""Does transport reduce to maxsub-monotonicity on arg-zone images?
B,F arg-zone images, olt B F, B fires.
 T1: maxsub B <= maxsub F  (olt B F)   [arg-zone]
 T2: lead F == lead B (both =1 when fire) ... but F may not be known to fire yet.
 Tfire-derive: from maxsub B<=maxsub F and lead F<=... can we get F fires?
   F fires <=> lead F < maxsub F. We know B fires => 1=lead B<maxsub B<=maxsub F.
   And lead F: olt B F => lead B<=lead F. If lead F==1 then 1<maxsub F => F fires. But lead F could be >1!
   Check: when B fires & olt B F, is lead F < maxsub F always (F fires)? (= argzone_F_fires) [known 0]
 Tord: olt(harg B)(harg F). harg=proj0. Check via maxsub: is it olt(proj0 B)(proj0 F)?
   And does maxsub B < maxsub F  OR (maxsub B==maxsub F AND ...) drive it?
 Also key: T1strict: when B fires & olt B F, is maxsub B <= maxsub F with equality possible?
   and relation to proj0 ordering.
Test all on arg-zone PAIRS (both images from ST arg-zones, olt B F, B fires).
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
def maxo(x,ys):
    m=x
    for y in ys:
        if lt_term(m,y): m=y
    return m
def proj(a,x):
    bb=x
    while True:
        gs=[g for g in Glist(a,bb) if not lt_term(g,bb)]
        if not gs: break
        bb=maxo(gs[0],gs[1:])
    return bb
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
def leadof(x): return 0 if x==() else x[0][1]
def harg(x): return () if x==() else x[0][2]
def maxsub(x):
    if x==(): return 0
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    return max(a,max(maxsub(b),maxsub(c)))
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
    X=NT(aM)
    if X in seen: continue
    seen.add(X); imgs.append(X)
# precompute
fire={X:fires(0,X) for X in imgs}
ms={X:maxsub(X) for X in imgs}
import itertools
imgs2=imgs
print('images',len(imgs2))
npair=0; t1=0; tord=0; tffail=0; eqms=0; eqms_ord_fail=0
exT1=[]
# limit pairs for runtime: sample
import random
random.seed(5); random.shuffle(imgs2)
S=imgs2[:1500]
for B in S:
    if not fire[B]: continue
    for F in S:
        if B is F: continue
        if not lt_term(B,F): continue
        npair+=1
        if ms[B]>ms[F]:
            t1+=1
            if len(exT1)<3: exT1.append((B,F))
        if not fire[F]: tffail+=1
        # Tord
        hb=proj(0,B); hf=proj(0,F)
        if not lt_term(hb,hf): tord+=1
        if ms[B]==ms[F]:
            eqms+=1
            if not lt_term(hb,hf): eqms_ord_fail+=1
print(f'firing-B olt pairs sampled = {npair}')
print(f'T1 maxsub B<=maxsub F      : fails={t1}')
print(f'Tfire F fires              : fails={tffail}')
print(f'Tord olt(proj0 B)(proj0 F) : fails={tord}')
print(f'  pairs with maxsub B==maxsub F = {eqms}, ord fails among them = {eqms_ord_fail}')
for e in exT1: print('  exT1 ms', ms[e[0]], ms[e[1]])
print('DONE')
