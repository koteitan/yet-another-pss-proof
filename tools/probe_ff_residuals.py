#!/usr/bin/env python3
"""SOUNDNESS GATE for the two residuals the green proof of argzone_fire_FF rests on.

Class: B=NT(aM), F=NT(aN) arg-zone ST images, y=0 (ST head val).
Residual R1 (argzone_proj_head):  X firing arg-zone image =>
     proj 0 X = harg X   AND   not olt (harg X) X.
   gate: over ALL firing images, count fails.
Residual R2 (argzone_fire_transport): olt B F, B fires (both arg-zone) =>
     not olt (harg F) F    (F head-viol => F fires)
     AND  olt (harg B) (harg F).
   gate: over all firing pairs, count fails.
Also re-confirm the derived CLAUSES (clause1 pfire, clause2 AUX2) follow.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G
from fast_pss import oper
def projlist(a,x): return [g for g in G(a,x) if not lt_term(g,x)]
def fires(a,x): return len(projlist(a,x))>0
def proj(a,x):
    bb=x
    while True:
        bad=projlist(a,bb)
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
def NT(S): return nrm(conv(translate(list(S))))
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
from collections import defaultdict
byY=defaultdict(list); seen=defaultdict(set)
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if not aM: continue
    B=NT(aM)
    if B in seen[y]: continue
    seen[y].add(B); byY[y].append(B)
# R1 over all firing images
r1a=r1b=0; nfire=0
for y,L in byY.items():
    for X in L:
        if not fires(y,X): continue
        nfire+=1
        aX=harg(X)
        if proj(y,X)!=aX: r1a+=1
        if lt_term(aX,X): r1b+=1
print(f'firing images = {nfire}')
print(f'R1a proj y X != harg X        = {r1a}')
print(f'R1b olt (harg X) X (not viol) = {r1b}')
# R2 + clauses over firing pairs
cap=400; tot=0; r2a=r2b=0; c1=c2=0
for y,L in byY.items():
    if len(L)>cap: L=random.sample(L,cap)
    FR={X:fires(y,X) for X in L}; PR={X:proj(y,X) for X in L}
    for B,F in itertools.combinations(L,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): B,F=F,B
        else: continue
        if not FR[B]: continue
        tot+=1
        aB=harg(B); aF=harg(F)
        if lt_term(aF,F): r2a+=1     # F NOT head-viol
        if not lt_term(aB,aF): r2b+=1
        # derived clause1: F fires
        if not FR[F]: c1+=1
        # derived clause2
        if not lt_term(PR[B],PR[F]): c2+=1
print(f'firing pairs = {tot}')
print(f'R2a F NOT head-viol           = {r2a}')
print(f'R2b not olt (harg B)(harg F)  = {r2b}')
print(f'CLAUSE1 F nofire (derived)    = {c1}')
print(f'CLAUSE2 AUX2 fail (derived)   = {c2}')
print('DONE')
