#!/usr/bin/env python3
"""Soundness gate for the SHARP residual that the rebuilt witness lemma uses.

On the arg-zone ST-image class (B=NT(aM), F=NT(aN), y=0, olt B F, B fires):
  AUX1 (F fires):           pfire y F                       -- count fails
  AUX2 (strict dominance):  olt (proj y B) (proj y F)       -- count fails
These two TOGETHER let the witness lemma pick g' = proj y F:
  g'=proj y F in G(y,F) and not olt g' F  (because F fires => proj y F is a
   viol crit, by proj_once+maxo_in), and olt (proj y B) g' = AUX2.
Report 0/0 on the deep arg-zone closure.
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
cap=400
tot=0; aux1f=0; aux2f=0; ex=[]
for y,L in byY.items():
    if len(L)>cap: L=random.sample(L,cap)
    PR={}; FR={}
    for B in L:
        PR[B]=proj(y,B); FR[B]=fires(y,B)
    for B,F in itertools.combinations(L,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): B,F=F,B
        else: continue
        if not FR[B]: continue   # B must fire
        tot+=1
        if not FR[F]:
            aux1f+=1
        if not lt_term(PR[B],PR[F]):
            aux2f+=1
            if len(ex)<3: ex.append((y,B,F))
print(f'arg-zone firing pairs = {tot}')
print(f'AUX1 (F fires) FAIL              = {aux1f}')
print(f'AUX2 olt (proj y B)(proj y F) FAIL = {aux2f}')
for y,B,F in ex[:3]:
    print('  y=%d B=%s'%(y,fmtb(B))); print('       F=%s'%fmtb(F))
print('DONE')
