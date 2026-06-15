#!/usr/bin/env python3
"""Final pieces for the proof route:
 route: g' = proj y F (= maxo vF, a viol crit of F). Need:
   (i)  le_term (proj y B) (proj y F)   [probe B above, 0 fail on 620k]
   (ii) proj y B != proj y F            [strictness]
 Then olt (proj y B) (proj y F)=g', and g' in G(y,F), not olt g' F. DONE.

 Test (ii) on the ARG-ZONE class (the real lemma scope) AND raw:
  N1 arg-zone: proj y B == proj y F  count (should be 0 => neq always)
  N2 raw olt B F both fire: proj y B == proj y F count
  Also reconfirm:
  P1 arg-zone: le_term (proj y B) (proj y F) fail
  P2 raw: le_term (proj y B)(proj y F) fail (B fires; if F nofire that's a problem)
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G
from fast_pss import oper
def projlist(a,x): return [g for g in G(a,x) if not lt_term(g,x)]
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
def le_term(a,b): return a==b or lt_term(a,b)
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
cap=300
tot=0; n1=0; p1f=0
exN=[]
for y,L in byY.items():
    if len(L)>cap: L=random.sample(L,cap)
    PR={}
    for B in L:
        if B not in PR: PR[B]=proj(y,B)
    for B,F in itertools.combinations(L,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): B,F=F,B
        else: continue
        mB=PR[B]; mF=PR[F]
        if mB==B or mF==F: continue   # both fire
        tot+=1
        if mB==mF:
            n1+=1
            if len(exN)<4: exN.append((y,B,F,mB))
        if not le_term(mB,mF): p1f+=1
print(f'arg-zone FF pairs = {tot}')
print(f'N1 proj y B == proj y F  = {n1}  (0 => strict neq holds)')
print(f'P1 le_term mB mF FAIL    = {p1f}')
for y,B,F,m in exN[:4]:
    print('  N1EQ y=%d B=%s F=%s m=%s'%(y,fmtb(B),fmtb(F),fmtb(m)))
print('DONE')
