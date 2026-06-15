#!/usr/bin/env python3
"""Strictness for FF: we have ole mB mF (T1+maxo_ub). Need olt mB mF.
Test:
 S0: mB == mF ever?  (expect never => then ole+neq => olt; but neq must be proved)
 S1: olt mB mF directly count (the goal)
 S2: exists violating crit g of F with olt mB g  (strict transport -> olt mB mF)
 S3: not olt mF B  (mF >= B, so if also mB ... )  -- explore
 S4: size mB < size mF ? (a cheap neq certificate)
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
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
def ole(a,b): return (a==b) or lt_term(a,b)
def sz(t):
    if isinstance(t,tuple) and len(t)==3:
        return 1+sz(t[1])+sz(t[2])
    return 1
base=enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5,6),max_len=18,rounds=9)
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
cap=600
tot=0; S0=0; S1=0; S2f=0; S4f=0; exS2=[]
for y,L in byY.items():
    if len(L)>cap: L=random.sample(L,cap)
    PR={}; VC={}
    for B in L:
        if B not in PR: PR[B]=proj(y,B); VC[B]=projlist(y,B)
    for B,F in itertools.combinations(L,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): B,F=F,B
        else: continue
        mB=PR[B]; mF=PR[F]
        if mB==B or mF==F: continue
        tot+=1
        if mB==mF: S0+=1
        if lt_term(mB,mF): S1+=1
        vF=VC[F]
        if not any(lt_term(mB,g) for g in vF): S2f+=1; (exS2.append((y,mB,vF)) if len(exS2)<4 else None)
        if not (sz(mB)<sz(mF)): S4f+=1
print(f'FF pairs={tot}')
print(f'S0 mB==mF count            = {S0}')
print(f'S1 olt mB mF (goal) count  = {S1}  (should == pairs)')
print(f'S2 exists viol crit g of F with olt mB g : fail={S2f}')
print(f'S4 size mB < size mF       : fail={S4f}')
for y,mB,vF in exS2[:3]:
    print('  S2FAIL y=%d mB=%s vF=%s'%(y,fmtb(mB),[fmtb(g) for g in vF][:5]))
print('DONE')
