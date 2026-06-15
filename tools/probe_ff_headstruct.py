#!/usr/bin/env python3
"""Understand head structure of arg-zone image X=NT(aM)=nrm(translate aM).
translate aM = P (snd(hd aM)) (..) (..).  Let v1=snd(hd aM) (subscript of 1st col).
Questions:
 Q1: lead X == v1 ?  (does ins absorb the head? i.e is lead preserved)
 Q2: for FIRING X: is v1 == 0 always? (lead X in {0,1}; fires => lead 0?)
     test lead X for firing vs nonfiring images.
 Q3: headarg X = proj v1 (nrm B') where B'=translate(arg of first col)?
 Q4: KEY: characterize firing.  fires(0,X) <=> lead X == 0 AND headarg has lead>=0(triv)?
     no.  test: fires(0,X) <=> lead X==0?  count mismatch.
     Actually head-viol <=> lead(headarg) >= lead X.  If lead X==0 then trivially
     lead(headarg)>=0 always true => head-viol always => fires.  And if lead X>=1?
     test: lead X==0 <=> fires.  (since head arg lead always>=0)
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
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
def TR(S): return conv(translate(list(S)))
def leadof(x): return -1 if x==() else x[0][1]
def headarg(x): return None if x==() else x[0][2]
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
seen=set(); imgs=[]
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    aM=tuple(takeW(M[1:]))
    if not aM: continue
    B=NT(aM)
    if B in seen: continue
    seen.add(B); imgs.append((aM,B))
q1f=0; q4f=0; nimg=0
firelead=defaultdict(int); nofirelead=defaultdict(int)
ex4=[]
for aM,X in imgs:
    nimg+=1
    v1=aM[0][1]  # snd of first pair = subscript of translate aM first principal
    # Q1: lead X == v1 (head not absorbed in nrm => lead preserved)?
    if leadof(X)!=v1: q1f+=1
    f=fires(0,X)
    lx=leadof(X)
    if f: firelead[lx]+=1
    else: nofirelead[lx]+=1
    # Q4: lead X==0 <=> fires
    if (lx==0) != f:
        q4f+=1
        if len(ex4)<4: ex4.append((fmtb(X),lx,f))
print(f'images={nimg}')
print(f'Q1 lead X != v1(=snd hd aM) = {q1f}')
print(f'Q4 (lead X==0) != fires      = {q4f}')
print(f'  firing images by lead   : {dict(firelead)}')
print(f'  nonfiring images by lead: {dict(nofirelead)}')
for e in ex4[:4]: print('  Q4fail:',e)
print('DONE')
