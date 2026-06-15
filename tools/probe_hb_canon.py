#!/usr/bin/env python3
"""On the firing arg-zone class: is hb=harg X itself 0-canonical (proj 0 hb == hb)?
If yes, tied_crit_lt_hb is IMMEDIATE from proj_G.
Also check: does proj 0 hb == hb hold? does Gterm 0 hb have ANY violator of hb?
(i.e. is hb a fixed point of proj 0). Report counts.
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
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
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
def fires(a,x): return any(not lt_term(g,x) for g in Glist(a,x))
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
seen=set(); imgs=[]
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    aM=tuple(takeW(M[1:]))
    if not aM: continue
    X=NT(aM)
    if X in seen: continue
    seen.add(X); imgs.append(X)
print('distinct images=',len(imgs))
nfire=0
hb_not_canon0=0     # proj 0 hb != hb  (want 0 if V5 route works)
hb_fires0=0         # hb fires at 0
ex=[]
for X in imgs:
    if X==(): continue
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X)
    if hb==(): continue
    if fires(0,hb): hb_fires0+=1
    p0=proj(0,hb)
    if p0!=hb:
        hb_not_canon0+=1
        if len(ex)<8: ex.append((X,hb,p0))
print(f'firing images = {nfire}')
print(f'hb fires at 0 (some Gterm0 hb violates hb)      = {hb_fires0}')
print(f'proj 0 hb != hb (NOT 0-canonical)               = {hb_not_canon0}  (0 => V5 route, immediate from proj_G)')
for (X,hb,p0) in ex:
    print(' X=',X)
    print('  hb=',hb)
    print('  proj0 hb=',p0)
print('DONE')
