#!/usr/bin/env python3
"""Find the class invariant that makes tied_crit_lt_hb true.
For each firing arg-zone image X, hb=harg X, L=lead hb (=maxsub hb).
For each tied critical g (g in Gterm0 hb, lead g == L), test candidate
invariants that would IMPLY olt g hb via wf3.

INV-TOP: every such g is in Gterm L hb  (critical at the TOP level L).
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term as olt
from fast_pss import oper

def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def Gset(u,x): return set(Glist(u,x))
def fires(a,x): return any(not olt(g,x) for g in Glist(a,x))
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
def maxsub(x):
    if x==(): return 0
    return max(x[0][1], max(maxsub(x[0][2]), maxsub(tuple(x[1:]))))
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
print('distinct images=',len(imgs),flush=True)

nfire=0; ntied=0
fail_top=0; fail_olt=0
ex_top=[]
for X in imgs:
    if X==(): continue
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X)
    if hb==(): continue
    L=leadof(hb)
    GLhb=Gset(L,hb)
    for g in Gset(0,hb):
        if leadof(g)!=L: continue
        ntied+=1
        if not olt(g,hb): fail_olt+=1
        if g not in GLhb:
            fail_top+=1
            if len(ex_top)<5: ex_top.append((hb,g))
print('firing images =',nfire)
print('tied criticals checked =',ntied)
print('INV-TOP fails (tied g NOT in Gterm L hb) =',fail_top,' (want 0)')
print('sanity NOT olt g hb =',fail_olt,' (want 0)')
for hb,g in ex_top:
    print('  TOPFAIL hb=',hb)
    print('          g =',g)
print('DONE',flush=True)
