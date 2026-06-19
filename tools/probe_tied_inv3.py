#!/usr/bin/env python3
"""Test SUFFICIENT + (hopefully) PROVABLE invariants for tied_crit_lt_hb.

For firing arg-zone image X, hb=harg X, L=lead hb=maxsub hb.

INV-PROJL  : proj L hb == hb   (hb is proj-canonical at its OWN lead level L)
INV-PROJ0  : proj 0 hb == hb   (hb is proj-canonical at 0 -- the goal's content, circular but check truth)
Sufficiency tests on RANDOM wf3 t with maxsub==lead:
  S-PROJL : wf3 t & maxsub t==lead t & proj (lead t) t == t  ==> all tied G0 crit < t ?
  S-PROJ0 : wf3 t & proj 0 t == t                            ==> all tied G0 crit < t ?
Class-essential check on the wf3 cex D2(D1(D2(D2+D2+D2))).
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term as olt
from fast_pss import oper
import valnorm

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

# find proj in valnorm
proj = getattr(valnorm,'proj',None)
print('valnorm has proj:', proj is not None)
if proj is None:
    # implement proj from spec
    def maxo(lst):
        m=lst[0]
        for x in lst[1:]:
            if olt(m,x): m=x
        return m
    def proj(u,t):
        while True:
            gs=[g for g in Glist(u,t) if not olt(g,t)]
            if not gs: return t
            t=maxo(gs)

# wf3
def hdle(x,y):
    if x==(): return True
    if y==(): return False
    a,e=x[0][1],y[0][1]
    if a<e: return True
    if a==e:
        bx,by=x[0][2],y[0][2]
        return olt(bx,by) or bx==by
    return False
def wf3(x):
    if x==(): return True
    a=x[0][1];b=x[0][2];c=tuple(x[1:])
    return wf3(b) and wf3(c) and all(olt(g,b) for g in Glist(a,b)) and hdle(c,(('D',a,b),))

sum3=(('D',2,()),('D',2,()),('D',2,()))
cex=(('D',2,((('D',1,((('D',2,sum3),)),)),)),)

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

nfire=0; f_projL=0; f_proj0=0
exL=None; ex0=None
for X in imgs:
    if X==(): continue
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X)
    if hb==(): continue
    L=leadof(hb)
    if proj(L,hb)!=hb:
        f_projL+=1
        if exL is None: exL=hb
    if proj(0,hb)!=hb:
        f_proj0+=1
        if ex0 is None: ex0=hb
print('firing images =',nfire)
print('INV-PROJL fails (proj L hb != hb) =',f_projL,' (want 0)')
print('INV-PROJ0 fails (proj 0 hb != hb) =',f_proj0,' (want 0; equals goal)')
print('  cex INV-PROJL:', proj(leadof(cex),cex)==cex, '(want False to be class-essential)')
print('  cex INV-PROJ0:', proj(0,cex)==cex, '(want False)')
if exL: print('  PROJL fail ex hb=',exL)
print('DONE',flush=True)
