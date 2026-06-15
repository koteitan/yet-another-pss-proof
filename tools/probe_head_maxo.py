#!/usr/bin/env python3
"""For firing arg-zone image X = P 1 hb hc (lead=1, y=0):
 violators V = filter (not olt g X) (Glist 0 X).  hb = first of Glist0X (=harg X).
 We proved S5: proj 0 hb = hb (hb stable).  R1a: proj 0 X = hb.
 To get proj 0 X = hb structurally via proj_once + maxo:
   proj 0 X = proj 0 (maxo (hd V) (tl V)).  We need maxo(...)=hb AND proj 0 hb=hb.
 So check M1: maxo (hd V) (tl V) == hb   (the selected max violator is hb).
 Equivalent: hb is the LARGEST violator (>= all others). Check M2: all g in V: ole g hb.
 Also hd V == hb? (since Glist starts with hb and hb is a violator, filter keeps it first).
   Check M3: hd V == hb.
 And M2 strong form: maxo over V = hb regardless of order, since hb in V and hb>=all.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
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
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
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
    B=NT(aM)
    if B in seen: continue
    seen.add(B); imgs.append(B)
nfire=0; m1=0; m2=0; m3=0
for X in imgs:
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X)
    V=[g for g in Glist(0,X) if not lt_term(g,X)]
    if not V: continue
    if maxo(V[0],V[1:])!=hb: m1+=1
    if any(lt_term(hb,g) for g in V): m2+=1   # some violator > hb -> bad
    if V[0]!=hb: m3+=1
print(f'firing images={nfire}')
print(f'M1 maxo(hd V)(tl V) != hb = {m1} (want 0)')
print(f'M2 exists g in V, olt hb g = {m2} (want 0: hb is the max violator)')
print(f'M3 hd V != hb             = {m3} (want 0: head is first violator)')
print('DONE')
