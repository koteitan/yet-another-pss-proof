#!/usr/bin/env python3
"""Test the clean structural route for clause 2:
For firing arg-zone X = P a hb hc, hb = harg X:
 S_stable : proj 0 hb == hb         (hb does NOT fire at 0; hb is 0-stable)
            <=> all g in Gterm 0 hb : olt g hb     (proj_G consequence)
 S_Ghb    : every violator g in Gterm 0 X is in insert hb (Gterm 0 hb)
            i.e. NO violator comes from the hc tail.  (already 0 from probe_mv_why)
 Combined: for violator g!=hb: g in Gterm 0 hb, and by S_stable olt g hb,
           so not olt hb g (irrefl/trans). => clause 2.
 Also test the SUFFICIENT structural facts in class-free-ish forms to see what's needed:
   T_allGhb : all g in Gterm 0 hb : olt g hb   (= S_stable, the key)
   Equivalent restatement: not pfire 0 hb.
 Also: does hc contribute Gterm 0 hc violators ever?  hc_viol.
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
def Gset(u,x): return set(Glist(u,x))
def fires(a,x): return any(not lt_term(g,x) for g in Glist(a,x))
def harg(x): return () if x==() else x[0][2]
def hc_of(x): return () if x==() else tuple(x[1:])
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
nfire=0
S_stable_fail=0     # proj 0 hb != hb
T_allGhb_fail=0     # exists g in Gterm0 hb with not olt g hb
hb_fires0=0         # hb fires at 0
S_Gviol_fail=0      # violator of X not in insert hb (Gterm0 hb)
for X in imgs:
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X)
    if proj(0,hb)!=hb: S_stable_fail+=1
    Ghb=Gset(0,hb)
    if any(not lt_term(g,hb) for g in Ghb): T_allGhb_fail+=1
    if fires(0,hb): hb_fires0+=1
    inserthbG = Ghb | {hb}
    for g in Gset(0,X):
        if lt_term(g,X): continue
        if g not in inserthbG: S_Gviol_fail+=1
print(f'firing images = {nfire}')
print(f'S_stable proj 0 hb == hb fails        = {S_stable_fail} (want 0)')
print(f'T_allGhb all g in Gterm0 hb: olt g hb fails = {T_allGhb_fail} (want 0)')
print(f'hb fires at 0 (should be 0 if stable) = {hb_fires0} (want 0)')
print(f'S_Gviol violator of X not in {{hb}}U Gterm0 hb = {S_Gviol_fail} (want 0)')
print('DONE')
