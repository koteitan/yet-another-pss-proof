#!/usr/bin/env python3
"""Verify the maxsub-spine infra lemmas for argzone_head_maxviol on the
ya-pss firing arg-zone NF image class.
X = nrm(translate aM), aM = takeWhile(0<fst) r, (0,y)#r in ST_PS.
hb = harg X.

Facts to verify (want 0 counterexamples each):
 F1   : firing X => lead X = 1
 F1lt : firing X => lead X < maxsub X        (the actual hypothesis used)
 F2   : firing X => lead hb = maxsub X       (= lead(proj 0 X), since proj0 X=hb)
 G1hb : g in Gterm 0 hb (g!=Z) => maxsub g <= maxsub X        (G1 applied at hb-subterm)
 NT   : g in Gterm 0 hb, lead g < lead hb => olt g hb         (NON-TIED part: subscript-first)
 TIED : count of g in Gterm 0 hb with lead g = lead hb        (the residual class - sister proves)
 SGv  : every violator g in Gterm 0 X (not olt g X) lies in insert hb (Gterm 0 hb)
 HB0  : every g in Gterm 0 hb : olt g hb     (hb 0-stable; the FULL claim NT+TIED give)
 maxsubX_gt1 : firing => maxsub X > 1
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
def leadof(x): return 0 if x==() else x[0][1]
def maxsub(x):
    if x==(): return 0
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    return max(a, max(maxsub(b), maxsub(c)))
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
F1=0;F1lt=0;F2=0;G1hb=0;NTf=0;TIED=0;SGv=0;HB0=0;msgt1=0
for X in imgs:
    if not fires(0,X): continue
    nfire+=1
    lx=leadof(X); ms=maxsub(X)
    hb=harg(X)
    lhb=leadof(hb)
    if lx!=1: F1+=1
    if not (lx<ms): F1lt+=1
    if lhb!=ms: F2+=1
    if ms<=1: msgt1+=1
    Ghb=Gset(0,hb)
    for g in Ghb:
        if g==(): continue
        if maxsub(g)>ms: G1hb+=1
        lg=leadof(g)
        if lg<lhb and not lt_term(g,hb): NTf+=1
        if lg==lhb: TIED+=1
        if not lt_term(g,hb): HB0+=1
    inserthbG = Ghb | {hb}
    for g in Gset(0,X):
        if lt_term(g,X): continue
        if g not in inserthbG: SGv+=1
print(f'firing images = {nfire}')
print(f'F1   firing=>lead X=1                 : fails={F1}')
print(f'F1lt firing=>lead X<maxsub X          : fails={F1lt}')
print(f'F2   firing=>lead hb=maxsub X         : fails={F2}')
print(f'msgt1 firing=>maxsub X<=1             : count={msgt1} (want 0)')
print(f'G1hb g in Gterm0 hb: maxsub g<=maxsub X: fails={G1hb}')
print(f'NT   g in Gterm0 hb, lead g<lead hb => olt g hb : fails={NTf}')
print(f'TIED g in Gterm0 hb with lead g=lead hb (residual): count={TIED}')
print(f'HB0  g in Gterm0 hb => olt g hb (full 0-stable) : fails={HB0}')
print(f'SGv  violator of X not in {{hb}}U Gterm0 hb     : fails={SGv}')
print('DONE')
