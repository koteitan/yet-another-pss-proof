#!/usr/bin/env python3
"""Verify the maxsub-spine lever facts on the ya-pss arg-zone NF image class.
X = nrm(translate aM), aM = takeWhile(0<fst) r, (0,y)#r in ST_PS.
spine X = leftmost-argument subscript list; maxsub X = max subscript anywhere; cmax = max of spine.
Candidate facts (want 0 counterexamples):
 F1: pfire 0 X  <=>  lead X < maxsub X
 F1c: pfire 0 X <=>  lead X < cmax X      (cmax = max along leftmost spine only)
 F2: lead (proj 0 X) = maxsub X
 F2c: lead (proj 0 X) = cmax X
 INV2: spine X begins 0,1,...,cmax X  (the inv2 NF invariant on the spine)
 SP: maxsub X == cmax X  (is the max-subscript on the leftmost spine? probably not always)
 firing => lead X == 1 (known); maxsub X > 1 ?
Also restrict to FIRING images for F2/F2c (proj only meaningful when fires, else proj=X).
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
def fires(a,x): return any(not lt_term(g,x) for g in Glist(a,x))
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
# x is tuple of principals (dummy0, sub, arg); spine follows arg of head only
def spine(x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]
    return [a]+spine(b)
def maxsub(x):
    if x==(): return 0
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    return max(a, max(maxsub(b), maxsub(c)))
def cmax(s): return max(s) if s else 0
def inv2(s):
    cm=cmax(s)
    for i in range(cm+1):
        if i>=len(s) or s[i]!=i: return False
    return True
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
nall=len(imgs); nfire=0
f1=0;f1c=0;f2=0;f2c=0;inv2f=0;spf=0; lead_ne1=0; maxsub_le1=0
for X in imgs:
    fr=fires(0,X)
    lx=leadof(X); ms=maxsub(X); s=spine(X); cm=cmax(s)
    # F1 / F1c (unconditional equivalence)
    if fr != (lx<ms): f1+=1
    if fr != (lx<cm): f1c+=1
    # INV2 on spine
    if not inv2(s): inv2f+=1
    # SP maxsub == cmax
    if ms!=cm: spf+=1
    if fr:
        nfire+=1
        px=proj(0,X)
        if leadof(px)!=ms: f2+=1
        if leadof(px)!=cm: f2c+=1
        if lx!=1: lead_ne1+=1
        if ms<=1: maxsub_le1+=1
print(f'distinct images = {nall}, firing = {nfire}')
print(f'F1  pfire <=> lead<maxsub  : fails = {f1}')
print(f'F1c pfire <=> lead<cmax    : fails = {f1c}')
print(f'F2  lead(proj0 X)=maxsub X : fails = {f2}  (firing only)')
print(f'F2c lead(proj0 X)=cmax X   : fails = {f2c} (firing only)')
print(f'INV2 spine begins 0..cmax  : fails = {inv2f}')
print(f'SP  maxsub == cmax (spine) : fails = {spf}')
print(f'firing lead!=1             : {lead_ne1}')
print(f'firing maxsub<=1           : {maxsub_le1}')
print('DONE')
