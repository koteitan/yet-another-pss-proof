#!/usr/bin/env python3
"""Subscript profile of hb = harg X = proj 1 (nrm arg) for firing arg-zone X.
Where do subscript-0 principals live in hb, and why are the corresponding
Gterm-0 criticals < hb?
 P0 : does hb contain a subscript-0 principal anywhere? (count images with >=1)
 SPINE0 : does the LEFTMOST spine of hb contain a subscript-0 principal?
 GAPLOC : the gap criticals g in Gterm0 hb \\ Gterm1 hb: are they all ARGUMENTS of
          subscript-0 principals NOT on the leftmost spine (i.e. buried in tails)?
 KEY candidate inductive invariant to test (want 0 fails):
   INV0: every subterm-principal P a' b' c' occurring in hb that has a'=0 (or a'< lead hb)
         satisfies: its arg b' is olt hb. (i.e. the head dominates all low-subscript args.)
   Stronger structural: hb non-firing at 0 <=> all g in Gterm0 hb : olt g hb (=T_allGhb).
 Also: is the leftmost spine of hb non-increasing in subscript and starting at lead hb=maxsub?
   (inv2-like). spine_desc.
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
def leadof(x): return 0 if x==() else x[0][1]
def principals(x):
    # all (a,b,c) principal occurrences (each suffix-head)
    out=[]
    def go(t):
        if t==(): return
        a=t[0][1]; b=t[0][2]; c=tuple(t[1:])
        out.append((a,b,c)); go(b); go(c)
    go(x); return out
def spine_subs(x):
    out=[]
    t=x
    while t!=():
        out.append(t[0][1]); t=t[0][2]
    return out
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(4):
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
nfire=0; P0=0; SPINE0=0; INV0_fail=0; spine_desc_fail=0; gap_buried=0; gap_total=0
for X in imgs:
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X); lhb=leadof(hb)
    pr=principals(hb)
    has0=any(a==0 for (a,b,c) in pr)
    if has0: P0+=1
    ss=spine_subs(hb)
    if any(a==0 for a in ss): SPINE0+=1
    # spine non-increasing & starts at lead hb
    if ss and (ss[0]!=lhb or any(ss[i+1]>ss[i] for i in range(len(ss)-1))): spine_desc_fail+=1
    # INV0: every principal with subscript < lhb has arg olt hb
    for (a,b,c) in pr:
        if a<lhb and not lt_term(b,hb): INV0_fail+=1
    G0=Gset(0,hb); G1=Gset(lhb,hb); gap=G0-G1
    gap_total+=len(gap)
print(f'firing images = {nfire}')
print(f'P0     hb contains a subscript-0 principal = {P0}')
print(f'SPINE0 hb leftmost spine has a 0-subscript = {SPINE0}')
print(f'spine_desc_fail (spine not nonincr from lead hb) = {spine_desc_fail}')
print(f'INV0  some principal subscript<lead hb with arg NOT olt hb = {INV0_fail} (want 0)')
print('DONE')
