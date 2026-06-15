#!/usr/bin/env python3
"""Verify tied_crit_lt_hb directly.
X = nrm(translate aM) firing arg-zone image, hb = harg X = arg of first principal.
For every g in Gterm 0 hb with lead g == lead hb, check: olt g hb.
Also dissect the dangerous case g==hb_b (head arg of hb) with lead hb_b == lead hb,
and report structure (does wf3 hb alone suffice, or is class needed?).
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, G
from fast_pss import oper

def Glist(u,x):
    # x is principal-list term (tuple of ('D',sub,arg))
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def Gterm_set(u,x): return set(Glist(u,x))
def fires(a,x): return any(not lt_term(g,x) for g in Glist(a,x))
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
def maxsub(x):
    if x==(): return 0
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    return max(a, max(maxsub(b), maxsub(c)))
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
n_tied_checked=0
fail_olt=0       # g in Gterm0 hb, lead g==lead hb, NOT olt g hb  (want 0)
n_g_eq_hbb=0     # g == head arg of hb, with tied lead (the dangerous self case)
hbb_tied=0       # cases where lead(hb_b)==lead(hb) i.e. would break if hb_b in Gterm0 hb tied
examples=[]
for X in imgs:
    if X==() : continue
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X); lhb=leadof(hb)
    if hb==(): continue
    hb_b=harg(hb)
    if leadof(hb_b)==lhb:
        hbb_tied+=1
        if len(examples)<10:
            examples.append(('HBB_TIED',X,hb))
    for g in Gterm_set(0,hb):
        if leadof(g)!=lhb: continue
        n_tied_checked+=1
        if g==hb_b: n_g_eq_hbb+=1
        if not lt_term(g,hb):
            fail_olt+=1
            if len(examples)<20:
                examples.append(('OLT_FAIL',X,hb,g))
print(f'firing images = {nfire}')
print(f'tied criticals g in Gterm0(hb), lead g==lead hb, checked = {n_tied_checked}')
print(f'  of these g == hb_b (head arg of hb)                     = {n_g_eq_hbb}')
print(f'FAIL: NOT olt g hb (BREAKS tied_crit_lt_hb)               = {fail_olt}  (want 0)')
print(f'cases lead(hb_b) == lead(hb) (self-head tied, danger)     = {hbb_tied}  (want 0 if class kills it)')
print('--- examples ---')
for e in examples:
    print(e[0])
    print('  X =',e[1])
    print('  hb=',e[2],' lead hb=',leadof(e[2]),' hb_b=',harg(e[2]),' lead hb_b=',leadof(harg(e[2])))
    if e[0]=='OLT_FAIL':
        print('  g =',e[3],' lead g=',leadof(e[3]),' olt g hb=',lt_term(e[3],e[2]))
print('DONE')
