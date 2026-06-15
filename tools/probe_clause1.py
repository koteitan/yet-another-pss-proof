#!/usr/bin/env python3
"""Can clause 1 (harg X is a violator: not olt hb X) be derived independently?
For firing arg-zone X = P a hb hc (a=1):
 Candidate derivations (want 0 failures => the implication holds on class):
  C1a: X fires at 0  => not olt hb X        (the claim itself; R1, expect 0)
  C1b: lead hb > lead X (=a)  => not olt hb X  (lead-gap, class-free given lead hb>a)
       so really need: firing => lead hb > a. Check LG: firing => lead hb > a.
  C1c: hb = proj a (nrm arg) and X fires at 0 => lead hb > a ?
 Also test: is 'X fires at 0' equivalent to 'lead X < maxsub X' (F1), and does
  that give lead hb = maxsub X > a = lead X, i.e. lead hb > a? (the clean route!)
  LH: firing => lead hb (= maxsub X) > lead X.  If LH holds (0 fails), clause1 is
   GREEN via lead_gap_head_violator + (lead hb = maxsub X) + (lead X < maxsub X).
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
nfire=0; C1a=0; LG=0; LH=0; F1=0; lh_eq_maxsub=0
for X in imgs:
    fr=fires(0,X)
    lx=leadof(X); ms=maxsub(X)
    if fr != (lx<ms): F1+=1
    if not fr: continue
    nfire+=1
    hb=harg(X); lhb=leadof(hb)
    if lt_term(hb,X): C1a+=1            # harg X NOT a violator (bad)
    if not (lhb> lx): LG+=1            # lead hb not > lead X
    if lhb!=ms: lh_eq_maxsub+=1
    if not (lhb> lx): LH+=1
print(f'firing images = {nfire}')
print(f'F1  fires<=>lead<maxsub fails = {F1} (want 0, CLASS fact)')
print(f'C1a harg X NOT a violator (clause1 false) = {C1a} (want 0)')
print(f'LG/LH firing => lead hb > lead X fails = {LG} (want 0)')
print(f'lead hb != maxsub X = {lh_eq_maxsub} (want 0)')
print('=> If F1=0 and lead hb=maxsub X (0) then clause1 GREEN via lead-gap, BUT F1 is CLASS-essential.')
print('DONE')
