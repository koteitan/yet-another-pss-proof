#!/usr/bin/env python3
"""Dissect clause 2 of argzone_head_maxviol.
For each firing arg-zone image X = nrm(translate aM), hb = harg X.
For every g in Gterm 0 X that is a violator (not olt g X), check:
  D : not olt hb g          (the domination we must prove; want 0 failures)
  When olt hb g is FALSE, classify WHY via leads:
    lead(hb) = a' (= maxsub X claimed). lead g = e.
    Case A (strict lead gap kills it): e < a'  => olt hb g impossible by lead gap.
    Case B (tied lead, NEEDS deeper arg): e == a' .
  Count: among violators g != hb:
    nstrict = those with lead g <  lead hb   (lead-gap suffices)
    ntied   = those with lead g == lead hb   (lead-gap fails; need spine/maxsub)
    nbig    = those with lead g >  lead hb   (would BREAK; want 0)
  Also verify the maxsub levers:
    L_lead_hb : lead hb == maxsub X
    L_g_bound : maxsub g <= maxsub X (G1) for g in Gterm 0 X
  And in the TIED case, check what resolves it: is hb >=o g always (ole g hb)?
    and is it because g's arg-part is olt hb's? print a few tied examples.
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
def Gterm_set(u,x):
    # set version (dedup)
    return set(Glist(u,x))
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
Dfail=0; nstrict=0; ntied=0; nbig=0
L_lead_hb_fail=0; L_g_bound_fail=0
tied_examples=[]
tied_ole_fail=0
for X in imgs:
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X); lhb=leadof(hb); msX=maxsub(X)
    if lhb!=msX: L_lead_hb_fail+=1
    for g in Gterm_set(0,X):
        if lt_term(g,X): continue   # only violators
        if maxsub(g)>msX: L_g_bound_fail+=1
        if g==hb: continue
        # domination check
        if lt_term(hb,g):
            Dfail+=1
        lg=leadof(g)
        if lg<lhb: nstrict+=1
        elif lg==lhb:
            ntied+=1
            # in tied case is hb >=o g ? i.e. not olt hb g (already counted by D)
            # record example
            if len(tied_examples)<8:
                tied_examples.append((X,hb,g))
        else:
            nbig+=1
print(f'firing images = {nfire}')
print(f'D  exists violator g!=hb with olt hb g (BREAKS clause2) = {Dfail} (want 0)')
print(f'  violators g!=hb with lead g <  lead hb (lead-gap OK)  = {nstrict}')
print(f'  violators g!=hb with lead g == lead hb (TIED, need spine) = {ntied}')
print(f'  violators g!=hb with lead g >  lead hb (impossible?) = {nbig} (want 0)')
print(f'L_lead_hb  lead hb == maxsub X fails = {L_lead_hb_fail} (want 0)')
print(f'L_g_bound  maxsub g <= maxsub X (G1) fails = {L_g_bound_fail} (want 0)')
print('--- tied examples (X, hb, g) ---')
for (X,hb,g) in tied_examples:
    print('X=',X)
    print('  hb=',hb,' lead=',leadof(hb),' maxsub=',maxsub(hb))
    print('  g =',g,' lead=',leadof(g),' maxsub=',maxsub(g),' olt hb g=',lt_term(hb,g),' olt g hb=',lt_term(g,hb))
print('DONE')
