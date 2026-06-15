#!/usr/bin/env python3
"""Characterize the EXACT head shape of firing arg-zone images X=nrm(translate aM).
y=0 forced.  X = P a hb hc  (a=lead=v1=snd(hd aM)).

For H1 we need: X fires (proj 0 X != X) =>
   (1) proj 0 X = harg X = hb
   (2) not olt hb X   (head arg is a violator)

KEY observations to verify and turn into a structural lemma:
 S1: firing => a==1 (lead==1).  (already: firing images all lead 1)
 S2: X = ins-result of nrm => the head principal a=lead(X). For firing, what is
     the relation between hb (=harg X = proj a' (nrm b') for original) and X?
 S3: Glist 0 X = (since 0<=a always) hb # Glist 0 hb @ Glist 0 hc.
     The violators of X (g with not olt g X) among Glist 0 X.
     CLAIM: the ONLY violator is hb itself, and proj 0 X = hb in one step
     (i.e. hb does NOT fire: proj 0 hb = hb, AND hb is the max violator).
 Check: filter (not olt g X) (Glist 0 X) == [hb]  for firing X?
 Check: not olt hb X  (hb violator) <=> a <= lead hb  i.e. lead hb >= a=1.
        Actually olt hb X = olt hb (P a hb hc). by olt def: hb<P a hb hc iff
        lead hb<a OR (lead hb=a and hb<hb..) => lead hb<a.  So not olt hb X
        <=> lead hb >= a = lead X.  i.e head arg subscript >= head subscript.
 Check S4: for firing X, is filter-violators(Glist 0 X) exactly [hb]? print dist.
 Check S5: does hb itself fire under proj 0?  (proj 0 hb == hb?)  Needed so that
        proj 0 X = proj 0 (maxo over [hb]) = proj 0 hb = hb in 'one bounce'.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G
from fast_pss import oper
def Glist(u,x):
    # returns list mirroring Isabelle Glist u (P a b c)= (if u<=a then b#Glist u b else [])@Glist u c
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def projlist(a,x): return [g for g in Glist(a,x) if not lt_term(g,x)]
def fires(a,x): return len(projlist(a,x))>0
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
def harg(x): return () if x==() else x[0][2]
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
print('distinct images=',len(imgs))
nfire=0
s1=0   # firing but lead!=1
s4=0   # firing but violators(Glist 0 X)!=[hb]
s5=0   # firing but hb fires (proj 0 hb!=hb)
s3=0   # firing but olt hb X  (hb NOT violator)
leadhb_lt_a=0
exs4=[]
for X in imgs:
    if not fires(0,X): continue
    nfire+=1
    a=leadof(X); hb=harg(X)
    if a!=1: s1+=1
    viol=[g for g in Glist(0,X) if not lt_term(g,X)]
    if viol!=[hb]:
        s4+=1
        if len(exs4)<5: exs4.append((fmtb(X),[fmtb(v) for v in viol],fmtb(hb)))
    if proj(0,hb)!=hb: s5+=1
    if lt_term(hb,X): s3+=1   # hb IS below X -> not a violator -> bad
    if leadof(hb)<a: leadhb_lt_a+=1
print(f'firing images={nfire}')
print(f'S1 firing & lead!=1            = {s1}')
print(f'S3 firing & olt hb X (hb<X)    = {s3}  (want 0: hb is violator)')
print(f'S4 firing & violators!=[hb]    = {s4}  (want 0: hb is ONLY violator)')
print(f'S5 firing & hb fires(proj!=id) = {s5}  (want 0: hb stable)')
print(f'   firing & lead hb < a=lead X = {leadhb_lt_a}  (if 0 => hb always violator)')
for e in exs4: print('  S4ex:',e)
print('DONE')
