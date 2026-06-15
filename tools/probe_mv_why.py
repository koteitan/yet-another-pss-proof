#!/usr/bin/env python3
"""WHY is harg X the max violator? Probe structural relations.
For firing arg-zone X, hb=harg X, X=P a hb hc (a=lead X=1 typically).
For each violator g in Gterm 0 X, g!=hb:
 hypotheses to test (want all-true on every g, i.e. 0 failures):
  H_ole   : g <=o hb               (g is olt-below-or-eq hb)  [the maximality]
  H_in_hb : g in Gterm 0 hb  OR  g == hb   (every violator lives inside hb's G_0 tree)
  H_sub   : g is a subterm of hb (occurs in hb)
 Also: is hb the FIRST element of Glist 0 X always? (head_first)
 And: relationship lead a (=lead X) to lead hb. (firing: a<lead hb expected)
 Key alt: maybe every violator g has g in Gterm 0 X means g sits either in hb's
   subtree (Gterm 0 hb U {hb}) or in hc's subtree (Gterm 0 hc). Check split:
   ng_in_hb, ng_in_hc, ng_in_both, ng_neither.
 For g in hc-part that is a violator: is it <o hb? (the cross-spine domination)
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
def leadof(x): return 0 if x==() else x[0][1]
def subterms(x):
    s=set()
    def go(t):
        s.add(t)
        if t!=():
            go(t[0][2]); go(tuple(t[1:]))
    go(x); return s
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
H_ole_fail=0; H_in_hb_fail=0; H_sub_fail=0; head_first_fail=0
ng_in_hb=0; ng_in_hc=0; ng_in_both=0; ng_neither=0
hc_viol_total=0; hc_viol_not_olt_hb=0
for X in imgs:
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X); hc=hc_of(X)
    gl=Glist(0,X)
    if gl and gl[0]!=hb: head_first_fail+=1
    Ghb=Gset(0,hb)|{hb}
    Ghc=Gset(0,hc)
    subhb=subterms(hb)
    for g in Gset(0,X):
        if lt_term(g,X): continue
        if g==hb: continue
        # H_ole
        if not (lt_term(g,hb) or g==hb): H_ole_fail+=1
        # H_in_hb
        if g not in Ghb: H_in_hb_fail+=1
        # H_sub
        if g not in subhb: H_sub_fail+=1
        inhb = g in Ghb; inhc = g in Ghc
        if inhb and inhc: ng_in_both+=1
        elif inhb: ng_in_hb+=1
        elif inhc:
            ng_in_hc+=1
            hc_viol_total+=1
            if not lt_term(g,hb): hc_viol_not_olt_hb+=1
        else: ng_neither+=1
print(f'firing images = {nfire}')
print(f'head_first  Glist0 X starts with hb fails = {head_first_fail} (want 0)')
print(f'H_ole   every violator g!=hb has g <=o hb = {H_ole_fail} (want 0)')
print(f'H_in_hb every violator g in Gterm0 hb U hb = {H_in_hb_fail} (want 0)')
print(f'H_sub   every violator g is subterm of hb  = {H_sub_fail} (want 0)')
print(f'split: in_hb={ng_in_hb} in_hc={ng_in_hc} both={ng_in_both} neither={ng_neither}')
print(f'hc-part violators total={hc_viol_total}, of those NOT olt hb = {hc_viol_not_olt_hb}')
print('DONE')
