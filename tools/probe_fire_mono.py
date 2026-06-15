#!/usr/bin/env python3
"""Is firing monotone on the arg-zone image class? olt B F & B fires => F fires?
(This is what makes the FN case empty.) Also test the contrapositive cleanly.
And test a possible MECHANISM: B fires => exists viol crit g of B; is that g
(or a transported one) a viol crit of F? If F doesn't fire, all crits g of F
have olt g F; but we have olt B F and B's violating crit gB (not olt gB B).
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G
from fast_pss import oper
def projlist(a,x): return [g for g in G(a,x) if not lt_term(g,x)]
def fires(a,x): return len(projlist(a,x))>0
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
from collections import defaultdict
byY=defaultdict(list); seen=defaultdict(set)
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if not aM: continue
    B=NT(aM)
    if B in seen[y]: continue
    seen[y].add(B); byY[y].append(B)
cap=300
tot=0; FN=0; exFN=[]
for y,L in byY.items():
    if len(L)>cap: L=random.sample(L,cap)
    FR={}
    for B in L:
        if B not in FR: FR[B]=fires(y,B)
    for B,F in itertools.combinations(L,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): B,F=F,B
        else: continue
        tot+=1
        if FR[B] and not FR[F]:
            FN+=1
            if len(exFN)<6: exFN.append((y,B,F))
print(f'arg-zone olt pairs = {tot}')
print(f'FN (smaller B fires, larger F does NOT) = {FN}  (0 => firing monotone)')
for y,B,F in exFN[:6]: print('  FN y=%d %s <o %s'%(y,fmtb(B),fmtb(F)))
print('DONE')
