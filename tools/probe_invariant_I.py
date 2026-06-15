#!/usr/bin/env python3
"""Investigate the standard-form invariant I for proj_nrm_argzone_olt.

Questions (deep ST closure):
  Q-nrmid:  is nrm(translate aM) == translate aM  for ST arg zones aM?
            (i.e. is the arg-zone translate already a normal form / wf3?)
  Q-projid: is proj y (nrm B) == nrm B  on arg zones? (proj a no-op)
  Q-projsub: for proj y B != B, characterize. record subscripts in B vs y.
  Q-headsub: what is the relation between the top subscripts of B and the
             collapse point y (=head subscript of the ST form)?
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST, fmt, maxsub
from valnorm import conv, nrm, lt_term, fmtb, G, in_OT
from fast_pss import oper

def proj(a,x):
    bb=x
    while True:
        bad=[g for g in G(a,bb) if not lt_term(g,bb)]
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if lt_term(g,h): g=h
        bb=g
    return bb

def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out

def topsubs(t):
    # t is conv-form: tuple of ('D',a,b)
    return [p[1] for p in t]

def allsubs(t):
    # all subscripts anywhere in conv-form
    out=[]
    for p in t:
        out.append(p[1])
        out+=allsubs(p[2])
    return out

base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(5):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=22 and tt not in extra:
                extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print('deep ST closure =',len(extra),flush=True)

from collections import defaultdict
byY=defaultdict(set)
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if aM: byY[y].add(aM)

# Q-nrmid, Q-projid, Q-headsub
n_nrmid_bad=0; n_projid_bad=0; n_total=0
ex_nrmid=[]; ex_projid=[]
topge=0; topless=0  # count whether top subs of B relate to y
maxtop_vs_y=[]
for y,S in byY.items():
    for aM in S:
        n_total+=1
        B=conv(translate(list(aM)))
        nB=nrm(B)
        if nB!=B:
            n_nrmid_bad+=1
            if len(ex_nrmid)<8: ex_nrmid.append((y,aM,B,nB))
        pB=proj(y,nB)
        if pB!=nB:
            n_projid_bad+=1
            if len(ex_projid)<8: ex_projid.append((y,aM,nB,pB))
        ts=topsubs(B)
        if ts:
            mt=max(ts)
            maxtop_vs_y.append((mt,y))

print(f'arg zones total={n_total}')
print(f'Q-nrmid  : nrm(translate aM) != translate aM  count={n_nrmid_bad}')
for y,aM,B,nB in ex_nrmid[:6]:
    print(f'    y={y} aM={aM} B={fmtb(B)} -> nrm={fmtb(nB)}')
print(f'Q-projid : proj y (nrm B)   != nrm B            count={n_projid_bad}')
for y,aM,nB,pB in ex_projid[:6]:
    print(f'    y={y} aM={aM} nB={fmtb(nB)} -> proj={fmtb(pB)}')

# Q-headsub: relation max-top-subscript of B vs y
ge=sum(1 for mt,y in maxtop_vs_y if mt>=y)
gt=sum(1 for mt,y in maxtop_vs_y if mt>y)
eq=sum(1 for mt,y in maxtop_vs_y if mt==y)
lt=sum(1 for mt,y in maxtop_vs_y if mt<y)
print(f'Q-headsub: maxtopsub(B) vs y :  > {gt}   == {eq}   < {lt}   (total {len(maxtop_vs_y)})')

# Q-allsub: all subscripts in B vs y
allge=0; alllt=0; tot_terms=0
for y,S in byY.items():
    for aM in S:
        B=conv(translate(list(aM)))
        subs=allsubs(B)
        tot_terms+=1
        if subs and max(subs)>=y: allge+=1
        else: alllt+=1
print(f'Q-allsub : exists subscript >= y in B : {allge}   all < y : {alllt}')
print('DONE')
