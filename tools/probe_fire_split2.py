#!/usr/bin/env python3
"""Sound firing-case split: compare ACTUAL proj y B vs proj y F directly
(NOT via the false E6_value=msfx identity). Split by firing status, and for
the FF case test whether the embedding/substructure relation Gterm y B <= Gterm y F
holds (the proj_submono premise). Goal: find the precise residual sub-statement.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST, fmt
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
def NT(S): return nrm(conv(translate(list(S))))
def Gset(u,x):
    # set of criticals
    return set(map(str,G(u,x)))

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
byY=defaultdict(list)
seen=defaultdict(set)
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if not aM: continue
    B=NT(aM)
    if B in seen[y]: continue
    seen[y].add(B)
    byY[y].append((B,aM))

cap=300
# direct: olt B F => olt (proj y B)(proj y F), partitioned by fire-status
res=defaultdict(lambda:[0,0,0])  # tag -> [pairs, rev, coll]
exR=defaultdict(list)
# also: when both fire, does Gterm y B subset Gterm y F hold? (proj_submono premise)
sub_ok=sub_no=0; exSub=[]
for y,L in byY.items():
    if len(L)>cap: L=random.sample(L,cap)
    PG={}  # cache proj and Gset per B
    for (B,aM) in L:
        if B not in PG: PG[B]=(proj(y,B), Gset(y,B))
    for (B,aM),(F,aN) in itertools.combinations(L,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): (B,aM),(F,aN)=(F,aN),(B,aM)
        else: continue
        pB,gB=PG[B]; pF,gF=PG[F]
        fB = pB!=B; fF = pF!=F
        tag = ('F' if fB else 'N')+('F' if fF else 'N')
        r=res[tag]; r[0]+=1
        if lt_term(pF,pB):
            r[1]+=1
            if len(exR[tag])<5: exR[tag].append((y,B,F,pB,pF))
        elif pB==pF: r[2]+=1
        if fB and fF:
            if gB <= gF: sub_ok+=1
            else:
                sub_no+=1
                if len(exSub)<5: exSub.append((y,B,F))
for tag in ('FF','NF','FN','NN'):
    p,rv,c=res[tag]
    print(f'({tag}) direct proj cmp: pairs={p} rev={rv} coll={c}')
for tag in ('FF','NF','FN','NN'):
    for y,B,F,pB,pF in exR[tag][:3]:
        print(f'   {tag}REV y={y}: {fmtb(B)} <o {fmtb(F)} -> proj {fmtb(pB)} vs {fmtb(pF)}')
print(f'FF Gterm-subset (proj_submono premise): ok={sub_ok} fail={sub_no}')
for y,B,F in exSub[:5]: print(f'   subFAIL y={y}: {fmtb(B)} <o {fmtb(F)}')
print('DONE')
