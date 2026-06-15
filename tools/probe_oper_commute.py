#!/usr/bin/env python3
"""Validate the suffix-closure induction witnesses.

For the ST_PS-induction step of suffix-closure, with N = oper(M,n) and a row-0
column index i>=1 of N (so S = N[i:] is a proper row-0-headed suffix), we want a
strictly-smaller ST_PS element M' (a row-0-headed suffix of M, hence in ST_PS by
IH) and m>=1 with S = oper(M', m) OR S a row-0 suffix already covered.

Candidate witness W1: when i <= j0 (suffix starts in green prefix take j0 M),
  S = N[i:] = drop i M ++ tiled-part. Claim: S == oper(drop i M, n), where
  drop i M is a row-0-headed suffix of M (M[i][0]==0).  TEST this equality and
  that drop i M is row-0-headed.

Candidate W2: when i > j0 (suffix starts inside the tiled region). Characterize.
"""
import sys, itertools
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import diagSeq, oper, Lng, idx1, entry, hasParent0, hasParent1, parent0, parent1
from wfe_explore import enum_ST

def oper_internal(M):
    """return (j0,j1) parent/child or None if degenerate (returns M or Pred)."""
    M=list(M); j1=Lng(M)-1
    if j1==0: return None
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return None
    i1=idx1(M,j1)
    if i1==1:
        if not hasParent1(M,j1): return None
        j0=parent1(M,j1)
    else:
        if not hasParent0(M,j1): return None
        j0=parent0(M,j1)
    return (j0,j1)

ST=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=16,rounds=9))
print('corpus',len(ST),flush=True)

w1_tot=w1_bad=0; w1ex=[]
w2_tot=0; w2_in_corpus=0; w2_oper_witness=0; w2ex=[]
STset=set(ST)
for M in ST:
    if Lng(M)<=1: continue
    info=oper_internal(M)
    for n in (1,2,3):
        N=oper(list(M),n)
        for i in range(1,len(N)):
            if N[i][0]!=0: continue
            S=tuple(N[i:])
            if info is None:
                continue
            j0,j1=info
            if i<=j0:
                w1_tot+=1
                dM=list(M[i:])
                # drop i M must be row-0-headed
                ok_head = (dM and dM[0][0]==0)
                cand=tuple(oper(dM,n)) if dM and Lng(dM)>1 else None
                if not (ok_head and cand==S):
                    w1_bad+=1
                    if len(w1ex)<8: w1ex.append((M,n,i,j0,S,cand,ok_head))
            else:
                w2_tot+=1
                if S in STset: w2_in_corpus+=1
                if len(w2ex)<8: w2ex.append((M,n,i,j0,j1,S))
print(f'W1 (i<=j0): tot={w1_tot} bad={w1_bad}',flush=True)
for e in w1ex[:6]: print('  W1bad',e)
print(f'W2 (i>j0): tot={w2_tot} in-corpus={w2_in_corpus}',flush=True)
for e in w2ex[:6]: print('  W2',e)
print('DONE',flush=True)
