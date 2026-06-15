#!/usr/bin/env python3
"""Degenerate oper branches: oper M n = M (j1=0) or = butlast M (Pred branches).
For the suffix-closure induction step we need, for any row-0 index i of N=oper(M,n),
a witness giving drop i N in ST_PS via IH on M.

Pred branch: N = butlast M. For i with N[i][0]==0 (i<len(N)=len(M)-1):
  drop i N = butlast (drop i M).  And M[i][0]==0, so drop i M in ST_PS by IH,
  and butlast(drop i M) = Pred(drop i M) when len(drop i M)>=2, hence in ST_PS via oper?
  Actually Pred is oper-of-degenerate. Better: drop i (butlast M) == butlast (drop i M).
  Then if drop i M in ST_PS (IH), is butlast(drop i M) in ST_PS? Only if it's an oper image.
  Test: drop i N == oper(drop i M, m) for some m? OR drop i N in STset.

j1=0 branch: N=M, len 1. row-0 index i: only i=0, drop 0 N = M in ST_PS (the elem itself).
"""
import sys
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import diagSeq, oper, Lng, idx1, entry, hasParent0, hasParent1, parent0, parent1
from wfe_explore import enum_ST

def oper_internal(M):
    M=list(M); j1=Lng(M)-1
    if j1==0: return ('id',)
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return ('pred',)
    i1=idx1(M,j1)
    if i1==1:
        if not hasParent1(M,j1): return ('pred',)
        j0=parent1(M,j1)
    else:
        if not hasParent0(M,j1): return ('pred',)
        j0=parent0(M,j1)
    return ('tile',j0,j1)

ST=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=16,rounds=9))
STset=set(ST)
print('corpus',len(ST),flush=True)

# Pred branch analysis
pred_tot=0; pred_drop_commute_bad=0; pred_S_in=0; pred_oper_wit=0; predfail=[]
id_tot=0
for M in ST:
    if Lng(M)<=1:
        continue
    info=oper_internal(M)
    for n in (1,2,3):
        N=oper(list(M),n)
        if info[0]=='tile': continue
        if info[0]=='id':
            id_tot+=1; continue
        # pred
        for i in range(len(N)):
            if N[i][0]!=0: continue
            pred_tot+=1
            # commutation drop i (butlast M) == butlast(drop i M)?
            lhs=tuple(N[i:]); rhs=tuple(list(M[i:])[:-1])
            if lhs!=rhs: pred_drop_commute_bad+=1
            S=tuple(N[i:])
            if S in STset: pred_S_in+=1
            # is S an oper image of drop i M?
            dM=list(M[i:])
            hit=False
            for m in (1,2,3):
                if Lng(dM)>1 and tuple(oper(dM,m))==S: hit=True; break
            if hit: pred_oper_wit+=1
            elif len(predfail)<15: predfail.append((M,n,i,S,dM))
print(f'PRED tot={pred_tot} drop-commute-bad={pred_drop_commute_bad} S_in_corpus={pred_S_in} oper_witness={pred_oper_wit}')
print(f'  no oper witness: {len(predfail)}')
for e in predfail[:15]:
    M,n,i,S,dM=e
    print('  PF M=',M,'n=',n,'i=',i,'S=',S,'dropiM=',dM)
print(f'ID-branch steps={id_tot}')
print('DONE',flush=True)
