#!/usr/bin/env python3
"""For idx1==1 (entry M 1 j1 > 0) last columns of ST_PS forms, investigate the
nextrel1 existence witness. nextrel1 M j0 j1 exists iff
   EXISTS j. le0 M j j1 AND entry M 1 j < entry M 1 j1.
Then j0 = Max{such j}.

Probe: is the IMMEDIATE nextrel0-parent chain (le0 ancestors) of j1 guaranteed
to contain a node with smaller row-1?  Specifically, check candidate witness:
   the nextrel0-parent j0_0 of j1 (one step), then iterate.
Report: smallest #le0-steps down to a strictly-smaller row1, and whether
le0 M 0 j1 (column 0 reachable, entry 1 0 = 0 < positive).
"""
import sys
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import Lng, idx1, entry, le0, nextrel0, hasParent1, parent1
from wfe_explore import enum_ST

def le0_ancestors(M, j1):
    # all j with le0 M j j1 (j<=j1)
    return [j for j in range(j1+1) if le0(M, j, j1)]

ST = list(enum_ST(seed_max_v=6, oper_ns=(1,2,3,4,5), max_len=16, rounds=9))
print('corpus',len(ST),flush=True)
checked=0; no_witness=0; col0_reach=0; col0_works=0; ex=[]
for M in ST:
    n=Lng(M)
    if n<=1: continue
    j1=n-1
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: continue
    if idx1(M,j1)!=1: continue
    checked+=1
    e1=entry(M,1,j1)
    anc=le0_ancestors(M,j1)
    wit=[j for j in anc if entry(M,1,j)<e1]
    if not wit:
        no_witness+=1
        if len(ex)<10: ex.append(M)
    # is column 0 a le0-ancestor and does it witness?
    if le0(M,0,j1):
        col0_reach+=1
        if entry(M,1,0)<e1: col0_works+=1
print(f'idx1==1 checked={checked} NO-WITNESS={no_witness}')
print(f'  le0 M 0 j1 holds in {col0_reach}/{checked}; of those entry1[0]<e1 in {col0_works}')
for e in ex: print('  CEX',e)
print('DONE',flush=True)
