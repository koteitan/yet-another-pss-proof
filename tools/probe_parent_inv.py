#!/usr/bin/env python3
"""Parent / nextR invariance under removing a row-0-headed prefix.

For M in ST_PS (so blockok 0) and a row-0 index p (M[p][0]==0, p<len-1), let
M' = drop p M.  The LAST column index of M' is (len M - 1) - p = j1 - p where
j1=len M-1.  Claim: the oper-relevant data of M' matches that of M shifted:
  * j1' = j1 - p
  * idx1 M' j1' == idx1 M j1
  * hasParent M' i1 j1' == hasParent M i1 j1, and parent M' i1 j1' = parent M i1 j1 - p
    (PROVIDED parent index >= p).
This is what lets oper(drop p M, m) decompose with the same block [j0-p, j1-p).

Test over the corpus for ALL row-0 prefix indices p (not just the tail zone),
restricted to p <= j0 (the green-prefix removals — these are the W1 commutation
cases) AND to p that land on a row-0 column.  Report mismatches.
"""
import sys
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import oper, Lng, idx1, entry, hasParent0, hasParent1, parent0, parent1
from wfe_explore import enum_ST

def opdata(M):
    M=list(M); j1=Lng(M)-1
    if j1==0: return ('id',)
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return ('pred',)
    i1=idx1(M,j1)
    if i1==1:
        if not hasParent1(M,j1): return ('pred',)
        return ('tile',i1,parent1(M,j1),j1)
    else:
        if not hasParent0(M,j1): return ('pred',)
        return ('tile',i1,parent0(M,j1),j1)

ST=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=16,rounds=9))
print('corpus',len(ST),flush=True)

tot=0; bad=0; ex=[]
for M in ST:
    n=Lng(M)
    if n<=1: continue
    dM_full=opdata(M)
    if dM_full[0]!='tile': continue
    _,i1,j0,j1=dM_full
    # remove row-0 prefix p with 1<=p<=j0 (green prefix), row-0 headed
    for p in range(1,n-1):
        if M[p][0]!=0: continue
        Mp=list(M[p:])
        dMp=opdata(Mp)
        tot+=1
        # expected: tile with same i1, parent j0-p, child j1-p  (only if p<=j0)
        if p<=j0:
            ok = (dMp[0]=='tile' and dMp[1]==i1 and dMp[2]==j0-p and dMp[3]==j1-p)
        else:
            # p>j0: the parent is strictly before p, removed. Different structure.
            ok = True  # not asserting; just count
            continue
        if not ok:
            bad+=1
            if len(ex)<15: ex.append((M,p,i1,j0,j1,dMp))
print(f'parent-inv (p<=j0, row0): tot={tot} bad={bad}')
for e in ex[:15]: print('  BAD',e)
print('DONE',flush=True)
