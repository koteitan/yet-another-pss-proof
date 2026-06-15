#!/usr/bin/env python3
"""Where does the TAIL-ZONE of N=oper(M,n) start, relative to j0?

The tail-zone of S0=(0,y)#r is i* = index of the 2nd row-0 column of S0
(= first row-0 col after the leading argument block). For N=oper(M,n) we ask:
is i* <= j0 (so W1 commutation applies and tail-zone = oper(drop i* M,...))?
Or does the tail-zone routinely fall in the tiled region (W2)?
"""
import sys, itertools
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import diagSeq, oper, Lng, idx1, entry, hasParent0, hasParent1, parent0, parent1
from wfe_explore import enum_ST

def oper_internal(M):
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

def tailzone_idx(N):
    # N=(0,y)#r ; tail-zone start = index of 2nd row-0 col (first 0<fst run ended)
    if not N or N[0][0]!=0: return None
    i=1
    while i<len(N) and N[i][0]>0: i+=1  # skip argument block
    if i>=len(N): return None  # empty tail-zone
    return i

ST=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=16,rounds=9))
le=gt=deg=0
for M in ST:
    if Lng(M)<=1: continue
    info=oper_internal(M)
    for n in (1,2,3):
        N=oper(list(M),n)
        ti=tailzone_idx(N)
        if ti is None: continue
        if info is None: deg+=1; continue
        j0,j1=info
        if ti<=j0: le+=1
        else: gt+=1
print(f'tail-zone start vs j0: i*<=j0: {le}  i*>j0: {gt}  degenerate-oper: {deg}')
print('DONE')
