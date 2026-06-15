#!/usr/bin/env python3
"""Find a precise witness for the W2 (i>j0) suffix-closure case.

N = oper(M,n) = take j0 M ++ concat_{k<n} blk k, blk k = [ (e0(j0+s)+k*d0, e1(j0+s)+k*d1) : s in 0..<(j1-j0) ].
For a row-0 column index i>j0 of N (so N[i][0]==0), write
   i = j0 + q*L + s,  L=j1-j0,  q in 0..<n, s in 0..<L.
N[i][0]=0  <=>  e0(j0+s)+q*d0 = 0  <=>  e0(j0+s)=0 and q*d0=0.
The suffix S = N[i:].

Candidate witness:  M' = drop (j0+s) M  (a row-0-headed suffix of M, since
M[j0+s][0] = e0(j0+s) = 0), and S = oper(M', m) for m = n - q ... or some such.

We TEST, over the corpus, several candidate (M', m) and report which (if any)
gives S == oper(M', m) exactly.  Also test the simpler claim S in STset.
"""
import sys
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

ST=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=16,rounds=9))
STset=set(ST)
print('corpus',len(ST),flush=True)

w2_tot=0
hit_dropM_nq=0     # S == oper(drop (j0+s) M, n-q)
hit_dropM_nmq=0    # other m values
hit_in_corpus=0
fail_all=[]
for M in ST:
    if Lng(M)<=1: continue
    info=oper_internal(M)
    if info is None: continue
    j0,j1=info
    L=j1-j0
    for n in (1,2,3,4):
        N=oper(list(M),n)
        for i in range(j0+1,len(N)):   # i>j0
            if N[i][0]!=0: continue
            S=tuple(N[i:])
            w2_tot+=1
            if S in STset: hit_in_corpus+=1
            # decompose i = j0 + q*L + s
            off=i-j0
            q=off//L; s=off%L
            Mp=list(M[j0+s:])
            ok=False
            # try a range of m
            for m in range(1, n+1):
                if Mp and Lng(Mp)>1 and tuple(oper(Mp,m))==S:
                    ok=True
                    if m==n-q: hit_dropM_nq+=1
                    else: hit_dropM_nmq+=1
                    break
            if not ok:
                if len(fail_all)<12: fail_all.append((M,n,i,j0,j1,q,s,S))
print(f'W2 tot={w2_tot} in_corpus={hit_in_corpus}',flush=True)
print(f'  S==oper(drop(j0+s)M, n-q): {hit_dropM_nq}   other-m: {hit_dropM_nmq}',flush=True)
print(f'  no (M\',m) witness from drop(j0+s)M: {len(fail_all)} (showing first)',flush=True)
for e in fail_all[:12]:
    M,n,i,j0,j1,q,s,S=e
    print('  FAIL M=',M,'n=',n,'i=',i,'j0=',j0,'j1=',j1,'q=',q,'s=',s)
    print('       S=',S)
print('DONE',flush=True)
