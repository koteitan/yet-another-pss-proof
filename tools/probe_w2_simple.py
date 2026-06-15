#!/usr/bin/env python3
"""Refined tile i>j0 claim: every row-0 index i>j0 of oper M n has i=j0+q*L (s=0),
j0=0 forced? and witness drop i (oper M n) = oper (drop j0 M) (n-q).
Test: i' = j0 (always), m = n-q, with q=(i-j0)//L; also verify entry M 0 j0 = 0."""
import sys
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import oper, Lng, idx1, entry, hasParent0, hasParent1, parent0, parent1
from wfe_explore import enum_ST
def opcl(M):
    M=list(M); j1=Lng(M)-1
    if j1==0: return ('id',)
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return ('pred',)
    i1=idx1(M,j1)
    if i1==1:
        if not hasParent1(M,j1): return ('pred',)
        return ('tile',i1,parent1(M,j1),j1)
    if not hasParent0(M,j1): return ('pred',)
    return ('tile',i1,parent0(M,j1),j1)
ST=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=16,rounds=9))
print('corpus',len(ST),flush=True)
tot=0; s_nonzero=0; j0_nonzero_entry=0; bad=0; ex=[]
for M in ST:
    if Lng(M)<=1: continue
    cl=opcl(M)
    if cl[0]!='tile': continue
    _,i1,j0,j1=cl; L=j1-j0
    for n in (1,2,3,4):
        N=oper(list(M),n)
        for i in range(len(N)):
            if i<=j0 or N[i][0]!=0: continue
            off=i-j0; q=off//L; s=off%L
            tot+=1
            if s!=0: s_nonzero+=1
            if entry(list(M),0,j0)!=0: j0_nonzero_entry+=1
            # witness i'=j0, m=n-q
            ip=j0; m=n-q
            Mp=list(M[ip:])
            ok=(ip<len(M) and M[ip][0]==0 and m>=1 and Lng(Mp)>1 and tuple(oper(Mp,m))==tuple(N[i:]))
            if not ok:
                bad+=1
                if len(ex)<10: ex.append((M,n,i,j0,j1,q,s,tuple(N[i:])))
print(f'tot={tot} s_nonzero={s_nonzero} j0_entry_nonzero={j0_nonzero_entry} bad={bad}')
for e in ex[:10]: print('  BAD',e)
print('DONE')
