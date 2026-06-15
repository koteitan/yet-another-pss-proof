#!/usr/bin/env python3
"""For the tile i>j0 residual: examine oper-internals of the witness drop i' M.
i'=j0+(off%L), m=n-(off//L). Report parent j0' and child j1' and i1' of drop i' M,
and whether j0'=0 (i.e. parent is the new head)."""
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
tot=0; j0p_zero=0; j0p_nonzero=0; i1_same=0; s_eq_j0p=0; bad=0
ex=[]
for M in ST:
    if Lng(M)<=1: continue
    cl=opcl(M)
    if cl[0]!='tile': continue
    _,i1,j0,j1=cl; L=j1-j0
    for n in (1,2,3,4):
        for i in range(len(oper(list(M),n))):
            N=oper(list(M),n)
            if i<=j0 or i>=len(N) or N[i][0]!=0: continue
            off=i-j0; q=off//L; s=off%L; ip=j0+s; m=n-q
            if m<1: continue
            Mp=list(M[ip:])
            if Lng(Mp)<=1: continue
            clp=opcl(Mp)
            tot+=1
            if clp[0]!='tile':
                bad+=1
                if len(ex)<10: ex.append(('NOTTILE',M,n,i,ip,clp)); 
                continue
            _,i1p,j0p,j1p=clp
            if j0p==0: j0p_zero+=1
            else: j0p_nonzero+=1
            if i1p==i1: i1_same+=1
            if s==j0p: s_eq_j0p+=1
print(f'tot={tot} j0p_zero={j0p_zero} j0p_nonzero={j0p_nonzero} i1_same={i1_same} s_eq_j0p={s_eq_j0p} notile={bad}')
for e in ex[:10]: print('  ',e)
print('DONE')
