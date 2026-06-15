#!/usr/bin/env python3
"""Classify the residual (non-W1) cases of suffix_oper_witness for ST_PS.
Residual = NOT (tiling-branch AND i<=j0). Break down into:
  - pred-bothzero: oper takes Pred via last-column (0,0)
  - pred-noparent: oper takes Pred via no-parent
  - id: Lng M <= 1
  - tile-igtj0: tiling branch with i>j0
For each, test the unified closed-form / pred-commute witness validity (0 bad target).
"""
import sys
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import oper, Lng, idx1, entry, hasParent0, hasParent1, parent0, parent1
from wfe_explore import enum_ST

def opclass(M):
    M=list(M); j1=Lng(M)-1
    if j1==0: return ('id',)
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return ('pred_bz',)
    i1=idx1(M,j1)
    if i1==1:
        if not hasParent1(M,j1): return ('pred_np',)
        return ('tile',i1,parent1(M,j1),j1)
    else:
        if not hasParent0(M,j1): return ('pred_np',)
        return ('tile',i1,parent0(M,j1),j1)

ST=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=16,rounds=9))
print('corpus',len(ST),flush=True)
cnt={}; bad={}; ex={}
for M in ST:
    if Lng(M)<=1: continue
    cl=opclass(M)
    for n in (1,2,3,4):
        N=oper(list(M),n)
        for i in range(len(N)):
            if N[i][0]!=0: continue
            # is this a residual case? residual iff NOT (tile and i<=j0)
            if cl[0]=='tile' and i<=cl[2]: continue
            tag=cl[0]
            cnt[tag]=cnt.get(tag,0)+1
            S=tuple(N[i:])
            # try closed-form witness
            ok=False
            if cl[0]=='pred_bz' or cl[0]=='pred_np':
                # pred: N=butlast M; witness drop i M with m s.t. oper(drop i M,m)=S
                dM=list(M[i:])
                for m in (1,2,3,4):
                    if Lng(dM)>1 and tuple(oper(dM,m))==S and dM[0][0]==0: ok=True;break
            elif cl[0]=='tile':
                _,i1,j0,j1=cl; L=j1-j0; off=i-j0
                q=off//L; s=off%L; ip=j0+s; m=n-q
                dM=list(M[ip:])
                ok=(ip<len(M) and M[ip][0]==0 and Lng(dM)>1 and m>=1 and tuple(oper(dM,m))==S)
            elif cl[0]=='id':
                ok=(i==0)
            if not ok:
                bad[tag]=bad.get(tag,0)+1
                if tag not in ex: ex[tag]=(M,n,i,S)
print('residual counts by class:',cnt)
print('residual BAD by class:',bad)
for t,e in ex.items(): print('  EX',t,e)
print('DONE',flush=True)
