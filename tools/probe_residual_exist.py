#!/usr/bin/env python3
"""FINAL: the single existence residual covering the whole oper induction step.

Claim (RESIDUAL): for M in ST_PS, 1<=n, and any i with i<len(oper M n) and
oper(M,n)[i][0]==0, there EXIST i', m with
   i' < len M,  M[i'][0]==0,  1<=m,  drop i (oper M n) == oper(drop i' M, m).
(We additionally check len(drop i' M)>1 is NOT required: oper handles len-1 as id.)

This single fact + IH (drop i' M in ST_PS) + ST_PS.oper closes the strengthened
suffix-closure lemma. Verify 0 failures across ALL oper branches (id/pred/tile).

Also: special i=0 case. drop 0 (oper M n) = oper M n. Need oper M n in ST_PS:
that's ST_PS.oper(M,n) directly (n>=1). So i=0 doesn't need the residual; but our
existence with i'=0,m=n,? Actually drop0(operMn)=operMn=oper(drop0 M,n) only if
oper M n==oper M n trivially with i'=0? oper(drop0 M,n)=oper(M,n). YES exact. So
i=0 also satisfied by i'=0,m=n. Good — uniform.
"""
import sys
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import oper, Lng, idx1, entry, hasParent0, hasParent1, parent0, parent1
from wfe_explore import enum_ST

def branch(M):
    M=list(M); j1=Lng(M)-1
    if j1==0: return ('id',)
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return ('pred',)
    i1=idx1(M,j1)
    if i1==1:
        if not hasParent1(M,j1): return ('pred',)
        return ('tile',parent1(M,j1),j1)
    else:
        if not hasParent0(M,j1): return ('pred',)
        return ('tile',parent0(M,j1),j1)

ST=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=16,rounds=9))
print('corpus',len(ST),flush=True)

tot=0; bad=0; ex=[]
by={'id':0,'pred':0,'tile':0}
for M in ST:
    if Lng(M)<1: continue
    n_M=Lng(M)
    for n in (1,2,3,4):
        N=oper(list(M),n)
        b=branch(M); by[b[0]]+=1
        for i in range(len(N)):
            if N[i][0]!=0: continue
            tot+=1
            target=tuple(N[i:])
            found=False
            # search witnesses i' (row-0 index of M), m in 1..n
            for ip in range(n_M):
                if M[ip][0]!=0: continue
                Mp=list(M[ip:])
                for m in range(1,n+1):
                    if tuple(oper(Mp,m))==target:
                        found=True; break
                if found: break
            if not found:
                bad+=1
                if len(ex)<15: ex.append((M,n,i,b,target))
print(f'RESIDUAL-EXISTENCE tot={tot} bad={bad}  branch-steps={by}')
for e in ex[:15]: print('  BAD',e)
print('DONE',flush=True)
