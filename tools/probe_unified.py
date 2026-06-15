#!/usr/bin/env python3
"""Unified suffix-closure witness across BOTH i<=j0 and i>j0.

Claim (UNIFIED): for N=oper(M,n) (genuine tiling branch, parent j0<j1),
and any index i with 1<=i<len(N) and N[i][0]==0:
  let off = i - j0.
  if off<=0 (i<=j0, green prefix):  i'=i,  m=n      ->  drop i N == oper(drop i' M, m)
  else: L=j1-j0; q=off//L; s=off%L; i'=j0+s; m=n-q  ->  drop i N == oper(drop i' M, m)
and in both cases M[i'][0]==0 (row-0-headed) and i'<len(M), m>=1, len(drop i' M)>1.

We unify: i' = i if i<=j0 else j0 + ((i-j0) % L);  m = n if i<=j0 else n - (i-j0)//L.
Verify 0 failures at deep closure.
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
print('corpus',len(ST),flush=True)

tot=0; bad=0; badex=[]
deg=0   # degenerate oper (M or Pred branch) — not covered by this lemma
for M in ST:
    if Lng(M)<=1: continue
    info=oper_internal(M)
    for n in (1,2,3,4):
        N=oper(list(M),n)
        if info is None:
            deg+=1
            continue
        j0,j1=info; L=j1-j0
        for i in range(1,len(N)):
            if N[i][0]!=0: continue
            tot+=1
            off=i-j0
            if off<=0:
                ip=i; m=n
            else:
                q=off//L; s=off%L; ip=j0+s; m=n-q
            Mp=list(M[ip:])
            head_ok = (ip<len(M) and M[ip][0]==0)
            len_ok  = (Lng(Mp)>1)
            m_ok    = (m>=1)
            eq = (head_ok and len_ok and m_ok and tuple(oper(Mp,m))==tuple(N[i:]))
            if not eq:
                bad+=1
                if len(badex)<12: badex.append((M,n,i,j0,j1,ip,m,head_ok,len_ok,m_ok,tuple(N[i:])))
print(f'UNIFIED tot={tot} bad={bad}  (degenerate-oper steps skipped={deg})',flush=True)
for e in badex[:12]:
    print('  BAD',e)
print('DONE',flush=True)
