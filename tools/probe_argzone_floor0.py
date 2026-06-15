#!/usr/bin/env python3
"""For the CONTIGUOUS arg zone (indices 1..k right after head index 0, all row0>0),
   verify:
   (A) nextrel0 M 0 j  holds for each such j  (index 0 directly row-0-parents j)?
       OR at least le0 M 0 j.
   (B) and then entry M 1 0 = y <= entry M 1 j follows from a value relation:
       specifically  nextrel0 M 0 j => entry M 1 0 <= entry M 1 j ?
   Decompose to find the minimal provable chain.
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import enum_ST
from fast_pss import oper

def Lng(M): return len(M)
def e0(M,j): return M[j][0]
def e1(M,j): return M[j][1]

def nextrel0(M,j0,j1):
    if not (j0<Lng(M) and j1<Lng(M) and j0<j1): return False
    if not (e0(M,j0)<e0(M,j1)): return False
    for j in range(j0+1,j1):
        if e0(M,j) < e0(M,j1): return False
    return True

base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(5):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=22 and tt not in extra:
                extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print('deep ST closure =',len(extra),flush=True)

# (A) nextrel0 M 0 j for contiguous argzone index j
totA=okA=0; exA=[]
# (B) le0 M 0 j for contiguous argzone index j (weaker)
# (C) the per-step value relation: nextrel0 M a b & e0(M,a)==0 ... we need general.
# Most promising: nextrel0 M 0 j directly. If e0(M,0)=0 and all of 1..j-1 have row0>0
#   and e0(M,j)>0 then valley condition: all between have row0 >= e0(M,j)? NOT necessarily.
# So nextrel0 M 0 j might fail. Let's measure.
totB=okB=0; exB=[]
for M in extra:
    M=list(M)
    if not M or e0(M,0)!=0: continue
    # contiguous argzone: indices 1..k while row0>0
    k=0
    j=1
    while j<len(M) and e0(M,j)>0:
        # this j is an argzone index
        totA+=1
        if nextrel0(M,0,j): okA+=1
        elif len(exA)<8: exA.append((j,M))
        # le0 via direct chain from 0? compute reflexive-trans reach from 0
        j+=1
print(f'(A) nextrel0 M 0 j for contiguous argzone idx: {okA}/{totA}')
for x in exA: print('   FAILA',x)

# (B) le0 M 0 j  (reach from 0)
def reach0(M):
    n=Lng(M); R={0}
    changed=True
    while changed:
        changed=False
        for a in list(R):
            for b in range(n):
                if b not in R and nextrel0(M,a,b):
                    R.add(b); changed=True
    return R
for M in extra:
    M=list(M)
    if not M or e0(M,0)!=0: continue
    R=reach0(M)
    j=1
    while j<len(M) and e0(M,j)>0:
        totB+=1
        if j in R: okB+=1
        elif len(exB)<8: exB.append((j,M))
        j+=1
print(f'(B) le0 M 0 j for contiguous argzone idx: {okB}/{totB}')
for x in exB: print('   FAILB',x)

# (D) The clean value invariant feeding it:
#   for ALL a,b with nextrel0 M a b AND e1(M,a) is "a row-0=0 anchor value"...
#   Simpler target candidate INV_step:
#   nextrel0 M a b  =>  e1(M,b) >= e1(M,a)  WHEN e0(M,a)=0  (anchor step)?
totD=okD=0; exD=[]
for M in extra:
    M=list(M)
    n=len(M)
    for a in range(n):
        if e0(M,a)!=0: continue
        for b in range(n):
            if nextrel0(M,a,b):
                totD+=1
                if e1(M,b)>=e1(M,a): okD+=1
                elif len(exD)<8: exD.append((a,b,M))
print(f'(D) nextrel0 M a b & row0(a)=0 => e1(b)>=e1(a): {okD}/{totD}')
for x in exD: print('   FAILD',x)
print('DONE')
