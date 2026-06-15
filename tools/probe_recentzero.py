#!/usr/bin/env python3
"""INVR: for every j, let z(j) = greatest i<=j with e0(M,i)=0.
   Claim e1(M,j) >= e1(M, z(j)).
   (each value >= the value at the most recent preceding row0=0 column)
This directly gives argzone_val_ge: for contiguous argzone idx j, z(j)=0=head, so e1(j)>=y.
Purely positional -> hopefully oper-preservable.
Also test a WEAKER/STRONGER variant to be safe.
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import enum_ST
from fast_pss import oper

def e0(M,j): return M[j][0]
def e1(M,j): return M[j][1]

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

tot=ok=0; ex=[]
no_zero=0
for M in extra:
    M=list(M)
    n=len(M)
    z=-1
    for j in range(n):
        if e0(M,j)==0:
            z=j
        if z<0:
            no_zero+=1
            continue
        tot+=1
        if e1(M,j)>=e1(M,z): ok+=1
        elif len(ex)<10: ex.append((j,z,M))
print(f'INVR e1(j)>=e1(recent-zero): {ok}/{tot}  (indices before first zero: {no_zero})')
for x in ex: print('  F',x)
print('DONE')
