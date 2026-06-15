#!/usr/bin/env python3
"""Test INV:  le0 M 0 j  =>  e1(M,j) >= e1(M,0).
Also general anchor form INV2: for any anchor a with row0(a)=0,
   le0 M a j  AND (no row0=0 strictly between a and j on the realized chain?) ...
Simplest: test le0 M a j with row0(a)=0 => e1(j)>=e1(a)?  (general anchored le0 value bound)
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
def reach(M,start):
    n=Lng(M); R={start}; changed=True
    while changed:
        changed=False
        for a in list(R):
            for b in range(n):
                if b not in R and nextrel0(M,a,b):
                    R.add(b); changed=True
    return R

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

# INV1: le0 M 0 j => e1(j) >= e1(0)
t1=o1=0; e1ex=[]
# INV2: anchored: row0(a)=0 & le0 M a j => e1(j) >= e1(a)
t2=o2=0; e2ex=[]
for M in extra:
    M=list(M)
    if not M: continue
    R0=reach(M,0)
    for j in R0:
        t1+=1
        if e1(M,j)>=e1(M,0): o1+=1
        elif len(e1ex)<8: e1ex.append((j,M))
    for a in range(len(M)):
        if e0(M,a)!=0: continue
        Ra=reach(M,a)
        for j in Ra:
            t2+=1
            if e1(M,j)>=e1(M,a): o2+=1
            elif len(e2ex)<8: e2ex.append((a,j,M))
print(f'INV1 le0 0 j => e1(j)>=e1(0): {o1}/{t1}')
for x in e1ex: print('   F1',x)
print(f'INV2 row0(a)=0 & le0 a j => e1(j)>=e1(a): {o2}/{t2}')
for x in e2ex: print('   F2',x)
print('DONE')
