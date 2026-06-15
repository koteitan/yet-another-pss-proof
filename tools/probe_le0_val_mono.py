#!/usr/bin/env python3
"""Candidate stronger invariants for argzone_val_ge.

M = pairseq (list of (row0,row1)).  entry M 0 j = M[j][0], entry M 1 j = M[j][1].

IST_le0  : le0 M a b  => entry M 1 a <= entry M 1 b
           (row-1 nondecreasing along any row-0 ancestry chain)

IST_floor_val: for every j with row0>0, the row-0 floor ancestor m (le0 M m j, row0(m)=0)
           has entry M 1 m == y0 == M[0][1]  (i.e. floor is the head value).
           weaker: entry M 1 m >= ... ? we just need head reachable.

Also re-verify the target argzone_val_ge itself.
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

def le0_pairs(M):
    # transitive reflexive closure of nextrel0, restricted to in-range
    n=Lng(M)
    reach={a:{a} for a in range(n)}
    edges=[(a,b) for a in range(n) for b in range(n) if nextrel0(M,a,b)]
    # floyd-ish
    changed=True
    while changed:
        changed=False
        for (a,b) in edges:
            for a0 in range(n):
                if a in reach[a0] and b not in reach[a0]:
                    reach[a0].add(b); changed=True
    return reach  # reach[a] = {b : le0 M a b}

def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out

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

# 1. IST_le0
tot1=ok1=0; ex1=[]
for M in extra:
    M=list(M)
    if not M: continue
    reach=le0_pairs(M)
    for a in range(len(M)):
        for b in reach[a]:
            tot1+=1
            if e1(M,a)<=e1(M,b): ok1+=1
            elif len(ex1)<6: ex1.append((a,b,M))
print(f'IST_le0 (row1 nondecr along le0): {ok1}/{tot1}')
for a,b,M in ex1: print('   FAIL',a,b,M)

# 2. IST_floor_val: floor ancestor of an argzone index equals head value
tot2=ok2=0; ex2=[]
for M in extra:
    M=list(M)
    if not M or e0(M,0)!=0: continue
    y0=e1(M,0)
    reach=le0_pairs(M)
    # invert reach to get ancestors
    for j in range(len(M)):
        if e0(M,j)<=0: continue
        # floor ancestors m: le0 M m j and row0(m)=0
        floors=[m for m in range(len(M)) if j in reach[m] and e0(M,m)==0]
        if not floors:
            ex2.append(('nofloor',j,M)) if len(ex2)<6 else None
            continue
        tot2+=1
        if all(e1(M,m)>=y0 for m in floors): ok2+=1
        elif len(ex2)<6: ex2.append((j,floors,y0,M))
print(f'IST_floor_val (all row0=0 le0-ancestors of argidx have row1>=head y): {ok2}/{tot2}')
for x in ex2: print('   FAIL',x)

# 3. stronger floor: floor ancestor is exactly index 0 / value exactly y0?
tot3=ok3=0; ex3=[]
for M in extra:
    M=list(M)
    if not M or e0(M,0)!=0: continue
    y0=e1(M,0)
    reach=le0_pairs(M)
    for j in range(1,len(M)):
        if e0(M,j)<=0: continue
        floors=[m for m in range(len(M)) if j in reach[m] and e0(M,m)==0]
        tot3+=1
        # is index 0 always among floors?
        if 0 in floors: ok3+=1
        elif len(ex3)<6: ex3.append((j,floors,M))
print(f'IST_idx0_floor (index 0 is le0-ancestor of every argidx j): {ok3}/{tot3}')
for x in ex3: print('   FAIL',x)

# 4. target itself (only argzone prefix from index1)
tot4=ok4=0; ex4=[]
for M in extra:
    M=list(M)
    if not M or e0(M,0)!=0: continue
    y=e1(M,0); aM=takeW(M[1:])
    if not aM: continue
    tot4+=1
    if all(v>=y for (i,v) in aM): ok4+=1
    elif len(ex4)<6: ex4.append((y,M))
print(f'TARGET argzone_val_ge: {ok4}/{tot4}')
for x in ex4: print('   FAIL',x)
print('DONE')
