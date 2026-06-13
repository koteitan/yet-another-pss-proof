#!/usr/bin/env python3
"""Structural-only deep sweep of E6_nbcK_T (no value semantics) + direct check
of the known X=M[2] counterexample and NT_tie on it."""
import sys
sys.path.insert(0, '.')
from fast_pss import oper
from wfe_explore import enum_ST

def maxr1(S): return max(c[1] for c in S)
def hosts_plus(extra):
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(ST); cur = list(out)
    for i in range(extra):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out: out.add(t); new.append(t)
        cur = new
        print('  +%d: total %d' % (i+1, len(out)), flush=True)
    return out
def dsegs(H):
    lh = len(H)
    for ppi in range(lh):
        lv = H[ppi][0]; dend = ppi+1
        while dend < lh and H[dend][0] > lv: dend += 1
        for k in range(ppi+2, dend+1):
            yield (H[ppi][1], tuple(H[ppi+1:k]))
def tw(p, xs):
    o=[]
    for x in xs:
        if p(x): o.append(x)
        else: break
    return o
def dw(p, xs):
    i=0
    while i<len(xs) and p(xs[i]): i+=1
    return list(xs[i:])

def sweep(extra):
    HS = hosts_plus(extra)
    print('hosts:', len(HS), flush=True)
    n=b=0; ex=[]; seen=set()
    for H in HS:
        for (u,S) in dsegs(H):
            if (u,S) in seen: continue
            seen.add((u,S))
            if len(S)<2: continue
            c0=S[0]; rest=list(S[1:])
            K=tw(lambda r:c0[0]<r[0],rest); T=dw(lambda r:c0[0]<r[0],rest)
            m=maxr1(S)
            if u<=c0[1] and K and maxr1(K)==m and c0[1]<m:
                n+=1
                if T:
                    b+=1
                    if len(ex)<6: ex.append((u,S))
    print(f'E6_nbcK_T (+{extra}): {n} inst, {b} violations')
    for u,S in ex:
        print('  fail u=%d S=%s'%(u,''.join('(%d,%d)'%p for p in S)))

if __name__=='__main__':
    extra=int(sys.argv[1]) if len(sys.argv)>1 else 5
    sweep(extra)
