#!/usr/bin/env python3
"""closure+2 audit of seam_open_m1_core facts:
 hmK : snd(hd K) = maxr1 K
 hmK1: snd(hd K1) = maxr1 K1   (K1 = tail @ B)
 F1  : fst(hd D) = e0(j0) + m*d0 + 1
 F2  : snd(hd D) = e1(j0)
"""
import sys
sys.path.insert(0, '.')
from audit_copyhead_m1 import mrun, sibm2, maxr1
from mine_sibm2 import bad_params
from fast_pss import oper, entry
from wfe_explore import enum_ST

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(tuple(M) for M in ST)
    cur = list(out)
    for _ in range(2):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t); new.append(t)
        cur = new
    print('hosts:', len(out), flush=True)
    n = b1 = b2 = b3 = b4 = 0
    for Mt in out:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        m = 1
        Y = M[:j0] + [(entry(M,0,j), entry(M,1,j)) for j in range(j0, j1)]
        if not sibm2(Y): continue
        B = [(entry(M,0,j) + m*d0, entry(M,1,j)) for j in range(j0, j1)]
        for a in range(len(Y)):
            if Y[a][0] <= 0: continue
            K = mrun(Y, a)
            b = a + 1 + len(K)
            if b >= len(Y): continue
            if Y[b] != Y[a]: continue
            if not all(Y[b][0] < x[0] for x in Y[b+1:]): continue
            if not Y[b][0] < entry(M,0,j0) + m*d0: continue
            if b >= j0: continue
            tail = Y[b+1:]
            if not (len(K) > len(tail) and K[:len(tail)] == tail): continue
            D = K[len(tail):]
            if not D: continue
            n += 1
            K1 = tail + B
            if K[0][1] != maxr1(K): b1 += 1
            if K1[0][1] != maxr1(K1): b2 += 1
            if D[0][0] != entry(M,0,j0) + m*d0 + 1: b3 += 1
            if D[0][1] != entry(M,1,j0): b4 += 1
    print(f'instances: {n}  hmK-fail: {b1}  hmK1-fail: {b2}  F1-fail: {b3}  F2-fail: {b4}')

if __name__ == '__main__':
    main()
