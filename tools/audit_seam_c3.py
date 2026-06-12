#!/usr/bin/env python3
"""closure+3 re-audit of ALL sibm2-family frozen statements under sibrel4.
 1. seam_open_m1   (b < j0, open run, m=1): conclusion sibrel4
 2. seam_copyhead_m1 residuals P / E2var / F2L2: emptiness
 3. seam_copyhead_deep (j0 < b, m=1): instance count + conclusion sibrel4
NOTE: audit_copyhead_m1.sibrel is already the 4-branch version.
"""
import sys
sys.path.insert(0, '.')
from audit_copyhead_m1 import mrun, sibm2, sibrel
from mine_sibm2 import bad_params
from fast_pss import oper, entry
from wfe_explore import enum_ST

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(tuple(M) for M in ST)
    cur = list(out)
    for _ in range(3):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t); new.append(t)
        cur = new
    print('closure+3 hosts:', len(out), flush=True)
    n_open = v_open = 0
    n_P = n_E2 = n_F2 = 0
    n_deep = v_deep = 0
    ex = []
    for Mt in out:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        m = 1
        Y = M[:j0] + [(entry(M,0,j), entry(M,1,j)) for j in range(j0, j1)]
        if not sibm2(Y): continue
        B = [(entry(M,0,j) + m*d0, entry(M,1,j)) for j in range(j0, j1)]
        cj1 = (entry(M,0,j1), entry(M,1,j1))
        blktail = [(entry(M,0,j), entry(M,1,j)) for j in range(j0+1, j1)]
        L2 = j0 + 1 < j1
        for a in range(len(Y)):
            if Y[a][0] <= 0: continue
            K = mrun(Y, a)
            b = a + 1 + len(K)
            if b >= len(Y): continue
            if Y[b] != Y[a]: continue
            if not all(Y[b][0] < x[0] for x in Y[b+1:]): continue
            if not Y[b][0] < entry(M,0,j0) + m*d0: continue
            tail = Y[b+1:]
            isopen = len(K) > len(tail) and K[:len(tail)] == tail
            if b < j0 and isopen:
                D = K[len(tail):]
                if not D: continue
                n_open += 1
                if not sibrel(K, tail + B):
                    v_open += 1
                    if len(ex) < 4: ex.append(('OPEN', M, a, b))
            elif b == j0 and isopen:
                D = K[len(tail):]
                if not D: continue
                # copyhead residual classes (exact statements)
                if D[0] == cj1 and len(D) >= 2:
                    n_P += 1
                    if len(ex) < 8: ex.append(('P', M, a, b))
                elif L2 and D == [cj1] and any(x != cj1 for x in blktail):
                    n_E2 += 1
                    if len(ex) < 8: ex.append(('E2var', M, a, b))
                elif D[0] != cj1 and cj1[0] < D[0][0] and cj1[1] == D[0][1] and L2:
                    n_F2 += 1
                    if len(ex) < 8: ex.append(('F2L2', M, a, b))
            elif j0 < b and isopen:
                D = K[len(tail):]
                if not D: continue
                n_deep += 1
                if not sibrel(K, tail + B):
                    v_deep += 1
                    if len(ex) < 8: ex.append(('DEEP', M, a, b))
    print(f'open_m1 (b<j0): n={n_open}  sibrel4-viol={v_open}')
    print(f'copyhead residuals: P={n_P}  E2var={n_E2}  F2L2={n_F2}  (expect 0)')
    print(f'deep (j0<b): n={n_deep}  sibrel4-viol={v_deep}')
    for t in ex[:8]:
        print(t[0], 'a=', t[2], 'b=', t[3], 'M=', ''.join(f'({x},{y})' for x, y in t[1]))

if __name__ == '__main__':
    main()
