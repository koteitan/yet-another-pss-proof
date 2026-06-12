#!/usr/bin/env python3
"""closure+6 V1 verification of SIBREL6 (lex first-diff form only)."""
import sys
sys.path.insert(0, '.')
from audit_copyhead_m1 import mrun
from fast_pss import oper
from wfe_explore import enum_ST

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(tuple(M) for M in ST)
    cur = list(out)
    for _ in range(6):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t); new.append(t)
        cur = new
    print('closure+6 hosts:', len(out), flush=True)
    n = bad = 0
    ex = []
    for Mt in out:
        X = list(Mt)
        for a in range(len(X)):
            if X[a][0] <= 0: continue
            K = mrun(X, a)
            b = a + 1 + len(K)
            if b >= len(X): continue
            if X[b] != X[a]: continue
            K1 = mrun(X, b)
            if K1 == K: continue
            if len(K) > len(K1) and K[:len(K1)] == K1: continue
            n += 1
            t = 0
            while t < len(K) and t < len(K1) and K[t] == K1[t]: t += 1
            ok = (t < len(K) and t < len(K1) and
                  (K1[t][0] < K[t][0] or (K1[t][0] == K[t][0] and K1[t][1] < K[t][1])))
            if not ok:
                bad += 1
                if len(ex) < 5: ex.append((X, a, b, K, K1))
    print(f'first-diff pairs: {n}  sibrel6-viol: {bad}')
    for X, a, b, K, K1 in ex:
        print('VIOL a=', a, 'b=', b, 'K=', K, 'K1=', K1)

if __name__ == '__main__':
    main()
