#!/usr/bin/env python3
"""NT_fdlex value audit at closure+5 (the sibrel6 value core):
ALL adjacent tie pairs outside S1/S2 (i.e., genuine first-diff):
  V1: first-diff is lex-drop (x1 <lex x)   [sibrel6 validity]
  V2: strict olt(NT K1, NT K)              [value lemma, NO head-max premise]
  V3: NT_tie conclusion not olt(proj u K, proj u1 K1)
Dedup by (u, K, K1)."""
import sys
sys.path.insert(0, '.')
from audit_copyhead_m1 import mrun
from mine_e6 import NT
from mine_proj import proj
from valnorm import lt_term
from fast_pss import oper
from wfe_explore import enum_ST

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(tuple(M) for M in ST)
    cur = list(out)
    for _ in range(5):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t); new.append(t)
        cur = new
    print('hosts:', len(out), flush=True)
    ntc = {}
    def NTC(S):
        S = tuple(S)
        if S not in ntc: ntc[S] = NT(list(S))
        return ntc[S]
    seen = set()
    n = v1 = v2 = v3 = 0
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
            key = (X[a][1], tuple(K), tuple(K1))
            if key in seen: continue
            seen.add(key)
            n += 1
            t = 0
            while t < len(K) and t < len(K1) and K[t] == K1[t]: t += 1
            if t >= len(K) or t >= len(K1):
                v1 += 1; continue
            x, x1 = K[t], K1[t]
            if not (x1[0] < x[0] or (x1[0] == x[0] and x1[1] < x[1])):
                v1 += 1
                if len(ex) < 3: ex.append(('V1', X, a, b, K, K1))
                continue
            if not lt_term(NTC(tuple(K1)), NTC(tuple(K))):
                v2 += 1
                if len(ex) < 5: ex.append(('V2', X, a, b, K, K1))
            u = X[a][1]
            if lt_term(proj(u, NTC(tuple(K))), proj(u, NTC(tuple(K1)))):
                v3 += 1
                if len(ex) < 5: ex.append(('V3', X, a, b, K, K1))
    print(f'first-diff pairs (dedup): {n}  V1(lex)-fail: {v1}  V2(strict NT)-fail: {v2}  V3(NT_tie)-fail: {v3}')
    for t in ex:
        print(t[0], 'a=', t[2], 'b=', t[3])
        print('  K =', t[4]); print('  K1=', t[5])

if __name__ == '__main__':
    main()
