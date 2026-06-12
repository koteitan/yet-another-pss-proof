#!/usr/bin/env python3
"""NT_endlex value audit at closure+4: for all SE pairs (end divergence),
check strict olt(NT K1, NT K) and the projected NT_tie conclusion."""
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
    for _ in range(4):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t); new.append(t)
        cur = new
    print('hosts:', len(out), flush=True)
    n = vlt = vtie = 0
    ntc = {}
    def NTC(S):
        S = tuple(S)
        if S not in ntc: ntc[S] = NT(list(S))
        return ntc[S]
    seen = set()
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
            t = 0
            while t < len(K) and t < len(K1) and K[t] == K1[t]: t += 1
            if t != len(K) - 1 or t >= len(K1): continue
            key = (X[a][1], tuple(K), tuple(K1))
            if key in seen: continue
            seen.add(key)
            n += 1
            if not lt_term(NTC(tuple(K1)), NTC(tuple(K))):
                vlt += 1
            u = X[a][1]
            if lt_term(proj(u, NTC(tuple(K))), proj(u, NTC(tuple(K1)))):
                vtie += 1
    print(f'SE pairs (dedup): {n}  strict olt(NT K1, NT K) fails: {vlt}  NT_tie-conclusion fails: {vtie}')

if __name__ == '__main__':
    main()
