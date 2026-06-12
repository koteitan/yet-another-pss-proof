#!/usr/bin/env python3
"""TOP_desc exact-statement audit, prefix-variant:
K = full top tree (adjacent roots), K1 = ANY nonempty 0-rooted 0-free-tail
segment starting at the next root (prefix of the next tree allowed).
Claim: ole (NT K1) (NT K).
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from valnorm import lt_term
from mine_e6 import NT
from fast_pss import oper

def hosts_plus(extra=1):
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(tuple(M) for M in ST)
    cur = list(out)
    for _ in range(extra):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t); new.append(t)
        cur = new
    return out

def main():
    import os
    extra = int(os.environ.get('EXTRA', '1'))
    HS = hosts_plus(extra)
    print('hosts:', len(HS), flush=True)
    ntc = {}
    def NTC(S):
        S = tuple(S)
        if S not in ntc: ntc[S] = NT(list(S))
        return ntc[S]
    seen = set()
    n = v = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        roots = [i for i, c in enumerate(M) if c[0] == 0]
        if len(roots) < 2: continue
        roots.append(len(M))
        for t in range(len(roots) - 2):
            p, p2, p3 = roots[t], roots[t+1], roots[t+2]
            K = tuple(M[p:p2])
            for e in range(p2 + 1, p3 + 1):
                K1 = tuple(M[p2:e])
                key = (K, K1)
                if key in seen: continue
                seen.add(key)
                n += 1
                a, b = NTC(K1), NTC(K)
                if not (a == b or lt_term(a, b)):
                    v += 1
                    if len(ex) < 4: ex.append((M, p, p2, e))
    print(f'(K, K1-prefix) pairs: {n}  violations: {v}')
    for M, p, p2, e in ex:
        print('VIOL p=', p, p2, e, 'M=', ''.join(f'({a},{b})' for a, b in M))

if __name__ == '__main__':
    main()
