#!/usr/bin/env python3
"""Dump/classify the ginv_GAP realized instances (closure+2).
Premises: bad branch d0=0, 0 < j0, fst(M!(j0-1)) < e0(j0),
q < j1-j0 with e1(j0) < e1(j0+q).
Conclusion: e1(j0+q) <= snd(M!(j0-1)).
Classify: (i1, snd(j0), e1(j0+q), snd(pp), q, block snd pattern class).
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from wfe_explore import enum_ST
from mine_sibm2 import bad_params
from fast_pss import oper, entry

def hosts_plus(extra=2):
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
    HS = hosts_plus(2)
    print('hosts:', len(HS), flush=True)
    n = viol = 0
    cls = Counter()
    ex = {}
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if d0 != 0: continue
        if j0 == 0: continue
        pp = M[j0-1]
        if not pp[0] < entry(M, 0, j0): continue
        s0 = entry(M, 1, j0)
        for q in range(j1 - j0):
            sq = entry(M, 1, j0 + q)
            if not s0 < sq: continue
            n += 1
            ok = sq <= pp[1]
            if not ok: viol += 1
            key = (i1, pp[1], s0, sq, q)
            cls[key] += 1
            if key not in ex: ex[key] = M
    print(f'GAP instances: {n}  violations: {viol}')
    for k, v in sorted(cls.items(), key=lambda kv: -kv[1])[:15]:
        print(f'{v:5d}  (i1,sndpp,s0,sq,q)={k}')
    print('classes:', len(cls))
    for k, M in list(ex.items())[:4]:
        print('EX', k, 'M=', ''.join(f'({a},{b})' for a, b in M))

if __name__ == '__main__':
    main()
