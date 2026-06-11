#!/usr/bin/env python3
"""Test whether the E6_seam conclusions hold WITHOUT the both-fire premise:
pure window form on closure+1 hosts:
  for host M, position i (pp=M[i]), S=M[i+1:-1] nonempty, q=M[-1],
  all fst(S) > fst(pp), fst(pp) < fst(q), snd q <= maxr1 S:
    INV : fst(hd(msfx S)) <= fst q
    INV2: hd(msfx S) fst-min of msfx S
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from mine_fire4 import msfx
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
    HS = hosts_plus(1)
    print('hosts:', len(HS), flush=True)
    n = inv_bad = inv2_bad = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        if len(M) < 2: continue
        q = M[-1]
        for i in range(len(M)-1):
            pp = M[i]; S = list(M[i+1:-1])
            if not S: continue
            if not all(pp[0] < r[0] for r in S): continue
            if not pp[0] < q[0]: continue
            m = max(c[1] for c in S)
            if q[1] > m: continue
            n += 1
            T = msfx(S)
            if not T[0][0] <= q[0]:
                inv_bad += 1
                if len(ex) < 5: ex.append(('INV', M, i, S, T))
            if not all(T[0][0] <= x[0] for x in T):
                inv2_bad += 1
                if len(ex) < 5: ex.append(('INV2', M, i, S, T))
    print(f'fire-free positions: {n}  INV-fail: {inv_bad}  INV2-fail: {inv2_bad}')
    for k, M, i, S, T in ex:
        print(k, 'i=', i, 'M=', ''.join(f'({a},{b})' for a,b in M))
        print('   S=', ''.join(f'({a},{b})' for a,b in S), ' T=', ''.join(f'({a},{b})' for a,b in T))

if __name__ == '__main__':
    main()
