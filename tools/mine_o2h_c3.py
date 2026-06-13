#!/usr/bin/env python3
"""O2H audit: i1=0 bad block with dominated head (fst(j0-1) < fst(j0))
==> snd(j0) = 0.  Also census: all i1=0 bad-block heads' snd values."""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from mine_sibm2 import bad_params
from fast_pss import oper
from collections import Counter

def hosts_plus(extra=3):
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
    HS = hosts_plus(3)
    print('hosts:', len(HS), flush=True)
    n = bad = 0; ex = []
    census = Counter()
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if i1 != 0: continue
        census[('any', M[j0][1] > 0)] += 1
        if j0 > 0 and M[j0 - 1][0] < M[j0][0]:
            n += 1
            census[('dom', M[j0][1] > 0)] += 1
            if M[j0][1] != 0:
                bad += 1
                if len(ex) < 6: ex.append((j0, j1, M))
    print(f'O2H: {n} dominated heads, {bad} with snd>0')
    print('census:', dict(census))
    for j0, j1, M in ex:
        print('O2H-fail j0=%d j1=%d M=%s' % (j0, j1,
              ''.join('(%d,%d)' % p for p in M)))

if __name__ == '__main__':
    main()
