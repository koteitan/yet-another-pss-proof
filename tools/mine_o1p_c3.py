#!/usr/bin/env python3
"""O1P audit (+3): i1=0 bad block, snd(j0)>0 ==> forall l in (j0,j1): snd(l) <= snd(j0).
Plus preservation census: for X=M[n] with i1X=0, snd(j0X)>0, classify j0X region."""
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
    pres = Counter()
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if i1 != 0: continue
        if M[j0][1] > 0:
            n += 1
            for l in range(j0 + 1, j1):
                if M[l][1] > M[j0][1]:
                    bad += 1
                    if len(ex) < 6: ex.append((j0, l, j1, M))
                    break
    print(f'O1P: {n} positive-head blocks, {bad} violations')
    for j0, l, j1, M in ex:
        print('O1P-fail j0=%d l=%d j1=%d M=%s' % (j0, l, j1,
              ''.join('(%d,%d)' % p for p in M)))
    # preservation census on closure+2 pre-images
    HS2 = [list(t) for t in HS]
    cnt = 0
    for M in HS2:
        bpM = bad_params(M)
        if bpM is None: continue
        j0M, j1M, i1M, d0M = bpM
        L = j1M - j0M
        for nn in (1,2,3,4):
            X = oper(list(M), nn)
            bp = bad_params(X)
            if bp is None: continue
            j0, j1, i1, d0 = bp
            if i1 != 0 or X[j0][1] == 0: continue
            cnt += 1
            if i1M != 0:
                pres[('i1M=1',)] += 1
            elif j0 < j0M:
                pres[('prefix', 'Mheadpos' if M[j0M][1] > 0 else 'Mhead0',
                      'sameblockhead?' , j0 == (bad_params(M)[0] if False else -1))] += 1
            else:
                k, off = divmod(j0 - j0M, L)
                pres[('copy', k, off, 'Mheadpos' if M[j0M][1] > 0 else 'Mhead0')] += 1
    print('positive-head X census:', cnt)
    for k, c in sorted(pres.items(), key=lambda t: -t[1]):
        print('  ', k, 'x%d' % c)

if __name__ == '__main__':
    main()
