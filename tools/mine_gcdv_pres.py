#!/usr/bin/env python3
"""GCDV preservation classification: for X = M[n] (bad branch), classify all
GCDV instances (a, w, x, om) of X by region (P=prefix, Ck=copy k) and check
which M-side fact closes them:
  - 'allP'        : whole window in prefix -> GCDV(M) verbatim
  - 'samecopy'    : a,w,x,om in one copy   -> GCDV(M) block window (shift)
  - 'wx-incopy'   : w,x in copies, a in prefix, om = copy head or in copy ->
                    GCDV(M) with window (j0M, j1M)?  check w',x' in block
  - other         : cross-seam pairs (w prefix / x copy etc.) -> residual
For residual classes, dump examples.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from mine_sibm2 import bad_params
from fast_pss import oper
from collections import Counter

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

def reg(p, j0M, L):
    if p < j0M: return ('P',)
    k, off = divmod(p - j0M, L)
    return ('C', k, off)

def gcdv_instances(M):
    L = len(M)
    out = []
    for om in range(1, L):
        if M[om][1] != 0: continue
        fom = M[om][0]
        a = None
        for p in range(om - 1, -1, -1):
            if M[p][0] < fom:
                a = p; break
        if a is None: continue
        for w in range(a + 1, om):
            if M[w][1] == 0: continue
            fx = M[w][0] + 1
            for x in range(w + 1, om):
                if M[x][0] != fx: continue
                if not all(fx <= M[t][0] for t in range(w + 1, x)): continue
                out.append((a, w, x, om))
    return out

def main():
    HS = hosts_plus(2)
    print('hosts(+2):', len(HS), flush=True)
    cls = Counter(); ex = {}
    Mside_fail = Counter()
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0M, j1M, i1M, d0M = bp
        L = j1M - j0M
        Minst = set(gcdv_instances(M))
        for n in (1, 2, 3, 4):
            X = oper(list(M), n)
            for (a, w, x, om) in gcdv_instances(X):
                ra, rw, rx, ro = (reg(p, j0M, L) for p in (a, w, x, om))
                if ro == ('P',):
                    key = ('allP', (a, w, x, om) in Minst)
                elif ra[0] == 'C' and ra[1] == ro[1] if ro[0]=='C' else False:
                    # same copy window
                    key = ('samecopy', i1M)
                else:
                    key = ('mix', ra[0] if ra[0]=='P' else 'C%d'%ra[1],
                           rw[0] if rw[0]=='P' else 'C%d'%rw[1],
                           rx[0] if rx[0]=='P' else 'C%d'%rx[1],
                           ro[0] if ro[0]=='P' else 'C%d'%ro[1],
                           'i1M=%d' % i1M)
                cls[key] += 1
                if key not in ex: ex[key] = (M, n, a, w, x, om)
    for k, c in sorted(cls.items(), key=lambda t: -t[1]):
        print(' ', k, 'x%d' % c)
    print('examples of mix/residual classes:')
    for k, v in ex.items():
        if k[0] != 'mix': continue
        M, n, a, w, x, om = v
        print(' ', k, 'n=%d a=%d w=%d x=%d om=%d' % (n, a, w, x, om))
        print('    M=%s' % ''.join('(%d,%d)' % p for p in M))

if __name__ == '__main__':
    main()
