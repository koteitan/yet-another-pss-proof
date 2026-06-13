#!/usr/bin/env python3
"""Preservation-structure miner for GCD/O2: for X = M[n] (M in closure+2),
X bad with i1=0, enumerate X's GCD / O2 instances and classify positions
relative to the copy seams of the oper that built X.

Region encoding for a position p in X (built as take j0 M @ n copies of
[j0..j1)): 'P' if p < j0M (prefix), else ('C', k, off) with
p = j0M + k*L + off, L = j1M - j0M.
Also record whether M itself is bad/i1=0 and whether the GCD pair maps to
a GCD instance of M (positions j0M+off form gap-clear pair in M's block).
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

def region(p, j0M, L):
    if p < j0M: return ('P', p)
    k, off = divmod(p - j0M, L)
    return ('C', k, off)

def main():
    HS = hosts_plus(2)
    print('hosts(+2):', len(HS), flush=True)
    gcls = Counter(); ocls = Counter()
    gex = {}
    for Mt in HS:
        M = list(Mt)
        bpM = bad_params(M)
        if bpM is None: continue  # X=M[n] only differs when bad branch
        j0M, j1M, i1M, d0M = bpM
        L = j1M - j0M
        for n in (1, 2, 3, 4):
            X = oper(list(M), n)
            bp = bad_params(X)
            if bp is None: continue
            j0, j1, i1, d0 = bp
            if i1 != 0: continue
            # GCD instances of X
            for w in range(j0 + 1, j1):
                if X[w][1] == 0: continue
                fx = X[w][0] + 1
                for x in range(w + 1, j1):
                    if X[x][0] != fx: continue
                    if not all(fx <= X[t][0] for t in range(w + 1, x)): continue
                    if i1M == 0 and d0M == 0:
                        rj0 = region(j0, j0M, L); rw = region(w, j0M, L)
                        rx = region(x, j0M, L)
                        key = ('G', i1M, rj0[0], rw[0], rx[0],
                               rj0 if rj0[0]=='P' else ('C','k%d'%rj0[1],rj0[2]),
                               rw if rw[0]=='P' else ('C','k%d'%rw[1],rw[2]),
                               rx if rx[0]=='P' else ('C','k%d'%rx[1],rx[2]))
                    else:
                        key = ('G', i1M, 'nonexact')
                    gcls[key] += 1
                    if key not in gex: gex[key] = (M, n, j0, j1, w, x)
            # O2 instances of X
            if j0 > 0 and X[j0 - 1][0] < X[j0][0]:
                for r in range(j0 + 1, j1):
                    if X[r][1] != X[j0][1] + 1: continue
                    if i1M == 0 and d0M == 0:
                        rj0 = region(j0, j0M, L); rr = region(r, j0M, L)
                        key = ('O', i1M,
                               rj0 if rj0[0]=='P' else ('C','k%d'%rj0[1],rj0[2]),
                               rr if rr[0]=='P' else ('C','k%d'%rr[1],rr[2]))
                    else:
                        key = ('O', i1M, 'nonexact')
                    ocls[key] += 1
                    if key not in gex: gex[key] = (M, n, j0, j1, r, r)
    print('GCD preservation classes:')
    for k, c in sorted(gcls.items(), key=lambda t: -t[1]):
        print('  %s x%d' % (k, c))
    print('O2 preservation classes:')
    for k, c in sorted(ocls.items(), key=lambda t: -t[1]):
        print('  %s x%d' % (k, c))
    print('examples:')
    for k in list(gex)[:30]:
        M, n, j0, j1, a, b = gex[k]
        print(' ', k, 'n=%d j0=%d j1=%d a=%d b=%d' % (n, j0, j1, a, b),
              'M=%s' % ''.join('(%d,%d)' % p for p in M))

if __name__ == '__main__':
    main()
