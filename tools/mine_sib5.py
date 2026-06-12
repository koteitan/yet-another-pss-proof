#!/usr/bin/env python3
"""SIB5 hypothesis test at closure+4:
For ALL adjacent tie pairs (K, K1) in closure+4 hosts:
  S1: K1 = K
  S2: K = K1 @ D, D != []
  SE: divergence at END of K (t = |K|-1, t < |K1|)  -- unconstrained x/x1
  S3: divergence mid-K with head-max both + first-diff descent
Check: every pair falls in S1|S2|SE|S3?  Also: within SE, classify (x,x1)
relations to see if a tighter end-branch exists.  Within mid-divergence,
check the branch-3 shape strictly.
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from audit_copyhead_m1 import mrun, maxr1
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
    print('closure+4 hosts:', len(out), flush=True)
    npair = 0
    cls = Counter()
    bad = 0
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
            npair += 1
            if K1 == K: cls['S1'] += 1; continue
            if len(K) > len(K1) and K[:len(K1)] == K1: cls['S2'] += 1; continue
            t = 0
            while t < len(K) and t < len(K1) and K[t] == K1[t]: t += 1
            if t >= len(K) or t >= len(K1):
                cls['len-anom'] += 1; bad += 1
                if len(ex) < 4: ex.append(('LEN', X, a, b, K, K1))
                continue
            x, x1 = K[t], K1[t]
            if t == len(K) - 1:
                rel = ('feq-sdrop' if (x1[0]==x[0] and x1[1]<x[1]) else
                       'fdrop-seq' if (x1[0]<x[0] and x1[1]==x[1]) else
                       'fdrop-srise' if (x1[0]<x[0] and x1[1]>x[1]) else
                       'feq-srise' if (x1[0]==x[0] and x1[1]>x[1]) else
                       'fdrop-sdrop' if (x1[0]<x[0] and x1[1]<x[1]) else 'other')
                cls[('SE', rel)] += 1
                continue
            # mid divergence: strict branch-3 check
            hm = K[0][1] == maxr1(K) and K1[0][1] == maxr1(K1)
            desc = (x1[0]==x[0] and x1[1]<x[1]) or (x1[0]<x[0] and x1[1]==x[1])
            if hm and desc:
                cls['S3'] += 1
            else:
                cls[('MIDBAD', hm, (x1[0]-x[0], x1[1]-x[1]))] += 1
                bad += 1
                if len(ex) < 6: ex.append(('MID', X, a, b, K, K1))
    print('pairs:', npair, ' outside S1/S2/SE/S3:', bad)
    for k, v in sorted(cls.items(), key=lambda kv: -kv[1]):
        print(f'{v:7d}  {k}')
    for tag, X, a, b, K, K1 in ex:
        print(tag, 'a=', a, 'b=', b)
        print('  K =', K)
        print('  K1=', K1)
        print('  X =', ''.join(f'({p},{q})' for p, q in X))

if __name__ == '__main__':
    main()
