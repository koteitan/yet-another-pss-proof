#!/usr/bin/env python3
"""sibrel repair mining: collect ALL tie pairs in closure+3-reachable hosts
that violate the CURRENT sibrel, classify their (K, K1) shapes to design the
4th branch.
Shape probes per violating pair:
  - divergence index t, x=K[t], x1=K1[t]: relation class
  - tail shapes: K after t (length, all-above?), K1 after t (climb?)
  - head-max status of both
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from audit_copyhead_m1 import mrun, sibm2, sibrel, maxr1
from fast_pss import oper
from wfe_explore import enum_ST

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(tuple(M) for M in ST)
    cur = list(out)
    for _ in range(2):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t); new.append(t)
        cur = new
    print('closure+2 hosts:', len(out), flush=True)
    seen = set()
    nv = 0
    cls = Counter()
    ex = {}
    for Mt in list(out):
        for n in (1,2,3,4):
            X = oper(list(Mt), n)
            Xt = tuple(X)
            if Xt in seen: continue
            seen.add(Xt)
            for a in range(len(X)):
                if X[a][0] <= 0: continue
                K = mrun(X, a)
                b = a + 1 + len(K)
                if b >= len(X): continue
                if X[b] != X[a]: continue
                K1 = mrun(X, b)
                if sibrel(K, K1): continue
                nv += 1
                t = 0
                while t < len(K) and t < len(K1) and K[t] == K1[t]:
                    t += 1
                if t >= len(K) or t >= len(K1):
                    key = ('len-prefix', len(K) < len(K1))
                else:
                    x, x1 = K[t], K1[t]
                    rel = ('feq-sdrop' if (x1[0]==x[0] and x1[1]<x[1]) else
                           'fdrop-seq' if (x1[0]<x[0] and x1[1]==x[1]) else
                           'feq-srise' if (x1[0]==x[0] and x1[1]>x[1]) else 'other')
                    kend = (t == len(K) - 1)
                    k1climb = all(K1[i][0] < K1[i+1][0] for i in range(t, len(K1)-1))
                    hmK = K[0][1] == maxr1(K)
                    hmK1 = K1[0][1] == maxr1(K1)
                    key = (rel, 'Kend' if kend else 'Kmid', 'K1climb' if k1climb else 'K1osc',
                           hmK, hmK1)
                cls[key] += 1
                if key not in ex: ex[key] = (Xt, a, b, K, K1)
    print('violating tie pairs (dedup hosts):', nv)
    for k, v in sorted(cls.items(), key=lambda kv: -kv[1]):
        print(f'{v:5d}  {k}')
    for k, (X, a, b, K, K1) in list(ex.items())[:6]:
        print('EX', k, 'a=', a, 'b=', b)
        print('   K =', K)
        print('   K1=', K1)

if __name__ == '__main__':
    main()
