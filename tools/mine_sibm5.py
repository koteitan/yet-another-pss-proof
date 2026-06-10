#!/usr/bin/env python3
"""sibm2: the REPAIRED M-level sibling-run invariant (closure+1 sampling).

For every standard M (closure + one extra oper step), every adjacent
tie-sibling pair (a,b) — b = first stop of a's run, fst/snd equal, fst>0 —
with FULL runs K = mrun M a, K1 = mrun M b (truncated only by end of M):

  sibm2:  (both runs head-maximal when nonempty)  AND  one of
    (E)  K1 = K
    (P)  K1 proper prefix of K
    (F1) common prefix t, t < |K|, t < |K1|,
         fst K[t] = fst K1[t]  and  snd K[t] > snd K1[t]
    (F2) common prefix t, t < |K|, t < |K1|,
         fst K[t] > fst K1[t]
  (i.e. NOT: K proper prefix of K1; NOT: first-diff ascending)

Report family counts x category (PP/PC/CC) and any violations.
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from fast_pss import oper, fmt
from wfe_explore import enum_ST
from mine_sibm2 import mrun_stop

def maxr1(S): return max(c[1] for c in S)

def family(K, K1):
    if K1 == K: return 'E'
    t = 0
    while t < min(len(K), len(K1)) and K[t] == K1[t]: t += 1
    if t == len(K1): return 'P'          # K1 proper prefix of K
    if t == len(K): return 'VIOL:K-pref-K1'
    a, b = K[t], K1[t]
    if a[0] > b[0]: return 'F2'
    if a[0] == b[0] and a[1] > b[1]: return 'F1'
    return 'VIOL:ascend'

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    hosts = set(ST)
    for M in ST:
        if len(M) < 2: continue
        for n in (1,2,3,4):
            hosts.add(tuple(oper(list(M), n)))
    print('hosts:', len(hosts))
    fam = Counter(); viol = []
    hmviol = []
    npairs = 0
    for X in hosts:
        lx = len(X)
        for a in range(lx):
            if X[a][0] <= 0: continue
            b = mrun_stop(X, a)
            if b is None: continue
            if X[b] != X[a]: continue
            npairs += 1
            K = list(X[a+1:b])
            c = mrun_stop(X, b)
            K1 = list(X[b+1:(c if c is not None else lx)])
            f = family(K, K1)
            open_b = 'open' if c is None else 'closed'
            fam[(f, open_b)] += 1
            if f.startswith('VIOL'):
                viol.append((fmt(X), a, b, fmt(K), fmt(K1), f))
            if K and K[0][1] != maxr1(K):
                hmviol.append(('hmK', fmt(X), a, b))
            if K1 and K1[0][1] != maxr1(K1):
                hmviol.append(('hmK1', fmt(X), a, b))
    print('pairs:', npairs)
    for k, v in sorted(fam.items(), key=lambda t: -t[1]): print('  ', k, v)
    print('family violations:', len(viol))
    for t in viol[:10]: print('  ', t)
    print('head-max violations:', len(hmviol))
    for t in hmviol[:10]: print('  ', t)

if __name__ == '__main__':
    main()
