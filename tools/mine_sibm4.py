#!/usr/bin/env python3
"""Re-validate NT_tie on ALL fbseg windows, with closure+1 sampling
(also expand every closure member by one extra oper step — the sibm falsity
was missed because violations first appear one step beyond the closure).

For every host H in ST_PS-closure(+1), every window decomposition
  H = pre @ [pp] @ mid @ S @ post,  S = c # rest != [],
  all of mid@S dominated (fst > fst pp),  all of mid at level >= fst (hd S):
if dropWhile (fst c <) rest = c1 # rest1 and snd c1 = snd c (tie):
  CHECK:  not olt( proj (snd c) (NT K), proj (snd c1) (NT K1) )
  where K = takeWhile (fst c <) rest, K1 = takeWhile (fst c1 <) rest1.
Also classify the shape relation K1 vs K: equal / proper-prefix / OTHER,
and head-max stats, to design the repaired shape invariant.
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from fast_pss import oper, fmt
from wfe_explore import enum_ST
from valnorm import lt_term
from mine_e6 import NT
from mine_proj import proj

def maxr1(S): return max(c[1] for c in S)

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    hosts = set(ST)
    for M in ST:
        if len(M) < 2: continue
        for n in (1,2,3,4):
            hosts.add(tuple(oper(list(M), n)))
    print('hosts:', len(hosts))
    shape = Counter(); viol = []
    nchecked = 0
    seenK = set()
    for H in hosts:
        lh = len(H)
        for ppi in range(lh):
            lvpp = H[ppi][0]
            # dominated stretch after pp
            dend = ppi+1
            while dend < lh and H[dend][0] > lvpp: dend += 1
            # windows S = H[si:ei) inside (ppi, dend], mid = H[ppi+1:si)
            for si in range(ppi+1, dend):
                hdlv = H[si][0]
                if any(H[m][0] < hdlv for m in range(ppi+1, si)): continue
                c = H[si]
                for ei in range(si+1, dend+1):
                    rest = list(H[si+1:ei])
                    i = 0
                    while i < len(rest) and rest[i][0] > c[0]: i += 1
                    K, T = rest[:i], rest[i:]
                    if not T: continue
                    c1, rest1 = T[0], T[1:]
                    if c1[1] != c[1]: continue   # tie only
                    j = 0
                    while j < len(rest1) and rest1[j][0] > c1[0]: j += 1
                    K1 = rest1[:j]
                    key = (tuple(K), tuple(K1), c[1])
                    if key in seenK: continue
                    seenK.add(key)
                    nchecked += 1
                    # shape classification
                    if K1 == K: sh = 'equal'
                    elif len(K1) < len(K) and K[:len(K1)] == K1: sh = 'prefix'
                    else: sh = 'OTHER'
                    hm = 'hmK?' if not K else ('hmK=' if K[0][1]==maxr1(K) else 'hmK<')
                    hm1 = 'hmK1?' if not K1 else ('hmK1=' if K1[0][1]==maxr1(K1) else 'hmK1<')
                    shape[(sh, hm, hm1)] += 1
                    ok = not lt_term(proj(c[1], NT(K)), proj(c1[1], NT(K1)))
                    if not ok:
                        viol.append((fmt(H), ppi, si, ei, fmt(K), fmt(K1)))
    print('distinct (K,K1,u) checked:', nchecked)
    for k, v in sorted(shape.items(), key=lambda t: -t[1]):
        print('  ', k, v)
    print('NT_tie violations:', len(viol))
    for t in viol[:15]: print('  ', t)

if __name__ == '__main__':
    main()
