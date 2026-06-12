#!/usr/bin/env python3
"""Characterize ALL i1=0 (d0=0 by convention) bad blocks at closure+2:
dump the snd-pattern classes of M[j0..j1] to find the rigidity that
makes ginv_CT true.
Classes keyed by: block length, snd(j0), max interior snd - snd(j0),
whether interior snd pattern is 'climb by row-0 chain with snd <= snd(j0)+1'.
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from wfe_explore import enum_ST
from mine_sibm2 import bad_params
from fast_pss import oper, entry, Lng, idx1

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
    cls = Counter()
    ex = {}
    n = 0
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if i1 != 0: continue
        n += 1
        blk = M[j0:j1+1]
        rel = tuple((c[0]-blk[0][0], c[1]-blk[0][1]) if c[1] >= blk[0][1] else (c[0]-blk[0][0], -(blk[0][1]-c[1])) for c in blk)
        # snd pattern relative to snd(j0); cap classes by length<=6 else 'long'
        key = (len(blk), blk[0][1], tuple(c[1] for c in blk)) if len(blk) <= 7 else ('long', len(blk))
        cls[key] += 1
        if key not in ex: ex[key] = M
    print('i1=0 bad hosts:', n)
    for k, v in sorted(cls.items(), key=lambda kv: -kv[1])[:25]:
        print(f'{v:6d}  {k}')
    print('distinct classes:', len(cls))

if __name__ == '__main__':
    main()
