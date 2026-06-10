#!/usr/bin/env python3
"""Premise-mine the NEW value lemma NT_lexdiff_lt on a SYNTHETIC class
(no host realizability), to freeze a sound pure statement.

Class: run-shaped segments over base level l (use l=0 wlog? levels enter
translate only via comparisons; ADD a shift test l in {0,1}):
  seg discipline D(l): nonempty, all fst > l, hd fst = l+1, steps fst <= +1.
  (= blockok (l+1) within a dominated run)
Subscripts 0..smax free; optional head-max.

Test pairs K = p @ [x] + r, K1 = p @ [x1] + r1 with
  LF1: fst x1 = fst x and snd x1 < snd x
  LF2: fst x1 < fst x and snd x1 = snd x
  (also probe LF3: fst x1 < fst x and snd x1 < snd x,
              LF4: fst x1 < fst x and snd x1 > snd x  -- for the record)
where K, K1 BOTH satisfy D(l) (note: automatic for prefix-compatible splits
except step discipline at the divergence and inside r1).

CHECK: olt(NT K1, NT K) strict?  with/without head-max on both.
"""
import sys
sys.path.insert(0, '.')
from itertools import product
from collections import Counter
from valnorm import lt_term
from mine_e6 import NT

def gen_segs(l, maxlen, maxlv, smax):
    """All D(l) segments with levels in (l, l+maxlv], length <= maxlen."""
    out = []
    def rec(seg):
        if seg:
            out.append(tuple(seg))
            if len(seg) == maxlen: return
        if not seg:
            for s in range(smax+1):
                rec([(l+1, s)])
            return
        last = seg[-1][0]
        for lv in range(l+1, min(last+1, l+maxlv)+1):
            for s in range(smax+1):
                seg.append((lv, s)); rec(seg); seg.pop()
    rec([])
    return out

def headmax(S): return S[0][1] == max(c[1] for c in S)

def main():
    l = 0
    segs = gen_segs(l, 5, 3, 2)
    print('segs:', len(segs))
    byshape = {}
    for S in segs:
        byshape.setdefault(len(S), []).append(S)
    res = Counter(); ex = {}
    nt = {}
    def NTc(S):
        if S not in nt: nt[S] = NT(list(S))
        return nt[S]
    n = 0
    for K in segs:
        for K1 in segs:
            # common prefix
            t = 0
            while t < min(len(K), len(K1)) and K[t] == K1[t]: t += 1
            if t == len(K) or t == len(K1): continue
            x, x1 = K[t], K1[t]
            if x1[0] == x[0] and x1[1] < x[1]: lf = 'LF1'
            elif x1[0] < x[0] and x1[1] == x[1]: lf = 'LF2'
            elif x1[0] < x[0] and x1[1] < x[1]: lf = 'LF3'
            elif x1[0] < x[0] and x1[1] > x[1]: lf = 'LF4'
            else: continue
            hm = headmax(K) and headmax(K1)
            n += 1
            ok = lt_term(NTc(K1), NTc(K))
            res[(lf, 'hm' if hm else 'nohm', 'olt' if ok else 'FAIL')] += 1
            if not ok and (lf, hm) not in ex:
                ex[(lf, hm)] = (K, K1)
    print('pairs tested:', n)
    for k, v in sorted(res.items()): print('  ', k, v)
    for k, v in ex.items(): print('  FAIL ex', k, v)

if __name__ == '__main__':
    main()
