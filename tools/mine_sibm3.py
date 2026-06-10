#!/usr/bin/env python3
"""Dump concrete instances of the delicate sibm_oper_bad subcases:
  D1: PP or PC pairs whose b-run reaches END of X with n>=2
  D2: d0>0 block config CFG-A: exists qa in (0,L): e0(j0+qa)=e0(j1) and
      tail-clear (all later block offsets > e0(j1)); report r1 relation
      e1(j0+qa) vs e1(j0) and vs e1(j1).
  D3: CC-same pairs with b-run leaving the copy (leave+1/END) under d0>0:
      what does the extended run look like vs mrun X a?
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from fast_pss import Lng, entry, oper, fmt
from wfe_explore import enum_ST
from mine_sibm2 import bad_params, mrun_stop, region

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    d1 = []
    cfgA = Counter(); cfgB = []
    d3 = Counter()
    for M in ST:
        bp = bad_params(list(M))
        if bp is None: continue
        j0, j1, i1, d0 = bp
        L = j1 - j0
        # D2: block config scan (pure M-level)
        if d0 > 0:
            for qa in range(1, L):
                if entry(M,0,j0+qa) == entry(M,0,j1) and \
                   all(entry(M,0,j0+q) > entry(M,0,j1) for q in range(qa+1, L)):
                    rel = ('e1[qa]%se1[j0]' % ('<' if entry(M,1,j0+qa)<entry(M,1,j0)
                           else ('=' if entry(M,1,j0+qa)==entry(M,1,j0) else '>')),
                           'e1[qa]%se1[j1]' % ('<' if entry(M,1,j0+qa)<entry(M,1,j1)
                           else ('=' if entry(M,1,j0+qa)==entry(M,1,j1) else '>')))
                    cfgA[rel] += 1
                    if entry(M,1,j0+qa) == entry(M,1,j0):
                        cfgB.append((fmt(M), j0, j1, qa))
        for n in range(1, 5):
            X = oper(list(M), n)
            for a in range(len(X)):
                if X[a][0] <= 0: continue
                b = mrun_stop(X, a)
                if b is None: continue
                if X[b] != X[a]: continue
                c = mrun_stop(X, b)
                ra, rb = region(a,j0,L), region(b,j0,L)
                if c is None and n >= 2 and (ra[0]=='P'):
                    runa = X[a+1:b]; runb = X[b+1:]
                    pref = (runa == runb) or (len(runb)<len(runa) and runa[:len(runb)]==runb)
                    d1.append((fmt(M), n, (j0,j1,d0), a, b,
                               'runa=%s runb=%s pref=%s' % (fmt(runa), fmt(runb), pref)))
                if ra[0]=='C' and rb[0]=='C' and ra[1]==rb[1] and d0>0 and c is not None:
                    rc = region(c,j0,L)
                    if rc[0]=='C' and rc[1]>rb[1]:
                        runa = X[a+1:b]; runb = X[b+1:c]
                        pref = (runa==runb) or (len(runb)<len(runa) and runa[:len(runb)]==runb)
                        d3[('d0>0 leave', pref)] += 1
                        if not pref: print('D3VIOL', fmt(M), n, a, b, c)
    print('=== D1: P*/END pairs with n>=2 ===', len(d1))
    seen=set()
    for t in d1[:40]:
        key=t[0]
        if key in seen: continue
        seen.add(key)
        print('  ', t)
    print('=== D2: CFG-A r1 relations ===')
    for k,v in sorted(cfgA.items(), key=lambda t:-t[1]): print('  ', k, v)
    print('   CFG-B (must be empty):', len(cfgB), cfgB[:5])
    print('=== D3: CC-same d0>0 leaving runs ===')
    for k,v in d3.items(): print('  ', k, v)

if __name__ == '__main__':
    main()
