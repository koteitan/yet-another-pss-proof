#!/usr/bin/env python3
"""Verify the invariant `hasParent_last_ST_PS`:

  M in ST_PS, 1 < Lng M, NOT (entry M 0 (Lng M-1) = 0 AND entry M 1 (Lng M-1) = 0)
  ==> hasParent M (idx1 M (Lng M-1)) (Lng M-1).

i.e. the LAST column of every standard form of length>1 whose last column is
not the degenerate (0,0) base has a parent.

idx1 M j1 = 1 if entry M 1 j1 > 0 else 0; hasParent for idx1 means:
  if idx1==1: hasParent1(M,j1) ; else hasParent0(M,j1).

Any counterexample => the invariant is FALSE.
"""
import sys
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import Lng, idx1, entry, hasParent0, hasParent1
from wfe_explore import enum_ST

def has_parent_last(M):
    j1 = Lng(M)-1
    i1 = idx1(M, j1)
    return hasParent1(M, j1) if i1==1 else hasParent0(M, j1)

def run(seed_max_v, oper_ns, max_len, rounds):
    ST = list(enum_ST(seed_max_v=seed_max_v, oper_ns=oper_ns, max_len=max_len, rounds=rounds))
    tot=0; checked=0; bad=0; ex=[]
    for M in ST:
        n=Lng(M)
        if n<=1: continue
        j1=n-1
        if entry(M,0,j1)==0 and entry(M,1,j1)==0:
            continue  # degenerate (0,0) last column - excluded
        checked+=1
        if not has_parent_last(M):
            bad+=1
            if len(ex)<20: ex.append((M, idx1(M,j1)))
    print(f'corpus={len(ST)} len>1&nondegen-last={checked} NO-PARENT(bad)={bad}', flush=True)
    for e in ex: print('  COUNTEREXAMPLE', e)
    return bad

if __name__=='__main__':
    total_bad=0
    # progressively deeper closures
    for (v,ns,ml,r) in [(6,(1,2,3,4,5),16,9),
                        (5,(1,2,3,4,5,6),20,10),
                        (7,(1,2,3),18,9)]:
        print(f'--- params v={v} ns={ns} max_len={ml} rounds={r} ---', flush=True)
        total_bad += run(v,ns,ml,r)
    print('TOTAL BAD =', total_bad)
    print('DONE', flush=True)
