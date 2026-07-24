#!/usr/bin/env python3
"""Equivalence A and B between the lean firing/proj model and BMOCF Ascend.

A: lean firing  <=>  BMOCF Ascend firing condition  (0,0) <=_M (0,j_1)
B: proj maxo-violator selection  <=>  i_0 = max{i | (i,0)<=_M(i,j_1)}

We interpret firing at three granularities and report which (if any) matches:
  A-oper : the whole-matrix oper "genuine tiling vs Pred" branch.
  A-seg  : the per-decomposition (col,seg) firing proj(col.row1, NT(seg))!=NT(seg)
           with the BMOCF condition computed on the segment's own matrix.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import (oper, diagSeq, Lng, le0, nextrel1, entry, idx1,
                      hasParent1, parent1)
from wfe_explore import translate, olt, maxsub
from fast_pss import fmt
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj
from mine_e6 import NT, decomp_all
from mine_e5 import trans_abs
from probe_bmocf_ancestor import build_next_le, enum_depth

# ---- BMOCF row-0 ancestor firing condition on a matrix M:  (0,0)<=_M(0,j1) ----
def ascend_fires(M):
    n = Lng(M)
    if n == 0: return False
    j1 = n - 1
    return le0(M, 0, j1)   # (0,0) <=_M (0,j1)  -- verified == build_next_le row0

def ascend_i0(M, i1_cap=1):
    """i_0 = max{ i <= i1_cap | (i,0) <=_M (i,j1) } per Ascend.  -1 if none."""
    n = Lng(M)
    if n == 0: return -1
    j1 = n - 1
    nx, le = build_next_le(M)
    best = -1
    for i in range(min(i1_cap, 1) + 1):  # 2-row -> i in {0,1}
        if (0, j1) in le[i]:
            best = i
    return best

# ---- lean firing notions ----
def oper_genuinely_fires(M):
    """True iff oper does the genuine tiling branch (not M / not Pred)."""
    n = Lng(M)
    if n <= 1: return False
    j1 = n - 1
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0: return False  # Pred
    i1 = idx1(M, j1)
    if i1 == 1:
        if not hasParent1(M, j1): return False
    else:
        # i1==0: needs unique row0 parent
        from fast_pss import hasParent0
        if not hasParent0(M, j1): return False
    return True

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        corpus = [M for M in seen if Lng(M) <= 16]
        md = max(seen.values())

        # ---- A-oper: whole-matrix firing vs ascend_fires ----
        a_match = a_mis = 0; exA = []
        for M in corpus:
            if Lng(M) <= 1: continue
            lean_f = oper_genuinely_fires(M)
            bmocf_f = ascend_fires(M)
            if lean_f == bmocf_f: a_match += 1
            else:
                a_mis += 1
                if len(exA) < 6: exA.append((M, lean_f, bmocf_f))

        # ---- A-seg: per-decomposition firing vs ascend condition on the segment ----
        s_match = s_mis = 0; exS = []
        for M in corpus:
            pairs = []
            decomp_all(list(M), pairs)
            for (col, seg) in pairs:
                if not seg: continue
                a = col[1]
                nt = NT(seg)
                lean_f = (proj(a, nt) != nt)
                # BMOCF condition on the segment as its own matrix:
                bmocf_f = ascend_fires(tuple(seg))
                if lean_f == bmocf_f: s_match += 1
                else:
                    s_mis += 1
                    if len(exS) < 8: exS.append((M, col, seg, lean_f, bmocf_f))

        print(f'[closure+{rounds}] hosts={len(seen)} used={len(corpus)} maxdepth={md}')
        print(f'  A-oper (whole-matrix fire == (0,0)<=_M(0,j1)): match={a_match} mismatch={a_mis}')
        for M, lf, bf in exA[:4]:
            print('     ', fmt(M), 'lean', lf, 'bmocf', bf)
        print(f'  A-seg  (per-segment fire == ascend on seg):   match={s_match} mismatch={s_mis}')
        for M, col, seg, lf, bf in exS[:6]:
            print('     M', fmt(M), 'col', col, 'seg',
                  ''.join(f'({x},{y})' for x, y in seg), 'lean', lf, 'bmocf', bf)

if __name__ == '__main__':
    main()
