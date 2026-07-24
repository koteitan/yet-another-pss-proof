#!/usr/bin/env python3
"""Faithful BMOCF Ascend on the SUBSCRIPT-PATH array, and the firing test.

In the 2-row case a subscript a in Idx is a single nat (length-1 non-increasing
array).  Descending the term t = psi_{a0}(psi_{a1}(... )) accumulates the
subscript array M' = (a0)(a1)... .  The Ascend firing condition for the OUTER
psi_{a0} is  (0,0) <=_{M'} (0, j_1)  with j_1 = Lng(M')-1 -- but note M' is the
chain of subscripts seen so far, a 1-COLUMN-PER-NESTING array, and row index i
runs over the (single) component of each subscript (i in {0} for 2-row).

We compute the subscript spine of b and test whether the BMOCF Ascend firing
(computed on that spine viewed as a matrix of subscripts) matches pfire 0 b.
We try the natural spine readings.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import le0, diagSeq, Lng, oper, nextrel1, entry
from wfe_explore import translate, olt, maxsub
from fast_pss import fmt as mfmt
from wfe_explore import fmt as tfmt
from probe_bmocf_ancestor import build_next_le, enum_depth
from probe_bmocf_equivA import subblocks, pfire0

def subscript_spine(b):
    """leading-arg chain subscripts: a0,a1,... following t[1] (first arg)."""
    s = []
    while b != ():
        a, arg, sib = b
        s.append(a)
        b = arg
    return s

def all_subscripts(b):
    """multiset/list of ALL subscripts in b (any position)."""
    s = []
    def rec(t):
        if t == (): return
        a, arg, sib = t
        s.append(a); rec(arg); rec(sib)
    rec(b)
    return s

def ascend_fire_spine(b):
    """BMOCF (0,0)<=_M(0,j1) where M = subscript spine as a 1-row array of
    single-nat columns.  Row-0 ancestry on a 1-row array reduces to: column 0
    reaches the last column under nextrel0 transitive closure on row-0 values =
    the spine subscripts."""
    sp = subscript_spine(b)
    if len(sp) <= 1: return False  # j1=0 -> only reflexive, no genuine ascension
    # build a 1-row "matrix": columns are (sp[j], 0); le0 uses row0 only.
    M = tuple((v, 0) for v in sp)
    return le0(M, 0, len(sp)-1)

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        corpus = [M for M in seen if Lng(M) <= 16]
        md = max(seen.values())
        blocks = set()
        for M in corpus:
            for B in subblocks(M):
                if B: blocks.add(B)
        # Test: pfire0 b  vs  lead b < maxsub b   (sanity of lever)  &
        #       pfire0 b  vs  ascend_fire_spine b
        m_lever = mis_lever = 0
        m_sp = mis_sp = 0; ex_sp = []
        for B in blocks:
            b = translate(B)
            lf = pfire0(b)
            # lever sanity is definitional here (pfire0 IS the lever); skip.
            sp = ascend_fire_spine(b)
            if lf == sp: m_sp += 1
            else:
                mis_sp += 1
                if len(ex_sp) < 8: ex_sp.append((B, b, lf, sp))
        print(f'[closure+{rounds}] maxdepth={md} blocks={len(blocks)}')
        print(f'  A.spine pfire0 == ascend(subscript-spine): match={m_sp} mismatch={mis_sp}')
        for B, b, lf, sp in ex_sp[:8]:
            print('     ', mfmt(B), 'b', tfmt(b), 'spine', subscript_spine(b),
                  'pfire', lf, 'ascend', sp)

if __name__ == '__main__':
    main()
