#!/usr/bin/env python3
"""Equivalence A, correct reading: pfire 0 (translate B) on the RAW term b.

Lean: pfire 0 b := exists g in Gterm 0 b, not g <o b.
Lever (Nrmstep:1722): pfire 0 b  <=>  lead b < maxsub b.

BMOCF Ascend firing at a psi_0-node with argument block B = the matrix whose
translate is b.  We test several candidate matrix-level readings of
  (0,0) <=_M (0, j_1)
and report which (if any) matches pfire 0 (translate B) exactly.

Candidate readings of the firing block B and its j_1:
  R1: B = full descendant block, condition = le0(B,0,last)            (row-0)
  R2: B = full block, condition = exists row-1 parent of last col      (row-1 Next)
  R3: lead(translate B) < maxsub(translate B)  (the Lean lever itself, sanity)
We enumerate all SubBlocks B that occur as Gterm-0 arguments, i.e. all
descendant blocks (0,0)::rest of ST_PS forms, since the core is about those.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import (oper, diagSeq, Lng, le0, nextrel1, entry, idx1,
                      hasParent1, parent1, hasParent0, parent0)
from wfe_explore import translate, olt, maxsub, fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import build_next_le, enum_depth

def lead(t):
    return t[0] if t else None  # t = (a,b,c): a is the SUBSCRIPT (row1 value)

def pfire0(b):
    """Lean lever: pfire 0 b <=> lead b < maxsub b (b!=Z)."""
    if b == (): return False
    return lead(b) < maxsub(b)

# ----- enumerate descendant blocks of ST_PS forms -----
def subblocks(M):
    """All SubBlocks (takeWhile/dropWhile reflexive-transitive sub-blocks),
    matching the lean SubBlock relation (the head-0 descendant decomposition)."""
    M = list(M)
    res = []
    def rec(seg):
        seg = list(seg)
        res.append(tuple(seg))
        if not seg: return
        (x, y) = seg[0]; rest = seg[1:]
        i = 0
        while i < len(rest) and rest[i][0] > x: i += 1
        # descendant block (the dominated takeWhile part)
        if rest[:i]:
            rec(rest[:i])
        # sibling tail
        if rest[i:]:
            rec(rest[i:])
    rec(M)
    return res

def ascend_row0(B):
    """(0,0) <=_M (0, j_1) reading R1: row-0 reachability of last column."""
    n = Lng(B)
    if n == 0: return False
    return le0(tuple(B), 0, n-1)

def ascend_row1parent(B):
    """R2: last column has a row-1 Next-parent (genuine row-1 ascension)."""
    n = Lng(B)
    if n <= 1: return False
    j1 = n-1
    if entry(B, 1, j1) == 0: return False
    return any(nextrel1(tuple(B), j0, j1) for j0 in range(j1))

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        corpus = [M for M in seen if Lng(M) <= 16]
        md = max(seen.values())
        blocks = set()
        for M in corpus:
            for B in subblocks(M):
                if B: blocks.add(B)
        # counts
        m1 = mis1 = m2 = mis2 = 0
        ex1 = []; ex2 = []
        for B in blocks:
            b = translate(B)
            lf = pfire0(b)
            r1 = ascend_row0(B)
            r2 = ascend_row1parent(B)
            if lf == r1: m1 += 1
            else:
                mis1 += 1
                if len(ex1) < 6: ex1.append((B, lf, r1))
            if lf == r2: m2 += 1
            else:
                mis2 += 1
                if len(ex2) < 6: ex2.append((B, lf, r2))
        print(f'[closure+{rounds}] maxdepth={md} blocks={len(blocks)}')
        print(f'  A.R1 pfire0 == le0(0,last):       match={m1} mismatch={mis1}')
        for B, lf, r in ex1[:5]:
            print('     ', mfmt(B), '-> b', tfmt(translate(B)), 'pfire', lf, 'R1', r)
        print(f'  A.R2 pfire0 == row1-Next-parent:  match={m2} mismatch={mis2}')
        for B, lf, r in ex2[:5]:
            print('     ', mfmt(B), '-> b', tfmt(translate(B)), 'pfire', lf, 'R2', r)

if __name__ == '__main__':
    main()
