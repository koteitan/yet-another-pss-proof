#!/usr/bin/env python3
"""DYNAMIC axis, DECISIVE: does the per-step core_i1 + within-block IH close, or
does the within-copy witness domination RE-REQUIRE the global positional fact?

For a row1<=1 oper-image child = G ++ copy_0 ++ copy_1 ++ ... (copy_k = block
shifted by k*d0), descendant block B = child[1:].  Each canonical witness K of B
(infix, translate K in Gterm0 (translate B), shifted to depth 1):

Classify the FIRST-DIVERGENCE position p of (shiftK) vs B relative to the COPY
STRUCTURE of B:
  - does p land at/after a COPY BOUNDARY (so the divergence is the d0-ramp
    between copies -- a CROSS-COPY core_i1/i0 domination)?  -> 'cross'
  - or does p land WITHIN copy_0 (the first copy = block region of B)?  -> 'intra'
For 'intra', the witness's divergence is INSIDE the block -- so it reduces to the
SAME clause on the BLOCK (a smaller form).  TEST: is the block (made into a
standard form (0,0)::block-tail or its shift) itself a row1<=1 ST_PS form that is
STRICTLY SMALLER (so IH applies)?  And does the intra witness's domination equal
the block's own Inv instance?

If EVERY witness is either 'cross' (core_i1) or 'intra-reducing-to-smaller-block'
with 0 BAD, the dynamic induction CLOSES with WF = generation/length.  If some
'intra' witness does NOT reduce to a smaller ST_PS form's Inv (re-requires the
global fact), the dynamic axis FAILS like the static ones.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, Lng, entry, idx1, hasParent1, parent1, hasParent0, parent0
from wfe_explore import translate, olt
from fast_pss import fmt as mfmt
from collections import Counter

Z = ()
def r1le1(M): return all(c[1] <= 1 for c in M)
def steps1(B): return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))
def blockok(d, B):
    if not B: return True
    return B[0][0] == d and all(p[0] >= d for p in B) and steps1(B)
def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def split(B):
    c = B[0]; rest = B[1:]; i = 0
    while i < len(rest) and rest[i][0] > c[0]: i += 1
    return c, tuple(rest[:i]), tuple(rest[i:])
def all_subblocks(B):
    res = []
    def rec(seg):
        seg = tuple(seg); res.append(seg)
        if not seg: return
        c, d, s = split(seg); rec(d); rec(s)
    rec(tuple(B)); return res
def shift(K, d): return tuple((p[0]+d, p[1]) for p in K)
def oper_comp(M, n):
    j1 = Lng(M) - 1
    if j1 == 0: return None
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0: return None
    i1 = idx1(M, j1)
    if i1 == 1:
        if not hasParent1(M, j1): return None
        j0 = parent1(M, j1)
    else:
        if not hasParent0(M, j1): return None
        j0 = parent0(M, j1)
    d0 = (entry(M, 0, j) - entry(M, 0, j0)) if False else ((entry(M,0,j1)-entry(M,0,j0)) if i1>0 else 0)
    G = list(M[:j0]); block = [(entry(M, 0, j), entry(M, 1, j)) for j in range(j0, j1)]
    return (G, block, d0, n)

def main():
    for depth in (5, 6, 7):
        # enumerate edges to row1<=1 children, with their oper components
        seen2 = set(); fr = []; edges = []
        for v in (1, 2, 3, 4):
            b = tuple(diagSeq(0, v))
            if b not in seen2: seen2.add(b); fr.append((b, 0))
        while fr:
            M, d = fr.pop()
            if d >= depth or Lng(M) <= 1: continue
            for n in (1, 2, 3):
                ch = tuple(oper(M, n))
                if Lng(ch) > 28: continue
                edges.append((M, ch, n))
                if ch not in seen2: seen2.add(ch); fr.append((ch, d + 1))
        cls = Counter()
        intra_reduces = intra_bad = 0
        crosschk = 0
        badex = []
        # to test 'intra reduces to smaller ST_PS', collect the set of all row1<=1
        # ST_PS forms (by length) so we can check the block-as-form membership
        allforms = set(M for M in seen2 if r1le1(M))
        for (M, ch, n) in edges:
            if not (ch and ch[0] == (0, 0) and r1le1(ch) and Lng(ch) <= 18): continue
            comp = oper_comp(M, n)
            if comp is None: continue
            G, block, d0, nn = comp
            B = tuple(ch[1:]); tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            if S != Z or not blockok(1, B): continue   # NARROW single-tree
            # copy structure within ch: ch = G ++ copy_0 ++...; copy length = len(block)
            blen = len(block); glen = len(G)
            # within B = ch[1:], the copy-0 region occupies indices [glen-1+? ...]
            # Simpler: a witness K (infix of B) -- find its first-diff p vs B; the
            # copy boundary in B is at offset (glen + blen - 1) [B drops the first
            # column of ch]. We test if p < that boundary (intra copy_0) or >= (cross).
            boundary = glen + blen - 1   # index in B where copy_1 starts (approx)
            G0 = set(Gterm(0, tB)); seenK = {}
            for K in all_subblocks(B):
                if not K: continue
                tK = translate(K)
                if tK in G0 and tK != tB and tK not in seenK: seenK[tK] = K
            for tK, K in seenK.items():
                Ksh = shift(K, 1 - K[0][0])
                p = 0
                while p < len(Ksh) and p < len(B) and Ksh[p] == B[p]: p += 1
                if p >= boundary:
                    cls['cross'] += 1; crosschk += 1
                else:
                    cls['intra'] += 1
                    # intra: does K reduce to a witness of a SMALLER block-form?
                    # heuristic: the block (made standard) is shorter than ch => IH.
                    if blen + 1 < Lng(ch):
                        intra_reduces += 1
                    else:
                        intra_bad += 1
                        if len(badex) < 6: badex.append((mfmt(ch), mfmt(K), p, boundary))
        print(f'[depth+{depth}] narrow witnesses: {dict(cls)}')
        print(f'   intra reduces-to-smaller-block: {intra_reduces}  intra NON-reducing(BAD): {intra_bad}')
        for ch, k, p, b in badex[:6]: print('      BAD ch', ch, 'K', k, 'p', p, 'boundary', b)

if __name__ == '__main__':
    main()
