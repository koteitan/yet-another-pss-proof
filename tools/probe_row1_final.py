#!/usr/bin/env python3
"""ROW-1 AXIS, final check: is seqlex(shift K, B) provable from a LOCAL relation
between the infix K=B[i:j] and B, or is the first-diff POSITION genuinely global?

For each canonical witness K=B[i:j] (single-tree blockok-1 B), shift to Ksh.
Find the first-diff position p between Ksh and B.  Test:
  (Q1) Is p determined by a LOCAL rule (e.g. p = first column where the infix's
       row0-ascent-pattern diverges from B's prefix)?  Tabulate p vs i (start) and
       vs the structure.
  (Q2) Is the first-diff ALWAYS within the first min(i+1, ...) columns -- i.e.
       bounded by the start offset?  Or can it be arbitrarily deep (global)?
  (Q3) The decisive soundness Q: does seqlex(Ksh,B) follow from
       'Ksh[0..p] <=_pairlt B[0..p] columnwise with strict at p' where p is the
       first diff -- which is just seqlex.  Is there a NON-positional certificate?
       Test: Ksh[p] is strictly pairlt-below B[p].  Is B[p] (the column where
       B 'wins') always B's column at the SAME depth as Ksh's run-end -- a
       structural anchor -- or arbitrary?
Honest goal: determine if the first-diff position is GLOBAL (=> Towsner) or LOCAL.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth
from probe_row1_align import blockok
from collections import Counter

Z = ()
def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def split(B):
    c = B[0]; rest = B[1:]; i = 0
    while i < len(rest) and rest[i][0] > c[0]: i += 1
    return c, tuple(rest[:i]), tuple(rest[i:])
def all_subblocks_pos(B):
    res = []
    def rec(seg, start):
        seg = tuple(seg); res.append((seg, start))
        if not seg: return
        c = seg[0]; rest = seg[1:]; i = 0
        while i < len(rest) and rest[i][0] > c[0]: i += 1
        rec(rest[:i], start+1); rec(rest[i:], start+1+i)
    rec(tuple(B), 0); return res
def shift(K, d): return tuple((p[0]+d, p[1]) for p in K)
def pairlt(p, q): return p[0] < q[0] or (p[0] == q[0] and p[1] < q[1])
def first_diff(M, N):
    i = 0
    while i < len(M) and i < len(N):
        if M[i] != N[i]: return i
        i += 1
    return min(len(M), len(N))   # one ran out

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        # Q2: is first-diff position p <= start-offset i + 1 (LOCAL bound)?
        p_le_i = p_gt_i = 0
        # distribution of (p - i)
        pmidist = Counter()
        chk = 0
        deepex = []
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            if S != Z or not blockok(1, B): continue
            G0 = set(Gterm(0, tB)); seenK = {}
            for (K, i) in all_subblocks_pos(B):
                if not K: continue
                tK = translate(K)
                if tK in G0 and tK != tB and tK not in seenK:
                    seenK[tK] = (K, i)
            for tK, (K, i) in seenK.items():
                Ksh = shift(K, 1 - K[0][0])
                p = first_diff(Ksh, B)
                chk += 1
                pmidist[p - i] += 1
                if p <= i + 1: p_le_i += 1
                else:
                    p_gt_i += 1
                    if len(deepex) < 6: deepex.append((mfmt(B), mfmt(Ksh), i, p))
        print(f'[+{rounds}] md={md} single-tree canonical checked={chk}')
        print(f'   first-diff p <= start-offset i+1 (LOCAL): {p_le_i}   p > i+1 (DEEP/global): {p_gt_i}')
        print(f'   (p - i) distribution: {dict(sorted(pmidist.items()))}')
        for b, k, i, p in deepex[:6]:
            print(f'   DEEP B={b} Ksh={k} i={i} firstdiff p={p}')

if __name__ == '__main__':
    main()
