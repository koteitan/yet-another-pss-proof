#!/usr/bin/env python3
"""ROW-1 AXIS, step 1: confirm seqlex(shift K, B) is ROW-1-decided on the NARROW
pinned object (single-tree blockok-1 B, canonical arg-witness K only).

Pinned object: host (0,0)::B in ST_PS row1<=1, translate B = P y A Z (S=Z,
single tree), so B is blockok-1.  Canonical arg-witnesses K: the Gterm_translate_
subblock witnesses, i.e. contiguous infixes B[i:j] with translate K in
Gterm0(translate B), translate K != translate B.

Shift K row0 to depth 1: delta = 1 - K[0].1, Ksh = K.map(p -> (p.1+delta, p.2)).
Then BOTH Ksh and B are blockok-1 (head row0 = 1).  seqlex(Ksh, B) is decided at
the first differing column.  TABULATE:
  - at the first differing column j: is it a ROW-0 diff or a ROW-1 diff?
  - if row-1 diff: is Ksh[j].2 < B[j].2 (shift-K strictly lower)?  [the win]
  - if row-0 diff: Ksh[j].1 vs B[j].1?  (this would be a LEVEL decision, the
    row-0 route -- we want this to be RARE / absent on the narrow object)
  - or Ksh is a proper PREFIX of B (runs out first) -> seqlex true by length.
Report counts @+5/+6/+7.  If the decision is (row-1 lower) OR (prefix) with
ZERO genuine row-0-decided cases, the leaf is purely a row-1/subscript fact.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth
from collections import Counter

Z = ()
def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def steps1(B): return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))
def blockok(d, B):
    if not B: return True
    return B[0][0] == d and all(p[0] >= d for p in B) and steps1(B)
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
def shift(K, delta): return tuple((p[0]+delta, p[1]) for p in K)
def pairlt(p, q): return p[0] < q[0] or (p[0] == q[0] and p[1] < q[1])
def seqlex(M, N):
    M = list(M); N = list(N); i = 0
    while i < len(M) and i < len(N):
        if M[i] != N[i]: return pairlt(M[i], N[i])
        i += 1
    if i == len(M): return len(N) > len(M)
    return False

def first_diff(M, N):
    """return (kind, j) where kind in 'row0','row1','prefixM','prefixN','equal'."""
    i = 0
    while i < len(M) and i < len(N):
        if M[i] != N[i]:
            if M[i][0] != N[i][0]: return ('row0', i)
            return ('row1', i)
        i += 1
    if len(M) < len(N): return ('prefixM', i)   # M ran out, M proper prefix of N
    if len(M) > len(N): return ('prefixN', i)
    return ('equal', i)

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        kinds = Counter()
        row1_lower = row1_notlower = 0
        row0_examples = []
        chk = 0
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            if S != Z: continue            # SINGLE-TREE only
            if not blockok(1, B): continue
            G0 = set(Gterm(0, tB))
            seenK = {}
            for K in all_subblocks(B):
                tK = translate(K)
                if tK in G0 and tK != tB and tK != Z and tK not in seenK:
                    seenK[tK] = K
            for tK, K in seenK.items():
                if not K: continue
                delta = 1 - K[0][0]
                Ksh = shift(K, delta)
                chk += 1
                kind, j = first_diff(Ksh, B)
                kinds[kind] += 1
                if kind == 'row1':
                    if Ksh[j][1] < B[j][1]: row1_lower += 1
                    else: row1_notlower += 1
                elif kind == 'row0':
                    if len(row0_examples) < 8:
                        row0_examples.append((mfmt(B), mfmt(Ksh), j, Ksh[j], B[j]))
        print(f'[+{rounds}] md={md} single-tree canonical-K checked={chk}')
        print(f'   first-diff kind: {dict(kinds)}')
        print(f'   row1-decided: shift-K lower={row1_lower}  NOT-lower={row1_notlower}')
        for b, k, j, kc, bc in row0_examples[:8]:
            print(f'   ROW0-decided B={b} Ksh={k} j={j} Ksh[j]={kc} B[j]={bc}')

if __name__ == '__main__':
    main()
