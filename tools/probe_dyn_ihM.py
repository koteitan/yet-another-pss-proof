#!/usr/bin/env python3
"""DYNAMIC axis, DECISIVE-2: does each child-witness domination reduce to either
(a) a CROSS-COPY core_i1/i0 fact (provable directly from the tiling), or
(b) a witness of the PARENT M (shorter ST_PS derivation => IH), with 0 BAD?

This is the proper dynamic-induction test: IH on the parent M's clause.
child = G ++ copies of block(=(v0,w0)::R), block = M[j0:j1], lp = M[j1].
B_child = child[1:].  translate(B_child) and its Gterm0 witnesses.

For each canonical witness tK of B_child (single-tree narrow), the domination
olt(tK, translate B_child).  We ask: is tK 'inherited' from M -- i.e. is tK equal
to (or olt-reducible to) translate of a witness of M's OWN descendant block?
Test: tK in Gterm0(translate(M[1:]))?  (witness inherited from parent's clause).
If the residual witnesses (NOT inherited from M) are exactly the cross-copy ones
that core_i1 handles, the induction closes:
   Inv(child) <= Inv(M) [IH, M shorter derivation] + core_i1 [cross-copy] .

Classify each child-witness tK:
  'fromM'  : tK in Gterm0(translate(M[1:]))   [IH supplies olt(tK, translate M[1:]);
             need lift to olt(tK, translate B_child)]
  'newcopy': tK not from M but is a tiled copy / cross-copy (core_i1 territory)
Then the LIFT 'fromM': does olt(tK, translate M[1:]) => olt(tK, translate B_child)?
i.e. is translate(M[1:]) <=o translate(B_child) (the child dominates parent's block)?
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
def ole(s, t): return s == t or olt(s, t)
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

def main():
    for depth in (5, 6, 7):
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
        lift_chk = lift_bad = 0
        newcopy_olt_bad = 0
        liftex = newex = None
        for (M, ch, n) in edges:
            if not (ch and ch[0] == (0, 0) and r1le1(ch) and Lng(ch) <= 18): continue
            if not (M and M[0] == (0, 0)): continue
            Bc = tuple(ch[1:]); tBc = translate(Bc)
            if tBc == Z: continue
            y, A, S = tBc
            if S != Z or not blockok(1, Bc): continue   # NARROW
            Bm = tuple(M[1:]); tBm = translate(Bm)
            G0m = set(Gterm(0, tBm))
            G0c = set(Gterm(0, tBc)); seenK = {}
            for K in all_subblocks(Bc):
                if not K: continue
                tK = translate(K)
                if tK in G0c and tK != tBc and tK not in seenK: seenK[tK] = K
            for tK in seenK:
                if tK in G0m:
                    cls['fromM'] += 1
                    # lift: olt(tK, tBm) [IH] => olt(tK, tBc)?  via tBm <=o tBc
                    lift_chk += 1
                    # we have olt(tK,tBm) by IH (parent clause). need olt(tK,tBc).
                    if olt(tK, tBm) and not olt(tK, tBc):
                        lift_bad += 1
                        if liftex is None: liftex = (mfmt(M), mfmt(ch))
                else:
                    cls['newcopy'] += 1
                    if not olt(tK, tBc):
                        newcopy_olt_bad += 1
                        if newex is None: newex = (mfmt(M), mfmt(ch))
        print(f'[depth+{depth}] narrow child-witnesses: {dict(cls)}')
        print(f'   LIFT fromM (olt tK tBm => olt tK tBc): chk={lift_chk} BAD={lift_bad}')
        if liftex: print('      LIFTbad M', liftex[0], 'ch', liftex[1])
        print(f'   newcopy witnesses olt tBc: BAD={newcopy_olt_bad}')
        if newex: print('      NEWbad M', newex[0], 'ch', newex[1])

if __name__ == '__main__':
    main()
