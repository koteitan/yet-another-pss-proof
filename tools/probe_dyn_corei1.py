#!/usr/bin/env python3
"""DYNAMIC axis, step 4: locate the per-step core_i1 mechanism.

Inv(child) holds for EVERY row1<=1 oper-image, independent of parent.  So Inv is
provable per-step from the TILING.  core_i1 (Mechanized:737) shape:
  translate( (v0,w0)::R ++ (c::C') )  <o  translate( (v0,w0)::R ++ [lp] )
  given hR (R above v0), Cge (C' >= c), Croot (c.1=lp.1), lpv (v0<lp.1),
  lead_lt (c.2 < lp.2).
i.e. a block extended by a LOWER-subscript continuation is dominated by the same
block extended by a single higher-subscript pair.  This is the ascending-copy
domination.

The arg-direction witness olt(translate K, translate B): we want to show each
canonical witness K (infix) is dominated by B via this shape.  TEST on the
NARROW pinned object (single-tree blockok-1 B), for each witness:
  does olt(translate K, translate B) match the core_i1 pattern, i.e. is there a
  decomposition  B = (v0,w0)::R ++ tail  and  K (shifted) = (v0,w0)::R ++ cont
  with cont's lead-subscript < tail's, so core_i1 fires?
We measure: for each witness, find the longest common prefix P of (shift K) and B;
then B = P ++ Btail, shiftK = P ++ Ktail; check Ktail.head vs Btail.head is a
core_i1-style domination (Ktail.head.1 == Btail.head.1 [row0 tie at divergence]
and Ktail.head.2 < Btail.head.2 [row1 strictly lower], OR Ktail empty [prefix]).
This is the per-divergence core_i1/i0 application.  0-viol => core_i1 (+i0 for the
row0-diff case) discharges every witness, and the dynamic generation composes them.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, Lng, entry
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

def enum_st_ps(depth, maxlen):
    seen = set(); frontier = []
    for v in (1, 2, 3, 4):
        base = tuple(diagSeq(0, v))
        if base not in seen: seen.add(base); frontier.append((base, 0))
    while frontier:
        M, d = frontier.pop()
        if d >= depth or Lng(M) <= 1: continue
        for n in (1, 2, 3):
            ch = tuple(oper(M, n))
            if Lng(ch) > maxlen: continue
            if ch not in seen: seen.add(ch); frontier.append((ch, d + 1))
    return seen

def main():
    for depth in (5, 6, 7):
        seen = enum_st_ps(depth, 28)
        hosts = [M for M in seen if Lng(M) <= 18 and r1le1(M) and M and M[0] == (0, 0)]
        chk = 0
        # classify the divergence column at the first diff of (shiftK, B)
        div = Counter()       # 'row1lower','row0lower','prefix','BAD'
        bad = []
        for M in hosts:
            B = tuple(M[1:]); tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            if S != Z or not blockok(1, B): continue   # NARROW: single-tree
            G0 = set(Gterm(0, tB)); seenK = {}
            for K in all_subblocks(B):
                if not K: continue
                tK = translate(K)
                if tK in G0 and tK != tB and tK not in seenK: seenK[tK] = K
            for tK, K in seenK.items():
                Ksh = shift(K, 1 - K[0][0])
                chk += 1
                # first diff
                i = 0
                while i < len(Ksh) and i < len(B) and Ksh[i] == B[i]: i += 1
                if i >= len(Ksh):           # shiftK is a prefix of B
                    div['prefix'] += 1
                elif i >= len(B):
                    div['BAD-Klonger'] += 1
                    if len(bad) < 6: bad.append((mfmt(B), mfmt(Ksh), 'Klonger'))
                else:
                    kc = Ksh[i]; bc = B[i]
                    if kc[0] == bc[0] and kc[1] < bc[1]: div['row1lower'] += 1
                    elif kc[0] < bc[0]: div['row0lower'] += 1
                    else:
                        div['BAD'] += 1
                        if len(bad) < 6: bad.append((mfmt(B), mfmt(Ksh), f'col{i} {kc} vs {bc}'))
        print(f'[depth+{depth}] single-tree narrow witnesses checked={chk}')
        print(f'   divergence class: {dict(div)}')
        for b, k, w in bad[:6]: print('      BAD', b, k, w)

if __name__ == '__main__':
    main()
