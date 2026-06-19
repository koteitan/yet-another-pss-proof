#!/usr/bin/env python3
"""The reduced HARD LEAF: for a SINGLE-TREE blockok(1) block B (translate B =
P y A Z, no sibling), prove Q(P y A Z) = forall x in Gterm0(P y A Z), olt x (PyAZ).
Each witness x = translate K, K a Gterm0 witness = contiguous infix of B.
Via seqlex_imp_olt: need seqlex(shift K, B) with shift K blockok(1).

The prior round found seqlex(shift K, B) NOT inductively provable for MULTI-ROOT
B (183/443 intermediate-node failure on the SubBlock derivation).  Question:
does restricting to SINGLE-TREE B make it provable by recursion on B's tree
structure?  A single tree B = (1,y) :: body, body all >= 2 (blockok 1, single
tree => body = takeWhile, no re-open at level 1).  Recurse: translate B = P y
(translate body) Z, body is a blockok-2 forest (possibly multi-root at level 2).

Hmm -- body itself can be MULTI-ROOT at level 2.  So single-tree at level 1 does
NOT give single-tree deeper.  Test:
  (A) For single-tree B, are ALL Gterm0 witnesses' canonical K such that
      seqlex(shift K, B) provable by the recursion that splits B = P y A Z and
      pushes into A = translate(body)?  Measure whether the seqlex fact composes
      down the SINGLE arg-spine (the only descent for a single tree at top).
  (B) Direct: is seqlex(shift K, B) for single-tree B reducible to the SAME fact
      on the deeper single-trees, i.e. does the recursion stay in 'single-tree'?
      NO (body multi-root).  So the hard leaf recurses back into the MULTI-ROOT
      case => the reduction does NOT bottom out.  CONFIRM this by checking
      whether the body (level-2 forest) is ever multi-root for single-tree B.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def steps1(B): return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))
def blockok(d, B):
    if not B: return True
    return B[0][0] == d and all(p[0] >= d for p in B) and steps1(B)
def split(B):
    c = B[0]; rest = B[1:]; i = 0
    while i < len(rest) and rest[i][0] > c[0]: i += 1
    return c, tuple(rest[:i]), tuple(rest[i:])

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        # B = host tail; if translate B = P y A Z (single tree) => B blockok 1 and
        # body = B[1:] (all > 1).  Is body multi-root at level 2 (i.e. body
        # re-opens at level 2 => its dropWhile(2<.) nonempty)?
        n_single = 0
        body_multiroot = 0
        ex = None
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            if S != Z: continue       # only single-tree at top
            if not blockok(1, B): continue
            n_single += 1
            body = B[1:]              # all > 1
            # does body re-open at level 2? body.dropWhile(2 < .) nonempty means
            # multi-root level-2 forest (so the deeper structure is NOT single-tree)
            c2, d2, s2 = split(body) if body else ((0,0),(),())
            if s2:
                body_multiroot += 1
                if ex is None: ex = (mfmt(B), mfmt(body))
        print(f'[+{rounds}] md={md} single-tree blockok-1 B: {n_single}  '
              f'of which body MULTI-ROOT at level 2: {body_multiroot}')
        if ex: print('   ex B', ex[0], 'body', ex[1])

if __name__ == '__main__':
    main()
