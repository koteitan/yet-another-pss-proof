#!/usr/bin/env python3
"""Verify the CLEAN recursion for the root clause Q(tB) = forall x in Gterm0 tB, olt x tB.

Structure: tB = translate B = P y A S, A=translate(desc), S=translate(sib),
desc = B[1:].takeWhile(B[0].1<.), sib = B[1:].dropWhile(B[0].1<.).

Claim (to verify 0-viol +5/+6/+7):
  (1) When sib == [] (single tree, S=Z): B is blockok(1) AND every witness
      x in Gterm0 tB satisfies olt x tB via the seqlex route (shift the canonical
      infix witness K, seqlex(shift K,B), seqlex_imp_olt).  Equivalently just:
      Q(tB) holds and B blockok.
  (2) When sib != []: the WHOLE-B clause reduces to:
        - Q(A) on the leading tree  P y A Z  =: translate(B[0]::desc)  (single tree)
        - Q(translate sib) on the sibling block (recurse; sib is ST_PS_suffix)
        - plus the cross terms olt(x, P y A S) for x a witness of the leading
          tree / of S.
      The decisive empirical fact: every EQUAL-lead witness with sib!=[] is
      decided in S (probe_witness_sibling).  So define the recursion on the
      SIBLING and verify:
        (2a) leadblock := B[0]::desc is blockok(1) single tree, Q via seqlex.
        (2b) for x in Gterm0(P y A Z) [leading tree witnesses]: olt(x, P y A S)?
             (need: leading-tree witness still dominated when siblings present)
        (2c) for x in Gterm0 S: olt(x, P y A S)?  (sibling witness vs whole)
We measure 2b and 2c violation counts, and confirm (1)'s blockok+Q.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def lead(t): return t[0] if t else -1
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
    """B = c::rest -> (c, desc, sib)."""
    c = B[0]; rest = B[1:]; i = 0
    while i < len(rest) and rest[i][0] > c[0]: i += 1
    return c, tuple(rest[:i]), tuple(rest[i:])

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        single_blockok_bad = 0   # (1) sib==[] but B not blockok 1
        n_single = n_multi = 0
        b2_chk = b2_bad = 0      # (2b) leading-tree witness vs whole multi-root
        c2_chk = c2_bad = 0      # (2c) sib witness vs whole
        b2ex = c2ex = None
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            c, desc, sib = split(B)
            if S == Z:
                n_single += 1
                if not blockok(1, B):
                    single_blockok_bad += 1
            else:
                n_multi += 1
                leadtree = (y, A, Z)
                for x in Gterm(0, leadtree):
                    if x == Z: continue
                    b2_chk += 1
                    if not olt(x, tB):
                        b2_bad += 1
                        if b2ex is None: b2ex = (B, x)
                # also x = A itself (the head arg) and leadtree as a whole node's arg
                for x in Gterm(0, S):
                    if x == Z: continue
                    c2_chk += 1
                    if not olt(x, tB):
                        c2_bad += 1
                        if c2ex is None: c2ex = (B, x)
        print(f'[+{rounds}] md={md} hosts={len(hosts)} single(S=Z)={n_single} multi={n_multi}')
        print(f'   (1) single-tree => blockok 1:   BAD={single_blockok_bad}')
        print(f'   (2b) leadtree witness olt whole: chk={b2_chk} BAD={b2_bad}')
        print(f'   (2c) sib witness olt whole:      chk={c2_chk} BAD={c2_bad}')
        if b2ex: print('      2bex', mfmt(((0,0),)+b2ex[0]), 'x', tfmt(b2ex[1]))
        if c2ex: print('      2cex', mfmt(((0,0),)+c2ex[0]), 'x', tfmt(c2ex[1]))

if __name__ == '__main__':
    main()
