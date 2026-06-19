#!/usr/bin/env python3
"""Final fbseg-discharge check: what makes a head-1 witness x (lead x = lead tB)
olt tB?  The R1 death shows olt(arg, node) FALSE locally; the ROOT clause holds
only because of GLOBAL sibling structure.  Pin down WHICH global fact.

For each EQUAL-LEAD witness x (lead x == lead tB) of tB:
  - olt(x, tB) is TRUE (root clause).  Since leads tie, olt drills into args:
    olt(x, tB)=olt((y,xa,xc),(y,A,S)) -> if xa!=A: olt(xa,A); else olt(xc,S).
  - So the decisive comparison is one level down: either olt(xa, A) or olt(xc,S).
We classify each equal-lead witness by which branch decides it, and whether that
branch's fact is an fbseg-LOCAL fact (about the segment) or needs the sibling
chain S.  If ALL equal-lead witnesses are decided by the FIRST-COLUMN drill that
matches the seqlex(shift K,B) divergence, then the content is seqlex-positional
(needs multi-root bridge); if some need the sibling S to be nonempty (copy
structure), that's the oper-tiling content.
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

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        eq_tot = 0
        dec_arg = dec_sib = 0          # decided by olt(xa,A) vs olt(xc,S)
        sib_empty_when_argdom = 0      # when arg branch and S==Z
        argbranch_S_nonempty = 0
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            for x in Gterm(0, tB):
                if x == Z: continue
                if lead(x) != lead(tB): continue   # only equal-lead (HARD)
                eq_tot += 1
                xa = x[1]; xc = x[2]
                if xa != A:
                    dec_arg += 1
                    if S == Z: sib_empty_when_argdom += 1
                    else: argbranch_S_nonempty += 1
                else:
                    dec_sib += 1
        print(f'[+{rounds}] md={md} hosts={len(hosts)} EQUAL-lead-witnesses={eq_tot}')
        print(f'   decided by arg drill olt(xa,A): {dec_arg}   (of which S==Z: {sib_empty_when_argdom}, S!=Z: {argbranch_S_nonempty})')
        print(f'   decided by sib drill olt(xc,S): {dec_sib}')

if __name__ == '__main__':
    main()
