#!/usr/bin/env python3
"""Find the FAITHFUL guard that makes L_2c hold (it is FALSE as a free tree fact).
L_2c: x in Gterm0 S, olt x S => olt x (P y A S), at faithful subnodes P y A S.

For each faithful subnode P y A S (S!=Z) and each x in Gterm0 S with olt x S:
  - record lead x vs y.
  - the only way L_2c can fail is lead x > y (then olt x (PyAS) false).
  So the guard we need is: lead x <= y  for all such x  (when olt x S).
  OR more precisely: olt x (PyAS) decided either by lead x < y, or lead x==y &
  then drills into (A vs x.arg) / (S vs x.tail).
Tabulate the distribution and verify lead x <= y is the operative guard (0 cases
of lead x > y on faithful data).  Also check: is  lead S <= y  (the head
dominates the sibling lead) the clean structural guard from ST_PS+row1<=1?
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
def lead(t): return t[0] if t else -1
def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        leadx_gt_y = 0          # the killer case
        leadx_eq_y = leadx_lt_y = 0
        leadS_gt_y = 0          # is lead S <= y always? (structural guard)
        n_sib_nodes = 0
        gtex = []
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            stack = [tB]
            while stack:
                nd = stack.pop()
                if nd == Z: continue
                y, A, S = nd
                if S != Z:
                    n_sib_nodes += 1
                    if lead(S) > y: leadS_gt_y += 1
                    for x in Gterm(0, S):
                        if x == Z: continue
                        if olt(x, S):
                            lx = lead(x)
                            if lx > y:
                                leadx_gt_y += 1
                                if len(gtex) < 6: gtex.append((y, tfmt(S), tfmt(x)))
                            elif lx == y: leadx_eq_y += 1
                            else: leadx_lt_y += 1
                stack.append(A); stack.append(S)
        print(f'[+{rounds}] md={md} hosts={len(hosts)} sib-nodes={n_sib_nodes}')
        print(f'   lead S > y (head fails to dominate sib lead): {leadS_gt_y}')
        print(f'   L_2c x-classes:  lead x>y(KILLER)={leadx_gt_y}  ==y={leadx_eq_y}  <y={leadx_lt_y}')
        for y, S, x in gtex: print('      KILLER y', y, 'S', S, 'x', x)

if __name__ == '__main__':
    main()
