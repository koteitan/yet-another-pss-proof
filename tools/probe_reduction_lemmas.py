#!/usr/bin/env python3
"""Verify the two REDUCTION LEMMAS that make the sibling-recursion inductive.
These must be GENERAL facts (provable), not just root-true.

L_2b: olt x (P y A Z)  &  S != Z  =>  olt x (P y A S)
      via  P y A Z <o P y A S  (olt Z S in 3rd coord) + trans.  [should be 0-viol always]

L_2c: x in Gterm0 S  &  olt x S  =>  olt x (P y A S)
      The natural sufficient cond:  S <=o P y A S  then trans.  But that's not
      always true.  So test L_2c DIRECTLY as a fact about (y,A,S,x):
      for x with olt x S, is olt x (P y A S)?
      If FALSE sometimes, find the guard (y>=lead S? from row1<=1 + ST_PS?).

We test over the ACTUAL root decomposition (faithful), AND as a general fact over
enumerated (y,A,S,x).  Report violations + the guard that fixes L_2c.
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
def ole(s, t): return s == t or olt(s, t)

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        # faithful: walk every subnode P y A S of every tB
        l2b_chk = l2b_bad = 0
        l2c_chk = l2c_bad = 0
        # for L_2c, also tabulate y vs lead S on the violations / and on all
        l2c_guard_ok = 0   # cases where olt x S & olt x (P y A S) & we check y>=?
        c_viol_leadS_vs_y = []
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
                # L_2b: x in Gterm0(P y A Z), olt x (P y A Z) => olt x nd
                pyaz = (y, A, Z)
                for x in Gterm(0, pyaz):
                    if x == Z: continue
                    if olt(x, pyaz):
                        l2b_chk += 1
                        if not olt(x, nd):
                            l2b_bad += 1
                # L_2c: x in Gterm0 S, olt x S => olt x nd
                if S != Z:
                    for x in Gterm(0, S):
                        if x == Z: continue
                        if olt(x, S):
                            l2c_chk += 1
                            if not olt(x, nd):
                                l2c_bad += 1
                                if len(c_viol_leadS_vs_y) < 8:
                                    c_viol_leadS_vs_y.append((y, lead(S), tfmt(x)))
                stack.append(A); stack.append(S)
        print(f'[+{rounds}] md={md} hosts={len(hosts)}')
        print(f'   L_2b (olt x (PyAZ) => olt x (PyAS)): chk={l2b_chk} BAD={l2b_bad}')
        print(f'   L_2c (x in Gterm0 S, olt x S => olt x (PyAS)): chk={l2c_chk} BAD={l2c_bad}')
        for y, ls, x in c_viol_leadS_vs_y:
            print(f'      L2cBAD y={y} leadS={ls} x={x}')

if __name__ == '__main__':
    main()
