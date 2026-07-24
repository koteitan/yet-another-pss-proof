#!/usr/bin/env python3
"""FAITHFUL probe v3: the CORRECT carrier = arg of a head-0 node.

H0clause(P 0 b c) requires (clause):  forall x in Gterm0 b, olt x b.
So define  H0ARG := { b : P 0 b c is a subterm-node of (P 0 tB Z) for some c }.
Carrier Q(b): forall x in Gterm0 b, olt x b,  for b in H0ARG.

Proof plan: strong induction on tsize b.  x in Gterm0 b:
  - lead x < lead b  : olt by olt_P_of_lead_lt.  (handles x=Z too, and the
    'lead x>lead b' can't happen because then x not olt -> but is it in H0ARG?)
  - lead x == lead b (=y): x=P y ax sx, b=P y bb sb. Reduce olt x b -> olt ax bb
    (when ax!=bb).  IH needs: bb in H0ARG and ax in Gterm0 bb.
      * ax in Gterm0 bb: TEST.
      * bb in H0ARG: bb = arg b. b in H0ARG so b = arg of a head-0 node. Is bb
        (=arg of b) in H0ARG?  Only if b is ITSELF head-0 (y==0): then b=P0 bb sb
        is a head-0 node and bb=its arg => bb in H0ARG.  If y==1, b=P1.. -> bb is
        arg of a head-1 node, NOT necessarily in H0ARG.  TEST what happens at y==1.

We restrict to b in H0ARG and verify:
  (Q) Q(b) holds for all b in H0ARG  (== core.py, should be 0 viol).
  At each hard equal-lead member, classify y and whether the IH target bb is in
  H0ARG and ax in Gterm0 bb, and whether olt ax bb holds.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

def lead(t): return t[0] if t else -1
def Gterm(u, t):
    if t == (): return []
    a, b, c = t
    out = []
    if u <= a:
        out.append(b); out += Gterm(u, b)
    out += Gterm(u, c)
    return out
def tsize(t):
    if t == (): return 1
    return tsize(t[1]) + tsize(t[2]) + 1

def h0args(t):
    """all b such that P 0 b c is a subterm-node of t."""
    res = []
    def rec(t):
        if t == (): return
        a, b, c = t
        if a == 0: res.append(b)
        rec(b); rec(c)
    rec(t)
    return res

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and len(M) >= 1 and M[0] == (0, 0)]
        md = max(seen.values())

        qchecked = qviol = 0; qcex = []
        hard = 0
        # IH-instance health on hard cases:
        bb_in_h0arg = bb_not = 0
        ax_in_Gbb = ax_not = 0
        oltaxbb_true = oltaxbb_false = 0
        ax_eq_bb = 0
        ydist = {}
        for B in hosts:
            tB = translate(tuple(B[1:]))
            whole = (0, tB, ())   # P 0 tB Z
            H = h0args(whole)
            Hset = set(H)
            for b in H:
                if b == (): continue
                for x in Gterm(0, b):
                    qchecked += 1
                    if not olt(x, b):
                        qviol += 1
                        if len(qcex) < 8: qcex.append((B, b, x))
                    if x == b: continue
                    if lead(x) == lead(b):
                        hard += 1
                        y = lead(b); ydist[y] = ydist.get(y, 0) + 1
                        ax, sx = x[1], x[2]; bb, sb = b[1], b[2]
                        if ax == bb:
                            ax_eq_bb += 1
                            continue
                        if bb in Hset: bb_in_h0arg += 1
                        else: bb_not += 1
                        if ax in set(Gterm(0, bb)): ax_in_Gbb += 1
                        else: ax_not += 1
                        if olt(ax, bb): oltaxbb_true += 1
                        else: oltaxbb_false += 1
        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  CARRIER Q over H0ARG: checked={qchecked} VIOLATIONS={qviol}')
        for B, b, x in qcex[:6]:
            print('    QCEX B', mfmt(B), 'b', tfmt(b), 'x', tfmt(x))
        print(f'  hard equal-lead total={hard} ydist={ydist}')
        print(f'    of hard (ax!=bb): bb in H0ARG={bb_in_h0arg} NOT={bb_not}')
        print(f'                      ax in Gterm0 bb={ax_in_Gbb} NOT={ax_not}')
        print(f'                      olt ax bb true={oltaxbb_true} FALSE={oltaxbb_false}')
        print(f'    ax==bb (tail step)={ax_eq_bb}')

if __name__ == '__main__':
    main()
