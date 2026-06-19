#!/usr/bin/env python3
"""ROW-1 AXIS, step 3: does the row-1-head recursion CLOSE the arg-direction?

Established (0-viol +5/+6/+7, narrow single-tree object):
  - lead(tK) <= lead(tB) for every canonical witness tK in Gterm0(tB).
  - when lead(tK)==lead(tB): tK=P y KA KS, tB=P y A Z, and olt(KA,A) holds with
    KA in Gterm0 A (self-similar).

Now the recursion for olt(tK, tB), tK in Gterm0(tB):  tB = P y A C (general node,
C may be Z or not -- we test the GENERAL faithful node, not just root).
  olt_P_P: lead tK<y => done; lead tK==y => need olt(KA,A) [middle] (KA!=A) or
  KA==A & olt(KS,C) [third].
The DECISIVE inductive carrier (row-1 flavored), tested for HEREDITY:

  RC(t) := forall x in Gterm0 t, ( lead x <= lead t ) AND olt x t.

We strong-induct on tsize t.  Step at t = P y A C:
  x in Gterm0(P y A C) = {A}? NO -- Gterm0 includes A iff 0<=y (always).
  Actually Gterm0(P y A C) = {A} U Gterm0 A U Gterm0 C.
  For each x: need lead x <= y AND olt x t.
   - x=A: lead A <= y?  and olt A t?   <-- THIS is the R1/argTrans DEATH point;
     test if RC's lead-bound HELPS here.
   - x in Gterm0 A: IH RC(A) gives lead x<=lead A and olt x A.  Need lead x<=y
     and olt x t.
   - x in Gterm0 C: IH RC(C) gives lead x<=lead C and olt x C.  Need lead x<=y
     and olt x t.

KEY TEST: is RC HEREDITARY on faithful nodes?  (Q alone was NOT: Q(p0(p1(0)))
false.)  Does adding the lead-bound conjunct make the carrier hereditary, i.e.
is RC(node) TRUE for EVERY faithful subnode?  If RC is hereditary AND the step
closes, the arg-direction is proven by tsize induction.

We test:  (H) RC holds at EVERY faithful subnode (hereditary).
          (S-A) for x=A at node: lead A <= y?  (the head-arg lead bound)
          (S-trans) lead x <= lead A & olt x A => lead x <= y & olt x (PyAC)?
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
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        # (H) RC hereditary over ALL faithful subnodes
        rc_nodes = rc_bad = 0
        # split the RC violation into lead-bound vs olt
        leadbound_bad = olt_bad = 0
        rcex = None
        # (S-A) head-arg lead bound  lead A <= y  at every faithful subnode
        sa_chk = sa_bad = 0
        saex = None
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            # walk EVERY faithful subnode (the recursion visits these)
            stack = [tB]
            while stack:
                nd = stack.pop()
                if nd == Z: continue
                y, A, C = nd
                rc_nodes += 1
                # RC(nd): forall x in Gterm0 nd, lead x<=lead nd and olt x nd
                ok = True
                for x in Gterm(0, nd):
                    if x == Z: continue
                    lb = lead(x) <= lead(nd)
                    ot = olt(x, nd)
                    if not lb: leadbound_bad += 1
                    if not ot: olt_bad += 1
                    if not (lb and ot):
                        ok = False
                if not ok:
                    rc_bad += 1
                    if rcex is None: rcex = (mfmt(B), tfmt(nd))
                # (S-A) lead A <= y
                if A != Z:
                    sa_chk += 1
                    if not (lead(A) <= y):
                        sa_bad += 1
                        if saex is None: saex = (mfmt(B), tfmt(nd))
                stack.append(A); stack.append(C)
        print(f'[+{rounds}] md={md} faithful-subnodes={rc_nodes}')
        print(f'   (H) RC hereditary (lead-bound AND olt at every subnode): BAD-nodes={rc_bad}')
        print(f'       breakdown: lead-bound viols={leadbound_bad}  olt viols={olt_bad}')
        if rcex: print('       RCbad B', rcex[0], 'node', rcex[1])
        print(f'   (S-A) head-arg lead bound lead A<=y: chk={sa_chk} BAD={sa_bad}')
        if saex: print('       SAbad B', saex[0], 'node', saex[1])

if __name__ == '__main__':
    main()
