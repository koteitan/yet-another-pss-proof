#!/usr/bin/env python3
"""DECISIVE full-induction test for the carrier
   Q(t) := forall x in Gterm0 t, olt x t
by strong induction on tsize t, over FAITHFUL trees t = translate(sub-block of
ST_PS host).  The inductive step at t = P y A S:

  Gterm0(P y A S) = {A} U Gterm0 A U Gterm0 S.
  Need olt x (PyAS) for each:
    (alpha) x = A          : need olt A (PyAS)                  [HEAD ARG]
    (beta)  x in Gterm0 A  : IH gives olt x A; lift to olt x (PyAS)   [ARG-deep]
    (gamma) x in Gterm0 S  : IH gives olt x S; lift to olt x (PyAS)   [SIB-deep]

The naive lift olt x A => olt x (PyAS) is the R1/argTrans DEATH (false locally).
So (alpha)/(beta) are the genuinely hard ones.  BUT the empirical split showed:
  - when (alpha)/(beta) is the deciding witness, S = Z (single tree)!
So we test the REFINED inductive step that SPLITS on S:
  CASE S=Z: t = P y A Z is a SINGLE tree => the underlying block is blockok(1),
            and Q(t) holds by the seqlex_imp_olt route (NOT by recursion on A).
            VERIFY: when S=Z, Q(P y A Z) is 0-viol (it must be, root clause) AND
            the seqlex route discharges it (blockok B, witnesses K shifted).
  CASE S!=Z: the (alpha)/(beta) witnesses (from A) are dominated by the LEADING
            single-tree fact APPLIED to leadtree=P y A Z, then lifted by
            P y A Z <o P y A S (L_2b). And (gamma) by L_2c (leadS<=y guard).
So Q(P y A S) for S!=Z reduces to Q(P y A Z) [single tree, handled by seqlex] +
Q(S) [IH, tsize smaller] + L_2b + L_2c.  tsize(P y A Z) <= tsize(P y A S) with
equality impossible since S!=Z adds nodes => P y A Z is STRICTLY smaller => IH
applies to it too!

So the induction is: STRONG on tsize, cases:
  S=Z : seqlex route (leaf, no recursion).
  S!=Z: IH(P y A Z) gives leadtree witnesses dominated by leadtree; L_2b lifts to
        whole; IH(S) gives sib witnesses dominated by S; L_2c lifts to whole.
        And the head arg A: A in Gterm0(P y A Z), so IH(P y A Z) + L_2b.

VERIFY 0-viol: (i) tsize(P y A Z) < tsize(P y A S) when S!=Z [WF].
              (ii) every leadtree(P y A Z) witness lifts via L_2b (done, 0-viol).
              (iii) every S witness lifts via L_2c (done, 0-viol).
              (iv) Gterm0(PyAS) = Gterm0(PyAZ) U Gterm0 S  [set identity].
This probe checks (i) and (iv) to complete the WF + coverage argument.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def tsize(t):
    if t == (): return 0
    a, b, c = t
    return 1 + tsize(b) + tsize(c)
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
        wf_bad = 0          # (i) tsize(PyAZ) >= tsize(PyAS) when S!=Z
        cov_bad = 0         # (iv) Gterm0(PyAS) != Gterm0(PyAZ) U Gterm0 S as multiset/set
        nodes = 0
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
                nodes += 1
                pyaz = (y, A, Z)
                if S != Z:
                    if not (tsize(pyaz) < tsize(nd)): wf_bad += 1
                # coverage: Gterm0(nd) as SET
                full = set(Gterm(0, nd))
                lead_w = set(Gterm(0, pyaz))
                sib_w = set(Gterm(0, S))
                if full != (lead_w | sib_w):
                    cov_bad += 1
                stack.append(A); stack.append(S)
        print(f'[+{rounds}] md={md} hosts={len(hosts)} nodes={nodes}')
        print(f'   (i) WF tsize(PyAZ)<tsize(PyAS) when S!=Z: BAD={wf_bad}')
        print(f'   (iv) Gterm0(PyAS)=Gterm0(PyAZ) U Gterm0 S (set): BAD={cov_bad}')

if __name__ == '__main__':
    main()
