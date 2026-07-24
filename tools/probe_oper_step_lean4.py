#!/usr/bin/env python3
"""v4: find the SMALLEST closed carrier class C for the arg-descent induction.

We need C such that:
  (1) translate B in C  (the root arg of P 0 tB Z).
  (2) Q(b):= forall x in Gterm0 b, olt x b holds for all b in C  (0 viol).
  (3) C closed under the equal-lead descent: if b in C, x in Gterm0 b, lead x ==
      lead b, x=P y ax sx, b=P y bb sb, ax!=bb, then bb in C.
  (4) well-founded: tsize bb < tsize b (always, since bb is a proper subterm).

Candidate C definitions to test (each a predicate over a term b, relative to root R=tB):
  C1: b == R or b in Gterm0(R)              (G-member-or-root)
  C2: closure of {R} under b -> arg(b)      (just the leftmost-arg spine)
  C3: b in argClosure: smallest set with R, and closed under b->arg(b) AND
      b->any element of Gterm0(arg b)?  too broad probably.
  C4: b in Garg := { arg(g) : g in {R} U Gterm0(R) } U {R} ... iterate.

Actually the descent maps b -> arg(b).  And the elements x come from Gterm0(b).
The reachable b's = closure of {R} under (b -> arg(b)) AND for the IH instance we
land on bb=arg(b) but the NEXT x is ax in Gterm0(bb).  So reachable carriers =
closure of {R} under b -> arg(b)?  No: from b we may pick ANY hard x in Gterm0(b);
its ax goes to bb=arg(b), independent of x.  So the only descent target is arg(b).
Hence reachable-b closure = { R, arg R, arg(arg R), ... } the LEFT-ARG SPINE.
But wait: at b we prove Q(b) which quantifies over ALL x in Gterm0(b), and the
reduction sends each such x to (ax, arg b).  So to prove Q(b) we only need
Q-like info about arg(b): specifically olt ax (arg b) for ax in Gterm0(arg b).
That's Q(arg b) RESTRICTED.  So induction hypothesis = Q(arg b).  Thus the
carrier closed set is the left-arg spine of R = {R, argR, arg^2 R, ...}.

TEST: C = left-arg spine of R.  Check (2) Q holds on all spine elements, and that
the descent target arg(b) is on the spine (trivially yes) and ax in Gterm0(arg b).
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

def spine(R):
    s = []
    b = R
    while b != ():
        s.append(b)
        b = b[1]   # arg
    return s

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and len(M) >= 1 and M[0] == (0, 0)]
        md = max(seen.values())
        qchecked = qviol = 0; qcex = []
        ax_not = oltfail = 0; bad = []
        for B in hosts:
            tB = translate(tuple(B[1:]))
            for b in spine(tB):
                if b == (): continue
                bb = b[1]
                for x in Gterm(0, b):
                    qchecked += 1
                    if not olt(x, b):
                        qviol += 1
                        if len(qcex) < 8: qcex.append((B, b, x))
                    if x == b or lead(x) != lead(b): continue
                    ax = x[1]
                    if ax == bb: continue
                    # IH instance: need ax in Gterm0 bb and olt ax bb
                    if ax not in set(Gterm(0, bb)):
                        ax_not += 1
                        if len(bad) < 6: bad.append(('AXNOT', B, b, x, bb))
                    if not olt(ax, bb):
                        oltfail += 1
                        if len(bad) < 6: bad.append(('OLTFAIL', B, b, x, bb))
        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  SPINE carrier Q: checked={qchecked} VIOLATIONS={qviol}')
        for B, b, x in qcex[:6]:
            print('    QCEX B', mfmt(B), 'b', tfmt(b), 'x', tfmt(x))
        print(f'  descent IH: ax-NOT-in-Gterm0(argb)={ax_not}  olt(ax,argb)-FALSE={oltfail}')
        for e in bad[:6]:
            print('    BAD', e[0], 'b', tfmt(e[2]), 'x', tfmt(e[3]), 'argb', tfmt(e[4]))

if __name__ == '__main__':
    main()
