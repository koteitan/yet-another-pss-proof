#!/usr/bin/env python3
"""FAITHFUL probe v2: find the CORRECT IH carrier for H0clause_oper_step.

core.py confirms H0clause(translate M) TRUE (0 viol).  H0clause checks, at every
head-0 SUBTERM-node P 0 b c of translate M, the clause  forall x in Gterm0 b, olt x b.

So the carrier is exactly:  b ranges over { arg of a head-0 subterm-node of
translate B }.  Call such b a "h0arg".  We must prove forall x in Gterm0 b, olt x b
for every h0arg b, by strong induction on tsize b.

Equal-lead reduction: x in Gterm0 b, lead x == lead b, x = P y ax sx, b = P y bb sb.
Want olt x b.  olt_P_P: olt ax bb  OR (ax==bb and olt sx sb).
We try to discharge via olt ax bb (when ax!=bb).  For IH we need:
   (1) bb (= arg b) is ITSELF an h0arg, i.e. y==0 (b is head-0) so that... NO:
       Gterm0 b with b = P y bb sb: bb in Gterm0 b requires 0<=y, always true.
       But to apply IH (the clause) to bb we need bb to be an h0arg of translate B.
   Question: is bb an h0arg?  bb = arg b.  b is itself an arg of a head-0 node,
   but bb is the arg of b.  b's head is y.  If y==0, then b = P 0 bb sb is a
   head-0 node, and bb is ITS arg => bb is an h0arg. GOOD.
   If y==1 (b = P 1 bb sb, head-1), b is NOT a head-0 node, so bb is the arg of a
   head-1 node => NOT directly an h0arg.  Then the clause/IH does not directly
   apply to bb.

So the real question: in the equal-lead descent, what is y(=lead b=lead x)?
  - If y==0: clean, bb is h0arg, IH applies.
  - If y==1: b=P1.., and we need olt ax bb where ax in Gterm0 bb but bb is arg of
    a head-1 node.  Is there still a usable invariant?

We classify every hard (equal-lead) case by y and test the descent target's role.
We test the GENERALIZED carrier:  Q(b) := forall x in Gterm0 b, olt x b, for b
ranging over ALL subterm-args (arg of ANY node) of translate B.  Is Q true for
all such b?  If yes, simple structural strong induction on tsize closes it
(every Gterm0 x's arg-descent lands on a smaller arg-subterm).
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

def all_arg_subterms(t):
    """every b that is the ARG (2nd field) of some subterm-node of t, plus t-args
    recursively. We collect every 'b' appearing as arg of a P-node."""
    res = []
    def rec(t):
        if t == (): return
        a, b, c = t
        res.append(b)          # b is an arg
        rec(b); rec(c)
    rec(t)
    return res

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and len(M) >= 1 and M[0] == (0, 0)]
        md = max(seen.values())

        # CARRIER Q over ALL arg-subterms b of translate B: forall x in Gterm0 b, olt x b
        qchecked = qviol = 0
        qcex = []
        # also classify hard equal-lead cases by y
        hard_y0 = hard_y1 = hard_other = 0
        for B in hosts:
            tB = translate(tuple(B[1:]))   # translate of descendant block
            # the object in the theorem is P 0 tB Z; its head-0 root arg is tB.
            # Q must hold for tB and recursively for every arg-subterm of tB
            # (and of the whole P 0 tB Z, but Z has none).
            for b in [tB] + all_arg_subterms(tB):
                if b == (): continue
                for x in Gterm(0, b):
                    qchecked += 1
                    if not olt(x, b):
                        qviol += 1
                        if len(qcex) < 8: qcex.append((B, b, x))
                    else:
                        if lead(x) == lead(b) and x != b:
                            y = lead(b)
                            if y == 0: hard_y0 += 1
                            elif y == 1: hard_y1 += 1
                            else: hard_other += 1
        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  CARRIER Q (forall arg-subterm b: forall x in Gterm0 b, olt x b):')
        print(f'    checked={qchecked}  VIOLATIONS={qviol}')
        for B, b, x in qcex[:6]:
            print('    QCEX B', mfmt(B), 'b', tfmt(b), 'x', tfmt(x))
        print(f'    hard equal-lead by y: y=0:{hard_y0} y=1:{hard_y1} other:{hard_other}')

if __name__ == '__main__':
    main()
