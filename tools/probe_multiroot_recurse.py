#!/usr/bin/env python3
"""DECISIVE: multi-root recursion on translate B = P y A S for the root clause.

Root clause C1 (0-viol +5/+6/+7): for every subnode (a,b,c) of tB=translate B,
olt(b, tB).  Equivalently every Gterm-0 witness x: olt(x, tB).

Recursion (the schema):  tB = P y A S where
   y = B[0].2, A = translate(B.desc), S = translate(B.sib),
   B.desc = B[1:].takeWhile(B[0].1 < .), B.sib = B[1:].dropWhile(B[0].1 < .)
A Gterm-0 witness x is one of:
   (i)   x = A                          (the head's own arg)        => need olt(A, tB)
   (ii)  x in Gterm0 A                  (deeper in the arg)         => recurse on A
   (iii) x in Gterm0 S                  (in the sibling tail)       => recurse on S

For this to be a clean induction with carrier  Q(t) := forall x in Gterm0 t, olt x t,
we need at the head-0 node P y A S (y from row1<=1 so y in {0,1}):
   (i)  olt(A, P y A S)        -- the head arg dominated by the whole
   (iii under reframe) the SIBLING witnesses olt x (P y A S), GIVEN Q(S).

The known death: Q(A) and Q(S) are NOT the right IH because the witness must be
olt the WHOLE tB, not its sub-part.  So test the SHARP reduction:
   R1: olt(A, tB)                              [head arg vs whole]
   R2: x in Gterm0 A  & olt(x,A)   => olt(x,tB)   [trans through A<o tB? need A<=tB... no, need olt x tB]
   R3: x in Gterm0 S  & olt(x,S)   => olt(x,tB)
We measure how often R2/R3 would need olt(x,tB) where we only have olt(x,A)/olt(x,S),
and whether olt(x,A) -> olt(x,tB) (i.e. ole(A,tB)) and olt(x,S)->olt(x,tB) hold.
The CRUX: is  ole(A, tB)  (so trans gives olt x tB from olt x A)?  and  ole(S,tB)?
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
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
        # over EVERY subnode P y A S of every tB (i.e. recurse everywhere),
        # test the reduction facts.
        r1_chk = r1_bad = 0          # olt(A, node)  (head arg vs its own node)
        argTrans_chk = argTrans_bad = 0   # ole(A, node): trans olt x A -> olt x node
        sibTrans_chk = sibTrans_bad = 0   # ole(S, node): trans olt x S -> olt x node
        r1ex = argex = sibex = None
        nnodes = 0
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            # walk every subnode
            stack = [tB]
            while stack:
                nd = stack.pop()
                if nd == Z: continue
                y, A, S = nd
                nnodes += 1
                # R1: olt(A, nd)  (arg dominated by node)
                if A != Z:
                    r1_chk += 1
                    if not olt(A, nd):
                        r1_bad += 1
                        if r1ex is None: r1ex = (B, nd)
                    # arg-trans: ole(A, nd)
                    argTrans_chk += 1
                    if not ole(A, nd):
                        argTrans_bad += 1
                        if argex is None: argex = (B, nd)
                # sib-trans: ole(S, nd)
                if S != Z:
                    sibTrans_chk += 1
                    if not ole(S, nd):
                        sibTrans_bad += 1
                        if sibex is None: sibex = (B, nd)
                stack.append(A); stack.append(S)
        print(f'[+{rounds}] md={md} hosts={len(hosts)} nodes={nnodes}')
        print(f'   R1 olt(A,node) [head arg < node]:   chk={r1_chk} BAD={r1_bad}')
        print(f'   argTrans ole(A,node):                chk={argTrans_chk} BAD={argTrans_bad}')
        print(f'   sibTrans ole(S,node):                chk={sibTrans_chk} BAD={sibTrans_bad}')
        if r1ex: print('     R1ex', mfmt(((0,0),)+r1ex[0]), 'node', tfmt(r1ex[1]))
        if argex: print('     argex', mfmt(((0,0),)+argex[0]), 'node', tfmt(argex[1]))
        if sibex: print('     sibex', mfmt(((0,0),)+sibex[0]), 'node', tfmt(sibex[1]))

if __name__ == '__main__':
    main()
