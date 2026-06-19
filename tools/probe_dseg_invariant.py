#!/usr/bin/env python3
"""Design + model-verify an fbseg-relative olt-domination invariant.

Key reframing (round 5): the witnesses x in Gterm0(translate B) are exactly the
ARGUMENT subtrees collected by translate's recursion: Gterm 0 (P a b c) =
{b} U Gterm0 b U Gterm0 c.  So a witness = translate(arg-run) at SOME recursion
node reachable from the root.  Concretely: descend translate B by arbitrary
desc(arg)/sib(tail) steps; at any node P a b c, the ARG b is a witness.

We carry the fbseg context.  The right olt statement is between the witness ARG
tree b and the WHOLE TREE translate B at the root.  But the inductive carrier
must relate a node's arg to translate B THROUGH the descent.

This probe finds the carrier by exploring relations that ARE preserved.
The promising one (from the seqlex analysis): the witness is dominated because
translate B's leading column wins.  We test the "ROOT-relative" carrier:
   D(node) := olt(arg(node), translate B)  for every node reachable from B,
where translate B is FIXED (the root).  This is what we actually need (every
witness is an arg of some node).  Inductiveness: need D(child) related to
D(node).  We measure whether D holds on ALL reachable nodes' args (0-viol?),
and separately whether each node-tree itself is <=o translate B (the chain).
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

def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out

def ole(s, t): return s == t or olt(s, t)

def subnodes(t):
    """all P-subnodes of t (including t)."""
    if t == (): return
    yield t
    a, b, c = t
    yield from subnodes(b)
    yield from subnodes(c)

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())

        # Carrier candidates (FIXED root tB):
        #  C1: for every subnode (a,b,c) of tB,  olt(b, tB)   [the arg]
        #  C2: for every subnode (a,b,c) of tB,  ole(node, tB) [the node itself]
        #  C3: for every subnode in the ARG-spine reachable by arg-steps only:
        #       olt(b, tB)
        c1 = c2 = 0; n_sub = 0
        c1ex = c2ex = None
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            for nd in subnodes(tB):
                a, b, c = nd
                n_sub += 1
                # arg b is a Gterm0 witness exactly when it's an arg of a
                # head-0 node ON THE Gterm-0 collection path.  Gterm0 collects
                # arg b at node iff 0<=a (always) along arg+sib recursion.  So
                # EVERY arg b at EVERY subnode is a Gterm0 witness of tB? check:
                pass
            # check: is Gterm0(tB) == { b : (a,b,c) subnode of tB } ?
            G0 = Gterm(0, tB)
            argset = [b for (a, b, c) in subnodes(tB)]
            # C1: every arg b of every subnode olt tB
            for (a, b, c) in subnodes(tB):
                if b != Z and not olt(b, tB):
                    c1 += 1
                    if c1ex is None: c1ex = (B, nd, b)
            # C2: every subnode <=o tB
            for nd in subnodes(tB):
                if not ole(nd, tB):
                    c2 += 1
                    if c2ex is None: c2ex = (B, nd)

        print(f'[+{rounds}] md={md} hosts={len(hosts)} subnodes={n_sub}')
        print(f'   C1 (every arg b of every subnode: olt b tB): VIOL={c1}')
        print(f'   C2 (every subnode node: ole node tB): VIOL={c2}')
        if c1ex: print('      C1ex', mfmt(((0,0),)+c1ex[0]), 'arg', tfmt(c1ex[2]))
        if c2ex: print('      C2ex', mfmt(((0,0),)+c2ex[0]), 'node', tfmt(c2ex[1]))

if __name__ == '__main__':
    main()
