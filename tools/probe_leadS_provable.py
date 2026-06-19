#!/usr/bin/env python3
"""DECISIVE: is the structural guard  lead S <= y  (lead(translate sib) <=
head.2) PROVABLE from ST_PS+row1<=1, or is it ANOTHER global-wall instance?

At a faithful subnode P y A S of translate B:  this node = translate of some
sub-block  c :: rest  with y=c.2, A=translate(rest.takeWhile(c.1<.)),
S=translate(rest.dropWhile(c.1<.)).  lead S = (head of sib).2 where sib's head
is the first column re-opening at <= c.1.

We want: that re-opening column's row1  <=  c.2  (= y).
i.e. for adjacent forest siblings (same row0 level after the dropWhile), the
LATER one's row1 <= the EARLIER head's row1.  Is this an ST_PS 'steps1' / row1
monotonicity fact?  Test it as a property of the ORIGINAL pair-sequence:
  for the sub-block c::rest, sib = rest.dropWhile(c.1<.); if sib nonempty,
  sib[0].2 <= c.2 ?
Tabulate over ALL sub-blocks of ALL hosts (faithful).  If 0-viol, this is a
clean column-LOCAL fact (provable from ST_PS steps1 + row1 discipline).  If it
has violations, the guard is itself global.

ALSO: test the deeper need -- when lead x == y (143 cases), what closes
olt x (PyAS)?  We verify olt x S already drills correctly: since lead x == y ==
lead S, olt x S compares (x.arg vs S.arg) then (x.tail vs S.tail); and olt x
(P y A S) compares (x.arg vs A) then (x.tail vs S).  These differ in the ARG
slot (S.arg vs A)!  So we need: when lead x = y and x.arg vs A ... test that the
==y cases are closed by  olt x S  alone (they were, empirically) and identify
the lemma.
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
def split(B):
    c = B[0]; rest = B[1:]; i = 0
    while i < len(rest) and rest[i][0] > c[0]: i += 1
    return c, tuple(rest[:i]), tuple(rest[i:])
def all_subblocks(B):
    res = []
    def rec(seg):
        seg = tuple(seg); res.append(seg)
        if not seg: return
        c, desc, sib = split(seg)
        rec(desc); rec(sib)
    rec(tuple(B)); return res

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        # COLUMN-LOCAL test of  sib[0].2 <= c.2  over all subblocks
        loc_chk = loc_bad = 0
        locex = []
        # also: is it just  sib[0].2 <= 1  (trivial from row1<=1) when c.2=1, but
        # when c.2=0 need sib[0].2 = 0.  Tabulate c.2 vs sib[0].2.
        from collections import Counter
        tab = Counter()
        # the ==y deep closure: when lead x==y, does olt x S suffice for olt x (PyAS)?
        eqy_chk = eqy_bad = 0
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            for seg in all_subblocks(B):
                if not seg: continue
                c, desc, sib = split(seg)
                if sib:
                    loc_chk += 1
                    tab[(c[1], sib[0][1])] += 1
                    if not (sib[0][1] <= c[1]):
                        loc_bad += 1
                        if len(locex) < 6: locex.append((mfmt(seg), c, sib[0]))
            # deep ==y closure on faithful nodes
            tB = translate(B)
            stack = [tB]
            while stack:
                nd = stack.pop()
                if nd == Z: continue
                y, A, S = nd
                if S != Z:
                    for x in Gterm(0, S):
                        if x == Z or lead(x) != y: continue
                        if olt(x, S):
                            eqy_chk += 1
                            if not olt(x, nd):
                                eqy_bad += 1
                stack.append(A); stack.append(S)
        print(f'[+{rounds}] md={md} hosts={len(hosts)}')
        print(f'   COLUMN-LOCAL  sib[0].2 <= c.2 (over subblocks): chk={loc_chk} BAD={loc_bad}')
        print(f'      (c.2, sib0.2) tab: {dict(tab)}')
        for s, c, s0 in locex: print('      LOCbad seg', s, 'c', c, 'sib0', s0)
        print(f'   deep ==y closure (olt x S => olt x (PyAS)): chk={eqy_chk} BAD={eqy_bad}')

if __name__ == '__main__':
    main()
