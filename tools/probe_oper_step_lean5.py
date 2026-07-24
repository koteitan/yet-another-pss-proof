#!/usr/bin/env python3
"""v5: test the LEAD-GUARDED clause as a clean structural invariant.

Conjecture P(b):  forall x in Gterm0 b,  lead x <= lead b  ->  olt x b.
This is lead-guarded.  Over ALL subterms b of translate B (no H0ARG restriction).
If P(b) holds for all subterms with 0 violations, AND it reduces cleanly by
structural recursion, it gives the H0clause root clause directly: at a head-0
node P 0 bb cc, every x in Gterm0 bb has lead x <= lead bb?  NO -- need lead
x <= lead bb for the guard.  H0clause needs ALL x in Gterm0 bb olt bb, incl those
with lead x > lead bb (which would be FALSE).  So core.py's 0-viol implies: at a
head-0 node, NO x in Gterm0 bb has lead x > lead bb.  i.e. for head-0-node args,
lead is an upper bound on Gterm0.  Combined with P, that closes it.

So test TWO facts:
  F1 (lead-bound at H0ARG): for b=arg of head-0 node, forall x in Gterm0 b,
     lead x <= lead b.   (this is the 'easy makes it total' fact)
  F2 (lead-guarded olt, GLOBAL): for ALL subterms b, forall x in Gterm0 b,
     lead x <= lead b -> olt x b.
If both hold (0 viol) then H0clause root clause = F1 + F2.

And test the reduction of F2 by structural induction:
  x in Gterm0 b, lead x <= lead b. b=P y bb sb (b!=Z since Gterm0 nonempty).
  mem_Gterm_P (0<=y): x=bb OR x in Gterm0 bb OR x in Gterm0 sb.
   - x=bb: lead bb <= lead b = y... but bb=arg, lead bb vs y unrelated. Need olt bb (P y bb sb): olt_P_P -> y<y? no; need... bb olt P y bb sb iff lead bb<y or (=y and ...). Hmm x=bb=arg case: is lead bb<=lead b given? guard says lead x<=lead b i.e. lead bb<=y. If lead bb<y: olt by lead. If lead bb==y: olt(bb,P y bb sb)= olt_P_P with first comp y==y, second bb vs bb equal, third: olt sb' ... = (y==y, bb==bb, olt (tail bb) sb)? messy. TEST whether x=bb hard case occurs.
   - x in Gterm0 sb: recurse on sb (sibling). need lead x<=lead sb? not given. TEST.
   - x in Gterm0 bb: this is the arg recursion. lead x<=lead bb? not given by guard
     (guard is lead x<=lead b=y). TEST relation lead bb vs y.
We just measure violations of F1,F2 and the structure of how the guard propagates.
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
def subterms(t):
    if t == (): return
    yield t
    yield from subterms(t[1]); yield from subterms(t[2])
def h0args(t):
    res = []
    for s in subterms(t):
        if s[0] == 0: res.append(s[1])
    return res

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and len(M) >= 1 and M[0] == (0, 0)]
        md = max(seen.values())
        f1_chk = f1_viol = 0; f1cex = []
        f2_chk = f2_viol = 0; f2cex = []
        for B in hosts:
            tB = translate(tuple(B[1:]))
            whole = (0, tB, ())
            # F1: lead bound at H0ARG
            for b in h0args(whole):
                if b == (): continue
                for x in Gterm(0, b):
                    f1_chk += 1
                    if lead(x) > lead(b):
                        f1_viol += 1
                        if len(f1cex) < 6: f1cex.append((B, b, x))
            # F2: lead-guarded olt GLOBAL over all subterms
            for b in subterms(whole):
                if b == (): continue
                for x in Gterm(0, b):
                    if lead(x) <= lead(b):
                        f2_chk += 1
                        if not olt(x, b):
                            f2_viol += 1
                            if len(f2cex) < 6: f2cex.append((B, b, x))
        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  F1 (lead<=lead at H0ARG): checked={f1_chk} VIOL={f1_viol}')
        for B, b, x in f1cex[:4]: print('    F1CEX b', tfmt(b), 'x', tfmt(x))
        print(f'  F2 (lead-guarded olt GLOBAL): checked={f2_chk} VIOL={f2_viol}')
        for B, b, x in f2cex[:4]: print('    F2CEX b', tfmt(b), 'x', tfmt(x))

if __name__ == '__main__':
    main()
