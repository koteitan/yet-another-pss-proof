#!/usr/bin/env python3
"""CRUX-DECISIVE: does a BMOCF <=_M / <_M^Next measure CLOSE the olt induction
on the HARD class?

The HARD class: head-0 node P 0 b c, x in Gterm 0 b, lead x == lead b, and we
must prove olt x b WITHOUT assuming the global core.

The advisor's claim: olt-monotonicity follows by structural induction on
<_M^Next chains.  For that to be a *tractable* proof (not just relocating the
difficulty), at the equal-lead step the relation between x and b must be
recoverable from a measure mu (from <=_M / <_M^Next) that
  (a) strictly decreases x -> b's relevant sub-structure, and
  (b) ENTAILS olt x b locally (given IH on smaller mu).

Since x in Gterm 0 b means x is reachable from b by descending arguments at
head-0 (subscript-0) principals, x is a DEEP SUBTERM of b.  The equal-lead case
means x and b share the same leading subscript.  We test the candidate measures
that the BMOCF structure offers, by checking on the HARD class whether olt x b
is *determined* (sound+complete) by:

  M1  termdepth:    x is strictly deeper in b  (trivially true; but does olt
                    follow from depth alone? -> NO if not, difficulty stays)
  M2  the SECOND component (arg) comparison: at equal lead, olt x b reduces to
      olt (arg x) (arg b)  [lean olt def].  Recurse.  Does this recursion always
      terminate in the EASY (lead) case, or does it hit another equal-lead HARD
      sub-case (=> the difficulty is genuinely recursive and NOT closed by a
      single ancestor fact)?
  M3  whether olt x b at equal lead is EVER decided at the arg level by a
      lead-comparison (easy) vs needs to go deeper (still hard).
"""
import sys
sys.path.insert(0, '.')
from fast_pss import diagSeq, Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from probe_bmocf_ancestor import enum_depth
from probe_bmocf_core import Gterm, lead

def olt_trace(x, b):
    """trace the olt(x,b) decision: return list of which component decided it,
    classifying each step as 'lead' (subscript decided) / 'argdeep' (recurse arg)
    / 'tail' (recurse tail) / 'base'."""
    steps = []
    while True:
        if x == ():
            steps.append('x=Z'); return (b != ()), steps
        if b == ():
            steps.append('b=Z'); return False, steps
        a, xb, xc = x; e, fb, fc = b
        if a != e:
            steps.append(('lead', a, e)); return a < e, steps
        # equal subscript -> recurse into ARG (the deep, hard direction)
        if xb != fb:
            steps.append('argdeep')
            x, b = xb, fb
            continue
        # args equal -> recurse tail
        steps.append('tail')
        x, b = xc, fc

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        frag = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)]
        md = max(seen.values())

        hard_total = 0
        decided_at_arglead = 0     # equal top lead, but next arg-step is a lead decision (one level)
        needs_deep_recursion = 0   # >1 equal-lead descents before a lead decides
        argdepth_hist = {}
        ex_deep = []
        for M in frag:
            t = translate(M)
            stack = [t]
            while stack:
                u = stack.pop()
                if u == (): continue
                a, b, c = u
                if a == 0:
                    lb = lead(b)
                    for x in Gterm(0, b):
                        if x == b: continue
                        if lead(x) != lb: continue   # only HARD (equal lead)
                        hard_total += 1
                        res, steps = olt_trace(x, b)
                        # count consecutive 'argdeep' before a 'lead' tuple
                        nargdeep = 0
                        for s in steps:
                            if s == 'argdeep': nargdeep += 1
                            elif isinstance(s, tuple) and s[0] == 'lead': break
                            elif s == 'tail': pass
                        argdepth_hist[nargdeep] = argdepth_hist.get(nargdeep, 0) + 1
                        if nargdeep <= 1: decided_at_arglead += 1
                        else:
                            needs_deep_recursion += 1
                            if len(ex_deep) < 5:
                                ex_deep.append((M, b, x, nargdeep, steps))
                stack.append(b); stack.append(c)
        print(f'[closure+{rounds}] maxdepth={md} frag={len(frag)}')
        print(f'  HARD (equal-lead Gterm0 coeffs) total={hard_total}')
        print(f'  olt decided within 1 arg-descent (shallow)={decided_at_arglead}')
        print(f'  olt needs >1 equal-lead arg-descents (deep recursion)={needs_deep_recursion}')
        print(f'  arg-descent-depth-until-lead-decides histogram: '
              f'{dict(sorted(argdepth_hist.items()))}')
        for M, b, x, nd, steps in ex_deep[:4]:
            print('     deep: b', tfmt(b)[:50], 'x', tfmt(x)[:50], 'depth', nd)

if __name__ == '__main__':
    main()
