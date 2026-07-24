#!/usr/bin/env python3
"""FAITHFUL core check using the EXACT lean definitions (Otembed/Wttone):

  Gterm u (P a b c) = (if u<=a then {b} U Gterm u b) U Gterm u c
  olt: subscript-first lex on (a,b,c)
  H0clause (P a b c) = (a=0 -> forall x in Gterm 0 b, olt x b)
                       and H0clause b and H0clause c

Core residual H0clause_oper_step (Face 1): H0clause (translate M) for all
M in ST_PS on the row1<=1 fragment.  PROOF-STATUS: model-verified 0/671.

TASK 5: re-confirm 0 violations at closure+5/+6 with these exact defs.
CRUX:  at each head-0 node P 0 b c, the clause needs olt x b for x in Gterm 0 b.
       Split x by lead x vs lead b:
         lead x <  lead b : auto olt (EASY/local)
         lead x == lead b : HARD residual.  Test if a BMOCF <=_M / ascension
         measure cleanly predicts olt on the HARD class.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, Lng, le0, entry
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth, build_next_le

def lead(t): return t[0] if t else -1

def Gterm(u, t):
    """exact lean Gterm as a list (may repeat; fine for membership/iteration)."""
    if t == (): return []
    a, b, c = t
    out = []
    if u <= a:
        out.append(b)
        out += Gterm(u, b)
    out += Gterm(u, c)
    return out

def H0clause(t):
    """exact lean H0clause; returns (ok, list of (b, x) violations)."""
    viols = []
    def rec(t):
        if t == (): return True
        a, b, c = t
        ok = True
        if a == 0:
            for x in Gterm(0, b):
                if not olt(x, b):
                    viols.append((b, x)); ok = False
        ok = rec(b) and ok
        ok = rec(c) and ok
        return ok
    res = rec(t)
    return res, viols

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18]
        md = max(seen.values())

        # row1<=1 fragment (PROOF-STATUS whole-image claim domain)
        frag = [M for M in hosts if all(c[1] <= 1 for c in M)]

        nodes = viol_nodes = 0
        cex = []
        easy = hard = hard_bad = 0
        hard_ex = []
        for M in frag:
            t = translate(M)
            ok, viols = H0clause(t)
            nodes += 1
            if not ok:
                viol_nodes += 1
                if len(cex) < 6: cex.append((M, viols[:2]))
        # CRUX split: enumerate every head-0 node and its Gterm-0 coeffs
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
                        lx = lead(x)
                        if lx < lb: easy += 1
                        elif lx == lb:
                            hard += 1
                            if not olt(x, b):
                                hard_bad += 1
                                if len(hard_ex) < 6: hard_ex.append((M, b, x))
                        # lx>lb would violate; counted via hard_bad effectively
                        else:
                            # lead x > lead b => olt x b is FALSE => violation
                            hard += 1; hard_bad += 1
                            if len(hard_ex) < 6: hard_ex.append((M, b, x))
                stack.append(b); stack.append(c)

        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)} '
              f'row1<=1 frag={len(frag)}')
        print(f'  TASK5 H0clause(translate M): nodes={nodes} VIOLATING-hosts={viol_nodes}')
        for M, vs in cex[:4]:
            print('    CEX', mfmt(M), '->', tfmt(translate(M)))
            for b, x in vs: print('        b', tfmt(b), 'x', tfmt(x))
        print(f'  CRUX head-0 coeff split: easy(leadx<leadb)={easy} '
              f'HARD(leadx>=leadb)={hard} of-which-olt-FALSE={hard_bad}')
        for M, b, x in hard_ex[:4]:
            print('     HARDbad', mfmt(M), 'b', tfmt(b), 'x', tfmt(x))

if __name__ == '__main__':
    main()
