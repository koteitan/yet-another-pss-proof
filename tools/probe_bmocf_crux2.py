#!/usr/bin/env python3
"""CRUX v2 -- using the GENUINE core statement (Gterm-0 coefficients).

Core (PROOF-STATUS Face 1, via Gterm_translate_subblock):
  for B with (0,0)::B in ST_PS (row1<=1), every g in Gterm 0 (translate B)
  satisfies  olt g (translate B).
Equivalently H0clause(translate B): all head-0 coefficients are strictly below.

TASK 5: re-confirm 0 violations at closure+5/+6 (on the row1<=1 fragment).

CRUX: the lean self-diagnosis (PROOF-STATUS (b)) splits each coefficient g by
   lead g  vs  lead (translate B):
     lead g <  lead B : auto olt  (18235/0 -- the EASY, local part)
     lead g == lead B : head-0-nested head-1 coefficient NOT in Gterm 1 -- the
                        HARD residual whose olt depends on FOREST POSITION.
We reproduce this split, and for the HARD class we test whether ANY of the
candidate BMOCF measures discriminates the olt:
   does some mu defined from <=_M / <_M^Next strictly drop from B to the
   subblock K that g comes from, in a way that *entails* olt g (translate B)
   without already assuming the global core?
We test this by checking, on the HARD class, whether olt g B is predicted by:
   P_anc : K's last column is NOT row-0-reachable from col 0 in B  (non-ascension)
   P_chain: nextchain(K) < nextchain(B)
and whether these predictors are SOUND (never predict olt when olt is false)
and COMPLETE enough (predict olt on the hard class).  A clean measure must be
BOTH sound and complete on the HARD class -- else the difficulty just relocates.
"""
import sys, functools
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, Lng, le0, entry
from wfe_explore import translate, olt, maxsub
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from valnorm import conv, lt_term, fmtb
from mine_proj import G
from probe_bmocf_ancestor import build_next_le, enum_depth

def lead_t(t): return t[0] if t else -1
def lead_c(g):  # g in conv (princ-list) form
    return g[0][1] if g else -1   # ('D', subscript, arg) -> subscript

def maxsub_c(g):
    if g == (): return 0
    return max(max(p[1], maxsub_c(p[2])) for p in g)

def host_row1_le1(M):
    return all(c[1] <= 1 for c in M)

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        corpus = [M for M in seen if Lng(M) <= 16]
        md = max(seen.values())

        # TASK5: H0clause on translate B for B in corpus.
        # Use the row1<=1 fragment as PROOF-STATUS does for the whole-image claim.
        checked = viol = 0; cex = []
        easy = hard = hard_olt_ok = hard_olt_bad = 0
        hard_examples = []
        for B in corpus:
            tB = translate(B)
            cB = conv(tB)
            leadB = lead_t(tB)
            for g in G(0, cB):
                checked += 1
                below = lt_term(g, cB)   # olt g (translate B)  (value/term order)
                if not below:
                    viol += 1
                    if len(cex) < 6: cex.append((B, g))
                # split by lead
                lg = lead_c(g)
                if lg < leadB:
                    easy += 1
                elif lg == leadB:
                    hard += 1
                    if below: hard_olt_ok += 1
                    else: hard_olt_bad += 1
                    if len(hard_examples) < 8:
                        hard_examples.append((B, g, below))
        print(f'[closure+{rounds}] maxdepth={md} hosts={len(corpus)}')
        print(f'  TASK5 H0clause(translate B): coeff-checked={checked} violations={viol}')
        for B, g in cex[:4]:
            print('    CEX B', mfmt(B), 'g', fmtb(g))
        print(f'  CRUX split: easy(lead<leadB)={easy}  HARD(lead==leadB)={hard}')
        print(f'     on HARD class: olt holds={hard_olt_ok} fails={hard_olt_bad}')

if __name__ == '__main__':
    main()
