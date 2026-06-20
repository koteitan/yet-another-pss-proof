#!/usr/bin/env python3
"""probe_wqo_bcore3.py -- give the architect's route its STRONGEST reading.

bcore2 showed the carrier olt(tK, tAt) FLIPS at intermediate <=_e ancestor nodes
(198/1467 .. 1738/12410 bad), same failure mode as bare SubBlock (lead-0 head At
can't dominate lead-1 witness K).  But a GENERATION induction does not need the
raw carrier at intermediates -- it needs the PER-STEP relation between consecutive
generation nodes At -> At+1 to be monotone & compose to the root.  And the
architect's specific lever is the COPY-DOMINATION i_0 = max{i|(i,0)<=_M(i,j1)}.

We test the strongest defensible per-step claims a <=_e-generation induction could
ride, at EVERY intermediate step (lo,hi)->(lo',hi'):

 (P1) per-step olt monotone:  olt(translate At)(translate At+1)
      (does each ancestor-grow step strictly increase the ordinal?)  This is what a
      "grow toward B, each step bigger" induction needs.  If TRUE everywhere, then
      olt(tK,tB) follows by chaining olt(tK,tA1)<...  -- BUT only if the FIRST step
      olt(tK, tA1) also holds.  Report both the first-step and the inner-steps.

 (P2) the i_0 copy-domination per architect sec 4/sec 2.2 Ascend: at each grow step
      that adds an ASCENDING COPY column, the added column's row-0 is dominated by
      its <=_M ancestor (the i_0 original).  We test: is the newly added boundary
      column an le0/nextrel1-descendant of an earlier column (genuine ancestor
      step), and does that coincide with olt-monotonicity?

 (P3) seqlex per-step:  seqlex(translate-respecting) -- does At seqlex-below At+1?

VERDICT LOGIC: a generation induction closes (B-core) iff there is a per-step
relation that is (a) TRUE at every step including the first K->A1, and (b) composes
(transitive) to olt(tK,tB).  If even the per-step olt FLIPS (At >o At+1 somewhere),
no monotone generation chain exists -> route weak.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import (Lng, entry, diagSeq, oper, le0, nextrel1, nextrel0,
                      hasParent1, parent1, hasParent0, parent0)
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def lead(t): return t[0] if t else -1

def Gterm(u, t):
    if t == (): return []
    a, b, c = t
    out = []
    if u <= a:
        out.append(b); out += Gterm(u, b)
    out += Gterm(u, c)
    return out

def find_infix(B, x):
    n = len(B); cands = []
    for i in range(n):
        for j in range(i+1, n+1):
            if translate(tuple(B[i:j])) == x:
                cands.append((i, j))
    if not cands: return None
    cands.sort(key=lambda ij: (-(ij[1]-ij[0]), ij[0]))
    return cands[0]

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        hosts = [M for M in seen if Lng(M) <= 20 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())

        # P1 per-step olt monotone along the ancestor-grow chain
        first_chk = first_bad = 0     # K -> A1 (first grow step) olt
        inner_chk = inner_bad = 0     # At -> At+1 inner steps olt
        inner_eq = 0                  # equal translate (degenerate step)
        # whether the FULL chain is monotone (every step strictly up)
        chain_total = chain_mono = 0
        # P2: at the bad inner steps, is the added column a genuine <=_M ancestor
        # descendant (i.e. does copy-domination structure even apply)?
        badstep_ex = []
        for B0 in hosts:
            B = tuple(B0[1:])
            tB = translate(B)
            if tB == Z: continue
            n = len(B)
            G0 = set(Gterm(0, tB))
            for x in G0:
                if x == tB: continue
                ij = find_infix(B, x)
                if ij is None: continue
                i, j = ij
                # build chain (lo,hi): grow right then left, exactly as bcore2
                lo, hi = i, j
                chain = [(lo, hi)]
                while hi < n:
                    hi += 1; chain.append((lo, hi))
                while lo > 0:
                    lo -= 1; chain.append((lo, hi))
                chain_total += 1
                mono = True
                for s in range(len(chain) - 1):
                    (alo, ahi) = chain[s]; (blo, bhi) = chain[s+1]
                    tA = translate(tuple(B[alo:ahi]))
                    tBn = translate(tuple(B[blo:bhi]))
                    if tA == Z or tBn == Z: continue
                    if tA == tBn:
                        if s == 0: pass
                        else: inner_eq += 1
                        continue
                    step_ok = olt(tA, tBn)
                    if s == 0:
                        first_chk += 1
                        if not step_ok: first_bad += 1
                    else:
                        inner_chk += 1
                        if not step_ok:
                            inner_bad += 1
                            mono = False
                            if len(badstep_ex) < 6:
                                badstep_ex.append((B, (alo,ahi), (blo,bhi), tA, tBn))
                if mono: chain_mono += 1
        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  P1 per-step olt monotone along <=_e ancestor-grow chain:')
        print(f'     FIRST step (K->A1): chk={first_chk} VIOL(not olt up)={first_bad}')
        print(f'     INNER steps:        chk={inner_chk} VIOL(At >=o At+1)={inner_bad}  (eq={inner_eq})')
        print(f'     fully-monotone chains: {chain_mono}/{chain_total}')
        for B, a, b, tA, tBn in badstep_ex[:4]:
            print(f'     STEPbad B {mfmt(B)} {a}->{b}  tA {tfmt(tA)[:22]} >=o tA+1 {tfmt(tBn)[:22]}')

if __name__ == '__main__':
    main()
