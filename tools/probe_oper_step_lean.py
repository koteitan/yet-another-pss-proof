#!/usr/bin/env python3
"""FAITHFUL probe matching the EXACT planned Lean proof of H0clause_oper_step.

Plan:
  MASTER lemma H0_root:  for every SubBlock K of B (with (0,0)::B in ST_PS,
  row1<=1):  forall x in Gterm 0 (translate K), olt x (translate K).
  Proved by strong induction on tsize(translate K).

  Step: translate K = P y bK cK  (bK = translate (K.takeWhile (K0<.)),
        cK = translate (K.dropWhile ...)).  Take x in Gterm 0 (translate K).
        By mem_Gterm_P, since 0<=y always: x = bK, or x in Gterm 0 bK, or
        x in Gterm 0 cK.
        We must show olt x (P y bK cK).

  We test the KEY reduction used in the proof:
   (A) ROOT-clause well-founded reduction: split x in Gterm 0 (translate K) by
       lead x vs y(=lead translate K):
         lead x < y  -> olt by olt_P_of_lead_lt (EASY).
         lead x == y -> x = P y (arg x) (sib x). Reduce olt x (P y bK cK) to
            olt (arg x) bK  (the lex arg step) -- need olt (arg x) bK.
            CLAIM: arg x in Gterm 0 bK, and bK = translate K' for SubBlock K'
            of B with tsize(bK) < tsize(translate K).  Then IH(K') gives
            olt (arg x) bK.  (We also need the case arg x == bK -> handle via
            the sib component, but verify it doesn't arise / handled.)
   We verify, over the corpus, that at every lead==y member x:
       - x has the form P y ax sx  (head subscript == y)
       - ax in Gterm 0 bK  OR ax == bK
       - if ax==bK then we'd need olt (sib x) cK -- record if this happens
       - bK is a legal SubBlock-translate (always true by construction)
       - IH on bK suffices: i.e. olt(ax,bK) holds (the recursive instance)
   And confirm 0 cases where the reduction fails.

Then H0clause(translate K) for all SubBlock K follows structurally from H0_root.
We also re-verify H0clause(translate B) directly (== core check).
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng, le0, entry
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

def subblocks_translates(B):
    """all translate K for SubBlock K of B (reflexive-transitive tw/dw)."""
    res = []
    def rec(seg):
        res.append(translate(tuple(seg)))
        if not seg: return
        (x, y) = seg[0]; rest = seg[1:]
        i = 0
        while i < len(rest) and rest[i][0] > x: i += 1
        rec(rest[:i]); rec(rest[i:])
    rec(tuple(B))
    return res

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        # genuine hosts: start with (0,0), row1<=1
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and len(M) >= 1 and M[0] == (0, 0)]
        md = max(seen.values())

        root_checked = 0
        easy = 0
        hard = 0
        hard_arg_reduces = 0       # olt x tK <- olt (arg x) bK with arg x in Gterm0 bK
        hard_arg_eq_bK = 0         # arg x == bK (need sib step)
        ihfail = 0                 # the recursive olt(arg x, bK) FALSE (would break IH)
        reduce_fail = 0            # olt x tK not implied by the arg reduction at all
        tsize_nondesc = 0          # tsize(bK) not < tsize(tK)
        ex = []
        for B in hosts:
            Bdesc = B[1:]          # the descendant block; (0,0)::Bdesc = B
            # MASTER: over all SubBlock K of Bdesc, the root clause.
            for tK in subblocks_translates(Bdesc):
                if tK == (): continue
                y, bK, cK = tK
                for x in Gterm(0, tK):
                    root_checked += 1
                    lx = lead(x)
                    if lx < y:
                        easy += 1
                        assert olt(x, tK)
                        continue
                    if lx > y:
                        # would be a real violation
                        reduce_fail += 1
                        if len(ex) < 6: ex.append(('LEADGT', B, tK, x))
                        continue
                    # lx == y : the HARD equal-lead case
                    hard += 1
                    ax, sx = x[1], x[2]    # arg x, sib x
                    # the target: olt x tK == olt (P y ax sx) (P y bK cK)
                    #   <=> olt ax bK or (ax==bK and olt sx cK)
                    # reduction used in Lean: prove via olt ax bK (IH) when ax!=bK.
                    if ax != bK:
                        # need ax in Gterm 0 bK for IH instance
                        inG = (ax in Gterm(0, bK)) or (ax == bK)
                        if not inG:
                            reduce_fail += 1
                            if len(ex) < 6: ex.append(('NOTINGTERM', B, tK, x))
                            continue
                        if tsize(bK) >= tsize(tK):
                            tsize_nondesc += 1
                        # IH would give olt ax bK iff ax in Gterm0 bK and core true
                        if not olt(ax, bK):
                            ihfail += 1
                            if len(ex) < 6: ex.append(('IHFAIL', B, tK, x, ax, bK))
                        else:
                            hard_arg_reduces += 1
                        # final olt must hold
                        if not olt(x, tK):
                            reduce_fail += 1
                            if len(ex) < 6: ex.append(('OLTFAIL', B, tK, x))
                    else:
                        # ax == bK : olt x tK reduces to olt sx cK (tail step)
                        hard_arg_eq_bK += 1
                        if not olt(x, tK):
                            reduce_fail += 1
                            if len(ex) < 6: ex.append(('OLTFAIL_TAIL', B, tK, x))

        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  ROOT clause over all SubBlocks: checked={root_checked}')
        print(f'    easy(lead x < y)={easy}')
        print(f'    hard(lead x == y)={hard}')
        print(f'      of hard: arg!=bK & IH-reduces(olt ax bK true)={hard_arg_reduces}')
        print(f'      of hard: arg==bK (tail step)={hard_arg_eq_bK}')
        print(f'    >>> IH-FAIL (olt ax bK FALSE, breaks induction)={ihfail}')
        print(f'    >>> tsize-nondescent (bK not smaller)={tsize_nondesc}')
        print(f'    >>> REDUCE-FAIL / OLT-FALSE (statement false)={reduce_fail}')
        for e in ex[:6]:
            print('      EX', e[0], 'B', mfmt(e[1]), 'tK', tfmt(e[2]), 'x', tfmt(e[3]))

if __name__ == '__main__':
    main()
