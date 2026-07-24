#!/usr/bin/env python3
"""seqlex route v2: align the SubBlock witness to B's depth.

x in Gterm0(translate B).  Gterm_translate_subblock gives K with SubBlock B K,
translate K = x.  The SubBlock path is a sequence of takeWhile(desc)/dropWhile(sib)
steps.  Observation: olt(translate K, translate B) is TRUE (core).  The depth
mismatch arises because a 'desc' step strips the head pair and goes one level
deeper.  The CORRECT comparison for seqlex_imp_olt at depth d=dB:
  build K' = the suffix of B starting where K begins, but realigned to depth dB?

Better idea: track the SubBlock path and at each step apply the seqlex_imp_olt
recursion DIRECTLY (arg step / tail step), which is what the lean proof would do.
i.e. prove olt(x, translate B) by following the Gterm0 membership recursion:
  mem_Gterm_P: x in Gterm0(P y bb sb) (0<=y) <=>
      x==bb  or x in Gterm0 bb  or  x in Gterm0 sb.
  - x==bb:  need olt bb (P y bb sb). olt_P_P: y==y, bb==bb, third olt sb? NO.
            Actually olt(bb, P y bb sb) needs lead bb<y OR (lead-eq stuff).
            => need a LEAD fact: lead bb < y? or olt(bb,..) some other way. TEST.
  - x in Gterm0 sb: recurse on sb with SAME b? need olt x (P y bb sb) from
            x in Gterm0 sb.  TEST what's needed.
  - x in Gterm0 bb: recurse: olt x bb (IH on bb) then olt bb (P y bb sb)? need
            transitivity olt x bb and bb <o b? but bb<o b may be false.

So the membership recursion needs, for each branch, a LOCAL olt fact. Let's
measure, over genuine H0ARG b and x in Gterm0 b, which branch x is in and what
local fact each branch needs, and whether that fact (stated locally) is TRUE.

  Branch ARG (x in Gterm0 bb): need  olt x b.  Decompose: is it that x==bb-case
     reduces, or recursion.  We test: for x in Gterm0 bb with x in Gterm0 b,
     is olt x b ALWAYS true AND does it follow from olt x bb plus 'olt-or-eq bb..'?
  Simplest sufficient local lemma per branch:
     L_eq:  olt bb b           (the x==bb branch)  [b=P y bb sb]
     L_arg: x in Gterm0 bb -> olt x b
     L_sib: x in Gterm0 sb -> olt x b
  We check truth of L_eq, and whether L_arg/L_sib reduce to smaller H0ARG
  instances + L_eq.
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
def h0arg_nodes(t):
    """yield (b, sb, y) for each head-0 node P 0 b sb (the H0ARG b and its tail)."""
    for s in subterms(t):
        if s[0] == 0:
            yield (s[1], s[2])

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and len(M) >= 1 and M[0] == (0, 0)]
        md = max(seen.values())
        # at each H0ARG b=P y bb sb, the clause forall x in Gterm0 b olt x b.
        # classify x by branch and test local sufficient facts.
        Leq_chk = Leq_viol = 0
        b_y0 = b_y1 = 0
        arg_branch = sib_branch = eq_branch = 0
        # KEY test: is bb (arg of H0ARG b) itself an H0ARG -> recursion stays in class?
        # Already known NO for y=1.  Instead test the SIB-suffix structure:
        # claim: b = P y bb sb is H0ARG; the clause for b reduces to clause for bb
        # (if y==0, bb is H0ARG) plus 'olt bb b' plus the sb clause.
        # For y==1: b=P1 bb sb. b is H0ARG. Is the WHOLE b = translate of a single
        # tree (sb==Z)? test sb.
        y1_sb_Z = y1_sb_nonZ = 0
        eqcex = []
        for B0 in hosts:
            tB = translate(tuple(B0[1:]))
            whole = (0, tB, ())
            for (b, _tail_unused) in [(tB, ())]:  # placeholder
                pass
            for (b, sb_of_node) in h0arg_nodes(whole):
                if b == (): continue
                y = lead(b); bb = b[1]; sb = b[2]
                if y == 0: b_y0 += 1
                elif y == 1:
                    b_y1 += 1
                    if sb == (): y1_sb_Z += 1
                    else: y1_sb_nonZ += 1
                # L_eq: olt bb b
                Leq_chk += 1
                if not olt(bb, b):
                    Leq_viol += 1
                    if len(eqcex) < 6: eqcex.append((B0, b))
                for x in Gterm(0, b):
                    if x == bb: eq_branch += 1
                    elif x in set(Gterm(0, bb)): arg_branch += 1
                    elif x in set(Gterm(0, sb)): sib_branch += 1
        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  H0ARG nodes: y=0:{b_y0} y=1:{b_y1} (y1 sb=Z:{y1_sb_Z} sb!=Z:{y1_sb_nonZ})')
        print(f'  L_eq (olt bb b for b=P y bb sb): checked={Leq_chk} VIOL={Leq_viol}')
        for B0, b in eqcex[:5]: print('    LEQCEX b', tfmt(b))
        print(f'  branch counts: x==bb:{eq_branch} x in Gterm0 bb:{arg_branch} x in Gterm0 sb:{sib_branch}')

if __name__ == '__main__':
    main()
