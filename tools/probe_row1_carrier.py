#!/usr/bin/env python3
"""ROW-1 AXIS, step 5: find the PROVABLE tree-level carrier R(x,t) preserved by
the subscript-drill, with strict subscript drop guaranteed.

Drill: (x,t) both P-nodes, equal lead (subscript) => recurse (x.arg,t.arg) if
args differ else (x.tail,t.tail).  Terminates at lead x < lead t (strict
subscript drop, olt) -- confirmed ALWAYS reached (0 eq, 0 fail).

P2 (lead x <= lead t) is 0-viol at every drilled pair.  Membership P1 fails.
Find the right carrier.  Candidates for R(x,t) at drilled pairs:

 R-a: t = P (lead t) A C  with x 'embeddable' -- test the SUBSCRIPT-SEQUENCE
      relation: spine-subscripts of x are <= spine-subscripts of t pointwise?
      (spine = follow .arg).  i.e. lead x<=lead t AND lead(x.arg)<=lead(t.arg) ...
      down the SHARED arg-spine.  This is a 'row-1 spine dominance'.
 R-b: x is olt-or-eq to t restricted to the matched prefix -- circular, skip.
 R-c: the KEY structural fact -- at a drilled equal-lead pair (x,t), x = P s xa xc,
      t = P s ta tc (same subscript s).  We recurse on (xa,ta).  The invariant
      that makes lead xa <= lead ta: is it that xa,ta come from translate of
      blocks where xa's block is a sub-run of ta's block at one-deeper level?
      Test: lead(xa) <= lead(ta) given lead(x)=lead(t)  (one-step preservation of
      the row-1 head bound under arg-drill) -- THIS is the inductive step we need.
 R-d: same for tail-drill: lead(xc) <= lead(tc) given lead(x)=lead(t) & xa==ta.

Test R-c, R-d one-step preservation at every drilled equal-lead pair (0-viol =>
the carrier 'lead x <= lead t' is INDUCTIVE under the drill, base = strict drop).
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth
from probe_row1_align import blockok

Z = ()
def lead(t): return t[0] if t else -1
def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out

def drill_pairs(x, t, acc):
    """collect equal-lead drilled pairs (x,t) and their one-step children."""
    if x == Z or t == Z: return
    a, b, c = x; e, f, g = t
    if a != e: return
    # equal lead: this is a drilled equal-lead pair
    if b != f:
        acc.append(('arg', x, t, b, f))   # recurse arg
        drill_pairs(b, f, acc)
    else:
        acc.append(('tail', x, t, c, g))
        drill_pairs(c, g, acc)

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        rc_chk = rc_bad = 0       # arg-drill: lead xa <= lead ta given lead x=lead t
        rd_chk = rd_bad = 0       # tail-drill: lead xc <= lead tc
        rcex = rdex = None
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            if S != Z: continue
            if not blockok(1, B): continue
            for tK in set(Gterm(0, tB)):
                if tK == Z or tK == tB: continue
                acc = []
                drill_pairs(tK, tB, acc)
                for kind, x, t, xc, tc in acc:
                    if kind == 'arg':
                        rc_chk += 1
                        if lead(xc) > lead(tc):
                            rc_bad += 1
                            if rcex is None: rcex = (mfmt(B), tfmt(x), tfmt(t))
                    else:
                        rd_chk += 1
                        if lead(xc) > lead(tc):
                            rd_bad += 1
                            if rdex is None: rdex = (mfmt(B), tfmt(x), tfmt(t))
        print(f'[+{rounds}] md={md}')
        print(f'   R-c arg-drill lead(xa)<=lead(ta) | lead x=lead t: chk={rc_chk} BAD={rc_bad}')
        if rcex: print('      Rc-bad B', rcex[0], 'x', rcex[1], 't', rcex[2])
        print(f'   R-d tail-drill lead(xc)<=lead(tc): chk={rd_chk} BAD={rd_bad}')
        if rdex: print('      Rd-bad B', rdex[0], 'x', rdex[1], 't', rdex[2])

if __name__ == '__main__':
    main()
