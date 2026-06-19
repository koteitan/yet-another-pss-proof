#!/usr/bin/env python3
"""LAST fbseg-carrier attempt: the Q-carrier is false on subnodes (p0(p1(0))).
The fbseg context provides the enclosing head pp that dominates.  Test the
fbseg-RELATIVE carrier:

For an fbseg-reachable segment S enclosed by head column pp (with pp.1 < all of
mid++S, u = pp.2), define the enclosing 'dominated tree'
   E(pp, S) := translate( pp :: S )      [the head pp with S as its dominated run]
(For the root, pp = (0,0), S = B, E = translate((0,0)::B) = P 0 (translate B) Z.)

Carrier  D(pp, S) := forall x in Gterm0(translate S), olt x E(pp,S).
(i.e. every witness of the segment is dominated by the HEAD-ROOTED enclosing
tree, not by translate S itself.)

Is D HEREDITARY along the fbseg descents (K_desc: into desc with new head c;
T_desc: into sib with same head pp)?  And does it discharge the root
(E((0,0),B) = P 0 (translate B) Z, and Gterm0(P 0 (translate B) Z) includes the
root-clause witnesses)?  Test 0-viol of D over ALL fbseg-reachable (pp,S).
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def split(B):
    c = B[0]; rest = B[1:]; i = 0
    while i < len(rest) and rest[i][0] > c[0]: i += 1
    return c, tuple(rest[:i]), tuple(rest[i:])

def reachable(B):
    """yield (pp, S): fbseg-reachable, pp the enclosing head column, S the segment.
    root: pp=(0,0), S=B.  K_desc: S=c::rest -> (c, desc).  T_desc: (pp, sib)."""
    out = []
    seen = set()
    stack = [((0, 0), tuple(B))]
    while stack:
        pp, S = stack.pop()
        key = (pp, S)
        if key in seen: continue
        seen.add(key)
        if not S: continue
        out.append((pp, S))
        c, desc, sib = split(S)
        if desc: stack.append((c, desc))
        if sib: stack.append((pp, sib))
    return out

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        d_chk = d_bad = 0
        ex = None
        # also check the root-discharge: at pp=(0,0), S=B, E = P 0 (translate B) Z,
        # and D requires forall x in Gterm0(translate B), olt x (P 0 (translate B) Z).
        # That is EXACTLY H0clause_oper_step's root clause lifted (since olt x (P 0 tB Z)
        # for x in Gterm0 tB <=> olt x tB by lead: P 0 tB Z has lead 0; if lead x>0 then
        # olt x (P0 tB Z) false!).  So check this too.
        root_chk = root_bad = 0
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            for (pp, S) in reachable(B):
                tS = translate(S)
                if tS == Z: continue
                E = translate((pp,) + S)       # translate(pp :: S)
                for x in Gterm(0, tS):
                    if x == Z: continue
                    d_chk += 1
                    if not olt(x, E):
                        d_bad += 1
                        if ex is None: ex = (mfmt((pp,)+S), tfmt(x), tfmt(E))
            # root discharge
            tB = translate(B)
            Eroot = (0, tB, Z)
            for x in Gterm(0, tB):
                if x == Z: continue
                root_chk += 1
                if not olt(x, Eroot): root_bad += 1
        print(f'[+{rounds}] md={md} hosts={len(hosts)}')
        print(f'   D(pp,S)=forall x in Gterm0(tS), olt x translate(pp::S): chk={d_chk} BAD={d_bad}')
        if ex: print('      Dbad seg', ex[0], 'x', ex[1], 'E', ex[2])
        print(f'   ROOT olt x (P 0 tB Z) for x in Gterm0 tB: chk={root_chk} BAD={root_bad}')

if __name__ == '__main__':
    main()
