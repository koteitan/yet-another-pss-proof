#!/usr/bin/env python3
"""ROW-1 AXIS, step 4: model the ACTUAL drill recursion and check it stays on
faithfully-true instances (never hits the p0(p1(0)) killer).

The arg-direction goal: for ROOT single-tree tB=P y A Z, every canonical witness
tK in Gterm0(tB) has olt tK tB.  Proof attempt by olt-drill:
  olt(tK, tB):
    if lead tK < lead tB: TRUE (olt_P_of_lead_lt).
    if lead tK == lead tB (=y): tK=P y KA KS, tB=P y A C.
       sub-goal: olt(KA, A)  [if KA!=A]  -- RECURSE with (KA, A)
              or KS<C-ish    [if KA==A]  -- third coord
The recursion visits PAIRS (x, t) starting from (tK, tB), stepping (x,t)->(x.arg, t.arg)
when leads tie.  We model this DRILL and check at EVERY visited pair:
   (P1) x in Gterm0 t      (membership preserved -- self-similar)
   (P2) lead x <= lead t   (row-1 head bound)
   (P3) the drill terminates (tsize x decreases) and concludes olt.
If P1&P2 hold at every drilled pair with 0 viol @+5/+6/+7, the recursion is a
sound carrier: D(x,t) := x in Gterm0 t  (with lead x<=lead t as invariant), and
olt x t proved by drilling.  The killer p0(p1(0)) should NEVER be a drilled t
(it would require lead x > lead t at a drilled pair).
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
def tsize(t):
    if t == (): return 0
    return 1 + tsize(t[1]) + tsize(t[2])
def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def steps1(B): return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))
def blockok(d, B):
    if not B: return True
    return B[0][0] == d and all(p[0] >= d for p in B) and steps1(B)

def drill(x, t, visit):
    """model olt(x,t) by the lead-tie drill; record visited (x,t) pairs.
    returns the truth value AND whether the drill stayed sound (each step lead-tie
    only when leads equal)."""
    visit.append((x, t))
    if x == Z: return True
    if t == Z: return False
    a, b, c = x; e, f, g = t
    if a < e: return True                 # lead x < lead t
    if a > e: return False                # lead x > lead t  -- the KILLER branch
    # a == e: drill into args then tails (olt_P_P)
    if b != f:
        return drill(b, f, visit)         # RECURSE arg
    return drill(c, g, visit)             # RECURSE tail

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        chk = 0
        p1_bad = p2_bad = 0      # membership / lead-bound at drilled pairs
        killer = 0               # drill hit lead x > lead t (a>e) at an ARG-drill pair
        p1ex = p2ex = killex = None
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            if S != Z: continue
            if not blockok(1, B): continue
            G0 = set(Gterm(0, tB))
            for tK in G0:
                if tK == Z or tK == tB: continue
                chk += 1
                visit = []
                res = drill(tK, tB, visit)
                # res should be True (olt tK tB). check soundness of drill path.
                if not res:
                    killer += 1
                    if killex is None: killex = (mfmt(B), tfmt(tK))
                # at each ARG-drill pair (x,t) with both nonZ and equal leads
                # (the genuine recursion targets), check P1/P2.
                for (x, t) in visit:
                    if x == Z or t == Z: continue
                    # membership x in Gterm0 t
                    if x not in set(Gterm(0, t)):
                        p1_bad += 1
                        if p1ex is None: p1ex = (mfmt(B), tfmt(x), tfmt(t))
                    if lead(x) > lead(t):
                        p2_bad += 1
                        if p2ex is None: p2ex = (mfmt(B), tfmt(x), tfmt(t))
        print(f'[+{rounds}] md={md} single-tree canonical-K checked={chk}')
        print(f'   drill concluded olt FALSE (killer a>e): {killer}')
        if killex: print('      KILLER B', killex[0], 'tK', killex[1])
        print(f'   (P1) drilled pair x in Gterm0 t: BAD={p1_bad}')
        if p1ex: print('      P1bad B', p1ex[0], 'x', p1ex[1], 't', p1ex[2])
        print(f'   (P2) drilled pair lead x <= lead t: BAD={p2_bad}')
        if p2ex: print('      P2bad B', p2ex[0], 'x', p2ex[1], 't', p2ex[2])

if __name__ == '__main__':
    main()
