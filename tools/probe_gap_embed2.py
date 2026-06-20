#!/usr/bin/env python3
"""probe_gap_embed2.py -- soundness checks A (non-circular) and B (needed
witnesses satisfy) for the §11 gap-embedding carrier fix.

gap_embed.py found GC_below (inserted label a' >= a_below) is EXACTLY equivalent
to olt(prev,cur) on the single-node-insertion LEFT-grow steps (0 false-keep, 0
false-drop), and at the a'==a_below ties GC_below never diverges from olt.  This
SMELLS circular (criterion A): for cur=(a',prev,c') the olt definition unfolds to
exactly `a' vs a_below` then recursion -- GC_below IS olt's first step.

Here we settle it decisively:

CHECK A (CIRCULARITY).  Prove/refute that GC_below == olt on node-insertion steps
is a DEFINITIONAL identity (=> circular), vs a genuine structural refinement.
We do it by checking the IMPLICATION the architect needs: a gap condition is
USEFUL only if, restricted to FULL multi-node embeddings K ↪ B, the PER-NODE gap
checks (each checkable without olt, locally) COMPOSE to give olt(tK,tB) WITHOUT
re-deriving olt.  We test: define GAPEMB(K,B) := the canonical infix embedding of
K into B is homeomorphic AND every inserted node satisfies GC_below LOCALLY.  Then:
  - Is GAPEMB(K,B) <=> olt(tK,tB) on the witness endpoints?  (if yes and the only
    cost is summing local subscript checks, the carrier is at least SOUND.)
  - CRUCIAL non-circularity discriminator: are there node-insertion steps where
    GC_below holds via the a'==a_below TIE but the SUBTREE comparison olt(arg,arg)
    is what really decides -- i.e. GC_below alone (local) does NOT determine olt,
    you still need the recursive olt on the args?  Count tie-steps and check
    whether a PURELY-LOCAL GC (no recursion) suffices.  If recursion into args is
    needed, GC_below is NOT a self-contained local condition => it is olt in
    disguise (circular).

CHECK B (NEEDED WITNESSES).  For the canonical Gterm-0 witnesses K of real
translate B (the H0clause_oper_step content, olt(tK,tB) TRUE 514/514), does the
gap-embedding K <=_e B hold = does EVERY inserted node along the K->B path satisfy
GC_below?  If some needed witness has a gap-VIOLATING inserted node, the fix
EXCLUDES exactly what we must dominate -> hollow.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def head_sub(t): return t[0] if t else -1

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

def left_path_gap_ok(B, i, n, use_strict=False):
    """Walk the LEFT-grow path [i:n] -> [0:n]; at each pure node-insertion step
    cur=(a',prev,c') check GC_below LOCALLY (a' >= a_below, or strict).  Return
    (all_local_gc_ok, needed_recursion_at_tie) where needed_recursion = a tie step
    a'==a_below occurred (so local GC alone is indecisive about olt -- olt would
    recurse into args)."""
    lo = i
    prev = translate(tuple(B[lo:n]))
    all_ok = True
    tie_recursion = False
    while lo > 0:
        lo -= 1
        cur = translate(tuple(B[lo:n]))
        if cur == Z or cur == prev:
            prev = cur; continue
        aprime = head_sub(cur); a_below = head_sub(prev)
        if aprime == a_below:
            tie_recursion = True   # local GC can't decide; olt would recurse
        gc = (aprime > a_below) if use_strict else (aprime >= a_below)
        if not gc:
            all_ok = False
        prev = cur
    return all_ok, tie_recursion

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        hosts = [M for M in seen if Lng(M) <= 20 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())

        # CHECK B: needed witnesses (endpoints) -- does GAPEMB(K,B) hold &
        # does GAPEMB <=> olt(tK,tB)?
        needed = 0
        gapemb_ok = 0        # GC_below all along the path holds
        gapemb_vs_olt_mis = 0
        # how many needed-witness paths REQUIRE a recursion-tie (local GC alone
        # insufficient) = circularity evidence
        needed_with_tie = 0
        ex_drop = []
        for B0 in hosts:
            B = tuple(B0[1:]); tB = translate(B)
            if tB == Z: continue
            n = len(B); G0 = set(Gterm(0, tB))
            for x in G0:
                if x == tB: continue
                ij = find_infix(B, x)
                if ij is None: continue
                i, j = ij
                tK = translate(tuple(B[i:j]))
                ol_endpoint = olt(tK, tB)
                if not ol_endpoint:
                    continue  # not a case we NEED (witness sanity says these are 0 anyway)
                needed += 1
                # full embedding = grow right to [i:n] then left to [0:n].
                # right segment is 0-viol monotone (GREEN); the gap content is the
                # LEFT segment.  Evaluate GC_below on the LEFT segment of [i:n]->[0:n].
                all_ok, tie = left_path_gap_ok(B, i, n)
                if all_ok: gapemb_ok += 1
                else:
                    if len(ex_drop) < 5: ex_drop.append((B, (i, j), tK))
                # GAPEMB(=all_ok) should match olt(tK,tB)=True; mismatch = drop a needed one
                if all_ok != ol_endpoint:
                    gapemb_vs_olt_mis += 1
                if tie: needed_with_tie += 1

        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  CHECK B (needed witnesses, olt(tK,tB)=TRUE): needed={needed}')
        print(f'     gap-embedding (GC_below all along LEFT path) HOLDS: {gapemb_ok}  '
              f'(DROPPED needed={needed-gapemb_ok})')
        print(f'     GAPEMB != olt(tK,tB) mismatches (needed ones excluded): {gapemb_vs_olt_mis}')
        for B,ij,tK in ex_drop[:3]:
            print('        DROPPED-needed B',mfmt(B),'witness',tfmt(tK)[:30])
        print(f'  CHECK A (circularity): needed paths REQUIRING a tie-recursion '
              f'(local GC indecisive, olt-recursion needed): {needed_with_tie}/{needed}')

if __name__ == '__main__':
    main()
