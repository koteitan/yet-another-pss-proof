#!/usr/bin/env python3
"""probe_bmocf_ancestor.py -- CHEAP model verification of the advisor's BMOCF
Ancestor (<=_M / <_M^Next) reframe of the lean-yapss single residual core.

We:
  (0) implement <=_M and <_M^Next per the HTML definition (generic over rows i),
      and cross-check the row-0 case agrees with the existing fast_pss.le0 and
      the row-1 case agrees with nextrel1.
  (A) test  pfire-firing  <=>  (0,0) <=_M (0,j_1)   (Ascend firing condition)
  (B) test  proj maxo-violator selection  <=>  i_0 = max{i | (i,0)<=_M(i,j_1)}
  (CRUX) test whether a <_M^Next-chain measure gives a well-founded decreasing
      measure proving  SubBlock B K -> olt(translate K)(translate B).
  (5) re-confirm the core itself is 0 violations.

All at closure depth 5 and 6 (NOT 4 -- closure+4 gives false positives).
"""
import sys
sys.path.insert(0, '.')
from fast_pss import (oper, diagSeq, Lng, le0, nextrel0, nextrel1, entry, idx1,
                      hasParent1, parent1, _reach0_masks)
from wfe_explore import translate, olt, maxsub, fmt
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj

# ---------------------------------------------------------------------------
# (0) BMOCF Ancestor relations, implemented straight from the HTML definition
# ---------------------------------------------------------------------------
# M is a 2-row matrix: list of (row0,row1). M_{i,j} = M[j][i].  i in {0,1}.
# Rows above i are i'<i.  (Higher row index = "lower" / inner in the array;
# the HTML uses "i'<i" as "all rows above".)

def Mij(M, i, j):
    return M[j][i]

NROWS = 2

def build_next_le(M):
    """Compute <_M^Next and <=_M (as boolean dicts) for a 2-row matrix M,
    faithfully per the HTML simultaneous recursion.

    Because <_M^Next at row i_1 references <=_M only at rows i<i_1, we can
    build row by row from i=0 upward (row 0 needs no lower rows)."""
    n = Lng(M)
    # le[i] : set of (j0,j1) with (i,j0) <=_M (i,j1)
    # nx[i] : set of (j0,j1) with (i,j0) <_M^Next (i,j1)
    le = [set() for _ in range(NROWS)]
    nx = [set() for _ in range(NROWS)]
    for i1 in range(NROWS):
        # compute nx[i1] using le[i] for i<i1 (already built)
        for j0 in range(n):
            for j1 in range(j0+1, n):
                # cond1 i0==i1 (we fix row), cond2 j0<j1 ok
                # cond3: for all i<i1: (i,j0) <=_M (i,j1)
                if not all((j0, j1) in le[i] for i in range(i1)):
                    continue
                # cond4: M_{i1,j0} < M_{i1,j1}
                if not (Mij(M, i1, j0) < Mij(M, i1, j1)):
                    continue
                # cond5 (valley): for all j with j0<j<=j1, if for all i<i1
                #   (i,j)<=_M(i,j1) then M_{i1,j} >= M_{i1,j1}
                ok = True
                for j in range(j0+1, j1+1):
                    if all((j, j1) in le[i] for i in range(i1)):
                        if not (Mij(M, i1, j) >= Mij(M, i1, j1)):
                            ok = False
                            break
                if ok:
                    nx[i1].add((j0, j1))
        # build le[i1] as reflexive-transitive closure along nx[i1] chains
        # (same row).  reflexive: (j,j).
        adj = {j: set() for j in range(n)}
        for (a, b) in nx[i1]:
            adj[a].add(b)
        for j in range(n):
            le[i1].add((j, j))
        # transitive closure
        changed = True
        while changed:
            changed = False
            for (a, b) in list(le[i1]):
                for c in adj.get(b, ()):
                    if (a, c) not in le[i1]:
                        le[i1].add((a, c)); changed = True
    return nx, le

def leM(M, i, j0, j1):
    nx, le = build_next_le(M)
    return (j0, j1) in le[i]

# ---------------------------------------------------------------------------
# closure enumeration with depth tracking
# ---------------------------------------------------------------------------
def enum_depth(seed_max_v, oper_ns, max_len, rounds):
    seen = {}
    frontier = []
    for v in range(seed_max_v+1):
        M = tuple(diagSeq(0, v))
        if M not in seen:
            seen[M] = 0; frontier.append(M)
    for r in range(rounds):
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in oper_ns:
                N = tuple(oper(list(M), n))
                if len(N) <= max_len and N not in seen:
                    seen[N] = r+1; nxt.append(N)
        frontier = nxt
        if not frontier: break
    return seen

# ---------------------------------------------------------------------------
# (0) cross-check ancestor implementation vs fast_pss le0 / nextrel1
# ---------------------------------------------------------------------------
def check_ancestor_matches_lean(seen):
    bad_le0 = bad_nx0 = bad_nx1 = 0
    tot = 0
    exs = []
    for M in seen:
        if Lng(M) < 1: continue
        n = Lng(M)
        nx, le = build_next_le(M)
        for a in range(n):
            for b in range(n):
                tot += 1
                # row0 le: <=_M at i=0 vs le0
                want = le0(M, a, b)
                got = (a, b) in le[0]
                if want != got:
                    bad_le0 += 1
                    if len(exs) < 5: exs.append(('LE0', M, a, b, want, got))
                # row0 next vs nextrel0
                if a < b:
                    w0 = nextrel0(M, a, b); g0 = (a, b) in nx[0]
                    if w0 != g0: bad_nx0 += 1
                    w1 = nextrel1(M, a, b); g1 = (a, b) in nx[1]
                    if w1 != g1:
                        bad_nx1 += 1
                        if len(exs) < 8: exs.append(('NX1', M, a, b, w1, g1))
    return tot, bad_le0, bad_nx0, bad_nx1, exs

if __name__ == '__main__':
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        md = max(seen.values())
        # keep modest corpus for the O(n^3) ancestor builder
        corpus = [M for M in seen if Lng(M) <= 16]
        tot, b0, bn0, bn1, exs = check_ancestor_matches_lean(corpus)
        print(f'[CHK closure+{rounds}] hosts={len(seen)} (used {len(corpus)}) '
              f'maxdepth={md} pairs={tot}  le0-mismatch={b0} '
              f'nextrel0-mismatch={bn0} nextrel1-mismatch={bn1}')
        for e in exs[:6]:
            print('   ', e[0], fmt(e[1]), 'a,b=', e[2], e[3], 'want/got', e[4], e[5])
