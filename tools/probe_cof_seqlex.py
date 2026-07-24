#!/usr/bin/env python3
"""Probe: the seqlex route to PSS Bachmann cofinality.

Checks, over an ST_PS closure:
  (Q1) which oper branches actually occur on ST_PS hosts of length > 1
       (self / lastpair-(0,0) / no-parent / bad)
  (Q2) the seqlex reformulation:  seqlex N M  =>  exists n>=1, N <=_lex M[n]
  (Q3) the "extension" obstruction shapes for the degenerate branches
"""
import sys
from fast_pss import (Lng, entry, diagSeq, oper, idx1, hasParent0, hasParent1,
                      parent0, parent1, fmt)

def pairlt(p, q):
    return p[0] < q[0] or (p[0] == q[0] and p[1] < q[1])

def seqlex(M, N):
    """column-lex: M <_lex N"""
    for a, b in zip(M, N):
        if a != b:
            return pairlt(a, b)
    return len(M) < len(N)

def branch(M):
    j1 = Lng(M) - 1
    if j1 == 0: return 'self'
    if entry(M,0,j1) == 0 and entry(M,1,j1) == 0: return 'zero'
    i1 = idx1(M, j1)
    if i1 == 1:
        if not hasParent1(M, j1): return 'noparent'
    else:
        if not hasParent0(M, j1): return 'noparent'
    return 'bad'

def closure(vmax, depth, nmax, cap=200000):
    seen = set()
    frontier = []
    for v in range(vmax+1):
        t = tuple(diagSeq(0, v))
        if t not in seen:
            seen.add(t); frontier.append(t)
    for _ in range(depth):
        nxt = []
        for M in frontier:
            for n in range(1, nmax+1):
                T = tuple(oper(list(M), n))
                if T not in seen and len(T) <= 30:
                    seen.add(T); nxt.append(T)
        frontier = nxt
        if len(seen) > cap: break
    return seen

if __name__ == '__main__':
    vmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    depth = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    nmax = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    S = sorted(closure(vmax, depth, nmax))
    print(f"closure size {len(S)}")

    # Q1: branch statistics
    from collections import Counter
    c = Counter(branch(list(M)) for M in S)
    print("branches:", dict(c))
    for M in S:
        if branch(list(M)) == 'noparent':
            print("  NOPARENT example:", fmt(M))
            break

    # invariant: row1 <= row0 ?
    bad_inv = [M for M in S if any(p[1] > p[0] for p in M)]
    print("row1<=row0 violations:", len(bad_inv), bad_inv[:3])

    # Q2: seqlex cofinality
    NMAX = 12
    viol = 0
    tested = 0
    for M in S:
        Ml = list(M)
        if Lng(Ml) <= 1: continue
        exps = [tuple(oper(Ml, n)) for n in range(1, NMAX+1)]
        for N in S:
            if N == M: continue
            if not seqlex(list(N), Ml): continue
            tested += 1
            ok = any(N == E or seqlex(list(N), list(E)) for E in exps)
            if not ok:
                viol += 1
                if viol <= 5:
                    print("VIOL:", fmt(M), "  N=", fmt(N))
    print(f"Q2: tested {tested}, violations {viol}")
