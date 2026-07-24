#!/usr/bin/env python3
"""Probe the structural facts needed by the seqlex route to PSS cofinality.

F1: does the `noparent` oper branch ever occur on ST_PS with length > 1?
F2: in the bad branch with d0 > 0 (i1 = 1), is  lp.2 = w0 + 1 ?
    (w0 = row-1 of the block root j0, lp = last column)
F3: in the bad branch with d0 = 0 (i1 = 0), is  lp = (v0+1, 0) and R all > v0 ?
F4: sibling non-increase (CNF at the seqlex level): for a standard form N,
    if N = A ++ (v,w0)::R ++ (v,w)::S with all R above v, then w <= w0.
F5: the "extension" obstruction: is there N in ST_PS extending G++blk (with
    M = G++blk++[lp] in ST_PS) whose next pair q satisfies pairlt q lp but
    q > the head of the next copy?
"""
import sys
from collections import Counter
from fast_pss import (Lng, entry, diagSeq, oper, idx1, hasParent0, hasParent1,
                      parent0, parent1, fmt)


def branch(M):
    j1 = Lng(M) - 1
    if j1 == 0: return 'self'
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0: return 'zero'
    i1 = idx1(M, j1)
    if i1 == 1:
        if not hasParent1(M, j1): return 'noparent'
    else:
        if not hasParent0(M, j1): return 'noparent'
    return 'bad'


def decomp(M):
    """(G, blk, lp, d0, j0) for the bad branch."""
    j1 = Lng(M) - 1
    i1 = idx1(M, j1)
    j0 = parent1(M, j1) if i1 == 1 else parent0(M, j1)
    d0 = (entry(M, 0, j1) - entry(M, 0, j0)) if i1 > 0 else 0
    return M[:j0], M[j0:j1], M[j1], d0, j0, i1


def closure(vmax, depth, nmax, maxlen=32, cap=400000):
    seen = set(); frontier = []
    for v in range(vmax + 1):
        t = tuple(diagSeq(0, v))
        if t not in seen:
            seen.add(t); frontier.append(t)
    for _ in range(depth):
        nxt = []
        for M in frontier:
            for n in range(1, nmax + 1):
                T = tuple(oper(list(M), n))
                if T not in seen and len(T) <= maxlen:
                    seen.add(T); nxt.append(T)
        frontier = nxt
        if len(seen) > cap: break
    return seen


if __name__ == '__main__':
    vmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    depth = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    nmax = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    S = sorted(closure(vmax, depth, nmax))
    print(f"closure size {len(S)}")
    print("branches:", dict(Counter(branch(list(M)) for M in S)))

    # F2 / F3
    f2bad = []; f3bad = []
    for M in S:
        Ml = list(M)
        if branch(Ml) != 'bad': continue
        G, blk, lp, d0, j0, i1 = decomp(Ml)
        v0, w0 = blk[0]
        if d0 > 0:
            if lp[1] != w0 + 1: f2bad.append((fmt(Ml), lp, w0))
        else:
            if not (lp == (v0 + 1, 0) and all(p[0] > v0 for p in blk[1:])):
                f3bad.append((fmt(Ml), lp, v0, w0))
    print("F2 (d0>0 -> lp.2 = w0+1) violations:", len(f2bad), f2bad[:3])
    print("F3 (d0=0 -> lp=(v0+1,0), R>v0) violations:", len(f3bad), f3bad[:3])

    # F4 sibling non-increase
    f4bad = []
    for M in S:
        Ml = list(M)
        n = len(Ml)
        for i in range(n):
            v, w0 = Ml[i]
            j = i + 1
            while j < n and Ml[j][0] > v:
                j += 1
            if j < n and Ml[j][0] == v:
                if Ml[j][1] > w0:
                    f4bad.append((fmt(Ml), i, j))
    print("F4 (sibling row-1 non-increase) violations:", len(f4bad), f4bad[:3])

    # F5 extension obstruction
    Sset = set(S)
    f5 = []
    for M in S:
        Ml = list(M)
        if branch(Ml) != 'bad': continue
        G, blk, lp, d0, j0, i1 = decomp(Ml)
        v0, w0 = blk[0]
        pre = tuple(G + blk)
        p = len(pre)
        nexthead = (v0 + d0, w0)
        for N in S:
            if len(N) > p and N[:p] == pre:
                q = N[p]
                # pairlt q lp  and  nexthead < q  ->  obstruction
                lt_lp = q[0] < lp[0] or (q[0] == lp[0] and q[1] < lp[1])
                gt_nh = nexthead[0] < q[0] or (nexthead[0] == q[0] and nexthead[1] < q[1])
                if lt_lp and gt_nh:
                    f5.append((fmt(Ml), fmt(N), q, lp, nexthead))
    print("F5 obstructions:", len(f5), f5[:3])
