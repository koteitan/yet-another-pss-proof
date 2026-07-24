#!/usr/bin/env python3
"""Probe the ASCENDING (d0 > 0) half of the PSS cofinality crux.

Setting (bad branch, d0>0):
  M = G ++ blk ++ [lp],  blk = (v0,w0)::R,  lp = (v0+d0, lp2)
  N = G ++ blk ++ q::S   with pairlt q lp
Facts probed:
  A1  lp.2 = w0 + 1
  A2  q <= (v0+d0, w0)  (so q is at most the head of the next copy)
  A3  when q == (v0+d0, w0):  R' <=lex shiftr0 d0 R
      where R' = takeWhile (row0 > v0+d0) S  (the descendant block of q in N)
"""
import sys
from collections import Counter
from fast_pss import (Lng, entry, diagSeq, oper, idx1, hasParent0, hasParent1,
                      parent0, parent1, fmt)


def pairlt(p, q):
    return p[0] < q[0] or (p[0] == q[0] and p[1] < q[1])


def seqlex(M, N):
    for a, b in zip(M, N):
        if a != b:
            return pairlt(a, b)
    return len(M) < len(N)


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

    a1 = a2 = a3 = 0
    a3tested = 0
    ex3 = []
    for M in S:
        Ml = list(M)
        if branch(Ml) != 'bad': continue
        G, blk, lp, d0, j0, i1 = decomp(Ml)
        if d0 == 0: continue
        v0, w0 = blk[0]
        R = blk[1:]
        if lp[1] != w0 + 1:
            a1 += 1
        pre = tuple(G + blk); p = len(pre)
        Rsh = [(x + d0, y) for (x, y) in R]
        for N in S:
            if len(N) > p and N[:p] == pre:
                q = N[p]
                if not pairlt(q, lp):
                    continue
                # A2
                if pairlt((v0 + d0, w0), q):
                    a2 += 1
                # A3
                if q == (v0 + d0, w0):
                    a3tested += 1
                    tail = list(N[p + 1:])
                    Rp = []
                    for x in tail:
                        if x[0] > v0 + d0:
                            Rp.append(x)
                        else:
                            break
                    if not (Rp == Rsh or seqlex(Rp, Rsh)):
                        a3 += 1
                        if len(ex3) < 3:
                            ex3.append((fmt(Ml), fmt(N), Rp, Rsh))
    print("A1 (lp.2 = w0+1) violations:", a1)
    print("A2 (q <= next copy head) violations:", a2)
    print(f"A3 (R' <= shiftr0 d0 R) tested {a3tested}, violations {a3}", ex3)
