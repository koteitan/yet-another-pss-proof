#!/usr/bin/env python3
"""DYNAMIC axis, step 3: is Inv(child) implied by the OPER-STEP STRUCTURE alone
(per-copy core_i1 domination), independent of Inv(parent)?

If YES, the dynamic induction is even cleaner: Inv(M[n]) follows from the tiling
of M[n] = G ++ n-copies-of-block, via core_i1 per copy, for ANY ST_PS M -- so the
row1-drop entry (child of diagSeq 0 2) is covered without needing Inv(parent).

We test, for EVERY oper edge (M, child=M[n]) producing a ROW1<=1 child:
  (S1) Inv(child) holds (0-viol)  [already known via T1, reconfirm on edges]
  (S2) the child's canonical witnesses fall into classes by the tiling:
       child = G ++ B_0 ++ B_1 ++ ... ++ B_{n-1}  where B_k = block shifted by k*d0.
       A witness K (infix of child[1:]) either:
         (a) lies entirely within one copy region [within a B_k or G] -- "intra",
         (b) spans a copy boundary -- "inter".
       For the seqlex/core_i1 argument we need: the dominating comparison is the
       ascending-copy one (core_i1: a later/larger copy dominates).  Tabulate
       intra vs inter, and check domination holds in each class.
  (S3) the KEY: does olt(translate K, translate B) for each witness follow from a
       comparison BETWEEN COPIES (core_i1 shape: block ++ next-copy-start <o
       block ++ [lp])?  Measure whether the FIRST divergence of (shift K) vs B
       lands at a COPY BOUNDARY (the d0-ramp), confirming the tiling drives it.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, Lng, entry
from wfe_explore import translate, olt
from fast_pss import fmt as mfmt
from collections import Counter

Z = ()
def r1le1(M): return all(c[1] <= 1 for c in M)
def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def split(B):
    c = B[0]; rest = B[1:]; i = 0
    while i < len(rest) and rest[i][0] > c[0]: i += 1
    return c, tuple(rest[:i]), tuple(rest[i:])
def all_subblocks(B):
    res = []
    def rec(seg):
        seg = tuple(seg); res.append(seg)
        if not seg: return
        c, d, s = split(seg); rec(d); rec(s)
    rec(tuple(B)); return res
def Inv_viol(host):
    B = tuple(host[1:]); tB = translate(B)
    if tB == Z: return 0
    G0 = set(Gterm(0, tB)); seen = set(); viol = 0
    for K in all_subblocks(B):
        tK = translate(K)
        if tK in G0 and tK != tB and tK not in seen:
            seen.add(tK)
            if not olt(tK, tB): viol += 1
    return viol

def oper_components(M, n):
    """return (G, block, d0) for the genuine tiling branch, else None."""
    j1 = Lng(M) - 1
    if j1 == 0: return None
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0: return None
    from fast_pss import idx1, hasParent1, parent1, hasParent0, parent0
    i1 = idx1(M, j1)
    if i1 == 1:
        if not hasParent1(M, j1): return None
        j0 = parent1(M, j1)
    else:
        if not hasParent0(M, j1): return None
        j0 = parent0(M, j1)
    d0 = (entry(M, 0, j1) - entry(M, 0, j0)) if i1 > 0 else 0
    G = list(M[:j0])
    block = [(entry(M, 0, j), entry(M, 1, j)) for j in range(j0, j1)]
    return (G, block, d0)

def main():
    for depth in (5, 6, 7):
        seen = set(); frontier = []; edges = []
        for v in (1, 2, 3, 4):
            base = tuple(diagSeq(0, v))
            if base not in seen: seen.add(base); frontier.append((base, 0))
        while frontier:
            M, d = frontier.pop()
            if d >= depth or Lng(M) <= 1: continue
            for n in (1, 2, 3):
                ch = tuple(oper(M, n))
                if Lng(ch) > 28: continue
                edges.append((M, ch, n))
                if ch not in seen: seen.add(ch); frontier.append((ch, d + 1))
        # S1: Inv(child) on every edge with row1<=1 child of length<=18
        s1_edges = s1_viol = 0
        # also: among these, how many have PARENT with Inv-viol>0 (parent 'bad')
        # but child still Inv-clean -> step ESTABLISHES Inv independent of parent
        established = 0
        examples = []
        for (M, ch, n) in edges:
            if not (ch and ch[0] == (0, 0) and r1le1(ch) and Lng(ch) <= 18): continue
            s1_edges += 1
            cv = Inv_viol(ch)
            if cv > 0: s1_viol += 1
            pv = Inv_viol(M) if (M and M[0] == (0, 0)) else -1
            if cv == 0 and pv != 0:    # parent bad or non-host, child clean
                established += 1
                if len(examples) < 6 and pv > 0:
                    examples.append((mfmt(M), n, mfmt(ch), pv))
        print(f'[depth+{depth}] edges-with-r1<=1-child={s1_edges}')
        print(f'   S1 Inv(child) viol={s1_viol}')
        print(f'   step ESTABLISHES Inv independent of parent (parent bad/non-host, child clean): {established}')
        for M, n, ch, pv in examples[:6]:
            print(f'      parent {M} (Inv-viol={pv}) --n={n}--> child {ch} (clean)')

if __name__ == '__main__':
    main()
