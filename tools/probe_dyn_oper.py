#!/usr/bin/env python3
"""DYNAMIC / oper-generation axis: test whether the seqlex-domination of the
arg-direction leaf is PRESERVED / ESTABLISHED across an oper step.

Target leaf: single-tree blockok-1 B (= tail of host (0,0)::B in ST_PS, row1<=1),
canonical witness K = contiguous infix B[i:j] with translate K in Gterm0(translate
B), translate K != translate B.  Need olt(translate K, translate B), equivalently
(B blockok-1) seqlex(shift K, B).

This probe ENUMERATES the ST_PS GENERATION (parent host M -> child host M[n]) and,
for each generation EDGE, checks:
  (T1) the leaf invariant Inv(host) := for every canonical arg-witness K of the
       descendant block B (B = host[1:]), olt(translate K, translate B).
       [This is the arg-direction clause for that host.]
  (T2) whether Inv(child) is implied by Inv(parent) + the oper-step structure --
       i.e. does each oper step PRESERVE Inv?  (the dynamic-induction step the
       static routes never tested)
  (T3) the BASE: Inv(diagSeq 0 v) for the generators.

We track generation by BFS over oper from diag bases, recording (M, child=M[n]).
Report 0-viol @+5/+6/+7 for T1 (Inv at every reachable host), T3 (base), and the
KEY T2 (preservation across the edge).
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, Lng, entry
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt

Z = ()
def lead(t): return t[0] if t else -1
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

def Inv(host):
    """arg-direction clause for the host: every canonical witness K of B=host[1:]
    has olt(translate K, translate B).  Returns (#checked, #viol)."""
    B = tuple(host[1:])
    tB = translate(B)
    if tB == Z: return (0, 0)
    G0 = set(Gterm(0, tB))
    seenK = {}
    for K in all_subblocks(B):
        tK = translate(K)
        if tK in G0 and tK != tB and tK not in seenK:
            seenK[tK] = K
    chk = viol = 0
    for tK in seenK:
        chk += 1
        if not olt(tK, tB): viol += 1
    return (chk, viol)

def gen_edges(maxdepth, vbases, ncounts, maxlen):
    """BFS the ST_PS generation; yield (parent, child) edges.  Track frontier of
    hosts; expand by oper with each n in ncounts up to maxdepth steps."""
    seen = set()
    edges = []
    frontier = []
    for v in vbases:
        base = tuple(diagSeq(0, v))
        if base not in seen:
            seen.add(base); frontier.append((base, 0))
    while frontier:
        M, d = frontier.pop()
        if d >= maxdepth: continue
        if Lng(M) <= 1: continue
        for n in ncounts:
            child = tuple(oper(M, n))
            if Lng(child) > maxlen: continue
            edges.append((M, child, n))
            if child not in seen:
                seen.add(child); frontier.append((child, d + 1))
    return edges, seen

def main():
    for depth in (5, 6, 7):
        edges, seen = gen_edges(depth, (1, 2, 3), (1, 2, 3), 28)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        # T1: Inv at every reachable host
        t1_chk = t1_viol = t1_bad_hosts = 0
        t1ex = None
        for M in hosts:
            c, v = Inv(M)
            t1_chk += c; t1_viol += v
            if v: t1_bad_hosts += 1; t1ex = (mfmt(M),) if t1ex is None else t1ex
        # T3: base
        t3_chk = t3_viol = 0
        for v in (1, 2, 3):
            base = diagSeq(0, v)
            c, vv = Inv(base); t3_chk += c; t3_viol += vv
        # T2: preservation across edges (parent Inv ok => child Inv ok)
        edge_chk = edge_break = 0   # edges where parent Inv-clean but child has viol
        ebex = None
        for (M, child, n) in edges:
            if not (M and M[0] == (0, 0) and all(x[1] <= 1 for x in M)): continue
            if not (child and child[0] == (0, 0) and all(x[1] <= 1 for x in child)): continue
            if Lng(child) > 18: continue
            _, pv = Inv(M)
            _, cv = Inv(child)
            edge_chk += 1
            if pv == 0 and cv > 0:
                edge_break += 1
                if ebex is None: ebex = (mfmt(M), n, mfmt(child))
        print(f'[depth+{depth}] hosts={len(hosts)} edges={len(edges)}')
        print(f'   T1 Inv (arg clause) at every host: chk={t1_chk} VIOL={t1_viol} bad-hosts={t1_bad_hosts}')
        print(f'   T3 base Inv(diagSeq): chk={t3_chk} VIOL={t3_viol}')
        print(f'   T2 PRESERVATION (parent clean -> child viol): edges-chk={edge_chk} BREAK={edge_break}')
        if ebex: print('      BREAK ex parent', ebex[0], 'n', ebex[1], 'child', ebex[2])

if __name__ == '__main__':
    main()
