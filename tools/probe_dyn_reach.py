#!/usr/bin/env python3
"""DYNAMIC axis, step 2: is the row1<=1 fragment self-contained for the
Inv-induction?  Two questions:

 Q-A: is every row1<=1 host reachable by oper steps STAYING in row1<=1 from the
      row1<=1 base diagSeq 0 1 = (0,0)(1,1)?  (If yes, induction base = (0,0)(1,1)
      which satisfies Inv, and the row1<=1-preserving steps carry it.)
      If NO (some row1<=1 host only comes from a row1>1 parent), we need the
      stronger Inv-on-the-whole-generation, which FAILS at high-v bases.

 Q-B: does the oper step preserve Inv even when the PARENT is NOT row1<=1 but the
      CHILD is row1<=1?  (the "row1-dropping" edges).  If Inv-clean is preserved
      across these too, then a row1<=1 host can inherit Inv from any parent that
      itself satisfies Inv -- but high-v bases DON'T.  So we need: along EVERY
      generation path to a row1<=1 host, Inv holds from some point on.

 Q-C (the real test): track FULL generation paths.  For each row1<=1 host, does
      there EXIST a generation path from a base on which Inv holds at EVERY node?
      Equivalently: is the FIRST row1<=1 node on the path Inv-clean, and is Inv
      preserved thereafter?  Measure: among row1<=1 hosts, how many have a parent
      (in the BFS tree) that is row1<=1?  And the "entry" nodes (row1<=1 with
      only row1>1 parents) -- do they satisfy Inv (0-viol)?
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, Lng
from wfe_explore import translate, olt
from fast_pss import fmt as mfmt

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
def Inv(host):
    B = tuple(host[1:]); tB = translate(B)
    if tB == Z: return 0
    G0 = set(Gterm(0, tB)); seenK = set()
    viol = 0
    for K in all_subblocks(B):
        tK = translate(K)
        if tK in G0 and tK != tB and tK not in seenK:
            seenK.add(tK)
            if not olt(tK, tB): viol += 1
    return viol

def main():
    for depth in (5, 6, 7):
        # BFS all edges
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
                edges.append((M, ch))
                if ch not in seen: seen.add(ch); frontier.append((ch, d + 1))
        hosts = [M for M in seen if Lng(M) <= 18 and r1le1(M) and M and M[0] == (0, 0)]
        hostset = set(hosts)
        # build parent map (any parent)
        parents = {}
        for (M, ch) in edges:
            parents.setdefault(ch, []).append(M)
        # Q-C: row1<=1 hosts whose ALL parents are row1>1 (entry nodes)
        entry_nodes = []
        has_r1_parent = 0
        for h in hosts:
            ps = parents.get(h, [])
            if not ps:
                entry_nodes.append((h, 'NO-PARENT/base'))
            elif any(r1le1(p) for p in ps):
                has_r1_parent += 1
            else:
                entry_nodes.append((h, 'only-r1>1-parents'))
        # do entry nodes satisfy Inv?
        entry_inv_viol = sum(1 for (h, _) in entry_nodes if Inv(h) > 0)
        # Q-A: among r1<=1 hosts != base, fraction reachable via a r1<=1 parent
        # Q-B: edges parent r1>1, child r1<=1 : Inv preserved? (parent Inv may be >0)
        qb_edges = qb_break = 0
        for (M, ch) in edges:
            if not (ch in hostset): continue
            if r1le1(M): continue   # parent row1>1
            qb_edges += 1
            # does child satisfy Inv regardless? (we already know T1 0-viol; here
            # we just confirm these row1-drop children are Inv-clean)
            if Inv(ch) > 0: qb_break += 1
        print(f'[depth+{depth}] r1<=1 hosts={len(hosts)} edges={len(edges)}')
        print(f'   Q-C entry-nodes (r1<=1 with no r1<=1 parent)={len(entry_nodes)} '
              f'has-r1<=1-parent={has_r1_parent}')
        print(f'        entry-nodes VIOLATING Inv: {entry_inv_viol}')
        print(f'   Q-B row1-drop edges (parent r1>1 -> child r1<=1)={qb_edges} '
              f'child-Inv-viol={qb_break}')
        for (h, why) in entry_nodes[:8]:
            print(f'      entry {mfmt(h)} [{why}] Inv-viol={Inv(h)}')

if __name__ == '__main__':
    main()
