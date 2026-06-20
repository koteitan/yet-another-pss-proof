#!/usr/bin/env python3
"""ANCESTOR-DISTANCE static-induction falsification probe (architect §24.2, ONE cheap probe).

Question: can `seqlex(shift canonical-K, B)` (the H0clause forest residual) be proved by
STATIC induction on the BMS FOREST-ANCESTOR (parent0/parent1) distance of K's root column up
to B's root, OR does the carrier falsify at INTERMEDIATE forest-ancestors (like round-4's
translate-tree SubBlock chain, FALSE 183/443, and round-7's derivation)?

This is DISTINCT from round-4 (translate-tree takeWhile/dropWhile desc/sib chain) and round-7
(oper-derivation), because the BMS forest-parent relation (le0/nextrel) is NOT the translate
tree structure (round-8: "translate tree ⊥ oper copy boundaries").

Carrier P(c) for canonical witness K=B[i:j] and forest-ancestor column c of K's root (in
M=(0,0)::B indexing): seqlex(shift_to(K, M[c].row0), M[c:]) is DOWNWARD-or-prefix at first diff.
The induction would climb the chain K-root -> parent -> ... -> 0 (B's root). FALSIFICATION =
any INTERMEDIATE ancestor c (strictly between K-root and 0) where the firstdiff is gt0/gt1/
prefixB ("upward") while it holds at the endpoints (K itself and the full B).

VERDICT: 0-viol at intermediates +5/+6/+7 => genuine lever (worth a Lean attempt).
         viols at intermediates => carrier dead => folds into forest-structural => frontal-only.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, idx1, hasParent1, parent1, hasParent0, parent0, entry as fentry
from wfe_explore import translate, olt
from probe_bmocf_ancestor import enum_depth
from probe_arch_global_inv import Gterm, infixes, shift_to, seqlex_firstdiff


def fparent(M, c):
    """BMS forest parent column of c (None at a root)."""
    if c <= 0:
        return None
    i1 = idx1(M, c)
    if i1 == 1:
        return parent1(M, c) if hasParent1(M, c) else None
    else:
        return parent0(M, c) if hasParent0(M, c) else None


def ancestor_chain(M, c):
    """columns from c up to the root, via forest parent."""
    chain = [c]
    seen = {c}
    while True:
        p = fparent(M, c)
        if p is None or p in seen:
            break
        chain.append(p)
        seen.add(p)
        c = p
    return chain


def probe(M):
    """For each canonical-K witness, walk K's forest-ancestor chain and test the seqlex
    carrier at every ancestor block. Returns (n_witness, n_intermediate_viol, examples)."""
    B = M[1:]
    if not B:
        return 0, 0, []
    t = translate(B)
    g0 = Gterm(0, t)
    nW = 0
    nViol = 0
    examples = []
    for g in g0:
        # recover canonical contiguous infix K=B[i:j]
        K = None; iK = None
        for i, j, cand in infixes(B):
            if translate(cand) == g:
                K = cand; iK = i; break
        if K is None:
            continue
        if g == t:
            continue  # trivial whole-block witness
        nW += 1
        rootCol = iK + 1  # B[i] == M[i+1]
        chain = ancestor_chain(M, rootCol)  # rootCol ... 0
        # test the carrier at every ancestor block M[c:]
        endpoints = {chain[0], 0}
        kinds = []
        for c in chain:
            Hc = list(M[c:])
            if not Hc:
                continue
            Ksh = shift_to(list(K), Hc[0][0])
            kind, pos = seqlex_firstdiff(Ksh, Hc)
            kinds.append((c, kind))
            upward = kind in ('gt0', 'gt1', 'prefixB')
            if upward and c not in endpoints:
                nViol += 1
                if len(examples) < 6:
                    examples.append((tuple(M), tuple(K), c, kind))
    return nW, nViol, examples


def run(tag, hosts):
    totW = 0; totV = 0; exs = []
    seen = set()
    for M in hosts:
        M = tuple(M)
        if M in seen:
            continue
        seen.add(M)
        try:
            w, v, e = probe(M)
        except Exception:
            continue
        totW += w; totV += v
        if v and len(exs) < 6:
            exs += e
    print(f"[{tag}] hosts={len(seen)} witnesses={totW} INTERMEDIATE-viols={totV}")
    for ex in exs[:6]:
        print("   viol:", ex)
    return totV


if __name__ == '__main__':
    # ST_PS hosts (0,0)::B, row1<=1, at closure +5/+6/+7 (enum_depth params mirror kept probes)
    for rounds, ml in [(5, 9), (6, 10), (7, 11)]:
        hosts = [M for M in enum_depth(2, (1, 2, 3), ml, rounds)
                 if len(M) >= 2 and all(p[1] <= 1 for p in M) and M[0] == (0, 0)]
        run(f"+{rounds}", hosts)
