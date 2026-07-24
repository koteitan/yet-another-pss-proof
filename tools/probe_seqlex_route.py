#!/usr/bin/env python3
"""Test the SEQLEX route for the root clause of H0clause_oper_step.

Root clause: x in Gterm0(translate B), (0,0)::B in ST_PS row1<=1.
Gterm_translate_subblock: x = translate K for SubBlock K of B.
seqlex_imp_olt: translate K <o translate B  <=  seqlex K B & blockok d K & blockok d B.

We test:  for the witness K of each x in Gterm0(translate B):
  - blockok 1 B ?   (B is the descendant block; (0,0)::B in ST_PS so all row0>=1,
    head row0 =1, steps1)  -> d should be 1 for B.
  - blockok 1 K ?   for the SubBlock K witness.
  - seqlex K B ?
If all hold (0 viol) the route closes via existing lemmas.

NOTE on d: translate B = P (B.head.2) ... and B has all row0 >= 1 (descendant of
(0,0)). The takeWhile in translate uses 0<q.1 i.e. row0>=1. blockok d B with d=
B.head.1 = 1.  But seqlex_imp_olt needs SAME d for K and B.  A SubBlock K of B
may start deeper.  Hmm -- so we need K and B at the same depth d.  The Gterm0
witness K: where does it sit?  Let's just measure blockok at d = K.head.1 and
d=B.head.1 and whether they match, and seqlex.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

def lead(t): return t[0] if t else -1
def Gterm(u, t):
    if t == (): return []
    a, b, c = t
    out = []
    if u <= a:
        out.append(b); out += Gterm(u, b)
    out += Gterm(u, c)
    return out

# enumerate SubBlock witnesses with their translate
def subblock_map(B):
    """return dict translate(K) -> list of K (SubBlocks)."""
    from collections import defaultdict
    d = defaultdict(list)
    def rec(seg):
        seg = tuple(seg)
        d[translate(seg)].append(seg)
        if not seg: return
        (x, y) = seg[0]; rest = seg[1:]
        i = 0
        while i < len(rest) and rest[i][0] > x: i += 1
        rec(rest[:i]); rec(rest[i:])
    rec(tuple(B))
    return d

def steps1(B):
    for j in range(len(B)-1):
        if B[j+1][0] > B[j][0] + 1: return False
    return True
def blockok(d, B):
    if not B: return True
    if B[0][0] != d: return False
    if any(p[0] < d for p in B): return False
    return steps1(B)

def pairlt(p, q):
    return p[0] < q[0] or (p[0] == q[0] and p[1] < q[1])
def seqlex(M, N):
    M = list(M); N = list(N)
    i = 0
    while i < len(M) and i < len(N):
        if M[i] != N[i]:
            return pairlt(M[i], N[i])
        i += 1
    # prefix
    if i == len(M): return len(N) > len(M)
    return False

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and len(M) >= 1 and M[0] == (0, 0)]
        md = max(seen.values())
        chk = 0
        no_witness = 0
        bok_B = bok_K = sl_ok = 0
        d_mismatch = 0
        bad = []
        for B0 in hosts:
            B = tuple(B0[1:])      # descendant block
            tB = translate(B)
            if tB == (): continue
            dB = B[0][0] if B else None       # = 1 normally
            sbm = subblock_map(B)
            for x in Gterm(0, tB):
                chk += 1
                Ks = sbm.get(x)
                if not Ks:
                    no_witness += 1
                    if len(bad) < 6: bad.append(('NOWIT', B, x))
                    continue
                # pick the FIRST witness (lean's Gterm_translate_subblock gives one)
                K = Ks[0]
                dK = K[0][0] if K else None
                # we want blockok d both with the SAME d.
                d = dB
                okB = blockok(d, B)
                okK = blockok(d, K) if K else True
                if okB: bok_B += 1
                if okK: bok_K += 1
                if seqlex(K, B): sl_ok += 1
                # the decisive: does olt translate K translate B follow?
                ok_route = okB and okK and (seqlex(K, B) or not K)
                if not ok_route:
                    if len(bad) < 12:
                        bad.append(('ROUTE', B, x, K, 'okB', okB, 'okK', okK,
                                    'sl', seqlex(K, B), 'd', d, 'dK', dK))
        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)} Gterm0-checked={chk}')
        print(f'  no SubBlock witness={no_witness}')
        print(f'  blockok dB on B={bok_B}/{chk}  blockok dB on K={bok_K}/{chk}  seqlex K B={sl_ok}/{chk}')
        for e in bad[:10]:
            if e[0] == 'ROUTE':
                print('  ROUTEFAIL B', mfmt(e[1]), 'x', tfmt(e[2]), 'K', mfmt(e[3]), e[4:])
            else:
                print(' ', e[0], 'B', mfmt(e[1]), 'x', tfmt(e[2]))

if __name__ == '__main__':
    main()
