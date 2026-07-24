#!/usr/bin/env python3
"""Structure probe for AscArgDom (the single residual of PSS cofinality).

For every ST_PS host M with the ascending bad decomposition at oper's TRUE root
(so the nextrel1 clause holds), and every ST_PS N sharing the prefix G++blk++[q],
record where the comparison  S_hi  vs  shiftr0 d0 (R ++ copies d0 blk' m)  is
decided.
"""
import sys, collections
sys.path.insert(0, '.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import pairlt, seqlex, sle, shiftr0, copies
from fast_pss import idx1, hasParent1, parent1, hasParent0, parent0, entry as fentry, Lng, fmt

def true_root(M):
    j1 = len(M)-1
    if j1 <= 0: return None
    i1 = idx1(M, j1)
    if i1 == 1:
        return parent1(M, j1) if hasParent1(M, j1) else None
    return parent0(M, j1) if hasParent0(M, j1) else None

def instances(rounds, ml, vmax, ns):
    hosts = [tuple(M) for M in enum_depth(vmax, ns, ml, rounds) if len(M) >= 2 and M[0] == (0,0)]
    hosts = sorted(set(hosts))
    # index hosts by prefix for speed
    for M in hosts:
        Ml = list(M); j1 = len(Ml)-1
        lp = Ml[j1]
        j0 = true_root(Ml)
        if j0 is None: continue
        G = Ml[:j0]; blk = Ml[j0:j1]
        if not blk: continue
        v0, w0 = blk[0]; R = blk[1:]
        if not all(v0 < x[0] for x in R): continue
        d0 = lp[0] - v0
        if d0 <= 0: continue
        if lp[1] != w0 + 1: continue
        pref = G + blk; P = len(pref)
        qh = (v0+d0, w0); blkp = shiftr0(d0, blk)
        for N in hosts:
            Nl = list(N)
            if len(Nl) <= P or Nl[:P] != pref: continue
            if Nl[P] != qh: continue
            S = Nl[P+1:]
            Shi = []
            for p in S:
                if v0+d0 < p[0]: Shi.append(p)
                else: break
            yield dict(M=M, N=N, G=G, blk=blk, R=R, S=S, Shi=Shi, v0=v0, w0=w0, d0=d0, lp=lp, blkp=blkp)

def bound(inst, m):
    return shiftr0(inst['d0'], list(inst['R']) + copies(inst['d0'], inst['blkp'], m))

def firstdiff(A, B):
    i = 0
    while i < len(A) and i < len(B) and A[i] == B[i]:
        i += 1
    return i

def main():
    rounds, ml, vmax = 8, 11, 5
    ns = (1,2,3,4,5)
    tot = 0; viol_exp = 0; viol_expl = 0
    stats = collections.Counter()
    exs = []
    for inst in instances(rounds, ml, vmax, ns):
        tot += 1
        Shi = inst['Shi']; m = len(Shi)
        okE = sle(Shi, bound(inst, m))
        if not okE:
            viol_expl += 1
        # existential: try m up to 2*len+3
        oke = any(sle(Shi, bound(inst, mm)) for mm in range(0, 2*len(Shi)+4))
        if not oke:
            viol_exp += 1
            if len(exs) < 5: exs.append(inst)
        # where is it decided?
        B = bound(inst, m)
        i = firstdiff(Shi, B)
        if i >= len(Shi):
            stats['prefix(Shi ends)'] += 1
        elif i >= len(B):
            stats['BOUND ends first (BAD)'] += 1
        else:
            a, b = Shi[i], B[i]
            if a[0] < b[0]: kind = 'row0-drop'
            elif a[0] == b[0] and a[1] < b[1]: kind = 'row1-drop'
            else: kind = 'OVERSHOOT'
            # inside shiftr0 d0 R or beyond?
            zone = 'inR' if i < len(inst['R']) else 'inCopies'
            stats[f'{kind}@{zone}'] += 1
        if len(Shi) == 0: stats['Shi empty'] += 1
        if len(inst['R']) == 0: stats['R empty'] += 1
    print(f"instances={tot}  explicit-viol={viol_expl}  existential-viol={viol_exp}")
    for k, v in sorted(stats.items()): print(f"   {k}: {v}")
    for e in exs:
        print("VIOL", fmt(e['M']), '|', fmt(e['N']), 'v0,w0,d0=', e['v0'], e['w0'], e['d0'])

main()
