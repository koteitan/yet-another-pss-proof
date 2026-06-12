#!/usr/bin/env python3
"""G6 u-uniformity test: weak windows (dominator anywhere left, fbseg-like),
visibility at u=0 (superset of every Gterm u). If 0 violations, G6 holds
u-uniformly and the GCAT-style induction can recurse into K and T freely.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from valnorm import lt_term
from mine_e6 import NT
from mine_proj import G
from mine_fire4 import msfx
from fast_pss import oper

def hosts_plus(extra=1):
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=12, rounds=7)
    out = set(tuple(M) for M in ST)
    cur = list(out)
    for _ in range(extra):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t); new.append(t)
        cur = new
    return out

def hdsub(t):
    return t[0][1] if t else None

def main():
    HS = hosts_plus(1)
    print('hosts:', len(HS), flush=True)
    ntc = {}
    def NTC(S):
        S = tuple(S)
        if S not in ntc: ntc[S] = NT(list(S))
        return ntc[S]
    seen = set()
    tot = viol = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        L = len(M)
        for i in range(L - 1):
            a = M[i][0]
            k = i + 1
            while k < L and M[k][0] > a:
                k += 1
            # any contiguous window inside the dominated region (fbseg-like: mid gap allowed)
            for j in range(i + 1, k):
                for kk in range(j + 1, k + 1):
                    Spt = tuple(M[j:kk])
                    if Spt in seen: continue
                    seen.add(Spt)
                    ntS = NTC(Spt)
                    m = max(c[1] for c in Spt)
                    ms = NTC(tuple(msfx(list(Spt))))
                    done = set()
                    for g in G(0, ntS):
                        gt = repr(g)
                        if gt in done: continue
                        done.add(gt)
                        if not g: continue
                        if hdsub(g) != m: continue
                        tot += 1
                        if not (g == ms or lt_term(g, ms)):
                            viol += 1
                            if len(ex) < 5: ex.append((Spt, g))
    print(f'weak windows: {len(seen)}  max-headed g (u=0): {tot}  G6 violations: {viol}')
    for Sp, g in ex:
        print('VIOL S=', ''.join(f'({x},{y})' for x, y in Sp))

if __name__ == '__main__':
    main()
