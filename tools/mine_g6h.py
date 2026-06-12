#!/usr/bin/env python3
"""G6' audit: head-min fbseg windows.
Premise: S = M[j:kk] inside region dominated by pp = M[i] (mid gap allowed),
u = snd pp, AND fst(hd S) <= fst x for all x in S (head row0-minimal).
Claim: g in Gterm u (NT S), hdsub g = maxr1 S ==> ole g (NT (msfx S)).
Both K = takeWhile and T = dropWhile windows inherit this class (with u
switching to snd c for K), so a GCAT-style induction is supported.
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
            a, u = M[i]
            k = i + 1
            while k < L and M[k][0] > a:
                k += 1
            for j in range(i + 1, k):
                h0 = M[j][0]
                for kk in range(j + 1, k + 1):
                    if M[kk-1][0] < h0: break   # head-min violated from here on
                    Spt = tuple(M[j:kk])
                    key = (u, Spt)
                    if key in seen: continue
                    seen.add(key)
                    ntS = NTC(Spt)
                    m = max(c[1] for c in Spt)
                    ms = NTC(tuple(msfx(list(Spt))))
                    done = set()
                    for g in G(u, ntS):
                        gt = repr(g)
                        if gt in done: continue
                        done.add(gt)
                        if not g: continue
                        if hdsub(g) != m: continue
                        tot += 1
                        if not (g == ms or lt_term(g, ms)):
                            viol += 1
                            if len(ex) < 5: ex.append((u, Spt, g))
    print(f'head-min fbseg windows: {len(seen)}  max-headed visible g: {tot}  violations: {viol}')
    for u, Sp, g in ex:
        print('VIOL u=', u, 'S=', ''.join(f'({x},{y})' for x, y in Sp))

if __name__ == '__main__':
    main()
