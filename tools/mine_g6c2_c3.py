#!/usr/bin/env python3
"""G6 unification test: for ANY dseg window S (exact dseg: pp immediately
before, u = snd pp), any g in Gterm u (NT S) with hdsub g = maxr1 S:
    ole g (NT (msfx S))    (ole = olt or equal)
NO fire premise, NO head-max premise, NO violator premise.
Subsumes E6_lpl (msfx S = S for head-max + size strictness),
E6_dom_tie, E6_dom_deep.
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
    HS = hosts_plus(3)
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
        for j in range(1, L):
            pp = M[j-1]; u = pp[1]
            for kk in range(j + 1, L + 1):
                Sp = M[j:kk]
                if not all(pp[0] < r[0] for r in Sp): break
                Spt = tuple(Sp)
                key = (u, Spt)
                if key in seen: continue
                seen.add(key)
                ntS = NTC(Spt)
                m = max(c[1] for c in Sp)
                ms = NTC(tuple(msfx(list(Sp))))
                for g in set(map(tuple_of, [])) or []:
                    pass
                gs = G(u, ntS)
                done = set()
                for g in gs:
                    gt = tup(g)
                    if gt in done: continue
                    done.add(gt)
                    if not g: continue
                    if hdsub(g) != m: continue
                    tot += 1
                    if not (g == ms or lt_term(g, ms)):
                        viol += 1
                        if len(ex) < 5: ex.append((u, Spt, g))
    print(f'dseg windows: {len(seen)}  max-headed visible g: {tot}  G6 violations: {viol}')
    for u, Sp, g in ex:
        print('VIOL u=', u, 'S=', ''.join(f'({x},{y})' for x, y in Sp))

def tup(t):
    return tuple((p[0], p[1], tup(p[2])) for p in t)

def tuple_of(x):
    return x

if __name__ == '__main__':
    main()
