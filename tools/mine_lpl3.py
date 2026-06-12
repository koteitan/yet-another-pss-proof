#!/usr/bin/env python3
"""E6_lpl audit with the EXACT dseg premise:
pp = M[j-1] immediately precedes S = M[j:kk], all fst(S) > fst(pp), u = snd(pp).
Then head-max S, piece C with pre' != [], head snd = maxr1, visible at u.
Expect 0 violations (matches 続25補4); classify visible instances.
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from wfe_explore import enum_ST
from valnorm import lt_term
from mine_e6 import NT
from mine_proj import G
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

def main():
    HS = hosts_plus(1)
    print('hosts:', len(HS), flush=True)
    ntc = {}
    def NTC(S):
        S = tuple(S)
        if S not in ntc: ntc[S] = NT(list(S))
        return ntc[S]
    seen = set()
    tot = vis = viol = 0
    cls = Counter()
    ex = {}
    for Mt in HS:
        M = list(Mt)
        L = len(M)
        for j in range(1, L):
            pp = M[j-1]; u = pp[1]
            for kk in range(j + 1, L + 1):
                Sp = M[j:kk]
                if not all(pp[0] < r[0] for r in Sp): break
                Spt = tuple(Sp)
                m = max(c[1] for c in Sp)
                if Sp[0][1] != m: continue
                key = (u, Spt)
                if key in seen: continue
                seen.add(key)
                ntS = NTC(Spt)
                gset = G(u, ntS)
                for aa in range(1, len(Sp)):
                    for bb in range(aa + 1, len(Sp) + 1):
                        C = Spt[aa:bb]
                        if C[0][1] != m: continue
                        tot += 1
                        ntC = NTC(C)
                        if ntC not in gset: continue
                        vis += 1
                        tags = []
                        if bb == len(Sp): tags.append('SUFFIX')
                        h0 = Sp[0][0]
                        ke = 1
                        while ke < len(Sp) and Sp[ke][0] > h0:
                            ke += 1
                        if bb <= ke: tags.append('INK')
                        if ntC == ntS: tags.append('EQ')
                        if not lt_term(ntC, ntS):
                            viol += 1
                            tags.append('VIOL')
                        t = tuple(tags)
                        cls[t] += 1
                        if t not in ex:
                            ex[t] = (Spt, aa, bb, u)
    print(f'(u,S) dseg head-max: {len(seen)}  C tests: {tot}  visible: {vis}  violations: {viol}')
    for t, v in sorted(cls.items(), key=lambda kv: -kv[1]):
        print(f'{v:6d}  {"+".join(t) if t else "(plain)"}')
    for t, (Sp, aa, bb, u) in ex.items():
        print('EX', '+'.join(t) if t else '(plain)', 'u=', u,
              'S=', ''.join(f'({x},{y})' for x, y in Sp), f'C=[{aa}:{bb}]')

if __name__ == '__main__':
    main()
