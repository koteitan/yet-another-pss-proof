#!/usr/bin/env python3
"""E6_memT premise minimization (exact dseg windows, closure+1).
Frozen form: dseg u (c0#rest), fire(whole), T != [], maxr1(c0#K) < maxr1(c0#rest)
  ==> C1: NT(msfx T) in Gterm u (NT T)
      C2: not olt (NT(msfx T)) (NT (c0#rest))
Variants: P0 = without the fire premise; P1 = with fire.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from valnorm import lt_term
from mine_e6 import NT
from mine_proj import G, proj
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

def main():
    HS = hosts_plus(1)
    print('hosts:', len(HS), flush=True)
    ntc = {}
    def NTC(S):
        S = tuple(S)
        if S not in ntc: ntc[S] = NT(list(S))
        return ntc[S]
    seen = set()
    st = {'P0': [0,0,0], 'P1': [0,0,0]}  # n, C1bad, C2bad
    ex = []
    for Mt in HS:
        M = list(Mt)
        L = len(M)
        for j in range(1, L):
            pp = M[j-1]; u = pp[1]
            for kk in range(j + 1, L + 1):
                S = M[j:kk]
                if not all(pp[0] < r[0] for r in S): break
                key = (u, tuple(S))
                if key in seen: continue
                seen.add(key)
                c0 = S[0]; rest = S[1:]
                ke = 0
                while ke < len(rest) and rest[ke][0] > c0[0]:
                    ke += 1
                K = rest[:ke]; T = rest[ke:]
                if not T: continue
                mw = max(c[1] for c in S)
                mk = max([c0[1]] + [c[1] for c in K])
                if not mk < mw: continue
                ntW = NTC(tuple(S)); ntT = NTC(tuple(T))
                msT = NTC(tuple(msfx(list(T))))
                c1 = msT in G(u, ntT)
                c2 = not lt_term(msT, ntW)
                fire = proj(u, ntW) != ntW
                for k, cond in (('P0', True), ('P1', fire)):
                    if cond:
                        st[k][0] += 1
                        if not c1: st[k][1] += 1
                        if not c2: st[k][2] += 1
                if (not c1 or not c2) and not fire and len(ex) < 5:
                    ex.append((u, S, c1, c2))
    for k in ('P0','P1'):
        print(f'{k}: n={st[k][0]}  C1(membership)-fail={st[k][1]}  C2(viol-vs-whole)-fail={st[k][2]}')
    for u, S, c1, c2 in ex:
        print('nofire-fail', f'c1={c1} c2={c2}', 'u=', u, 'S=', ''.join(f'({a},{b})' for a,b in S))

if __name__ == '__main__':
    main()
