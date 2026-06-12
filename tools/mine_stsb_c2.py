#!/usr/bin/env python3
"""STS_B decomposition mining.
Config: host pre@(p#rest)@[q]@post (q = M[-1] simplification? No: q mid-host
allowed -> q = M[j] for any j; here STS_B has [q]@post so q is the column
right after rest), T = dropWhile (fst p <) rest != [], fst(hd T) = fst p,
fst p <= fst q, all rest >= fst p.
Questions:
 Q1: does q join hd-T's run?  (K1' = takeWhile (fst c1 <) (rest1@[q]) vs K1)
 Q2: for q-not-joining: hdarg(NT(T@[q])) == hdarg(NT T)? (then part2 = part1)
 Q3: class sizes; part2 violations in q-joining class (expect 0).
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from valnorm import lt_term
from mine_e6 import NT
from mine_proj import proj
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

def hdsub(t): return t[0][1] if t else None
def hdarg(t): return t[0][2] if t else None

def main():
    HS = hosts_plus(2)
    print('hosts:', len(HS), flush=True)
    ntc = {}
    def NTC(S):
        S = tuple(S)
        if S not in ntc: ntc[S] = NT(list(S))
        return ntc[S]
    seen = set()
    n = njoin = q2bad = 0
    p1bad = p2bad_join = p2bad_nojoin = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        L = len(M)
        for i in range(L - 1):
            p = M[i]
            for j in range(i + 1, L):
                rest = M[i+1:j]; q = M[j]
                if not all(p[0] <= r[0] for r in rest): continue
                if not p[0] <= q[0]: continue
                ke = 0
                while ke < len(rest) and rest[ke][0] > p[0]:
                    ke += 1
                K = rest[:ke]; T = rest[ke:]
                if not T: continue
                if T[0][0] != p[0]: continue
                key = (tuple(M[i:j+1]),)
                if key in seen: continue
                seen.add(key)
                n += 1
                c1 = T[0]; rest1 = T[1:]
                K1 = []
                for r in rest1:
                    if r[0] > c1[0]: K1.append(r)
                    else: break
                join = (len(K1) == len(rest1)) and q[0] > c1[0]
                ntT = NTC(tuple(T)); ntTq = NTC(tuple(T) + (q,))
                A = proj(p[1], NTC(tuple(K)))
                # part1
                v1 = (p[1] < hdsub(ntT)) or (p[1] == hdsub(ntT) and lt_term(A, hdarg(ntT)))
                if v1: p1bad += 1
                # part2
                v2 = (p[1] < hdsub(ntTq)) or (p[1] == hdsub(ntTq) and lt_term(A, hdarg(ntTq)))
                if join:
                    njoin += 1
                    if v2: p2bad_join += 1
                else:
                    if hdarg(ntTq) != hdarg(ntT):
                        q2bad += 1
                        if len(ex) < 4: ex.append(('Q2', M, i, j))
                    if v2: p2bad_nojoin += 1
    print(f'STS_B-like configs: {n}  q-joins-run: {njoin}')
    print(f'part1-viol: {p1bad}  part2-viol(join): {p2bad_join}  part2-viol(nojoin): {p2bad_nojoin}')
    print(f'nojoin hdarg-changed (Q2): {q2bad}')
    for t in ex:
        print(t[0], 'i=', t[2], 'j=', t[3], 'M=', ''.join(f'({a},{b})' for a,b in t[1]))

if __name__ == '__main__':
    main()
