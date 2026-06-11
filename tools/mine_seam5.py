#!/usr/bin/env python3
"""Premise-minimization for E6_seam conclusions.
Configs (same-cut window, segprov shape):
  A: fire(S) only
  B: fire(S@[q]) only
  C: both (current frozen form)
For each: count INV-fail (fst hd msfx <= fst q) and INV2-fail (hd fst-min).
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from mine_proj import proj
from mine_e6 import NT
from mine_fire4 import msfx
from fast_pss import oper

def hosts_plus(extra=1):
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
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
    stats = {k: [0,0,0] for k in 'ABC'}  # n, inv_bad, inv2_bad
    ex = []
    for Mt in HS:
        M = list(Mt)
        if len(M) < 2: continue
        q = M[-1]
        for i in range(len(M)-1):
            pp = M[i]; S = list(M[i+1:-1])
            if not S: continue
            if not all(pp[0] < r[0] for r in S): continue
            if not pp[0] < q[0]: continue
            m = max(c[1] for c in S)
            if q[1] > m: continue
            u = pp[1]
            x = NT(S); x2 = NT(S+[q])
            fS = proj(u,x) != x
            fSq = proj(u,x2) != x2
            T = msfx(S)
            inv = T[0][0] <= q[0]
            inv2 = all(T[0][0] <= c[0] for c in T)
            for k, cond in (('A', fS), ('B', fSq), ('C', fS and fSq)):
                if cond:
                    stats[k][0] += 1
                    if not inv: stats[k][1] += 1
                    if not inv2: stats[k][2] += 1
            if fS and not fSq and (not inv or not inv2) and len(ex) < 4:
                ex.append(('A-only', M, i, S, T))
            if fSq and not fS and (not inv or not inv2) and len(ex) < 4:
                ex.append(('B-only', M, i, S, T))
    for k in 'ABC':
        n, ib, i2b = stats[k]
        print(f'{k}: n={n}  INV-fail={ib}  INV2-fail={i2b}')
    for k, M, i, S, T in ex:
        print(k, 'i=', i, 'M=', ''.join(f'({a},{b})' for a,b in M))
        print('   T=', ''.join(f'({a},{b})' for a,b in T))

if __name__ == '__main__':
    main()
