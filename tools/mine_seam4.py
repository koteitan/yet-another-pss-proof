#!/usr/bin/env python3
"""Test FDIAG candidate: in same-cut both-fire seam config,
fst is non-decreasing along S @ [q]. Also weaker variants:
  FDIAG_T: fst non-decreasing on msfx S @ [q] only (suffix from first max).
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
    n = full_bad = sfx_bad = 0
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
            u = pp[1]
            x = NT(S); x2 = NT(S+[q])
            if proj(u,x)==x or proj(u,x2)==x2: continue
            m = max(c[1] for c in S)
            if q[1] > m: continue
            n += 1
            E = S + [q]
            if not all(E[k][0] <= E[k+1][0] for k in range(len(E)-1)):
                full_bad += 1
                if len(ex) < 5: ex.append(('FULL', M, i, S))
            T = msfx(S) + [q]
            if not all(T[k][0] <= T[k+1][0] for k in range(len(T)-1)):
                sfx_bad += 1
                if len(ex) < 5: ex.append(('SFX', M, i, S))
    print(f'instances: {n}  FDIAG(full S@[q])-fail: {full_bad}  FDIAG_T(msfx@[q])-fail: {sfx_bad}')
    for k, M, i, S in ex:
        print(k, 'i=', i, 'M=', ''.join(f'({a},{b})' for a,b in M))

if __name__ == "__main__":
    main()
