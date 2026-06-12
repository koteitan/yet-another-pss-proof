#!/usr/bin/env python3
"""Dump the realized ginv_CT instances (closure+2) to see their shape.

Premises: M in ST_PS closure, bad branch with d0 = 0; anchor qa (last
block index after which row0 strictly climbs); tight parent w
(e1(j0+w) = e1(j0+qa) + 1); child x (Suc e0(j0+w) = e0(j0+x), gap clear).
Conclusion: e1(j0+x) <= e1(j0+qa).
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from mine_sibm2 import bad_params
from fast_pss import oper, entry, Lng

def hosts_plus(extra=2):
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
    HS = hosts_plus(2)
    print('hosts:', len(HS), flush=True)
    n = viol = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if d0 != 0: continue
        L = j1 - j0
        for qa in range(L):
            if not all(entry(M,0,j0+qa) < entry(M,0,j0+q) for q in range(qa+1, L)):
                continue
            for w in range(qa+1, L):
                if entry(M,1,j0+w) != entry(M,1,j0+qa) + 1: continue
                for x in range(w+1, L):
                    if entry(M,0,j0+x) != entry(M,0,j0+w) + 1: continue
                    if not all(entry(M,0,j0+x) <= M[r][0] for r in range(j0+w+1, j0+x)):
                        continue
                    n += 1
                    ok = entry(M,1,j0+x) <= entry(M,1,j0+qa)
                    if not ok: viol += 1
                    if len(ex) < 12:
                        ex.append((M, j0, j1, qa, w, x, ok))
    print(f'CT instances: {n}  violations: {viol}')
    for M, j0, j1, qa, w, x, ok in ex:
        blk = ''.join(f'({a},{b})' for a, b in M[j0:j1])
        print(f'ok={ok} j0={j0} j1={j1} qa={qa} w={w} x={x} blk={blk}')
        print('   M=', ''.join(f'({a},{b})' for a, b in M))

if __name__ == '__main__':
    main()
