#!/usr/bin/env python3
"""ginv_BTWRAP_T3 class split: premises = bad branch (any d0), anchor qa with
e1(j0+qa) = e1(j0) (tau=0), strict dom after qa, head-tie
e1(j0+Suc qa) = e1(j0+qa). Split instances by i1; check e0c for i1=0.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from mine_sibm2 import bad_params
from fast_pss import oper, entry

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
    n0 = n1 = v = e0c_bad = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        L = j1 - j0
        for qa in range(L):
            if entry(M,1,j0+qa) != entry(M,1,j0): continue
            if not all(entry(M,0,j0+qa) < entry(M,0,j0+q) for q in range(qa+1, L)):
                continue
            if qa + 1 >= L: continue
            if entry(M,1,j0+qa+1) != entry(M,1,j0+qa): continue
            for q in range(qa+1, L):
                if i1 == 0:
                    n0 += 1
                    if not entry(M,0,j0) <= entry(M,0,j0+qa):
                        e0c_bad += 1
                else:
                    n1 += 1
                    if not entry(M,1,j0+q) <= entry(M,1,j0+qa):
                        v += 1
                        if len(ex) < 4: ex.append((M, j0, j1, qa, q))
    print(f'i1=0 instances: {n0} (e0c fails: {e0c_bad})   i1=1 instances: {n1}  i1=1 violations: {v}')
    for M, j0, j1, qa, q in ex:
        print('VIOL j0=', j0, 'qa=', qa, 'q=', q, 'M=', ''.join(f'({a},{b})' for a,b in M))

if __name__ == '__main__':
    main()
