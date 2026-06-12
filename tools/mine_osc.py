#!/usr/bin/env python3
"""OSC discipline audits on i1=0 (d0=0) bad blocks, closure+2:
O1 : forall r in (j0, j1): snd(M!r) <= Suc(snd(M!j0))
O2 : (0 < j0, fst(M!(j0-1)) < e0(j0), exists bump r with snd = Suc(snd j0))
     ==> snd(M!(j0-1)) >= Suc(snd(M!j0))
O3': bump at r (snd(M!r) = Suc(snd j0)), then any x in (r, j1) with
     fst(M!x) = Suc(fst(M!r)) and gap-clear (forall t in (r,x):
     fst(M!x) <= fst(M!t)) has snd(M!x) <= snd(M!j0)
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
    nb = o1b = 0
    n2 = o2b = 0
    n3 = o3b = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if i1 != 0: continue
        nb += 1
        s0 = M[j0][1]
        bumps = []
        for r in range(j0 + 1, j1):
            if M[r][1] > s0 + 1:
                o1b += 1
                if len(ex) < 4: ex.append(('O1', M, j0, j1, r))
                break
        for r in range(j0 + 1, j1):
            if M[r][1] == s0 + 1:
                bumps.append(r)
        if bumps and j0 > 0 and M[j0-1][0] < M[j0][0]:
            n2 += 1
            if not M[j0-1][1] >= s0 + 1:
                o2b += 1
                if len(ex) < 4: ex.append(('O2', M, j0, j1, bumps[0]))
        for r in bumps:
            fx = M[r][0] + 1
            for x in range(r + 1, j1):
                if M[x][0] != fx: continue
                if not all(fx <= M[t][0] for t in range(r + 1, x)): continue
                n3 += 1
                if not M[x][1] <= s0:
                    o3b += 1
                    if len(ex) < 4: ex.append(('O3', M, j0, j1, (r, x)))
    print(f'i1=0 blocks: {nb}  O1-fail: {o1b}')
    print(f'O2 configs: {n2}  O2-fail: {o2b}')
    print(f'O3 configs: {n3}  O3-fail: {o3b}')
    for t in ex:
        print(t[0], 'j0=', t[2], 'j1=', t[3], 'at', t[4], 'M=', ''.join(f'({a},{b})' for a, b in t[1]))

if __name__ == '__main__':
    main()
