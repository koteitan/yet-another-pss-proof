#!/usr/bin/env python3
"""PFMIN test: for ANY segment S = M[i+1:j] of a closure+1 host with
all fst(S) > fst(M[i]) and pfire(u=M[i].snd, NT S):
  INV2: hd(msfx S) is fst-min of msfx S.
Also INV-next: if j < len(M) and snd(M[j]) <= maxr1 S and fst(M[i]) < fst(M[j]):
  fst(hd(msfx S)) <= fst(M[j]).
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
    n = n2 = inv2_bad = inv_bad = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        for i in range(len(M)):
            pp = M[i]; u = pp[1]
            for j in range(i+2, len(M)+1):
                S = M[i+1:j]
                if not all(pp[0] < r[0] for r in S): break
                x = NT(S)
                if proj(u, x) == x: continue
                n += 1
                T = msfx(S)
                if not all(T[0][0] <= c[0] for c in T):
                    inv2_bad += 1
                    if len(ex) < 5: ex.append(('INV2', M, i, j, S, T))
                if j < len(M):
                    qq = M[j]
                    if qq[1] <= max(c[1] for c in S) and pp[0] < qq[0]:
                        n2 += 1
                        if not T[0][0] <= qq[0]:
                            inv_bad += 1
                            if len(ex) < 5: ex.append(('INV', M, i, j, S, T))
    print(f'fire segments: {n}  INV2-fail: {inv2_bad}')
    print(f'same-cut next:  {n2}  INV-fail: {inv_bad}')
    for k, M, i, j, S, T in ex:
        print(k, 'i=', i, 'j=', j, 'M=', ''.join(f'({a},{b})' for a,b in M))
        print('   S=', ''.join(f'({a},{b})' for a,b in S), ' T=', ''.join(f'({a},{b})' for a,b in T))

if __name__ == '__main__':
    main()
