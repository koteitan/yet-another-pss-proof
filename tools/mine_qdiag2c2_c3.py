#!/usr/bin/env python3
"""QDIAG premise minimization. Config: segprov u S q (exact: pp adjacent,
S = M[i+1:j], q = M[j]), S nonempty, q-cut (maxr1 S < snd q).
Premise variants:
  P0: q-cut only
  P1: q-cut + fire(S)
  P2: q-cut + fire(S@[q])
  P3: q-cut + both fire (frozen form)
Claim: snd strictly increasing along S.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from mine_proj import proj
from mine_e6 import NT
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
    HS = hosts_plus(3)
    print('hosts:', len(HS), flush=True)
    st = {k: [0,0] for k in ('P0','P1','P2','P3')}
    ex = {}
    for Mt in HS:
        M = list(Mt)
        L = len(M)
        for i in range(L - 1):
            pp = M[i]; u = pp[1]
            for j in range(i + 2, L):
                S = M[i+1:j]; q = M[j]
                if not all(pp[0] < r[0] for r in S): break
                if not pp[0] < q[0]: continue
                if not max(c[1] for c in S) < q[1]: continue
                inc = all(S[t][1] < S[t+1][1] for t in range(len(S)-1))
                x = NT(S); x2 = NT(S + [q])
                fS = proj(u, x) != x
                fSq = proj(u, x2) != x2
                for k, c in (('P0', True), ('P1', fS), ('P2', fSq), ('P3', fS and fSq)):
                    if c:
                        st[k][0] += 1
                        if not inc:
                            st[k][1] += 1
                            if k not in ex: ex[k] = (M, i, j)
    for k in ('P0','P1','P2','P3'):
        print(f'{k}: n={st[k][0]}  non-increasing-fail={st[k][1]}')
    for k, (M, i, j) in ex.items():
        print(k, 'i=', i, 'j=', j, 'M=', ''.join(f'({a},{b})' for a, b in M))

if __name__ == '__main__':
    main()
