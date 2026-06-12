#!/usr/bin/env python3
"""UCT universal-window form of ginv_CT:
ANY M in ST_PS closure, indices a < w < x < om <= len(M)-1... om < len(M):
  dom : forall k in (a, om): fst(M!a) < fst(M!k)
  stop: fst(M!om) <= fst(M!a)
  tight: snd(M!w) = Suc(snd(M!a))
  child: fst(M!x) = Suc(fst(M!w)) and forall r in (w,x): fst(M!x) <= fst(M!r)
  ==> snd(M!x) <= snd(M!a)
(btfullok window + tight-node refinement; CT = instance with a=j0+qa, om=j1.)
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
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
    n = viol = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        L = len(M)
        for a in range(L):
            fa, sa = M[a]
            om = a + 1
            while om < L and M[om][0] > fa:
                om += 1
            if om >= L: continue   # no stop
            for w in range(a + 1, om):
                if M[w][1] != sa + 1: continue
                fx_target = M[w][0] + 1
                for x in range(w + 1, om):
                    if M[x][0] != fx_target: continue
                    if not all(fx_target <= M[r][0] for r in range(w + 1, x)):
                        continue
                    n += 1
                    if not M[x][1] <= sa:
                        viol += 1
                        if len(ex) < 6: ex.append((M, a, w, x, om))
    print(f'UCT instances: {n}  violations: {viol}')
    for M, a, w, x, om in ex:
        print(f'VIOL a={a} w={w} x={x} om={om} M=', ''.join(f'({p},{q})' for p, q in M))

if __name__ == '__main__':
    main()
