#!/usr/bin/env python3
"""GCD1' audit (+3): i1=1 bad block, snd(j0)=0, block fst-dominated
(forall j in (j0,j1): fst(j) >= fst(j1)), w,x gap-clear level+1 pair,
snd(w)>0 ==> snd(x) < snd(w)."""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from mine_sibm2 import bad_params
from fast_pss import oper

def hosts_plus(extra=3):
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
    n = bad = 0; ex = []
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if i1 != 1: continue
        if M[j0][1] != 0: continue
        if not all(M[j][0] >= M[j1][0] for j in range(j0 + 1, j1)): continue
        for w in range(j0 + 1, j1):
            if M[w][1] == 0: continue
            fx = M[w][0] + 1
            for x in range(w + 1, j1):
                if M[x][0] != fx: continue
                if not all(fx <= M[t][0] for t in range(w + 1, x)): continue
                n += 1
                if not M[x][1] < M[w][1]:
                    bad += 1
                    if len(ex) < 6: ex.append((j0, j1, w, x, M))
    print(f"GCD1': {n} pairs, {bad} violations")
    for j0, j1, w, x, M in ex:
        print("GCD1'-fail j0=%d j1=%d w=%d x=%d M=%s" % (j0, j1, w, x,
              ''.join('(%d,%d)' % p for p in M)))

if __name__ == '__main__':
    main()
