#!/usr/bin/env python3
"""GCD audit: in i1=0 (d0=0) bad blocks, the gap-clear level+1 child of ANY
interior column strictly drops in row 1:
  forall w in (j0, j1), x in (w, j1):
    fst(M!x) = Suc(fst(M!w)) and (forall t in (w,x): fst(M!x) <= fst(M!t))
    ==> snd(M!x) < snd(M!w)  (when snd(M!w) > 0; report =0 parents too)
Subsumes ginv_CT without any anchor analysis.
"""
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
    n = bad = z = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if i1 != 0: continue
        for w in range(j0 + 1, j1):
            fx = M[w][0] + 1
            for x in range(w + 1, j1):
                if M[x][0] != fx: continue
                if not all(fx <= M[t][0] for t in range(w + 1, x)): continue
                n += 1
                if M[w][1] == 0:
                    z += 1
                    if M[x][1] != 0 and len(ex) < 4:
                        ex.append(('Z', M, w, x))
                elif not M[x][1] < M[w][1]:
                    bad += 1
                    if len(ex) < 4: ex.append(('GCD', M, w, x))
    print(f'gap-clear child pairs: {n}  (zero-snd parents: {z})  GCD-fail: {bad}')
    for t in ex:
        print(t[0], 'w=', t[2], 'x=', t[3], 'M=', ''.join(f'({a},{b})' for a, b in t[1]))

if __name__ == '__main__':
    main()
