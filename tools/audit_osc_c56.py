#!/usr/bin/env python3
"""Deep audit (+extra closure) of the LAST-ANCHORED OSC cores:
GCD (i1=0 bad block), O2 (original form), O1P (positive-head interior bound).
Usage: audit_osc_c56.py [extra]"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from mine_sibm2 import bad_params
from fast_pss import oper

def hosts_plus(extra):
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(tuple(M) for M in ST)
    cur = list(out)
    for i in range(extra):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t); new.append(t)
        cur = new
        print('level +%d: +%d hosts (total %d)' % (i+1, len(new), len(out)),
              flush=True)
    return out

def main():
    extra = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    HS = hosts_plus(extra)
    print('hosts:', len(HS), flush=True)
    gn = gb = on = ob = pn = pb = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if i1 != 0: continue
        # GCD
        for w in range(j0 + 1, j1):
            if M[w][1] == 0: continue
            fx = M[w][0] + 1
            for x in range(w + 1, j1):
                if M[x][0] != fx: continue
                if not all(fx <= M[t][0] for t in range(w + 1, x)): continue
                gn += 1
                if not M[x][1] < M[w][1]:
                    gb += 1
                    if len(ex) < 8: ex.append(('GCD', j0, j1, w, x, M))
        # O2
        if j0 > 0 and M[j0 - 1][0] < M[j0][0]:
            for r in range(j0 + 1, j1):
                if M[r][1] == M[j0][1] + 1:
                    on += 1
                    if not M[j0][1] + 1 <= M[j0 - 1][1]:
                        ob += 1
                        if len(ex) < 8: ex.append(('O2', j0, j1, r, r, M))
        # O1P
        if M[j0][1] > 0:
            pn += 1
            for l in range(j0 + 1, j1):
                if M[l][1] > M[j0][1]:
                    pb += 1
                    if len(ex) < 8: ex.append(('O1P', j0, j1, l, l, M))
                    break
    print(f'GCD: {gn} pairs, {gb} violations')
    print(f'O2 : {on} instances, {ob} violations')
    print(f'O1P: {pn} blocks, {pb} violations')
    for t, j0, j1, a, b, M in ex:
        print('%s-fail j0=%d j1=%d a=%d b=%d M=%s' % (t, j0, j1, a, b,
              ''.join('(%d,%d)' % p for p in M)))

if __name__ == '__main__':
    main()
