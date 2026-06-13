#!/usr/bin/env python3
"""O2V' audit (snd(a)=0 added) + realized bad-block O2 head-snd census."""
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
    on = obad = 0; oex = []
    pos_head = 0; pos_ex = []
    for Mt in HS:
        M = list(Mt); L = len(M)
        # O2V' universal
        for om in range(1, L):
            if M[om][1] != 0: continue
            fom = M[om][0]
            a = None
            for p in range(om - 1, -1, -1):
                if M[p][0] < fom:
                    a = p; break
            if a is None or a == 0: continue
            if M[a][1] != 0: continue          # NEW: snd(a) = 0
            if not M[a - 1][0] < M[a][0]: continue
            for r in range(a + 1, om):
                if M[r][1] != M[a][1] + 1: continue
                on += 1
                if not M[a][1] + 1 <= M[a - 1][1]:
                    obad += 1
                    if len(oex) < 6: oex.append((a, r, om, M))
        # realized bad-block O2 with snd(j0) > 0?
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if i1 != 0: continue
        if j0 > 0 and M[j0 - 1][0] < M[j0][0] and M[j0][1] > 0:
            for r in range(j0 + 1, j1):
                if M[r][1] == M[j0][1] + 1:
                    pos_head += 1
                    if len(pos_ex) < 4: pos_ex.append((j0, r, j1, M))
    print(f"O2V': {on} instances, {obad} violations")
    print(f'bad-block O2 with snd(j0)>0: {pos_head}')
    for a, r, om, M in oex:
        print("O2V'-fail a=%d r=%d om=%d M=%s" % (a, r, om,
              ''.join('(%d,%d)' % p for p in M)))
    for j0, r, j1, M in pos_ex:
        print('poshead j0=%d r=%d j1=%d M=%s' % (j0, r, j1,
              ''.join('(%d,%d)' % p for p in M)))

if __name__ == '__main__':
    main()
