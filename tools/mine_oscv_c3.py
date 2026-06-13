#!/usr/bin/env python3
"""Universal nextrel0-window audit for the OSC cores (closure+3, ALL hosts).

GCDV: a < w < x < om < len M,
  parent0 window: fst(a) < fst(om), forall k in (a,om): fst(om) <= fst(k),
  snd(om) = 0,
  0 < snd(w), fst(x) = Suc(fst(w)), gap-clear: forall t in (w,x): fst(x) <= fst(t)
  ==> snd(x) < snd(w)

O2V: 0 < a, a < r < om < len M,
  parent0 window: fst(a) < fst(om), forall k in (a,om): fst(om) <= fst(k),
  snd(om) = 0,
  fst(a-1) < fst(a),
  snd(r) = Suc(snd(a))
  ==> Suc(snd(a)) <= snd(a-1)
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
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
    gn = gbad = on = obad = 0
    gex = []; oex = []
    for Mt in HS:
        M = list(Mt)
        L = len(M)
        for om in range(1, L):
            if M[om][1] != 0: continue
            fom = M[om][0]
            # a = parent0(om): last p < om with fst < fst(om); window auto-dominated
            a = None
            for p in range(om - 1, -1, -1):
                if M[p][0] < fom:
                    a = p; break
            if a is None: continue
            # GCDV pairs inside (a, om)
            for w in range(a + 1, om):
                if M[w][1] == 0: continue
                fx = M[w][0] + 1
                for x in range(w + 1, om):
                    if M[x][0] != fx: continue
                    if not all(fx <= M[t][0] for t in range(w + 1, x)): continue
                    gn += 1
                    if not M[x][1] < M[w][1]:
                        gbad += 1
                        if len(gex) < 6: gex.append((a, w, x, om, M))
            # O2V
            if a > 0 and M[a - 1][0] < M[a][0]:
                for r in range(a + 1, om):
                    if M[r][1] != M[a][1] + 1: continue
                    on += 1
                    if not M[a][1] + 1 <= M[a - 1][1]:
                        obad += 1
                        if len(oex) < 6: oex.append((a, r, om, M))
    print(f'GCDV: {gn} instances, {gbad} violations')
    print(f'O2V : {on} instances, {obad} violations')
    for a, w, x, om, M in gex:
        print('GCDV-fail a=%d w=%d x=%d om=%d M=%s' % (a, w, x, om,
              ''.join('(%d,%d)' % p for p in M)))
    for a, r, om, M in oex:
        print('O2V-fail a=%d r=%d om=%d M=%s' % (a, r, om,
              ''.join('(%d,%d)' % p for p in M)))

if __name__ == '__main__':
    main()
