#!/usr/bin/env python3
"""Universal-form audit for the OSC cores GCD/O2 (closure+3, ALL hosts,
no bad-branch context).

GCDU: w < x < om < len M,
  fst(x) = Suc(fst(w)), gap-clear (forall t in (w,x): fst(x) <= fst(t)),
  0 < snd(w),
  dominated-closed window at w: (forall k in (w,om): fst(w) < fst(k)),
  fst(om) <= fst(w)
  ==> snd(x) < snd(w)

O2U: 0 < a, fst(a-1) < fst(a), a < r < om < len M,
  dominated from a: (forall k in (a,om): fst(a) < fst(k)),
  fst(om) <= fst(r),
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
        # GCDU
        for w in range(L):
            if M[w][1] == 0: continue
            fw = M[w][0]
            # find first close om > w with fst <= fst(w); dominance up to om automatic
            om = None
            for k in range(w + 1, L):
                if M[k][0] <= fw:
                    om = k; break
            if om is None: continue
            fx = fw + 1
            for x in range(w + 1, om):
                if M[x][0] != fx: continue
                if not all(fx <= M[t][0] for t in range(w + 1, x)): continue
                gn += 1
                if not M[x][1] < M[w][1]:
                    gbad += 1
                    if len(gex) < 4: gex.append((w, x, om, M))
        # O2U
        for a in range(1, L):
            if not M[a - 1][0] < M[a][0]: continue
            fa = M[a][0]
            # first close past a relative to a: dominance window extent
            ext = L
            for k in range(a + 1, L):
                if M[k][0] <= fa:
                    ext = k; break
            for r in range(a + 1, ext):
                if M[r][1] != M[a][1] + 1: continue
                # need some om in (r, ext] with fst(om) <= fst(r)
                ok_om = None
                for om in range(r + 1, min(ext + 1, L)):
                    if M[om][0] <= M[r][0]:
                        ok_om = om; break
                if ok_om is None: continue
                on += 1
                if not M[a][1] + 1 <= M[a - 1][1]:
                    obad += 1
                    if len(oex) < 4: oex.append((a, r, ok_om, M))
    print(f'GCDU: {gn} instances, {gbad} violations')
    print(f'O2U : {on} instances, {obad} violations')
    for w, x, om, M in gex:
        print('GCDU-fail w=%d x=%d om=%d M=%s' % (w, x, om,
              ''.join('(%d,%d)' % p for p in M)))
    for a, r, om, M in oex:
        print('O2U-fail a=%d r=%d om=%d M=%s' % (a, r, om,
              ''.join('(%d,%d)' % p for p in M)))

if __name__ == '__main__':
    main()
