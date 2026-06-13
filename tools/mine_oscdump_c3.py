#!/usr/bin/env python3
"""Dump ALL realized GCD (and summarize O2) bad-block instances at closure+3,
with full context: block bounds, values, run structure."""
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
    gcd_inst = []
    o2_sig = {}
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if i1 != 0: continue
        # GCD instances
        for w in range(j0 + 1, j1):
            if M[w][1] == 0: continue
            fx = M[w][0] + 1
            for x in range(w + 1, j1):
                if M[x][0] != fx: continue
                if not all(fx <= M[t][0] for t in range(w + 1, x)): continue
                gcd_inst.append((tuple(M), j0, j1, w, x))
        # O2 instances (signature collapse)
        if j0 > 0 and M[j0 - 1][0] < M[j0][0]:
            for r in range(j0 + 1, j1):
                if M[r][1] == M[j0][1] + 1:
                    sig = (M[j0 - 1], M[j0], M[r], r - j0, j1 - j0,
                           M[j0][1] + 1 <= M[j0 - 1][1])
                    o2_sig[sig] = o2_sig.get(sig, 0) + 1
    print('GCD instances:', len(gcd_inst))
    for Mt, j0, j1, w, x in gcd_inst:
        s = ''.join(('[' if j == j0 else '') + ('<w>' if j == w else '') +
                    ('<x>' if j == x else '') + '(%d,%d)' % p +
                    (']' if j == j1 else '')
                    for j, p in enumerate(Mt))
        print('  j0=%d j1=%d w=%d x=%d  %s' % (j0, j1, w, x, s))
    print('O2 signatures (pred, head, r-col, r-j0, blocklen, concl):',
          len(o2_sig))
    for sig, c in sorted(o2_sig.items()):
        print('  %s x%d' % (sig, c))

if __name__ == '__main__':
    main()
