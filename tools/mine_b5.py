#!/usr/bin/env python3
"""B5' audit: in i1=0 bad blocks, every interior column strictly after
j0+1 has snd = 0:   forall r: j0+1 < r < j1 --> snd(M!r) = 0.
Also B5a: snd(M!(j0+1)) <= Suc(snd(M!j0)) (the bump bound) and
B5b: the i1>0 & d0=0 CT-window class is empty.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from mine_sibm2 import bad_params
from fast_pss import oper, entry

def hosts_plus(extra=2):
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
    HS = hosts_plus(2)
    print('hosts:', len(HS), flush=True)
    n0 = b5_bad = b5a_bad = 0
    n1 = ct1 = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        if i1 == 0:
            n0 += 1
            for r in range(j0+2, j1):
                if M[r][1] != 0:
                    b5_bad += 1
                    if len(ex) < 5: ex.append(('B5', M, j0, j1, r))
                    break
            if j0+1 < j1 and M[j0+1][1] > M[j0][1] + 1:
                b5a_bad += 1
                if len(ex) < 5: ex.append(('B5a', M, j0, j1, j0+1))
        elif d0 == 0:
            n1 += 1
            # CT window premises with i1>0
            L = j1 - j0
            for qa in range(L):
                if not all(entry(M,0,j0+qa) < entry(M,0,j0+q) for q in range(qa+1, L)):
                    continue
                for w in range(qa+1, L):
                    if entry(M,1,j0+w) != entry(M,1,j0+qa) + 1: continue
                    for x in range(w+1, L):
                        if entry(M,0,j0+x) != entry(M,0,j0+w) + 1: continue
                        if not all(entry(M,0,j0+x) <= M[r][0] for r in range(j0+w+1, j0+x)):
                            continue
                        ct1 += 1
                        if len(ex) < 8: ex.append(('CT1', M, j0, j1, (qa,w,x)))
    print(f'i1=0 blocks: {n0}  B5-fail: {b5_bad}  B5a(bump>+1)-fail: {b5a_bad}')
    print(f'i1>0&d0=0 blocks: {n1}  CT-window instances: {ct1}')
    for t in ex:
        print(t[0], 'j0=', t[2], 'j1=', t[3], 'at', t[4], 'M=', ''.join(f'({a},{b})' for a,b in t[1]))

if __name__ == '__main__':
    main()
