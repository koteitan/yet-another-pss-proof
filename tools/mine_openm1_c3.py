#!/usr/bin/env python3
"""seam_open_m1 instance classification (closure+1):
config: bad branch, m=1, Y = M[:j0] + block(shift 0) = M[:j1], sibm2 Y,
tie pair (a,b) with b < j0, everything after b above tie level,
fst(Y!b) < e0(j0) + d0, OPEN: mrun Y a = drop(Suc b) Y @ D, D != [].
Classify: D vs next block B = [(e0(j)+d0, e1(j)) for j in [j0..j1)]:
  EQ: D == B ; PRE: D is proper prefix of B ; BPRE: B is proper prefix of D;
  sibrel branch of the CONCLUSION K vs drop(Suc b)Y @ B.
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
sys.path.insert(0, '.')
from audit_copyhead_m1 import mrun, sibm2, sibrel
from mine_sibm2 import bad_params
from fast_pss import oper, entry
from wfe_explore import enum_ST

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
    HS = hosts_plus(1)
    print('hosts:', len(HS), flush=True)
    n = 0
    cls = Counter()
    ex = []
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        m = 1
        Y = M[:j0] + [(entry(M,0,j), entry(M,1,j)) for j in range(j0, j1)]
        if not sibm2(Y): continue
        B = [(entry(M,0,j) + m*d0, entry(M,1,j)) for j in range(j0, j1)]
        for a in range(len(Y)):
            if Y[a][0] <= 0: continue
            K = mrun(Y, a)
            b = a + 1 + len(K)
            if b >= len(Y): continue
            if Y[b] != Y[a]: continue
            if not all(Y[b][0] < x[0] for x in Y[b+1:]): continue
            if not Y[b][0] < entry(M,0,j0) + m*d0: continue
            if b >= j0: continue
            tail = Y[b+1:]
            if not (len(K) > len(tail) and K[:len(tail)] == tail): continue
            D = K[len(tail):]
            if not D: continue
            n += 1
            if D == B: dc = 'D=B'
            elif len(D) < len(B) and B[:len(D)] == D: dc = 'D<B'
            elif len(D) > len(B) and D[:len(B)] == B: dc = 'D>B'
            else: dc = 'DIFF'
            K1 = tail + B
            sr = sibrel(K, K1)
            cls[(dc, sr)] += 1
            if (dc, sr) not in ex or len(ex) < 8:
                ex.append((dc, sr, M, a, b, D, B))
    print('open_m1 instances:', n)
    for k, v in cls.items():
        print(f'{v:4d}  D-class={k[0]}  sibrel-holds={k[1]}')
    for dc, sr, M, a, b, D, B in ex[:6]:
        print(dc, sr, 'a=', a, 'b=', b, 'D=', D, 'B=', B)
        print('   M=', ''.join(f'({x},{y})' for x, y in M))

if __name__ == '__main__':
    main()
