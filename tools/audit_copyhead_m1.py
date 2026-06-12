#!/usr/bin/env python3
"""Closure+1 audit of the EXACT frozen residual statements
seam_copyhead_m1_L2 and seam_copyhead_m1_P (nrmstep.thy).

Context (shared, m = 1): host M in ST_PS closure+1 with bad-branch
parameters (j0, j1, i1, d0); Y = take j0 M @ cp 0 (one copy laid down,
shift 0 = M[:j1]); sibm2 Y; adjacent tie pair (a, b) in Y with b = j0;
ob: everything after b in Y is above the tie level; high:
fst(Y!b) < e0(j0) + 1*d0; the run is open: mrun Y a = drop (Suc b) Y @ D
with D != [].

Residual statements audited (all expected EMPTY at closure+1):
  _P     : D = M!j1 # D', D' != []          (any L)
  _E2var : Suc j0 < j1, D = [M!j1], some x in blktail with x != M!j1
  _F2L2  : Suc j0 < j1, fst(M!j1) < fst(hd D), snd(M!j1) = snd(hd D)

(seam_copyhead_m1_L2 itself is now PROVEN for: E-const blktail, F1
divergence; closure+1 found 18 L2 instances, all E-const — the proven
class.)  Also counts realized instances by class as a cross-check.
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from fast_pss import oper, fmt, Lng, entry
from wfe_explore import enum_ST
from mine_sibm2 import bad_params, mrun_stop


def mrun(X, a):
    la = X[a][0]
    K = []
    for c in range(a + 1, len(X)):
        if X[c][0] > la:
            K.append(X[c])
        else:
            break
    return K


def maxr1(S):
    return max(c[1] for c in S)


def sibrel(K, K1):
    if K1 == K:
        return True
    if len(K) > len(K1) and K[:len(K1)] == K1:
        return True
    t = 0
    while t < len(K) and t < len(K1) and K[t] == K1[t]:
        t += 1
    if t < len(K) and t < len(K1):
        x, x1 = K[t], K1[t]
        if K[0][1] == maxr1(K) and K1[0][1] == maxr1(K1):
            if (x1[0] == x[0] and x1[1] < x[1]) or (x1[0] < x[0] and x1[1] == x[1]):
                return True
        # branch 4: end-position snd-drop, no head-max
        if t == len(K) - 1 and x1[0] == x[0] and x1[1] < x[1]:
            return True
    return False


def sibm2(X):
    for a in range(len(X)):
        if X[a][0] <= 0:
            continue
        b = a + 1 + len(mrun(X, a))
        if b >= len(X):
            continue
        if X[b][0] != X[a][0] or X[b][1] != X[a][1]:
            continue
        if not sibrel(mrun(X, a), mrun(X, b)):
            return False
    return True


def hosts_plus1():
    ST = enum_ST(seed_max_v=4, oper_ns=(1, 2, 3, 4), max_len=13, rounds=7)
    out = set(ST)
    for M in ST:
        if len(M) < 2:
            continue
        for n in (1, 2, 3, 4):
            out.add(tuple(oper(list(M), n)))
    return out


def main():
    HS = hosts_plus1()
    print('hosts:', len(HS), flush=True)
    cnt = Counter()
    bad_P = bad_E2var = bad_F2L2 = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None:
            continue
        j0, j1, i1, d0 = bp
        m = 1
        cp0 = [(entry(M, 0, j), entry(M, 1, j)) for j in range(j0, j1)]
        Y = M[:j0] + cp0          # = M[:j1]
        if not sibm2(Y):
            continue
        b = j0
        if b >= len(Y):
            continue
        for a in range(len(Y)):
            if Y[a][0] <= 0:
                continue
            K = mrun(Y, a)
            if a + 1 + len(K) != b:
                continue
            if Y[b][0] != Y[a][0] or Y[b][1] != Y[a][1]:
                continue
            if not all(Y[b][0] < x[0] for x in Y[b + 1:]):
                continue
            if not Y[b][0] < entry(M, 0, j0) + m * d0:
                continue
            tail = Y[b + 1:]
            if not (len(K) > len(tail) and K[:len(tail)] == tail):
                continue              # run not open (D = [] or mismatch)
            D = K[len(tail):]
            assert D
            cj1 = (entry(M, 0, j1), entry(M, 1, j1))
            blktail = [(entry(M, 0, j), entry(M, 1, j)) for j in range(j0 + 1, j1)]
            L2 = j0 + 1 < j1
            # exact frozen residual classes
            if D[0] == cj1 and len(D) >= 2:
                cnt['P'] += 1
                bad_P += 1
                if len(ex) < 6:
                    ex.append(('P', M, a, b, K))
            elif L2 and D == [cj1] and any(x != cj1 for x in blktail):
                cnt['E2var'] += 1
                bad_E2var += 1
                if len(ex) < 6:
                    ex.append(('E2var', M, a, b, K))
            elif D[0] != cj1 and cj1[0] < D[0][0] and cj1[1] == D[0][1]:
                cnt['F2' + ('L2' if L2 else 'L1')] += 1
                if L2:
                    bad_F2L2 += 1
                    if len(ex) < 6:
                        ex.append(('F2L2', M, a, b, K))
            elif D == [cj1]:
                cnt['E-const' if all(x == cj1 for x in blktail) else 'E?'] += 1
            else:
                cnt['F1/other'] += 1
    print('instance classes:', dict(cnt))
    print('seam_copyhead_m1_P     violations-of-emptiness:', bad_P)
    print('seam_copyhead_m1_E2var violations-of-emptiness:', bad_E2var)
    print('seam_copyhead_m1_F2L2  violations-of-emptiness:', bad_F2L2)
    for e in ex:
        tag, M, a, b, K = e
        print(tag, fmt(M), 'a=', a, 'b=', b, 'K=', K)


if __name__ == '__main__':
    main()
