#!/usr/bin/env python3
"""Mine projE_ii / projE_iii: the max-violator correspondence on segprov pairs.

segprov u S q: pre @ (pp # S) @ [q] in ST_PS, all of S dominated by pp,
fst pp < fst q, u = snd pp.  x = nrm(tr S), x' = nrm(tr (S@[q])).

Questions (both-fire case, projE_ii):
  Q1: classification of (mx, mx') where m* = max violator: eq / einc / eflip / other
  Q2: does any violator of x' fail to be (partner of violator of x) or Z?
  Q3: overtaking: is mx' always the partner of mx (not of a smaller violator)?
Only-extended-fires case (projE_iii):
  Q4: classification of (x, mx'): einc/eflip/other  (goal: Einc x (proj u x'))
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj

def canon(t):
    return tuple(('D', v, canon(b)) for _, v, b in t)

def trans(C):
    return canon(nrm(conv(translate(list(C)))))

def is_leaf(t):
    return len(t) == 1 and not t[0][2]

def einc(x, y):
    x, y = canon(x), canon(y)
    if not x:
        return is_leaf(y)
    if not y:
        return False
    if x[0] == y[0] and einc(x[1:], y[1:]):
        return True
    if len(x) == 1 and len(y) == 1 and x[0][1] == y[0][1] and einc(x[0][2], y[0][2]):
        return True
    return False

def eflip(x, y):
    x, y = canon(x), canon(y)
    if not x or not y:
        return False
    if is_leaf(x) and is_leaf(y) and x[0][1] < y[0][1]:
        return True
    if x[0] == y[0] and eflip(x[1:], y[1:]):
        return True
    if len(x) == 1 and len(y) == 1 and x[0][1] == y[0][1] and eflip(x[0][2], y[0][2]):
        return True
    return False

def viols(u, b):
    return [canon(g) for g in G(u, b) if not lt_term(g, b)]

def maxv(vs):
    m = vs[0]
    for h in vs[1:]:
        if lt_term(m, h):
            m = h
    return m

def rel(a, b):
    if a == b: return 'eq'
    if einc(a, b): return 'einc'
    if eflip(a, b): return 'eflip'
    return 'other'

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    npos = nboth = next_only = 0
    q1 = {}; q4 = {}
    q2bad = 0; q3bad = 0
    ex = {'q1other': [], 'q1eq': [], 'q4other': [], 'q2': [], 'q3': []}
    for M in ST:
        if len(M) < 2: continue
        q = M[-1]
        for i in range(len(M)-1):
            pp = M[i]; S = list(M[i+1:-1])
            if not all(pp[0] < r[0] for r in S): continue
            if not pp[0] < q[0]: continue
            u = pp[1]
            npos += 1
            x = trans(S); x2 = trans(S+[q])
            vx = viols(u, x); vx2 = viols(u, x2)
            fx, fx2 = bool(vx), bool(vx2)
            if fx and fx2:
                nboth += 1
                mx, mx2 = maxv(vx), maxv(vx2)
                r = rel(mx, mx2)
                q1[r] = q1.get(r, 0) + 1
                if r == 'other' and len(ex['q1other']) < 5:
                    ex['q1other'].append((M, i, mx, mx2))
                if r == 'eq' and len(ex['q1eq']) < 5:
                    ex['q1eq'].append((M, i, mx, mx2))
                # Q2: every violator of x' is partner/eq of some violator of x, or Z
                for g2 in set(vx2):
                    if g2 == ():
                        continue
                    if not any(g2 == g or einc(g, g2) or eflip(g, g2) for g in vx):
                        q2bad += 1
                        if len(ex['q2']) < 5: ex['q2'].append((M, i, g2))
                # Q3: mx' is partner/eq of mx specifically
                if not (mx2 == mx or einc(mx, mx2) or eflip(mx, mx2)):
                    q3bad += 1
                    if len(ex['q3']) < 5: ex['q3'].append((M, i, mx, mx2))
            elif (not fx) and fx2:
                next_only += 1
                mx2 = maxv(vx2)
                r = rel(x, mx2)
                q4[r] = q4.get(r, 0) + 1
                if r == 'other' and len(ex['q4other']) < 5:
                    ex['q4other'].append((M, i, x, mx2))
    print(f'segprov positions: {npos}, both-fire: {nboth}, ext-only-fire: {next_only}')
    print('Q1 rel(mx, mx2):', q1)
    print('Q2 uncovered x2-violators:', q2bad)
    print('Q3 mx2 not partner of mx:', q3bad)
    print('Q4 rel(x, mx2) [projE_iii]:', q4)
    for k in ('q1other','q1eq','q2','q3','q4other'):
        for e in ex[k]:
            M, i = e[0], e[1]
            print(f'-- {k}: M={"".join(f"({a},{b})" for a,b in M)} i={i}')
            for t in e[2:]:
                print('     ', fmtb(list(t)) if t else 'Z')

if __name__ == '__main__':
    main()
