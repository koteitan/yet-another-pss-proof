#!/usr/bin/env python3
"""Deep (+extra) blast-radius audit of the value-side cascade lemmas against
their LITERAL Isabelle statements:
  - E6_nbcK_T   (structural, cheap): premises => dropWhile == []
  - NT_tie_fdlex (value, expensive): fd-case => NOT olt(proj K, proj K1)
  - NT_tie_resolved (value): tie-case => NOT olt(proj-side)
Usage: audit_value_deep.py [extra] [maxhosts_for_value]
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper
from wfe_explore import enum_ST
from valnorm import lt_term
from mine_e6 import NT
from mine_proj import G, proj
from mine_fire4 import msfx

def maxr1(S): return max(c[1] for c in S)
NTC = {}
def nt(S):
    S = tuple(S)
    if S not in NTC: NTC[S] = NT(list(S))
    return NTC[S]
def olt(a, b): return lt_term(a, b)

def hosts_plus(extra):
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(ST); cur = list(out)
    for i in range(extra):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out: out.add(t); new.append(t)
        cur = new
        print('  +%d: total %d' % (i+1, len(out)), flush=True)
    return out

def dsegs(H):
    lh = len(H)
    for ppi in range(lh):
        lv = H[ppi][0]; dend = ppi+1
        while dend < lh and H[dend][0] > lv: dend += 1
        for k in range(ppi+2, dend+1):
            yield (H[ppi][1], tuple(H[ppi+1:k]))

def tw(pred, xs):
    out=[]
    for x in xs:
        if pred(x): out.append(x)
        else: break
    return out
def dw(pred, xs):
    i=0
    while i<len(xs) and pred(xs[i]): i+=1
    return list(xs[i:])

def main():
    extra = int(sys.argv[1]) if len(sys.argv)>1 else 5
    HS = hosts_plus(extra)
    print('hosts:', len(HS), flush=True)
    n_nbcKT = b_nbcKT = 0; ex_nbcKT = []
    n_fd = b_fd = 0; ex_fd = []
    n_tie = b_tie = 0; ex_tie = []
    seen = set()
    for H in HS:
        for (u, S) in dsegs(H):
            if (u, S) in seen: continue
            seen.add((u, S))
            if len(S) < 2: continue
            c0 = S[0]; rest = list(S[1:])
            K = tw(lambda r: c0[0] < r[0], rest)
            T = dw(lambda r: c0[0] < r[0], rest)
            m = maxr1(S)
            # E6_nbcK_T (structural)
            if u <= c0[1] and K and maxr1(K) == m and c0[1] < m:
                n_nbcKT += 1
                if T:
                    b_nbcKT += 1
                    if len(ex_nbcKT) < 4: ex_nbcKT.append((u, S))
            # tie case: dropWhile = c1#rest1, snd c1 = snd c0
            if T and T[0][1] == c0[1]:
                c1 = T[0]; rest1 = list(T[1:])
                K1 = tw(lambda r: c1[0] < r[0], rest1)
                # NT_tie_resolved conclusion
                A = proj(c0[1], nt(K)) if K else proj(c0[1], ())
                A1 = proj(c1[1], nt(K1)) if K1 else proj(c1[1], ())
                n_tie += 1
                if olt(A, A1):
                    b_tie += 1
                    if len(ex_tie) < 4: ex_tie.append((u, S))
                # fd-case sub-check (first-diff lex between K and K1)
                pfx = 0
                while pfx < len(K) and pfx < len(K1) and K[pfx] == K1[pfx]: pfx += 1
                if pfx < len(K) and pfx < len(K1):
                    x = K[pfx]; x1 = K1[pfx]
                    if x1[0] < x[0] or (x1[0]==x[0] and x1[1]<x[1]):
                        n_fd += 1
                        if olt(A, A1):
                            b_fd += 1
                            if len(ex_fd) < 4: ex_fd.append((u, S))
    print(f'E6_nbcK_T  : {n_nbcKT} inst, {b_nbcKT} violations (T must be [])')
    print(f'NT_tie_res : {n_tie} inst, {b_tie} violations (NOT olt A A1)')
    print(f'NT_tie_fdlx: {n_fd} inst, {b_fd} violations (fd-case)')
    for u, S in ex_nbcKT:
        print('  nbcKT-fail u=%d S=%s' % (u, ''.join('(%d,%d)'%p for p in S)))
    for u, S in ex_tie:
        print('  tie-fail u=%d S=%s' % (u, ''.join('(%d,%d)'%p for p in S)))
    for u, S in ex_fd:
        print('  fd-fail u=%d S=%s' % (u, ''.join('(%d,%d)'%p for p in S)))

if __name__ == '__main__':
    main()
