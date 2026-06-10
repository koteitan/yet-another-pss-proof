#!/usr/bin/env python3
"""Closure+1 audit of the EXACT frozen Isabelle sorry statements
(nrmstep.thy): E6_lpl, E6_dom_deep, E6_memT, E6_nbcK_T, E6_nbcK_K,
STS_B, r1ok_climb.  (memo 続29: every class fact must be re-validated
with closure+1 sampling against the literal statement.)
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from fast_pss import oper, fmt, Lng, entry, idx1, hasParent0, hasParent1, parent0, parent1
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

def pfire(u, t):
    return any(not lt_term(g, t) for g in G(u, t))

def hdsub(t): return t[0][1]
def hdarg(t): return t[0][2]

def hosts_plus1():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(ST)
    for M in ST:
        if len(M) < 2: continue
        for n in (1,2,3,4):
            out.add(tuple(oper(list(M), n)))
    return out

def dsegs(H):
    """(u, S) with pre @ pp # S @ post = H, S nonempty dominated by pp."""
    lh = len(H)
    for ppi in range(lh):
        lv = H[ppi][0]
        dend = ppi+1
        while dend < lh and H[dend][0] > lv: dend += 1
        for k in range(ppi+2, dend+1):
            yield (H[ppi][1], list(H[ppi+1:k]))

def main():
    HS = hosts_plus1()
    print('hosts:', len(HS), flush=True)
    cnt = Counter(); bad = Counter(); ex = {}
    seen = set()
    for H in HS:
        for (u, S) in dsegs(H):
            key = (u, tuple(S))
            if key in seen: continue
            seen.add(key)
            m = maxr1(S)
            tS = nt(S)
            gset = None
            L = len(S)
            fire = pfire(u, tS)
            hm = (S[0][1] == m)
            # ---- E6_lpl ----
            if hm:
                for a in range(1, L):           # pre' = S[:a] nonempty
                    for b in range(a+1, L+1):   # C = S[a:b] nonempty
                        C = S[a:b]
                        if C[0][1] != m: continue
                        tC = nt(C)
                        if gset is None: gset = G(u, tS)
                        if not any(g == tC for g in gset): continue
                        cnt['lpl'] += 1
                        if not lt_term(tC, tS):
                            bad['lpl'] += 1; ex.setdefault('lpl', (S, a, b, u))
            # ---- E6_dom_deep ----
            if fire:
                tw = 0
                while tw < L and S[tw][1] < m: tw += 1
                for a in range(tw+1, L):        # |takeWhile| < |pre'| = a
                    for b in range(a+1, L+1):
                        C = S[a:b]
                        if C[0][1] != m: continue
                        tC = nt(C)
                        if gset is None: gset = G(u, tS)
                        if not any(g == tC for g in gset): continue
                        if lt_term(tC, tS): continue
                        cnt['domdeep'] += 1
                        tM = nt(msfx(S))
                        if not (tC == tM or lt_term(tC, tM)):
                            bad['domdeep'] += 1; ex.setdefault('domdeep', (S, a, b, u))
            # ---- segment-as-c0#rest facts ----
            c0, rest = S[0], S[1:]
            i = 0
            while i < len(rest) and rest[i][0] > c0[0]: i += 1
            K, T = rest[:i], rest[i:]
            # E6_memT
            if fire and T and maxr1([c0]+K) < m:
                cnt['memT'] += 1
                tT = nt(T); tMT = nt(msfx(T))
                okmem = any(g == tMT for g in G(u, tT))
                okolt = not lt_term(tMT, tS)
                if not (okmem and okolt):
                    bad['memT'] += 1; ex.setdefault('memT', (S, u, okmem, okolt))
            # E6_nbcK_T
            if u <= c0[1] and K and maxr1(K) == m and c0[1] < m:
                cnt['nbcK_T'] += 1
                if T:
                    bad['nbcK_T'] += 1; ex.setdefault('nbcK_T', (S, u))
            # E6_nbcK_K
            if fire and u <= c0[1] and K and maxr1(K) == m and c0[1] < m:
                cnt['nbcK_K'] += 1
                tK = nt(K)
                if not (pfire(c0[1], tK) or msfx(K) == K):
                    bad['nbcK_K'] += 1; ex.setdefault('nbcK_K', (S, u))
    print('dseg-based done', dict(cnt), flush=True)

    # ---- STS_B ----
    for H in HS:
        lh = len(H)
        for ip in range(lh):
            p = H[ip]
            for jq in range(ip+1, lh):
                rest = list(H[ip+1:jq]); q = H[jq]
                i = 0
                while i < len(rest) and rest[i][0] > p[0]: i += 1
                K, T = rest[:i], rest[i:]
                if not T: continue
                if T[0][0] != p[0]: continue
                key = ('stsb', p, tuple(rest), q)
                if key in seen: continue
                seen.add(key)
                cnt['STS_B'] += 1
                A = proj(p[1], nt(K)) if K else proj(p[1], ())
                for tt in (nt(T), nt(T+[q])):
                    viol = (p[1] < hdsub(tt)) or (p[1] == hdsub(tt) and lt_term(A, hdarg(tt)))
                    if viol:
                        bad['STS_B'] += 1; ex.setdefault('STS_B', (fmt(H), ip, jq))
                        break
    print('STS_B done', flush=True)

    # ---- r1ok_climb ----
    for M in HS:
        M = list(M)
        j1 = Lng(M)-1
        if j1 == 0: continue
        if entry(M,0,j1) == 0 and entry(M,1,j1) == 0: continue
        i1 = idx1(M, j1)
        if i1 == 1:
            if not hasParent1(M, j1): continue
            j0 = parent1(M, j1)
        else:
            if not hasParent0(M, j1): continue
            j0 = parent0(M, j1)
        d0 = (entry(M,0,j1)-entry(M,0,j0)) if i1 > 0 else 0
        L = j1 - j0
        for qq in range(L):
            if not all(entry(M,0,j0+qq) <= entry(M,0,j0+r) for r in range(qq)): continue
            tgt = entry(M,0,j0+qq) + d0 - 1
            if tgt < 0: tgt = 0
            for rp in range(qq, L):
                if entry(M,0,j0+rp) != tgt: continue
                if not all(tgt < entry(M,0,j0+r) for r in range(rp+1, L)): continue
                cnt['climb'] += 1
                if not (entry(M,1,j0+qq) <= entry(M,1,j0+rp) + 1):
                    bad['climb'] += 1; ex.setdefault('climb', (fmt(M), qq, rp))
    print('instances:', dict(cnt))
    print('VIOLATIONS:', dict(bad))
    for k, v in ex.items(): print('  ex', k, v)

if __name__ == '__main__':
    main()
