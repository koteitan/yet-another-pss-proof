#!/usr/bin/env python3
"""Verify the EXACT residual lemmas that sigma_seqlex_mono is reduced to.

Reduction (mirrors seqlex_imp_olt block induction on length M + length N):
  M=(0,y)#r, N=(0,y')#r'  both ST_PS, seqlex M N.
  sigma M = (0,y) # SP(y,aM) @ sigma tM            (S) [verified 0/10437]
  where SP(y,a) = untr 1 (proj y (nrm (translate a))).

Residual obligations the green skeleton leaves as named sorries:

 (R-KH) keeps_head holds on every ST_PS sequence  (head non-absorption, T1).
        => sigma M = (0,y)#SP(y,aM)@sigma tM literally.

 (R-SP) ARG-ZONE core: for ST_PS M=(0,y)#r, N=(0,y)#r' (SAME head y),
        seqlex_arg_or_tail args-case gives  aM != aN  and  seqlex aM aN.
        Then  seqlex (SP(y,aM)) (SP(y,aN))   AND the depth-gap condition
        needed by seqlex_append_left holds:
          len SP(y,aM) < len SP(y,aN)  -->  sigma tM != [] -->
              pairlt (hd (sigma tM)) (SP(y,aN) ! len SP(y,aM)).
        (the gap is automatic: SP rows are >=1, sigma-tail head row =0.)

 (R-IH) TAIL-ZONE: tails-case gives aM=aN (=> SP equal) and seqlex tM tN;
        need seqlex(sigma tM)(sigma tN).  This is the induction hypothesis;
        it requires tM,tN to be valid recursion arguments (blockok 0, and the
        cores hold on them).  We check the zones stay in the verified universe.
"""
import sys, itertools, random
sys.path.insert(0, '.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, fmt, enum_ST
from valnorm import conv, nrm, lt_term, G

random.seed(11)

def untr(t, d):
    out = []
    for (_, a, b) in t:
        out.append((d, a)); out += untr(b, d+1)
    return out
def proj(a, bb):
    while True:
        bad = [g for g in G(a, bb) if not lt_term(g, bb)]
        if not bad: break
        g = bad[0]
        for h in bad[1:]:
            if lt_term(g, h): g = h
        bb = g
    return bb
def nrm_t(M): return nrm(conv(translate(list(M))))
def sigma(M): return untr(nrm_t(M), 0)
def SP(y, a): return untr(proj(y, nrm(conv(translate(list(a))))), 1)
def pairlt(p, q): return p[0] < q[0] or (p[0] == q[0] and p[1] < q[1])
def seqlex(M, N):
    i = 0
    while i < len(M) and i < len(N):
        if M[i] != N[i]: return pairlt(M[i], N[i])
        i += 1
    return len(M) < len(N)
def ztake(r): return list(itertools.takewhile(lambda q: 0 < q[0], r))
def zdrop(r): return list(itertools.dropwhile(lambda q: 0 < q[0], r))

ST = list(enum_ST(seed_max_v=5, oper_ns=(1,2,3,4,5), max_len=15, rounds=8))
print('ST_PS corpus =', len(ST), flush=True)

# (R-KH): keeps_head on every ST_PS sequence  (== (S) literal head retention)
kh_bad = 0; kh_tot = 0
for M in ST:
    M = list(M)
    if not M: continue
    kh_tot += 1
    y = M[0][1]; r = M[1:]
    lhs = sigma(M)
    rhs = [(0, y)] + SP(y, ztake(r)) + sigma(zdrop(r))
    if lhs != rhs: kh_bad += 1
print(f'(R-KH) head-nonabsorption / (S): tot={kh_tot} violations={kh_bad}', flush=True)

# (R-SP) and gap: arg-zone monotonicity + append gap, on SAME-head ordered pairs
sp_bad = 0; sp_ord = 0; gap_bad = 0
# (R-IH) tails: aM=aN  => SP equal, and seqlex tM tN => seqlex(sigma tM)(sigma tN)
ih_bad = 0; ih_ord = 0
sample = ST if len(ST) < 400 else random.sample(ST, 400)
for M in sample:
    for N in sample:
        M = list(M); N = list(N)
        if not M or not N: continue
        if M[0][1] != N[0][1]: continue   # same head y only
        y = M[0][1]
        aM = ztake(M[1:]); tM = zdrop(M[1:])
        aN = ztake(N[1:]); tN = zdrop(N[1:])
        if not seqlex(M[1:], N[1:]): continue
        # determine arg-or-tail decision (mirror seqlex_arg_or_tail)
        if aM == aN:
            # tails case: need seqlex tM tN  and seqlex(sigma tM)(sigma tN)
            if seqlex(tM, tN):
                ih_ord += 1
                if not seqlex(sigma(tM), sigma(tN)): ih_bad += 1
        else:
            # args case
            if seqlex(aM, aN):
                sp_ord += 1
                spm = SP(y, aM); spn = SP(y, aN)
                if not seqlex(spm, spn): sp_bad += 1
                # gap condition for seqlex_append_left
                if len(spm) < len(spn):
                    st = sigma(tM)
                    if st:
                        if not pairlt(st[0], spn[len(spm)]): gap_bad += 1
print(f'(R-SP) arg-zone seqlex-mono: ordered={sp_ord} violations={sp_bad}', flush=True)
print(f'(gap) append-left gap cond: violations={gap_bad}', flush=True)
print(f'(R-IH) tail-zone seqlex-mono: ordered={ih_ord} violations={ih_bad}', flush=True)
print('DONE')
