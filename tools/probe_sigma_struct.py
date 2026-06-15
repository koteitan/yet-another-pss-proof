#!/usr/bin/env python3
"""Verify the STRUCTURAL recursion of sigma on NF blocks (head never absorbed).

For M in ST_PS, M = (0,y)#r, r = aM ++ tM (zone split at depth 0):
  translate M = P y (translate aM) (translate tM)
  nrm(translate M) = ins y (proj y (nrm(translate aM))) (nrm(translate tM))
Conjecture (from T1=0): the ins NEVER absorbs the head, so
  nrm(translate M) = P y (proj y (nrm(translate aM))) (nrm(translate tM))
hence
  sigma M = (0,y) # untr 1 (proj y (nrm(translate aM))) @ sigma tM            (S)
and the arg-part = untr 1 (proj y (nrm(translate aM))).

We ALSO need: is the tail part exactly sigma(tM)?  (yes by def of sigma on tM,
since translate tM is the tail term and untr 0).  And arg part is a depth-1
block.  Verify (S) exactly, and that the arg-part equals
  sigmaP(y, aM) := untr 1 (proj y (nrm (translate aM)))
which is the "sigma with a proj-y wrap at depth 1".

THEN the seqlex block induction can recurse:
  - tails zone: seqlex tM tN  -> need seqlex (sigma tM)(sigma tN)  [IH, shorter]
  - args zone:  seqlex aM aN  -> need seqlex (sigmaP y aM)(sigmaP y aN) [IH-like]
We test the args-zone monotonicity of sigmaP too.
"""
import sys, itertools, random
sys.path.insert(0, '.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, maxsub, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb

random.seed(3)

def untr(t, d):
    out = []
    for (_, a, b) in t:
        out.append((d, a)); out += untr(b, d+1)
    return out

# proj on conv-term: replicate valnorm's inner collapse loop as a function
from valnorm import G
def proj(a, bb):
    while True:
        bad = [g for g in G(a, bb) if not lt_term(g, bb)]
        if not bad: break
        g = bad[0]
        for h in bad[1:]:
            if lt_term(g, h): g = h
        bb = g
    return bb

def sigma_term(w):   # w a conv-term ; sigma at depth 0 of the term
    return untr(nrm(w), 0)
def sigma(M):
    return untr(nrm(conv(translate(list(M)))), 0)

def zone_take(r): return list(itertools.takewhile(lambda q: 0 < q[0], r))
def zone_drop(r): return list(itertools.dropwhile(lambda q: 0 < q[0], r))

def sigmaP(y, aM):
    # untr 1 (proj y (nrm (translate aM)))
    return untr(proj(y, nrm(conv(translate(list(aM))))), 1)

ST = list(enum_ST(seed_max_v=5, oper_ns=(1,2,3,4,5), max_len=15, rounds=8))
print('ST_PS corpus =', len(ST), flush=True)

# verify decomposition (S) exactly
bad_S = 0; nonempty = 0
for M in ST:
    M = list(M)
    if not M: continue
    nonempty += 1
    y = M[0][1]; r = M[1:]
    aM = zone_take(r); tM = zone_drop(r)
    lhs = sigma(M)
    rhs = [(0, y)] + sigmaP(y, aM) + sigma(tM)
    if lhs != rhs:
        bad_S += 1
        if bad_S <= 5:
            print('  S-miss M=', fmt(M))
            print('    lhs=', fmt(lhs)); print('    rhs=', fmt(rhs))
print(f'(S) decomposition exact: nonempty={nonempty} violations={bad_S}', flush=True)

# args-zone: sigmaP monotone?  For NF blocks M with head (0,y), the arg-zone aM
# is a depth-1 block.  We need: seqlex aM aN  => seqlex (sigmaP y aM)(sigmaP y aN)
# enumerate (y, aM) from actual NF blocks
argpool = {}
for M in ST:
    M = list(M)
    if not M: continue
    y = M[0][1]; aM = zone_take(M[1:])
    argpool.setdefault(y, set()).add(tuple(aM))
viol_arg = tot_arg = 0
for y, aset in argpool.items():
    al = sorted(aset)
    if len(al) > 200: al = random.sample(al, 200)
    for a1, a2 in itertools.combinations(al, 2):
        a1l, a2l = list(a1), list(a2)
        # seqlex on depth-1 blocks: same column-lex
        def seqlex(M, N):
            i = 0
            while i < len(M) and i < len(N):
                if M[i] != N[i]:
                    return M[i][0] < N[i][0] or (M[i][0]==N[i][0] and M[i][1]<N[i][1])
                i += 1
            return len(M) < len(N)
        if seqlex(a1l, a2l): lo, hi = a1l, a2l
        elif seqlex(a2l, a1l): lo, hi = a2l, a1l
        else: continue
        tot_arg += 1
        sl, sh = sigmaP(y, lo), sigmaP(y, hi)
        # compare via seqlex too
        if not seqlex(sl, sh):
            viol_arg += 1
            if viol_arg <= 6:
                print(f'  ARG-miss y={y}: {fmt(lo)} <seqlex {fmt(hi)} ; sigmaP {fmt(sl)} | {fmt(sh)}')
print(f'args-zone sigmaP-mono: ordered={tot_arg} violations={viol_arg}', flush=True)
print('DONE', flush=True)
