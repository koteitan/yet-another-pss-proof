#!/usr/bin/env python3
"""Probe the SEQUENCE-side block induction for sigma_seqlex_mono.

sigma M = untr 0 (nrm (translate M)).  We test whether seqlex(sigma M)(sigma N)
can be proven by the SAME block induction as seqlex_imp_olt, i.e. whether
sigma commutes with the zone decomposition up to a controllable seam.

Block of M: M = (0,y)#r ; r = aM (takeWhile 0<fst) ++ tM (dropWhile).
translate M = P y (translate aM)(translate tM).
nrm(translate M) = ins y (proj y (nrm(translate aM))) (nrm(translate tM)).

KEY tests:
  (T1) when does ins ABSORB the head y (i.e. nrm(translate M) drops principal y)?
  (T2) does seqlex M N decompose (head / arg / tail) IN A WAY that survives sigma?
  (T3) Candidate clean lemma:  seqlex M N  with M,N NF blockok-0,
       both NONEMPTY same head (0,y) ==> the seqlex decision (arg-zone vs tail-
       zone) maps to the corresponding decision on sigma.  Count violations.
"""
import sys, itertools, random
sys.path.insert(0, '.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, maxsub, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb

random.seed(5)

def untr(t, d):
    out = []
    for (_, a, b) in t:
        out.append((d, a)); out += untr(b, d+1)
    return out
def sigma(M):
    return untr(nrm(conv(translate(list(M)))), 0)
def pairlt(p, q): return p[0] < q[0] or (p[0] == q[0] and p[1] < q[1])
def seqlex(M, N):
    i = 0
    while i < len(M) and i < len(N):
        if M[i] != N[i]: return pairlt(M[i], N[i])
        i += 1
    return len(M) < len(N)
def blockok(d, B):
    if not B: return True
    if B[0][0] != d: return False
    if any(p[0] < d for p in B): return False
    return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))
def takeW(r): return [p for p in itertools.takewhile(lambda q: 0 < q[0], r)]
def dropW(r):
    out = list(itertools.dropwhile(lambda q: 0 < q[0], r)); return out

ST = list(enum_ST(seed_max_v=5, oper_ns=(1,2,3,4,5), max_len=15, rounds=8))
print('ST_PS corpus =', len(ST), flush=True)

# sanity: sigma is blockok 0 and translate(sigma M)=nrm(translate M)
bad_blk = 0
for M in ST:
    if not blockok(0, sigma(list(M))): bad_blk += 1
print('blockok(0,sigma M) violations =', bad_blk, flush=True)

# T1: head absorption frequency
absorbed = total = 0
for M in ST:
    sM = sigma(list(M))
    if not M: continue
    y = M[0][1]
    total += 1
    # head absorbed iff sigma's first column subscript != y  OR length shorter at head
    if not sM or sM[0] != (0, y):
        absorbed += 1
print(f'T1 head-absorption: {absorbed}/{total} blocks lose/alter their head under sigma', flush=True)

# MAIN seq: seqlex M N ==> seqlex (sigma M)(sigma N)
pool = sorted(set(ST), key=lambda M: (len(M), M))
if len(pool) > 1200: pool = random.sample(pool, 1200)
viol = tot = 0
ex = []
for M, Np in itertools.combinations(pool, 2):
    M = list(M); Np = list(Np)
    if seqlex(M, Np): lo, hi = M, Np
    elif seqlex(Np, M): lo, hi = Np, M
    else: continue
    tot += 1
    if not seqlex(sigma(lo), sigma(hi)):
        viol += 1
        if len(ex) < 6: ex.append((lo, hi))
print(f'MAIN seqlex-mono under sigma: ordered={tot} violations={viol}', flush=True)
for lo, hi in ex:
    print(f'  {fmt(lo)} <seqlex {fmt(hi)}  but sigma not: {fmt(sigma(lo))} ; {fmt(sigma(hi))}')

# T3: the block-induction skeleton AFTER sigma.
# For same-head (0,y) NF blocks lo<hi: seqlex_arg_or_tail says the seqlex of the
# TAILS r,r' splits into (argEq & tailLex) or (argNeq & argLex). We check the
# analogous split holds for sigma(lo),sigma(hi): i.e. does the FIRST differing
# column of sigma(lo),sigma(hi) lie consistently?  We test the weaker, exact
# claim actually needed:  the induction reduces seqlex(sigma lo)(sigma hi) to a
# seqlex on a STRICTLY SHORTER pair (arg-zone or tail-zone of the *sigma* images).
# Operationally: verify monotone consistency is *not* destroyed by absorption.
same = miss = 0
for M, Np in itertools.combinations(pool, 2):
    M = list(M); Np = list(Np)
    if not M or not Np: continue
    if M[0] != Np[0]: continue
    if not seqlex(M, Np): continue
    same += 1
    if not seqlex(sigma(M), sigma(Np)):
        miss += 1
print(f'T3 same-head seqlex preserved by sigma: same-head-ordered={same} miss={miss}', flush=True)
print('DONE', flush=True)
