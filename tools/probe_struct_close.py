#!/usr/bin/env python3
"""Deep structural probe of tail_zone_ST_PS and keeps_head_ST_PS.

Goals:
 (A) tail_zone_ST_PS: M=(0,y)#r in ST_PS  ==>  dropWhile(0<fst) r in ST_PS.
     Verify at deep closure; and CHARACTERIZE the tail zone (is it itself a
     diagSeq, or how does it relate to M?).
 (B) keeps_head_ST_PS: M in ST_PS ==> keeps_head M.  Verify; break out the
     tied-tail-head subcase (a=e where head subscript y equals normalized tail
     head subscript) to see how often it occurs.
 (C) Try to find a structural invariant on ST_PS membership that is (i) closed
     under tail-zone and (ii) implies keeps_head, using only blockok-style data.
"""
import sys, itertools
sys.path.insert(0, '.')
sys.setrecursionlimit(1000000)
from fast_pss import diagSeq, oper, Lng
from wfe_explore import translate, olt, fmt, enum_ST
from valnorm import conv, nrm, lt_term

Z = ()

def proj(a, t):
    # proj a t : in three-term land. We work in conv/buchholz form via nrm.
    pass

def untr(t, d):
    out = []
    for (_, a, b) in t:
        out.append((d, a)); out += untr(b, d+1)
    return out

def takeW(r): return [p for p in itertools.takewhile(lambda q: 0 < q[0], r)]
def dropW(r): return list(itertools.dropwhile(lambda q: 0 < q[0], r))

def blockok(d, B):
    if not B: return True
    if B[0][0] != d: return False
    if any(p[0] < d for p in B): return False
    return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))

# build a large ST_PS closure
ST = list(enum_ST(seed_max_v=6, oper_ns=(1,2,3,4,5), max_len=18, rounds=10))
STset = set(ST)
print('ST_PS corpus =', len(ST), flush=True)

# (A) tail-zone closure
A_bad = 0; A_tot = 0
tail_not_in = []
tail_shapes = {}  # describe how tail relates to membership
for M in ST:
    if not M: continue
    if M[0][0] != 0: continue
    y = M[0][1]
    r = list(M[1:])
    tz = dropW(r)
    A_tot += 1
    if tuple(tz) not in STset:
        # may just be outside the enumerated finite corpus; check membership properly
        A_bad += 1
        if len(tail_not_in) < 20:
            tail_not_in.append((M, tz))
print(f'(A) tail-zone in-corpus: tot={A_tot} not-found-in-corpus={A_bad}', flush=True)

# Characterize: is tail zone = drop the leading argument-block? i.e.
# M = (0,y) ++ aM ++ tM where aM=takeW(r). tM should start with (0,y') row0.
# Claim: tM is a *suffix* of M starting at a row-0 column, and itself blockok 0.
suffix_blockok_bad = 0
for M in ST:
    if not M or M[0][0] != 0: continue
    r = list(M[1:]); tz = dropW(r)
    if tz and not blockok(0, tz):
        suffix_blockok_bad += 1
print(f'(A2) tail-zone blockok 0 violations = {suffix_blockok_bad}', flush=True)

# Is the tail zone a SUFFIX of M that is ALSO reachable? Let's test a stronger
# structural claim: EVERY row-0-headed suffix of M in ST_PS is in ST_PS.
# i.e. for each index i with M[i][0]==0, M[i:] in ST_PS.
suffix_not_in = 0; suffix_tot = 0; suffix_ex = []
for M in ST:
    n = len(M)
    for i in range(n):
        if M[i][0] != 0: continue
        suf = tuple(M[i:])
        suffix_tot += 1
        if suf not in STset:
            suffix_not_in += 1
            if len(suffix_ex) < 15: suffix_ex.append((M, i, list(suf)))
print(f'(A3) row0-headed suffixes in corpus: tot={suffix_tot} not-found={suffix_not_in}', flush=True)
for M,i,suf in suffix_ex[:8]:
    print('   M=',fmt(M),' i=',i,' suf=',fmt(suf), ' suf-blockok0=',blockok(0,suf))

print('DONE-A', flush=True)
