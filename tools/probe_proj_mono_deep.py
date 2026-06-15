#!/usr/bin/env python3
"""DEEP soundness gate for the candidate crux lemma

    PROJMONO:  a, b, f  with  olt b f  (b,f hereditary args of NF translates)
               ==>  olt (proj a (nrm b)) (proj a (nrm f))   strictly.

This is the §1 collapse content for the arg-zone (sigmaP).  The 7th-incident
warning: oV_mono_cnf looked true on shallow samples but was FALSE at depth 5 on
y2=p0(p1(y1)) <o y1.  So we MUST go deep and MUST explicitly inject the
y-tower and similar non-NF hereditary args.

We also test the EXACT thing the proof needs: hereditary args of NF translates
(which is the universe sigmaP/proj is applied to inside the induction), AND
the broader universe of ALL cnf subterms (to catch a y1/y2-style break).
"""
import sys, itertools, random
sys.path.insert(0, '.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, maxsub, fmt, enum_ST
from valnorm import conv, nrm, lt_term, le_term, G
from fast_pss import oper

random.seed(17)

def proj(a, x):
    bb = x
    while True:
        bad = [g for g in G(a, bb) if not lt_term(g, bb)]
        if not bad: break
        g = bad[0]
        for h in bad[1:]:
            if lt_term(g, h): g = h
        bb = g
    return bb

def args_with_sub(t):
    for p in t:
        _, a, b = p
        yield (a, b)
        yield from args_with_sub(b)

def subterms(t):          # all conv-subterms (incl tails)
    out = set()
    def rec(s):
        out.add(s)
        for p in s:
            _, a, b = p
            rec(b)
        # tails: suffixes of the principal list
        for i in range(1, len(s)+1):
            out.add(s[i:])
    rec(t)
    return out

# ---- DEEP closure (+5 beyond enum, like the soundness gate) ----
base = enum_ST(seed_max_v=5, oper_ns=(1,2,3,4,5), max_len=16, rounds=8)
extra = set(base); cur = list(extra)
for _ in range(5):
    new = []
    for M in cur:
        M = list(M)
        if len(M) < 2: continue
        for n in (1,2,3,4,5):
            tt = tuple(oper(M, n))
            if len(tt) <= 22 and tt not in extra:
                extra.add(tt); new.append(tt)
    cur = new
    if not cur: break
print('deep ST closure =', len(extra), flush=True)

terms = set(conv(translate(list(M))) for M in extra)

# universe A: hereditary ARGS of NF translates (what proj is actually applied to)
from collections import defaultdict
argsub = defaultdict(set)
for c in terms:
    for (a, b) in args_with_sub(c):
        argsub[a].add(b)

# universe B: ALL cnf subterms (to catch a y1/y2-style break across non-args)
allsub = set()
for c in terms: allsub |= subterms(c)
# inject the y-tower explicitly (the known disaster family)
D = lambda v, x: ('D', v, x); T = lambda *ps: tuple(ps)
y0 = T(D(1, ()))
yk = y0
ytower = [y0]
for _ in range(6):
    yk = T(D(0, T(D(1, yk)))); ytower.append(yk)
for y in ytower: allsub.add(y)
# also p0(p1(x)) wrappers of args
for c in list(allsub):
    allsub.add(T(D(0, T(D(1, c)))))
subbysub = defaultdict(set)
for s in allsub:
    for a in range(0, 6):
        subbysub[a].add(s)

def check(name, bysub, cap):
    tot = rev = nonstrict = 0
    exNS = []; exR = []
    for a, S in bysub.items():
        S = list(S)
        if len(S) > cap: S = random.sample(S, cap)
        for b, f in itertools.combinations(S, 2):
            if lt_term(b, f): lo, hi = b, f
            elif lt_term(f, b): lo, hi = f, b
            else: continue
            tot += 1
            pl = proj(a, nrm(lo)); ph = proj(a, nrm(hi))
            if lt_term(ph, pl):
                rev += 1
                if len(exR) < 5: exR.append((a, lo, hi))
            elif pl == ph:
                nonstrict += 1
                if len(exNS) < 5: exNS.append((a, lo, hi))
    print(f'[{name}] olt-ordered pairs={tot} reversals={rev} collapses(nonstrict)={nonstrict}', flush=True)
    from valnorm import fmtb
    for a, lo, hi in exR: print(f'   REV a={a}: {fmtb(lo)} <o {fmtb(hi)}  proj-> {fmtb(proj(a,nrm(lo)))} vs {fmtb(proj(a,nrm(hi)))}')
    for a, lo, hi in exNS: print(f'   COLLAPSE a={a}: {fmtb(lo)} <o {fmtb(hi)}  proj-> {fmtb(proj(a,nrm(lo)))} = {fmtb(proj(a,nrm(hi)))}')
    return rev, nonstrict

print('--- universe A: hereditary ARGS of NF translates ---', flush=True)
ra, na = check('ARGS', argsub, 260)
print('--- universe B: ALL cnf subterms + y-tower + p0p1 wrappers ---', flush=True)
rb, nb = check('ALLSUB', subbysub, 220)
print(f'SUMMARY: ARGS rev={ra} coll={na} ; ALLSUB rev={rb} coll={nb}', flush=True)
print('DONE', flush=True)
