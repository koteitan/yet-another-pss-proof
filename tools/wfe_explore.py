#!/usr/bin/env python3
"""Explore the within-maxsub-level structure of NF = translate`ST_PS under the
pure-lex order olt, to design the wfE_within_level proof (the sole remaining
sorry in wf.thy).

Questions:
  Q1 (hereditary spine shape): for x in NF and ANY subterm position, does the
     argument part b of each principal P a b c have spine = a consecutive run
     [a+1, a+2, ..., k] followed by values <= that run max?  (the "shifted inv2"
     hereditary invariant candidate)
  Q2 sibling subscripts: cnf gives non-increasing tops; what exactly are the
     sibling runs in NF?
  Q3 within-level descent: collect olt-descending pairs at equal maxsub and
     test candidate measures.
"""
import sys, itertools
sys.path.insert(0, '.')
from fast_pss import diagSeq, oper, Lng

# ---------- three terms ----------
Z = ()
def P(a,b,c): return (a,b,c)

def translate(M):
    M = list(M)
    if not M: return Z
    (x,y) = M[0]; rest = M[1:]
    i = 0
    while i < len(rest) and rest[i][0] > x: i += 1
    return (y, translate(rest[:i]), translate(rest[i:]))

def olt(s,t):
    if s == (): return t != ()
    if t == (): return False
    a,b,c = s; e,f,g = t
    if a != e: return a < e
    if b != f: return olt(b,f)
    return olt(c,g)

def maxsub(t):
    if t == (): return 0
    a,b,c = t
    return max(a, maxsub(b), maxsub(c))

def spine(t):
    s=[]
    while t != ():
        a,b,c = t
        s.append(a); t = b
    return s

def tops(t):
    s=[]
    while t != ():
        a,b,c = t
        s.append(a); t = c
    return s

def subterms(t):
    yield t
    if t != ():
        a,b,c = t
        yield from subterms(b)
        yield from subterms(c)

def fmt(t):
    if t == (): return '0'
    a,b,c = t
    s = f'p{a}({fmt(b)})'
    if c != (): s += '+' + fmt(c)
    return s

# ---------- enumerate ST_PS ----------
def enum_ST(seed_max_v=3, oper_ns=(1,2,3), max_len=11, rounds=4):
    seen = set()
    frontier = []
    for v in range(seed_max_v+1):
        M = tuple(diagSeq(0,v))
        if M not in seen:
            seen.add(M); frontier.append(M)
    for _ in range(rounds):
        nxt=[]
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in oper_ns:
                N = tuple(oper(list(M), n))
                if len(N) <= max_len and N not in seen:
                    seen.add(N); nxt.append(N)
        frontier = nxt
        if not frontier: break
    return seen

def is_consec_run_spine(t):
    """spine of t is [s0, s0+1, ..., s0+k] then values <= s0+k (shifted inv2)."""
    s = spine(t)
    if not s: return True
    s0 = s[0]
    m = max(s)
    # positions 0..(m-s0) must read s0, s0+1, ..., m
    need = m - s0 + 1
    if len(s) < need: return False
    for i in range(need):
        if s[i] != s0+i: return False
    return all(v <= m for v in s)

def main():
    ST = enum_ST()
    print(f'#ST_PS enumerated: {len(ST)}')
    NF = {}
    for M in ST:
        t = translate(M)
        NF.setdefault(maxsub(t), []).append((M,t))
    for m in sorted(NF):
        print(f'level {m}: {len(NF[m])} terms')

    # Q1: hereditary spine shape on ALL subterms of NF terms
    bad = []
    for m, lst in NF.items():
        for M,t in lst:
            for st in subterms(t):
                if st != () and not is_consec_run_spine(st):
                    bad.append((M,t,st))
    print(f'\nQ1 hereditary consec-run-spine violations: {len(bad)}')
    for M,t,st in bad[:5]:
        print('  M=',''.join(f'({a},{b})' for a,b in M))
        print('  subterm:', fmt(st), ' spine=', spine(st))

    # Q1b: arg-subscript relation: for subterm P a b c with b!=Z, is lead(b)=a+1?
    bad2 = []
    for m, lst in NF.items():
        for M,t in lst:
            for st in subterms(t):
                if st != ():
                    a,b,c = st
                    if b != () and b[0] != a+1:
                        bad2.append((M,st))
    print(f'\nQ1b arg-lead = sub+1 violations: {len(bad2)}')
    for M,st in bad2[:5]:
        print('  M=',''.join(f'({a},{b})' for a,b in M), '  sub:', fmt(st))

    # Q2: sibling tops within NF subterms (after the head): pattern?
    pats = {}
    for m, lst in NF.items():
        for M,t in lst:
            for st in subterms(t):
                if st != ():
                    tp = tuple(tops(st))
                    if len(tp) >= 2:
                        # non-increasing? equal? drop pattern
                        ni = all(tp[i] >= tp[i+1] for i in range(len(tp)-1))
                        pats.setdefault(('noninc' if ni else 'OTHER'), set()).add(tp)
    for k,v in pats.items():
        ex = list(itertools.islice(v,4))
        print(f'\nQ2 sibling tops {k}: {len(v)} patterns, e.g. {ex}')

    # Q3: within-level descent pairs (sample) - check: does descent at equal
    # maxsub strictly decrease the *spine tail* lexicographically...
    # measure candidate A: (depth of first spine break, ...) -- just dump a few
    print('\nQ3: sample within-level olt pairs (w < x, maxsub equal):')
    cnt = 0
    for m, lst in NF.items():
        if m == 0: continue
        terms = [t for _,t in lst]
        terms = list(dict.fromkeys(terms))
        for i in range(len(terms)):
            for j in range(len(terms)):
                if i!=j and olt(terms[i],terms[j]):
                    cnt += 1
                    if cnt <= 8:
                        print(f'  [m={m}] {fmt(terms[i])}  <  {fmt(terms[j])}')
    print(f'  total within-level comparable pairs: {cnt}')

if __name__ == '__main__':
    main()
