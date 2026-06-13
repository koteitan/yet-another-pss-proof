#!/usr/bin/env python3
"""Characterize the domain D on which proj is monotone: what property do
NF-translate subterms satisfy that the wf3 proj_mono counterexamples violate?

Candidate invariants on a conv-form term t (for each principal D_a(b) in t):
  H1  leading level of b <= a          (arg's top principal not above a)
  H2  every level in b <= a            (hereditary: no level above a under D_a)
  H3  leading level of b <  a+1 (==H1)
  H4  G_a(b) all < b   (the wf3 coefficient cond -- baseline, all wf3 have ~this)
We print which invariants ALL NF-translate subterms satisfy, and whether the
known wf3 counterexample b=D0(D1 0 + D0 0) violates them.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate
from fast_pss import oper, diagSeq, Lng
from valnorm import conv, lt_term, le_term, G as Gset, in_OT

def levels(b):
    out = []
    for (_, a, c) in b:
        out.append(a); out += levels(c)
    return out

def lead_level(b):
    return b[0][1] if b else -1

def principals(t):
    """yield every principal (a, b) hereditarily."""
    for (_, a, b) in t:
        yield (a, b)
        yield from principals(b)

def check_invariants(t):
    """return set of invariant labels VIOLATED by some principal of t."""
    bad = set()
    for (a, b) in principals(t):
        if b == (): continue
        if lead_level(b) > a: bad.add('H1_lead<=a')
        if any(l > a for l in levels(b)): bad.add('H2_allhered<=a')
    return bad

def enum(seed_max_v, oper_ns, max_len, rounds):
    seen = set(); frontier = []
    for v in range(seed_max_v+1):
        M = tuple(diagSeq(0, v)); seen.add(M); frontier.append(M)
    for _ in range(rounds):
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in oper_ns:
                N = tuple(oper(list(M), n))
                if len(N) <= max_len and N not in seen:
                    seen.add(N); nxt.append(N)
        frontier = nxt
        if not frontier: break
    return seen

if __name__ == '__main__':
    smv = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    rounds = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    mlen = int(sys.argv[3]) if len(sys.argv) > 3 else 24
    ST = enum(smv, (1,2,3), mlen, rounds)
    allbad = set(); per = {}
    nterms = 0
    for M in ST:
        c = conv(translate(M))
        nterms += 1
        bad = check_invariants(c)
        for x in bad:
            per[x] = per.get(x, 0) + 1
        allbad |= bad
    print(f'NF-translate hosts={len(ST)}')
    print(f'invariants VIOLATED by some NF translate: {sorted(allbad) or "NONE"}')
    for k, v in sorted(per.items()):
        print(f'   {k}: violated in {v} hosts')
    # the wf3 counterexample
    cex = (('D', 0, (('D', 1, ()), ('D', 0, ()))),)   # D0(D1 0 + D0 0)
    print('wf3 counterexample b=D0(D1 0+D0 0) violates:', sorted(check_invariants(cex)))
    cex2 = (('D', 0, (('D', 1, ()),)),)               # D0(D1 0)
    print('wf3 counterexample b=D0(D1 0)      violates:', sorted(check_invariants(cex2)))
