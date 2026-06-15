#!/usr/bin/env python3
"""Head-anchored ProjFixesNrm check.

The nrm value-chain only calls proj a (nrm b) where a is the HEAD subscript of
the enclosing P-node.  So the honest obligation is, for every P a b c subterm:
    proj a (nrm b) == nrm b
This audit checks that (head-anchored), contrasting with the false 'for all u'.
Also checks the stronger structural claim:
    for nrm-image s = nrm b argument of head a:  Gterm a s all olt s.
And: does proj a (nrm b) = nrm b reduce to  'lead(nrm b) >= a is impossible OR
the head arg of nrm b is < it'.  Report the structural pattern.
"""
import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, '.')
from wfe_explore import Z, P, olt, translate, enum_ST, subterms, maxsub
from audit_projfix_wf3 import Gterm, wf3, proj, nrm

def lead(t):
    return 0 if t == () else t[0]

def main():
    ST = enum_ST(seed_max_v=3, oper_ns=(1,2,3), max_len=11, rounds=6)
    terms = set()
    for M in ST:
        t = translate(M)
        for st in subterms(t):
            terms.add(st)
    print(f'#distinct subterms enumerated: {len(terms)}')

    # head-anchored: for every P a b c subterm, proj a (nrm b) == nrm b
    total = viol = 0
    examples = []
    for t in terms:
        if t == (): continue
        a, b, c = t
        nb = nrm(b)
        total += 1
        if proj(a, nb) != nb:
            viol += 1
            if len(examples) < 8:
                examples.append((a, b, nb, proj(a, nb)))
    print(f'\n[HEAD] proj a (nrm b) == nrm b  for every P a b c subterm:')
    print(f'    checks={total}  violations={viol}')
    for a,b,nb,p in examples:
        print(f'    VIOL a={a} nrm(b)={nb}  lead(nrm b)={lead(nb)}  proj={p}')

    # structural: for the head-anchored arg s=nrm(b) with head a, is Gterm a s < s?
    total2 = viol2 = 0
    ex2 = []
    for t in terms:
        if t == (): continue
        a, b, c = t
        s = nrm(b)
        for g in Gterm(a, s):
            total2 += 1
            if not olt(g, s):
                viol2 += 1
                if len(ex2) < 8: ex2.append((a, s, g))
    print(f'\n[HEAD-STRUCT] Gterm a (nrm b) all olt (nrm b), head a:')
    print(f'    checks={total2}  violations={viol2}')
    for a,s,g in ex2:
        print(f'    VIOL a={a} s={s} g={g}')

    # is the head-anchored property simply: lead(nrm b) < a   OR  Gterm-clause?
    # observe relationship lead(nrm b) vs a
    from collections import Counter
    rel = Counter()
    for t in terms:
        if t == (): continue
        a, b, c = t
        nb = nrm(b)
        if nb == (): rel['nrm_b=Z'] += 1
        elif lead(nb) < a: rel['lead<a'] += 1
        elif lead(nb) == a: rel['lead=a'] += 1
        else: rel['lead>a'] += 1
    print(f'\n[REL] lead(nrm b) vs head a:  {dict(rel)}')

if __name__ == '__main__':
    main()
