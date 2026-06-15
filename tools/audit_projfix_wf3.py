#!/usr/bin/env python3
"""Empirical audit of the ProjFixesNrm route.

Mirrors the Lean defs (Three = () | (a,b,c); olt; Gterm; wf3; proj; nrm) EXACTLY.

Checks two claims at closure depth:
  A. not_pfire_of_wf3:  wf3 t -> for ALL u, every g in Gterm u t has olt g t.
  B. ProjFixesNrm:      proj u (nrm t) == nrm t   for all u,t (the real target).
Also reports per-claim whether wf3(nrm t) holds (should always).
"""
import sys, itertools
sys.setrecursionlimit(100000)
sys.path.insert(0, '.')
from wfe_explore import Z, P, olt, translate, enum_ST, subterms, maxsub

# ---- Gterm u t  (Lean: P a b c => (if u<=a then {b} u Gterm u b else {}) u Gterm u c)
def Gterm(u, t):
    if t == (): return []
    a,b,c = t
    out = []
    if u <= a:
        out.append(b)
        out += Gterm(u, b)
    out += Gterm(u, c)
    return out

# ---- wf3 t (Lean: P a b c => wf3 b & wf3 c & (all x in Gterm a b, olt x b) & hdle c (P a b Z))
def hdle(x, y):
    if x == (): return True
    if y == (): return False
    a,b,_ = x; e,f,_ = y
    return a < e or (a == e and (olt(b,f) or b == f))

def wf3(t):
    if t == (): return True
    a,b,c = t
    if not wf3(b): return False
    if not wf3(c): return False
    for x in Gterm(a, b):
        if not olt(x, b): return False
    if not hdle(c, (a, b, Z)): return False
    return True

# ---- proj u b (Lean): filter Gterm for g with not olt g b; if empty -> b else proj of maxo
def maxo(x, ys):
    for y in ys:
        if olt(x, y): x = y
    return x

def proj(u, b):
    gs = [g for g in Gterm(u, b) if not olt(g, b)]
    if not gs:
        return b
    return proj(u, maxo(gs[0], gs[1:]))

# ---- ins a b t (Lean)
def ins(a, b, t):
    if t == (): return (a, b, Z)
    e,f,g = t
    if a < e or (a == e and olt(b, f)):
        return t
    return (a, b, t)

def nrm(t):
    if t == (): return Z
    a,b,c = t
    return ins(a, proj(a, nrm(b)), nrm(c))

def main():
    ST = enum_ST(seed_max_v=3, oper_ns=(1,2,3), max_len=11, rounds=6)
    terms = set()
    for M in ST:
        t = translate(M)
        for st in subterms(t):
            terms.add(st)
        terms.add(nrm(t))
        for st in subterms(nrm(t)):
            terms.add(st)
    print(f'#distinct terms (incl subterms & nrm-images): {len(terms)}')

    maxlvl = max((maxsub(t) for t in terms), default=0)
    U = range(0, maxlvl + 3)

    # Claim A: wf3 t -> for all u, all g in Gterm u t, olt g t
    a_total = a_viol = 0
    a_examples = []
    for t in terms:
        if not wf3(t): continue
        for u in U:
            for g in Gterm(u, t):
                a_total += 1
                if not olt(g, t):
                    a_viol += 1
                    if len(a_examples) < 5:
                        a_examples.append((u, g, t))
    print(f'\n[A] not_pfire_of_wf3 (wf3 t => Gterm u t all < t):')
    print(f'    checks={a_total}  violations={a_viol}')
    for u,g,t in a_examples:
        print(f'    VIOL u={u} g={g} t={t}')

    # Claim B: proj u (nrm t) == nrm t (ProjFixesNrm)
    b_total = b_viol = 0
    b_examples = []
    nrm_imgs = set(nrm(translate(M)) for M in ST)
    for t in terms:  # apply nrm to everything to get images
        nt = nrm(t)
        for u in U:
            b_total += 1
            if proj(u, nt) != nt:
                b_viol += 1
                if len(b_examples) < 5:
                    b_examples.append((u, t, nt, proj(u, nt)))
    print(f'\n[B] ProjFixesNrm (proj u (nrm t) == nrm t):')
    print(f'    checks={b_total}  violations={b_viol}')
    for u,t,nt,p in b_examples:
        print(f'    VIOL u={u} t={t} nrm={nt} proj={p}')

    # sanity: wf3(nrm t) always
    bad_wf = sum(1 for t in terms if not wf3(nrm(t)))
    print(f'\n[sanity] wf3(nrm t) failures: {bad_wf}')

if __name__ == '__main__':
    main()
