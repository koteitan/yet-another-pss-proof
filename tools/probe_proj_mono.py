#!/usr/bin/env python3
"""Probe the candidate STRUCTURAL spine for nrm_order_pres / nrm_step_dec:

  P-MONO   : b <T b'  =>  proj u b <=T proj u b'         (proj monotone, level u)
  P-SMONO  : b <T b'  =>  proj u b <T  proj u b'  OR collapse-explained
  INS-MONO : (a,b) "<" (a',b') heads => ins-results compare correctly
  NRM-MONO : the induction target -- s <T t (in NF) => nrm s <=T nrm t,
             strict unless a value-collapse (which on NF must not happen)

If proj is monotone on the NF-subterm domain, nrm_order_pres falls out by
structural induction (proj/ins monotone => nrm monotone). We test on the
closure+6 corpus of standard-form translates AND their hereditary subterms,
plus the advice re-entry hosts.

Domain matters: proj/nrm only need to be monotone on terms that actually arise
as subterms of NF translates (the wf3/standard domain), NOT on all Three.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, olt, maxsub
from fast_pss import oper, diagSeq, Lng
from valnorm import conv, nrm, lt_term, le_term, G as Gset

def proj(u, b):
    """conv-form proj: iterated-max collapse over G(u,b) filtered to g>=b."""
    bb = b
    while True:
        bad = [g for g in Gset(u, bb) if not lt_term(g, bb)]
        if not bad:
            break
        g = bad[0]
        for h in bad[1:]:
            if lt_term(g, h):
                g = h
        bb = g
    return bb

def subterms(c):
    """hereditary sub-args (conv form) of a conv'd term: every D_a(b) arg b."""
    out = []
    for (_, a, b) in c:
        out.append((a, b))
        out += subterms(b)
    return out

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
    ns = (1, 2, 3)
    ST = enum(smv, ns, mlen, rounds)
    # collect all hereditary (level a, arg b) sub-pairs from NF translates
    pairs = set()
    for M in ST:
        c = conv(translate(M))
        for (a, b) in [(a, b) for (_, a, b) in c] + subterms(c):
            pairs.add((a, b))
    # also include the advice re-entry hosts' subterms
    extra = [
        [(0,0),(1,1),(2,2),(3,0),(4,1),(5,2),(6,0),(7,1),(8,2),(8,0)],
        [(0,0),(1,1),(2,1),(3,1),(4,0),(5,1),(6,1),(7,0),(8,1),(9,1),(8,1),(9,0),
         (10,1),(11,1),(10,1),(11,0),(12,1),(13,1),(12,1),(13,0),(14,1),(15,1),(14,1)],
    ]
    for M in extra:
        c = conv(translate(tuple(M)))
        for (a, b) in [(a, b) for (_, a, b) in c] + subterms(c):
            pairs.add((a, b))
    print(f'corpus hosts={len(ST)}  distinct (level,arg) sub-pairs={len(pairs)}')

    # group args by level u
    by_u = {}
    for (u, b) in pairs:
        by_u.setdefault(u, set()).add(b)

    pmono_viol = []; checked = 0
    for u, bs in by_u.items():
        bs = list(bs)
        for i in range(len(bs)):
            pi = proj(u, bs[i])
            for j in range(len(bs)):
                if i == j: continue
                if lt_term(bs[i], bs[j]):
                    checked += 1
                    pj = proj(u, bs[j])
                    # P-MONO: proj u b <= proj u b'
                    if not le_term(pi, pj):
                        pmono_viol.append((u, bs[i], bs[j], 'REVERSAL'))
    print(f'[P-MONO] checked={checked}  violations(reversal of proj)={len(pmono_viol)}')
    for v in pmono_viol[:15]:
        print('  ', v)

    # NRM-MONO on all NF-translate args at each level (the real induction target)
    allargs = list({b for (_, b) in pairs})
    nmono_viol = []; nck = 0
    for i in range(len(allargs)):
        ni = nrm(allargs[i])
        for j in range(len(allargs)):
            if i == j: continue
            if lt_term(allargs[i], allargs[j]):
                nck += 1
                nj = nrm(allargs[j])
                if not le_term(ni, nj):
                    nmono_viol.append((allargs[i], allargs[j], 'REVERSAL'))
    print(f'[NRM-MONO on subterms] checked={nck}  violations={len(nmono_viol)}')
    for v in nmono_viol[:15]:
        print('  ', v)
