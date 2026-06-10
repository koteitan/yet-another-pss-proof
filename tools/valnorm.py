#!/usr/bin/env python3
"""Value-normalizer for Buchholz names (three-terms) and the INJ(m) experiment.

Hypothesised normalization rules (to be validated):
  o(D_a b): if some g in G_a(nrm b) has NOT g < nrm b (term order on normal
  names = value order), then psi_a is constant there and
  o(D_a b) = o(D_a g*) with g* = max G_a(nrm b).  Iterate.
  Sums: principal p_i is absorbed if some later principal p_j > p_i.

Validations:
  V1 nrm(t) in OT for all t;  V2 nrm idempotent;  V3 nrm = id on OT;
  V4 known identities: nrm(D0 D1 D2 0) = D0 D2 0;  t_k chain all equal.
Experiment INJ(m):
  for same-level NF terms (and ArgsA blocks) s <o t: is nrm s <T nrm t strictly?
  Collect violations (collapse pairs / order reversals).
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import (Z, P, translate, olt, maxsub, fmt, enum_ST)
from argsa_check import topsummands, sargs, build_argsa

# ---- three -> buchholz list-of-principals form ----
# principal: ('D', a, term);  term: tuple of principals (use tuples: hashable)
def conv(t):
    out = []
    while t != ():
        a, b, c = t
        out.append(('D', a, conv(b)))
        t = c
    return tuple(out)

def lt_princ(p, q):
    _, u, a = p; _, v, b = q
    if u != v: return u < v
    return lt_term(a, b)

def lt_term(a, b):
    if a == (): return b != ()
    if b == (): return False
    for x, y in zip(a, b):
        if x != y: return lt_princ(x, y)
    return len(a) < len(b)

def le_term(a, b): return a == b or lt_term(a, b)

def G(u, a):
    out = []
    for p in a:
        _, v, b = p
        if v >= u:
            out.append(b); out += G(u, b)
    return out

def in_OT(a):
    if a == (): return True
    if len(a) >= 2:
        if not all(le_term((a[i+1],), (a[i],)) or a[i+1] == a[i]
                   for i in range(len(a)-1)):
            # weakly decreasing principals
            pass
        for i in range(len(a)-1):
            if lt_princ(a[i], a[i+1]): return False
        return all(in_OT((p,)) for p in a)
    _, v, b = a[0]
    return in_OT(b) and all(lt_term(g, b) for g in G(v, b))

def norm_sum(ps):
    """absorb principals dominated by a later one (ordinal sum)."""
    out = []
    for i, p in enumerate(ps):
        if any(lt_princ(p, q) for q in ps[i+1:]):
            continue
        out.append(p)
    return tuple(out)

def nrm(t):
    """t: term (tuple of principals, raw). returns value-normal name."""
    ps = []
    for p in t:
        _, a, b = p
        bb = nrm(b)
        # collapse projection loop
        while True:
            bad = [g for g in G(a, bb) if not lt_term(g, bb)]
            if not bad: break
            g = bad[0]
            for h in bad[1:]:
                if lt_term(g, h): g = h
            bb = g
        ps.append(('D', a, bb))
    return norm_sum(tuple(ps))

def fmtb(a):
    if a == (): return '0'
    return '+'.join(f'D{p[1]}({fmtb(p[2])})' for p in a)

def main():
    # ---- validations ----
    D = lambda v, x: ('D', v, x)
    T = lambda *ps: tuple(ps)
    d2 = T(D(0, T(D(1, T(D(2, ()))))))      # D0 D1 D2 0
    print('V4a nrm(D0D1D2 0) =', fmtb(nrm(d2)), ' (expect D0(D2(0)))')
    t1 = T(D(0, T(D(1, ()))))                # D0 D1 0
    t2 = T(D(0, t1)); t3 = T(D(0, t2))
    print('V4b t_k values:', fmtb(nrm(t1)), '|', fmtb(nrm(t2)), '|', fmtb(nrm(t3)))
    y0 = T(D(1, ()))
    y1 = T(D(0, T(D(1, y0))))
    y2 = T(D(0, T(D(1, y1))))
    y3 = T(D(0, T(D(1, y2))))
    print('V4c y_k values:', fmtb(nrm(y1)), '|', fmtb(nrm(y2)), '|', fmtb(nrm(y3)))

    ST = enum_ST(seed_max_v=4, oper_ns=(1, 2, 3, 4), max_len=13, rounds=7)
    print('corpus', len(ST))
    NF = {}
    for M in ST:
        w = translate(M)
        NF.setdefault(maxsub(w), []).append(w)
    NFset, argsa, hosts = build_argsa(ST)

    allterms = [conv(w) for lst in NF.values() for w in lst]
    badV = [a for a in allterms if not in_OT(nrm(a))]
    print('V1 nrm lands in OT: violations', len(badV))
    badI = [a for a in allterms[:2000] if nrm(nrm(a)) != nrm(a)]
    print('V2 idempotent: violations', len(badI))

    # ---- INJ(m) on NF levels and ArgsA ----
    import itertools
    for name, fam in [('NF', NF), ('ArgsA', {m: list(s) for m, s in argsa.items()})]:
        for m in sorted(fam):
            terms = fam[m]
            if len(terms) > 320:
                terms = sorted(terms, key=lambda w: len(fmt(w)))[:320]
            eq = rev = 0
            ex = []
            for s, t in itertools.combinations(terms, 2):
                if olt(s, t): lo, hi = s, t
                elif olt(t, s): lo, hi = t, s
                else: continue
                nl, nh = nrm(conv(lo)), nrm(conv(hi))
                if nl == nh:
                    eq += 1
                    if len(ex) < 3: ex.append(('EQ', lo, hi))
                elif lt_term(nh, nl):
                    rev += 1
                    if len(ex) < 3: ex.append(('REV', lo, hi))
            n = len(terms)
            print(f'INJ {name}[{m}]: n={n}, collapse-pairs={eq}, reversals={rev}')
            for tag, lo, hi in ex:
                print(f'   {tag}: {fmt(lo)}  <o  {fmt(hi)}')
                print(f'        vals: {fmtb(nrm(conv(lo)))}  vs  {fmtb(nrm(conv(hi)))}')

if __name__ == '__main__':
    main()
