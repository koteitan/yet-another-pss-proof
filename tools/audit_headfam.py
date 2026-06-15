#!/usr/bin/env python3
"""Audit HeadFamilyNF's actual domain (closure+5/+6).

HeadFamilyNF (from oV_nf_arg_lt, used in oV_nf_order_pres): for NF terms P 0 b c,
P 0 f g with olt b f, the head psi_0(oV x) < psi_0(oV f) for every x <=o b.

Findings (run python3 audit_headfam.py):
(1) The head ARGS b (= args of lead-0 NF terms) overwhelmingly have lead >= 1
    (Omega_1 band): oV b >= Omega_1 > eps_0 = eps(0). So they are in the COLLAPSE
    region, NOT sub-eps. The sub-eps lever psi_strict_mono_lt_epsLvl does NOT apply.
(2) proj 0 b does NOT collapse to sub-Omega: lead(proj 0 b) stays >= 1. So the
    proj route lands in another Omega-band fixpoint (still collapse region).
=> HeadFamilyNF does NOT trivialize via sub-eps / proj-to-sub-Omega. It is genuine
   Omega-band collapse-region content, the dual of the (bypassed) collapse face.
(3) BUT: nrm is strictly term-order-preserving on NF (0 collapses, 0 reversals),
   so nrm_order_pres is TRUE; the clean route is TERM-STRUCTURAL (proj/ins
   monotone via proj0_olt_NF = {proj0_fireprop_NF, proj0_bothfire_NF}), avoiding
   oV/psi entirely. The oV/head route inherits psi_proj (sorryAx, suspect collapse).
"""
import sys, itertools
sys.path.insert(0, '.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST

Z = ()
def le_t(a, b): return a == b or lt_term(a, b)
def lead(t): return None if t == () else t[0][1]
def maxo(lst):
    m = lst[0]
    for h in lst[1:]:
        if lt_term(m, h): m = h
    return m
def proj(u, t):
    while True:
        bad = [x for x in G(u, t) if not lt_term(x, t)]
        if not bad: return t
        t = maxo(bad)

def audit(rounds):
    seen = set(); tot = 0; lh = {}; plh = {}
    for M in enum_ST(rounds=rounds):
        t = conv(translate(M))
        if t == () or lead(t) != 0: continue
        b = t[0][2]
        k = tuple(map(str, (b,)))
        if k in seen: continue
        seen.add(k); tot += 1
        lh[lead(b)] = lh.get(lead(b), 0) + 1
        plh[lead(proj(0, b))] = plh.get(lead(proj(0, b)), 0) + 1
    keyfn = lambda x: (x[0] is None, x[0])
    print(f"rounds={rounds}: lead-0 NF-term args b = {tot}")
    print(f"  (1) lead(b): {dict(sorted(lh.items(), key=keyfn))} "
          f"(>=1 => Omega-band, collapse region, NOT sub-eps)")
    print(f"  (2) lead(proj 0 b): {dict(sorted(plh.items(), key=keyfn))} "
          f"(stays >=1 => proj does NOT reach sub-Omega)")

    # (3) nrm strictly term-order-preserving on NF?
    nfs = []; sn = set()
    for M in enum_ST(rounds=rounds):
        t = conv(translate(M)); kk = tuple(map(str, (t,)))
        if kk in sn: continue
        sn.add(kk); nfs.append(t)
    rev = eq = npair = 0
    for v, u in itertools.combinations(nfs, 2):
        if lt_term(v, u): a, b = v, u
        elif lt_term(u, v): a, b = u, v
        else: continue
        npair += 1
        na, nb = nrm(a), nrm(b)
        if na == nb: eq += 1
        elif lt_term(nb, na): rev += 1
    print(f"  (3) NF pairs={npair}  nrm collapses={eq}  nrm reverses={rev} "
          f"(0/0 => nrm strictly order-preserving; term-structural route is clean)")

if __name__ == "__main__":
    for r in (5, 6):
        audit(r); print()
