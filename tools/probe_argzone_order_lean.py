#!/usr/bin/env python3
"""Soundness gate for the arg-zone ORDER port into Lean (Three encoding).

Verifies the NEW claims I intend to state/prove in YAPSS/Nrmstep.lean:

  (A) nrm_argzone_olt (NRMMONO, recursion residual, ya-pss-verified TRUE):
        on NF terms B,F:  olt B F -> olt (nrm B) (nrm F)
      (here B,F are themselves NF = nrm-images, so nrm is identity; we test
       the genuine version on translate-images of ST_PS args).

  (B) proj_step_argzone_olt (PROJSTEP crux, whole-image form):
        on NF terms B,F:  olt B F -> olt (proj 0 B) (proj 0 F)

  (C) argzone_proj_head (H1, whole-image firing lands on head arg):
        NF X fires under proj 0  =>  proj 0 X = hdarg X  AND  not olt (hdarg X) X

  (D) argzone_head_lead_gt (H1 lead-gap, GREEN candidate):
        NF X fires => lead X < lead (hdarg X)

  (E) argzone_harg_olt / argzone_F_fires (H2 transport):
        olt B F, B fires => F fires AND olt (hdarg B) (hdarg F)
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()

def le(s, t): return s == t or olt(s, t)

def Gterm(u, t):
    if t == Z: return []
    a, b, c = t
    out = []
    if u <= a:
        out.append(b); out += Gterm(u, b)
    out += Gterm(u, c)
    return out

def pfire(u, b):
    return any(not olt(g, b) for g in Gterm(u, b))

def proj(u, b):
    while True:
        bad = [g for g in Gterm(u, b) if not olt(g, b)]
        if not bad: return b
        m = bad[0]
        for h in bad[1:]:
            if olt(m, h): m = h
        b = m

def lead(t): return 0 if t == Z else t[0]
def hdarg(t): return Z if t == Z else t[1]

def ins(a, b, t):
    if t == Z: return (a, b, Z)
    e, f, g = t
    if a < e or (a == e and olt(b, f)): return t
    return (a, b, t)

def nrm(t):
    if t == Z: return Z
    a, b, c = t
    return ins(a, proj(a, nrm(b)), nrm(c))

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1, 2, 3, 4), max_len=13, rounds=7)
    NF = sorted({translate(M) for M in ST}, key=str)
    print(f"NF terms: {len(NF)}")

    # whole NF terms (these are nrm-images; head subscript should be 0)
    nontrivial = [t for t in NF if t != Z]
    bad_lead0 = sum(1 for t in nontrivial if lead(t) != 0)
    print(f"NF head-subscript != 0 : {bad_lead0}/{len(nontrivial)}")

    # (B) whole-image PROJSTEP
    B_tot = B_bad = 0
    Bex = []
    for x in NF:
        for y in NF:
            if olt(x, y):
                B_tot += 1
                if not olt(proj(0, x), proj(0, y)):
                    B_bad += 1
                    if len(Bex) < 5: Bex.append((x, y))
    print(f"(B) whole-image PROJSTEP olt(proj0 X)(proj0 Y): tot {B_tot} viol {B_bad}")
    for e in Bex: print("   B VIOL", e)

    # (C) whole-image firing -> proj = hdarg AND hdarg is violator
    C_tot = C_bad_eq = C_bad_viol = 0
    Cex = []
    for x in nontrivial:
        if pfire(0, x):
            C_tot += 1
            if proj(0, x) != hdarg(x): C_bad_eq += 1; (Cex.append(('eq', x)) if len(Cex)<5 else None)
            if olt(hdarg(x), x): C_bad_viol += 1; (Cex.append(('viol', x)) if len(Cex)<5 else None)
    print(f"(C) firing NF: tot {C_tot}  proj!=hdarg {C_bad_eq}  hdarg-not-violator {C_bad_viol}")
    for e in Cex: print("   C VIOL", e)

    # (D) lead-gap
    D_tot = D_bad = 0
    for x in nontrivial:
        if pfire(0, x):
            D_tot += 1
            if not (lead(x) < lead(hdarg(x))): D_bad += 1
    print(f"(D) firing NF lead X < lead(hdarg X): tot {D_tot} viol {D_bad}")

    # (E) H2 transport: olt B F, B fires => F fires AND olt(hdarg B)(hdarg F)
    E_tot = E_bad_fire = E_bad_ord = 0
    Eex = []
    for x in nontrivial:
        if not pfire(0, x): continue
        for y in nontrivial:
            if olt(x, y):
                E_tot += 1
                if not pfire(0, y): E_bad_fire += 1; (Eex.append(('Ffire', x, y)) if len(Eex)<5 else None)
                if not olt(hdarg(x), hdarg(y)): E_bad_ord += 1; (Eex.append(('hord', x, y)) if len(Eex)<5 else None)
    print(f"(E) H2 transport: tot {E_tot}  F-no-fire {E_bad_fire}  hdarg-order-rev {E_bad_ord}")
    for e in Eex: print("   E VIOL", e)

if __name__ == '__main__':
    main()
