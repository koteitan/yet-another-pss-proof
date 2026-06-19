#!/usr/bin/env python3
"""DECISIVE probe: is the collapse leg
   [ Cset=CsetSelf (canonical closure) + SUFF/NEC + B2 ] ==> CollapseResidueMaxo
non-circular, or does it genuinely require psi_proj?

Model: term-side normal-name value order (lt_term = value order; nrm = canonical
rep). We model the ORDINAL closure C_a(alpha) on the CANONICAL fragment via the
with-C (CsetSelf) characterization:
   delta in CsetSelf(alpha) v   iff   every principal generator psi_u(xi) of delta
   has [ u<v, OR (xi < alpha AND xi a-canonical AND xi in CsetSelf(alpha) v) ].
This is precisely term_in_Cself / princ_in_Cself from audit_joint_sublemmas.
canonicity acanon(u, t) := not exists g in G(u,t) with not lt_term(g,t).

We test, at closure+5/+6/+7, the EXACT membership question:
  is  psi_a(oV b')  in  C_a(oV g)  ?
for maxo violators g of wf3 b' at level a, and whether the M1 witness xi (the
generator of psi_a(oV b') inside C_a(oV g)) is FORCED to be oV(proj a b') = oV g
(=circular) or can be certified < oV g non-circularly.

Key NON-CIRCULAR levers tested:
 (L1) NEC at b' / bound oV g:  if oV b' in C_a(oV g) then every x in Gterm a b'
      has oV x < oV g. Does this HOLD? (it is SUFF-derivable, non-circular)
 (L2) does oV b' in C_a(oV g) ?  (needed for L1 to apply / for the M1 witness=oV b')
 (L3) the M1 witness xi of psi_a(oV b') in C_a(oV g): what is it? is xi = oV b'
      itself (=> need oV b' canonical, contradicted by B2) or strictly smaller?
 (L4) THE TEST: assuming membership psi_a(oV b') in C_a(oV g), derive
      psi_a(oV b') = psi_a(xi) with xi<oV g canonical. Is xi's VALUE = oV b'?
      If xi != oV b' as values but psi_a(xi)=psi_a(oV b'), that is a NON-TRIVIAL
      collapse below oV g -- which is exactly psi_proj-flavoured.
"""
import sys
sys.path.insert(0, '.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST

Z = ()
def le_t(a, b): return a == b or lt_term(a, b)
def cn(x):
    return tuple(('D', vv, cn(bb)) for _, vv, bb in x)
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
def acanon(u, t):
    return not any(not lt_term(x, t) for x in G(u, t))

# CsetSelf membership on the canonical fragment, bound = canonical term alpha.
# delta, alpha are canonical (nrm'd) terms; v = subscript.
def princ_in_Cself(alpha, v, p):
    _, u, xi = p
    if u < v: return True
    if not lt_term(xi, alpha): return False
    if not acanon(u, xi): return False
    return term_in_Cself(alpha, v, xi)
def term_in_Cself(alpha, v, delta):
    if delta == Z: return True
    return all(princ_in_Cself(alpha, v, p) for p in delta)

def psi_a(a, arg):
    """canonical value of psi_a(arg) as a normal name = nrm(D_a arg)."""
    return cn(nrm((('D', a, arg),)))

def collect_terms(rounds):
    terms = set()
    for M in enum_ST(rounds=rounds):
        t = conv(translate(M)); st = [t]
        while st:
            x = st.pop()
            if not x: continue
            for (_, _, arg) in x: st.append(arg)
            terms.add(x)
    return terms

def audit(rounds):
    terms = collect_terms(rounds)
    seen = set()
    inst = 0
    crm_true = 0          # psi_a(oV b') NOT in C_a(oV g)  (= CollapseResidueMaxo holds)
    membership = 0        # psi_a(oV b') in C_a(oV g)
    # L1: NEC at b' bound oV g (the SUFF-derivable necessity, IF oV b' in C_a(oV g))
    ovb_in_Cg = 0
    nec_l1_holds = 0
    nec_l1_inst = 0
    # L4: the witness collapse below oV g
    wit_eq_ovb_value = 0  # exists xi<oV g canonical, psi_a(xi)=psi_a(oV b'), value(xi)=value(oV b')
    wit_strict_below = 0  # exists such xi with value(xi) < value(oV b')  (=> below b', collapse)
    nontrivial_collapse_below = 0
    ex = []
    for b in terms:
        if not in_OT(b): continue
        bc = cn(b)
        for a in range(0, 4):
            bad = [x for x in G(a, b) if not lt_term(x, b)]
            if not bad: continue
            g = maxo(bad)
            gc = cn(g)
            key = (a, str(bc), str(gc))
            if key in seen: continue
            seen.add(key); inst += 1
            # values
            pb = psi_a(a, bc)   # psi_a(oV b')  as canonical name (single principal expected)
            # membership psi_a(oV b') in C_a(oV g): the value pb is a principal; it's in
            # C_a(gc) iff it equals psi_a(xi) for some xi<gc canonical in C_a(gc).
            # Equivalently (plateau): pb in C_a(gc) iff pb != psi_a(gc) AND pb<psi_a(gc)
            # ... but the faithful test is: pb is a generator value reachable. We use the
            # value-order proxy consistent with psi_proj_mem_imp_strict / psi_notMem_iff_eq:
            #   pb in C_a(gc)  <=>  pb (strictly) < psi_a(gc)  [since oV b' <= oV g]
            pg = psi_a(a, gc)
            in_Cg = lt_term(pb, pg)   # strict value-order  == membership
            if in_Cg:
                membership += 1
            else:
                crm_true += 1
            # L2: oV b' in C_a(oV g)?  (b' as a value, not psi_a(b'))
            ob_in = term_in_Cself(gc, a, bc)
            if ob_in: ovb_in_Cg += 1
            # L1: NEC -- IF oV b' in C_a(oV g) then all x in Gterm a b' have oV x < oV g
            if ob_in:
                nec_l1_inst += 1
                ok = all(lt_term(cn(x), gc) for x in G(a, b))
                if ok: nec_l1_holds += 1
            # L4: when membership holds, find the witness xi<gc canonical with psi_a(xi)=pb
            if in_Cg:
                # search small canonical args xi with psi_a(xi)=pb, xi<gc, acanon(a,xi)
                found = None
                # candidate xi values: all subterm values in corpus below gc
                cands = set()
                for t2 in terms:
                    tc = cn(t2)
                    if lt_term(tc, gc) and acanon(a, tc) and psi_a(a, tc) == pb:
                        cands.add(tc)
                # also b' itself
                if psi_a(a, bc) == pb and acanon(a, bc) and lt_term(bc, gc):
                    cands.add(bc)
                if cands:
                    # is any candidate's value == value(oV b')?
                    if any(c == bc for c in cands):
                        wit_eq_ovb_value += 1
                    elif any(lt_term(c, bc) for c in cands):
                        wit_strict_below += 1
                        nontrivial_collapse_below += 1
                        if len(ex) < 4:
                            ex.append((a, bc, gc, sorted(map(str, cands))))
    print(f"rounds={rounds}: wf3 maxo-violator instances = {inst}")
    print(f"  CollapseResidueMaxo holds (psi_a(oVb') NOT< psi_a(oVg)) = {crm_true}/{inst}")
    print(f"  membership cases (psi_a(oVb') < psi_a(oVg))            = {membership}/{inst}")
    print(f"  L2  oV b' in C_a(oV g)                                 = {ovb_in_Cg}/{inst}")
    print(f"  L1  NEC@b' bound oVg holds when oVb' in C_a(oVg)        = {nec_l1_holds}/{nec_l1_inst}")
    print(f"  L4  membership-witness == oV b' value                  = {wit_eq_ovb_value}")
    print(f"  L4  membership-witness STRICTLY below oV b' (collapse) = {wit_strict_below}")
    for a, bc, gc, cands in ex:
        print(f"      a={a} b'={bc} g={gc} witnesses={cands}")

if __name__ == "__main__":
    for r in (5, 6, 7):
        audit(r)
        print()
