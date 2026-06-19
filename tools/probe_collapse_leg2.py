#!/usr/bin/env python3
"""DECISIVE probe 2: pin the EXACT non-circular derivation.

Finding from probe 1: oV b' NOT in C_a(oV g) (0/586), and CollapseResidueMaxo TRUE.

The membership-route: assume psi_a(oV b') in C_a(oV g).
M1 (psi_form_of_mem) => exists xi in C_a(oV g), xi < oV g, psi_a(xi) = psi_a(oV b').
psi_arg_lt_of_mem applied to psi_a(oV b') in C_a(oV g) gives directly: oV b' < oV g.
  -- NO: psi_arg_lt_of_mem gives the ARGUMENT of the value < bound. The value
     psi_a(oV b') = psi_a(xi); the arg is xi (the GENERATOR's arg), not oV b'.
     But also psi_arg_lt_of_mem on a value psi_a(beta) in C_a(alpha) gives beta<alpha
     ONLY if the witness is forced =beta by injectivity (canonical beta).

THE crux to test:
  Is psi_a(oV b') in C_a(oV g)  EQUIVALENT to  oV b' in C_a(oV g) ?
  (this is what psi_arg_lt_of_mem-style reasoning would give if oV b' were canonical)
  i.e. test:  membership(psi_a(oV b') in C_a(oV g))  <=>  (oV b' in C_a(oV g))
  Both were 0 in probe1. Test the BICONDITIONAL holds always (the M1 reduction).

And the NON-CIRCULAR finish hypothesis:
  CLAIM: psi_a(oV b') in C_a(oV g)  =>  oV b' in C_a(oV g).
  Proof attempt (NON-circular): M1 gives xi<oV g canonical with psi_a(xi)=psi_a(oV b').
    If we DON'T know xi=oV b', can we still get oV b' in C_a(oV g)?
    psi_a(oV b') in C_a(oV g) and psi_a is a generator-value => by Cset_psi_closed
    REVERSE... Actually the clean fact: psi_a(oV b') in C_a(oV g) with oV b'<=oV g.
    Buchholz: a value psi_a(beta) in C_v(alpha) forces beta in C_v(alpha) when beta
    canonical (argExt_of_kernel/K). For NON-canonical beta=oV b' (B2!), argExt gives
    the canonical REP in C_v(alpha) -- = K = NoncanonValueMem. So:
      psi_a(oV b') in C_a(oV g)  =(K/argExt)=>  oV b' in C_a(oV g) [if oV b' canonical]
      OR rep(oV b') in C_a(oV g) [if non-canonical].
  So the membership gives: the canonical REP of oV b' is in C_a(oV g) and <oV g.
  The rep of oV b' (a-canonical) = oV(proj a b') -- THAT is the circularity claim.

TEST: compute rep_a(oV b') := value of proj a b' (the a-canonical rep). Check:
  (T1) is psi_a(oV b') in C_a(oV g) <=> rep_a(oV b') in C_a(oV g) ?  [the K reduction]
  (T2) is rep_a(oV b') = oV g ?  (the circular identity proj a b' = g)
  (T3) THE ESCAPE: is there ANY a-canonical delta with delta<oV g, delta in C_a(oV g),
       psi_a(delta)=psi_a(oV b'), and delta != rep_a(oV b')?  If the ONLY such delta
       is rep_a(oV b')=oV g, circular. If membership is simply IMPOSSIBLE (no delta),
       then CRM follows from "no witness exists" = NEC-style, possibly non-circular.
  (T4) Critically: does CRM follow from  [oV b' NOT in C_a(oV g)]  alone?
       i.e. is the implication  (oV b' notin C_a(oV g))  =>  (psi_a(oV b') notin C_a(oV g))
       TRUE on the model? If yes, and if (oV b' notin C_a(oV g)) is SUFF/NEC-derivable
       non-circularly, the leg is VIABLE.
"""
import sys
sys.path.insert(0, '.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST

Z = ()
def cn(x): return tuple(('D', vv, cn(bb)) for _, vv, bb in x)
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
def princ_in_Cself(alpha, v, p):
    _, u, xi = p
    if u < v: return True
    if not lt_term(xi, alpha): return False
    if not acanon(u, xi): return False
    return term_in_Cself(alpha, v, xi)
def term_in_Cself(alpha, v, delta):
    if delta == Z: return True
    return all(princ_in_Cself(alpha, v, p) for p in delta)
def psi_a(a, arg): return cn(nrm((('D', a, arg),)))

def collect(rounds):
    terms = set()
    for M in enum_ST(rounds=rounds):
        t = conv(translate(M)); st=[t]
        while st:
            x=st.pop()
            if not x: continue
            for (_,_,arg) in x: st.append(arg)
            terms.add(x)
    return terms

def audit(rounds):
    terms = collect(rounds)
    seen=set(); inst=0
    # membership of psi_a(oV b') in C_a(oV g) modeled as strict value-order < AND
    # the generator-trace test: psi_a(oV b') in C_a(oVg) iff exists canonical xi<oVg
    # in C_a(oVg) with psi_a(xi)=psi_a(oV b').
    mem_strict=0; mem_gentrace=0
    t1_equiv=0; t2_circular=0; t3_escape=0; t4_holds=0; t4_inst=0
    repeqg=0
    ex=[]
    # precompute canonical subterm pool per round
    pool = [cn(t) for t in terms if in_OT(t)]
    for b in terms:
        if not in_OT(b): continue
        bc=cn(b)
        for a in range(0,4):
            bad=[x for x in G(a,b) if not lt_term(x,b)]
            if not bad: continue
            g=maxo(bad); gc=cn(g)
            key=(a,str(bc),str(gc))
            if key in seen: continue
            seen.add(key); inst+=1
            pb=psi_a(a,bc); pg=psi_a(a,gc)
            mstrict = lt_term(pb,pg)         # value-order membership proxy
            # gen-trace membership: exists canonical xi<gc in C_a(gc), psi_a(xi)=pb
            gentrace=False; witnesses=[]
            for xc in pool:
                if lt_term(xc,gc) and acanon(a,xc) and term_in_Cself(gc,a,xc) and psi_a(a,xc)==pb:
                    gentrace=True; witnesses.append(xc)
            if mstrict: mem_strict+=1
            if gentrace: mem_gentrace+=1
            # T1: the two membership notions agree
            if mstrict==gentrace: t1_equiv+=1
            # rep of oV b' = value of proj a b'
            rep = cn(proj(a,b))
            if rep==gc: repeqg+=1
            # T4: (oV b' notin C_a(oV g)) => (psi_a(oV b') notin C_a(oV g))
            ob_in = term_in_Cself(gc,a,bc)
            t4_inst+=1
            # implication holds if NOT(ob_in) implies NOT(mem)
            mem = mstrict  # use strict as the faithful membership
            if (not ob_in and not mem) or ob_in:
                t4_holds+=1
            # T3: escape -- membership witnesses that are NOT the rep and != g
            if mem and witnesses:
                nonrep = [w for w in witnesses if w!=rep and w!=gc]
                if nonrep: t3_escape+=1
                if all(w==rep or w==gc for w in witnesses): t2_circular+=1
    print(f"rounds={rounds}: instances={inst}")
    print(f"  membership (strict value-order)     = {mem_strict}/{inst}")
    print(f"  membership (generator-trace)        = {mem_gentrace}/{inst}")
    print(f"  T1 two membership notions agree     = {t1_equiv}/{inst}")
    print(f"  rep_a(oV b') == oV g (proj=g)       = {repeqg}/{inst}")
    print(f"  T4 (oVb' notin C) => (psi notin C)  = {t4_holds}/{t4_inst}")
    print(f"  T3 membership has NON-rep witness   = {t3_escape}")
    print(f"  T2 membership ONLY via rep/g (circ) = {t2_circular}")

if __name__=="__main__":
    for r in (5,6,7):
        audit(r); print()
