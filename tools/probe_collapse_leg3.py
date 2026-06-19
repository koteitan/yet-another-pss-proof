#!/usr/bin/env python3
"""DECISIVE probe 3: the B2 + argExt(K) contradiction, and whether it is psi_proj.

VERDICT (2026-06-20): CIRCULAR. The collapse leg [Cset=CsetSelf + SUFF + B2] does
NOT non-circularly give CollapseResidueMaxo. Decisive facts (586/586 @+5/6/7):
  - rep_a(oV b') = oV(proj a b') = oV g  (the value identity = psi_proj).
  - the MINIMAL a-canonical realizer of psi_a(oV b') IS oV g (not < oV g).
  - so the M1/argExt witness xi<oV g canonical with psi_a(xi)=psi_a(oV b') CANNOT
    exist; refuting it requires knowing the minimal realizer = oV g = oV(proj a b'),
    which IS psi_proj. B2 only excludes xi=oV b'; the larger-canonical-witness case
    needs the value identity. Confirmed against ya-pss psi_proj_nonmem (also sorry
    even with term_nec+B2 green). NOTE: probe_collapse_leg5/6 showed lt_term (term
    name order) is NOT faithful to ordinal value order at Omega_k crossings, so the
    'gap' (lt_term) comparisons are unreliable; only psi_a-value-equality (via nrm)
    and acanon are faithful, and those are what the verdict rests on.


Established:
 - oV b' NOT in C_a(oV g)  (586/586)
 - rep_a(oV b') = oV(proj a b') = oV g  (586/586)   <- the circular identity
 - psi_arg_lt_of_mem (PROVEN): psi_a(oVb') in C_a(oVg) => oV b' < oV g (consistent w/ B1)

THE membership-route contradiction (Buchholz's actual argument), step by step:
  Assume H: psi_a(oV b') in C_a(oV g).
  (S1) argExt_of_kernel/K applied to value psi_a(oV b') in C_a(oV g):
       extracts generator xi < oV g, xi in C_a(oV g), psi_a(xi)=psi_a(oV b').
       Split on xi canonical:
        - xi a-canonical: psi_canonical_inj forces ... xi = (canonical arg). But
          oV b' is NON-canonical (B2). So xi != oV b' as the canonical witness;
          instead K says: the CANONICAL REP of oV b' is in C_a(oV g).
        - The canonical rep of oV b' = oV(proj a b') = oV g.  => oV g in C_a(oV g)
          with oV g < oV g??  CONTRADICTION (rep < bound but rep = bound).

  So the contradiction is:  K gives  rep_a(oV b') in C_a(oV g) AND rep_a(oV b')<oV g
  (psi_arg_lt), but rep_a(oV b') = oV g, so oV g < oV g.  CONTRADICTION.

  THIS contradiction needs:
   (a) K = NoncanonValueMem (the 4-leaf joint induction)  -- supplies rep in C
   (b) rep_a(oV b') = oV g  i.e. oV(proj a b') = oV g  -- IS the proj identity.
       BUT do we need the VALUE identity oV(proj a b')=oV g, or only that the
       canonical rep (whatever it is) is < oV g AND equals oV g?

  The KEY question (T-CIRC): does the contradiction require knowing
   rep = oV g (value identity = psi_proj-flavoured),
  OR does it suffice that  the canonical rep delta satisfies  psi_a(delta)=psi_a(oV b')
   AND delta is the LEAST a-canonical with that value, AND delta >= oV g (so not <oV g)?

TEST T-CIRC: among all a-canonical delta with psi_a(delta)=psi_a(oV b'):
   - is the MINIMAL such delta equal to oV g?  (if yes: rep=g, value identity needed)
   - is EVERY such delta >= oV g?  (if yes: NO canonical witness < oV g exists =>
       membership impossible by K WITHOUT needing the value identity, only the
       BAND fact 'no canonical rep below oV g')
   - crucially: is there an a-canonical delta with psi_a(delta)=psi_a(oV b') and
       delta < oV g?  If NONE (0 viol), then membership is refuted by
       'no canonical witness below the bound' = a NEC/SUFF band fact, possibly
       WITHOUT the full value identity rep=g.  This is the ESCAPE.
"""
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
def maxo(lst):
    m=lst[0]
    for h in lst[1:]:
        if lt_term(m,h): m=h
    return m
def proj(u,t):
    while True:
        bad=[x for x in G(u,t) if not lt_term(x,t)]
        if not bad: return t
        t=maxo(bad)
def acanon(u,t): return not any(not lt_term(x,t) for x in G(u,t))
def psi_a(a,arg): return cn(nrm((('D',a,arg),)))
def collect(rounds):
    terms=set()
    for M in enum_ST(rounds=rounds):
        t=conv(translate(M)); st=[t]
        while st:
            x=st.pop()
            if not x: continue
            for (_,_,arg) in x: st.append(arg)
            terms.add(x)
    return terms

def audit(rounds):
    terms=collect(rounds)
    pool=sorted({cn(t) for t in terms if in_OT(t)}, key=lambda z: (len(str(z)), str(z)))
    seen=set(); inst=0
    canon_below=0      # exists a-canonical delta < oV g with psi_a(delta)=psi_a(oVb')
    min_canon_eq_g=0   # the MINIMAL a-canonical delta with that value == oV g
    every_canon_ge_g=0 # every a-canonical delta with that value is >= oV g
    no_canon_witness=0 # NO a-canonical delta (in pool) with that value at all except >=g
    b2_noncanon=0      # oV b' is a-non-canonical (B2)
    ex=[]
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
            pb=psi_a(a,bc)
            if not acanon(a,bc): b2_noncanon+=1
            # all a-canonical delta in pool with psi_a(delta)=pb
            canon_deltas=[d for d in pool if acanon(a,d) and psi_a(a,d)==pb]
            # include g itself
            if acanon(a,gc) and psi_a(a,gc)==pb and gc not in canon_deltas:
                canon_deltas.append(gc)
            below=[d for d in canon_deltas if lt_term(d,gc)]
            if below: canon_below+=1
            if canon_deltas:
                mn=min(canon_deltas, key=lambda z:(0,) if z==Z else (1,))
                # minimal by value order
                mn=canon_deltas[0]
                for d in canon_deltas[1:]:
                    if lt_term(d,mn): mn=d
                if mn==gc: min_canon_eq_g+=1
                if all((d==gc) or (not lt_term(d,gc)) for d in canon_deltas):
                    every_canon_ge_g+=1
                if not below:
                    no_canon_witness+=1
            else:
                no_canon_witness+=1
            if len(ex)<3 and below:
                ex.append((a,bc,gc,[str(d) for d in below]))
    print(f"rounds={rounds}: instances={inst}")
    print(f"  B2 oV b' a-non-canonical                       = {b2_noncanon}/{inst}")
    print(f"  EXISTS a-canonical delta < oV g, psi=psi(oVb') = {canon_below}/{inst}   (>0 = ESCAPE BLOCKED)")
    print(f"  no a-canonical witness BELOW oV g              = {no_canon_witness}/{inst}")
    print(f"  minimal a-canonical witness == oV g            = {min_canon_eq_g}/{inst}")
    print(f"  every a-canonical witness >= oV g              = {every_canon_ge_g}/{inst}")
    for a,bc,gc,below in ex:
        print(f"     a={a} b'={bc} g={gc} below-witnesses={below}")

if __name__=="__main__":
    for r in (5,6,7):
        audit(r); print()
